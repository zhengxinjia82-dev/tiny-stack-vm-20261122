// Tiny stack VM for make.fun's tiny stack ISA v1. One run answers a set:
// reads <id>/{program,input}.bin, writes <id>/{stdout.bin,exit.txt}.
import { mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STEP_MAX = 1000000;
const OUT_MAX = 65536;

// Opcode table: [byte, immediate bytes, popped, pushed]. Other bytes trap 5.
const IMM = new Uint8Array(256);
const POPN = new Uint8Array(256);
const PSHN = new Uint8Array(256);
const KNOWN = new Uint8Array(256);
for (const [op, imm, pops, pushes] of [
  [0x00,0,0,0],[0x01,1,0,1],[0x02,4,0,1],[0x03,0,1,0],[0x04,0,1,2],[0x05,0,2,2],
  [0x06,0,2,3],[0x07,0,3,3],[0x10,0,2,1],[0x11,0,2,1],[0x12,0,2,1],[0x13,0,2,1],
  [0x14,0,2,1],[0x15,0,2,1],[0x16,0,2,1],[0x17,0,1,1],[0x18,0,2,1],[0x19,0,2,1],
  [0x1a,0,2,1],[0x1b,0,1,1],[0x1c,0,2,1],[0x1d,0,2,1],[0x1e,0,2,1],[0x20,0,2,1],
  [0x21,0,2,1],[0x22,0,2,1],[0x30,2,0,0],[0x31,2,1,0],[0x32,2,1,0],[0x33,2,0,0],
  [0x34,0,0,0],[0x40,0,1,1],[0x41,0,2,0],[0x50,0,1,0],[0x51,0,1,0],[0x52,0,0,1],
  [0x53,0,1,0],
]) {
  IMM[op] = imm; POPN[op] = pops; PSHN[op] = pushes; KNOWN[op] = 1;
}

function runVM(prog, input) {
  const n = prog.length;
  const st = new Int32Array(256);
  const cs = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(OUT_MAX);
  let sp = 0, cp = 0, pc = 0, steps = 0, ip = 0, ol = 0;
  const done = (exit) => ({ out: out.subarray(0, ol), exit, steps });
  for (;;) {
    if (steps === STEP_MAX) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = prog[pc];
    if (!KNOWN[op]) return done(5);
    const imm = IMM[op];
    if (pc + imm >= n) return done(9);
    steps++;
    if (sp < POPN[op]) return done(2);
    if (sp - POPN[op] + PSHN[op] > 256) return done(3);
    const q = pc;
    pc = q + 1 + imm;
    switch (op) {
      case 0x00: return done(0);
      case 0x01: st[sp++] = (prog[q + 1] << 24) >> 24; break;
      case 0x02:
        st[sp++] = prog[q + 1] | (prog[q + 2] << 8) | (prog[q + 3] << 16) | (prog[q + 4] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: st[sp] = st[sp - 1]; sp++; break;
      case 0x05: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; }
      case 0x06: st[sp] = st[sp - 2]; sp++; break;
      case 0x07: {
        const a = st[sp - 3];
        st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a;
        break;
      }
      case 0x17: st[sp - 1] = (-st[sp - 1]) | 0; break;
      case 0x1b: st[sp - 1] = ~st[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = st[sp - 1], a = st[sp - 2];
        let r;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return done(4);
            r = (a === -2147483648 && b === -1) ? a : (a / b) | 0;
            break;
          case 0x14:
            if (b === 0) return done(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15:
            if (b === 0) return done(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16:
            if (b === 0) return done(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        }
        sp -= 2; st[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[q + 1] | (prog[q + 2] << 8)) << 16) >> 16;
        if (op === 0x30) pc = pc + rel;
        else {
          const v = st[--sp];
          if ((op === 0x31) === (v === 0)) pc = pc + rel;
        }
        break;
      }
      case 0x33:
        if (cp === 64) return done(7);
        cs[cp++] = pc;
        pc = prog[q + 1] | (prog[q + 2] << 8);
        break;
      case 0x34:
        if (cp === 0) return done(8);
        pc = cs[--cp];
        break;
      case 0x40: {
        const addr = st[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        st[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = st[sp - 1], v = st[sp - 2];
        if (addr < 0 || addr > 255) return done(6);
        sp -= 2; mem[addr] = v;
        break;
      }
      case 0x50: {
        const s = String(st[sp - 1]);
        if (ol + s.length > OUT_MAX) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (ol + 1 > OUT_MAX) return done(11);
        out[ol++] = st[--sp] & 255;
        break;
      case 0x52: st[sp++] = ip < input.length ? input[ip++] : -1; break;
      case 0x53: return done(st[--sp] & 255);
    }
  }
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
let instances = 0, totalSteps = 0;
for (const id of readdirSync(IN_DIR).sort()) {
  const dir = join(IN_DIR, id);
  try { if (!statSync(dir).isDirectory()) continue; } catch { continue; }
  let prog = new Uint8Array(0), input = new Uint8Array(0);
  try { prog = readFileSync(join(dir, 'program.bin')); } catch {}
  try { input = readFileSync(join(dir, 'input.bin')); } catch {}
  const { out, exit, steps } = runVM(prog, input);
  if (exit < 0 || exit > 255) throw new Error('bad exit ' + exit);
  const od = join(OUT_DIR, id);
  mkdirSync(od, { recursive: true });
  writeFileSync(join(od, 'stdout.bin'), out);
  writeFileSync(join(od, 'exit.txt'), String(exit) + '\n');
  instances++;
  totalSteps += steps;
}
console.error(`done: ${instances} instances, ${totalSteps} steps`);
