#!/usr/bin/env python3

import os
import sys
import random

# ISA:
# Registers: ZERO, A0, ... A5

# Instructions:
# addi rd rs1 imm
# add rd rs1 rs2
# br rs1 imm

# this file generates a random sequence of instructions
# and writes it to a file. USed to stress test the processor


def genNinst(n: int):
    ret = []
    for i in range(n):
        cmd = random.randint(0, 100)
        if cmd <= 40:
            rd = random.randint(1, 5)
            rs1 = random.randint(1, 5)
            rs2 = random.randint(1, 5)
            ret.append(f"add {rd} {rs1} {rs2}")
        elif cmd <= 95:
            rd = random.randint(1, 5)
            rs1 = random.randint(1, 5)
            imm = random.randint(0, 2**16)
            ret.append(f"addi {rd} {rs1} {imm}")
        elif cmd <= 100:
            rs1 = random.randint(1, 5)
            imm = random.randint(-20, 20)
            imm = max(i + imm, 1)
            ret.append(f"br {rs1} {imm}")
    return ret


def main():
    if len(sys.argv) != 3:
        print("Usage: stress.py <num_instructions> <output_file>")
        sys.exit(1)
    n = int(sys.argv[1])
    out = sys.argv[2]
    inst = genNinst(n)
    with open(out, "w") as f:
        for i in inst:
            f.write(i + "\n")


if __name__ == "__main__":
    main()
