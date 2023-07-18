#!/usr/bin/env python3

import sys
import random

# ISA:
# Registers: ZERO, A0, ... A5

# Instructions:
# addi rd rs1 imm
# add rd rs1 rs2
# mul rd rs1 rs2
# sub rd rs1 rs2
# jumpnz rs1 imm
# jumpneg rs1 imm

# this file generates a random sequence of instructions
# and writes it to a file. USed to stress test the processor

MAXREGS = 9


def genNinst(n: int):
    MAXDEPTH = 5
    ret = [f"addi {MAXREGS} {MAXREGS} {MAXDEPTH}"] + ["nop"] * (n-2)

    branch_prelude = [f"jumpneg {MAXREGS} EXIT",
                      f"addi {MAXREGS} {MAXREGS} -1"]

    i = 0
    while i < len(ret):
        if ret[i] == "nop":
            cmd = random.randint(0, 100)
            if cmd <= 20:
                rd = random.randint(1, MAXREGS-1)
                rs1 = random.randint(1, MAXREGS-1)
                rs2 = random.randint(1, MAXREGS-1)
                ret[i] = f"add {rd} {rs1} {rs2}"
            elif cmd <= 30:
                rd = random.randint(1, MAXREGS-1)
                rs1 = random.randint(1, MAXREGS-1)
                imm = random.randint(0, 2**16)
                ret[i] = f"addi {rd} {rs1} {imm}"
            elif cmd <= 40:
                rd = random.randint(1, MAXREGS-1)
                rs1 = random.randint(1, MAXREGS-1)
                rs2 = random.randint(1, MAXREGS-1)
                ret[i] = f"sub {rd} {rs1} {rs2}"
            elif cmd <= 80:
                rd = random.randint(1, MAXREGS-1)
                rs1 = random.randint(1, MAXREGS-1)
                rs2 = random.randint(1, MAXREGS-1)
                ret[i] = f"mul {rd} {rs1} {rs2}"
            elif cmd <= 100:
                # want to stay inside program
                lower = -i + 1
                upper = n - i - 1
                target = random.randint(lower, upper)
                reg = random.randint(1, MAXREGS-1)
                branch_type = random.choice(['jumpnz', 'jumpneg'])
                ret[i] = f"{branch_type} {reg} {target}"
                for ins in reversed(branch_prelude):
                    ret.insert(i, ins)
                    i += 1
        i += 1
    # Replace EXIT with the proper imm value

    for i, ins in enumerate(ret):
        if ins.find("EXIT") != -1:
            ret[i] = ins.replace("EXIT", str(len(ret) - i - 1))
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
