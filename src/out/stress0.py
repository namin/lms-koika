#!/usr/bin/env python3

import sys
import random

# ISA:
# Registers: ZERO, A0, ... A5

# Instructions:
# addi rd rs1 imm
# add rd rs1 rs2
# br rs1 tag
# target tag

# this file generates a random sequence of instructions
# and writes it to a file. USed to stress test the processor

MAXREGS = 5
BRANCHLIMIT = 200


def genNinst(n: int):
    num_branch_targets = n//10
    ret = ["target entry",
           f"addi {MAXREGS} {MAXREGS} {BRANCHLIMIT}"] + ["nop"] * (n-2)
    targets = [f"target {i}" for i in range(num_branch_targets)]

    for i in range(num_branch_targets):
        idx = random.randint(0, n-1)
        while ret[idx] != "nop":
            idx = random.randint(0, n-1)
        ret[idx] = targets[i]
    ret.append("target exit")

    branch_prelude = [f"brneg {MAXREGS} exit",
                      f"addi {MAXREGS} {MAXREGS} -1"]

    i = 0
    while i < len(ret):
        if ret[i] == "nop":
            cmd = random.randint(0, 100)
            if cmd <= 30:
                rd = random.randint(1, MAXREGS-1)
                rs1 = random.randint(1, MAXREGS-1)
                rs2 = random.randint(1, MAXREGS-1)
                ret[i] = f"add {rd} {rs1} {rs2}"
            elif cmd <= 80:
                rd = random.randint(1, MAXREGS-1)
                rs1 = random.randint(1, MAXREGS-1)
                imm = random.randint(0, 2**16)
                ret[i] = f"addi {rd} {rs1} {imm}"
            elif cmd <= 100:
                target = random.randint(0, num_branch_targets-1)
                reg = random.randint(1, MAXREGS-1)
                branch_type = random.choice(['brneg', 'brnez'])
                ret[i] = f"{branch_type} {reg} {target}"
                for ins in reversed(branch_prelude):
                    ret.insert(i, ins)
                    i += 1
        i += 1
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
