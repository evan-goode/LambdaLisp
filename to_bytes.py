#!/usr/bin/env python3

import re
import sys

def dbn_to_bitstring(dbn: str) -> str:
    # fortified version of Justine's compile.sh

    binary = []

    while dbn:
        char = dbn[0]
        if char == "λ":
            binary.extend("00")
            dbn = dbn[1:]
        elif char == "[":
            binary.extend("01")
            dbn = dbn[1:]
        elif index_match := re.search(r"^(\d+)(.*)", dbn):
            index = int(index_match.group(1))
            remainder = index_match.group(2)
            binary.extend((index * "1") + "10")
            dbn = remainder
        else:
            dbn = dbn[1:]

    return "".join(binary)

if __name__ == "__main__":
    print(dbn_to_bitstring(sys.stdin.read()), end="")
