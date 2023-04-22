import subprocess
import time
import sys
import os
import re

INJ_BASE_FUN = "f"
KEYS = "coqT, refineT, compilT, runtimeT, elpiT".split(", ")


def buildDict():
    res = dict()
    for key in KEYS:
        res[key] = []
    return res


def printDict(d):
    for key in KEYS:
        d[key] = sum(d[key])/len(d[key])
    L = [d[k] for k in KEYS]
    L.append(d["elpiT"] - d["refineT"])
    L.append(d["coqT"] / d["elpiT"])
    print(", ".join(map(lambda x: str(round(x, 4)), L)))


def findFloats(s):
    return [float(x) for x in re.findall("\d+\.\d+", s)]


def filterLines(lines):
    validStarts = ["Finished", "Refine", "[elpitime]"]
    for line in lines.split("\n"):
        for start in validStarts:
            if line.startswith(start):
                yield line


def parseFile(s):
    lines = [findFloats(x) for x in filterLines(s)]
    coqT = lines[0][0]
    refineT = lines[1][0]
    elpiStats = lines[2]
    compilT, runtimeT = elpiStats[0], elpiStats[-1]
    elpiT = lines[3][0]
    res = buildDict()
    for key in KEYS:
        res[key].append(eval(key))
    return res


def buildTree(len):
    if len == 0:
        return INJ_BASE_FUN + " "
    S = buildTree(len-1)
    STR = "(compose " + S + S + ")"
    return STR


def writeFile(fileName: str, composeLen: int, isCoq: bool):
    PREAMBLE = f"""\
From elpi.apps.tc.tests Require Import stdppInj.
From Coq Require Import Setoid.
Elpi Debug "time-refine".
Set Debug "elpitime".
{"Elpi Override TC TC_check Only Equiv." if isCoq else ""}
"""
    GOAL = buildTree(composeLen)
    with open(fileName + ".v", "w") as fd:
        fd.write(PREAMBLE)
        fd.write(f"Goal Inj eq eq({GOAL}). Time apply _. Qed.\n")


def runCoqMake(fileName):
    fileName = fileName + ".vo"
    subprocess.run(["rm", fileName])
    return subprocess.check_output(["make", fileName]).decode()


def run(file_name, height):
    def partialFun(isCoq: bool):
        writeFile(file_name, height, isCoq)
        return runCoqMake(file_name)
    return partialFun


def loopTreeDepth(file_name: str, maxHeight: int, makeCoq=True, onlyOne=False):
    print("Height, Coq, Refine, ElpiCompil, ElpiRuntime, Elpi, ElpiNoRefine, Ratio(Coq/Elpi)")
    for i in range(1 if not onlyOne else maxHeight, maxHeight+1):
        FUN = run(file_name, i)
        x = FUN(True) if makeCoq else "Finished 0.0"
        y = FUN(False)
        print(i, ", ", end="", sep="")
        dic = parseFile(x + y)
        printDict(dic)


if __name__ == "__main__":
    print(os.curdir)
    file_name = "tests/test"
    height = int(sys.argv[1])
    loopTreeDepth(file_name, height, makeCoq=not (
        "-nocoq" in sys.argv), onlyOne=("-onlyOne" in sys.argv))
