import subprocess
import time
import sys, os

STDOUT = "/dev/null"
DEVNULL = open(STDOUT, "w")
INJ_BASE_FUN = "f"

# Set Debug "elpitime".

def buildTree(len):
    if len == 0:
        return INJ_BASE_FUN + " "
    S = buildTree(len-1)
    STR = "(compose " + S + S + ")"
    return STR


def writeFile(fileName: str, composeLen: int, isCoq: bool, time: int):
    PREAMBLE = """\
From elpi.apps.tc Require Import stdpp.stdppInj.
From Coq Require Import Setoid.
"""
    if isCoq:
        PREAMBLE += "\nElpi Override TC TC_check Only Equiv.\n"
    GOAL = buildTree(composeLen)
    with open(fileName + ".v", "w") as fd:
        fd.write(PREAMBLE)
        for i in range(time):
            fd.write(f"Goal Inj eq eq({GOAL}). apply _. Qed.\n")


def runCoqMake(fileName):
    fileName = fileName + ".vo"
    subprocess.run(["rm", fileName])
    subprocess.run(["make", fileName], stdout=DEVNULL)


def run(file_name, height, loop_nb):
    def partialFun(isCoq: bool):
        writeFile(file_name, height, isCoq, loop_nb)
        startTime = time.time()
        runCoqMake(file_name)
        return time.time() - startTime
    return partialFun


def loopTreeDepth(file_name: str, loop_nb: int, maxHeight: int):
    print("Height, Elpi, Coq, Ratio(Elpi/Coq)")
    for i in range(maxHeight, maxHeight+1):
        FUN = run(file_name, i, loop_nb)
        T_Coq = FUN(True)
        T_Elpi = FUN(False)
        print(i, T_Elpi, T_Coq, T_Coq/T_Elpi, sep=", ")


if __name__ == "__main__":
    print(os.curdir)
    file_name = "tc/stdpp/test"
    height = int(sys.argv[1])
    loop_nb = int(sys.argv[2])
    loopTreeDepth(file_name, loop_nb, height)
