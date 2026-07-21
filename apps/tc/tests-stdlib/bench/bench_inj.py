import subprocess
import time
import sys
import os
import re
import random

"""
About this file:

- it aims to test elpi vs coq performances of
type class search.

- it should be run from the ./apps/tc folder

- parameters of command line:
    * N : the depth of the tree to build in tests/test.v
    * -nocoq : optional to test only elpi
    * -onlyOne : optional to run the test only for the tree of size N. By default, the tests are made for each i in [1..N] included
"""

INJ_BASE_FUN = "f"

TOT_COQ_TIME = "coqT"
TOT_ELPI_TIME = "elpiT"
TOT_NORMALIZE = "normalize"
TOT_COMPILE_CTX = "compile context"
TOT_BUILD_QUERY = "build query"
TOT_INSTANCE_SEARCH = "instance search"
TOT_FULL_INSTANCE_SEARCH = "full instance search"
TOT_REFINE = "refine"
MSOLVE = "msolve"

COMPILT = "compilT"
RUNTIMET = "runtimeT"

KEYL =                               [TOT_COQ_TIME, TOT_ELPI_TIME, TOT_NORMALIZE, TOT_COMPILE_CTX, TOT_BUILD_QUERY, TOT_INSTANCE_SEARCH, TOT_FULL_INSTANCE_SEARCH, TOT_REFINE, MSOLVE, COMPILT,    RUNTIMET]
HEADER = re.sub(r'\s+', ' ', "Height, Coq,          Elpi,          normalize,     ctx,             BuildQuery,      TC search,           TC Search Full,           Refine,     msolve, ElpiCompil, ElpiRuntime, DIFF, Ratio(Coq/Elpi), Ratio(Elpi/Coq)")


def printDict(d):
    # for key in KEYS:
        # d[key] = sum(d[key])/len(d[key])
    # L = [d[k] for k in KEYS]
    L = []
    for k in KEYL: L.append(d[k])
    L.append(d[TOT_ELPI_TIME] - d[MSOLVE])
    L.append(d[TOT_COQ_TIME] / d[TOT_ELPI_TIME])
    L.append(d[TOT_ELPI_TIME] / d[TOT_COQ_TIME] if d[TOT_COQ_TIME] > 0 else 100)
    print(", ".join(map(lambda x: str(round(x, 5)), L)))


def findFloats(s):
    return [float(x) for x in re.findall("\d+\.\d*", s)]


def filterLines(lines):
    with open("xxx.txt", "w") as f:
        f.write(lines)
    DEBUG_STR = "Debug: [TC] - Time of "
    r = {}
    for line in lines.split("\n"):
        fl = findFloats(line)
        if line.startswith("Finished transaction"):
            if TOT_COQ_TIME in r: r[TOT_ELPI_TIME] = fl[0]
            else: r[TOT_COQ_TIME] = fl[0]
        elif line.strip().startswith("Elpi: query-compilation"):
            r[COMPILT] = fl[0]
            r[RUNTIMET] = fl[-1]
        elif line.startswith(DEBUG_STR):
            def check_(n): return line.startswith(DEBUG_STR + n)
            def set_(n): r[n] = fl[0]
            if check_(TOT_NORMALIZE): set_(TOT_NORMALIZE)
            elif check_(TOT_COMPILE_CTX): set_(TOT_COMPILE_CTX)
            elif check_(TOT_BUILD_QUERY): set_(TOT_BUILD_QUERY)
            elif check_(TOT_INSTANCE_SEARCH): set_(TOT_INSTANCE_SEARCH)
            elif check_(TOT_FULL_INSTANCE_SEARCH): set_(TOT_FULL_INSTANCE_SEARCH)
            elif check_(TOT_REFINE): set_(TOT_REFINE)
            elif check_(MSOLVE): set_(MSOLVE)
            else: raise "Not found" + line
    with open("zzz.txt", "w") as f:
        f.write(str(r))
    return r

def buildTree(len):
    if len == 0:
        return INJ_BASE_FUN + " "
    S = buildTree(len-1)
    STR = "(compose " + S + S + ")"
    return STR

accumulate = """
Elpi Accumulate TC_solver lp:{{
  :after "firstHook"
  tc {{:gref Inj}} {{Inj lp:R1 lp:R1 (@compose lp:A lp:A lp:A lp:L lp:R)}} Sol :-
    L = R, !,
    tc {{:gref Inj}} {{Inj lp:R1 lp:R1 lp:L}} InjL,
    Sol = {{@compose_inj lp:A lp:A lp:A lp:R1 lp:R1 lp:R1 lp:L lp:L lp:InjL lp:InjL }}.
}}.
"""

refine_no_check = """
Elpi Accumulate TC.Solver lp:{{
  :after "0"
  tc.refine-proof Proof G GL :- !,
      
    /*********** CHECK IF THE PROOF TYPECHECKS ***********/
    tc.time-it tc.oTC-time-refine (@no-tc! => refine.no_check Proof G GL) "refine.typecheck",
    
    if-true tc.print-solution (coq.say "[TC] The proof typechecks").
}}.
""" if False else ""

def writeFile(fileName: str, composeLen: int, isCoq: bool):
    TXT = f"(* {random.random()} *)\n"
    GOAL = buildTree(composeLen)
    if isCoq:
        TXT += "From elpi_apps_tc_tests_stdlib Require Import stdppInjClassic.\n"
        TXT += f"Goal Inj eq eq({GOAL}). Time apply _. Qed.\n"
    else:
        TXT += "From elpi_apps_tc_tests_stdlib Require Import stdppInj.\n"
        TXT += refine_no_check # (Un)Comment this for using refine or refine.no_check
        TXT += f"Goal Inj eq eq({GOAL}).\n"
        # TXT += "Elpi Command time_it. Elpi Accumulate  lp:{{ main _ :- coq.say {gettimeofday}. }}. Elpi time_it.\n"
        TXT += 'Set Time TC Bench. Set Debug "elpitime".\n'
        TXT += "Time apply _.\n"
        # TXT += "Unset Time TC Bench. Set Debug \"-elpitime\". Elpi time_it.\n"
        TXT += "Qed.\n"
    with open(fileName + ".v", "w") as fd:
        fd.write(TXT)

def runCoqMake(fileName):
    fileName = fileName + ".vo"
    if (os.path.exists(fileName)):
        subprocess.run(["rm", fileName])
    r = subprocess.run(["dune" , "build", fileName], capture_output=True, text=True)
    out = r.stdout
    err = r.stderr
    return f"{out}\n---\n f{err}"


def run(file_name, height):
    def partialFun(isCoq: bool):
        writeFile(file_name, height, isCoq)
        return runCoqMake(file_name)
    return partialFun


def plot_dict(i, d):
    L = [2**i, d[TOT_INSTANCE_SEARCH]]
    L.append(L[-1] + d[TOT_INSTANCE_SEARCH] + d[TOT_BUILD_QUERY] + d[TOT_COMPILE_CTX] + d[TOT_NORMALIZE])
    L.append(L[-1] + d[TOT_REFINE])
    L.append(d[TOT_ELPI_TIME])
    L.append(d[TOT_COQ_TIME])
    return L

def print_plot(pl):
    l = ""
    for i in pl:
        l += ",".join(map(lambda x: str(round(x, 5)), i)) + "\n"
    return l

def loopTreeDepth(file_name: str, maxHeight: int, makeCoq=True, onlyOne=False):
    plot = []
    print(HEADER)
    for i in range(1 if not onlyOne else maxHeight, maxHeight+1):
        FUN = run(file_name, i)
        x = FUN(True) if makeCoq else "Finished transaction in 0.0"
        y = FUN(False)
        print(2**i, ", ", end="", sep="")
        # print("The xx result is " , x)
        dic = filterLines(x + y)
        plot.append(plot_dict(i, dic))
        printDict(dic)
    return plot

if __name__ == "__main__":
    print(os.curdir)
    file_name = "tests-stdlib/bench/bench_inj"
    height = int(sys.argv[1])
    pl = loopTreeDepth(file_name, height, makeCoq=not (
        "-nocoq" in sys.argv), onlyOne=("-onlyOne" in sys.argv))
    
    print("\n\n ELPI STATS")
    print("HEIGHT, TC, BUILD, REFINE, COQ")

    print(print_plot((pl)))
    #writeFile(file_name, 1, False)
