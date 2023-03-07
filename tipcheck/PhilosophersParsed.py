from typing import List, Tuple
from transition_system import TransitionSystem, Synchronisation
from transition_system_circuits import SynchCircuit, process_system
from wmod_parser import read_wmod_file
from pyeda.inter import And, Not
from pyeda.boolalg import Expr
import itertools


# Dining philosophers
# --------------------

# possible values of nbrPhils: 5, 10
nbrPhils = 5

# possible values of nbrSteps: 10, 50, 100, 200, 500, 1000
nbrSteps = 100

def file_name_i(i: int, j: int) -> str:
    return f"Examples/HVC2017/EDP{i}_{j}.wmod"

file_name = file_name_i(nbrPhils, nbrSteps)

def phil_synch() -> Synchronisation:
    return read_wmod_file(file_name)


# Defining the circuits
# ----------------------

def phils_sc() -> SynchCircuit:
    ps = phil_synch()
    return process_system(ps)


def is_held(sc: SynchCircuit, f: int) -> Expr:
    return sc.loc(f"Fork:{f}") == "1"


def is_thinking(sc: SynchCircuit, p: int) -> Expr:
    return sc.loc(f"Philo:{p}") == "think"


def uncontr_block(sc: SynchCircuit) -> Expr:
    return And(*[And(is_held(sc, p), is_thinking(sc, p)) for p in range(2, nbrPhils + 1, 2)])


def any_error(sc: SynchCircuit) -> Expr:
    return Or(*(Not(tran) for tran in sc.all_trans()))


def phils_props(sc: SynchCircuit) -> Tuple[List[Expr], List[Expr], List[Expr]]:
    even_phils = range(2, nbrPhils + 1, 2)
    uncontr_blocks = [uncontr_block(sc)]
    bad = uncontr_block(sc)

    props = (
        [Not(any_error(sc))],
        [Expr.all_terms(sc.all_controllable_trans()), bad],
        []
    )

    return props


def phils_c(sc: SynchCircuit) -> Expr:
    always, nevers, finites = phils_props(sc)

    prop_expr = (
        And(*always),
        Not(And(*[Or(*t) for t in itertools.product(*nevers)])),
        And(*finites)
    )

    return And(*prop_expr)


def main() -> Expr:
    sc = phils_sc()
    circ = phils_c(sc)

    with open(f"Examples/phils{nbrPhils}_{nbrSteps}.blif", "w") as f:
        f.write(circ.to_blif())

    return circ

