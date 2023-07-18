from collections import defaultdict
from dataclasses import dataclass
from sys import argv, stderr
from tqdm import tqdm
from typing import List
from z3 import And, Implies, Int, Not, Or, Solver

def z3_min(z,x,y):
    return And(Or(Int(repr(z)) == Int(repr(x)), Int(repr(z)) == Int(repr(y))), Int(repr(z)) <= Int(repr(x)), Int(repr(z)) <= Int(repr(y)))

def z3_max(z,x,y):
    return And(Or(Int(repr(z)) == Int(repr(x)), Int(repr(z)) == Int(repr(y))), Int(repr(z)) >= Int(repr(x)), Int(repr(z)) >= Int(repr(y)))

@dataclass(eq=True, frozen=True)
class Comparator:
    idx: int
    top: int
    bot: int
    def __repr__(self):
        return f"C{self.idx}({self.top},{self.bot})"

@dataclass(eq=True, frozen=True)
class Variable:
    channel: int
    step: int
    def __repr__(self):
        return f"X{self.channel}_{self.step}"
    def z3(self):
        return Int(repr(self))
    def vars(self):
        yield self

@dataclass(eq=True, frozen=True)
class Register:
    index: int
    def __repr__(self):
        return f"R{self.index}"
    def z3(self):
        return Int(repr(self))

@dataclass(eq=True, frozen=True)
class Eq:
    left: object
    right: object
    def __repr__(self):
        return f"{repr(self.left)} = {repr(self.right)}"
    def z3(self):
        if type(self.right) == Min:
            return z3_min(self.left, self.right.left, self.right.right)
        elif type(self.right) == Max:
            return z3_max(self.left, self.right.left, self.right.right)
        else:
            return self.left.z3() == self.right.z3()
    def vars(self):
        yield from self.left.vars()
        yield from self.right.vars()

@dataclass(eq=True, frozen=True)
class Min:
    left: object
    right: object
    def __repr__(self):
        return f"min({repr(self.left)},{repr(self.right)})"
    def vars(self):
        yield from self.left.vars()
        yield from self.right.vars()

@dataclass(eq=True, frozen=True)
class Max:
    left: object
    right: object
    def __repr__(self):
        return f"max({repr(self.left)},{repr(self.right)})"
    def vars(self):
        yield from self.left.vars()
        yield from self.right.vars()

@dataclass(eq=True, frozen=True)
class Lesseq:
    left: object
    right: object
    def __repr__(self):
        return f"$lesseq({repr(self.left)},{repr(self.right)})"
    def z3(self):
        return self.left.z3() <= self.right.z3()
    def vars(self):
        yield from self.left.vars()
        yield from self.right.vars()

@dataclass(eq=True, frozen=True)
class Less:
    left: object
    right: object
    def __repr__(self):
        return f"$less({repr(self.left)},{repr(self.right)})"
    def z3(self):
        return self.left.z3() < self.right.z3()
    def vars(self):
        yield from self.left.vars()
        yield from self.right.vars()

@dataclass(eq=True, frozen=True)
class Greatereq:
    left: object
    right: object
    def __repr__(self):
        return f"$greatereq({repr(self.left)},{repr(self.right)})"
    def z3(self):
        return self.left.z3() >= self.right.z3()
    def vars(self):
        yield from self.left.vars()
        yield from self.right.vars()

@dataclass(eq=True, frozen=False)
class Unit:
    x: Register
    y: Register
    z: Register
    has_move: bool
    is_max: bool
    def to(self, target):
        codes = []
        if target == "asm":
            if self.is_max:
                if self.has_move:
                    codes.append(f"mov {self.y} {self.z}")
                codes.append(f"cmp {self.x} {self.y}")
                codes.append(f"cmovge {self.x} {self.z}")
                codes.append(f"cmovge {self.y} {self.x}")
            else:
                if self.has_move:
                    codes.append(f"mov {self.x} {self.z}")
                codes.append(f"cmp {self.x} {self.y}")
                codes.append(f"cmovge {self.y} {self.z}")
                codes.append(f"cmovge {self.x} {self.y}")
        elif target == "C":
            if self.is_max:
                if self.has_move:
                    codes.append(f"int {self.z} = {self.y};")
                codes.append(f"{self.z} = ({self.x} >= {self.y}) ? {self.x} : {self.z};")
                codes.append(f"{self.x} = ({self.x} >= {self.y}) ? {self.y} : {self.x};")
            else:
                if self.has_move:
                    codes.append(f"int {self.z} = {self.x};")
                codes.append(f"{self.z} = ({self.x} >= {self.y}) ? {self.y} : {self.z};")
                codes.append(f"{self.y} = ({self.x} >= {self.y}) ? {self.x} : {self.y};")
        else:
            raise RuntimeError(f"unknown target {repr(target)}")
        return codes

    def length(self, target):
        if target == "asm":
            return 4 if self.has_move else 3
        elif target == "C":
            return 3 if self.has_move else 2
        else:
            raise RuntimeError(f"unknown target {repr(target)}")

    def saved(self, target):
        if target == "asm":
            return 0 if self.has_move else 1
        elif target == "C":
            return 0 if self.has_move else 1
        else:
            raise RuntimeError(f"unknown target {repr(target)}")

    def invars(self):
        yield self.x
        yield self.y

    def outvars(self):
        yield self.x if self.is_max else self.y
        if self.has_move:
            yield self.z

@dataclass(eq=True, frozen=True)
class Program:
    num_channels: Int
    units: List[Unit]
    inputs: List[Register]
    outputs: List[Register]
    target: str
    def append(self, unit):
        self.units.append(unit)
    def to(self):
        codes = []
        if self.target == "asm":
            for unit in self.units:
                codes.extend(unit.to(target))
        elif self.target == "C":
            codes.append(f"void sort_{self.num_channels}(int *a) {{")
            codes.extend([f"    int {r} = a[{i}];" for i, r in enumerate(self.inputs)])
            for unit in self.units:
                codes.extend("    "+code for code in unit.to(target))
            codes.extend([f"    a[{i}] = {r};" for i, r in enumerate(self.outputs)])
            codes.append("}")
        else:
            raise RuntimeError(f"unknown target {repr(target)}")
        return codes
    def length(self):
        if self.target in ("asm", "C"):
            count = 0
            for unit in self.units:
                count += unit.length(target)
            return count
        else:
            raise RuntimeError(f"unknown target {repr(target)}")
    def saved(self):
        if self.target in ("asm", "C"):
            count = 0
            for unit in self.units:
                count += unit.saved(target)
            return count
        else:
            raise RuntimeError(f"unknown target {repr(target)}")

    def reallocate(self):
        live = set(self.outputs)
        lives = [set(live)]
        freeds = []
        for unit in reversed(self.units):
            old_live = set(live)
            live.difference_update(unit.outvars())
            live.update(unit.invars())
            lives[:0] = [set(live)]
            freeds[:0] = [live.difference(old_live)]
        assert live == set(self.inputs)
        freeds[:0] = [set()]
        freed = set()
        repl = {}
        new_units = []
        for i, unit in enumerate(self.units):
            freeds[i] = {repl[r] if r in repl else r for r in freeds[i]}
            lives[i] = {repl[r] if r in repl else r for r in lives[i]}
            freed.update(freeds[i])
            if freed and unit.z not in lives[i]:
                freed = list(freed)
                r, freed = freed[0], set(freed[1:])
                repl[unit.z] = r
            new_x = repl[unit.x] if unit.x in repl else unit.x
            new_y = repl[unit.y] if unit.y in repl else unit.y
            new_z = repl[unit.z] if unit.z in repl else unit.z
            new_units.append(Unit(x=new_x, y=new_y, z=new_z, has_move=unit.has_move, is_max=unit.is_max))
        new_outputs = [repl[r] if r in repl else r for r in self.outputs]
        return Program(num_channels=self.num_channels, units=new_units, inputs=self.inputs, outputs=new_outputs, target=self.target)

    def registers(self):
        return {r for unit in self.units for r in (unit.x, unit.y, unit.z)}

class State:
    def __init__(self, vars=[], regs=[], var2reg=None, reg2var=None, constraints=None):
        self.vars = []
        self.regs = []
        self.var2reg = {}
        self.reg2var = {}
        self.constraints = constraints if constraints is not None else []
        self.extend(vars)
        self.extend(regs)
        if var2reg is not None:
            self.var2reg = var2reg
        if reg2var is not None:
            self.var2reg = reg2var
    def extend(self, varregs):
        for var, reg in varregs:
            self.append(var, reg)
    def append(self, var, reg):
        self.vars.append(var)
        self.regs.append(reg)
        self.var2reg[var] = reg
        self.reg2var[reg] = var
    def replace(self, old_var, new_var, reg):
        del self.var2reg[old_var]
        self.var2reg[new_var] = reg
        self.reg2var[reg] = new_var
        self.vars.append(new_var)
    def record(self, constraint):
        self.constraints.append(constraint)
    def current(self, channel):
        return [var for var in self.vars if var.channel == channel][-1]
    def next(self):
        return Register(len(self.regs))
    def __repr__(self):
        return f"State(vars={self.vars}, regs={self.regs}, var2reg={self.var2reg}, reg2var={self.reg2var}, constraints={self.constraints})"

def run(constraints, extra_constraints, goals):
    constraint = And(*(c.z3() for c in constraints))
    extra_constraint = And(*(c.z3() for c in extra_constraints))
    goal = And(*(c.z3() for c in goals))
    s = Solver()
    s.append(Not(Implies(And(constraint, extra_constraint), goal)))
    r = s.check()
    if debug:
        print(r)
    return r.r == 1, s

def compile(sn, target, do_max, try_min, try_max):
    comps = [Comparator(idx, top, bot) for idx, (top, bot) in enumerate(sn)]
    n = max((y for _,y in sn))+1
    s = State()
    s.extend(((Variable(i,0), Register(i)) for i in range(n)))
    if debug:
        print(f"sn = {sn}", file=stderr)
        print(f"n = {n}", file=stderr)
        print(f"comps = {comps}", file=stderr)
        print(f"s = {s}", file=stderr)
    codes = []
    units = []
    for c in tqdm(comps):
        top_pre_var = s.current(c.top)
        top_post_var = Variable(c.top, c.idx+1)
        bot_pre_var = s.current(c.bot)
        bot_post_var = Variable(c.bot, c.idx+1)
        if debug:
            print(top_pre_var, bot_pre_var, file=stderr)
            print(top_post_var, bot_post_var, file=stderr)
        x = s.var2reg[top_pre_var]
        y = s.var2reg[bot_pre_var]
        keep = True
        is_max = do_max
        for z in s.regs:
            if not try_min:
                continue
            if z not in (x,y):
                if prune:
                    top_pre_constraints = [c for c in s.constraints if type(c) == Eq and c.left == top_pre_var and type(c.right) == Min]
                    if not top_pre_constraints:
                        continue
                    assert len(top_pre_constraints) == 1
                    if not s.reg2var[z] in (top_pre_constraints[0].right.left, top_pre_constraints[0].right.right):
                        continue
                vars = []
                vars.append({top_pre_var, bot_pre_var})# s.reg2var[z]})
                state_constraints = []
                for c in reversed(s.constraints):
                    for i, vs in enumerate(vars):
                        if vs.intersection(c.vars()):
                            if i+1 < len(vars):
                                vars[i+1].update(c.vars())
                            # elif i+1 <= 16:
                            else:
                                vars.append(set(c.vars()))
                            # else:
                            #     break
                            state_constraints.append(c)
                            break
                constraints = list(state_constraints)
                if debug:
                    print("SLICE",len(s.constraints),len(state_constraints))
                # constraints = list(s.constraints)
                constraints.append(Less(x, y))
                constraints.append(Eq(z, s.reg2var[z]))
                constraints.append(Eq(x, top_pre_var))
                constraints.append(Eq(y, bot_pre_var))
                extra_constraints = []#Less(z, y)]
                goals = [Eq(z,Min(x,y))]
                returncode, solver = run(constraints=constraints, extra_constraints=extra_constraints, goals=goals)
                if debug:
                    print("CASE 1:", file=stderr)
                    print(solver.assertions(), file=stderr)
                if returncode:
                    if debug:
                        print(solver.model())
                        print(s.reg2var)
                    continue
                keep = False
                is_max = False
                if True or debug:
                    print("CULLING MIN")
                break
        else:
            for z in s.regs:
                if not try_max:
                    continue
                if z not in (x,y):
                    if prune:
                        bot_pre_constraints = [c for c in s.constraints if type(c) == Eq and c.left == bot_pre_var and type(c.right) == Max]
                        if not bot_pre_constraints:
                            continue
                        assert len(bot_pre_constraints) == 1
                        if not s.reg2var[z] in (bot_pre_constraints[0].right.left, bot_pre_constraints[0].right.right):
                            continue
                    vars = []
                    vars.append({top_pre_var, bot_pre_var})# s.reg2var[z]})
                    state_constraints = []
                    for c in reversed(s.constraints):
                        for i, vs in enumerate(vars):
                            if vs.intersection(c.vars()):
                                if i+1 < len(vars):
                                    vars[i+1].update(c.vars())
                                # elif i+1 <= 16:
                                else:
                                    vars.append(set(c.vars()))
                                # else:
                                #     break
                                state_constraints.append(c)
                                break
                    constraints = list(state_constraints)
                    if debug:
                        print("SLICE",len(s.constraints),len(state_constraints))
                    # constraints = list(s.constraints)
                    constraints.append(Less(x, y))
                    constraints.append(Eq(z, s.reg2var[z]))
                    constraints.append(Eq(x, top_pre_var))
                    constraints.append(Eq(y, bot_pre_var))
                    extra_constraints = []
                    goals = [Eq(z,Max(x,y))]
                    returncode, solver = run(constraints=constraints, extra_constraints=extra_constraints, goals=goals)
                    if debug:
                        print("CASE 1:", file=stderr)
                        print(solver.assertions(), file=stderr)
                    if returncode:
                        if debug:
                            print(solver.model())
                        continue
                    keep = False
                    is_max = True
                    if True or debug:
                        print("CULLING MAX")
                    break
            else:
                z = s.next()
        units.append(Unit(x=x,y=y,z=z,has_move=keep,is_max=is_max))
        if is_max:
            s.replace(top_pre_var, top_post_var, x)
            s.append(bot_post_var, z)
        else:
            s.replace(bot_pre_var, bot_post_var, y)
            s.append(top_post_var, z)
        s.record(Eq(top_post_var, Min(top_pre_var, bot_pre_var)))
        s.record(Eq(bot_post_var, Max(top_pre_var, bot_pre_var)))
        s.record(Lesseq(top_post_var, bot_post_var))
        if debug:
            print(s.constraints, file=stderr)
            print(codes, file=stderr)
            print(f"s = {s}", file=stderr)
    inputs = [Register(i) for i in range(n)]
    outputs = [s.var2reg[s.current(i)] for i in range(n)]
    prog = Program(num_channels=n, units=units, inputs=inputs, outputs=outputs, target=target)
    return prog

debug = False
prune = True
target = "C"
n_from, n_to = int(argv[1]), int(argv[2])
sn_type = argv[3]
from sn import sn
sn[3]["mirrored"] = [(0,1), (0,2), (1,2)]
# sn = defaultdict(dict)
# sn[2][sn_type] = [(0, 1)]
# sn[3][sn_type] = [(1, 2), (0, 2), (0, 1)]
# sn[4][sn_type] = [(0, 1), (2, 3), (0, 2), (1, 3), (1, 2)]
# sn[5][sn_type] = [(0, 1), (3, 4), (2, 4), (2, 3), (1, 4), (0, 3), (0, 2), (1, 3), (1, 2)]
# sn[6][sn_type] = [(1, 2), (4, 5), (0, 2), (3, 5), (0, 1), (3, 4), (2, 5), (0, 3), (1, 4), (2, 4), (1, 3), (2, 3)]
# sn[7][sn_type] = [(1, 2), (3, 4), (5, 6), (0, 2), (3, 5), (4, 6), (0, 1), (4, 5), (2, 6), (0, 4), (1, 5), (0, 3), (2, 5), (1, 3), (2, 4), (2, 3)]
# sn[8][sn_type] = [(0, 1), (2, 3), (4, 5), (6, 7), (0, 2), (1, 3), (4, 6), (5, 7), (1, 2), (5, 6), (0, 4), (3, 7), (1, 5), (2, 6), (1, 4), (3, 6), (2, 4), (3, 5), (3, 4)]
# sn[9][sn_type] = [(0, 1), (3, 4), (6, 7), (1, 2), (4, 5), (7, 8), (0, 1), (3, 4), (6, 7), (2, 5), (0, 3), (1, 4), (5, 8), (3, 6), (4, 7), (2, 5), (0, 3), (1, 4), (5, 7), (2, 6), (1, 3), (4, 6), (2, 4), (5, 6), (2, 3)]
# sn[10][sn_type] = [(4, 9), (3, 8), (2, 7), (1, 6), (0, 5), (1, 4), (6, 9), (0, 3), (5, 8), (0, 2), (3, 6), (7, 9), (0, 1), (2, 4), (5, 7), (8, 9), (1, 2), (4, 6), (7, 8), (3, 5), (2, 5), (6, 8), (1, 3), (4, 7), (2, 3), (6, 7), (3, 4), (5, 6), (4, 5)]
# sn[11][sn_type] = [(0, 1), (2, 3), (4, 5), (6, 7), (8, 9), (1, 3), (5, 7), (0, 2), (4, 6), (8, 10), (1, 2), (5, 6), (9, 10), (0, 4), (3, 7), (1, 5), (6, 10), (4, 8), (5, 9), (2, 6), (0, 4), (3, 8), (1, 5), (6, 10), (2, 3), (8, 9), (1, 4), (7, 10), (3, 5), (6, 8), (2, 4), (7, 9), (5, 6), (3, 4), (7, 8)]
# sn[12][sn_type] = [(0, 1), (2, 3), (4, 5), (6, 7), (8, 9), (10, 11), (1, 3), (5, 7), (9, 11), (0, 2), (4, 6), (8, 10), (1, 2), (5, 6), (9, 10), (0, 4), (7, 11), (1, 5), (6, 10), (3, 7), (4, 8), (5, 9), (2, 6), (0, 4), (7, 11), (3, 8), (1, 5), (6, 10), (2, 3), (8, 9), (1, 4), (7, 10), (3, 5), (6, 8), (2, 4), (7, 9), (5, 6), (3, 4), (7, 8)]
# sn[13][sn_type] = [(1, 7), (9, 11), (3, 4), (5, 8), (0, 12), (2, 6), (0, 1), (2, 3), (4, 6), (8, 11), (7, 12), (5, 9), (0, 2), (3, 7), (10, 11), (1, 4), (6, 12), (7, 8), (11, 12), (4, 9), (6, 10), (3, 4), (5, 6), (8, 9), (10, 11), (1, 7), (2, 6), (9, 11), (1, 3), (4, 7), (8, 10), (0, 5), (2, 5), (6, 8), (9, 10), (1, 2), (3, 5), (7, 8), (4, 6), (2, 3), (4, 5), (6, 7), (8, 9), (3, 4), (5, 6)]
# sn[14][sn_type] = [(0, 1), (2, 3), (4, 5), (6, 7), (8, 9), (10, 11), (12, 13), (0, 2), (4, 6), (8, 10), (1, 3), (5, 7), (9, 11), (0, 4), (8, 12), (1, 5), (9, 13), (2, 6), (3, 7), (0, 8), (1, 9), (2, 10), (3, 11), (4, 12), (5, 13), (5, 10), (6, 9), (3, 12), (7, 11), (1, 2), (4, 8), (1, 4), (7, 13), (2, 8), (5, 6), (9, 10), (2, 4), (11, 13), (3, 8), (7, 12), (6, 8), (10, 12), (3, 5), (7, 9), (3, 4), (5, 6), (7, 8), (9, 10), (11, 12), (6, 7), (8, 9)]
# sn[15][sn_type] = [(0, 1), (2, 3), (4, 5), (6, 7), (8, 9), (10, 11), (12, 13), (0, 2), (4, 6), (8, 10), (12, 14), (1, 3), (5, 7), (9, 11), (0, 4), (8, 12), (1, 5), (9, 13), (2, 6), (10, 14), (3, 7), (0, 8), (1, 9), (2, 10), (3, 11), (4, 12), (5, 13), (6, 14), (5, 10), (6, 9), (3, 12), (13, 14), (7, 11), (1, 2), (4, 8), (1, 4), (7, 13), (2, 8), (11, 14), (5, 6), (9, 10), (2, 4), (11, 13), (3, 8), (7, 12), (6, 8), (10, 12), (3, 5), (7, 9), (3, 4), (5, 6), (7, 8), (9, 10), (11, 12), (6, 7), (8, 9)]
# sn[16][sn_type] = [(0, 1), (2, 3), (4, 5), (6, 7), (8, 9), (10, 11), (12, 13), (14, 15), (0, 2), (4, 6), (8, 10), (12, 14), (1, 3), (5, 7), (9, 11), (13, 15), (0, 4), (8, 12), (1, 5), (9, 13), (2, 6), (10, 14), (3, 7), (11, 15), (0, 8), (1, 9), (2, 10), (3, 11), (4, 12), (5, 13), (6, 14), (7, 15), (5, 10), (6, 9), (3, 12), (13, 14), (7, 11), (1, 2), (4, 8), (1, 4), (7, 13), (2, 8), (11, 14), (5, 6), (9, 10), (2, 4), (11, 13), (3, 8), (7, 12), (6, 8), (10, 12), (3, 5), (7, 9), (3, 4), (5, 6), (7, 8), (9, 10), (11, 12), (6, 7), (8, 9)]
if __name__ == "__main__":
    for i in range(n_from,n_to+1):
        sn_types = [sn_type] if sn_type != "all" else sn[i].keys()
        for snt in sn_types:
            comps = sn[i][snt]
            print(comps)
            for do_max in False, True:
                for try_min in False, True:
                    for try_max in False, True:
                        prog = compile(comps, target, do_max, try_min, try_max)
                        prog = prog.reallocate()
                        print("\n".join(prog.to()))
                        print("!", i, snt, do_max, try_min, try_max, prog.length(), prog.saved(), len(prog.registers()))
