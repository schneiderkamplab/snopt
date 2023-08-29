import click
from dataclasses import dataclass
from nnf import Var, true as nnf_true
from os import chdir, system
from re import match
from sn import sn
from sys import argv, stderr, setrecursionlimit
from time import process_time
from tqdm import tqdm
from typing import List
from z3 import And, Implies, Int, Not, Or, Solver

setrecursionlimit(10**6)

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
    def nnf(self):
        return Var(repr(self))
    def z3(self):
        return Int(repr(self))
    def tex(self):
        return f"X^{{{self.channel}}}_{{{self.step}}}"
    def vars(self):
        yield self

@dataclass(eq=True, frozen=True)
class Register:
    index: int
    def __repr__(self):
        return f"R{self.index}"
    def nnf(self):
        return Var(repr(self))
    def z3(self):
        return Int(repr(self))
    def __lt__(self, other):
        return self.index < other.index
    def vars(self):
        yield self

class Constraint:
    pass

@dataclass(eq=True, frozen=True)
class Eq(Constraint):
    left: object
    right: object
    def __repr__(self):
        return f"{repr(self.left)} = {repr(self.right)}"
    def nnf(self):
        left = self.left.nnf()
        right = self.right.nnf()
        return (left | right.negate()) & (left.negate() | right)
    def z3(self):
        if type(self.right) == Min:
            return z3_min(self.left, self.right.left, self.right.right)
        elif type(self.right) == Max:
            return z3_max(self.left, self.right.left, self.right.right)
        else:
            return self.left.z3() == self.right.z3()
    def tex(self):
        return f"{self.left.tex()} = {self.right.tex()}"
    def vars(self):
        yield from self.left.vars()
        yield from self.right.vars()

@dataclass(eq=True, frozen=True)
class Min:
    left: object
    right: object
    def __repr__(self):
        return f"min({repr(self.left)},{repr(self.right)})"
    def nnf(self):
        return self.left.nnf() & self.right.nnf()
    def tex(self):
        return f"\min({self.left.tex()},{self.right.tex()})"
    def vars(self):
        yield from self.left.vars()
        yield from self.right.vars()

@dataclass(eq=True, frozen=True)
class Max:
    left: object
    right: object
    def __repr__(self):
        return f"max({repr(self.left)},{repr(self.right)})"
    def nnf(self):
        return self.left.nnf() | self.right.nnf()
    def tex(self):
        return f"\max({self.left.tex()},{self.right.tex()})"
    def vars(self):
        yield from self.left.vars()
        yield from self.right.vars()

@dataclass(eq=True, frozen=True)
class Lesseq(Constraint):
    left: object
    right: object
    def __repr__(self):
        return f"$lesseq({repr(self.left)},{repr(self.right)})"
    def nnf(self):
        return self.left.nnf().negate() | self.right.nnf()
    def z3(self):
        return self.left.z3() <= self.right.z3()
    def tex(self):
        return f"{self.left.tex()} \leq {self.right.tex()}"
    def vars(self):
        yield from self.left.vars()
        yield from self.right.vars()

@dataclass(eq=True, frozen=True)
class Less(Constraint):
    left: object
    right: object
    def __repr__(self):
        return f"$less({repr(self.left)},{repr(self.right)})"
    def nnf(self):
        return self.left.nnf().negate() & self.right.nnf()
    def z3(self):
        return self.left.z3() < self.right.z3()
    def tex(self):
        return f"{self.left.tex()} < {self.right.tex()}"
    def vars(self):
        yield from self.left.vars()
        yield from self.right.vars()

@dataclass(eq=True, frozen=True)
class Greatereq(Constraint):
    left: object
    right: object
    def __repr__(self):
        return f"$greatereq({repr(self.left)},{repr(self.right)})"
    def nnf(self):
        return self.left.nnf() | self.right.nnf().negate()
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
        elif target == "py":
            if self.is_max:
                if self.has_move:
                    codes.append(f"{self.z} = {self.y}")
                codes.append(f"{self.z} = {self.x} if {self.x} >= {self.y} else {self.z}")
                codes.append(f"{self.x} = {self.y} if {self.x} >= {self.y} else {self.x}")
            else:
                if self.has_move:
                    codes.append(f"{self.z} = {self.x};")
                codes.append(f"{self.z} = {self.y} if {self.x} >= {self.y} else {self.z}")
                codes.append(f"{self.y} = {self.x} if {self.x} >= {self.y} else {self.y}")
        else:
            raise RuntimeError(f"unknown target {repr(target)}")
        return codes

    def length(self, target):
        if target == "asm":
            return 4 if self.has_move else 3
        elif target in ("C", "py"):
            return 3 if self.has_move else 2
        else:
            raise RuntimeError(f"unknown target {repr(target)}")

    def saved(self, target):
        if target in ("asm", "C", "py"):
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

@dataclass(eq=True, frozen=False)
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
                codes.extend(unit.to(self.target))
        elif self.target == "C":
            codes.append(f"void sort_{self.num_channels}(int *a) {{")
            codes.extend([f"    int {r} = a[{i}];" for i, r in enumerate(self.inputs)])
            for unit in self.units:
                codes.extend("    "+code for code in unit.to(self.target))
            codes.extend([f"    a[{i}] = {r};" for i, r in enumerate(self.outputs)])
            codes.append("}")
        elif self.target == "py":
            codes.append(f"def sort_{self.num_channels}(a):")
            codes.extend([f"    {r} = a[{i}]" for i, r in enumerate(self.inputs)])
            for unit in self.units:
                codes.extend("    "+code for code in unit.to(self.target))
            codes.extend([f"    a[{i}] = {r}" for i, r in enumerate(self.outputs)])
            codes.append(f"""if __name__ == '__main__':
    from random import randint
    from sys import argv
    num_loops = int(argv[1]) if len(argv) > 1 else -1
    count_loops = 0
    count_errors = 0
    try:
        while num_loops != 0:
            a = [randint(0,{self.num_channels}**2-1) for i in range({self.num_channels})]
            b = list(a)
            sort_{self.num_channels}(a)
            if sorted(a) != a:
                print(b, a)
                count_errors += 1
            count_loops += 1
            num_loops -= 1
    except KeyboardInterrupt:
        pass
    print(count_errors,"errors out of",count_loops)""")
        return codes
    def length(self):
        count = 0
        for unit in self.units:
            count += unit.length(self.target)
        return count
    def saved(self):
        count = 0
        for unit in self.units:
            count += unit.saved(self.target)
        return count

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
        if VERBOSE > 3:
            for i in range(len(self.units)):
                print(sorted(lives[i]), sorted(freeds[i]), file=stderr)
        freed = set()
        repl = {}
        new_units = []
        for i, unit in enumerate(self.units):
            freeds[i] = {repl[r] if r in repl else r for r in freeds[i]}
            lives[i] = {repl[r] if r in repl else r for r in lives[i]}
            freed.update(freeds[i])
            if VERBOSE > 3:
                print(lives[i], file=stderr)
            old_z = repl[unit.z] if unit.z in repl else unit.z
            if freed and old_z not in lives[i]:
                freed = list(freed)
                r, freed = freed[0], set(freed[1:])
                repl[old_z] = r
            if VERBOSE > 3:
                print(unit, file=stderr)
            new_x = repl[unit.x] if unit.x in repl else unit.x
            new_y = repl[unit.y] if unit.y in repl else unit.y
            new_z = repl[unit.z] if unit.z in repl else unit.z
            new_units.append(Unit(x=new_x, y=new_y, z=new_z, has_move=unit.has_move, is_max=unit.is_max))
            if VERBOSE > 3:
                print(new_units[-1], file=stderr)
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

class NNFWrapper:
    def __init__(self, assertions, model) -> None:
        self._assertions = assertions
        self._model = model
    def assertions(self):
        return self.assertions
    def model(self):
        return self.model

def run(constraints, goal, zero_one, backend, prune, fallback):
    if backend == "sat":
        constraint = nnf_true
        for c in constraints:
            constraint &= c.nnf()
        f = (constraint.negate() | goal.nnf()).negate()
        r = f.solve()
        if r is not None:
            return True, NNFWrapper(f, r), None
        elif prune or not fallback:
            return False, NNFWrapper(f, "UNSAT"), None
        if VERBOSE > 2:
            print("UNSAT but no prune - deferring to z3", file=stderr)
        backend = "z3"
    assert backend == "z3"
    neg_goal_z3 = Not(goal.z3())
    s = Solver()
    s.set(unsat_core=True)
    s.set('core.minimize', True)
    for i in range(len(constraints)):
        s.assert_and_track(constraints[i].z3(), f'c{i}')
    s.assert_and_track(neg_goal_z3, 'g')
    r = s.check()
    if VERBOSE > 3:
        print(r, file=stderr)
    u = None
    if r.r == -1:
        id2c = {}
        for i in range(len(constraints)):
            id2c[f'c{i}'] = constraints[i]
        id2c['g'] = goal
        core = s.unsat_core()
        u = [id2c[str(x)] for x in core]
    if zero_one and r.r == 1:
        vars = {var.z3() for cs in (constraints, [goal]) for c in cs for var in c.vars()}
        for var in vars:
            s.append(And(var >= 0, var <= 1))
        r = s.check()
        if r.r != 1:
            print(constraints, goal, file=stderr)
            assert False
    return r.r == 1, s, u

def visualize_unsat_core(n: int, comp: Comparator, comps: List[Comparator], core: List[Constraint], s: State):
    mark_channel = {}
    mark_comp = {comp: "red"}
    cs, cols = [], []
    for c in core:
        if isinstance(c, Eq) and isinstance(c.left, Register) and (isinstance(c.right, Min) or isinstance(c.right, Max)):
            var = s.reg2var[c.left]
            mark_channel[var] = "orange"
            goal = Eq(var, Min(s.reg2var[c.right.left], s.reg2var[c.right.right]))
        elif isinstance(c, Lesseq):
            mark_channel[c.left] = "blue"
            mark_channel[c.right] = "blue"
            comp_i = Comparator(c.left.step-1, c.left.channel, c.right.channel)
            mark_comp[comp_i] = "blue"
            cs.append(c)
            cols.append("blue")
        elif isinstance(c, Eq) and isinstance(c.left, Variable) and isinstance(c.right, Min):
            mark_channel[c.left] = "teal"
            comp_i = Comparator(c.left.step-1, c.right.left.channel, c.right.right.channel)
            mark_comp[comp_i] = "teal"
            cs.append(c)
            cols.append("teal")
        elif isinstance(c, Eq) and isinstance(c.left, Variable) and isinstance(c.right, Max):
            mark_channel[c.left] = "pink"
            comp_i = Comparator(c.left.step-1, c.right.left.channel, c.right.right.channel)
            mark_comp[comp_i] = "pink"
            cs.append(c)
            cols.append("pink")
        elif isinstance(c, Less) and isinstance(c.left, Register) and isinstance(c.right, Register):
            cs.append(Less(s.reg2var[c.left], s.reg2var[c.right]))
            cols.append("red")
    lines = []
    channels_direct = set()
    channels_indirect = set()
    layer_from = 0
    if any((Variable(j, 0) in mark_channel for j in range(n))):
        lines.append("\\nodelabel{"+",".join((f"\\tiny $\\textcolor{{{mark_channel[v]}}}{{{v.tex()}}}$" if v in mark_channel else "") for v in (Variable(j, 0) for j in range(n)))+"}")
        lines.append("\\addlayer")
    for i in range(len(comps)):
        lines.append(f"\\addcomparator[{mark_comp[comps[i]] if comps[i] in mark_comp else 'black'}]{{{comps[i].top+1}}}{{{comps[i].bot+1}}}")
        if i+1 < len(comps):
            if VERBOSE > 4:
                print(comps[i].bot, comps[i].top+1, file=stderr)
            channels_direct.add(comps[i].top)
            channels_direct.add(comps[i].bot)
            for j in range(comps[i].top+1, comps[i].bot):
                channels_indirect.add(j)
            if VERBOSE > 4:
                print(channels_direct,channels_indirect,comps[i],comps[i+1], file=stderr)
            for k in (comps[i+1].top, comps[i+1].bot):
                if k in channels_direct:
                    channels_direct.clear()
                    channels_indirect.clear()
                    layer_added = False
                    for l in range(layer_from+1,i+2):
                        if any((Variable(j, l) in mark_channel for j in range(n))):
                            if not layer_added:
                                lines.append("\\addlayer")
                                layer_added = True
                            lines.append("\\nodelabel{"+",".join((f"\\tiny $\\textcolor{{{mark_channel[v]}}}{{{v.tex()}}}$" if v in mark_channel else "") for v in (Variable(j, l) for j in range(n)))+"}")
                    layer_from = i+1
                    lines.append("\\nextlayer")
                    if VERBOSE > 4:
                        print("=================")
                    break
            if channels_direct:
                for k in range(comps[i+1].top+1, comps[i+1].bot):
                    if k in channels_direct or k in channels_direct:
                        channels_indirect.clear()
                        lines.append("\\addlayer")
                        if VERBOSE > 4:
                            print("-----------------")
                        break
    template1 = r"""\begin{figure}[t]
\centering
\begin{scaletikzpicturetowidth}{\textwidth}
\begin{sortingnetwork}{"""
    template2 = r"""
\end{sortingnetwork}
\end{scaletikzpicturetowidth}
  \caption{$"""
    template3 = r"""$}
\end{figure}
"""
    formula = " \wedge ".join(f"\\textcolor{{{col}}}{{{c.tex()}}}" for c,col in zip(cs,cols)) + f" \\rightarrow \\textcolor{{orange}}{{{goal.tex()}}}"
    return f"{template1}{n}}}\n"+"\n".join(lines)+template2+formula+template3

def compile(sn, target, do_max, try_min, try_max, prune, slice, zero_one, backend, fallback, visualize_core):
    comps = [Comparator(idx, top, bot) for idx, (top, bot) in enumerate(sn)]
    n = max((y for _,y in sn))+1
    s = State()
    s.extend(((Variable(i,0), Register(i)) for i in range(n)))
    if VERBOSE > 2:
        print(f"sn = {sn}", file=stderr)
        print(f"n = {n}", file=stderr)
        print(f"comps = {comps}", file=stderr)
        print(f"s = {s}", file=stderr)
    codes = []
    units = []
    cores = []
    for comp in tqdm(comps):
        top_pre_var = s.current(comp.top)
        top_post_var = Variable(comp.top, comp.idx+1)
        bot_pre_var = s.current(comp.bot)
        bot_post_var = Variable(comp.bot, comp.idx+1)
        if VERBOSE > 3:
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
                if slice:
                    vars = []
                    vars.append({top_pre_var, bot_pre_var})
                    state_constraints = []
                    for c in reversed(s.constraints):
                        for i, vs in enumerate(vars):
                            if vs.intersection(c.vars()):
                                if i+1 < len(vars):
                                    vars[i+1].update(c.vars())
                                elif slice == -1 or i+1 <= slice:
                                    vars.append(set(c.vars()))
                                else:
                                    break
                                state_constraints.append(c)
                                break
                    constraints = list(state_constraints)
                    if VERBOSE > 2:
                        print("SLICE",len(s.constraints),len(state_constraints), file=stderr)
                else:
                    constraints = list(s.constraints)
                constraints.append(Less(x, y))
                constraints.append(Eq(z, s.reg2var[z]))
                constraints.append(Eq(x, top_pre_var))
                constraints.append(Eq(y, bot_pre_var))
                goal = Eq(z,Min(x,y))
                returncode, solver, core = run(constraints=constraints, goal=goal, zero_one=zero_one, backend=backend, prune=prune, fallback=fallback)
                if VERBOSE > 2:
                    print("CASE 1:", file=stderr)
                    print(solver.assertions(), file=stderr)
                if returncode:
                    if VERBOSE > 2:
                        print(solver.model(), file=stderr)
                        print(s.reg2var, file=stderr)
                    continue
                if not returncode and visualize_core:
                    if not core:
                        if VERBOSE > 1:
                            print("no core to visualize")
                    else:
                        cores.append(visualize_unsat_core(n, comp, comps, core, s))
                keep = False
                is_max = False
                if VERBOSE > 1:
                    print("CULLING MIN", file=stderr)
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
                    if slice:
                        vars = []
                        vars.append({top_pre_var, bot_pre_var})
                        state_constraints = []
                        for c in reversed(s.constraints):
                            for i, vs in enumerate(vars):
                                if vs.intersection(c.vars()):
                                    if i+1 < len(vars):
                                        vars[i+1].update(c.vars())
                                    elif slice == -1 or i+1 <= slice:
                                        vars.append(set(c.vars()))
                                    else:
                                        break
                                    state_constraints.append(c)
                                    break
                        constraints = list(state_constraints)
                        if VERBOSE > 2:
                            print("SLICE",len(s.constraints),len(state_constraints), file=stderr)
                    else:
                        constraints = list(s.constraints)
                    constraints.append(Less(x, y))
                    constraints.append(Eq(z, s.reg2var[z]))
                    constraints.append(Eq(x, top_pre_var))
                    constraints.append(Eq(y, bot_pre_var))
                    goal = Eq(z,Max(x,y))
                    returncode, solver, core = run(constraints=constraints, goal=goal, zero_one=zero_one, backend=backend, prune=prune, fallback=fallback)
                    if VERBOSE > 2:
                        print("CASE 1:", file=stderr)
                        print(solver.assertions(), file=stderr)
                    if returncode:
                        if VERBOSE > 2:
                            print(solver.model(), file=stderr)
                            print(s.reg2var, file=stderr)
                        continue
                    if not returncode and visualize_core:
                        if not core:
                            if VERBOSE > 1:
                                print("no core to visualize")
                        else:
                            cores.append(visualize_unsat_core(n, comp, comps, core, s))
                    keep = False
                    is_max = True
                    if VERBOSE > 1:
                        print("CULLING MAX", file=stderr)
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
        if VERBOSE > 1:
            print(s.constraints, file=stderr)
            print(codes, file=stderr)
            print(f"s = {s}", file=stderr)
    inputs = [Register(i) for i in range(n)]
    outputs = [s.var2reg[s.current(i)] for i in range(n)]
    prog = Program(num_channels=n, units=units, inputs=inputs, outputs=outputs, target=target)
    return prog, cores

TARGETS = ["asm", "C", "py"]
BACKENDS = ["sat", "z3"]
VERBOSE = 0

@click.command()
#parameters
@click.option("--prune", type=bool, multiple=True, default=[True])
@click.option("--slice", type=click.IntRange(min=-1), multiple=True, default=[-1])
@click.option("--sn-type", "-s", type=str, multiple=True, default=['%'])
@click.option("--from", "-f", "from_", type=click.IntRange(min=2), default=3)
@click.option("--to", "-t", type=click.IntRange(min=2), default=8)
@click.option("--do-max", type=bool, multiple=True, default=[False])
@click.option("--try-min", type=bool, multiple=True, default=[True])
@click.option("--try-max", type=bool, multiple=True, default=[False])
@click.option("--backend", "-b", type=click.Choice(BACKENDS, case_sensitive=False), multiple=True, default=["sat"])
@click.option("--fallback", type=bool, multiple=True, default=[False])
@click.option("--reallocate", "-r", type=bool, multiple=True, default=[True])
#output
@click.option("--verbosity", "-v", count=True)
@click.option("--progress/--no-progress", default=True)
@click.option("--dump", "-d", type=str, default=None)
@click.option("--target", type=click.Choice(TARGETS, case_sensitive=False), multiple=True, default=[])
@click.option("--zero_one/--no-zero-one", type=bool, default=False)
@click.option("--visualize-core/--no-visualize-core", type=bool, default=False)
def main(dump, prune, slice, reallocate, target, sn_type, from_, to, do_max, try_min, try_max, verbosity, progress, zero_one, backend, fallback, visualize_core):
    global VERBOSE
    VERBOSE = verbosity 
    global tqdm
    if not progress:
        tqdm = lambda x: x
    targets = target if target else TARGETS
    print("inputs", "snt", "do_max", "try_min", "try_max", "prune", "slice", "backend", "fallback", "reallocate", "prog_len", "prog_saved", "prog_regs", "cpu_time")
    for i in range(from_,to+1):
        if not i in sn:
            if VERBOSE > 1:
                print("no sorting networks for",i,"channels", file=stderr)
            continue
        sn_types = []
        for snt in sn_type:
            snt = f"^{snt.replace('%', '.*')}$"
            for key in sn[i].keys():
                if match(snt, key):
                    sn_types.append(key)
        for snt in sn_types:
            if not snt in sn[i]:
                if VERBOSE > 1:
                    print("no sorting networks of type",snt,"for",i,"channels", file=stderr)
                continue
            comps = sn[i][snt] 
            if VERBOSE > 1:
                print(comps, file=stderr)
            for do_max_ in do_max:
                for try_min_ in try_min:
                    for try_max_ in try_max:
                        for prune_ in prune:
                            for slice_ in slice:
                                if slice_ > i:
                                    print(f"slice divider {slice_} greater than number of channels {i}", file=stderr)
                                    continue
                                slice_ = (i//slice_) if slice_ > 0 else slice_
                                for fallback_ in fallback:
                                    for backend_ in backend:
                                        if backend_ != "sat" and fallback_:
                                            print(f"fallback is only relevant for 'sat' backend", file=stderr)
                                            continue
                                        if prune_ and fallback_:
                                            print(f"fallback is not needed when using 'prune'", file=stderr)
                                            continue
                                        start_time = process_time()
                                        prog, cores = compile(sn=comps, target=targets[0], do_max=do_max_, try_min=try_min_, try_max=try_max_, prune=prune_, slice=slice_, zero_one=zero_one, backend=backend_, fallback=fallback_, visualize_core=visualize_core)
                                        cpu_time = process_time()-start_time
                                        if False in reallocate:
                                            print(i, snt, do_max_, try_min_, try_max_, prune_, slice_, backend_, fallback_, False, prog.length(), prog.saved(), len(prog.registers()), "%.6f" % cpu_time)
                                            for target in targets:
                                                prog.target = target
                                                if dump is not None:
                                                    with open(f"{dump}/sn_{i}_{snt}_{do_max_}_{try_min_}_{try_max_}_{prune_}_{slice_}_{backend_}_{fallback_}_{False}.{target.lower()}", "wt") as f:
                                                        print("\n".join(prog.to()),file=f)
                                                if VERBOSE > 1:
                                                    print("\n".join(prog.to()), file=stderr)
                                        if True in reallocate:
                                            start_time = process_time()
                                            prog = prog.reallocate()
                                            cpu_time += process_time()-start_time
                                            print(i, snt, do_max_, try_min_, try_max_, prune_, slice_, backend_, fallback_, True, prog.length(), prog.saved(), len(prog.registers()), "%.6f" % cpu_time)
                                            for target in targets:
                                                prog.target = target
                                                if dump is not None:
                                                    with open(f"{dump}/sn_{i}_{snt}_{do_max_}_{try_min_}_{try_max_}_{prune_}_{slice_}_{backend_}_{fallback_}_{True}.{target.lower()}", "wt") as f:
                                                        print("\n".join(prog.to()),file=f)
                                                if VERBOSE > 1:
                                                    print("\n".join(prog.to()), file=stderr)
                                        if visualize_core and cores:
                                            template1 = r"""\documentclass{article}
\usepackage{tikz}
\usetikzlibrary{arrows,automata,shapes,shapes.multipart,decorations.markings,positioning}
\usepackage{environ}
\makeatletter
\newcounter{sncolumncounter}
\newcounter{snrowcounter}
\def \nodelabel#1{%
\setcounter{snrowcounter}{1}
 \foreach \i in {#1}{%
   \draw (\sncolwidth*\value{sncolumncounter},\value{snrowcounter}) node[anchor=south]{\scriptsize\i};
   \addtocounter{snrowcounter}{1}
 }
 \addtocounter{snrowcounter}{-1}
 %\addtocounter{sncolumncounter}{1}
}
\newcommand{\sncolwidth}{0.7} % relative to row distance
\newcommand{\addcomparator}[3][black]{%
    \draw[line width=1pt,color=#1] (\sncolwidth*\value{sncolumncounter},#2) node[circle,fill=#1,minimum size=5pt,inner sep=0pt,outer sep=0pt]{}--(\sncolwidth*\value{sncolumncounter},#3) node[circle,fill=#1,minimum size=5pt,inner sep=0pt,outer sep=0pt]{};
}
\def \addlayer{%
  \addtocounter{sncolumncounter}{1}
}
\def \nextlayer{%
  \draw [dashed] (\sncolwidth*\value{sncolumncounter}+\sncolwidth,0.6)--(\sncolwidth*\value{sncolumncounter}+\sncolwidth,\value{snrowcounter}+0.6);
  \addtocounter{sncolumncounter}{2}
}
\newsavebox{\measure@tikzpicture}
\NewEnviron{scaletikzpicturetowidth}[1]{%
  \def\tikz@width{#1}%
  \def\tikzscale{1}\begin{lrbox}{\measure@tikzpicture}%
  \BODY
  \end{lrbox}%
  \pgfmathparse{#1/\wd\measure@tikzpicture}%
  \edef\tikzscale{\pgfmathresult}%
  \BODY
}
\newenvironment{sortingnetwork}[1]{%
  \setcounter{sncolumncounter}{0}
  \setcounter{snrowcounter}{#1}
  \def \sn@fullsize{15}
  \begin{tikzpicture}[scale=\tikzscale]
  \begin{scope}[yscale=-1,xscale=1]
}{
  \foreach \i in {1, ..., \value{snrowcounter}}
  {
    \draw[line width=1pt] (-\sncolwidth,\i)--(\sncolwidth*\value{sncolumncounter}+\sncolwidth,\i);
  }
  \end{scope}
  \end{tikzpicture}
}
\renewcommand{\min}{min}
\renewcommand{\max}{max}
\makeatother
\begin{document}
"""
                                            template2 = r"""\end{document}"""
                                            if dump:
                                                prefix = f"sn_{i}_{snt}_{do_max_}_{try_min_}_{try_max_}_{prune_}_{slice_}_{backend_}_{fallback_}_{False}"
                                                with open(f"{dump}/{prefix}.tex", "wt") as f:
                                                    print(template1+"\n".join(cores)+template2, file=f)
                                                chdir(dump)
                                                system(f"pdflatex {prefix}.tex")
                                            else:
                                                print(template1+"\n".join(cores)+template2, file=stderr)

if __name__ == "__main__":
    main()
