#
# Understanding IC3.
# 

import graphviz
import itertools
import z3
from z3 import *

# # Model program counter variable in boolean encoding.
# # {"a1","a2","a3"}

# class pc:
#     # Boolean encoding of program counters.
#     encoding = {
#         "a1" = [False, False],
#         "a2" = [False, True],
#         "a3" = [True, False]
#     }

#     def __init__(self, i):
#         self.pci0 = Bool('pc%d_0'%i)
#         self.pci1 = Bool('pc%d_1'%i)
#         # TODO: Add next state versions of variables.
    
#     def eq(pcval):
#         return [self.pci0,self.pci1] == encoding[pcval]

#     def advance(curr_pcval, next_pcval):
#         pre = And([self.pci0, self.pci1] == encoding[pcval])
#         post = And([self.pci0, self.pci1] == encoding[next_pcval])
#         return And(pre, post)

# pcs = [pc(0), pc(1)]

# # Model barrier variable.
# barriers = [Bool('barrier0'), Bool('barrier1')]


def gen_all_states(currvars):
    """ Generate all states for list of given state variables. """
    boolean = [True, False]
    return list(itertools.product(*[boolean for s in currvars]))

def gen_transitions(currvars, nextvars, trans):
    allvars = (currvars + nextvars)
    transitions = []
    s = Solver()
    s.add(trans)
    while s.check() == sat:
        m = s.model()
        # print(m)
        # Prevent finding this model again.
        neg = []
        for v in allvars:
            neg.append(v == m[v])
        s.add(Not(And(*neg)))
        trans = ([m[x] for x in currvars],[m[x] for x in nextvars])
        # print(trans)
        transitions.append(trans)
    return transitions

def nextify(expr,curr_vars, next_vars):
    """ For a given state expression over current state variables,
    substitute next state versions of the variables."""
    return substitute(expr, list(zip(curr_vars, next_vars)))

class IC3:
    """ 
    IC3 implementation for proving P is invariant of given system
    defined by initial predicate I and transition relation T.
    """
    def __init__(self, I, T, P, curr_vars, next_vars):
        self.I = I
        self.T = T
        self.P = P
        self.curr_vars = curr_vars
        self.next_vars = next_vars

    def nxt(self, e):
        return nextify(e, curr_vars, next_vars)

    def F(self, k):
        """ Returns the formula for frame Fk."""
        return And(self.frames[k], self.clauses[k])

    def inductivelyGeneralize(self, m, k):
        # TODO.
        pass

    def pushGeneralization(self, k):
        # TODO.
        pass

    def strengthen(self, k):
        # TODO.
        s = Solver()
        s.add(And(self.F(k), self.T, nxt(Not(self.P))))
        while s.check() == sat:
            # the counterexample to induction.
            m = s.model()
            print(m)
            # TODO.
            self.inductivelyGeneralize(m, k)
            self.pushGeneralization(k)
            return

    def propagateClauses(self, k):
        # TODO.
        pass
    
    def prove(self):
        # Return immediately if initial states or its 1-step 
        # successors violate the property.
        Pnext = self.nxt(self.P)
        s = Solver()
        s.add(Or(And(self.I, Not(self.P)), And(self.I, self.T, Not(Pnext))))
        if s.check() == sat:
            print("Initial checks of ic3 prove failed")
            m = s.model()
            print(m)
            return False
        print("Initial checks of ic3 prove passed")

        MAX_I = 10

        # Each frame is initialized to the property P we are trying to 
        # prove, except for the initial frame.
        self.frames = [self.P for i in range(MAX_I)]
        self.frames[0] = self.I
        # Each frame formula Fi is P /\ clauses[i]
        self.clauses = [And() for i in range(MAX_I)]
        k = 1
        while True:
            if not self.strengthen(k):
                return False
            self.propagateClauses(k)
            # if clauses(Fi) = clauses(Fiplus1) for some 1<=i<=k
            #   return true
            k+=1


# Define boolean state variables.
x0 = Bool("x0")
x1 = Bool("x1")
x2 = Bool("x2")

curr_vars = [x0,x1,x2]
next_vars = [Bool(v.decl().name() + "_next") for v in curr_vars]
print(curr_vars)
print(next_vars)
svars = curr_vars + next_vars

def nxt(e):
    return nextify(e, curr_vars, next_vars)

# Initial states
init = And(Not(x0), Not(x1), Not(x2))

# Transition relation.
a1pre = And(x0 == x1)
a1post = And(nxt(x0) == Not(x1), nxt(x1) == x1, nxt(x2) == x2)
a1 = And(a1pre, a1post)

a2pre = And(x0 == x2)
a2post = And(nxt(x0) == Not(x2), nxt(x1) == x1, nxt(x2) == Not(x0))
a2 = And(a2pre, a2post)

trans = Or(a1, a2)
print(trans)
# print(init)
# print(nextify(init, curr_vars, next_vars))

states = gen_all_states(curr_vars)
transitions = gen_transitions(curr_vars, next_vars, trans)

# Generate initial states.
init_states = []
s = Solver()
s.add(init)
while s.check() == sat:
    m = s.model()
    # Prevent finding this model again.
    neg = []
    sval = [m[v] for v in curr_vars]
    init_states.append(tuple(sval))
    for v in curr_vars:
        neg.append(v == m[v])
    s.add(Not(And(*neg)))

def state_str(s):
    return "".join([str(int(bool(b))) for b in s])



G = graphviz.Digraph("states")
print("## States")
for s in states:
    print(s)
    if s in init_states:
        G.node(state_str(s), color="green")
    else:
        G.node(state_str(s))
print("## Transitions")
for s,t in transitions:
    print(s,t)
    G.edge(state_str(s), state_str(t))

f = open("states.dot", 'w')
f.write(G.source)
f.close()

# P1 = And(Not(x0 == x1))
P1 = Not(And(x0,x1,x2))
ic3 = IC3(init, trans, P1, curr_vars, next_vars)
res = ic3.prove()
if not res:
    print("Failed to prove property")

# form.add(trans)



