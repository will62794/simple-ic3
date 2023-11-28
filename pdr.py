# This example shows a more advance use of pySMT.
#
# It provides a simple implementation of Bounded Model Checking [1]
# with K-Induction [2], and PDR [3,4], and applies it on a simple
# transition system.
#
# [1] Biere, Cimatti, Clarke, Zhu,
#     "Symbolic Model Checking without BDDs",
#     TACAS 1999
#
# [2] Sheeran, Singh,  Stalmarck,
#     "Checking  safety  properties  using  induction  and  a SAT-solver",
#     FMCAD 2000
#
# [3] Bradley
#     "SAT-Based Model Checking without Unrolling",
#     VMCAI 2011
#
# [4] Een, Mischenko, Brayton
#     "Efficient implementation of property directed reachability",
#     FMCAD 2011
#
from pysmt.shortcuts import Symbol, Not, And, Or, Equals, EqualsOrIff, Implies, Bool
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import BOOL
import graphviz
import itertools

def is_next_var_name(vname):
    return vname.endswith("_NEXT")

def next_var_name(vname):
    return "%s_NEXT" % vname

def next_var(v):
    """Returns the 'next' of the given variable"""
    return Symbol(next_var_name(v.symbol_name()), v.symbol_type())

def at_time(v, t):
    """Builds an SMT variable representing v at time t"""
    return Symbol("%s@%d" % (v.symbol_name(), t), v.symbol_type())


class TransitionSystem(object):
    """Trivial representation of a Transition System."""

    def __init__(self, variables, init, trans):
        self.variables = variables
        self.init = init
        self.trans = trans

# EOC TransitionSystem

class PDR(object):
    def __init__(self, system):
        self.system = system
        self.frames = [system.init]
        self.frame_history = []
        self.solver = Solver()
        self.prime_map = dict([(v, next_var(v)) for v in self.system.variables])

    def check_property(self, prop):
        """Property Directed Reachability approach without optimizations."""
        print("Checking property %s..." % prop)

        while True:
            cube = self.get_bad_state(prop)
            if cube is not None:
                print("bad cube:", cube)
                # Blocking phase of a bad state
                if self.recursive_block(cube):
                    print("--> Bug found at step %d" % (len(self.frames)))
                    break
                else:
                    print("   [PDR] Cube blocked '%s'" % str(cube))
            else:
                # Checking if the last two frames are equivalent i.e., are inductive
                if self.inductive():
                    print("--> The system is safe!")
                    break
                else:
                    print("   [PDR] Adding frame %d..." % (len(self.frames)))
                    # print(self.frames[-1])
                    self.frame_history.append(self.frames[-1])
                    self.frames.append(TRUE())
                    # self.frames.append(prop)

    def get_bad_state(self, prop):
        """Extracts a reachable state that intersects the negation
        of the property and the last current frame"""
        return self.solve(And(self.frames[-1], Not(prop)))

    def solve(self, formula):
        """Provides a satisfiable assignment to the state variables that are consistent with the input formula"""
        if self.solver.solve([formula]):
            return And([EqualsOrIff(v, self.solver.get_value(v)) for v in self.system.variables])
        return None

    def recursive_block(self, cube):
        """Blocks the cube at each frame, if possible.

        Returns True if the cube cannot be blocked.
        """
        for i in range(len(self.frames)-1, 0, -1):
            cubeprime = cube.substitute(dict([(v, next_var(v)) for v in self.system.variables]))
            cubepre = self.solve(And(self.frames[i-1], self.system.trans, Not(cube), cubeprime))
            if cubepre is None:
                for j in range(1, i+1):
                    self.frames[j] = And(self.frames[j], Not(cube))
                return False
            cube = cubepre
        return True

    def inductive(self):
        """Checks if last two frames are equivalent """
        if len(self.frames) > 1 and \
           self.solve(Not(EqualsOrIff(self.frames[-1], self.frames[-2]))) is None:
            return True
        return False

class StateGenerator(object):
    """ Generate all states of a given transition system (reachable and/or unreachable)."""
    
    def __init__(self, system):
        self.system = system
        self.solver = Solver()

    def solve_enumerate(self, formula):
        """ Enumerate all satisfying assignments for given formula. """
        my_solver = Solver()
        my_solver.add_assertion(formula)
        models = []
        while my_solver.solve():
            model = my_solver.get_model()
            # print("LLLLL:", model)
            # for a in model:
            #     print("AAA", a[0])
            #     print("BBB", a[1])
            partial_model = [EqualsOrIff(k[0], k[1]) for k in model]
            # print("MODEL:")
            # print(model)
            # print("--")
            my_solver.add_assertion(Not(And(partial_model)))
            models.append(model)
        return models

    def gen_transition(self):
        """ Generate one (s,t) state transition. Returns cube representing the generated  """
        res = self.solver.solve([self.system.trans])
        if not res:
            return None
        # print(self.system.variables)
        cube_preds = []
        trans = {"curr": {}, "next": {}} 
        for v in self.system.variables:
            vcurr = self.solver.get_value(v)
            vnext = self.solver.get_value(next_var(v))
            # print (v,vcurr,vnext, type(vcurr), type(vnext))
            x = {}
            x[v] = True
            trans["curr"][v] = vcurr
            trans["next"][v] = vnext
            # cube_preds.append(And(EqualsOrIff(v, vcurr), EqualsOrIff(next_var(v), vnext)))
        cube = And(cube_preds)
        return trans
        
    def gen_transitions(self):
        all_trans = []
        while True:
            trans = self.gen_transition()
            # No more transitions to find.
            if not trans:
                break
            all_trans.append(trans)
            # Block this transition from being found again.
            block_preds = []
            for v in self.system.variables:
                block = And(EqualsOrIff(v, trans["curr"][v]), EqualsOrIff(next_var(v), trans["next"][v]))
                block_preds.append(block)
            
            self.solver.add_assertion(Not(And(block_preds)))
        return all_trans

    def state_graph(self, styler, labeler):
        G = graphviz.Digraph("state_graph")
        all_trans = self.gen_transitions()
        # Map from state's string representation to its structured 
        # (pySMT based) representation.
        all_states = {}
        def state_str(s):
            out = ""
            vals = [str(s[v]) for v in self.system.variables]
            return ",".join(vals)
        for t in all_trans:
            scurr = state_str(t["curr"])
            snext = state_str(t["next"])
            G.edge(scurr,snext)
            all_states[scurr] = t["curr"]
            all_states[snext] = t["next"]
        # Add all states for styling.
        for s in all_states:
            sval = all_states[s]
            G.node(s, label=labeler(s, sval), **styler(s, sval))
        return G
    
    def reachable(self, styler, labeler):
        # Generate initial states.
        G = graphviz.Digraph("state_graph")
        self.system.init
        init_models = self.solve_enumerate(self.system.init)
        print("INIT MODELS:")
        for m in init_models:
            print(m)
            print(m[self.system.variables[0]])
            print(m[self.system.variables[2]])

        models_reachable = init_models
        frontier = []
        frontier += models_reachable

        # Generate states reachable from init.
        while len(frontier) > 0:
            m = frontier.pop()

            if m in models_reachable:
                continue

            models_reachable.append(res[0])

            print("CURR:")
            print(m)
            curr_state_formula = And([EqualsOrIff(k[0], k[1]) for k in m])
            # print("currf:", curr_state_formula)
            # res = self.solve_enumerate(And([curr_state_model, self.system.trans]))
            # print(self.system.trans)
            # res = self.solver.solve([self.system.trans])
            res = self.solve_enumerate(And(curr_state_formula, self.system.trans))
            print("TRANS MODELS:")
            for r in res:
                print(r)
                print("__")
                partial = []
                for a in r:
                    if is_next_var_name(str(a[0])):
                        print(a[0], a[1])
                        # print(a[0].substitute({self.system.variables[0]: self.system.variables[0]}))
                        print(str(a[0]).replace("_NEXT", ""), a[1])
                        print("____")
                        partial.append(EqualsOrIff(Symbol(str(a[0]).replace("_NEXT", ""), a[0].symbol_type()), a[1]))
                newm = And(partial)
                print("newm:", newm)
                res = self.solve_enumerate(newm)
                print(res[0])
                frontier.append(res[0])
            # print(self.solver.get_model())


        # print("vars:", self.system.variables)
        # for v in self.system.variables:
            # print("var value:", v, self.solver.get_value(v))
        # self.solver.get_value(self.system.variables[0])
        # print(r)



class BMCInduction(object):

    def __init__(self, system):
        self.system = system

    def get_subs(self, i):
        """Builds a map from x to x@i and from x' to x@(i+1), for all x in system."""
        subs_i = {}
        for v in self.system.variables:
            subs_i[v] = at_time(v, i)
            subs_i[next_var(v)] = at_time(v, i+1)
        return subs_i

    def get_unrolling(self, k):
        """Unrolling of the transition relation from 0 to k:

        E.g. T(0,1) & T(1,2) & ... & T(k-1,k)
        """
        res = []
        for i in range(k+1):
            subs_i = self.get_subs(i)
            res.append(self.system.trans.substitute(subs_i))
        return And(res)

    def get_simple_path(self, k):
        """Simple path constraint for k-induction:
        each time encodes a different state
        """
        res = []
        for i in range(k+1):
            subs_i = self.get_subs(i)
            for j in range(i+1, k+1):
                state = []
                subs_j = self.get_subs(j)
                for v in self.system.variables:
                    v_i = v.substitute(subs_i)
                    v_j = v.substitute(subs_j)
                    state.append(Not(EqualsOrIff(v_i, v_j)))
                res.append(Or(state))
        return And(res)

    def get_k_hypothesis(self, prop, k):
        """Hypothesis for k-induction: each state up to k-1 fulfills the property"""
        res = []
        for i in range(k):
            subs_i = self.get_subs(i)
            res.append(prop.substitute(subs_i))
        return And(res)

    def get_bmc(self, prop, k):
        """Returns the BMC encoding at step k"""
        init_0 = self.system.init.substitute(self.get_subs(0))
        prop_k = prop.substitute(self.get_subs(k))
        return And(self.get_unrolling(k), init_0, Not(prop_k))

    def get_k_induction(self, prop, k):
        """Returns the K-Induction encoding at step K"""
        subs_k = self.get_subs(k)
        prop_k = prop.substitute(subs_k)
        return And(self.get_unrolling(k),
                   self.get_k_hypothesis(prop, k),
                   self.get_simple_path(k),
                   Not(prop_k))

    def check_property(self, prop):
        """Interleaves BMC and K-Ind to verify the property."""
        print("Checking property %s..." % prop)
        for b in range(100):
            f = self.get_bmc(prop, b)
            print("   [BMC]    Checking bound %d..." % (b+1))
            if is_sat(f):
                print("--> Bug found at step %d" % (b+1))
                return

            f = self.get_k_induction(prop, b)
            print("   [K-IND]  Checking bound %d..." % (b+1))
            if is_unsat(f):
                print("--> The system is safe!")
                return


def lock_server():
    """ Simpler lock server example based on Ivy example.

    type client
    type server

    after init  {
        semaphore(Y) := true ;
        link(X, Y) := false;
    }

    action connect(c: client, s: server) = {
        require semaphore(s);
        link(c, s) := true;
        semaphore(s) := false;
    }

    action disconnect(c: client, s: server) = {
        require link(c, s);
        link(c, s) := false;
        semaphore(s) := true;
    }

    invariant [unique] forall C1, C2 : client, S: server. link(C1, S) & link(C2, S) -> C1 = C2
    
    """
    from pysmt.typing import BVType

    nclients = 1
    nservers = 2
    def semaphore_var(p):
        return Symbol(p + "_semaphore", BOOL)
    def link_var(c, s):
        return Symbol("%s_%s_link" % (c,s), BOOL)

    def unchanged(x):
        return EqualsOrIff(next_var(x), x)

    server = [("s" + str(i)) for i in range(nservers)]
    semaphores = {s:semaphore_var(s) for s in server}

    client = [("c" + str(i)) for i in range(nclients)]
    links = {(c,s) : link_var(c,s) for (c,s) in itertools.product(client, server)}

    def connect(c, s):
        without_s = [x for x in server if x!=s]
        without_c_s = [(ca,sa) for (ca,sa) in itertools.product(client, server) if (ca,sa)!=(c,s)]
        return semaphores[s] & next_var(links[(c,s)]) & Not(next_var(semaphores[s])) &\
            And([unchanged(semaphores[t]) for t in without_s]) &\
            And([unchanged(links[(cx,sx)]) for (cx,sx) in without_c_s])

    def disconnect(c, s):
        without_s = [x for x in server if x!=s]
        without_c_s = [(ca,sa) for (ca,sa) in itertools.product(client, server) if (ca,sa)!=(c,s)]
        return links[(c,s)] & Not(next_var(links[(c,s)])) & next_var(semaphores[s]) &\
            And([unchanged(semaphores[t]) for t in without_s]) &\
            And([unchanged(links[(cx,sx)]) for (cx,sx) in without_c_s])

    variables = list(semaphores.values()) + list(links.values())

    initsem = And([semaphores[s] for s in server])
    initlink = And([Not(links[(c,s)]) for (c,s) in itertools.product(client, server)])
    init = And(initsem, initlink)
    
    action_connect = Or([connect(c,s) for (c,s) in itertools.product(client, server)])
    action_disconnect = Or([disconnect(c,s) for (c,s) in itertools.product(client, server)])
    trans = Or(action_connect, action_disconnect)
    
    # Two clients cannot hold the lock of the same server simultaneously.
    def safelink(c1,c2,s):
        return Implies(links[(c1,s)] & links[(c2,s)], Bool(c1 == c2))
    safety = And([safelink(c1,c2,s) for (c1,c2,s) in itertools.product(client, client, server)])

    return (TransitionSystem(variables, init, trans), [safety])

def counter(bit_count):
    """Counter example with n bits and reset signal."""

    # Example Counter System (SMV-like syntax)
    #
    # VAR bits: word[bit_count];
    #     reset: boolean;
    #
    # INIT: bits = 0 & reset = FALSE;
    #
    # TRANS: next(bits) = bits + 1
    # TRANS: next(bits = 0) <-> next(reset)

    from pysmt.typing import BVType
    bits = Symbol("bits", BVType(bit_count))
    nbits = next_var(bits)
    reset = Symbol("r", BOOL)
    nreset = next_var(reset)
    variables = [bits, reset]

    init = bits.Equals(0) & Not(reset)

    trans = nbits.Equals(bits + 1) &\
            (nbits.Equals(0)).Iff(nreset)

    # A true invariant property: (reset -> bits = 0)
    true_prop = reset.Implies(bits.Equals(0))

    # A false invariant property: (bits != 2**bit_count-1)
    false_prop = bits.NotEquals(2**bit_count -1)

    return (TransitionSystem(variables, init, trans), [true_prop, false_prop])

