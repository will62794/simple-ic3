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
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE, simplify
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
        # Store frames as a list (conjunction) of clauses.
        self.frames = [[system.init]]
        self.frame_history = []
        self.solver = Solver()
        self.prime_map = dict([(v, next_var(v)) for v in self.system.variables])

    def check_property(self, prop):
        """Property Directed Reachability approach without optimizations."""
        print("Checking property %s..." % prop)

        while True:
            print(" [PDR] Checking for bad state in BLOCKING phase...")
            cube = self.get_bad_state(prop)
            if cube is not None:
                print(" [PDR] bad cube:", cube)
                # Blocking phase of a bad state
                # Is clause inductive relative to frame F[i-1]?
                if self.recursive_block(cube):
                    print("--> Bug found at step %d" % (len(self.frames)))
                    break
                else:
                    print(" [PDR] Cube blocked '%s'" % str(cube))
            else:
                print("*** No bad cube found. entering PROPAGATION phase. ***")
                # Checking if the last two frames are equivalent i.e., are inductive
                if self.inductive():
                    print("last two frames are equivalent")
                    print("--> The system is safe!")
                    print("inductive certificate:")
                    # print(self.frames[-1])
                    print(simplify(And(self.frames[-1])))
                    break
                else:
                    # if(len(self.frames) > 3):
                        # return
                    print(" [PDR] -------------- Adding frame %d ----------------" % (len(self.frames)))
                    # print(self.frames[-1])
                    # self.frame_history.append(self.frames[-1])
                    self.frames.append([TRUE()])
                    print(f" [PDR] New frame, {len(self.frames)-1}, clauses: {self.frames[-1]}")
                    # self.frames.append(prop)

                    print(" [PDR] Propagating clauses...")
                    # Propagate clauses forward for all frames after adding new frame.
                    for i in range(len(self.frames)-1):
                        print(f" [PDR] Propagating forward from frame {i}.")

                        # We propagate a clause from an earlier frame to a later frame.
                        num_clauses_propagated = 0
                        frame_i_clauses = self.frames[i]
                        for ci,c in enumerate(frame_i_clauses):
                            # Don't propagate trivial clauses.
                            if c == TRUE():
                                continue
                            # if is_sat(F[i] /\ c /\ T /\ ~c')
                            # then add clause c to F[i+1]
                            # In other words, if c is inductive at frame i, then propagate it to frame i+1.
                            cprime = c.substitute(self.prime_map)
                            # print("clause:", c)
                            # print("clause:", cprime)
                            
                            # We know check if clause c at frame i is inductive relative to frame I, in which case
                            # propagate it forward to the next frame.
                            frame_i_f = And(self.frames[i])
                            ret = self.solve(And(frame_i_f, c, self.system.trans, Not(cprime)))
                            if ret is None:
                                print(" [PDR] Propagating clause %d '%s' from frame %d to frame %d" % (ci, str(c), i, i+1))
                                self.frames[i+1] = self.frames[i+1] + [c]
                                self.frames[i+1] = sorted(self.frames[i+1], key=lambda x: str(x))
                                num_clauses_propagated += 1
                            else:
                                print(" [PDR] NOT Propagating clause %d '%s' from frame %d to frame %d" % (ci, str(c), i, i+1))

                        # If we propagated all clauses forward, this must mean this frame is inductive so we are done.
                        print(f" [PDR] Propagated {num_clauses_propagated} clauses from frame {i} to {i+1}.")
                        if not self.solve(Not(EqualsOrIff(And(self.frames[i]), And(self.frames[i+1])))):
                            print(" [PDR] Frame %d is inductive. The system is safe!" % i)
                            for c in self.frames[i]:
                                print("   ", c)
                            print(" [PDR] End propagation of clauses.")
                            for i in range(len(self.frames)):
                                print(" [PDR] Frame %d, clauses:" % i)
                                for c in self.frames[i]:
                                    print(" ", c)
                            return


    def get_bad_state(self, prop):
        """Extracts a reachable state that intersects the negation
        of the property and the last current frame"""
        last_frame_f = And(self.frames[-1])
        print("  Last frame clauses:")
        for c in self.frames[-1]:
            print("  ", c)
        return self.solve(And(last_frame_f, Not(prop)))

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
            # Replace each current state variable with its primed version in the current cube.
            # This allows us to then do a 1-step backwards reachability check using the transition relation.
            print("    [recursive_block] checking 1-step preimage of bad cube.")
            cubeprime = cube.substitute(dict([(v, next_var(v)) for v in self.system.variables]))
            # The 1-step backwards reachability check from the current bad state/cube.
            cubepre = self.solve(And(And(self.frames[i-1]), self.system.trans, Not(cube), cubeprime))
            print("    [recursive_block] cubepre:", cubepre)
            if cubepre is None:
                print("    [recursive_block] no preimage of bad cube found. Blocking cube automatically from all prior frames.")
                for j in range(1, i+1):
                    self.frames[j] = self.frames[j] + [Not(cube)]
                return False
            cube = cubepre
        return True

    def inductive(self):
        """Checks if last two frames are equivalent """
        if len(self.frames) > 1 and self.solve(Not(EqualsOrIff(And(self.frames[-1]), And(self.frames[-2])))) is None:
            return True
        return False

def model_hash(m):
    fields = []
    for k in m:
        # fields.append((str(k[0]), m[k[0]]))
        fields.append((str(k), m[k]))
    model_kvs_sorted = tuple(sorted(fields, key=lambda x: x[0]))
    return hash(model_kvs_sorted)

class StateGenerator(object):
    """ Generate all states of a given transition system (reachable and/or unreachable)."""
    
    def __init__(self, system):
        self.system = system
        self.solver = Solver()

    def solve_enumerate(self, formula, all_vars=None):
        """ Enumerate all satisfying assignments for given formula. """
        my_solver = Solver()
        my_solver.add_assertion(formula)
        models = []
        while my_solver.solve():
            model = my_solver.get_model()

            if all_vars is None:
                all_vars = []
                for k in model:
                    all_vars.append(k[0])

            model_vals = model.get_values([v for v in (all_vars)], model_completion=True)
            # print("model vals:", model_vals)
            
            # Add assertion to avoid generating this next state again.
            trans_model_formula = [EqualsOrIff(v, model_vals[v]) for v in model_vals]
            my_solver.add_assertion(Not(And(trans_model_formula)))
            # print(trans_model_formula)

            # print("VVVVV:")
            # for v in vals:
                # print("* ", v, vals[v])
            # for a in model:
            #     print("AAA", a[0])
            #     print("BBB", a[1])
            # partial_model = [EqualsOrIff(k[0], k[1]) for k in model]
            # print(self.system.variables[0])
            # print(list(vals.keys())[0])
            
            # print("--")
            models.append(model_vals)
        # print(len(models))
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
    
    def state_str(self, s):
        out = ""
        vals = [str(v)+"="+str(s[v]) for v in self.system.variables]
        return "\n".join(vals) 
    
    # def gen_transitions(self):
    #     all_trans = []
    #     while True:
    #         trans = self.gen_transition()
    #         # No more transitions to find.
    #         if not trans:
    #             break
    #         all_trans.append(trans)
    #         # Block this transition from being found again.
    #         block_preds = []
    #         for v in self.system.variables:
    #             block = And(EqualsOrIff(v, trans["curr"][v]), EqualsOrIff(next_var(v), trans["next"][v]))
    #             block_preds.append(block)
            
    #         self.solver.add_assertion(Not(And(block_preds)))
    #     return all_trans

    # def state_graph(self, styler, labeler):
    #     G = graphviz.Digraph("state_graph")
    #     all_trans = self.gen_transitions()
    #     # Map from state's string representation to its structured 
    #     # (pySMT based) representation.
    #     all_states = {}
  
    #     for t in all_trans:
    #         scurr = self.state_str(t["curr"])
    #         snext = self.state_str(t["next"])
    #         G.edge(scurr,snext)
    #         all_states[scurr] = t["curr"]
    #         all_states[snext] = t["next"]
    #     # Add all states for styling.
    #     for s in all_states:
    #         sval = all_states[s]
    #         G.node(s, label=labeler(s, sval), **styler(s, sval))
    #     return G
    
    def gen_reachable(self, init, styler, labeler):
        # Generate initial states.
        G = graphviz.Digraph("state_graph", strict=True)
        print("init formula:", init)
        init_models = self.solve_enumerate(init, all_vars=self.system.variables)
        print("INIT MODELS:")
        # for m in init_models:
            # print(m, type(m))
            # print(hash(m))
            # print(m[self.system.variables[0]])
            # print(m[self.system.variables[2]])

        # exit(0)

        init_model_hashes = [model_hash(m) for m in init_models]
        print("Num init states:", len(init_models))
        reachable_model_hashes = []
        reachable_models = []
        edges = []
        reachable_model_table = {}
        frontier = list(init_models)

        # Generate states reachable from init.
        while len(frontier) > 0:
            # print("Frontier size:", len(frontier))

            m = frontier.pop()
            reachable_model_table[model_hash(m)] = m
            # print(m)
            # print("reachable:", reachable_model_hashes)

            if model_hash(m) in reachable_model_hashes:
                continue
            
            # Mark as reachable.
            reachable_model_hashes.append(model_hash(m))
            reachable_models.append(m)

            # print("CURR:")
            # print(m)
            # curr_state_formula = And([EqualsOrIff(k[0], k[1]) for k in m])
            curr_state_formula = And([EqualsOrIff(k, m[k]) for k in m])
            # print("currf:", curr_state_formula)
            # res = self.solve_enumerate(And([curr_state_model, self.system.trans]))
            # print(self.system.trans)
            # res = self.solver.solve([self.system.trans])
            next_vars = [next_var(v) for v in self.system.variables]

            res = self.solve_enumerate(And(curr_state_formula, self.system.trans), all_vars = self.system.variables + next_vars)
            # print("TRANS MODELS:")
            for r in res:
                # print(r)
                # print("__")
                partial = []
                for a in r:
                    # print("avar:", a)
                    if is_next_var_name(str(a)):
                        # print(r[a])
                        partial.append(EqualsOrIff(Symbol(str(a).replace("_NEXT", ""), a.symbol_type()), r[a]))
                newm = And(partial)
                res = self.solve_enumerate(newm)
                frontier.append(res[0])
                # if model_hash(res[0]) not in reachable_model_hashes:
                edges.append((model_hash(m), model_hash(res[0])))

            # print(self.solver.get_model())

        # print("INIT MODELS:")
        # for m in init_models:
        #     print(m)

        # for m in reachable_models:
        #     print("MODEL:")
        #     print(m)


        print("Total number of reachable states found:", len(reachable_models))
        print("Total number of reachable edges found:", len(edges))
        
        # Build Graphviz DOT graph.
        for e in edges:
            G.edge(str(e[0]), str(e[1]))
       
        def state_labeler(skey, sval):
            # print sval.keys()
            out = "\n".join([str(k)+": "+str(sval[k]) for k in sval.keys()]) #+ "\n" + skey
            return out.replace("semaphore", "sem")
            # return [str((k,str(sval[k]))) for k in sval]
        def state_styler(skey, sval):
            return {"color": "red"}
       
        for h in reachable_model_hashes:
            s = str(h)
            sval = reachable_model_table[h]
            sstr = self.state_str(sval)
            # print(sstr)
            color = "gray" if h in init_model_hashes else "white"
            G.node(s, label=sstr, style="filled", fillcolor=color)
        return G
        

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


def lock_server(clients=2, servers=1):
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

    nclients = clients
    nservers = servers
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

        # UNSAFE version.
        # return next_var(links[(c,s)]) & Not(next_var(semaphores[s])) &\
        #     And([unchanged(semaphores[t]) for t in without_s]) &\
        #     And([unchanged(links[(cx,sx)]) for (cx,sx) in without_c_s])

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

