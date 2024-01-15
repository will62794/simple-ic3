from pdr import *
import pysmt

# (system, props) = counter(4)

def run_pdr(system, props):

    # Run PDR property checking.
    P0 = props[0]
    pdr = PDR(system)
    pdr.check_property(P0)

    # for i,f in enumerate(pdr.frame_history):
    #     print(i,f)
    # for prop in props:
        # pdr.check_property(prop)
        # print("")

def sats_prop(s, P):
    """ Does given state 's' satisfy property 'P'."""
    # Check if (s /\ ~P) is unsatisfiable.
    cube = And([EqualsOrIff(v, s[v]) for v in s])
    return is_unsat(And(cube, Not(P)))

# Generate all possible transitions of the system.
def state_styler(skey, sval):
    cube = And([EqualsOrIff(v, sval[v]) for v in sval])
    # Colorize states that satisfy the property.
    params = {"color": "black"}

    if sats_prop(sval, P0):
        params["color"] = "green"
        params["style"] = ""

    # F0 = pdr.frame_history[0]
    # F1 = pdr.frame_history[1]
    # if not is_sat(And(cube, Not(F0))):
    #     # params["fillcolor"] = "orange"
    #     params["color"] = "orange"
    #     params["style"] = ""

    # if not is_sat(And(cube, Not(system.init))):
    #     params["fillcolor"] = "gray"
    #     params["style"] = "filled"

    return params

def state_labeler(skey, sval):
    # print sval.keys()
    out = "\n".join([str(k)+": "+str(sval[k]) for k in sval.keys()]) #+ "\n" + skey
    return out.replace("semaphore", "sem")
    # return [str((k,str(sval[k]))) for k in sval]


# G.render("state-graphs/state-graph")

# bmcind = BMCInduction(example[0])
# for prop in props:
#     # bmcind.check_property(prop)
#     pdr.check_property(prop)
#     print("")


if __name__ == "__main__":
    (system, props) = lock_server(clients=2, servers=1)


    # G = gen.state_graph(state_styler, state_labeler)

    print("================")
    print("================")

    print("Generating all reachable states.")
    sg = StateGenerator(system)
    G = sg.gen_reachable(system.init, state_styler, state_labeler)
    G.render("state-graphs/state-graph-reach")

    print("Generating complete state graph.")
    G = sg.gen_reachable(TRUE(), state_styler, state_labeler)
    G.render("state-graphs/state-graph-full")

    # run_pdr(system, props)