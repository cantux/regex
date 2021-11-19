import graphviz
from collections import defaultdict, deque

class State:
    st_inc_id = 0
    def __init__(self, accept=False):
        self.transitions = {}
        self.e_transitions = []
        self.accept = accept

        # keep an incremental id for graphviz
        State.st_inc_id += 1
        self.st_inc_id = State.st_inc_id
        self.debug_info = []

    def __str__(self):
        return "id: " + str(self.st_inc_id) +\
                "\ntransitions: " + str(self.transitions) +\
                "\nepsilon_ts: " + "".join([str(x) for x in self.e_transitions])

class NFA:
    @staticmethod
    def create(symbol=None):
        start = State()
        end = State(True)
        # TODO: support charsets: 
        # deconstructed_symbol = CharsetUtil.deconstructSymbol(symbol)
        # [a-z], [A-Z], [0-9] ord
        if symbol:
            start.transitions[symbol] = end
        else:
            start.e_transitions.append(end)
        return (start, end)

    @staticmethod
    def union(a, b):
        a_start, a_end = a
        b_start, b_end = b

        begin = State()
        begin.e_transitions.append(a_start)
        begin.e_transitions.append(b_start)

        fin = State(True)
        a_end.e_transitions.append(fin)
        a_end.accept = False
        b_end.e_transitions.append(fin)
        b_end.accept = False

        return (begin, fin)

    @staticmethod
    def concat(a, b):
        a_start, a_end = a
        b_start, b_end = b
        a_end.e_transitions.append(b_start)
        a_end.accept = False
        return (a_start, b_end)

    @staticmethod
    def closure(s):
        begin, fin = NFA.create() # see that epsilon trans is implicit

        s_start, s_end = s
        begin.e_transitions.append(s_start)

        s_end.e_transitions.append(fin)
        s_end.e_transitions.append(s_start)
        s_end.accept = False

        return (begin, fin)

    @staticmethod
    def zeroOrOne(s):
        begin, fin = NFA.create()
        s_start, s_end = s
        
        s_start.e_transitions.append(begin)
        s_end.e_transitions.append(fin)
        s_end.accept = False

        return s_start, fin

    @staticmethod
    def oneOrMore(s):
        begin, fin = State(), State(True) # notice that start and end are not bound
        s_start, s_end = s

        begin.e_transitions.append(s_start)
        s_end.e_transitions.append(fin)
        s_end.e_transitions.append(s_start)
        s_end.accept = False

        return begin, fin

    @staticmethod
    def build(postfix_ptrn):
        if not postfix_ptrn:
            return NFA.create()

        s = []

        for c in postfix_ptrn:
            if c == "*":
                s.append(NFA.closure(s.pop()))
            elif c == "?":
                s.append(NFA.zeroOrOne(s.pop()))
            elif c == "+":
                s.append(NFA.oneOrMore(s.pop()))
            elif c == "|":
                s.append(NFA.union(s.pop(), s.pop()))
            elif c == ":":
                right = s.pop()
                left = s.pop()
                s.append(NFA.concat(left, right))
            else:
                # case where we see a char
#                 res = []
#                 if c == ".":
#                     for x in range(48,57):
#                         res.append(chr(x))                
                s.append(NFA.create(c))
        return s.pop()

    @staticmethod
    def eps_closure(state, current):
        if state not in current:
            current.add(state)
            for nxt in state.e_transitions:
                NFA.eps_closure(nxt, current)

    @staticmethod
    def nfa_match(start, word):
        # see that this is similar to powerset construction
        current = set()
        NFA.eps_closure(start, current)
        previous = set()

        for c in word:
            previous = current

            current = set()

            for state in previous:
                if c in state.transitions:
                    NFA.eps_closure(state.transitions[c], current)
        return any([c.accept for c in current])

    @staticmethod
    def visualize_nfa(start_state):
        g = graphviz.Digraph()
        g.attr(rankdir='LR')

        visited = set()
        
        def dfs(curr):
            if curr.st_inc_id not in visited:
                visited.add(curr.st_inc_id)
                visited.add(curr.st_inc_id)
                g.node(str(curr.st_inc_id), shape="doublecircle" if curr.accept else "circle")

                state_to_charset_map = defaultdict(list)
                for sym, nxt_st in curr.transitions.items():
                    state_to_charset_map[str(nxt_st.st_inc_id)].append(sym)
                for nxt_st_id, sym_lst in state_to_charset_map.items():
                    g.edge(str(curr.st_inc_id), str(nxt_st_id), label="".join(sym_lst))
                for nxt_st in curr.e_transitions:
                    g.edge(str(curr.st_inc_id), str(nxt_st.st_inc_id), label="@")

                for _, nxt_st in curr.transitions.items():
                    dfs(nxt_st)
                for nxt_st in curr.e_transitions:
                    dfs(nxt_st)

        dfs(start_state)
        return g

class DFA:
    def __init__(self):
        return

    @staticmethod
    def create_key(sts):
        return tuple(sorted(sts, key=lambda x: x.st_inc_id))

    @staticmethod
    def get_key_str(sts):
        return ",".join(map(lambda x: str(x.st_inc_id), sts))

    @staticmethod
    def nfa_to_dfa(nfa_start):
        # Compiler Design Ullman et al. pg. 153
        # also outlined at: http://www.cs.nuim.ie/~jpower/Courses/Previous/parsing/node9.html
        dfa_graph = defaultdict(dict)
        accepts = set()

        starting_set = set()
        NFA.eps_closure(nfa_start, starting_set)
        start_state = DFA.create_key(starting_set)

        for s in start_state:   # quick check to see if start state reaches to end
            if s.accept:        # case for accepting empty word ""
                accepts.add(start_state)

        q = deque([start_state])
        seen = set()

        while q:
            curr_states = q.popleft()
            if curr_states not in seen:
                seen.add(curr_states)
                # print(DFA.get_key_str(curr_states))
                # from the current aggregate set of states, find all possible next states
                sym_dct = defaultdict(set)
                for c_state in curr_states:
                    for sym, nxt_st in c_state.transitions.items():
                        eps_reachable = set()           
                        NFA.eps_closure(nxt_st, eps_reachable)
                        sym_dct[sym].update(eps_reachable)

                # for every transition record it into the DFA and accepts
                for sym, set_of_states in sym_dct.items():
                    next_key = DFA.create_key(set_of_states)
                    for s in set_of_states:
                        if s.accept:
                            accepts.add(next_key)
                            break
                    dfa_graph[curr_states][sym] = next_key
                    q.append(next_key)
        return dfa_graph, start_state, accepts 

    @staticmethod
    def dfa_match(dfa_graph, start, accepts, word):
        curr = start
        for c in word:
            if curr in dfa_graph and c in dfa_graph[curr]:
                curr = dfa_graph[curr][c]
            else:
                return False
        return curr in accepts

    @staticmethod
    def visualize_dfa(dd, accepts):
        g = graphviz.Digraph()
        g.attr(rankdir='LR')

        for state, transitions in dd.items():
            curr_str = DFA.get_key_str(state)
            g.node(curr_str, shape="doublecircle" if state in accepts else "circle")
            for sym, next_state in transitions.items():
                g.edge(curr_str, DFA.get_key_str(next_state), label=sym)

        return g

class Regex:
    def __init__(self, ptrn):
        self.ptrn = ptrn
        self.postfix_ptrn = Regex.infix_to_postfix(self.ptrn)
        self.nfa_start, _ = NFA.build(self.postfix_ptrn)
        self.dfa_graph, self.dfa_start, self.dfa_accepts = DFA.nfa_to_dfa(self.nfa_start)

    @staticmethod
    def infix_to_postfix(infix_ptrn):
        # tricky cases
        # a|b* -> ab*| -> need precedence to cover this case
        # see: https://blog.cernera.me/converting-regular-expressions-to-postfix-notation-with-the-shunting-yard-algorithm/
        # (ab)* -> ab:*     
        # a|(bc) -> bc:a| instead of ab:c|
        postfix_ptrn = []
        op_s = []
        precedence = {"*": 50, "+": 50, "?": 50, "|": 40, ":": 40}
        def isChar(c):
            ordnl = ord(c)
            return (48 <= ordnl <= 57) or (65 <= ordnl <= 90) or (97 <= ordnl <= 122)
        def isMetaChar(c):
            return c in "*+?|:.^$(){}[-]"
        def preproc(infix):
            preproc_ptrn = []
            i = 1
            while i < len(infix):
                if (isChar(infix[i - 1]) and isChar(infix[i])) \
                        or (infix[i] == "(") \
                        or (infix[i - 1] == ")" and isChar(infix[i])):
                    preproc_ptrn.append(infix[i - 1])
                    preproc_ptrn.append(":")
                else:
                    preproc_ptrn.append(infix[i - 1])
                i += 1
            preproc_ptrn.append(infix[-1])
            return "".join(preproc_ptrn)
        infix_preproc_ptrn = preproc(infix_ptrn)
        print("after preproc: " + infix_preproc_ptrn)
        for c in infix_preproc_ptrn:
            if isChar(c):
                postfix_ptrn.append(c)
            if c == "(":
                op_s.append(c)
            elif c == ")":
                while op_s[-1] != "(":
                    postfix_ptrn.append(op_s.pop())
                op_s.pop() # remove "(" too
            elif isMetaChar(c):
                while op_s and precedence.get(c, 0) <= precedence.get(op_s[-1], 0):
                    postfix_ptrn.append(op_s.pop())
                op_s.append(c)

        while op_s:
            postfix_ptrn.append(op_s.pop())
        res = ''.join(postfix_ptrn)
        return res

    def nfa_match(self, word):
        return NFA.nfa_match(self.nfa_start, word)

    def dfa_match(self, word):
        return DFA.dfa_match(self.dfa_graph, self.dfa_start, self.dfa_accepts, word)

    def visualize_nfa(self):
        NFA.visualize_nfa(self.nfa_start).view()

    def visualize_dfa(self):
        DFA.visualize_dfa(self.dfa_graph, self.dfa_accepts).view()  
    
def test():
#     r8 = Regex("ab*")
#     r8.visualize_nfa()
#     assert r8.dfa_match("a")
#     assert r8.dfa_match("ab")
#     assert r8.dfa_match("abb")
#     r2 = Regex("a")
#     assert r2.dfa_match("a")
#     assert not r2.dfa_match("")
#     assert not r2.dfa_match("aa")
#     assert not r2.dfa_match("b")
#     r3 = Regex("a*")
#     assert r3.dfa_match("aa")
#     assert not r3.dfa_match("b")
#     assert r3.dfa_match("")
#     assert r3.dfa_match("a")
#     r4 = Regex("a|b")
#     assert not r4.dfa_match("ab")
#     assert not r4.dfa_match("")
#     assert r4.dfa_match("a")
#     assert r4.dfa_match("b")
#     r5 = Regex("ab")
#     r8.visualize_nfa()
#     r5.visualize_dfa()
#     assert r5.dfa_match("ab")
#     assert not r5.dfa_match("")
#     assert not r5.dfa_match("a")
#     assert not r5.dfa_match("b")
#     r6 = Regex("((a|b)c)*")
#     assert r6.dfa_match("")
#     assert r6.dfa_match("ac")
#     assert r6.dfa_match("bc")
#     assert r6.dfa_match("acac")
#     assert r6.dfa_match("acbc")
#     assert not r6.dfa_match("ab")
#     assert not r6.dfa_match("a")
#     assert not r6.dfa_match("b")
#     r7 = Regex("a(b|c)*")
#     assert r7.dfa_match("a")
#     assert r7.dfa_match("ac")
#     assert r7.dfa_match("acc")
#     assert r7.dfa_match("abbb")
#     assert not r7.dfa_match("bc")
#     assert not r7.dfa_match("bcc")   
#     r8 = Regex("a*(b?|c+)*")
#     r8.visualize_nfa()
#     r8.visualize_dfa()
#     assert r8.dfa_match("")
#     assert r8.dfa_match("a")
#     assert r8.dfa_match("b")
#     assert r8.dfa_match("c")
#     assert r8.dfa_match("ab")
#     assert r8.dfa_match("ac")
#     assert r8.dfa_match("bb") # tricky, can be closure of 0or1
#     assert r8.dfa_match("cc")
#     assert r8.dfa_match("aab")
#     assert r8.dfa_match("abb")
#     assert r8.dfa_match("acc")
#     assert r8.dfa_match("aabb")
#     assert r8.dfa_match("aacc")
#     assert r8.dfa_match("bc")
#     assert r8.dfa_match("cb")
#     assert r8.dfa_match("abc")
#     assert r8.dfa_match("acb")
#     assert r8.dfa_match("ccb")
#     assert r8.dfa_match("bbc")
#     r9 = Regex("a?")
#     r9.visualize_nfa()
#     assert r9.dfa_match("")
#     assert r9.dfa_match("a")
#     assert not r9.dfa_match("aa")
#     assert not r9.dfa_match("b")
#     assert not r9.dfa_match("ab")
#     assert not r9.dfa_match("ba")
#     r10 = Regex("a+")
#     r10.visualize_nfa()
#     assert r10.dfa_match("a")
#     assert r10.dfa_match("aa")
#     assert not r10.dfa_match("")
#     assert not r10.dfa_match("b")
#     assert not r10.dfa_match("ab")
#     assert not r10.dfa_match("ba")
    r11 = Regex("(a|b)*")
    r11.visualize_dfa()
    assert r11.dfa_match("ab")
    assert r11.dfa_match("abababba")
    assert r11.dfa_match("")
    assert r11.dfa_match("a")
    assert r11.dfa_match("b")

if __name__ == "__main__":
    test()
