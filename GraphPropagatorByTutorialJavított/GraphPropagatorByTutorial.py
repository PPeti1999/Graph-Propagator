from z3 import *

# Parse SMTLIB constraints
example = """
(declare-datatypes () ((Node
(|Node1| )
(|Node2| )
(|Node3| )
(|Node4| )
(|Node5| )
)))

(declare-fun Edge (Node Node) Bool)
(declare-fun Reachable (Node Node) Bool)

(declare-const Start Node)
(declare-const Goal Node)

(assert (forall ((n1 Node) (n2 Node))
    (= (Reachable n1 n2)
       (or (Edge n1 n2)
           (exists ((x Node)) (and (Edge n1 x) (Reachable x n2)))))))

(assert (Reachable Start Goal))
(assert (not (= Start Goal)))
(check-sat)
(get-model)
"""

# Step 1: Define the domain `Sort` and relations
Node = DatatypeSort("Node")
Edge = PropagateFunction("Edge", Node, Node, BoolSort())
Reachable = PropagateFunction("Reachable", Node, Node, BoolSort())
Start = Const("Start", Node)
Goal = Const("Goal", Node)
fmls = parse_smt2_string(example, decls={"Edge": Edge, "Reachable": Reachable})
[Node1, Node2, Node3, Node4, Node5] = [Node.constructor(i) for i in range(Node.num_constructors())]

edgeTable = [
    (Node1, Node2),
    (Node2, Node3),
    (Node3, Node4),
    (Node4, Node5)
]

# Compute reachability table dynamically
reachabilityTable = []
nodes = [Node1, Node2, Node3, Node4, Node5]
for i in range(len(nodes)):
    for j in range(i+1, len(nodes)):
        reachabilityTable.append((nodes[i], nodes[j]))

constructors = {con() for con in [Node1, Node2, Node3, Node4, Node5]}

# Compute the reflexive transitive closure
def rtc(constructors, bin):
    step = {k: set([]) for k in constructors}
    for k, v in bin:
        step[k()] |= {v()}
    t = {k: {k} for k in constructors}
    change = True
    while change:
        change = False
        for k, vs in t.items():
            sz0 = len(vs)
            vs |= {w for v in vs for w in step[v] if w not in vs}
            if len(vs) > sz0:
                change = True
    print("Reflexive Transitive Closure:", t)
    return t

# Node class for UnionFind
class Node:
    def __init__(self, a):
        self.term = a
        self.id = a.get_id()
        self.root = self
        self.size = 1
        self.value = None

    def __eq__(self, other):
        return self.id == other.id

    def __ne__(self, other):
        return self.id != other.id
    
    def to_string(self):
        return f"{self.term} -> r:{self.root.term}"

    def __str__(self):
        return self.to_string()

# UnionFind class for equivalence management
class UnionFind:
    def __init__(self, trail):
        self._nodes = {}
        self.trail = trail

    def node(self, a):
        if a in self._nodes:
            return self._nodes[a]
        n = Node(a)
        self._nodes[a] = n
        def undo():
            del self._nodes[a]
        self.trail.append(undo)
        return n

    def merge(self, a, b):
        a = self.node(a)
        b = self.node(b)
        a = self.find(a)
        b = self.find(b)
        if a == b:
            return
        if a.size < b.size:
            a, b = b, a
        if a.value is not None and b.value is not None:
            print("Merging two values", a, a.value, b, b.value)
            return False
        value = a.value
        if b.value is not None:
            value = b.value        
        old_root = b.root
        old_asize = a.size
        old_bvalue = b.value
        old_avalue = a.value
        b.root = a.root
        b.value = value
        a.value = value
        a.size += b.size
        def undo():
            b.root = old_root
            a.size = old_asize
            b.value = old_bvalue
            a.value = old_avalue
        self.trail.append(undo)
        return True

    def find(self, a):
        assert isinstance(a, Node)
        root = a.root
        while root != root.root:
            root = root.root
        return root

    def set_value(self, a):
        n = self.find(self.node(a))
        if n.value is not None:
            return
        def undo():
            n.value = None
        n.value = a
        self.trail.append(undo)

    def get_value(self, a):
        return self.find(self.node(a)).value        

    def root_term(self, a):
        return self.find(self.node(a)).term

    def __str__(self):
        return self.to_string()

    def __repr__(self):
        return self.to_string()

    def to_string(self):
        return "\n".join([n.to_string() for t, n in self._nodes.items()])

# Custom Propagator Class
class TC(UserPropagateBase):
    def __init__(self, s=None, ctx=None):
        UserPropagateBase.__init__(self, s, ctx)
        self.trail = []
        self.lim = []
        self.add_fixed(lambda x, v: self._fixed(x, v))
        self.add_final(lambda: self._final())
        self.add_eq(lambda x, y: self._eq(x, y))
        self.add_created(lambda t: self._created(t))
        self.uf = UnionFind(self.trail)
        for v in constructors:
            self.uf.set_value(v)
        self.first = True
        self._fixed_le = []
        self._fixed_le_syntax = []
        self._fixed_le_table = rtc(constructors, edgeTable)
        self._fixed_le_syntax_table = rtc(constructors, reachabilityTable)

    def push(self):
        self.lim += [len(self.trail)]

    def pop(self, n):
        head = self.lim[len(self.lim) - n]
        while len(self.trail) > head:
            self.trail[-1]()
            self.trail.pop(-1)
        self.lim = self.lim[0:len(self.lim)-n]

    def fresh(self, new_ctx):
        return TC(ctx=new_ctx)

    def _fixed(self, x, v):        
        print("fixed: ", x, " := ", v)
        if x.decl().eq(Edge):
            self._fixed_trail(x, v, self._fixed_le_table, self._fixed_le)
        elif x.decl().eq(Reachable):
            self._fixed_trail(x, v, self._fixed_le_syntax_table, self._fixed_le_syntax)

    def _fixed_trail(self, x, v, table, trail):
        if self.check_conflict(x, v, table):
            return
        trail.append((x,v))
        def undo():
            trail.pop(-1)
        self.trail.append(undo)

    def _created(self, t):
        print("Created", t)
        self.add(t)
        if t.decl() in [Edge, Reachable]:
            x, y = t.arg(0), t.arg(1)
            self.add(x)
            self.add(y)
        if self.first:
            self.first = False
            for v in constructors:
                self.add(v)

    def _eq(self, x, y):
        print(x, " = ", y)
        if not self.uf.merge(x, y):
            self.conflict()

    def _final(self):
        print("Final check")
        self.check_rtc(self._fixed_le, self._fixed_le_table)
        self.check_rtc(self._fixed_le_syntax, self._fixed_le_syntax_table)

    def check_conflict(self, f, v, rtc, is_final=False):
        a, b = f.arg(0), f.arg(1)
        va, vb = self.uf.get_value(a), self.uf.get_value(b)
        if va is None or vb is None:
            if is_final:
                print("Unassigned", a, va, b, vb)
                return True
            return False
        if is_true(v):
            if vb not in rtc[va]:
                print("Conflict: asserted relation should be included in TC", f, v, a, va, b, vb)
                self.conflict(deps=[f], eqs=[(a, va), (b, vb)])
                return True
        elif is_false(v):
            if vb in rtc[va]:
                print("Conflict: asserted negated relation should not be included in TC", f, v, a, va, b, vb)
                self.conflict(deps=[f], eqs=[(a, va), (b, vb)])
                return True
        return False

    def check_rtc(self, asserted, rtc):
        for f, v in asserted:
            if self.check_conflict(f, v, rtc, is_final=True):
                return

    def generate_subgraphs(self):
        subgraphs = {}
        for node in constructors:
            subgraphs[node] = self.uf.get_value(node)
        print("Subgraphs:", subgraphs)

# Create solver and propagator
s = Solver()
b = TC(s)

# Add constraints
for (a, b) in edgeTable:
    s.add(Edge(a(), b()))

# Add valid Start/Goal combinations
s.add(Start != Goal)
s.add(Or([And(Start == Node1(), Goal == Node3()),
          And(Start == Node1(), Goal == Node4()),
          And(Start == Node2(), Goal == Node4()),
          And(Start == Node2(), Goal == Node5()),
          And(Start == Node3(), Goal == Node5())]))

s.add(fmls)

# Run solver and print results
result = s.check()
print("\nSolver result:", result)
if result == sat:
    m = s.model()
    print("\nSolution found:")
    print("Start =", m[Start])
    print("Goal =", m[Goal])
    print("\nEdge relationships:")
    for src, dst in edgeTable:
        print(f"{src()} -> {dst()}")
    print("\nReachability relationships:")
    for src, dst in reachabilityTable:
        if m.eval(Reachable(src(), dst())):
            print(f"{src()} can reach {dst()}")
else:
    print("No solution found")