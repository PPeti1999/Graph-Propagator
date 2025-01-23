from z3 import *

# Example
# Parse SMTLIB constraints for graph-based properties.
example = """
(declare-datatypes () ((GraphNode
    (|NodeA| )
    (|NodeB| )
    (|NodeC| )
    (|NodeD| )
    (|NodeE| )
)))

(declare-fun edge (GraphNode GraphNode) Bool)

(declare-const |Node1| GraphNode)
(declare-const |Node2| GraphNode)
(declare-const |Node3| GraphNode)
(declare-const |Node4| GraphNode)
(declare-const |Node5| GraphNode)

; Define a structure to hold graph solutions
(declare-datatypes () 
    ((SolutionVariables 
        (SolVars 
            (|Sol_Node1| GraphNode) 
            (|Sol_Node2| GraphNode) 
            (|Sol_Node3| GraphNode)
        )
    ))
)

(declare-datatypes () 
    ((Solution 
        (Sol 
            (vars SolutionVariables) 
            (|Sol_Edge| GraphNode)
        )
    ))
)

(define-fun theSolution () Solution 
    (Sol (SolVars |Node1| |Node2| |Node3|) |Node5| )
)

; Reflexive and transitive closure for edge relations
(define-fun edgeExists ((n1 GraphNode) (n2 GraphNode)) Bool 
    (or 
        (= n1 n2)
        (exists ((mid GraphNode)) 
            (and (edge n1 mid) (edge mid n2))
        )
    )
)

; Connectivity constraint: all nodes must be reachable
(define-fun isConnected ((n1 GraphNode) (n2 GraphNode)) Bool 
    (edgeExists n1 n2)
)

; Check that the graph is acyclic
(define-fun isAcyclic ((start GraphNode)) Bool
    (forall ((n1 GraphNode) (n2 GraphNode))
        (=> 
            (edge n1 n2)
            (not (edgeExists n2 n1))
        )
    )
)

; Assert connectivity
(assert (and 
    (isConnected |NodeA| |NodeB|) 
    (isConnected |NodeB| |NodeC|) 
    (isConnected |NodeC| |NodeD|) 
    (isConnected |NodeD| |NodeE|)
))

; Assert acyclicity
(assert (isAcyclic |NodeA|))

; Additional constraints to test
(assert (distinct |NodeA| |NodeB|))
(assert (distinct |NodeC| |NodeD|))
(assert (distinct |NodeE| |NodeA|))

; Solve for properties of the graph
(check-sat)
(get-model)

; Test alternative constraints
(assert (not (isConnected |NodeA| |NodeE|)))
(check-sat)
(get-model)

; Test edge relationships
(assert (edge |NodeA| |NodeB|))
(assert (not (edge |NodeB| |NodeA|)))
(check-sat)
(get-model)
"""
# Parse the SMT-LIB string
GraphNode = DatatypeSort("GraphNode")
edge = PropagateFunction("edge", GraphNode, GraphNode, BoolSort())

# Parse the SMT constraints
fmls = parse_smt2_string(example, decls={"edge": edge})

# Define constructors for `GraphNode`
NodeA, NodeB, NodeC, NodeD, NodeE = [
    GraphNode.constructor(i)() for i in range(GraphNode.num_constructors())
]

# Define table-based constraints for graph edges
edgeTable = [
    (NodeA, NodeB),
    (NodeB, NodeC),
    (NodeC, NodeD),
    (NodeD, NodeE)
]

# Collect all constructors into a set
constructors = {NodeA, NodeB, NodeC, NodeD, NodeE}
# Step 1: Define the Rtc function for reflexive-transitive closure
def rtc(constructors, edges):
    closure = {k: {k} for k in constructors}  # Reflexív elemek
    for a, b in edges:
        closure[a].add(b)
    change = True
    while change:
        change = False
        for a in constructors:
            new_reachable = set().union(*(closure[b] for b in closure[a]))
            if new_reachable - closure[a]:
                closure[a].update(new_reachable)
                change = True
    return closure

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


# Step 2: Define the Union-Find class for connected components
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
            raise RuntimeError("UnionFind merge conflict: Attempting to merge two values.")
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

    # skip path compression to keep the example basic
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


# Step 4: Custom Propagator Class for graphs
class TC(UserPropagateBase):
    def __init__(self, s=None, ctx=None):
        UserPropagateBase.__init__(self, s, ctx)
        self.trail = []  # Trail for backtracking
        self.lim = []  # Push/Pop limits
        self.add_fixed(lambda x, v: self._fixed(x, v))
        self.add_final(lambda: self._final())
        self.add_eq(lambda x, y: self._eq(x, y))
        self.add_created(lambda t: self._created(t))

        self.uf = UnionFind(self.trail)  # Union-Find for equivalence classes

        # Initialize constructors in Union-Find
        for v in constructors:
            self.uf.set_value(v)

        self.first = True
        self._fixed_edges = []  # To track fixed edge assignments
        self._fixed_edge_table = rtc(constructors, self._fixed_edges)

    def push(self):
        self.lim.append(len(self.trail))
        print("State pushed. Current limit stack:", self.lim)

    def pop(self, n):
        head = self.lim[-n]
        print(f"Restoring state to trail position {head}")
        while len(self.trail) > head:
            self.trail.pop()()
        self.lim = self.lim[:-n]
        print("State restored.")

    def fresh(self, new_ctx):
        return TC(ctx=new_ctx)

    def _fixed(self, x, v):
        print(f"Fixed: {x} := {v}")
        if x.decl().name() == "edge":
            a, b = x.arg(0), x.arg(1)
            if is_true(v):
                self._check_connectivity_and_acyclicity(a, b)
                self.conflict(deps=[x])  
            elif is_false(v):
                print(f"Edge {a} -> {b} explicitly disabled.")

    def _check_connectivity_and_acyclicity(self, a, b):
        print(f"Checking edge: {a} -> {b}")
        self._fixed_edges.append((a, b))
        self._fixed_edge_table = rtc(constructors, self._fixed_edges)

        print("RTC Table:", self._fixed_edge_table)
        
        if not self.check_connectivity():
            print("Connectivity failure detected.")
            self.conflict(deps=[edge(a, b)])

        if not self.check_acyclicity():
            print("Cycle detected.")
            self.conflict(deps=[edge(a, b)])

    def _created(self, t):
        print("Created:", t)
        if t.decl().name() == "edge":
            a, b = t.arg(0), t.arg(1)
            self._check_connectivity_and_acyclicity(a, b)

    def _eq(self, x, y):
        print(f"{x} = {y}")
        self.uf.merge(x, y)

    def _final(self):
        print("Performing final checks...")
        if not self.check_connectivity():
            print("Final Conflict: Graph is not connected.")
        if not self.check_acyclicity():
            print("Final Conflict: Graph contains a cycle.")
        print("Final checks completed.")

    def check_connectivity(self):
        # Recompute reflexive-transitive closure with fixed edges
        closure = rtc(constructors, self._fixed_edges)
        # Check if all nodes are reachable from a single root
        for node in constructors:
            if not all(node in closure[start] for start in constructors):
                return False
        return True

    def check_acyclicity(self):
        visited = set()
        stack = set()

        def dfs(node):
            if node in stack:
                return False  # Cycle detected
            if node in visited:
                return True
            visited.add(node)
            stack.add(node)
            for a, b in self._fixed_edges:
                if a == node:
                    if not dfs(b):
                        return False
            stack.remove(node)
            return True

        for node in constructors:
            if not dfs(node):
                return False
        return True

    def check_conflict(self, f, v, rtc, is_final=False):
        a, b = f.arg(0), f.arg(1)
        va, vb = self.uf.get_value(a), self.uf.get_value(b)

        if va is None or vb is None:
            if is_final:
                print("Unassigned values during final check:", a, va, b, vb)
            return False

        if is_true(v):
            if vb not in rtc[va]:
                print(f"Conflict: {a} -> {b} not in RTC.")
                self.conflict(deps=[f])
                return True
        elif is_false(v):
            if vb in rtc[va]:
                print(f"Conflict: {a} -> {b} should not be in RTC.")
                self.conflict(deps=[f])
                return True

        return False

    


# Step 5: Use the Propagator with Solver
s = Solver()
b = TC(s)

# Add constraints
for a, b in edgeTable:
    s.add(edge(a, b))

s.add(fmls)

# Run the solver
print(s.check())
