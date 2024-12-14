from z3 import *

class GraphConstraintPropagator:
    def __init__(self, solver):
        self.solver = solver
        self.edges = []
        self.nodes = set()
        self.parent = {}

    def add_node(self, node):
        """Add a node to the graph."""
        self.nodes.add(node)
        self.parent[node] = node

    def add_edge(self, u, v):
        """Add an edge to the graph."""
        self.edges.append((u, v))
        self.nodes.add(u)
        self.nodes.add(v)
        self.parent.setdefault(u, u)
        self.parent.setdefault(v, v)

    def find(self, node):
        """Union-Find: Find the root of a node."""
        if self.parent[node] != node:
            self.parent[node] = self.find(self.parent[node])
        return self.parent[node]

    def union(self, u, v):
        """Union-Find: Merge two sets."""
        root_u = self.find(u)
        root_v = self.find(v)
        if root_u != root_v:
            self.parent[root_u] = root_v

    def propagate_rtc(self):
        """Propagate Reflexive Transitive Closure (RTC)."""
        rtc_table = {(u, v): Bool(f'rtc_{u}_{v}') for u in self.nodes for v in self.nodes}

        for u in self.nodes:
            for v in self.nodes:
                if u == v:
                    self.solver.add(rtc_table[u, v])  # Reflexivity

        for u, v in self.edges:
            self.solver.add(rtc_table[u, v])  # Direct edges

        for w in self.nodes:
            for u in self.nodes:
                for v in self.nodes:
                    self.solver.add(Implies(And(rtc_table[u, w], rtc_table[w, v]), rtc_table[u, v]))  # Transitivity

        print("RTC propagation constraints added.")

    def rtc(self, constructors, bin):
        """Compute the reflexive transitive closure of a binary relation."""
        step = {k: set([]) for k in constructors}
        for k, v in bin:
            step[k()] |= {v()}
        t = {k: {k} for k in constructors}
        change = True
        while change:
            change = False
            for k, vs in t.items():
                sz0 = len(vs)
                vs |= {w for v in vs for w in step[v]}
                if len(vs) > sz0:
                    change = True
        print("RTC computed:", t)
        return t

    def detect_transitivity_conflicts(self):
        """Add transitivity constraints for all nodes to the solver."""
        for w in self.nodes:
            for u in self.nodes:
                for v in self.nodes:
                    rtc_u_w = Bool(f'rtc_{u}_{w}')
                    rtc_w_v = Bool(f'rtc_{w}_{v}')
                    rtc_u_v = Bool(f'rtc_{u}_{v}')
                    self.solver.add(Implies(And(rtc_u_w, rtc_w_v), rtc_u_v))
        print("Transitivity constraints added.")

    def enforce_cycle_constraints(self):
        """Enforce constraints to prevent or allow specific cycles."""
        visited = {node: Bool(f'visited_{node}') for node in self.nodes}
        for u, v in self.edges:
            self.solver.add(Implies(visited[u], visited[v]))
        self.solver.add(Not(And([visited[node] for node in self.nodes])))  # Prevent full graph cycles
        print("Cycle constraints enforced.")

    def detect_cycles(self):
        """Return the nodes involved in a cycle if any."""
        print("Detecting cycles...")
        visited = {node: False for node in self.nodes}
        stack = set()

        def dfs(node):
            if node in stack:
                return True, node
            if visited[node]:
                return False, None
            visited[node] = True
            stack.add(node)
            for u, v in self.edges:
                if u == node:
                    has_cycle, cycle_start = dfs(v)
                    if has_cycle:
                        return True, cycle_start
            stack.remove(node)
            return False, None

        for node in self.nodes:
            has_cycle, cycle_start = dfs(node)
            if has_cycle:
                print(f"Cycle detected starting at: {cycle_start}")
                return True, cycle_start
        print("No cycles detected.")
        return False, None

    def propagate_k_hop_dominance(self, k):
        """Propagate k-hop dominance."""
        dominant = {node: Bool(f'dominant_{node}') for node in self.nodes}
        distance = {(u, v): Int(f'distance_{u}_{v}') for u in self.nodes for v in self.nodes}

        for u in self.nodes:
            for v in self.nodes:
                if u == v:
                    self.solver.add(distance[u, v] == 0)
                else:
                    self.solver.add(distance[u, v] >= 0)

        for u, v in self.edges:
            self.solver.add(distance[u, v] == 1)

        for w in self.nodes:
            for u in self.nodes:
                for v in self.nodes:
                    self.solver.add(distance[u, v] <= distance[u, w] + distance[w, v])

        for node in self.nodes:
            self.solver.add(Or([And(dominant[n], distance[node, n] <= k) for n in self.nodes]))
        print(f"{k}-hop dominance propagated.")

    def add_dynamic_assertions(self, *constraints):
        """Add user-defined assertions to the solver."""
        for constraint in constraints:
            self.solver.add(constraint)
        print("Dynamic assertions added.")

    def load_graph_from_file(self, filename):
        """Load a graph from an adjacency list file."""
        with open(filename, 'r') as f:
            for line in f:
                nodes = line.strip().split()
                if len(nodes) == 2:
                    self.add_edge(nodes[0], nodes[1])
                else:
                    self.add_node(nodes[0])
        print(f"Graph loaded from {filename}.")

    def test_connectivity(self):
        """Check if the graph is connected."""
        print("Checking connectivity...")
        for u in self.nodes:
            for v in self.nodes:
                if u != v:
                    connected = Bool(f'rtc_{u}_{v}')
                    if self.solver.check(connected) != sat:
                        print("The graph is not connected.")
                        return False
        print("The graph is connected.")
        return True

    def test_acyclicity(self):
        """Check if the graph is acyclic."""
        print("Checking acyclicity...")
        visited = {node: Bool(f'visited_{node}') for node in self.nodes}
        for u, v in self.edges:
            if self.solver.check(Implies(visited[u], visited[v])) != sat:
                print("The graph has a cycle.")
                return False
        print("The graph is acyclic.")
        return True

    def explore_model(self):
        """Explore the model of the solver."""
        if self.solver.check() == sat:
            model = self.solver.model()
            print("Model found:")
            for d in model.decls():
                print(f"{d.name()} = {model[d]}")
        else:
            print("No model found.")

    def run_tests(self):
        """Run automated tests on the graph."""
        print("Running tests...")
        self.propagate_rtc()
        self.detect_transitivity_conflicts()
        self.test_connectivity()
        self.test_acyclicity()
        self.explore_model()

# Example usage
if __name__ == "__main__":
    solver = Solver()
    propagator = GraphConstraintPropagator(solver)

    # Define a graph
    propagator.add_node('A')
    propagator.add_node('B')
    propagator.add_node('C')
    propagator.add_edge('A', 'B')
    propagator.add_edge('B', 'C')
    propagator.add_edge('C', 'A')  # Intentional cycle to test constraints

    # Detect cycles
    propagator.detect_cycles()

    # Propagate k-hop dominance example
    propagator.propagate_k_hop_dominance(2)

    # Add dynamic assertions
    propagator.add_dynamic_assertions(Bool('example_assertion_1'))

    # Run tests
    propagator.run_tests()
