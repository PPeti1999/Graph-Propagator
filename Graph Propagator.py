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

    def _check_transitivity(self, u, v, w):
        """Add transitivity constraints to the solver."""
        rtc_u_w = Bool(f'rtc_{u}_{w}')
        rtc_w_v = Bool(f'rtc_{w}_{v}')
        rtc_u_v = Bool(f'rtc_{u}_{v}')
        return Implies(And(rtc_u_w, rtc_w_v), rtc_u_v)

    def detect_transitivity_conflicts(self):
        """Add transitivity constraints for all nodes to the solver."""
        for w in self.nodes:
            for u in self.nodes:
                for v in self.nodes:
                    constraint = self._check_transitivity(u, v, w)
                    self.solver.add(constraint)
        print("Transitivity constraints added.")

    def register_dynamic_term(self, term):
        """Register a dynamically created term."""
        print(f"Registering term dynamically: {term}")
        self.solver.add(term)

    def propagate_fixed_values(self, node, value):
        """Handle fixed value propagation dynamically."""
        print(f"Propagating fixed value for {node}: {value}")
        self.solver.add(Bool(f'fixed_{node}') == value)

    def handle_fixed_assignments(self):
        """Handle assignments to fixed values dynamically."""
        for node in self.nodes:
            fixed = Bool(f'fixed_{node}')
            self.solver.add(Implies(fixed, Or([Bool(f'fixed_{other}') for other in self.nodes if other != node])))
        print("Fixed assignments constraints added.")

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

    def compute_treedepth(self):
        """Compute the treedepth of the graph."""
        parent = {node: Int(f'parent_{node}') for node in self.nodes}
        depth = {node: Int(f'depth_{node}') for node in self.nodes}

        for node in self.nodes:
            self.solver.add(parent[node] >= 0)
            self.solver.add(depth[node] >= 0)

        for u, v in self.edges:
            self.solver.add(Implies(parent[u] == v, depth[u] == depth[v] + 1))

        max_depth = Int('max_depth')
        self.solver.add(max_depth == Max([depth[node] for node in self.nodes]))
        print("Treedepth computation added to constraints.")

    def propagate_union_distributive(self):
        """Model graph composition with union-distributive properties."""
        reach = {(u, v): Bool(f'reach_{u}_{v}') for u in self.nodes for v in self.nodes}

        for u, v in self.edges:
            self.solver.add(reach[u, v])

        for w in self.nodes:
            for u in self.nodes:
                for v in self.nodes:
                    self.solver.add(Implies(And(reach[u, w], reach[w, v]), reach[u, v]))

    def propagate_ifds(self):
        """Interprocedural data flow analysis using graph constraints."""
        flow = {(u, v): Bool(f'flow_{u}_{v}') for u in self.nodes for v in self.nodes}

        for u, v in self.edges:
            self.solver.add(flow[u, v])

        for w in self.nodes:
            for u in self.nodes:
                for v in self.nodes:
                    self.solver.add(Implies(And(flow[u, w], flow[w, v]), flow[u, v]))

    def propagate_data_dependency_graph(self):
        """Handle data dependency analysis using weighted graphs."""
        weights = {(u, v): Int(f'weight_{u}_{v}') for u, v in self.edges}

        for (u, v), weight in weights.items():
            self.solver.add(weight >= 0)

        for node in self.nodes:
            incoming = Sum([weights[e] for e in self.edges if e[1] == node])
            outgoing = Sum([weights[e] for e in self.edges if e[0] == node])
            self.solver.add(incoming == outgoing)

    def enforce_cycle_constraints(self):
        """Enforce constraints to prevent or allow specific cycles."""
        visited = {node: Bool(f'visited_{node}') for node in self.nodes}
        for u, v in self.edges:
            self.solver.add(Implies(visited[u], visited[v]))
        self.solver.add(Not(And([visited[node] for node in self.nodes])))  # Prevent full graph cycles

    def optimize_treewidth(self):
        """Optimize treewidth with weighted nodes or edges."""
        weight = {node: Int(f'weight_{node}') for node in self.nodes}
        for node in self.nodes:
            self.solver.add(weight[node] >= 1)
        total_weight = Sum([weight[node] for node in self.nodes])
        self.solver.add(total_weight <= len(self.nodes))

    def propagate_stateful_por(self):
        """Apply stateful partial order reduction (POR) constraints."""
        safe_set = {node: Bool(f'safe_{node}') for node in self.nodes}
        source_set = {node: Bool(f'source_{node}') for node in self.nodes}

        for u, v in self.edges:
            self.solver.add(Implies(safe_set[u], source_set[v]))

        # New logic for stateful POR based on dependency ordering
        for u, v in self.edges:
            if u != v:
                self.solver.add(Implies(source_set[u], Not(safe_set[v])))  # Avoid overlapping sources and safe sets

        # Ensure at least one safe node exists
        self.solver.add(Or([safe_set[node] for node in self.nodes]))  # At least one safe node
        print("Stateful partial order reduction constraints applied.")

    def propagate_dependency_graph(self):
        """Construct and validate dependencies using graph matrices."""
        dependency_matrix = {(u, v): Bool(f'dependency_{u}_{v}') for u in self.nodes for v in self.nodes}

        for u, v in self.edges:
            self.solver.add(dependency_matrix[u, v])

        for u in self.nodes:
            for v in self.nodes:
                self.solver.add(Implies(dependency_matrix[u, v], dependency_matrix[v, u]))  # Symmetric dependency

    def optimize_sparsity(self):
        """Leverage graph sparsity for optimization."""
        sparsity = Int('sparsity')
        edge_count = len(self.edges)
        node_count = len(self.nodes)

        # Existing sparsity formula
        self.solver.add(sparsity == edge_count - node_count + 1)  # Sparsity formula for undirected graphs
        self.solver.add(sparsity >= 0)

        # Advanced sparsity constraints (from the book)
        density = Real('density')
        self.solver.add(density == edge_count / (node_count * (node_count - 1)))  # Density formula
        self.solver.add(density <= 1)

        # Optimize sparsity with constraints on edge reduction
        sparsity_weight = Int('sparsity_weight')
        self.solver.add(sparsity_weight == Sum([1 for (u, v) in self.edges]))

        # Add constraints for sparsity minimization
        self.solver.add(sparsity_weight <= node_count)  # Example constraint
        print("Advanced sparsity optimization constraints added.")

    def final_check(self):
        """Perform final validation of all constraints."""
        print("Performing final checks.")
        for u, v in self.edges:
            if not self._check_reachability(u, v):
                print(f"Conflict detected between nodes {u} and {v}.")

    def _check_reachability(self, u, v):
        """Check if node v is reachable from node u."""
        visited = set()

        def dfs(node):
            if node == v:
                return True
            visited.add(node)
            for x, y in self.edges:
                if x == node and y not in visited:
                    if dfs(y):
                        return True
            return False

        return dfs(u)

    def push_state(self):
        """Push the current solver state."""
        self.solver.push()
        print("Solver state pushed.")

    def pop_state(self):
        """Pop the solver state."""
        self.solver.pop()
        print("Solver state popped.")

    def log_event(self, event):
        """Log an event for debugging purposes."""
        print(f"Event logged: {event}")

    def create_nested_solver(self):
        """Simulate nested solver creation."""
        nested_solver = Solver()
        print("Nested solver created.")
        return nested_solver

    def explain_conflict(self, u, v):
        """Explain the cause of a conflict."""
        print(f"Conflict: Path between {u} and {v} violates constraints.")

    def fresh_context(self):
        """Create a fresh solver context."""
        return Solver()

    def explore_model(self):
        """Explore the model of the solver."""
        if self.solver.check() == sat:
            model = self.solver.model()
            print("Model found:")
            for d in model.decls():
                print(f"{d.name()} = {model[d]}")
        else:
            print("No model found.")

    def add_assertions(self, *constraints):
        """Add multiple assertions to the solver."""
        for constraint in constraints:
            self.solver.add(constraint)
        print("Assertions added to the solver.")

    def run_tests(self):
        """Run automated tests on the graph."""
        print("Running tests...")
        self.propagate_rtc()
        self.detect_transitivity_conflicts()
        self.push_state()
        result = self.solver.check()
        print(f"Test result: {result}")
        self.pop_state()

    def is_connected(self):
        """Check if the graph is connected using RTC."""
        for u in self.nodes:
            for v in self.nodes:
                if u != v:
                    connected = Bool(f'rtc_{u}_{v}')
                    if self.solver.check(connected) != sat:
                        return False
        return True

    def is_acyclic(self):
        """Check if the graph is acyclic."""
        visited = {node: Bool(f'visited_{node}') for node in self.nodes}
        for u, v in self.edges:
            if self.solver.check(Implies(visited[u], visited[v])) != sat:
                return False
        return True
    
    def test_connectivity(propagator):
        print("Checking connectivity...")
        if propagator.is_connected():
            print("The graph is connected.")
        else:
            print("The graph is not connected.")

    def test_acyclicity(propagator):
        print("Checking acyclicity...")
        if propagator.is_acyclic():
            print("The graph is acyclic.")
        else:
            print("The graph has a cycle.")
# Example usage
if __name__ == "__main__":
     ##########################################################################################BAsic
    solver = Solver()
    propagator = GraphConstraintPropagator(solver)

    propagator.add_node('A')
    propagator.add_node('B')
    propagator.add_node('C')
    propagator.add_edge('A', 'B')
    propagator.add_edge('B', 'C')

    propagator.propagate_rtc()
    propagator.detect_transitivity_conflicts()
    propagator.propagate_fixed_values('A', True)
    propagator.register_dynamic_term(Bool('dynamic_term'))

    propagator.propagate_k_hop_dominance(2)
    propagator.handle_fixed_assignments()

    propagator.push_state()
    propagator.final_check()
    propagator.pop_state()

    # Demonstrate nested solver usage
    nested_solver = propagator.create_nested_solver()

    result = solver.check()
    print(f"Solver result: {result}")

    # Explore the model
    propagator.explore_model()

    # Run automated tests
    propagator.run_tests()

    # Add example assertions
    propagator.add_assertions(Bool('example_assertion_1'), Bool('example_assertion_2'))
    result = solver.check()
    print(f"Solver result after adding assertions: {result}")
    #################################################################################################vvTest Tutorial alapja
    def test_connectivity(propagator):
        print("Checking connectivity...")
        if propagator.is_connected():
            print("The graph is connected.")
        else:
            print("The graph is not connected.")

    def test_acyclicity(propagator):
        print("Checking acyclicity...")
        if propagator.is_acyclic():
            print("The graph is acyclic.")
        else:
            print("The graph has a cycle.")

    s = Solver()
    b = GraphConstraintPropagator(s)
    
    # Add nodes and edges
    b.add_node('A')
    b.add_node('B')
    b.add_edge('A', 'B')
    
    # Add RTC constraints and SMT formulas
    b.propagate_rtc()
    s.add(Bool('example_assertion_1'))
    
    # Check satisfiability
    print(s.check())
    
    solver = Solver()
    propagator = GraphConstraintPropagator(solver)

    # Define a graph
    propagator.add_node('A')
    propagator.add_node('B')
    propagator.add_node('C')
    propagator.add_edge('A', 'B')
    propagator.add_edge('B', 'C')

    # Propagate RTC and check transitivity
    propagator.propagate_rtc()
    propagator.detect_transitivity_conflicts()

    # Test connectivity and acyclicity
    test_connectivity(propagator)
    test_acyclicity(propagator)

    # Explore the model
    print("Exploring the model:")
    propagator.explore_model()

    # Summary
    print("\nSummary:")
    print(f"RTC constraints added: {len(propagator.edges)} edges processed.")
    print("Solver state: satisfiable" if solver.check() == sat else "Solver state: unsatisfiable")