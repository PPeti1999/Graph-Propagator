from z3 import *

class GraphConstraintPropagator(UserPropagateBase):
    def __init__(self, solver=None, context=None):
        super().__init__(solver, context)
        self.trail = []  # For backtracking
        self.limit = []  # To handle scopes

        # Callback registrations
        self.add_fixed(self._fixed)
        self.add_eq(self._eq)
        self.add_created(self._created)
        self.add_final(self._final)

        # Structures for graph constraint propagation
        self.nodes = set()
        self.edges = []  # List of edges (u, v)
        self.reachability_table = {}  # Dynamic transitive closure

    def push(self):
        """Handles scope entry in Z3's solving process."""
        self.limit.append(len(self.trail))

    def pop(self, n):
        """Handles scope exit in Z3's solving process."""
        head = self.limit[-n]
        while len(self.trail) > head:
            self.trail.pop()()
        self.limit = self.limit[:-n]

    def fresh(self, ctx):
        """Handles fresh context creation in Z3's solving process."""
        return GraphConstraintPropagator(context=ctx)

    def add_node(self, node):
        """Add a node to the graph."""
        self.nodes.add(node)

    def add_edge(self, u, v):
        """Add an edge to the graph."""
        self.edges.append((u, v))
        self.add(Implies(Bool(f'reachable_{u}'), Bool(f'reachable_{v}')))

    def _fixed(self, var, value):
        """Handle fixed values assigned during solving."""
        print(f"Fixed: {var} := {value}")
        # Update transitive closure dynamically
        self._update_reachability()

    def _eq(self, var1, var2):
        """Handle new equalities discovered during solving."""
        print(f"Equality: {var1} == {var2}")
        self._merge_nodes(var1, var2)

    def _created(self, term):
        """Handle new terms created during solving."""
        print(f"Created: {term}")
        if term.decl().name() == "reachable":
            self.add(term)

    def _final(self):
        """Perform final checks for consistency."""
        print("Final Check")
        for u, v in self.edges:
            if not self._check_reachability(u, v):
                self.conflict(deps=[Bool(f'reachable_{u}'), Bool(f'reachable_{v}')])

    def _update_reachability(self):
        """Update the dynamic reachability table."""
        for u, v in self.edges:
            if u not in self.reachability_table:
                self.reachability_table[u] = set()
            self.reachability_table[u].add(v)
            # Propagate transitivity
            for mid in self.reachability_table.get(u, []):
                self.reachability_table[mid] |= self.reachability_table[u]

    def _merge_nodes(self, var1, var2):
        """Merge nodes for equality handling."""
        if var1 in self.reachability_table:
            self.reachability_table[var1] |= self.reachability_table.get(var2, set())
        if var2 in self.reachability_table:
            self.reachability_table[var2] |= self.reachability_table.get(var1, set())

    def _check_reachability(self, u, v):
        """Check if reachability is consistent."""
        reachable = self.reachability_table.get(u, set())
        return v in reachable

    def compute_components(self):
        """Compute connected components in the graph."""
        visited = set()
        components = []

        def dfs(node, component):
            visited.add(node)
            component.add(node)
            for u, v in self.edges:
                if u == node and v not in visited:
                    dfs(v, component)

        for node in self.nodes:
            if node not in visited:
                component = set()
                dfs(node, component)
                components.append(component)

        print(f"Components: {components}")
        return components

    def detect_cycles(self):
        """Detect cycles in the graph."""
        visited = set()
        stack = set()

        def visit(node):
            if node in stack:
                return True
            if node in visited:
                return False

            visited.add(node)
            stack.add(node)

            for u, v in self.edges:
                if u == node and visit(v):
                    return True

            stack.remove(node)
            return False

        for node in self.nodes:
            if visit(node):
                print("Cycle detected!")
                return True

        print("No cycles detected.")
        return False

    def compute_tree_depth(self):
        """Compute the depth of the graph if it is a tree."""
        def dfs_depth(node, depth):
            max_depth = depth
            for u, v in self.edges:
                if u == node:
                    max_depth = max(max_depth, dfs_depth(v, depth + 1))
            return max_depth

        if self.detect_cycles():
            print("Cannot compute depth: the graph contains a cycle.")
            return -1

        root_candidates = self.nodes - {v for _, v in self.edges}
        if len(root_candidates) != 1:
            print("Cannot compute depth: the graph is not a tree.")
            return -1

        root = next(iter(root_candidates))
        depth = dfs_depth(root, 0)
        print(f"Tree depth: {depth}")
        return depth

    def compute_treedepth(self):
        """Compute the treedepth of the graph using a POT."""
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

    def lazy_propagation(self):
        """Implement lazy constraint generation for RTC."""
        print("Lazy propagation started.")
        for u, v in self.edges:
            self.add(Implies(Bool(f'reachable_{u}'), Bool(f'reachable_{v}')))
        print("Lazy constraints dynamically added.")

    def propagate_ifds(self):
        """Interprocedural data flow analysis using graph constraints."""
        flow = {(u, v): Bool(f'flow_{u}_{v}') for u in self.nodes for v in self.nodes}

        for u, v in self.edges:
            self.solver.add(flow[u, v])

        for w in self.nodes:
            for u in self.nodes:
                for v in self.nodes:
                    self.solver.add(Implies(And(flow[u, w], flow[w, v]), flow[u, v]))

        print("IFDS propagation added.")

    def propagate_data_dependency_graph(self):
        """Handle data dependency analysis using weighted graphs."""
        weights = {(u, v): Int(f'weight_{u}_{v}') for u, v in self.edges}

        for (u, v), weight in weights.items():
            self.solver.add(weight >= 0)

        for node in self.nodes:
            incoming = Sum([weights[e] for e in self.edges if e[1] == node])
            outgoing = Sum([weights[e] for e in self.edges if e[0] == node])
            self.solver.add(incoming == outgoing)

        print("Data dependency constraints applied.")

    def enforce_cycle_constraints(self):
        """Enforce constraints to prevent or allow specific cycles."""
        visited = {node: Bool(f'visited_{node}') for node in self.nodes}
        for u, v in self.edges:
            self.solver.add(Implies(visited[u], visited[v]))
        self.solver.add(Not(And([visited[node] for node in self.nodes])))  # Prevent full graph cycles
        print("Cycle constraints enforced.")

    def propagate_k_hop_dominance(self, k):
        """Propagate k-hop dominance constraints."""
        print("K-hop dominance propagation started.")
        dominance = {node: {node} for node in self.nodes}

        for _ in range(k):
            new_dominance = {node: set(dominance[node]) for node in self.nodes}
            for u, v in self.edges:
                new_dominance[u].update(dominance[v])
            dominance = new_dominance

        for node, dom_nodes in dominance.items():
            print(f"Node {node} dominates: {dom_nodes}")

    def final_check(self, ctx):
        """Perform final verification of all constraints."""
        print("Final check triggered.")

        # Validate RTC
        self.lazy_propagation()

        # Validate reachability constraints
        for u, v in self.edges:
            if not self.solver.check():
                print(f"Final check failed for edge {u} -> {v}.")

        print("Final validation completed.")

# Usage Example
def main():
    solver = Solver()
    propagator = GraphConstraintPropagator(solver)

    # Define graph
    propagator.add_node('A')
    propagator.add_node('B')
    propagator.add_node('C')
    propagator.add_edge('A', 'B')
    propagator.add_edge('B', 'C')

    # Compute components
    propagator.compute_components()

    # Detect cycles
    propagator.detect_cycles()

    # Compute tree depth
    propagator.compute_tree_depth()

    # Compute treedepth
    propagator.compute_treedepth()

    # Lazy propagation
    propagator.lazy_propagation()

    # IFDS propagation
    propagator.propagate_ifds()

    # Data dependency graph propagation
    propagator.propagate_data_dependency_graph()

    # Enforce cycle constraints
    propagator.enforce_cycle_constraints()

    # Propagate k-hop dominance
    propagator.propagate_k_hop_dominance(2)

    # Final check
    propagator.final_check(None)

    # Add constraints and check
    solver.add(Bool('reachable_A'))
    solver.add(Bool('reachable_B'))
    print(solver.check())

     # Demonstrate dynamic reachability updates
    propagator._update_reachability()
    print("Reachability table:", propagator.reachability_table)

if __name__ == "__main__":
    main()
