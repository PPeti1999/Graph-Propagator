import pytest


@pytest.mark.parametrize("edges, expected", [
    ([(1, 2), (2, 3)], True),  # Connected graph
    ([(1, 2), (3, 4)], False)  # Disconnected graph
])
def test_connectivity(self, propagator):
    print("Checking connectivity...")
    if propagator.is_connected():
        print("The graph is connected.")
    else:
        print("The graph is not connected.")


@pytest.mark.parametrize("edges, expected", [
    ([('A', 'B'), ('B', 'C')], True),
    ([('A', 'B'), ('B', 'C'), ('C', 'A')], False)
])
def test_acyclicity(self, propagator):
    print("Checking acyclicity...")
    if propagator.is_acyclic():
        print("The graph is acyclic.")
    else:
        print("The graph has a cycle.")


@pytest.mark.parametrize("edges, expected", [
    ([('A', 'B'), ('B', 'A')], False),
    ([('A', 'B'), ('B', 'C'), ('B', 'B')], False),
    ([('A', 'B'), ('B', 'C')], True)
])
def test_simple_graph(self, propagator):
    print("Checking simple graph...")
    if propagator.is_simple_graph():
        print("The graph is simple.")
    else:
        print("The graph is not simple.")


@pytest.mark.parametrize("edges, expected", [
    ([('A', 'B'), ('B', 'C'), ('C', 'D'), ('D', 'A'), ('B', 'D'), ('C', 'A')], True),
])
def test_complete(self, propagator):
    print("Checking complete graph...")
    if propagator.is_complete():
        print("The graph is complete.")
    else:
        print("The graph is not complete.")
