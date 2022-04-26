/// Simple graph and implementation of Tarjan's `Strongly Connected Components`
/// algorithm. This module is used during semantic analysis (namely,
/// typechecking) to identify mutually recursive functions.
///

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NodeId(usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EdgeId(usize);

impl From<NodeId> for usize {
    fn from(NodeId(idx): NodeId) -> Self {
        idx
    }
}

impl From<EdgeId> for usize {
    fn from(EdgeId(idx): EdgeId) -> Self {
        idx
    }
}

impl PartialEq<usize> for NodeId {
    fn eq(&self, other: &usize) -> bool {
        &self.0 == other
    }
}

impl<T> std::ops::Index<NodeId> for Vec<Node<T>> {
    type Output = Node<T>;

    fn index(&self, index: NodeId) -> &Self::Output {
        &self[index.0]
    }
}

impl<T> std::ops::IndexMut<NodeId> for Vec<Node<T>> {
    fn index_mut(&mut self, index: NodeId) -> &mut Self::Output {
        &mut self[index.0]
    }
}

impl<T> std::ops::Index<NodeId> for [Node<T>] {
    type Output = Node<T>;

    fn index(&self, index: NodeId) -> &Self::Output {
        &self[index.0]
    }
}

impl<T> std::ops::IndexMut<NodeId> for [Node<T>] {
    fn index_mut(&mut self, index: NodeId) -> &mut Self::Output {
        &mut self[index.0]
    }
}

impl std::ops::Index<EdgeId> for Vec<Edge> {
    type Output = Edge;

    fn index(&self, index: EdgeId) -> &Self::Output {
        &self[index.0]
    }
}

impl std::ops::IndexMut<EdgeId> for Vec<Edge> {
    fn index_mut(&mut self, index: EdgeId) -> &mut Self::Output {
        &mut self[index.0]
    }
}

impl std::ops::Index<EdgeId> for [Edge] {
    type Output = Edge;

    fn index(&self, index: EdgeId) -> &Self::Output {
        &self[index.0]
    }
}

impl std::ops::IndexMut<EdgeId> for [Edge] {
    fn index_mut(&mut self, index: EdgeId) -> &mut Self::Output {
        &mut self[index.0]
    }
}

#[derive(Debug)]
pub struct Node<T> {
    pub value: T,
    edges: Vec<EdgeId>,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Edge {
    left: NodeId,
    right: NodeId,
}

#[derive(Debug)]
pub struct Graph<T> {
    edges: Vec<Edge>,
    nodes: Vec<Node<T>>,
}

impl<T> Graph<T> {
    pub fn new() -> Self {
        Graph {
            edges: vec![],
            nodes: vec![],
        }
    }

    /// Given a value, creates a new Node and appends it to the graph's stack
    /// of nodes and returns the new node's index.
    ///
    /// Node: this does NOT check whether a node with the existing value
    /// already exists.
    pub fn add_node(&mut self, value: T) -> NodeId {
        self.nodes.push(Node {
            value,
            edges: vec![],
        });
        NodeId(&self.nodes.len() - 1)
    }

    /// Connect two existing nodes by creating an `Edge<T>` containing the
    /// provided `NodeId<T>`s and adding it to the graph's stack of edges,
    /// and returns the `EdgeId<T>` corresponding to the newly inserted edge.
    ///
    /// Node: this does NOT check whether an edge containing the same
    /// `NodeId<T>` already exists.
    pub fn connect(&mut self, nx: NodeId, ny: NodeId) -> EdgeId {
        let edge_id = EdgeId(self.edges.len());
        self.nodes[nx].edges.push(edge_id);
        self.edges.push(Edge {
            left: nx,
            right: ny,
        });
        edge_id
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
}

impl<'a, T: 'a> std::ops::Index<NodeId> for Graph<T> {
    type Output = Node<T>;

    fn index(&self, index: NodeId) -> &Self::Output {
        &self.nodes[index]
    }
}

impl<T> std::ops::Index<EdgeId> for Graph<T> {
    type Output = Edge;

    fn index(&self, index: EdgeId) -> &Self::Output {
        &self.edges[index]
    }
}

/// A *strongly connected component* (SCC) of a directed graph G is the maximal
/// strongly connected subgraph H < G.
///
/// Consider the following graph *G*:
/// ```txt
///  G := (a) 🡢 (b) 🡢 (d) 🡢 (e)
///         🡤  🡧      
///          (c)       
/// ```
///
#[derive(Clone, Debug, PartialEq)]
pub struct Scc(Vec<NodeId>);
impl Scc {
    // fn new(node_ids: impl IntoIterator<Item = NodeId>) -> Self {
    //     Self(node_ids.into_iter().collect())
    // }

    fn take_from_until(stack: &mut Vec<NodeId>, until_id: NodeId) -> Self {
        let mut conns = vec![];
        while let Some(index) = stack.pop() {
            conns.push(index);
            if until_id == index {
                break;
            }
        }
        Self(conns)
    }

    pub fn node_ids(self) -> Vec<NodeId> {
        self.0
    }
}

impl std::ops::Deref for Scc {
    type Target = Vec<NodeId>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for Scc {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl std::ops::Index<usize> for Scc {
    type Output = NodeId;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl std::ops::IndexMut<usize> for Scc {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}
impl From<Scc> for Vec<NodeId> {
    fn from(Scc(ids): Scc) -> Self {
        ids
    }
}

impl From<Scc> for Vec<usize> {
    fn from(Scc(ids): Scc) -> Self {
        ids.into_iter().map(|NodeId(n)| n).collect()
    }
}

/// Structure to hold state and graph nodes throughout component connection
/// analysis using Tarjan's algorithm for *strongly connected components*.
///
/// Tarjan's algorithm performs a depth-first search (DFS) of a graph *G*,
/// producing a DFS tree *G'* whose subtrees are coined *strongly connected
/// components* (SCC). A node `N` is a `head` if
///
/// If a (nontrivial) subtree *H* of *G'* can be found,
/// then the subtree *H* and all of its nodes form a *single* SCC.
///
///
/// Strongly connected components are stored in the `conns` field.
///
struct Tarjan<'a, T: 'a> {
    index: usize,
    graph: &'a Graph<T>,
    /// Steps throughout the traversal at which a node is visited for the first
    /// time.
    found: Vec<usize>,
    /// For a given index `i`, `Tarjan.early[i]` indicates the earliest visited
    /// node that can be reached from the subgraph with root node `NodeId(i)`.
    ///
    /// Top-most reachable ancestor with minimum possible `found` value.
    early: Vec<usize>,
    stack: Vec<NodeId>,
    conns: Vec<Scc>,
}

impl<'a, T> Tarjan<'a, T> {
    pub fn from_graph(graph: &'a Graph<T>) -> Self {
        let zero = std::iter::repeat(0)
            .take(graph.node_count())
            .collect::<Vec<_>>();
        Self {
            graph,
            index: 1,
            stack: vec![],
            conns: vec![],
            found: zero.clone(),
            early: zero,
        }
    }

    fn nodes(&'a self) -> impl Iterator<Item = &'a NodeId> + 'a {
        self.stack.iter()
    }

    fn stack_has_node(&self, node_id: &NodeId) -> bool {
        self.nodes().any(|x| x == node_id)
    }

    fn strong_connect(&mut self, node_idx: NodeId) {
        let NodeId(idx) = node_idx;
        self.found[idx] = self.index;
        self.early[idx] = self.index;
        self.index += 1;
        self.stack.push(node_idx);

        for edge_id in &self.graph[node_idx].edges {
            let Edge {
                right: right @ NodeId(rid),
                ..
            } = self.graph[*edge_id];

            if self.found[rid] == 0 {
                self.strong_connect(right);
                self.early[idx] = self.early[idx].min(self.early[rid]);
            } else if self.stack_has_node(&right) {
                self.early[idx] = self.early[idx].min(self.found[rid]);
            }
        }

        if self.early[idx] == self.found[idx] {
            self.conns
                .push(Scc::take_from_until(&mut self.stack, node_idx));
        }
    }

    fn components(mut self) -> Vec<Scc> {
        for node in 0..self.graph.node_count() {
            if self.found[node] == 0 {
                self.strong_connect(NodeId(node))
            }
        }
        self.conns
    }
}

pub fn strong_conn_comps<T>(graph: &Graph<T>) -> Vec<Scc> {
    Tarjan::from_graph(graph).components()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn has_1_strongly_connected_component() {
        let mut graph = Graph::new();
        let node_1 = graph.add_node(());
        let node_2 = graph.add_node(());
        let node_3 = graph.add_node(());
        graph.connect(node_1, node_2);
        graph.connect(node_2, node_1);
        graph.connect(node_2, node_3);
        let connections = strong_conn_comps(&graph);

        println!("{:?}", &connections);

        assert_eq!(connections.len(), 2);
        assert_eq!(*connections[0], vec![node_3]);
        assert_eq!(*connections[1], vec![node_2, node_1]);
    }

    #[test]
    fn has_2_strongly_connected_components() {
        let mut graph = Graph::new();
        let node_1 = graph.add_node(());
        let node_2 = graph.add_node(());
        let node_3 = graph.add_node(());
        let node_4 = graph.add_node(());
        graph.connect(node_1, node_2);
        graph.connect(node_2, node_1);
        graph.connect(node_2, node_3);
        graph.connect(node_3, node_4);
        graph.connect(node_4, node_2);
        let connections = strong_conn_comps(&graph);

        assert_eq!(connections.len(), 1);
        assert_eq!(*connections[0], vec![node_4, node_3, node_2, node_1]);
    }
}
