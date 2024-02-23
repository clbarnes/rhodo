use serde::{de::DeserializeOwned, Deserialize, Serialize};

use crate::{error::EdgeBuild, NodeId, Tree};

#[derive(Debug, Serialize, Deserialize)]
/// DFS post-order sorted columnar table of node IDs, parent IDs (only the first is None), node data; designed for efficient serialization
struct Table<D: Serialize, N: NodeId + Serialize> {
    ids: Vec<N>,
    parents: Vec<Option<N>>,
    data: Vec<D>,
}

impl<D: Serialize, N: NodeId + Serialize> From<Tree<D, N>> for Table<D, N> {
    fn from(mut value: Tree<D, N>) -> Self {
        let ids: Vec<_> = value.dfs(*value.root()).unwrap().collect();
        let (parents, data) = ids.iter().fold(
            (Vec::with_capacity(ids.len()), Vec::with_capacity(ids.len())),
            |(mut parents, mut data), id| {
                let node = value.nodes.remove(id).unwrap();
                parents.push(node.parent);
                data.push(node.data);
                (parents, data)
            },
        );
        Self { ids, parents, data }
    }
}

impl<D: Serialize, N: NodeId + Serialize> TryFrom<Table<D, N>> for Tree<D, N> {
    fn try_from(value: Table<D, N>) -> Result<Self, Self::Error> {
        Self::new_from_edges(
            value
                .ids
                .into_iter()
                .zip(value.parents.into_iter())
                .zip(value.data.into_iter())
                .map(|((id, p), d)| (p, id, d)),
        )
    }

    type Error = EdgeBuild<N>;
}

impl<D: Serialize + Clone, N: NodeId + Serialize> Serialize for Tree<D, N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let t: Table<_, _> = self.clone().into();
        t.serialize(serializer)
    }
}

// impl<'de, D: Deserialize<'de>, N: NodeId + Deserialize<'de>> Deserialize<'de> for Tree<D, N> {
//     fn deserialize<S>(deserializer: S) -> Result<Self, D::Error>
//     where
//         D: serde::Deserializer<'de>,
//     {
//         let table = Table::deserialize(deserializer)?;
//         table.try_into().map_err(|e| )
//     }
// }
