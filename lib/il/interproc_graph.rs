use crate::Result;
use executor;
use graph::Edge;
use graph::Graph;
use graph::Vertex;
use il;
use il::program::Program;
use il::Function;
use il::FunctionLocation;
use il::ProgramLocation;
use std::collections::HashMap;
use std::collections::HashSet;

// Honestly not a big fan of how the graph is designed, clients of the graph shouldnt need to keep track of indices
pub struct ICFG {
    calls_and_rets: Graph<FunctionNode, ICFGEdge>,
}

impl ICFG {
    pub fn add_function_node(&mut self, func: &Function) -> Result<()> {
        let ind = func.index().unwrap();
        self.calls_and_rets.insert_vertex(FunctionNode(ind))
    }

    pub fn add_function_edge(
        &mut self,
        from: &Function,
        to: &Function,
        loc: ProgramLocation,
        edge_type: ICFGEdgeType,
    ) -> Result<()> {
        self.calls_and_rets.insert_edge(ICFGEdge::new(
            loc,
            edge_type,
            from.index().unwrap(),
            to.index().unwrap(),
        ))
    }

    pub fn get_post_calls(&self, func: usize, prog: &Program) -> Vec<ProgramLocation> {
        let callers = self.get_function_callers(func);
        callers
            .into_iter()
            .filter_map(|loc| loc.apply(prog).and_then(|ref_loc| ref_loc.forward()).ok())
            .flatten()
            .map(|ref_loc| ref_loc.into())
            .collect()
    }

    pub fn get_function_callers(&self, func: usize) -> Vec<ProgramLocation> {
        let inc = self.get_incoming(func);
        inc.iter()
            .filter_map(|edge| {
                if edge.edge_type == ICFGEdgeType::Call {
                    Some(edge.loc_from.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn get_function_returns(&self, func: usize) -> Vec<ProgramLocation> {
        let out = self.get_outgoing(func);
        out.iter()
            .filter_map(|edge| {
                if edge.edge_type == ICFGEdgeType::Ret {
                    Some(edge.loc_from.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn get_incoming(&self, func: usize) -> &Vec<ICFGEdge> {
        self.calls_and_rets.edges_in(func).unwrap()
    }

    pub fn get_outgoing(&self, func: usize) -> &Vec<ICFGEdge> {
        self.calls_and_rets.edges_out(func).unwrap()
    }

    pub fn from(program: &Program) -> ICFG {
        let mut calls: Vec<(&Function, &Function, ProgramLocation)> = Vec::new();
        let mut rets: HashMap<&Function, Vec<ProgramLocation>> = HashMap::new();
        let mut added_edges = HashSet::new();

        let mut cfg = ICFG {
            calls_and_rets: Graph::new(),
        };
        for function in program.functions() {
            let call_targets = get_call_targets(function, program);
            let ret_points = get_ret_points(function);

            let mut call_targets: Vec<(&Function, &Function, ProgramLocation)> = call_targets
                .into_iter()
                .map(|item| (function, item.0, item.1))
                .collect();
            calls.append(&mut call_targets);

            rets.insert(function, ret_points);

            cfg.add_function_node(function).unwrap();
        }

        for c in calls {
            cfg.add_function_edge(c.0, c.1, c.2, ICFGEdgeType::Call)
                .unwrap();
            for ret in &rets[c.0] {
                let seen_edge = ICFGEdge::new(ret.clone(), ICFGEdgeType::Ret, c.1.index().unwrap(), c.0.index().unwrap());

                if !added_edges.contains(&seen_edge) {
                cfg.add_function_edge(c.1, c.0, ret.clone(), ICFGEdgeType::Ret)
                    .unwrap();
                added_edges.insert(seen_edge);
                }
            }
        }

        cfg
    }
}
fn get_ret_points(func: &Function) -> Vec<ProgramLocation> {
    let mut outs = Vec::new();
    for block in func.blocks() {
        let no_out_edges = func
            .control_flow_graph()
            .edges_out(block.index())
            .unwrap()
            .is_empty();
        if no_out_edges {
            if let Some(exit) = block.instructions().last() {
                outs.push(ProgramLocation::new(
                    func.index(),
                    FunctionLocation::Instruction(block.index(), exit.index()),
                ))
            }
        }
    }

    outs
}

fn get_call_targets<'f>(
    func: &'f Function,
    program: &'f Program,
) -> Vec<(&'f Function, ProgramLocation)> {
    let call_targets = func
        .blocks()
        .iter()
        .fold(Vec::new(), |mut call_targets, block| {
            block.instructions().iter().for_each(|instruction| {
                let loc = ProgramLocation::new(
                    func.index(),
                    FunctionLocation::Instruction(block.index(), instruction.index()),
                );
                match *instruction.operation() {
                    il::Operation::Branch { ref target } => {
                        executor::eval(target).ok().map(|constant| {
                            call_targets.push((
                                program
                                    .function_by_address(constant.value_u64().unwrap())
                                    .unwrap(),
                                loc,
                            ))
                        });
                    }
                    _ => {}
                }
            });
            call_targets
        });
    call_targets
}

// holds onto a function index
#[derive(Clone)]
struct FunctionNode(usize);

unsafe impl Sync for FunctionNode {}

impl Vertex for FunctionNode {
    // The index of this vertex.
    fn index(&self) -> usize {
        self.0
    }

    // A string to display in dot graphviz format.
    fn dot_label(&self) -> String {
        self.0.to_string()
    }
}

#[derive(Clone, Debug, PartialEq, Copy,Eq,Hash)]
pub enum ICFGEdgeType {
    Call,
    Ret,
}

#[derive(Clone, Debug,PartialEq,Eq,Hash)]
pub struct ICFGEdge {
    loc_from: ProgramLocation,
    edge_type: ICFGEdgeType,
    from: usize,
    to: usize,
}

impl ICFGEdge {
    pub fn get_from(&self) -> &ProgramLocation {
        &self.loc_from
    }

    pub fn get_edge_type(&self) -> ICFGEdgeType {
        self.edge_type
    }
}

unsafe impl Sync for ICFGEdge {}

impl Edge for ICFGEdge {
    /// The index of the head vertex.
    fn head(&self) -> usize {
        self.from
    }
    /// The index of the tail vertex.
    fn tail(&self) -> usize {
        self.to
    }
    /// A string to display in dot graphviz format.
    fn dot_label(&self) -> String {
        "".to_owned()
    }
}

impl ICFGEdge {
    fn new(loc_from: ProgramLocation, edge_type: ICFGEdgeType, from: usize, to: usize) -> ICFGEdge {
        ICFGEdge {
            loc_from,
            edge_type,
            from,
            to,
        }
    }
}
