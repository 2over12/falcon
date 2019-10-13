//! A fixed-point engine for data-flow analysis.

use crate::executor;
use error::*;
use il;
use std::collections::{HashMap, VecDeque};
use std::fmt::Debug;

/// A trait which implements a forward, flow-sensitive analysis to a
/// fixed point.
pub trait FixedPointAnalysis<'f, State: 'f + Clone + Debug + PartialOrd> {
    /// Given an input state for a block, create an output state for this
    /// block.
    fn trans(&self, location: il::RefProgramLocation<'f>, state: Option<State>) -> Result<State>;

    /// Given two states, join them into one state.
    fn join(&self, state0: State, state1: &State) -> Result<State>;
}

/// A forward, work-list data-flow analysis algorithm.
///
/// When force is true, the partial order over inputs is forced by joining
/// states which do not inherently enforce the partial order.
pub fn fixed_point_forward_options<'f, Analysis, State>(
    analysis: Analysis,
    function: &'f il::Function,
    force: bool,
) -> Result<HashMap<il::ProgramLocation, State>>
where
    Analysis: FixedPointAnalysis<'f, State>,
    State: 'f + Clone + Debug + PartialOrd,
{
    let mut states: HashMap<il::ProgramLocation, State> = HashMap::new();

    let mut queue: VecDeque<il::ProgramLocation> = VecDeque::new();

    // Find the entry block to the function.
    let entry_index = function
        .control_flow_graph()
        .entry()
        .ok_or("Function's control flow graph must have entry")?;
    let entry_block = function.control_flow_graph().block(entry_index)?;

    match entry_block.instructions().first() {
        Some(ref instruction) => {
            let location = il::RefFunctionLocation::Instruction(entry_block, instruction);
            let location = il::RefProgramLocation::new(function, location);
            queue.push_back(location.into());
        }
        None => {
            let location = il::RefFunctionLocation::EmptyBlock(entry_block);
            let location = il::RefProgramLocation::new(function, location);
            queue.push_back(location.into());
        }
    }

    while !queue.is_empty() {
        let location = queue.pop_front().unwrap();

        // TODO this should not be an unwrap
        let location = location.function_location().apply(function).unwrap();

        let location = il::RefProgramLocation::new(function, location);
        let location_predecessors = location.backward()?;
        let state =
            location_predecessors
                .into_iter()
                .fold(None, |s, p| match states.get(&p.into()) {
                    Some(in_state) => match s {
                        Some(s) => Some(analysis.join(s, in_state).unwrap()),
                        None => Some(in_state.clone()),
                    },
                    None => s,
                });

        let mut state = analysis.trans(location.clone(), state)?;

        if let Some(in_state) = states.get(&location.clone().into()) {
            let ordering = match state.partial_cmp(in_state) {
                Some(ordering) => match ordering {
                    ::std::cmp::Ordering::Less => Some("less"),
                    ::std::cmp::Ordering::Equal => {
                        continue;
                    }
                    ::std::cmp::Ordering::Greater => None,
                },
                None => Some("no relation"),
            };
            if force {
                state = analysis.join(state, in_state)?;
            } else {
                if let Some(ordering) = ordering {
                    bail!(
                        "Found a state which was not >= previous state (it was {}) @ {}",
                        ordering,
                        location
                    );
                }
            }
        }

        states.insert(location.clone().into(), state);

        for successor in location.forward()? {
            if !queue.contains(&successor.clone().into()) {
                queue.push_back(successor.into());
            }
        }
    }

    Ok(states)
}

use il::ICFG;

fn get_call_function_index(loc: &il::RefProgramLocation, prog: &il::Program) -> Option<usize> {
    let ins = loc.instruction()?;
    match ins.operation() {
        il::Operation::Branch { target } => executor::eval(target)
            .ok()
            .and_then(|item| item.value_u64())
            .and_then(|item| prog.function_by_address(item))
            .and_then(|func| func.index()),
        _ => None,
    }
}

fn is_call(loc: &il::RefProgramLocation, prog: &il::Program) -> bool {
    get_call_function_index(loc, prog).is_some()
}

fn get_post_call_target(loc: &il::RefProgramLocation, prog: &il::Program) -> Option<usize> {
    let previous = loc.backward().ok()?;

    if previous.len() != 1 {
        return None;
    }

    let prev_loc = &previous[0];
    get_call_function_index(prev_loc, prog)
}

fn is_post_call(loc: &il::RefProgramLocation, prog: &il::Program) -> bool {
    get_post_call_target(loc, prog).is_some()
}

fn get_entry_loc(func: &il::Function) -> Result<il::ProgramLocation> {
    let entry_index = func
        .control_flow_graph()
        .entry()
        .ok_or("Function's control flow graph must have entry")?;
    let entry_block = func.control_flow_graph().block(entry_index)?;

    match entry_block.instructions().first() {
        Some(ref instruction) => {
            let location = il::RefFunctionLocation::Instruction(entry_block, instruction);
            let location = il::RefProgramLocation::new(func, location);
            Ok(location.into())
        }
        None => {
            let location = il::RefFunctionLocation::EmptyBlock(entry_block);
            let location = il::RefProgramLocation::new(func, location);
            Ok(location.into())
        }
    }
}

fn is_ret(loc: &il::ProgramLocation, icfg: &ICFG) -> bool {
    let index = loc.function_index();

    if index.is_none() {
        return false;
    }

    let edges = icfg.get_outgoing(index.unwrap());
    edges
        .iter()
        .any(|item| item.get_edge_type() == il::ICFGEdgeType::Ret && item.get_from() == loc)
}

fn is_function_entry(loc: &il::ProgramLocation, prog: &il::Program) -> bool {
    let applied = loc.apply(prog);

    if applied.is_err() {
        return false;
    }

    let applied = applied.unwrap();
    let entry_loc = get_entry_loc(applied.function());
    entry_loc.is_ok() && &entry_loc.unwrap() == loc
}

/// A forward, work-list data-flow analysis algorithm.
///
/// When force is true, the partial order over inputs is forced by joining
/// states which do not inherently enforce the partial order.
fn fixed_point_forward_options_context_insensitive<'f, Analysis, State>(
    analysis: Analysis,
    function: &'f il::Function,
    prog: &'f il::Program,
    icfg: &ICFG,
    force: bool,
) -> Result<HashMap<il::ProgramLocation, State>>
where
    Analysis: FixedPointAnalysis<'f, State>,
    State: 'f + Clone + Debug + PartialOrd,
{
    let mut states: HashMap<il::ProgramLocation, State> = HashMap::new();

    let mut queue: VecDeque<il::ProgramLocation> = VecDeque::new();

    // Find the entry block to the function.
    queue.push_back(get_entry_loc(function)?);

    while !queue.is_empty() {
        let loc_orig = queue.pop_front().unwrap();
        // TODO this should not be an unwrap
        let location = loc_orig.apply(prog).unwrap();

        let location_predecessors = if is_post_call(&location, prog) {
            let target_index = get_post_call_target(&location, prog).unwrap();
            icfg.get_function_returns(target_index)
                .into_iter()
                .map(|item| item.apply(prog))
                .filter_map(|item| {
                    if item.is_ok() {
                        Some(item.unwrap())
                    } else {
                        None
                    }
                })
                .collect()
        } else if is_function_entry(&loc_orig, prog) {
            let curr_fun = location.function().index();
            if let Some(ind) = curr_fun {
                let pred = icfg.get_function_callers(ind);
                pred.into_iter()
                    .map(|loc| loc.apply(prog))
                    .filter_map(|item| item.ok())
                    .collect()
            } else {
                Vec::new()
            }
        } else {
            location.backward()?
        };

        let state =
            location_predecessors
                .into_iter()
                .fold(None, |s, p| match states.get(&p.into()) {
                    Some(in_state) => match s {
                        Some(s) => Some(analysis.join(s, in_state).unwrap()),
                        None => Some(in_state.clone()),
                    },
                    None => s,
                });

        let mut state = analysis.trans(location.clone(), state)?;

        if let Some(in_state) = states.get(&location.clone().into()) {
            let ordering = match state.partial_cmp(in_state) {
                Some(ordering) => match ordering {
                    ::std::cmp::Ordering::Less => Some("less"),
                    ::std::cmp::Ordering::Equal => {
                        continue;
                    }
                    ::std::cmp::Ordering::Greater => None,
                },
                None => Some("no relation"),
            };
            if force {
                state = analysis.join(state, in_state)?;
            } else {
                if let Some(ordering) = ordering {
                    bail!(
                        "Found a state which was not >= previous state (it was {}) @ {}",
                        ordering,
                        location
                    );
                }
            }
        }

        states.insert(location.clone().into(), state);

        let successors = if is_call(&location, prog) {
            let func_ind = get_call_function_index(&location, prog).unwrap();
            let entry_loc = get_entry_loc(prog.function(func_ind).unwrap());
            let final_loc = entry_loc?;
            vec![final_loc]
        } else if is_ret(&loc_orig, icfg) {
            icfg.get_post_calls(location.function().index().unwrap(), prog)
        } else {
            let fwds = location.forward()?;
            fwds.into_iter().map(|item| item.into()).collect()
        };

        for successor in successors {
            if !queue.contains(&successor) {
                queue.push_back(successor.into());
            }
        }
    }
    Ok(states)
}

pub fn fixed_point_forward_context_insensitive<'f, Analysis, State>(
    analysis: Analysis,
    function_root: &'f il::Function,
    prog: &'f il::Program,
    icfg: &ICFG
) -> Result<HashMap<il::ProgramLocation, State>>
where
    Analysis: FixedPointAnalysis<'f, State>,
    State: 'f + Clone + Debug + PartialOrd,
{
    fixed_point_forward_options_context_insensitive(analysis, function_root, prog, icfg, false)
}

/// A guaranteed sound analysis, which enforces the partial order over states.
pub fn fixed_point_forward<'f, Analysis, State>(
    analysis: Analysis,
    function: &'f il::Function,
) -> Result<HashMap<il::ProgramLocation, State>>
where
    Analysis: FixedPointAnalysis<'f, State>,
    State: 'f + Clone + Debug + PartialOrd,
{
    fixed_point_forward_options(analysis, function, false)
}

/// A backward, work-list data-flow analysis algorithm.
///
/// When force is true, the partial order over inputs is forced by joining
/// states which do not inherently enforce the partial order.
pub fn fixed_point_backward_options<'f, Analysis, State>(
    analysis: Analysis,
    function: &'f il::Function,
    force: bool,
) -> Result<HashMap<il::RefProgramLocation<'f>, State>>
where
    Analysis: FixedPointAnalysis<'f, State>,
    State: 'f + Clone + Debug + PartialOrd,
{
    let mut states: HashMap<il::RefProgramLocation<'f>, State> = HashMap::new();

    let mut queue: VecDeque<il::RefProgramLocation<'f>> = VecDeque::new();

    // Find the entry block to the function.
    let exit_index = function
        .control_flow_graph()
        .entry()
        .ok_or("Function's control flow graph must have entry")?;
    let exit_block = function.control_flow_graph().block(exit_index)?;

    match exit_block.instructions().last() {
        Some(ref instruction) => {
            let location = il::RefFunctionLocation::Instruction(exit_block, instruction);
            let location = il::RefProgramLocation::new(function, location);
            queue.push_back(location.clone());
        }
        None => {
            let location = il::RefFunctionLocation::EmptyBlock(exit_block);
            let location = il::RefProgramLocation::new(function, location);
            queue.push_back(location.clone());
        }
    }

    while !queue.is_empty() {
        let location = queue.pop_front().unwrap();

        let location_successors = location.forward()?;

        let state = location_successors
            .iter()
            .fold(None, |s, p| match states.get(p) {
                Some(in_state) => match s {
                    Some(s) => Some(analysis.join(s, in_state).unwrap()),
                    None => Some(in_state.clone()),
                },
                None => s,
            });

        let mut state = analysis.trans(location.clone(), state)?;

        if let Some(in_state) = states.get(&location) {
            let ordering = match state.partial_cmp(in_state) {
                Some(ordering) => match ordering {
                    ::std::cmp::Ordering::Less => Some("less"),
                    ::std::cmp::Ordering::Equal => {
                        continue;
                    }
                    ::std::cmp::Ordering::Greater => None,
                },
                None => Some("no relation"),
            };
            if force {
                state = analysis.join(state, in_state)?;
            } else {
                if let Some(ordering) = ordering {
                    bail!(
                        "Found a state which was not >= previous state (it was {}) @ {}",
                        ordering,
                        location
                    );
                }
            }
        }

        states.insert(location.clone(), state);

        for successor in location.backward()? {
            if !queue.contains(&successor) {
                queue.push_back(successor);
            }
        }
    }

    Ok(states)
}

/// A guaranteed sound analysis, which enforces the partial order over states.
pub fn fixed_point_backward<'f, Analysis, State>(
    analysis: Analysis,
    function: &'f il::Function,
) -> Result<HashMap<il::RefProgramLocation<'f>, State>>
where
    Analysis: FixedPointAnalysis<'f, State>,
    State: 'f + Clone + Debug + PartialOrd,
{
    fixed_point_backward_options(analysis, function, false)
}
