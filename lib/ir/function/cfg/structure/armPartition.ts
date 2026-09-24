import type { BlockAddr } from '../../../../hbc/disassembly/function.ts';
import { AddressMap } from '../../../../utils/map.ts';
import { AddressSet } from '../../../../utils/set.ts';

export function successorsWithin(
	nodes: AddressSet<BlockAddr>,
	successors: ReadonlyMap<BlockAddr, AddressSet<BlockAddr>>,
): AddressMap<AddressSet<BlockAddr>> {
	const bounded = new AddressMap<AddressSet<BlockAddr>>();
	for (const node of nodes) {
		bounded.set(
			node,
			new AddressSet(
				[...successors.get(node) ?? []].filter((target) =>
					nodes.has(target)
				),
			),
		);
	}
	return bounded;
}
/** Nodes reachable from `entry` without leaving this contracted DAG subset. */
export function reachableNodes(
	entry: BlockAddr,
	nodes: AddressSet<BlockAddr>,
	successors: ReadonlyMap<BlockAddr, AddressSet<BlockAddr>>,
): AddressSet<BlockAddr> {
	const reachable = new AddressSet<BlockAddr>();
	const pending = [entry];
	while (pending.length > 0) {
		const node = pending.pop()!;
		if (reachable.has(node) || !nodes.has(node)) continue;
		reachable.add(node);
		for (const successor of successors.get(node) ?? []) {
			pending.push(successor);
		}
	}
	return reachable;
}
/** Arm ownership before its shared lexical continuation. */
export function reachableBefore(
	entry: BlockAddr,
	join: BlockAddr,
	nodes: AddressSet<BlockAddr>,
	successors: ReadonlyMap<BlockAddr, AddressSet<BlockAddr>>,
): AddressSet<BlockAddr> {
	const reachable = new AddressSet<BlockAddr>();
	const pending = [entry];
	while (pending.length > 0) {
		const node = pending.pop()!;
		if (node === join || reachable.has(node) || !nodes.has(node)) continue;
		reachable.add(node);
		for (const successor of successors.get(node) ?? []) {
			pending.push(successor);
		}
	}
	return reachable;
}
/** Sentinel owner for a node more than one arm reaches. */
const SHARED_ARM = -1;
export interface ExclusiveArmPartition {
	/** Nodes only one arm entry reaches, keyed by that entry. */
	armNodes: AddressMap<AddressSet<BlockAddr>>;
	/** Single entry of the shared continuation, absent when the arms diverge. */
	trailerRoot: BlockAddr | null;
	trailerNodes: AddressSet<BlockAddr>;
}
/**
 * Split a dispatch by which arm can reach each node instead of by a proven
 * common postdominator.
 *
 * A node every path reaches through one arm entry belongs to that arm; a node
 * more than one arm reaches is shared continuation. That owns the shapes a
 * postdominator proof has to decline. A dispatch whose arms return, throw or
 * leave the scope has no common postdominator at all, and one whose shared node
 * is reached on some paths but bypassed on others has one that postdominates no
 * arm — yet in both the arms themselves are disjoint and ordinary.
 *
 * The shared set is only usable when it has a single entry, because that is
 * what lets the caller append it once as a Sequence trailer. Several entries
 * mean several arrivals, which is a genuine join the skeleton still labels.
 */
export function exclusiveArmPartition(
	subEntry: BlockAddr,
	armEntries: readonly BlockAddr[],
	branchNodes: AddressSet<BlockAddr>,
	branchSuccessors: ReadonlyMap<BlockAddr, AddressSet<BlockAddr>>,
): ExclusiveArmPartition | null {
	if (!branchNodes.has(subEntry)) return null;
	const successors = successorsWithin(branchNodes, branchSuccessors);
	const order = topologicalOrder(subEntry, branchNodes, successors);
	if (!order) return null;
	const entries = new AddressSet(armEntries);
	// Contraction can leave the entry with a successor that is no arm of this
	// dispatch, and the walk below would silently lose its ownership.
	for (const successor of successors.get(subEntry) ?? []) {
		if (!entries.has(successor)) return null;
	}

	const owner = new AddressMap<BlockAddr>();
	const reach = (node: BlockAddr, from: BlockAddr) => {
		const existing = owner.get(node);
		owner.set(
			node,
			existing == null || existing === from ? from : SHARED_ARM,
		);
	};
	for (const entry of entries) {
		if (branchNodes.has(entry)) reach(entry, entry);
	}
	for (const node of order) {
		if (node === subEntry) continue;
		const reaching = owner.get(node);
		// Reachable from no arm entry, so this dispatch does not own it.
		if (reaching == null) return null;
		for (const successor of successors.get(node) ?? []) {
			if (successor === subEntry) return null;
			reach(successor, reaching);
		}
	}

	const armNodes = new AddressMap<AddressSet<BlockAddr>>();
	for (const entry of entries) armNodes.set(entry, new AddressSet());
	const trailerNodes = new AddressSet<BlockAddr>();
	for (const node of branchNodes) {
		if (node === subEntry) continue;
		const reaching = owner.get(node)!;
		if (reaching === SHARED_ARM) trailerNodes.add(node);
		else armNodes.get(reaching)?.add(node);
	}
	if (trailerNodes.size === 0) {
		return { armNodes, trailerRoot: null, trailerNodes };
	}

	const trailerPredecessors = new AddressMap<number>();
	for (const node of trailerNodes) trailerPredecessors.set(node, 0);
	for (const from of trailerNodes) {
		for (const to of successors.get(from) ?? []) {
			if (!trailerNodes.has(to)) continue;
			trailerPredecessors.set(to, (trailerPredecessors.get(to) ?? 0) + 1);
		}
	}
	let trailerRoot: BlockAddr | null = null;
	for (const node of trailerNodes) {
		if (trailerPredecessors.get(node) !== 0) continue;
		if (trailerRoot != null) return null;
		trailerRoot = node;
	}
	if (trailerRoot == null) return null;
	if (
		!reachableNodes(trailerRoot, trailerNodes, successors)
			.equals(trailerNodes)
	) return null;
	return { armNodes, trailerRoot, trailerNodes };
}
export function topologicalOrder(
	entry: BlockAddr,
	nodes: AddressSet<BlockAddr>,
	successors: AddressMap<AddressSet<BlockAddr>>,
): BlockAddr[] | null {
	const indegree = new AddressMap<number>();
	for (const node of nodes) indegree.set(node, 0);
	for (const targets of successors.values()) {
		for (const target of targets) {
			indegree.set(target, (indegree.get(target) ?? 0) + 1);
		}
	}
	const ready = [...nodes].filter((node) => indegree.get(node) === 0)
		.toSorted((left, right) => left - right);
	if (!ready.includes(entry)) return null;
	ready.splice(ready.indexOf(entry), 1);
	ready.unshift(entry);
	const order: BlockAddr[] = [];
	while (ready.length > 0) {
		const node = ready.shift()!;
		order.push(node);
		for (const target of successors.get(node) ?? []) {
			const next = (indegree.get(target) ?? 0) - 1;
			indegree.set(target, next);
			if (next === 0) {
				ready.push(target);
				ready.sort((left, right) => left - right);
			}
		}
	}
	return order.length === nodes.size ? order : null;
}
