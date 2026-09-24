import type { Region } from './region.ts';

export function printRegion(region: Region, indent = ''): string {
	switch (region.kind) {
		case 'basic':
			return `${indent}basic blocks=${formatBlocks(region.sourceBlocks)}`;
		case 'sequence':
			return [
				`${indent}sequence${
					region.exitLabel ? ` label=${region.exitLabel}` : ''
				} blocks=${formatBlocks(region.sourceBlocks)}`,
				...region.regions.map((child) =>
					printRegion(child, `${indent}  `)
				),
			].join('\n');
		case 'if':
			return [
				`${indent}if ${
					region.join == null
						? 'join=none'
						: `join=0x${region.join.toString(16)}`
				} header=0x${region.header.toString(16)}${
					region.predicateBlocks
						? ` predicates=${formatBlocks(region.predicateBlocks)}`
						: ''
				}${
					region.conditionalValue
						? ` value=${region.conditionalValue.forms.join('|')}`
						: ''
				} blocks=${formatBlocks(region.sourceBlocks)}`,
				printRegion(region.consequent, `${indent}  then `),
				printRegion(region.alternate, `${indent}  else `),
			].join('\n');
		case 'switch':
			return [
				`${indent}switch cases=${region.cases.length} header=0x${
					region.header.toString(16)
				} default=0x${region.defaultTarget.toString(16)}${
					region.join == null
						? ''
						: ` join=0x${region.join.toString(16)}`
				} blocks=${formatBlocks(region.sourceBlocks)}`,
				...region.cases.map((switchCase) =>
					printRegion(
						switchCase.body,
						`${indent}  case 0x${switchCase.target.toString(16)} `,
					)
				),
				printRegion(
					region.defaultBody,
					`${indent}  default 0x${
						region.defaultTarget.toString(16)
					} `,
				),
			].join('\n');
		case 'tryCatch':
			return [
				`${indent}tryCatch handler=0x${
					region.handlerAddress.toString(16)
				}${
					region.retryLoop
						? ` retry=0x${
							region.retryLoop.header.toString(16)
						}->0x${region.retryLoop.normalExit.toString(16)}`
						: ''
				} protected=${formatBlocks(region.protectedBlocks)} blocks=${
					formatBlocks(region.sourceBlocks)
				}${
					region.subsumedHandlerBlocks
						? ` subsumed=${
							formatBlocks(region.subsumedHandlerBlocks)
						}`
						: ''
				}`,
				printRegion(region.body, `${indent}  try `),
				printRegion(region.handler, `${indent}  catch `),
			].join('\n');
		case 'tryFinally':
			return [
				`${indent}tryFinally handler=0x${
					region.handlerAddress.toString(16)
				} protected=${formatBlocks(region.protectedBlocks)} blocks=${
					formatBlocks(region.sourceBlocks)
				}${
					region.normalExit == null
						? ''
						: ` normalExit=0x${region.normalExit.toString(16)}`
				}${
					region.finallyCopyKinds?.length
						? ` copies=${region.finallyCopyKinds.join(',')}`
						: ''
				}`,
				...formatDeferredExits(region, `${indent}  `),
				printRegion(region.body, `${indent}  try `),
				printRegion(region.finalizer, `${indent}  finally `),
			].join('\n');
		case 'loop':
			return [
				`${indent}loop id=${region.id}${
					region.label ? ` label=${region.label}` : ''
				}${
					region.syntax
						? ` syntax=${region.syntax.kind} value=${region.syntax.value.name}`
						: ''
				} header=0x${region.header.toString(16)}${
					region.headerLatchBranch
						? ` headerLatch=0x${
							region.headerLatchBranch.latch.toString(16)
						} bodyEntry=0x${
							region.headerLatchBranch.bodyEntry.toString(16)
						}`
						: ''
				}${
					region.continuation == null
						? ''
						: ` continuation=0x${region.continuation.toString(16)}`
				} latches=${
					region.latches.map((addr) => `0x${addr.toString(16)}`).join(
						',',
					)
				} children=${region.children.join(',')} exits=${
					region.exits.map((edge) =>
						`${edge.kind}${edge.label ? `:${edge.label}` : ''}:0x${
							edge.from.toString(16)
						}->0x${edge.to.toString(16)}${
							edge.trailer ? '[trailer]' : ''
						}${
							edge.sequenceExit
								? `[seq:${edge.sequenceExit.label ?? '?'}->0x${
									edge.sequenceExit.target.toString(16)
								}]`
								: ''
						}`
					).join(',')
				} blocks=${formatBlocks(region.sourceBlocks)}`,
				printRegion(region.body, `${indent}  body `),
				...region.exits.flatMap((exit, index) =>
					exit.trailer
						? [printRegion(
							exit.trailer,
							`${indent}  exit[${index}] `,
						)]
						: []
				),
			].join('\n');
		case 'delegateYield':
			return `${indent}delegateYield completion=${region.completion} blocks=${
				formatBlocks(region.sourceBlocks)
			}`;
		case 'break':
			return `${indent}break target=0x${region.target.toString(16)}`;
		case 'continue':
			return `${indent}continue target=0x${region.target.toString(16)}`;
		case 'labelBreak':
			return `${indent}labelBreak label=${region.label} target=0x${
				region.target.toString(16)
			}`;
		case 'labelContinue':
			return `${indent}labelContinue label=${region.label} target=0x${
				region.target.toString(16)
			}`;
		case 'deferredExit':
			return `${indent}deferredExit ${region.exit.kind} target=0x${
				('target' in region.exit
					? region.exit.target
					: region.exit.kind === 'exception'
					? region.exit.handler
					: 0).toString(16)
			} actions=${region.exit.actions.length}`;
		case 'return':
			return `${indent}return`;
		case 'throw':
			return `${indent}throw`;
		case 'terminalReference':
			return `${indent}terminalReference entry=0x${
				region.entry.toString(16)
			}`;
		case 'fallback':
			return `${indent}fallback entry=0x${
				region.entry.toString(16)
			} blocks=${
				formatBlocks(region.sourceBlocks)
			} reason=${region.reason}`;
	}
}

function formatDeferredExits(region: Region, indent: string): string[] {
	return (region.deferredExits ?? []).flatMap((exit) =>
		exit.actions.flatMap((action) => {
			if (action.kind !== 'finally') return [];
			return [
				`${indent}deferred finally ${action.action.kind} canonical=0x${
					action.action.canonical.toString(16)
				} copy=0x${action.action.copyRoot.toString(16)} owner=${
					action.action.ownerBlock == null
						? '<none>'
						: `0x${action.action.ownerBlock.toString(16)}`
				} statements=${action.action.statements?.length ?? 0}`,
			];
		})
	);
}

function formatBlocks(blocks: Iterable<number>): string {
	return [...blocks].toSorted((left, right) => left - right).map((addr) =>
		`0x${addr.toString(16)}`
	).join(',');
}
