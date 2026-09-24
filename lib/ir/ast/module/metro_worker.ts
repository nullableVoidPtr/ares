import path from 'node:path';
import {
	buildMetroModuleCode,
	MetroModuleWorkerMessage,
	MetroModuleWorkerRequest,
} from './metro.ts';

type WorkerScope = {
	onmessage:
		| ((event: MessageEvent<MetroModuleWorkerRequest>) => void)
		| null;
	postMessage(message: MetroModuleWorkerMessage): void;
};

const workerSelf = globalThis as unknown as WorkerScope;

workerSelf.onmessage = (event: MessageEvent<MetroModuleWorkerRequest>) => {
	const { tasks, options } = event.data;
	for (const task of tasks) {
		try {
			Deno.mkdirSync(
				path.dirname(task.path),
				{ recursive: true },
			);
			Deno.writeTextFileSync(
				task.path,
				buildMetroModuleCode(task.stmt, options),
			);
			workerSelf.postMessage({
				type: 'progress',
				moduleId: task.moduleId,
			});
		} catch (error) {
			workerSelf.postMessage({
				type: 'error',
				moduleId: task.moduleId,
				message: error instanceof Error ? error.message : String(error),
				stack: error instanceof Error ? error.stack : undefined,
			});
			return;
		}
	}
	workerSelf.postMessage({ type: 'result' });
};
