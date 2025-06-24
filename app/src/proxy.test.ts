import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import child_process from 'node:child_process';
import EventEmitter from 'events';
import { Readable, Writable } from 'stream';

import { proxyInner, ProxyRequest } from './proxy';

vi.mock('child_process');

const mockChildProcess = (): child_process.ChildProcess => {
    const proc = new EventEmitter() as child_process.ChildProcess;

    proc.stdout = new EventEmitter() as Readable;
    proc.stderr = new EventEmitter() as Readable;
    proc.stdin = new Writable();
    proc.stdin._write = () => {};

    return proc;
};

describe('Test executing proxy', () => { 
    let process: child_process.ChildProcess;

    beforeEach(() => {
        process = mockChildProcess();
        vi.spyOn(child_process, 'spawn').mockReturnValueOnce(process);
    });

    afterEach(() => {
        vi.restoreAllMocks();
    })

    it('proxy should return stdout and stderr on successful exit', async () => {
        const proxyExec = proxyInner({} as ProxyRequest, 'mock-proxy-command', '');

        const proc_stdout = 'stdout';
        const proc_stderr = 'stderr';
        process.stdout?.emit('data', proc_stdout);
        process.stderr?.emit('data', proc_stderr);

        process.emit('close', 0);

        const { stderr, stdout, code } = await proxyExec;

        expect(code).toEqual(0);
        expect(stdout).toEqual(proc_stdout);
        expect(stderr).toEqual(proc_stderr);
    });

    it('proxy should fail on error code', async () => {
        const proxyExec = proxyInner({} as ProxyRequest, 'mock-proxy-command', '');

        process.stderr?.emit('data', 'error');
        process.emit('close', 1);

        await expect(proxyExec).rejects.toThrowError('Process exited with code 1: error');
    })

    it('proxy should handle subprocess error', async () => {
        const proxyExec = proxyInner({} as ProxyRequest, 'mock-proxy-command', '');

        process.emit('error', 'error');

        await expect(proxyExec).rejects.toThrowError('error');
    })
});
