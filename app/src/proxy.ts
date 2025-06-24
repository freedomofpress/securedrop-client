import child_process from 'node:child_process';

export type ProxyRequest = {
    method: string,
    path_query: string,
    stream: false,
    body: string,
    headers: object,
}

export type ProxyResponse = {
    stdout: string,
    stderr: string,
    code: number,
}

export async function proxy(request: ProxyRequest): Promise<ProxyResponse> {
    return proxyInner(request, process.env.SD_PROXY_CMD, process.env.SD_PROXY_ORIGIN);
}

export async function proxyInner(request: ProxyRequest, proxyCommand: string, proxyOrigin: string): Promise<ProxyResponse> {
    return new Promise((resolve, reject) => {
        const process = child_process.spawn(proxyCommand, [], {
        env: {"SD_PROXY_ORIGIN": proxyOrigin}
        });

        let stdout = '';
        let stderr = '';
        process.stdout.on('data', (data) => {
        stdout += data.toString();
        });

        process.stderr.on('data', (data) => {
        stderr += data.toString();
        });

        process.on('close', (code) => {
        if(code === 0) {
            resolve({stdout, stderr, code} as ProxyResponse);
        } else {
            reject(new Error(`Process exited with code ${code}: ${stderr}`));
        }
        });

        process.on('error', (error) => {
        reject(error);
        });

        process.stdin.write(JSON.stringify(request) + '\n');
        process.stdin.end();
    });
}
