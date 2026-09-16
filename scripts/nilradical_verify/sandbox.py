#!/usr/bin/env python3
"""Fail-closed macOS adapter for Comparator's documented Landrun argument subset.
A real Seatbelt sandbox, never a command-stripping fake sandbox.
"""
import hashlib, json, os, pathlib, subprocess, sys

def policy(writes):
    # No mach-lookup, networking, signals, ptrace, AppleEvents or IPC entitlement.
    return '\n'.join(['(version 1)', '(deny default)', '(allow process-exec)',
        '(allow process-fork)', '(allow file-read*)', '(allow sysctl-read)',
        '(allow file-write* (literal "/dev/null"))'] +
        ['(allow file-write* (subpath ' + json.dumps(str(pathlib.Path(p).resolve())) + '))' for p in writes])

def main():
    if sys.platform != 'darwin' or os.geteuid() == 0:
        raise RuntimeError('This sandbox profile requires macOS and an unprivileged user')
    args = sys.argv[1:]
    writes, env_names = [], []
    while args and args[0] != '--':
        arg = args.pop(0)
        if arg in ('--best-effort', '-ldd', '-add-exec'):
            continue # Never permits best-effort behavior: Seatbelt must start successfully.
        if arg not in ('--ro', '--rw', '--rwx', '--rox', '--env') or not args:
            raise RuntimeError('Unsupported sandbox argument: ' + arg)
        val = args.pop(0)
        if arg == '--env':
            env_names.append(val)
        elif arg in ('--rw', '--rwx'):
            if val == '/dev':
                continue # Narrower than upstream: only /dev/null is writable.
            dest = pathlib.Path(val).resolve()
            expected = pathlib.Path.cwd().resolve() / '.lake'
            if dest != expected:
                raise RuntimeError('Unexpected writable path: ' + str(dest))
            writes.append(dest)
    if not args or len(args) < 2:
        raise RuntimeError('Missing sandbox command')
    command = args[1:]
    env = {k: os.environ[k] for k in env_names if k in os.environ}
    # Environment is inherited only from the independently controlled harness.
    for key in ('PATH', 'HOME', 'TMPDIR', 'LEAN_PATH', 'LEAN_ABORT_ON_PANIC'):
        if key in os.environ:
            env.setdefault(key, os.environ[key])
    out = subprocess.run(['/usr/bin/sandbox-exec', '-p', policy(writes), *command], env=env,
                         stdout=subprocess.PIPE)
    # Export bytes are captured outside the submission's write permissions.
    if pathlib.Path(command[0]).name == 'lean4export' and out.returncode == 0:
        dest = pathlib.Path(os.environ['NILRADICAL_EXPORT_DIR'])
        name = command[1].replace('.', '_') + '.ndjson'
        (dest / name).write_bytes(out.stdout)
    sys.stdout.buffer.write(out.stdout)
    return out.returncode

if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as e:
        print('SANDBOX_BLOCKED:', e, file=sys.stderr)
        sys.exit(70)
