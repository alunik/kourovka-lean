#!/usr/bin/env python3
"""Nilradical's independently controlled Comparator/Nanoda acceptance runner.
Only freeze trusted challenge inputs. Run never executes a submission outside a sandbox.
"""
import argparse, hashlib, json, os, pathlib, platform, re, shutil, signal, subprocess, sys, time, tomllib
from datetime import datetime, timezone
ROOT = pathlib.Path(__file__).resolve().parent
ALLOWED = ['propext', 'Quot.sound', 'Classical.choice']
MODULE = re.compile(r'^[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*$')

def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for block in iter(lambda: f.read(1024*1024), b''):
            h.update(block)
    return h.hexdigest()

def dump(path, obj):
    pathlib.Path(path).write_text(json.dumps(obj, indent=2, sort_keys=True)+'\n')

def canonical(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

def run(cmd, cwd=None, env=None, timeout=60):
    return subprocess.run(cmd, cwd=cwd, env=env, text=True, capture_output=True, timeout=timeout)

def tree_inventory(root):
    root = pathlib.Path(root)
    files = {}
    if root.exists():
        for path in sorted(root.rglob('*')):
            if path.is_symlink() and path.is_dir():
                raise ValueError('Directory symlink is not supported in trusted tree: '+str(path))
            if path.is_file():
                if path.is_symlink():
                    files[path.relative_to(root).as_posix()] = {'link': os.readlink(path), 'sha256': sha(path)}
                else:
                    files[path.relative_to(root).as_posix()] = sha(path)
    return {'sha256': canonical(files), 'file_count': len(files)}

def validate_project_config(project):
    config = tomllib.loads((project/'lakefile.toml').read_text())
    allowed = {'name', 'version', 'defaultTargets', 'require', 'lean_lib'}
    if set(config) - allowed:
        raise ValueError('Unsupported project TOML settings: '+str(sorted(set(config)-allowed)))
    for library in config.get('lean_lib', []):
        if set(library) != {'name'} or not MODULE.fullmatch(library['name']):
            raise ValueError('Only ordinary named lean_lib roots are supported')
    for dependency in config.get('require', []):
        if set(dependency) - {'name','scope','git','rev'} or 'git' not in dependency or not re.fullmatch(r'[0-9a-f]{40}',dependency.get('rev','')):
            raise ValueError('Project requirements must use exact Git commits with standard paths')
    manifest = json.loads((project/'lake-manifest.json').read_text())
    if manifest.get('packagesDir', '.lake/packages') != '.lake/packages' or manifest.get('lakeDir', '.lake') != '.lake':
        raise ValueError('Nonstandard Lake cache/package directories are not supported')
    names = []
    for dependency in manifest['packages']:
        if dependency.get('configFile') not in (None,'lakefile','lakefile.lean','lakefile.toml') or dependency.get('manifestFile') not in (None,'lake-manifest.json'):
            raise ValueError('Nonstandard dependency config/manifest paths are not supported')
        names.append(dependency['name'])
    if len(names) != len(set(names)):
        raise ValueError('Duplicate dependency package names')

def source_inventory(project):
    validate_project_config(project)
    files = []
    for directory in project.rglob('*'):
        rel = directory.relative_to(project)
        if not any(x.startswith('.') for x in rel.parts) and directory.is_symlink() and directory.is_dir():
            raise ValueError('Source directory symlink is not supported: '+str(rel))
    for p in project.rglob('*.lean'):
        relative = p.relative_to(project)
        if any(x.startswith('.') for x in relative.parts):
            continue
        if p.is_symlink():
            raise ValueError('Source symlinks are not accepted: '+str(relative))
        files.append(relative.as_posix())
    for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
        if not (project/name).is_file():
            raise ValueError('Missing trusted project configuration '+name)
        files.append(name)
    if (project/'lakefile.lean').exists():
        raise ValueError('Executable project lakefile.lean is not supported; use reviewed TOML')
    return {name: sha(project/name) for name in sorted(files)}

def dependency_inventory(project):
    manifest = json.loads((project/'lake-manifest.json').read_text())
    answer = {}
    for dep in manifest['packages']:
        if dep['type'] != 'git' or dep.get('subDir'):
            raise ValueError('Only exact Git-pinned whole-package dependencies are supported')
        name = dep['name']
        if not re.fullmatch('[A-Za-z0-9_-]+', name):
            raise ValueError('Bad package name')
        p = (project/'.lake/packages'/name).resolve()
        result = run(['git', '-C', str(p), 'rev-parse', 'HEAD'])
        if result.returncode or result.stdout.strip() != dep['rev']:
            raise ValueError('Dependency revision mismatch: '+name)
        status = run(['git', '-C', str(p), 'status', '--porcelain', '--untracked-files=no'])
        if status.returncode or status.stdout.strip():
            raise ValueError('Dirty trusted dependency: '+name)
        # Byte-bind all .lean inputs, including untracked ones. Build caches are a
        # declared trusted-upstream input; never copy any project build output.
        for directory in p.rglob('*'):
            rel = directory.relative_to(p)
            if '.git' not in rel.parts and '.lake' not in rel.parts and directory.is_symlink() and directory.is_dir():
                raise ValueError('Dependency source directory symlink is not supported: '+str(directory))
        src = {x.relative_to(p).as_posix(): sha(x) for x in sorted(p.rglob('*.lean'))
               if '.git' not in x.relative_to(p).parts and '.lake' not in x.relative_to(p).parts}
        answer[name] = {'path': str(p), 'rev': dep['rev'], 'sources_sha256': canonical(src),
                        'source_file_count': len(src), 'build_cache': tree_inventory(p/'.lake/build'),
                        'lake_config_cache': {x.name:sha(x) for x in sorted((p/'.lake').glob('lakefile.*')) if x.is_file()},
                        'cache_trust': 'existing upstream cache, read-only during run'}
    return answer

def freeze(args):
    project = pathlib.Path(args.project).resolve()
    challenge = pathlib.Path(args.challenge).resolve()
    if not MODULE.fullmatch(args.solution_module) or not all(MODULE.fullmatch(n) for n in args.theorem):
        raise ValueError('Use explicit nonempty fully qualified names')
    if not (project/(args.solution_module.replace('.', '/')+'.lean')).is_file():
        raise ValueError('Named solution module source is absent')
    data = {'schema': 1, 'created_utc': datetime.now(timezone.utc).isoformat(),
            'tools_manifest_sha256': sha(ROOT/'tools.local.json'),
            'project': str(project), 'source_files': source_inventory(project),
            'dependencies': dependency_inventory(project),
            'challenge_text': challenge.read_text(), 'challenge_sha256': sha(challenge),
            'solution_module': args.solution_module, 'theorem_names': args.theorem,
            'permitted_axioms': ALLOWED,
            'profile': 'macos-seatbelt-comparator-nanoda-v1',
            'human_approval': 'REQUIRED_SEPARATELY; freezing does not approve mathematical meaning'}
    dump(args.output, data)
    print('FROZEN', sha(args.output))

def tools_check():
    data = json.loads((ROOT/'tools.local.json').read_text())
    for name in ('comparator', 'exporter', 'nanoda', 'lean', 'lake'):
        entry = data[name]
        if sha(entry['path']) != entry['sha256']:
            raise ValueError('Checker binary hash changed: '+name)
    prefix = pathlib.Path(data['lean']['path']).parent
    if tree_inventory(prefix.parent/'lib') != data['toolchain_library_tree']:
        raise ValueError('Lean toolchain library/cache tree changed')
    version = run([data['lean']['path'], '--version'])
    if version.returncode or data['lean_version_string'] != version.stdout.strip():
        raise ValueError('Lean version mismatch')
    return data, prefix

def isolation_probe(work, env):
    import sandbox
    writable = work/'probe-write'
    writable.mkdir()
    protected = work/'protected-canary'
    protected.write_text('immutable\n')
    (writable/'dependency-alias').symlink_to(protected)
    # Probe filesystem denial, inherited child denial, TCP and AF_UNIX sockets,
    # and successful allowed output. No external network connection is made.
    code = r'''import pathlib, socket, subprocess, sys
p=pathlib.Path(sys.argv[1]); w=pathlib.Path(sys.argv[2]); passed=[]
try: p.write_text('tampered'); raise RuntimeError('write unexpectedly permitted')
except PermissionError: passed.append('protected_write_denied')
c=subprocess.run(['/bin/sh','-c','printf tampered > "$1"','sh',str(p)],capture_output=True)
assert c.returncode != 0, 'child escaped sandbox'; passed.append('child_write_denied')
for typ, addr in [(socket.AF_INET, ('127.0.0.1',0)),(socket.AF_UNIX,'/tmp/nilradical-isolation-probe')]:
 try:
  s=socket.socket(typ,socket.SOCK_STREAM); s.bind(addr); raise RuntimeError('network unexpectedly permitted')
 except PermissionError: passed.append('socket_denied_'+str(typ))
try: (w/'dependency-alias').write_text('tampered'); raise RuntimeError('symlink write unexpectedly permitted')
except PermissionError: passed.append('dependency_symlink_write_denied')
(w/'allowed').write_text('allowed'); passed.append('build_write_permitted')
print('|'.join(passed))
'''
    p = run(['/usr/bin/sandbox-exec','-p',sandbox.policy([writable]),sys.executable,
             '-c',code,str(protected),str(writable)], env=env)
    if p.returncode or protected.read_text() != 'immutable\n':
        raise ValueError('Isolation probe failed: '+p.stdout+p.stderr)
    return p.stdout.strip().split('|')

def verify(args):
    report = {'schema': 1, 'status': 'INTEGRITY_BLOCKED', 'started_utc': datetime.now(timezone.utc).isoformat(),
              'host': platform.platform(), 'human_statement_approval': 'NOT_RECORDED'}
    receipt = pathlib.Path(args.receipt).resolve()
    receipt.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    try:
        if sys.platform != 'darwin' or os.geteuid() == 0:
            raise ValueError('Current tested profile requires macOS and non-root; no unsandboxed fallback')
        if args.timeout <= 0:
            raise ValueError('Timeout must be positive')
        contract = pathlib.Path(args.contract).resolve()
        if sha(contract) != args.contract_sha256:
            raise ValueError('Frozen contract hash mismatch')
        data = json.loads(contract.read_text())
        if data['schema'] != 1 or data['permitted_axioms'] != ALLOWED or not data['theorem_names']:
            raise ValueError('Invalid or weakened contract')
        if data['profile'] != 'macos-seatbelt-comparator-nanoda-v1':
            raise ValueError('Unknown acceptance profile')
        if sha(ROOT/'tools.local.json') != data.get('tools_manifest_sha256'):
            raise ValueError('Verifier tool manifest differs from frozen contract')
        if hashlib.sha256(data['challenge_text'].encode()).hexdigest() != data['challenge_sha256']:
            raise ValueError('Frozen challenge text/hash mismatch')
        report['contract_sha256'] = sha(contract)
        project = pathlib.Path(data['project'])
        if source_inventory(project) != data['source_files']:
            raise ValueError('Source snapshot changed since freeze')
        if dependency_inventory(project) != data['dependencies']:
            raise ValueError('Dependency snapshot changed since freeze')
        tool, prefix = tools_check()
        report['tools'] = tool
        report['harness_sha256'] = {p.name: sha(p) for p in [ROOT/'verify.py', ROOT/'sandbox.py']}
        work = receipt.parent/('work-'+str(time.time_ns()))
        work.mkdir()
        report['work_directory'] = str(work)
        stage = work/'project'
        stage.mkdir()
        for name in data['source_files']:
            target = stage/name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(project/name, target)
            if sha(target) != data['source_files'][name]:
                raise ValueError('Source changed while staging: '+name)
        # Trust only reviewed project TOML and pinned dependencies, with a fixed
        # verifier-owned challenge module. Never import project build outputs.
        challenge_name = 'NilradicalFrozenChallenge'
        if (stage/(challenge_name+'.lean')).exists():
            raise ValueError('Reserved verifier module collision')
        (stage/(challenge_name+'.lean')).write_text(data['challenge_text'])
        if sha(stage/(challenge_name+'.lean')) != data['challenge_sha256']:
            raise ValueError('Staged challenge digest mismatch')
        with (stage/'lakefile.toml').open('a') as f:
            f.write('\n[[lean_lib]]\nname = "NilradicalFrozenChallenge"\n')
        package_dir = stage/'.lake/packages'
        package_dir.mkdir(parents=True)
        for name, dep in data['dependencies'].items():
            (package_dir/name).symlink_to(dep['path'], target_is_directory=True)
        exports = work/'exports'
        exports.mkdir()
        tmp = work/'tmp'
        tmp.mkdir()
        (work/'home').mkdir()
        env = {'PATH':str(prefix)+':/usr/bin:/bin:/usr/sbin:/sbin', 'HOME':str(work/'home'),
               'TMPDIR':str(tmp)+'/', 'LEAN_ABORT_ON_PANIC':'1',
               'COMPARATOR_LANDRUN':str(ROOT/'sandbox.py'),
               'COMPARATOR_LEAN4EXPORT':tool['exporter']['path'],
               'NILRADICAL_EXPORT_DIR':str(exports)}
        report['isolation_checks'] = isolation_probe(work, env)
        config = {'challenge_module':challenge_name, 'solution_module':data['solution_module'],
                  'theorem_names':data['theorem_names'], 'permitted_axioms':ALLOWED,
                  'external_kernels':{'nanoda':[tool['nanoda']['path']]}}
        cfg = work/'comparator.json'
        dump(cfg, config)
        before = {str(p):sha(p) for p in [cfg, contract, ROOT/'verify.py', ROOT/'sandbox.py', ROOT/'tools.local.json']}
        stage_sources = {str(stage/n):sha(stage/n) for n in data['source_files']}
        stage_sources[str(stage/(challenge_name+'.lean'))] = sha(stage/(challenge_name+'.lean'))
        before.update(stage_sources)
        cmd = [tool['lake']['path'], 'env', tool['comparator']['path'], str(cfg)]
        report['command'] = cmd
        logfile = receipt.parent/(receipt.stem+'.log')
        with logfile.open('wb') as log:
            proc = subprocess.Popen(cmd, cwd=stage, env=env, stdout=log, stderr=subprocess.STDOUT,
                                    start_new_session=True)
            try:
                rc = proc.wait(timeout=args.timeout)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
                raise ValueError('Whole-process timeout; process group killed')
            # Remove any child process deliberately left behind by elaboration.
            try: os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError: pass
        report['returncode'] = rc
        report['log'] = str(logfile)
        report['log_sha256'] = sha(logfile)
        if any(not pathlib.Path(p).is_file() or sha(p) != h for p,h in before.items()):
            raise ValueError('Protected verifier or staged sources were modified')
        if source_inventory(project) != data['source_files']:
            raise ValueError('Original source snapshot changed during verification')
        if dependency_inventory(project) != data['dependencies']:
            raise ValueError('Dependency source/cache snapshot changed during verification')
        tools_check()
        report['exports'] = {p.name:{'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
                             for p in sorted(exports.glob('*.ndjson'))}
        if rc != 0:
            report['status'] = 'INTEGRITY_REJECTED'
            report['reason'] = 'Comparator did not accept: inspect log; never accept solver PASS text'
        elif len(report['exports']) != 2:
            raise ValueError('Both independently captured exports are required')
        else:
            # Status is governed by trusted binary exit status and immutable
            # config requiring both kernels; not strings generated by a solver.
            report['status'] = 'INTEGRITY_PASSED'
            report['next_gate'] = 'AWAITING_HUMAN_STATEMENT_AND_NOVELTY_APPROVAL'
            report['theorem_names'] = data['theorem_names']
            report['permitted_axioms'] = ALLOWED
            report['trust_notes'] = ['macOS Seatbelt custom profile tested by local canaries, not independently security-audited',
                'read access is broad; never run on a host with secrets available to untrusted submissions',
                'upstream compiled library caches are trusted inputs; byte hashes checked before and after; project sources rebuilt fresh',
                'same-kernel replay and independently implemented Nanoda verify one exported dependency closure',
                'semantic correctness of challenge requires separate human review']
    except Exception as e:
        report['reason'] = str(e)
    finally:
        report['elapsed_seconds'] = round(time.monotonic()-started,3)
        dump(receipt,report)
        print(report['status'],report.get('reason',''),str(receipt))
    return 0 if report['status'] == 'INTEGRITY_PASSED' else 1

def main():
    p=argparse.ArgumentParser(description=__doc__)
    sub=p.add_subparsers(dest='command',required=True)
    f=sub.add_parser('freeze')
    for key in ('project','challenge','solution-module','output'): f.add_argument('--'+key,required=True)
    f.add_argument('--theorem',action='append',required=True)
    v=sub.add_parser('run')
    for key in ('contract','contract-sha256','receipt'): v.add_argument('--'+key,required=True)
    v.add_argument('--timeout',type=int,default=3600)
    a=p.parse_args()
    if a.command=='freeze': freeze(a); return 0
    return verify(a)

if __name__=='__main__':
    try: sys.exit(main())
    except Exception as e: print('BLOCKED:',e,file=sys.stderr); sys.exit(1)
