#!/usr/bin/env python3
"""Build pinned checkers and create the local trusted binary manifest. Python 3.11+."""
import argparse, json, os, pathlib, shutil, subprocess, sys
from verify import ROOT, sha, tree_inventory, dump

def command(args, cwd=None, env=None):
    subprocess.run([str(x) for x in args], cwd=cwd, env=env, check=True)

def checkout(url, rev, directory):
    if not directory.exists():
        command(['git','clone','--filter=blob:none',url,directory])
    if subprocess.check_output(['git','-C',str(directory),'status','--porcelain','--untracked-files=no'],text=True).strip():
        raise ValueError('Refusing to alter dirty tool checkout '+str(directory))
    command(['git','-C',directory,'checkout','--detach',rev])
    assert subprocess.check_output(['git','-C',str(directory),'rev-parse','HEAD'],text=True).strip()==rev

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean-prefix',type=pathlib.Path,required=True)
    p.add_argument('--cargo',type=pathlib.Path,required=True)
    p.add_argument('--rebuild',action='store_true',help='Replaces local checker manifest; invalidates frozen contracts')
    a=p.parse_args()
    if sys.platform != 'darwin' or os.geteuid()==0:
        raise ValueError('Only unprivileged macOS is implemented and tested')
    if (ROOT/'tools.local.json').exists() and not a.rebuild:
        raise ValueError('Local setup exists; use --rebuild only when no verification is running')
    pins=json.loads((ROOT/'pins.json').read_text())
    prefix=a.lean_prefix.resolve()
    version=subprocess.check_output([str(prefix/'bin/lean'),'--version'],text=True).strip()
    if '4.34.0-rc2' not in version or pins['lean_commit'] not in version:
        raise ValueError('Wrong Lean toolchain for the current supported profile')
    tools=ROOT/'tools';tools.mkdir(exist_ok=True)
    comparator=tools/'comparator';nanoda=tools/'nanoda'
    checkout(pins['comparator']['url'],pins['comparator']['rev'],comparator)
    checkout(pins['nanoda']['url'],pins['nanoda']['rev'],nanoda)
    env=os.environ.copy();env['PATH']=str(prefix/'bin')+':'+env.get('PATH','')
    command([prefix/'bin/lake','build','comparator','lean4export'],cwd=comparator,env=env)
    exported=comparator/'.lake/packages/lean4export'
    assert subprocess.check_output(['git','-C',str(exported),'rev-parse','HEAD'],text=True).strip()==pins['lean4export']['rev']
    cargo=a.cargo.absolute() # Keep the Cargo proxy basename; rustup dispatches on argv[0].
    # If using the bundled isolated rustup/cargo installation, keep its homes local.
    if (tools/'rustup').is_dir():
        env['RUSTUP_HOME']=str(tools/'rustup');env['CARGO_HOME']=str(tools/'cargo')
    command([cargo,'build','--manifest-path',nanoda/'Cargo.toml','--release','--locked'],env=env)
    binaries=tools/'bin';binaries.mkdir(exist_ok=True)
    shutil.copy2(comparator/'.lake/build/bin/comparator',binaries/'comparator')
    shutil.copy2(exported/'.lake/build/bin/lean4export',binaries/'lean4export')
    paths={'comparator':binaries/'comparator','exporter':binaries/'lean4export',
           'nanoda':nanoda/'target/release/nanoda_bin','lean':prefix/'bin/lean','lake':prefix/'bin/lake'}
    data={name:{'path':str(path),'sha256':sha(path)} for name,path in paths.items()}
    data.update({'lean_version_string':version, 'toolchain_library_tree':tree_inventory(prefix/'lib'),
                 'source_pins':{name:pins[name]['rev'] for name in ('comparator','lean4export','nanoda')},
                 'build_provenance':'Built from pinned clean upstream sources by bootstrap.py'})
    data['source_pins']['lean']=pins['lean_commit']
    dump(ROOT/'tools.local.json',data)
    print('Built and pinned. Run selftest.py before accepting any endpoint.')

if __name__=='__main__':
    try: main()
    except Exception as e: print('BOOTSTRAP_BLOCKED:',e,file=sys.stderr);sys.exit(1)
