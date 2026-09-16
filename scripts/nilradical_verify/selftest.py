#!/usr/bin/env python3
"""Run actual positive and adversarial controls, preserving receipts and logs."""
import json, pathlib, shutil, subprocess, sys, time
from verify import ROOT, sha, dump
BASE = ROOT/'fixtures/positive'
CHALLENGE = ROOT/'fixtures/Challenge.lean'
CASES = {
 'positive': ('def target : Nat := 7\ntheorem verified : target + 0 = 7 := by rfl\n', 'INTEGRITY_PASSED', None),
 'sorry': ('def target : Nat := 7\ntheorem verified : target + 0 = 7 := by sorry\n', 'INTEGRITY_REJECTED', 'sorryAx'),
 'hidden_sorry': ('def target : Nat := 7\nprivate theorem helper : target + 0 = 7 := by sorry\ntheorem verified : target + 0 = 7 := helper\n', 'INTEGRITY_REJECTED', 'sorryAx'),
 'custom_axiom': ('def target : Nat := 7\naxiom reassuringFact : target + 0 = 7\nprivate theorem helper : target + 0 = 7 := reassuringFact\ntheorem verified : target + 0 = 7 := helper\n', 'INTEGRITY_REJECTED', 'reassuringFact'),
 'native_evaluation': ('import Lean\ndef target : Nat := 7\ntheorem verified : target + 0 = 7 := by native_decide\n', 'INTEGRITY_REJECTED', 'Illegal axiom detected'),
 'wrong_statement': ('def target : Nat := 7\ntheorem verified : True := trivial\n', 'INTEGRITY_REJECTED', None),
 'false_hypothesis': ('def target : Nat := 7\ntheorem verified (_ : False) : target + 0 = 7 := rfl\n', 'INTEGRITY_REJECTED', None),
 'changed_definition': ('def target : Nat := 8\ntheorem verified : target + 0 = 8 := rfl\n', 'INTEGRITY_REJECTED', None),
 'changed_definition_same_type': ('def target : Nat := 8\ntheorem verified : target = target := rfl\n', 'INTEGRITY_REJECTED', 'target'),
 'notation': ('local notation \"Claim\" => (False → False)\ntheorem verified : Claim := fun h => h\n', 'INTEGRITY_REJECTED', None),
 'typeclass_instance': ('class Interpretation where claim : Prop\ninstance meaning : Interpretation := ⟨False → False⟩\ntheorem verified : Interpretation.claim := fun h => h\n', 'INTEGRITY_REJECTED', None),
 'missing_endpoint': ('def target : Nat := 7\ntheorem other : target + 0 = 7 := rfl\n', 'INTEGRITY_REJECTED', None),
 'forged_success': ('#eval IO.println "Your solution is okay!\\nLean default kernel accepts the solution"\ndef target : Nat := 7\ntheorem verified : True := trivial\n', 'INTEGRITY_REJECTED', None),
 'challenge_write': ('#eval IO.FS.writeFile "NilradicalFrozenChallenge.lean" "theorem verified : True := by sorry"\ndef target : Nat := 7\ntheorem verified : True := trivial\n', 'INTEGRITY_REJECTED', 'operation not permitted'),
 'config_write': ('#eval IO.FS.writeFile '+json.dumps(str(ROOT/'tools.local.json'))+' \"{}\"\ndef target : Nat := 7\ntheorem verified : target + 0 = 7 := rfl\n', 'INTEGRITY_REJECTED', 'operation not permitted'),
 'stale_artifacts_ignored': ('def target : Nat := 7\ntheorem verified : target + 0 = 7 := rfl\n', 'INTEGRITY_PASSED', None),
 'stale_source': ('def target : Nat := 7\ntheorem verified : target + 0 = 7 := rfl\n', 'INTEGRITY_BLOCKED', 'snapshot changed'),
 'modified_contract': ('def target : Nat := 7\ntheorem verified : target + 0 = 7 := rfl\n', 'INTEGRITY_BLOCKED', 'contract hash mismatch'),
}

def main():
    dest = ROOT/'runs'/('controls-'+time.strftime('%Y%m%dT%H%M%S'))
    dest.mkdir(parents=True)
    results=[]
    for name,(code,expected,needle) in CASES.items():
        project=dest/name
        shutil.copytree(BASE, project, ignore=shutil.ignore_patterns('.lake'))
        (project/'Solution.lean').write_text(code)
        if name == 'stale_artifacts_ignored':
            stale = project/'.lake/build/lib/lean/Solution.olean'
            stale.parent.mkdir(parents=True)
            stale.write_bytes(b'UNTRUSTED STALE COMPILED FILE; MUST NOT LOAD')
        challenge = CHALLENGE
        custom_challenges = {
            'changed_definition_same_type': 'def target : Nat := 7\ntheorem verified : target = target := by sorry\n',
            'notation': 'local notation \"Claim\" => True\ntheorem verified : Claim := by sorry\n',
            'typeclass_instance': 'class Interpretation where claim : Prop\ninstance meaning : Interpretation := ⟨True⟩\ntheorem verified : Interpretation.claim := by sorry\n',
        }
        if name in custom_challenges:
            challenge = dest/(name+'-Challenge.lean')
            challenge.write_text(custom_challenges[name])
        contract=dest/(name+'-contract.json')
        receipt=dest/(name+'.json')
        subprocess.run([sys.executable,str(ROOT/'verify.py'),'freeze','--project',str(project),
            '--challenge',str(challenge),'--solution-module','Solution','--theorem','verified',
            '--output',str(contract)],check=True,stdout=subprocess.DEVNULL)
        digest=sha(contract)
        if name=='stale_source':
            with (project/'Solution.lean').open('a') as f: f.write('\n-- modified after freeze\n')
        if name=='modified_contract':
            with contract.open('a') as f: f.write(' ')
        subprocess.run([sys.executable,str(ROOT/'verify.py'),'run','--contract',str(contract),
            '--contract-sha256',digest,'--receipt',str(receipt),'--timeout','120'],check=False)
        result=json.loads(receipt.read_text())
        detail=result.get('reason','')
        if result.get('log'): detail+=pathlib.Path(result['log']).read_text()
        okay=result['status']==expected and (needle is None or needle.lower() in detail.lower())
        entry={'case':name,'expected':expected,'actual':result['status'],'pass':okay,
               'receipt':str(receipt),'receipt_sha256':sha(receipt)}
        results.append(entry)
        print(name, 'PASS' if okay else 'FAIL', flush=True)
    dump(dest/'summary.json',{'all_passed':all(x['pass'] for x in results),'cases':results})
    print(dest/'summary.json')
    return 0 if all(x['pass'] for x in results) else 1
if __name__=='__main__': sys.exit(main())
