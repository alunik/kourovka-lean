#!/usr/bin/env python3
"""Small regression controls for configuration and snapshot escape routes."""
import argparse, json, pathlib, shutil, tempfile, unittest
from unittest.mock import patch
import verify

class Guardrails(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='nilradical-guard-')
        self.root=pathlib.Path(self.temp.name)
        self.project=self.root/'project'
        shutil.copytree(verify.ROOT/'fixtures/positive',self.project)
    def tearDown(self): self.temp.cleanup()
    def change_manifest(self, **changes):
        p=self.project/'lake-manifest.json';d=json.loads(p.read_text());d.update(changes);verify.dump(p,d)
    def test_external_packages_dir(self):
        self.change_manifest(packagesDir='../other')
        with self.assertRaisesRegex(ValueError,'directories'): verify.source_inventory(self.project)
    def test_external_source_dir(self):
        with (self.project/'lakefile.toml').open('a') as f:f.write('\nsrcDir = "../other"\n')
        with self.assertRaises(ValueError): verify.source_inventory(self.project)
    def test_external_package_configuration(self):
        self.change_manifest(packages=[{'name':'dep','configFile':'../outside.lean'}])
        with self.assertRaisesRegex(ValueError,'config/manifest'): verify.source_inventory(self.project)
    def test_source_directory_symlink(self):
        (self.project/'Alias').symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(ValueError,'symlink'): verify.source_inventory(self.project)
    def test_compiled_directory_symlink(self):
        cache=self.root/'cache';cache.mkdir();(cache/'Alias').symlink_to(self.project,target_is_directory=True)
        with self.assertRaisesRegex(ValueError,'symlink'): verify.tree_inventory(cache)
    def test_changed_while_staging(self):
        contract=self.root/'contract.json'
        verify.freeze(argparse.Namespace(project=str(self.project),challenge=str(verify.ROOT/'fixtures/Challenge.lean'),
            solution_module='Solution',theorem=['verified'],output=str(contract)))
        original=shutil.copyfile
        def race(src,dst,*args,**kwargs):
            result=original(src,dst,*args,**kwargs)
            if pathlib.Path(src).name=='Solution.lean':
                with open(dst,'a') as f:f.write('\n-- changed during staging\n')
            return result
        receipt=self.root/'receipt.json'
        with patch('verify.shutil.copyfile',side_effect=race):
            rc=verify.verify(argparse.Namespace(contract=str(contract),contract_sha256=verify.sha(contract),receipt=str(receipt),timeout=60))
        data=json.loads(receipt.read_text())
        self.assertEqual(rc,1);self.assertEqual(data['status'],'INTEGRITY_BLOCKED')
        self.assertIn('Source changed while staging',data['reason'])
    def test_nonpositive_timeout(self):
        receipt=self.root/'receipt.json'
        rc=verify.verify(argparse.Namespace(contract='not-opened',contract_sha256='not-opened',receipt=str(receipt),timeout=0))
        self.assertEqual(rc,1);self.assertIn('positive',json.loads(receipt.read_text())['reason'])

if __name__=='__main__':unittest.main(verbosity=2)
