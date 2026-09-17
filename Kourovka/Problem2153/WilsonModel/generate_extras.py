#!/usr/bin/env python3
"""Untrusted candidate tables for further kernel-checked Wilson products."""
from pathlib import Path
import importlib.util
HERE=Path(__file__).resolve().parent
INPUTS = next(p for p in HERE.parents if p.name == 'Problem2153') / 'campaign-inputs'
source = INPUTS / 'wilson_probe.py'
spec=importlib.util.spec_from_file_location('wilson_source',source)
m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
c=m.mm(m.t,m.sigma); c2=m.mm(c,c)
assert m.eq(m.mm(c2,c),m.I) and not m.eq(c,m.I)
s='''import Kourovka.Problem2153.WilsonModel.Certificates
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel
open Field8 F8
'''
for name,mat in [('c3',c),('c3Squared',c2)]:
 s+=f'def {name} : Mat :=\n  !!['+';\n    '.join(', '.join('e'+str(v) for v in row) for row in mat)+']\n\n'
s+='''theorem c3_eq : wilsonT * sigma = c3 := by decide +kernel
theorem c3Squared_eq : c3 * c3 = c3Squared := by decide +kernel
theorem c3_cubed_step : c3Squared * c3 = 1 := by decide +kernel
theorem c3_ne_one : c3 ≠ 1 := by decide +kernel
end Kourovka.Problem2153.WilsonModel
'''
(HERE/'Extras.lean').write_text(s)
