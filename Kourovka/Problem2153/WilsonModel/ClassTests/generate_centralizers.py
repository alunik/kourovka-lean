"""Emit bounded kernel checks; the soundness theorem is in Base.lean."""
from pathlib import Path
HERE=Path(__file__).resolve().parent
for w in range(16):
    (HERE/f'Centralizer{w:02}.lean').write_text(f'''import Kourovka.Problem2153.WilsonModel.ClassTests.Base
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.ClassTests

theorem pattern_uniform_{w} : (fun a c : Fin 7 => centralizerPattern a c {w}) =
    (fun (_ : Fin 7) (c : Fin 7) => centralizerPattern 0 c {w}) := by decide +kernel

end Kourovka.Problem2153.WilsonModel.ClassTests
''')
