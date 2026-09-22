# Statement correspondence and scope

The independent agent reviews of 21 September 2026 found the two production statements to match their independent challenges. Both challenges used standard Mathlib objects. The later human statement approval accepted exactly these two results.

## Complex branch

`WordMaps.word_surjective` states that every `w : FreeGroup (Fin 2)` with `w ≠ 1` induces a surjective map on `PSL(2, K)` for a field `K` satisfying `CharZero K` and `IsAlgClosed K`. `WordMaps.complex_word_surjective` specializes this to the standard complex field.

`FreeGroup.lift` is ordinary group-word evaluation. A map from `Fin 2` supplies the ordered input pair. `PSL(2, K)` is Mathlib's special linear group modulo its center, and `Function.Surjective` means every target has an actual preimage. No restriction on word length, exponent sums, derived subgroup or proper powers is present. The proof derives the trace and conjugacy conditions internally; they are not extra endpoint assumptions.

## Real branch

`RealWord.exists_nontrivial_nonsurjective_word` states that there exists `w : FreeGroup (Fin 2)` with `w ≠ 1` whose ordinary evaluation map on standard `PSL(2, ℝ)` is not surjective.

The concrete word uses `[r,s] = r s r⁻¹ s⁻¹`, `d = b a b⁻¹`, `c = [a,d]` and `W = [a c a⁻¹, d c⁻¹ d⁻¹]`. The formal proof establishes `RealWord.word_ne_one`, the universal bound `RealWord.tr_value_gt_seven_fourths`, and omission of the projective image of `J = [[0,-1],[1,0]]`. It proves that this target is nonidentity and has square one. The quotient argument lifts arbitrary projective inputs and checks the center ambiguity; it is not a finite computational sample.

The formal omission endpoint names the class of `J`. The explanatory consequence that every nonidentity projective involution is omitted is not advertised as a separate checked Lean theorem. The SO₃(ℝ) result is credited prior work, outside these snapshots.

## Evidence and chronology

The exact endpoint lists, challenge digests and dependency pins appear in the sanitized [complex contract](complex-contract.json) and [real contract](real-contract.json). The protected [verification records](verification.json) mechanically compare statements and dependencies and check the proof exports in Lean and Nanoda. The standalone semantic reviews preceded those protected runs; their historical statements that approval was pending are superseded only by the later [human statement acceptance](acceptance.json).

Human statement acceptance establishes the recorded correspondence decision. It does not assert external peer review, accept priority, or endorse the later mathematical note.
