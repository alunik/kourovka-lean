module

/-
Adapted from Qiuzhen-CFSG/CFSG, commit 96b2a02085dc678f3e0a97b334c31ada599c55fd.
Released under Apache 2.0; see ../LICENSE and SUZUKI_PROVENANCE.json.
-/
public import Mathlib.FieldTheory.Finite.GaloisField

namespace BenderSuzuki.PFAppendixIII
public instance instFactNatPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
public abbrev BinaryGaloisField (m : ℕ) : Type := GaloisField 2 m
end BenderSuzuki.PFAppendixIII
