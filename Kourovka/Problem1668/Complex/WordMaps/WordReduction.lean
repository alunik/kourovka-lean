import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Find

/-!
# Alternating representatives of two-generator words

A shortest syllable list among all conjugates contains no zero exponent, no
adjacent equal generator, and (unless it is a singleton) no equal first and last
generator. Rotating once if necessary therefore gives alternating nonzero powers
of generator zero and generator one. The proof uses only the universal property
of the free group and ordinary group identities.
-/

namespace WordMaps

abbrev WordSyllable := Fin 2 × ℤ

def syllableProduct (l : List WordSyllable) : FreeGroup (Fin 2) :=
  (l.map fun p => FreeGroup.of p.1 ^ p.2).prod

@[simp] theorem syllableProduct_nil : syllableProduct [] = 1 := rfl

@[simp] theorem syllableProduct_cons (p : WordSyllable) (l : List WordSyllable) :
    syllableProduct (p :: l) = FreeGroup.of p.1 ^ p.2 * syllableProduct l := rfl

@[simp] theorem syllableProduct_append (l k : List WordSyllable) :
    syllableProduct (l ++ k) = syllableProduct l * syllableProduct k := by
  simp [syllableProduct]

theorem exists_syllableProduct (w : FreeGroup (Fin 2)) :
    ∃ l, syllableProduct l = w := by
  induction w using FreeGroup.induction_on with
  | one => exact ⟨[], rfl⟩
  | of i => exact ⟨[(i, 1)], by simp⟩
  | inv_of i _ => exact ⟨[(i, -1)], by simp⟩
  | mul x y hx hy =>
    obtain ⟨l, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := hy
    exact ⟨l ++ k, syllableProduct_append _ _⟩

theorem exists_minimal_syllableProduct (w : FreeGroup (Fin 2)) :
    ∃ l, IsConj w (syllableProduct l) ∧
      ∀ k, IsConj w (syllableProduct k) → l.length ≤ k.length := by
  classical
  have hex : ∃ n : ℕ, ∃ l, l.length = n ∧ IsConj w (syllableProduct l) := by
    obtain ⟨l, rfl⟩ := exists_syllableProduct w
    exact ⟨l.length, l, rfl, IsConj.refl _⟩
  obtain ⟨l, hl, hc⟩ := Nat.find_spec hex
  refine ⟨l, hc, fun k hk => ?_⟩
  rw [hl]
  exact Nat.find_min' hex ⟨k, rfl, hk⟩

theorem minimal_syllables_nonzero {w : FreeGroup (Fin 2)} {l : List WordSyllable}
    (hc : IsConj w (syllableProduct l))
    (hmin : ∀ k, IsConj w (syllableProduct k) → l.length ≤ k.length) :
    ∀ p ∈ l, p.2 ≠ 0 := by
  intro p hp hz
  obtain ⟨a, b, rfl⟩ := List.mem_iff_append.mp hp
  have heq : syllableProduct (a ++ p :: b) = syllableProduct (a ++ b) := by
    simp [hz]
  have h := hmin (a ++ b) (heq ▸ hc)
  simp only [List.length_append, List.length_cons] at h
  omega

theorem minimal_syllables_chain {w : FreeGroup (Fin 2)} {l : List WordSyllable}
    (hc : IsConj w (syllableProduct l))
    (hmin : ∀ k, IsConj w (syllableProduct k) → l.length ≤ k.length) :
    l.IsChain (fun a b => a.1 ≠ b.1) := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro a b pre post hl hab
  subst l
  let c : WordSyllable := (a.1, a.2 + b.2)
  have heq : syllableProduct (pre ++ a :: b :: post) =
      syllableProduct (pre ++ c :: post) := by
    simp [c, ← hab, zpow_add, mul_assoc]
  have h := hmin (pre ++ c :: post) (heq ▸ hc)
  simp only [List.length_append, List.length_cons] at h
  omega

theorem minimal_syllables_boundary {w : FreeGroup (Fin 2)}
    {a b : WordSyllable} {mid : List WordSyllable}
    (hc : IsConj w (syllableProduct (a :: mid ++ [b])))
    (hmin : ∀ k, IsConj w (syllableProduct k) →
      (a :: mid ++ [b]).length ≤ k.length) : a.1 ≠ b.1 := by
  intro hab
  let c : WordSyllable := (a.1, b.2 + a.2)
  have hconj : IsConj (syllableProduct (a :: mid ++ [b]))
      (syllableProduct (mid ++ [c])) := by
    rw [isConj_iff]
    refine ⟨(FreeGroup.of a.1 ^ a.2)⁻¹, ?_⟩
    simp only [syllableProduct_cons, syllableProduct_append, syllableProduct_nil,
      mul_one, inv_inv]
    simp [c, ← hab, zpow_add, mul_assoc]
  have h := hmin (mid ++ [c]) (hc.trans hconj)
  simp only [List.length_append, List.length_cons, List.length_nil] at h
  omega

def pairedSyllables (bs : List (ℤ × ℤ)) : List WordSyllable :=
  bs.flatMap fun p => [(0, p.1), (1, p.2)]

@[simp] theorem pairedSyllables_nil : pairedSyllables [] = [] := rfl

@[simp] theorem pairedSyllables_cons (p : ℤ × ℤ) (bs : List (ℤ × ℤ)) :
    pairedSyllables (p :: bs) = (0, p.1) :: (1, p.2) :: pairedSyllables bs := rfl

theorem chain_eq_pairedSyllables (l : List WordSyllable)
    (hc : l.IsChain (fun a b => a.1 ≠ b.1))
    (hfirst : ∀ a ∈ l.head?, a.1 = 0)
    (hlast : ∀ a ∈ l.getLast?, a.1 = 1) :
    ∃ bs, pairedSyllables bs = l := by
  induction l using List.twoStepInduction with
  | nil => exact ⟨[], rfl⟩
  | singleton a =>
    have h0 := hfirst a (by simp)
    have h1 := hlast a (by simp)
    exact False.elim (by omega)
  | cons_cons a b l ih _ =>
    have ha : a.1 = 0 := hfirst a (by simp)
    have hb : b.1 = 1 := by
      have hne := (List.isChain_cons_cons.mp hc).1
      omega
    have hcl : l.IsChain (fun a b => a.1 ≠ b.1) := hc.tail.tail
    have hfl : ∀ c ∈ l.head?, c.1 = 0 := by
      intro c hmem
      have hne := hc.tail.rel_head? hmem
      omega
    have hll : ∀ c ∈ l.getLast?, c.1 = 1 := by
      cases l with
      | nil => simp
      | cons c t => simpa using hlast
    obtain ⟨bs, hbs⟩ := ih hcl hfl hll
    refine ⟨(a.2, b.2) :: bs, ?_⟩
    simp only [pairedSyllables_cons, hbs]
    congr 1
    · exact Prod.ext ha.symm rfl
    · congr 1
      exact Prod.ext hb.symm rfl

theorem pairedSyllables_nonzero {bs : List (ℤ × ℤ)}
    (h : ∀ p ∈ pairedSyllables bs, p.2 ≠ 0) :
    ∀ p ∈ bs, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  induction bs with
  | nil => simp
  | cons p bs ih =>
    simp only [pairedSyllables_cons, List.mem_cons, forall_eq_or_imp] at h
    simpa using And.intro (And.intro h.1 h.2.1) (ih h.2.2)

/-- Every nonidentity two-generator word is conjugate either to a nonzero
generator power or to a nonempty sequence of nonzero alternating powers. -/
theorem word_conjugate_power_or_blocks (w : FreeGroup (Fin 2)) (hw : w ≠ 1) :
    (∃ i : Fin 2, ∃ m : ℤ, m ≠ 0 ∧ IsConj w (FreeGroup.of i ^ m)) ∨
    ∃ bs : List (ℤ × ℤ), bs ≠ [] ∧ (∀ p ∈ bs, p.1 ≠ 0 ∧ p.2 ≠ 0) ∧
      IsConj w (syllableProduct (pairedSyllables bs)) := by
  obtain ⟨l, hc, hmin⟩ := exists_minimal_syllableProduct w
  have hnz := minimal_syllables_nonzero hc hmin
  have hchain := minimal_syllables_chain hc hmin
  cases l with
  | nil => exact False.elim (hw (isConj_one_left.mp hc))
  | cons a l =>
    cases l using List.reverseRecOn with
    | nil =>
      left
      exact ⟨a.1, a.2, hnz a (by simp), by simpa using hc⟩
    | append_singleton mid b =>
      right
      have hab := minimal_syllables_boundary hc hmin
      have finish (k : List WordSyllable) (hk : k ≠ [])
          (hck : IsConj w (syllableProduct k))
          (hnzk : ∀ p ∈ k, p.2 ≠ 0)
          (hchaink : k.IsChain (fun a b => a.1 ≠ b.1))
          (hfirst : ∀ p ∈ k.head?, p.1 = 0)
          (hlast : ∀ p ∈ k.getLast?, p.1 = 1) :
          ∃ bs, bs ≠ [] ∧ (∀ p ∈ bs, p.1 ≠ 0 ∧ p.2 ≠ 0) ∧
            IsConj w (syllableProduct (pairedSyllables bs)) := by
        obtain ⟨bs, hbs⟩ := chain_eq_pairedSyllables k hchaink hfirst hlast
        refine ⟨bs, ?_, pairedSyllables_nonzero (hbs ▸ hnzk), hbs ▸ hck⟩
        intro he
        simp [he] at hbs
        exact hk hbs
      by_cases ha : a.1 = 0
      · have hb : b.1 = 1 := by omega
        apply finish (a :: mid ++ [b]) (by simp) hc hnz hchain
        · simpa using ha
        · simp only [List.getLast?_concat]
          simpa using hb
      · have ha1 : a.1 = 1 := by omega
        let k := mid ++ [b] ++ [a]
        have hck : IsConj w (syllableProduct k) := by
          apply hc.trans
          rw [isConj_iff]
          refine ⟨(FreeGroup.of a.1 ^ a.2)⁻¹, ?_⟩
          simp [k, mul_assoc]
        have hnzk : ∀ p ∈ k, p.2 ≠ 0 := by
          intro p hp
          apply hnz p
          simpa [k, or_assoc, or_comm, or_left_comm] using hp
        have hchaink : k.IsChain (fun a b => a.1 ≠ b.1) := by
          apply hchain.tail.append (List.IsChain.singleton _)
          simpa using hab.symm
        apply finish k (by simp [k]) hck hnzk hchaink
        · intro p hp
          have hmem : p ∈ (mid ++ [b]).head? := by
            simpa [k, List.head?_append_of_ne_nil] using hp
          have hne := hchain.rel_head? hmem
          omega
        · simpa [k] using ha1

end WordMaps
