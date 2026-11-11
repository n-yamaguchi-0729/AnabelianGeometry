/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The imported Riemann–Roch and principal-divisor results retain the Anthropic FLT notices in
their source files. This file's simultaneous evaluation proof replaces the symmetric-product
argument in Akio Tamagawa, The Grothendieck conjecture for affine curves (1997), Claim 4.14.
-/

module

public import Nyll.AnabelianGeometry.FunctionField.SimultaneousRiemannRoch
public import Nyll.AnabelianGeometry.FunctionField.MinimalPencils
public import Nyll.AnabelianGeometry.FunctionField.PencilNormalization
public import Nyll.AnabelianGeometry.FunctionField.ThreePointPencil
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.EllAddEqOrd
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.SectionBounds
public import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree
public import Nyll.AlgebraicCurves.Places.Evaluation.HasValueIffMemEqOrOrdSubPos
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.Group.Submonoid.Basic

/-!
# Effective representatives for minimal-pencil generation

The concrete input `hRR` below is supplied by
`AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch` for an essentially finite type
curve function field over an algebraically closed base. No existence of movable divisors or
of generators is assumed. Simultaneous section-space vanishing constructs the representatives.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve Module
open scoped IntermediateField

namespace AnabelianGeometry.FunctionField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]

omit [IsCurveOver K F] in
/-- The canonical degree follows from the two Riemann–Roch identities at zero and `W`. -/
theorem canonical_degree_of_riemannRoch (W : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F,
      (ell D : ℤ) - ell (W - D) = Divisor.degree D + 1 - g) :
    Divisor.degree W = 2 * (g : ℤ) - 2 := by
  have hzero := hRR 0
  have hW := hRR W
  rw [sub_zero, map_zero] at hzero
  rw [sub_self] at hW
  omega

/-- A degree `2g-1` divisor has exactly `g` independent sections. -/
theorem ell_eq_genus_of_degree_two_mul_sub_one (W : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F,
      (ell D : ℤ) - ell (W - D) = Divisor.degree D + 1 - g)
    (D : Divisor K F) (hD : Divisor.degree D = 2 * (g : ℤ) - 1) :
    ell D = g := by
  have hW := canonical_degree_of_riemannRoch W g hRR
  have hneg : Divisor.degree (W - D) < 0 := by
    rw [map_sub, hW, hD]
    omega
  have hz := ell_eq_zero_of_degree_neg hneg
  have h := hRR D
  rw [hz, hD] at h
  omega

/-- A nonzero section gives the corresponding effective divisor in its divisor class. -/
theorem exists_effective_representative_of_ell_pos (A : Divisor K F) (hA : 0 < ell A) :
    ∃ E : Divisor K F, 0 ≤ E ∧ Divisor.degree E = Divisor.degree A ∧
      ell E = ell A ∧ (E - A).IsPrincipal := by
  have hbot : LSpace A ≠ ⊥ := by
    intro h
    have hz : ell A = 0 := by rw [ell, h, finrank_bot]
    omega
  obtain ⟨f, hfA, hf0⟩ := (Submodule.ne_bot_iff _).mp hbot
  obtain ⟨Δ, hΔ, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine ⟨A + Δ, ?_, ?_, ell_add_of_forall_eq_ord A hf0 hΔ, ?_⟩
  · rw [Finsupp.le_def]
    intro P
    have hb := (mem_lSpace_iff_ord.mp hfA).resolve_left hf0 P
    rw [Finsupp.zero_apply, Finsupp.add_apply, hΔ P]
    omega
  · rw [map_add, hdeg, add_zero]
  · refine ⟨f, hf0, fun P => ?_⟩
    rw [add_sub_cancel_left, hΔ P]

omit [IsCurveOver K F] in
/-- If a divisor has one section, it has at most one effective representative in its class. -/
theorem effective_representative_unique {A E E' : Divisor K F}
    (hA : ell A = 1) (hE : 0 ≤ E) (hE' : 0 ≤ E')
    (hEA : (E - A).IsPrincipal) (hE'A : (E' - A).IsPrincipal) : E = E' := by
  obtain ⟨f, hf0, hf⟩ := hEA
  obtain ⟨f', hf'0, hf'⟩ := hE'A
  have hfA : f ∈ LSpace A := by
    apply mem_lSpace_iff_ord.mpr
    refine Or.inr (fun P => ?_)
    have hb := hE P
    have heq := hf P
    simp only [Finsupp.zero_apply, Finsupp.sub_apply] at hb heq
    omega
  have hf'A : f' ∈ LSpace A := by
    apply mem_lSpace_iff_ord.mpr
    refine Or.inr (fun P => ?_)
    have hb := hE' P
    have heq := hf' P
    simp only [Finsupp.zero_apply, Finsupp.sub_apply] at hb heq
    omega
  let u : LSpace A := ⟨f, hfA⟩
  let u' : LSpace A := ⟨f', hf'A⟩
  have hu : u ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' u hu).mp hA u'
  have hcval : algebraMap K F c * f = f' := by
    have h := congrArg Subtype.val hc
    simpa only [SetLike.val_smul, Algebra.smul_def] using h
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at hcval
    exact hf'0 hcval.symm
  have hcF : algebraMap K F c ≠ 0 := (map_ne_zero (algebraMap K F)).mpr hc0
  ext P
  have heq := hf P
  have heq' := hf' P
  have hord : P.ord f' = P.ord f := by
    rw [← hcval, P.ord_mul hcF hf0, P.ord_algebraMap, zero_add]
  simp only [Finsupp.sub_apply] at heq heq'
  omega

/-- Vanishing after removal of a point forces every effective representative to avoid it. -/
theorem effective_representative_avoids_of_ell_sub_eq_zero
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {A E : Divisor K F} (hE : 0 ≤ E) (hEA : (E - A).IsPrincipal)
    (P : Place K F) (hzero : ell (A - Finsupp.single P 1) = 0) : E P = 0 := by
  obtain ⟨f, hf0, hf⟩ := hEA
  by_contra hEP
  have hpos : 1 ≤ E P := by
    have := hE P
    change 0 ≤ E P at this
    omega
  have hfmem : f ∈ LSpace (A - Finsupp.single P 1) := by
    apply mem_lSpace_iff_ord.mpr
    refine Or.inr (fun Q => ?_)
    have hQ := hE Q
    have horder := hf Q
    simp only [Finsupp.zero_apply, Finsupp.sub_apply] at hQ horder ⊢
    rcases eq_or_ne Q P with rfl | hQP
    · rw [Finsupp.single_eq_same]
      omega
    · rw [Finsupp.single_eq_of_ne hQP]
      omega
  have : FiniteDimensional K (LSpace (A - Finsupp.single P 1)) :=
    finiteDimensional_lSpace _
  have hbot : LSpace (A - Finsupp.single P 1) = ⊥ :=
    Submodule.finrank_eq_zero.mp hzero
  rw [hbot, Submodule.mem_bot] at hfmem
  exact hf0 hfmem

/-- Simultaneously choose one degree-`g` divisor whose prescribed degree-zero translates have
one section and avoid every point of a prescribed nonempty finite set. -/
theorem exists_simultaneous_degree_genus_divisor
    [IsAlgClosed K] [Algebra.EssFiniteType K F]
    (W : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F,
      (ell D : ℤ) - ell (W - D) = Divisor.degree D + 1 - g)
    {ι : Type*} [Finite ι] (C : ι → Divisor K F)
    (hC : ∀ i, Divisor.degree (C i) = 0)
    (B : Finset (Place K F)) (hB : B.Nonempty)
    (S : Set (Place K F)) (hS : S.Infinite) :
    ∃ A : Divisor K F, 0 ≤ A ∧ Divisor.degree A = g ∧
      (∀ P ∈ A.support, P ∈ S) ∧
      ∀ i, ell (A - C i) = 1 ∧
        ∀ P ∈ B, ell (A - C i - Finsupp.single P 1) = 0 := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let E : ι × B → Divisor K F := fun j => W + C j.1 + Finsupp.single j.2.1 1
  have hE : ∀ j, ell (E j) ≤ g := by
    intro j
    apply le_of_eq
    apply ell_eq_genus_of_degree_two_mul_sub_one W g hRR
    dsimp only [E]
    rw [map_add, map_add, hC j.1, add_zero, Divisor.degree_single,
      IsCurveOver.deg_eq_one_of_isAlgClosed]
    have hW := canonical_degree_of_riemannRoch W g hRR
    omega
  obtain ⟨T, hTS, hTcard, hTell⟩ :=
    exists_finset_simultaneous_ell_eq_zero g E hE S hS
  let A : Divisor K F := ∑ P ∈ T, Finsupp.single P 1
  have hAeff : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro P _
    rw [Finsupp.le_def]
    intro Q
    rcases eq_or_ne Q P with rfl | hQP
    · simp only [Finsupp.zero_apply, Finsupp.single_eq_same]
      exact zero_le_one
    · simp only [Finsupp.zero_apply, Finsupp.single_eq_of_ne hQP]
      exact le_rfl
  have hAdeg : Divisor.degree A = g := by
    change Divisor.degree (∑ P ∈ T, Finsupp.single P 1) = _
    rw [map_sum]
    simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed,
      Nat.cast_one, mul_one, Finset.sum_const, nsmul_eq_mul, mul_one, hTcard]
  have hvanish : ∀ i, ∀ P ∈ B, ell (A - C i - Finsupp.single P 1) = 0 := by
    intro i P hPB
    have hdual := hTell (i, ⟨P, hPB⟩)
    change ell (W + C i + Finsupp.single P 1 - A) = 0 at hdual
    have hrr := hRR (A - C i - Finsupp.single P 1)
    have heq : W - (A - C i - Finsupp.single P 1) =
        W + C i + Finsupp.single P 1 - A := by abel
    rw [heq, hdual, map_sub, map_sub, hAdeg, hC i, Divisor.degree_single,
      IsCurveOver.deg_eq_one_of_isAlgClosed] at hrr
    omega
  refine ⟨A, hAeff, hAdeg, ?_, ?_⟩
  · intro P hPA
    apply hTS
    by_contra hPT
    have hz : A P = 0 := by
      change (∑ Q ∈ T, Finsupp.single Q 1) P = 0
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro Q hQT
      exact Finsupp.single_eq_of_ne (fun hPQ => hPT (hPQ.symm ▸ hQT))
    exact Finsupp.mem_support_iff.mp hPA hz
  · intro i
    obtain ⟨P, hPB⟩ := hB
    have hupper := ell_le_ell_sub_single_add_deg (A - C i) P
    rw [hvanish i P hPB, IsCurveOver.deg_eq_one_of_isAlgClosed] at hupper
    have hlower := hRR (A - C i)
    rw [map_sub, hAdeg, hC i] at hlower
    refine ⟨by omega, hvanish i⟩

/-- The finite-family version of Tamagawa's Claim 4.14. Equal divisor classes automatically
receive the same effective representative; applying this to partial sums gives the cyclic
condition needed for the product decomposition. -/
theorem exists_simultaneous_effective_representatives
    [IsAlgClosed K] [Algebra.EssFiniteType K F]
    (W : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F,
      (ell D : ℤ) - ell (W - D) = Divisor.degree D + 1 - g)
    {ι : Type*} [Finite ι] (C : ι → Divisor K F)
    (hC : ∀ i, Divisor.degree (C i) = 0)
    (B : Finset (Place K F)) (hB : B.Nonempty)
    (S : Set (Place K F)) (hS : S.Infinite) :
    ∃ (A : Divisor K F) (D : ι → Divisor K F),
      (∀ i, 0 ≤ D i ∧ Divisor.degree (D i) = g ∧ ell (D i) = 1 ∧
        (∀ P ∈ B, D i P = 0) ∧ (D i - (A - C i)).IsPrincipal) ∧
      (∀ i j, (C i - C j).IsPrincipal → D i = D j) ∧
      ∀ i j, (D j - D i + (C j - C i)).IsPrincipal := by
  classical
  obtain ⟨A, _, hAdeg, _, hA⟩ :=
    exists_simultaneous_degree_genus_divisor W g hRR C hC B hB S hS
  obtain ⟨P, _⟩ := hS.nonempty
  have : Nonempty (Place K F) := ⟨P⟩
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
    finiteDimensional_lSpace_zero K F
  have hex : ∀ i, ∃ E : Divisor K F, 0 ≤ E ∧
      Divisor.degree E = Divisor.degree (A - C i) ∧
      ell E = ell (A - C i) ∧ (E - (A - C i)).IsPrincipal := by
    intro i
    apply exists_effective_representative_of_ell_pos
    rw [(hA i).1]
    exact zero_lt_one
  choose D hD using hex
  refine ⟨A, D, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hD i).1, ?_, ?_, ?_, (hD i).2.2.2⟩
    · rw [(hD i).2.1, map_sub, hAdeg, hC i, sub_zero]
    · exact (hD i).2.2.1.trans (hA i).1
    · intro Q hQB
      exact effective_representative_avoids_of_ell_sub_eq_zero (hD i).1
        (hD i).2.2.2 Q ((hA i).2 Q hQB)
  · intro i j hij
    have hj : (D j - (A - C i)).IsPrincipal := by
      have hsum := (Divisor.principal (K := K) (F := F)).add_mem (hD j).2.2.2 hij
      have heq : D j - (A - C i) = D j - (A - C j) + (C i - C j) := by abel
      rw [heq]
      exact Divisor.mem_principal.mp hsum
    exact effective_representative_unique (hA i).1 (hD i).1 (hD j).1
      (hD i).2.2.2 hj
  · intro i j
    have hsub := (Divisor.principal (K := K) (F := F)).sub_mem
      (hD j).2.2.2 (hD i).2.2.2
    have heq : D j - D i + (C j - C i) =
        (D j - (A - C j)) - (D i - (A - C i)) := by abel
    rw [heq]
    exact Divisor.mem_principal.mp hsub

private theorem divOf_prod {ι : Type*} (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    Divisor.divOf (K := K) (∏ i ∈ s, f i) = ∑ i ∈ s, Divisor.divOf (K := K) (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.prod_empty, Finset.sum_empty]
      ext P
      rw [Divisor.divOf_apply one_ne_zero, P.ord_one, Finsupp.zero_apply]
  | @insert i s his ih =>
      intro hf
      rw [Finset.prod_insert his, Finset.sum_insert his,
        Divisor.divOf_mul (hf i (Finset.mem_insert_self i s))
          (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

omit [IsCurveOver K F] in
private theorem sum_adjacent_divisor_sub {n : ℕ} (D : Fin (n + 1) → Divisor K F) :
    (∑ i : Fin n, (D i.succ - D i.castSucc)) = D (Fin.last n) - D 0 := by
  rw [Finset.sum_sub_distrib]
  have htotal : D 0 + (∑ i : Fin n, D i.succ) =
      (∑ i : Fin n, D i.castSucc) + D (Fin.last n) :=
    (Fin.sum_univ_succ D).symm.trans (Fin.sum_univ_castSucc D)
  calc
    (∑ i : Fin n, D i.succ) - ∑ i : Fin n, D i.castSucc =
        (D 0 + ∑ i : Fin n, D i.succ) - ((∑ i : Fin n, D i.castSucc) + D 0) := by abel
    _ = ((∑ i : Fin n, D i.castSucc) + D (Fin.last n)) -
        ((∑ i : Fin n, D i.castSucc) + D 0) := by rw [htotal]
    _ = D (Fin.last n) - D 0 := by abel

/-- Equality of actual principal divisors determines a nonzero function up to a constant. -/
theorem exists_constant_mul_of_divOf_eq (hC : ConstantsAreBase K F)
    {f h : F} (hf : f ≠ 0) (hh : h ≠ 0)
    (heq : Divisor.divOf (K := K) f = Divisor.divOf (K := K) h) :
    ∃ c : K, c ≠ 0 ∧ f = algebraMap K F c * h := by
  have hmem : f * h⁻¹ ∈ LSpace (0 : Divisor K F) := by
    apply mem_lSpace_iff_ord.mpr
    refine Or.inr (fun P => ?_)
    have hord := congrArg (fun D : Divisor K F => D P) heq
    rw [Divisor.divOf_apply hf, Divisor.divOf_apply hh] at hord
    rw [Finsupp.zero_apply, neg_zero, P.ord_mul hf (inv_ne_zero hh), P.ord_inv, hord]
    omega
  rw [hC] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hfactor : f = algebraMap K F c * h := by
    rw [show algebraMap K F c = f * h⁻¹ from hc, mul_assoc, inv_mul_cancel₀ hh, mul_one]
  refine ⟨c, ?_, hfactor⟩
  intro hc0
  rw [hc0, map_zero, zero_mul] at hfactor
  exact hf hfactor

/-- From the actual cyclic divisors in Claim 4.14, construct the factors in Lemma 4.13.
Every nonconstant factor is minimal. Its orders at the avoided finite set are exactly those
of the corresponding point difference, so distinct values on the distinguished set can be
read off without an additional geometric existence hypothesis. -/
theorem exists_minimal_factors_of_divisor_cycle
    [IsAlgClosed K] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hC : ConstantsAreBase K F) (W : Divisor K F) (g : ℕ)
    (hRR : ∀ E : Divisor K F,
      (ell E : ℤ) - ell (W - E) = Divisor.degree E + 1 - g)
    {n : ℕ} (P Q : Fin n → Place K F) (D : Fin (n + 1) → Divisor K F)
    (hD : ∀ i, 0 ≤ D i ∧ Divisor.degree (D i) = g ∧ ell (D i) = 1)
    (hcycle : D (Fin.last n) = D 0)
    (hstep : ∀ i, (Finsupp.single (P i) 1 - Finsupp.single (Q i) 1 +
      D i.succ - D i.castSucc).IsPrincipal)
    (B : Finset (Place K F)) (havoid : ∀ i, ∀ R ∈ B, D i R = 0)
    {f : F} (hf : f ≠ 0)
    (hdiv : Divisor.divOf (K := K) f =
      ∑ i : Fin n, (Finsupp.single (P i) 1 - Finsupp.single (Q i) 1)) :
    ∃ (c : K) (a : Fin n → F), c ≠ 0 ∧ f = algebraMap K F c * ∏ i, a i ∧
      ∀ i, a i ≠ 0 ∧ a i ∈ LSpace (D i.castSucc + Finsupp.single (Q i) 1) ∧
        (a i ∈ Set.range (algebraMap K F) ∨ (IsMinimal (K := K) (a i) ∧ P i ≠ Q i)) ∧
        ∀ R ∈ B, R.ord (a i) = Finsupp.single (P i) 1 R - Finsupp.single (Q i) 1 R := by
  classical
  choose a ha0 ha using hstep
  have hdiva : ∀ i, Divisor.divOf (K := K) (a i) =
      Finsupp.single (P i) 1 - Finsupp.single (Q i) 1 + D i.succ - D i.castSucc := by
    intro i
    ext R
    rw [Divisor.divOf_apply (ha0 i)]
    exact (ha i R).symm
  have hprod0 : (∏ i, a i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => ha0 i)
  have hproddiv : Divisor.divOf (K := K) (∏ i, a i) = Divisor.divOf (K := K) f := by
    rw [divOf_prod Finset.univ a (fun i _ => ha0 i)]
    simp_rw [hdiva]
    have hsplit :
        (∑ i : Fin n, (Finsupp.single (P i) 1 - Finsupp.single (Q i) 1 +
          D i.succ - D i.castSucc)) =
        (∑ i : Fin n, (Finsupp.single (P i) 1 - Finsupp.single (Q i) 1)) +
          ∑ i : Fin n, (D i.succ - D i.castSucc) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      abel
    rw [hsplit, sum_adjacent_divisor_sub D, hcycle, sub_self, add_zero]
    exact hdiv.symm
  obtain ⟨c, hc0, hcf⟩ := exists_constant_mul_of_divOf_eq hC hf hprod0 hproddiv.symm
  refine ⟨c, a, hc0, hcf, ?_⟩
  intro i
  have hamem : a i ∈ LSpace (D i.castSucc + Finsupp.single (Q i) 1) := by
    apply mem_lSpace_iff_ord.mpr
    refine Or.inr (fun R => ?_)
    have heq := ha i R
    have hnext := (hD i.succ).1 R
    have hsingle : (0 : ℤ) ≤ Finsupp.single (P i) 1 R := by
      rcases eq_or_ne R (P i) with rfl | hRP
      · rw [Finsupp.single_eq_same]
        exact zero_le_one
      · rw [Finsupp.single_eq_of_ne hRP]
    simp only [Finsupp.zero_apply, Finsupp.sub_apply, Finsupp.add_apply] at heq hnext ⊢
    omega
  refine ⟨ha0 i, hamem, ?_, ?_⟩
  · by_cases hconst : a i ∈ Set.range (algebraMap K F)
    · exact Or.inl hconst
    · refine Or.inr ⟨isMinimal_of_mem_degree_genus_add_place hC W g hRR
        (hD i.castSucc).1 (hD i.castSucc).2.1 (hD i.castSucc).2.2
        (Q i) hamem hconst, ?_⟩
      intro hPQ
      have hprincipal : (D i.succ - D i.castSucc).IsPrincipal := by
        refine ⟨a i, ha0 i, fun R => ?_⟩
        simpa only [hPQ, sub_self, zero_add] using ha i R
      have hself : (D i.castSucc - D i.castSucc).IsPrincipal := by
        rw [sub_self]
        exact ⟨1, one_ne_zero, fun R => by rw [Finsupp.zero_apply, R.ord_one]⟩
      have hDD := effective_representative_unique (hD i.castSucc).2.2
        (hD i.castSucc).1 (hD i.succ).1 hself hprincipal
      have hmemzero : a i ∈ LSpace (0 : Divisor K F) := by
        apply mem_lSpace_iff_ord.mpr
        refine Or.inr (fun R => ?_)
        have heq := ha i R
        rw [hPQ, sub_self, zero_add, hDD, sub_self, Finsupp.zero_apply] at heq
        rw [Finsupp.zero_apply, neg_zero, ← heq]
      rw [hC] at hmemzero
      exact hconst hmemzero
  · intro R hRB
    have heq := ha i R
    simp only [Finsupp.sub_apply, Finsupp.add_apply] at heq
    rw [havoid i.succ R hRB, havoid i.castSucc R hRB, add_zero, sub_zero] at heq
    exact heq.symm

/-- Construct the entire divisor cycle and then the minimal factors from a point-difference
decomposition of the principal divisor. All moving divisors are produced internally. -/
theorem exists_minimal_factorization_of_point_differences
    [IsAlgClosed K] [Algebra.EssFiniteType K F]
    (hC : ConstantsAreBase K F) (W : Divisor K F) (g : ℕ)
    (hRR : ∀ E : Divisor K F,
      (ell E : ℤ) - ell (W - E) = Divisor.degree E + 1 - g)
    {n : ℕ} (P Q : Fin n → Place K F)
    (B : Finset (Place K F)) (hB : B.Nonempty)
    (S : Set (Place K F)) (hS : S.Infinite)
    {f : F} (hf : f ≠ 0)
    (hdiv : Divisor.divOf (K := K) f =
      ∑ i : Fin n, (Finsupp.single (P i) 1 - Finsupp.single (Q i) 1)) :
    ∃ (c : K) (a : Fin n → F), c ≠ 0 ∧ f = algebraMap K F c * ∏ i, a i ∧
      ∀ i, a i ≠ 0 ∧
        (a i ∈ Set.range (algebraMap K F) ∨ (IsMinimal (K := K) (a i) ∧ P i ≠ Q i)) ∧
        ∀ R ∈ B, R.ord (a i) = Finsupp.single (P i) 1 R - Finsupp.single (Q i) 1 R := by
  classical
  let V : Fin n → Divisor K F := fun i => Finsupp.single (P i) 1 - Finsupp.single (Q i) 1
  let C : Fin (n + 1) → Divisor K F :=
    fun j => ∑ i : Fin n, if i.val < j.val then V i else 0
  have hCzero : C 0 = 0 := by
    simp only [C, Fin.val_zero, Nat.not_lt_zero, ite_false, Finset.sum_const_zero]
  have hClast : C (Fin.last n) = ∑ i : Fin n, V i := by
    simp only [C, Fin.val_last, Fin.is_lt, ite_true]
  have hCstep : ∀ i : Fin n, C i.succ = C i.castSucc + V i := by
    intro i
    have hterm : ∀ j : Fin n,
        (if j.val < i.val + 1 then V j else 0) =
          (if j.val < i.val then V j else 0) + (if j = i then V i else 0) := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [Nat.lt_succ_self, ite_true, lt_self_iff_false, ite_false, zero_add]
      · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
        by_cases hlt : j.val < i.val
        · rw [ite_eq_left (by omega), ite_eq_left hlt, ite_eq_right hji, add_zero]
        · rw [ite_eq_right (by omega), ite_eq_right hlt, ite_eq_right hji, add_zero]
    change (∑ j : Fin n, if j.val < i.val + 1 then V j else 0) =
      (∑ j : Fin n, if j.val < i.val then V j else 0) + V i
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hCdegree : ∀ j, Divisor.degree (C j) = 0 := by
    intro j
    change Divisor.degree (∑ i : Fin n, if i.val < j.val then V i else 0) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs
    · change Divisor.degree (Finsupp.single (P i) 1 - Finsupp.single (Q i) 1) = 0
      rw [map_sub, Divisor.degree_single, Divisor.degree_single,
        IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed]
      rfl
    · exact map_zero _
  obtain ⟨A, D, hD, hsame, hadj⟩ :=
    exists_simultaneous_effective_representatives W g hRR C hCdegree B hB S hS
  have hcycle : D (Fin.last n) = D 0 := by
    apply hsame
    rw [hCzero, sub_zero, hClast]
    change Divisor.IsPrincipal
      (∑ i : Fin n, (Finsupp.single (P i) (1 : ℤ) - Finsupp.single (Q i) 1))
    rw [← hdiv]
    exact Divisor.divOf_mem_principal hf
  have hstep : ∀ i : Fin n,
      (Finsupp.single (P i) 1 - Finsupp.single (Q i) 1 +
        D i.succ - D i.castSucc).IsPrincipal := by
    intro i
    have h := hadj i.castSucc i.succ
    rw [hCstep i, add_sub_cancel_left] at h
    change (D i.succ - D i.castSucc +
      (Finsupp.single (P i) 1 - Finsupp.single (Q i) 1)).IsPrincipal at h
    convert h using 1
    abel
  obtain ⟨R, _⟩ := hS.nonempty
  have : Nonempty (Place K F) := ⟨R⟩
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) := finiteDimensional_lSpace_zero K F
  obtain ⟨c, a, hc0, hcf, ha⟩ := exists_minimal_factors_of_divisor_cycle hC W g hRR P Q D
    (fun i => ⟨(hD i).1, (hD i).2.1, (hD i).2.2.1⟩) hcycle hstep B
    (fun i => (hD i).2.2.2.1) hf hdiv
  exact ⟨c, a, hc0, hcf, fun i => ⟨(ha i).1, (ha i).2.2.1, (ha i).2.2.2⟩⟩

/-- Write a divisor as a finite list of point differences anchored at one fixed point, with
the degree term kept explicitly. The proof works for negative coefficients as well. -/
theorem exists_anchored_point_differences [IsAlgClosed K] (P₀ : Place K F)
    (D : Divisor K F) :
    ∃ L : List (Place K F × Place K F),
      (L.map (fun a => Finsupp.single a.1 (1 : ℤ) - Finsupp.single a.2 1)).sum =
        D - Divisor.degree D • Finsupp.single P₀ 1 ∧
      ∀ a ∈ L, a.1 = P₀ ∨ a.2 = P₀ := by
  classical
  induction D using Finsupp.induction with
  | zero =>
      exact ⟨[], by simp only [List.map_nil, List.sum_nil, map_zero, zero_smul, sub_zero],
        fun a ha => by cases ha⟩
  | single_add P z D _ _ ih =>
      obtain ⟨L, hLsum, hLanchor⟩ := ih
      have hsingle : Divisor.degree (Finsupp.single P z : Divisor K F) = z := by
        rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one]
      have hstep : ∃ M : List (Place K F × Place K F),
          (M.map (fun a => Finsupp.single a.1 (1 : ℤ) - Finsupp.single a.2 1)).sum =
            Finsupp.single P z - z • Finsupp.single P₀ 1 ∧
          ∀ a ∈ M, a.1 = P₀ ∨ a.2 = P₀ := by
        cases z with
        | ofNat m =>
            refine ⟨List.replicate m (P, P₀), ?_, ?_⟩
            · rw [List.map_replicate, List.sum_replicate, ← natCast_zsmul, smul_sub,
                Finsupp.smul_single_one]
              rfl
            · intro a ha
              have haeq : a = (P, P₀) := (List.mem_replicate.mp ha).2
              exact Or.inr (congrArg Prod.snd haeq)
        | negSucc m =>
            refine ⟨List.replicate (m + 1) (P₀, P), ?_, ?_⟩
            · rw [List.map_replicate, List.sum_replicate, ← natCast_zsmul, smul_sub]
              have hz : (Int.negSucc m : ℤ) = -((m + 1 : ℕ) : ℤ) := by omega
              rw [hz, Finsupp.single_neg, neg_smul]
              simp only [Finsupp.smul_single_one]
              abel
            · intro a ha
              have haeq : a = (P₀, P) := (List.mem_replicate.mp ha).2
              exact Or.inl (congrArg Prod.fst haeq)
      obtain ⟨M, hMsum, hManchor⟩ := hstep
      refine ⟨M ++ L, ?_, ?_⟩
      · rw [List.map_append, List.sum_append, hMsum, hLsum, map_add, hsingle, add_smul]
        abel
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hManchor a ha
        · exact hLanchor a ha

/-- Every actual principal divisor is a finite sum of point differences meeting a chosen
point. This supplies the initial decomposition in Tamagawa's Lemma 4.13. -/
theorem exists_anchored_principal_divisor_decomposition [IsAlgClosed K]
    (P₀ : Place K F) (f : F) :
    ∃ L : List (Place K F × Place K F),
      (L.map (fun a => Finsupp.single a.1 (1 : ℤ) - Finsupp.single a.2 1)).sum =
        Divisor.divOf (K := K) f ∧
      ∀ a ∈ L, a.1 = P₀ ∨ a.2 = P₀ := by
  obtain ⟨L, hL, hanchor⟩ := exists_anchored_point_differences P₀ (Divisor.divOf (K := K) f)
  rw [Divisor.degree_divOf, zero_smul, sub_zero] at hL
  exact ⟨L, hL, hanchor⟩

private theorem exists_nonzero_value_of_ord_zero [IsAlgClosed K]
    (P : Place K F) {x : F} (hx : x ≠ 0) (hord : P.ord x = 0) :
    ∃ c : K, c ≠ 0 ∧ P.HasValue x c := by
  have : Module.Finite K P.ResidueField := IsCurveOver.finiteResidue P
  have : Algebra.IsIntegral K P.ResidueField := Algebra.IsIntegral.of_finite K P.ResidueField
  have hsurj : Function.Surjective (algebraMap K P.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral.surjective
  obtain ⟨hmem, hunit⟩ := P.exists_isUnit_of_ord_eq_zero hx hord
  obtain ⟨c, hc, hc0⟩ := P.exists_hasValue_of_surjective hsurj hmem
  exact ⟨c, hc0 hunit, hc⟩

private theorem zero_and_second_value_of_order_difference [IsAlgClosed K]
    (S : Finset (Place K F)) (hS : 1 < S.card) (P Q : Place K F)
    (hP : P ∈ S) (hPQ : P ≠ Q) {x : F} (hx : x ≠ 0)
    (hord : ∀ R ∈ S, R.ord x = Finsupp.single P (1 : ℤ) R - Finsupp.single Q 1 R) :
    P.HasValue x 0 ∧ ∃ R ∈ S,
      R.ord x < 0 ∨ ∃ c : K, c ≠ 0 ∧ R.HasValue x c := by
  classical
  have hPord : P.ord x = 1 := by
    rw [hord P hP, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hPQ, sub_zero]
  have hzero : P.HasValue x 0 := by
    apply (P.hasValue_iff_mem_and_eq_or_ord_sub_pos x 0).mpr
    refine ⟨P.mem_of_ord_nonneg hx (by omega), Or.inr ?_⟩
    rw [map_zero, sub_zero, hPord]
    exact zero_lt_one
  obtain ⟨R, hRS, hRP⟩ := S.exists_mem_ne hS P
  refine ⟨hzero, R, hRS, ?_⟩
  by_cases hRQ : R = Q
  · subst R
    left
    rw [hord Q hRS, Finsupp.single_eq_of_ne hPQ.symm, Finsupp.single_eq_same]
    omega
  · right
    apply exists_nonzero_value_of_ord_zero R hx
    rw [hord R hRS, Finsupp.single_eq_of_ne hRP, Finsupp.single_eq_of_ne hRQ, sub_self]

/-- Each nonconstant factor furnished by the anchored divisor construction can be oriented
by inversion so that two distinguished points have respectively value zero and either a pole
or a nonzero finite value. This is exactly the input to Möbius normalization. -/
theorem oriented_values_of_anchored_order_difference [IsAlgClosed K]
    (S : Finset (Place K F)) (hS : 1 < S.card) (P Q : Place K F)
    (hPQ : P ≠ Q) (hmeet : P ∈ S ∨ Q ∈ S) {x : F} (hx : x ≠ 0)
    (hord : ∀ R ∈ S, R.ord x = Finsupp.single P (1 : ℤ) R - Finsupp.single Q 1 R) :
    ∃ y : F, (y = x ∨ y = x⁻¹) ∧ ∃ R ∈ S, ∃ T ∈ S,
      R.HasValue y 0 ∧ (T.ord y < 0 ∨ ∃ c : K, c ≠ 0 ∧ T.HasValue y c) := by
  rcases hmeet with hP | hQ
  · obtain ⟨hzero, T, hTS, hT⟩ :=
      zero_and_second_value_of_order_difference S hS P Q hP hPQ hx hord
    exact ⟨x, Or.inl rfl, P, hP, T, hTS, hzero, hT⟩
  · have hinv : ∀ R ∈ S,
        R.ord x⁻¹ = Finsupp.single Q (1 : ℤ) R - Finsupp.single P 1 R := by
      intro R hR
      rw [R.ord_inv, hord R hR]
      omega
    obtain ⟨hzero, T, hTS, hT⟩ :=
      zero_and_second_value_of_order_difference S hS Q P hQ hPQ.symm (inv_ne_zero hx) hinv
    exact ⟨x⁻¹, Or.inr rfl, Q, hQ, T, hTS, hzero, hT⟩

/-- The constructive content of Tamagawa's Lemma 4.13 before Möbius normalization:
every nonzero function is a constant times a finite product of constant or minimal functions,
and each minimal factor or its inverse has two distinct values on the distinguished set.
The infinite set `U` is only the allowed set for choosing auxiliary divisors; it can be the
whole place space. Neither the point decomposition nor the cyclic divisors are inputs. -/
theorem exists_oriented_minimal_factorization
    [IsAlgClosed K] [Algebra.EssFiniteType K F]
    (hC : ConstantsAreBase K F) (W : Divisor K F) (g : ℕ)
    (hRR : ∀ E : Divisor K F,
      (ell E : ℤ) - ell (W - E) = Divisor.degree E + 1 - g)
    (S : Finset (Place K F)) (hS : 1 < S.card)
    (U : Set (Place K F)) (hU : U.Infinite) {f : F} (hf : f ≠ 0) :
    ∃ (n : ℕ) (c : K) (a : Fin n → F), c ≠ 0 ∧ f = algebraMap K F c * ∏ i, a i ∧
      ∀ i, a i ≠ 0 ∧ (a i ∈ Set.range (algebraMap K F) ∨
        (IsMinimal (K := K) (a i) ∧ ∃ y : F, (y = a i ∨ y = (a i)⁻¹) ∧
          ∃ R ∈ S, ∃ T ∈ S, R.HasValue y 0 ∧
            (T.ord y < 0 ∨ ∃ b : K, b ≠ 0 ∧ T.HasValue y b))) := by
  classical
  obtain ⟨P₀, hP₀⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨L, hLsum, hLanchor⟩ := exists_anchored_principal_divisor_decomposition P₀ f
  let P : Fin L.length → Place K F := fun i => (L.get i).1
  let Q : Fin L.length → Place K F := fun i => (L.get i).2
  have hdiv : Divisor.divOf (K := K) f =
      ∑ i : Fin L.length, (Finsupp.single (P i) 1 - Finsupp.single (Q i) 1) := by
    rw [← hLsum]
    have hm : List.ofFn (fun i : Fin L.length =>
        Finsupp.single (P i) (1 : ℤ) - Finsupp.single (Q i) 1) =
        L.map (fun a => Finsupp.single a.1 (1 : ℤ) - Finsupp.single a.2 1) := by
      change List.ofFn ((fun a : Place K F × Place K F =>
        Finsupp.single a.1 (1 : ℤ) - Finsupp.single a.2 1) ∘ L.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    rw [← hm, List.sum_ofFn]
  let B := (S ∪ Finset.univ.image P) ∪ Finset.univ.image Q
  have hSB : S ⊆ B := fun R hR =>
    Finset.mem_union_left _ (Finset.mem_union_left _ hR)
  have hB : B.Nonempty := ⟨P₀, hSB hP₀⟩
  obtain ⟨c, a, hc0, hcf, ha⟩ :=
    exists_minimal_factorization_of_point_differences hC W g hRR P Q B hB U hU hf hdiv
  refine ⟨L.length, c, a, hc0, hcf, ?_⟩
  intro i
  refine ⟨(ha i).1, ?_⟩
  rcases (ha i).2.1 with hconst | ⟨hminimal, hPQ⟩
  · exact Or.inl hconst
  · refine Or.inr ⟨hminimal, ?_⟩
    apply oriented_values_of_anchored_order_difference S hS (P i) (Q i) hPQ ?_ (ha i).1
      (fun R hR => (ha i).2.2 R (hSB hR))
    rcases hLanchor (L.get i) (List.get_mem L i) with hP | hQ
    · left
      change (L.get i).1 ∈ S
      rw [hP]
      exact hP₀
    · right
      change (L.get i).2 ∈ S
      rw [hQ]
      exact hP₀

/-- All elements of minimal rational subfields whose coordinate has zero and infinity at
two points of the distinguished set. This includes constants and zero. -/
def normalizedMinimalSubfieldGenerators (S : Set (Place K F)) : Set F :=
  {y | ∃ x : F, IsMinimal (K := K) x ∧
    (∃ P ∈ S, ∃ Q ∈ S, P.HasValue x 0 ∧ Q.HasValue x⁻¹ 0) ∧ y ∈ K⟮x⟯}

theorem mem_normalizedMinimalSubfieldGenerators_of_oriented
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hC : ConstantsAreBase K F) (S : Set (Place K F)) {a : F}
    (ha : IsMinimal (K := K) a)
    (hvalues : ∃ y : F, (y = a ∨ y = a⁻¹) ∧ ∃ P ∈ S, ∃ Q ∈ S,
      P.HasValue y 0 ∧ (Q.ord y < 0 ∨ ∃ c : K, c ≠ 0 ∧ Q.HasValue y c)) :
    a ∈ normalizedMinimalSubfieldGenerators (K := K) S := by
  obtain ⟨y, hya, P, hPS, Q, hQS, hP, hQ⟩ := hvalues
  have hy : IsMinimal (K := K) y := by
    rcases hya with rfl | rfl
    · exact ha
    · exact ha.inv hC
  have hy0 : y ≠ 0 := by
    intro h
    exact hy.not_constant hC ⟨0, (map_zero _).trans h.symm⟩
  have hnormalize : ∃ z : F, IsMinimal (K := K) z ∧ P.HasValue z 0 ∧
      Q.HasValue z⁻¹ 0 ∧ y ∈ K⟮z⟯ := by
    rcases hQ with hpole | ⟨c, hc0, hc⟩
    · have hinv : 0 < Q.ord y⁻¹ := by rw [Q.ord_inv]; omega
      have hQinv : Q.HasValue y⁻¹ 0 := by
        apply (Q.hasValue_iff_mem_and_eq_or_ord_sub_pos y⁻¹ 0).mpr
        refine ⟨Q.mem_of_ord_nonneg (inv_ne_zero hy0) hinv.le, Or.inr ?_⟩
        simpa only [map_zero, sub_zero] using hinv
      exact ⟨y, hy, hP, hQinv, IntermediateField.mem_adjoin_simple_self K y⟩
    · exact exists_normalized_minimal_of_zero_and_nonzero_value hC hy P Q hP c hc0 hc
  obtain ⟨z, hz, hzP, hzQ, hyz⟩ := hnormalize
  refine ⟨z, hz, ⟨P, hPS, Q, hQS, hzP, hzQ⟩, ?_⟩
  rcases hya with hya | hya
  · rwa [hya] at hyz
  · have := (K⟮z⟯).inv_mem hyz
    simpa only [hya, inv_inv] using this

/-- Tamagawa's Lemma 4.13, in the multiplicative form used for additive reconstruction.
Every function, including zero, is in the multiplicative closure of the normalized minimal
subfields. The divisor movement and minimal-factor decomposition are constructed above. -/
theorem closure_normalizedMinimalSubfieldGenerators_eq_top
    [IsAlgClosed K] [Algebra.EssFiniteType K F]
    (hC : ConstantsAreBase K F) (W : Divisor K F) (g : ℕ)
    (hRR : ∀ E : Divisor K F,
      (ell E : ℤ) - ell (W - E) = Divisor.degree E + 1 - g)
    (S : Finset (Place K F)) (hS : 1 < S.card)
    (U : Set (Place K F)) (hU : U.Infinite) :
    Submonoid.closure (normalizedMinimalSubfieldGenerators (K := K) (S : Set (Place K F))) =
      ⊤ := by
  classical
  obtain ⟨P₀, hP₀⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨PInf, hPInf, hInf0⟩ := S.exists_mem_ne hS P₀
  have haux : (U \ ({P₀, PInf} : Finset (Place K F))).Infinite :=
    hU.sdiff ({P₀, PInf} : Finset (Place K F)).finite_toSet
  obtain ⟨P₁, hP₁⟩ := haux.nonempty
  have h10 : P₁ ≠ P₀ := by
    intro h
    exact hP₁.2 (Finset.mem_insert.mpr (Or.inl h))
  have h1Inf : P₁ ≠ PInf := by
    intro h
    exact hP₁.2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
  obtain ⟨x, hx, hx0, _, hxiInf⟩ := exists_three_point_minimal P₀ P₁ PInf h10.symm hInf0.symm h1Inf
  have hconstants : ∀ c : K, algebraMap K F c ∈
      normalizedMinimalSubfieldGenerators (K := K) (S : Set (Place K F)) := by
    intro c
    exact ⟨x, hx, ⟨P₀, hP₀, PInf, hPInf, hx0, hxiInf⟩, (K⟮x⟯).algebraMap_mem c⟩
  have : Nonempty (Place K F) := ⟨P₀⟩
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) := finiteDimensional_lSpace_zero K F
  apply le_antisymm le_top
  intro f _
  by_cases hf : f = 0
  · subst f
    apply Submonoid.subset_closure
    simpa only [map_zero] using hconstants 0
  · obtain ⟨n, c, a, _, hcf, ha⟩ :=
      exists_oriented_minimal_factorization hC W g hRR S hS U hU hf
    rw [hcf]
    apply (Submonoid.closure _).mul_mem (Submonoid.subset_closure (hconstants c))
    apply (Submonoid.closure _).prod_mem
    intro i _
    apply Submonoid.subset_closure
    rcases (ha i).2 with ⟨b, hb⟩ | ⟨hminimal, hvalues⟩
    · rw [← hb]
      exact hconstants b
    · exact mem_normalizedMinimalSubfieldGenerators_of_oriented hC _ hminimal hvalues

end AnabelianGeometry.FunctionField
