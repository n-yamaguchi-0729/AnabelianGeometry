/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.AbelianVarieties.Basic
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPoints
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.KernelPoints
public import Nyll.SchemeTheory.Affine.FiniteSchemeAlgebra
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.EndDegree
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemeFlatFinite
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFinite
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFiniteEndKerStrNatCardEqEndDegree
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFormallyUnramifiedSchemeNsmulIsUnit
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSurjectiveEndDegreeEqFinrank
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.AbelianVarieties.Isogenies.Degree.Multiplication
public import Nyll.AbelianVarieties.Isogenies.Degree.Polynomial
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Nyll.AbelianVarieties.Geometry.AbelianSchemeBaseChange
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawBaseChangeSchemeNsmulCompFstEqPullbackMap
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSmoothOfRelativeDimension
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFiniteFlatSchemeNsmul
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.LocallyQuasiFiniteDescendsAlongSurjectiveInfFlatInfQuasiCompact
public import Nyll.AbelianVarieties.Geometry.AbelianSchemePropertyBundleFibreStr
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Degrees and cardinalities of torsion kernels

Multiplication degrees determine torsion cardinalities and the finite flat kernel ranks.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.TorsionCardinality


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace Cardinality

theorem locallyOfFinitePresentation_of_field (K : Type u) [Field K] {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] :
    LocallyOfFinitePresentation q := by
  have : IsNoetherianRing (Γ(Spec (CommRingCat.of K), ⊤) : CommRingCat.{u}) :=
    isNoetherianRing_of_ringEquiv K
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have h := (HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFiniteType)
    (f := q) X.affineCover).mp inferInstance
  exact HasRingHomProperty.of_source_openCover (P := @LocallyOfFinitePresentation)
    X.affineCover (fun i => RingHom.FinitePresentation.of_finiteType.mp (h i))

section Etale

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem etale_endKerStr_nsmul (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    [LocallyOfFiniteType f] (n : ℕ) (hn : (n : K) ≠ 0) :
    Etale (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) := by
  exact JacobianVarieties.Picard.Proofs.MultiplicationDegree.P2mDegNIsog.etale_endKerStr_nsmul
    L hc n hn

end Etale

section Points

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem coe_nsmul_eq_comp (L : RelativeGroupLaw K f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ (L.nsmul f n RelativeGroupLaw.idPoint).1 := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id x.1)
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h]
  rfl

theorem isTorsionPoint_iff_schemeHomOverComp_eq (L : RelativeGroupLaw K f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t f) :
    L.IsTorsionPoint t n x ↔
      NeronModelInfra.schemeHomOverComp x (L.nsmul f n RelativeGroupLaw.idPoint) = L.one t := by
  rw [RelativeGroupLaw.isTorsionPoint_def]
  constructor
  · intro h
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, ← coe_nsmul_eq_comp, h]
  · intro h
    apply Subtype.ext
    rw [coe_nsmul_eq_comp, ← NeronModelInfra.schemeHomOverComp_coe, h]

end Points

theorem natCard_isTorsionPoint_eq_pow
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) n x} = n ^ (2 * g) := by
  have : IsProper f := hA.proper
  have : Etale (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) :=
    etale_endKerStr_nsmul L hc n hn
  obtain ⟨-, -, hcard⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
      K f L (L.nsmul f n RelativeGroupLaw.idPoint)
  have hdeg :=
    GoodReductionJacobian.RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero
      K f L hc hA g n hn
  rw [← hdeg, ← hcard]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x =>
    isTorsionPoint_iff_schemeHomOverComp_eq L (𝟙 _) n x))

theorem finite_isTorsionPoint
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : (n : K) ≠ 0) :
    Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) n x} := by
  apply Nat.finite_of_card_ne_zero
  rw [natCard_isTorsionPoint_eq_pow K f L hc hA g n hn]
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (Nat.cast_zero)
  exact pow_ne_zero _ hn0

end Cardinality

theorem
    _root_.GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) n x} = n ^ (2 * g) :=
  Cardinality.natCard_isTorsionPoint_eq_pow K f L hc hA g n hn

end AbelianVarieties.NOSProofs.TorsionCardinality
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.MultiplicationDegree


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : 0 < n) :
    L.endDegree (L.nsmul f n RelativeGroupLaw.idPoint) = n ^ (2 * g) := by
  classical
  let : CommGroup (SchemeHomOver f f) := L.pointCommGroup hc f
  have hid : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) RelativeGroupLaw.idPoint =
        L.mul t (NeronModelInfra.schemeHomOverComp x RelativeGroupLaw.idPoint)
          (NeronModelInfra.schemeHomOverComp y RelativeGroupLaw.idPoint) := by
    intro T t x y
    have h : ∀ z : SchemeHomOver t f,
        NeronModelInfra.schemeHomOverComp z (RelativeGroupLaw.idPoint (f := f)) = z :=
      fun z => Subtype.ext (Category.comp_id _)
    rw [h, h, h]
  have hpow : ∀ m : ℕ,
      L.nsmul f m RelativeGroupLaw.idPoint = (RelativeGroupLaw.idPoint (f := f)) ^ m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [RelativeGroupLaw.nsmul_succ, pow_succ, ih]; rfl
  obtain ⟨p, -, hp⟩ :=
    RelativeGroupLaw.exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle
      K f L hc hA g RelativeGroupLaw.idPoint RelativeGroupLaw.idPoint hid hid
  have hp' : ∀ m : ℕ,
      ((L.endDegree (L.nsmul f (m + 1) RelativeGroupLaw.idPoint) : ℕ) : ℚ) = p.eval (m : ℚ) := by
    intro m
    have := hp (m : ℤ)
    change ((L.endDegree ((RelativeGroupLaw.idPoint (f := f)) ^ (m : ℤ) *
      RelativeGroupLaw.idPoint) : ℕ) : ℚ) = p.eval ((m : ℤ) : ℚ) at this
    rw [zpow_natCast, ← pow_succ, ← hpow] at this
    rw [this]; push_cast; rfl
  let q : Polynomial ℚ := (Polynomial.X + 1) ^ (2 * g)
  have hq : ∀ m : ℕ, q.eval ((m : ℕ) : ℚ) = (((m + 1) ^ (2 * g) : ℕ) : ℚ) := by
    intro m
    simp only [q, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  have hagree : ∀ m : ℕ, ((m + 1 : ℕ) : K) ≠ 0 → p.eval ((m : ℕ) : ℚ) = q.eval ((m : ℕ) : ℚ) := by
    intro m hm
    rw [← hp', hq,
      RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero K f L hc hA g (m + 1) hm]
  have hinf : Set.Infinite {x : ℚ | p.eval x = q.eval x} := by
    by_cases h0 : ringChar K = 0
    · have : CharZero K := by
        have : CharP K (ringChar K) := ringChar.charP K
        rw [h0] at this
        exact CharP.charP_to_charZero K
      refine Set.infinite_of_injective_forall_mem
        (f := fun j : ℕ => (j : ℚ)) Nat.cast_injective ?_
      intro j
      exact hagree j (by exact_mod_cast Nat.succ_ne_zero j)
    · refine Set.infinite_of_injective_forall_mem
        (f := fun j : ℕ => ((ringChar K * j : ℕ) : ℚ)) ?_ ?_
      · intro i j hij
        have hij' : ((ringChar K * i : ℕ) : ℚ) = ((ringChar K * j : ℕ) : ℚ) := hij
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) (by exact_mod_cast hij')
      · intro j
        apply hagree
        have : ((ringChar K * j + 1 : ℕ) : K) = 1 := by
          push_cast; rw [ringChar.Nat.cast_ringChar, zero_mul, zero_add]
        rw [this]; exact one_ne_zero
  have hpq : p = q := Polynomial.eq_of_infinite_eval_eq p q hinf
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  have := hp' m
  rw [hpq, hq] at this
  exact_mod_cast this

end AbelianVarieties.NOSProofs.MultiplicationDegree
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_schemeKerStr_and_finrank_eq_pow_and_finrank_schemeNsmul_eq_pow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.TorsionDegree


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace FiniteRank

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

section Points

variable (L : RelativeGroupLaw K f)

theorem compT_mul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f)
    (β δ : SchemeHomOver f f) :
    z ⊚ (L.mul f β δ) = L.mul t (z ⊚ β) (z ⊚ δ) :=
  L.pointEval_mul z β δ

theorem compT_one {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f) :
    z ⊚ (L.one f) = L.one t :=
  L.pointEval_one z

theorem comp_idPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (x : SchemeHomOver t f) :
    x ⊚ (RelativeGroupLaw.idPoint (f := f)) = x :=
  RelativeGroupLaw.pointEval_idPoint x

theorem isHom_nsmul (hc : L.IsCommutative) (n : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t f) :
    (L.mul t x y) ⊚ (L.nsmul f n RelativeGroupLaw.idPoint) =
      L.mul t (x ⊚ L.nsmul f n RelativeGroupLaw.idPoint)
        (y ⊚ L.nsmul f n RelativeGroupLaw.idPoint) :=
  L.pointEval_nsmul_mul hc n t x y

end Points

theorem preimage_base_singleton_eq_univ (s : ↥(Spec (CommRingCat.of K))) :
    f.base ⁻¹' {s} = Set.univ := by
  have : Subsingleton ↥(Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _

theorem connectedSpace (hA : AbelianSchemePropertyBundle K f) : ConnectedSpace A := by
  have h := hA.connectedFibres (IsLocalRing.closedPoint K)
  have h' : _root_.IsConnected (Set.univ : Set A) := by
    rw [← preimage_base_singleton_eq_univ (f := f) (IsLocalRing.closedPoint K)]
    exact h
  exact connectedSpace_iff_univ.mpr h'

theorem locallyOfFiniteType (hA : AbelianSchemePropertyBundle K f) : LocallyOfFiniteType f := by
  have : Smooth f := hA.smooth
  infer_instance

theorem main [IsAlgClosed K] (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) (g : ℕ) [SmoothOfRelativeDimension g f]
    (n : ℕ) (hn : n ≠ 0) :
    IsFinite (L.schemeKerStr n) ∧
      (L.schemeKerStr n).finrank (IsLocalRing.closedPoint K) = n ^ (2 * g) ∧
      IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n) ∧
      Function.Surjective (L.schemeNsmul n) ∧
      ∀ x : A, (L.schemeNsmul n).finrank x = n ^ (2 * g) := by
  set β : SchemeHomOver f f := L.nsmul f n RelativeGroupLaw.idPoint with hβ
  have hdeg : L.endDegree β = n ^ (2 * g) :=
    GoodReductionJacobian.RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow K f L hc hA g n
      (Nat.pos_of_ne_zero hn)
  have hdeg_ne : L.endDegree β ≠ 0 := by
    rw [hdeg]; exact pow_ne_zero _ hn
  have hker : IsFinite (L.endKerStr β) := by
    by_contra h
    exact hdeg_ne (RelativeGroupLaw.endDegree_of_not_isFinite L β h)
  have hker' : IsFinite (L.schemeKerStr n) := hker
  have hrank : (L.schemeKerStr n).finrank (IsLocalRing.closedPoint K) = n ^ (2 * g) := by
    have h : L.endDegree β = (L.endKerStr β).finrank (IsLocalRing.closedPoint K) :=
      @RelativeGroupLaw.endDegree_of_isFinite K _ A f L β hker
    rw [hdeg] at h
    exact h.symm
  have : IsProper f := hA.proper
  have : IsFinite β.1 :=
    @GoodReductionJacobian.RelativeGroupLaw.isFinite_of_isFinite_endKerStr K _ A f _ L β
      (fun t x y => isHom_nsmul L hc n t x y) hker
  have : Flat β.1 := GoodReductionJacobian.AbelianSchemePropertyBundle.flat_of_isFinite K hA β
  have : LocallyOfFiniteType f := locallyOfFiniteType hA
  have : ConnectedSpace A := connectedSpace hA
  obtain ⟨hsurj, -, hfin⟩ :=
    RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat K f L β
  have hβ1 : β.1 = L.schemeNsmul n := rfl
  refine ⟨hker', hrank, ?_, ?_, ?_, ?_⟩
  · rw [← hβ1]; infer_instance
  · rw [← hβ1]; infer_instance
  · rw [← hβ1]; exact hsurj
  · intro x
    rw [← hβ1, ← hfin x, hdeg]

end FiniteRank

end AbelianVarieties.NOSProofs.TorsionDegree

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem isFinite_schemeKerStr_and_finrank_eq_pow_and_finrank_schemeNsmul_eq_pow
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : n ≠ 0) :
    IsFinite (L.schemeKerStr n) ∧
      (L.schemeKerStr n).finrank (IsLocalRing.closedPoint K) = n ^ (2 * g) ∧
      IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n) ∧
      Function.Surjective (L.schemeNsmul n) ∧
      ∀ x : A, (L.schemeNsmul n).finrank x = n ^ (2 * g) :=
  AbelianVarieties.NOSProofs.TorsionDegree.FiniteRank.main L hc hA g n hn

/-
The relative finite-flat argument below extends the invertible-order FLT argument
by using the all-order geometric-fibre degree theorem above.
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC. Apache-2.0.
Pinned source: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Local extension: Naganori Yamaguchi (assisted by OpenAI Codex), 2026.
-/

open CategoryTheory.Limits

/-- Multiplication after changing the base is the actual pullback of multiplication. -/
theorem isPullback_baseChange_schemeNsmul
    {R R' : Type u} [CommRing R] [CommRing R']
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    IsPullback ((L.baseChange ι).schemeNsmul n) (pullback.fst f ι)
      (pullback.fst f ι) (L.schemeNsmul n) := by
  have h := baseChange_schemeNsmul_comp_fst_and_eq_pullback_map ι L n
  refine IsPullback.of_right (h₁₂ := pullback.snd f ι) (v₁₃ := ι) (h₂₂ := f)
    ?_ h.1 (IsPullback.of_hasPullback f ι).flip
  rw [h.2.1, L.schemeNsmul_over]
  exact (IsPullback.of_hasPullback f ι).flip

/-- For an abelian variety, nonzero multiplication is quasi-finite in every
characteristic. The geometric degree calculation descends from an algebraic closure. -/
theorem locallyQuasiFinite_schemeNsmul_of_ne_zero
    {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) (n : ℕ) (hn : n ≠ 0) :
    LocallyQuasiFinite (L.schemeNsmul n) := by
  let Ω := AlgebraicClosure K
  let ι := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have hAΩ := hA.baseChange_of_field ι
  have : Smooth (baseChangeStr ι f) := hAΩ.smooth
  obtain ⟨g, hg⟩ := (L.baseChange ι).exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
  have : SmoothOfRelativeDimension g (baseChangeStr ι f) := hg
  have : IsFinite ((L.baseChange ι).schemeNsmul n) :=
    (isFinite_schemeKerStr_and_finrank_eq_pow_and_finrank_schemeNsmul_eq_pow
      Ω (baseChangeStr ι f) (L.baseChange ι) (IsCommutative.baseChange ι hc)
      hAΩ g n hn).2.2.1
  have hcover : Flat ι ∧ Surjective ι :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap K Ω))).2
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Flat ι := hcover.1
  have : Surjective ι := hcover.2
  have : MorphismProperty.DescendsAlong
      (@LocallyQuasiFinite : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @LocallyQuasiFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_baseChange_schemeNsmul L ι n)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

/-- Nonzero multiplication on an abelian scheme is finite, including orders
that vanish in a residue field. No Noetherian hypothesis is needed for finiteness. -/
theorem isFinite_schemeNsmul_of_ne_zero
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle R f) (n : ℕ) (hn : n ≠ 0) :
    IsFinite (L.schemeNsmul n) := by
  have : IsProper f := hA.proper
  have : LocallyQuasiFinite (L.schemeNsmul n) := by
    refine locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo f
      (L.schemeNsmul n) (L.schemeNsmul_over n) ?_
    intro s
    rw [← fibre_schemeNsmul_eq_schemeFibreEndo L s n]
    exact locallyQuasiFinite_schemeNsmul_of_ne_zero (L.fibre s)
      (fun t x y => fibre_mul_comm L (fun t x y => hc.mul_comm t x y) s t x y)
      (GoodReductionJacobian.abelianSchemePropertyBundle_fibreStr hA s) n hn
  have : IsProper (L.schemeNsmul n) := by
    have : IsProper (L.schemeNsmul n ≫ f) := by
      rw [L.schemeNsmul_over]
      infer_instance
    exact IsProper.of_comp _ f
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- Nonzero multiplication on a Noetherian abelian scheme is finite flat,
without requiring the order to be invertible on the base. -/
theorem isFinite_and_flat_schemeNsmul_of_ne_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle R f) (n : ℕ) (hn : n ≠ 0) :
    IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n) := by
  have hfin := isFinite_schemeNsmul_of_ne_zero L hc hA n hn
  exact ⟨hfin, flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle L hA n hfin⟩

/-- The actual relative torsion kernel is finite flat for every nonzero order.
In particular this supplies the residue-characteristic power kernels. -/
theorem isFinite_and_flat_schemeKerStr_of_ne_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle R f) (n : ℕ) (hn : n ≠ 0) :
    IsFinite (L.schemeKerStr n) ∧ Flat (L.schemeKerStr n) := by
  have h := isFinite_and_flat_schemeNsmul_of_ne_zero L hc hA n hn
  have : IsFinite (L.schemeNsmul n) := h.1
  have : Flat (L.schemeNsmul n) := h.2
  exact ⟨inferInstance, inferInstance⟩

/-- Field-valued torsion of nonzero order in an abelian scheme is finite,
including residue-characteristic torsion. Finiteness comes from the actual
finite scheme kernel, not from a prime-to-characteristic cardinality formula. -/
theorem finite_torsionBy_algPoints
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle R f)
    (Ω : Type u) [Field Ω] [Algebra R Ω] (n : ℕ) (hn : n ≠ 0) :
    Finite (Submodule.torsionBy ℤ (L.AlgPoints hc Ω) (n : ℤ)) := by
  have : IsFinite (L.schemeNsmul n) := isFinite_schemeNsmul_of_ne_zero L hc hA n hn
  have : IsFinite (L.schemeKerStr n) := inferInstance
  have : Finite (SchemeHomOver (Spec.algebraMap R Ω) (L.schemeKerStr n)) :=
    SchemeTheory.Affine.FiniteScheme.finite_fieldPoints Ω (L.schemeKerStr n)
  let e := (AlgPoints.torsionByEquiv (L := L) (hc := hc) (T := Ω) n).trans
    (L.torsionSubsetEquivSchemeKerPoints (Spec.algebraMap R Ω) n)
  exact Finite.of_injective e e.injective

end GoodReductionJacobian.RelativeGroupLaw
end
