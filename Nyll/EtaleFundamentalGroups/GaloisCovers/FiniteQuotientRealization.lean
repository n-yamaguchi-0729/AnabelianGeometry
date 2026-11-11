/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.FiberQuotient
public import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenNormalUniverse
public import Nyll.EtaleFundamentalGroups.GeometricFiber.EquivariantFiberCoverIso
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic

/-!
# Realization of explicit finite quotients by Galois covers

A continuous homomorphism from an etale fundamental group to a finite
discrete group has open normal kernel.  The Galois-category equivalence
therefore realizes that kernel by a pointed connected finite-etale Galois
cover.  When the homomorphism is surjective, the pointed deck quotient is
canonically isomorphic to the prescribed target group.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u v

variable {X : Scheme.{u}} [ConnectedSpace X]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

/-- A continuous finite discrete representation is realized, at the level
of kernels, by the pointed quotient of an actual connected finite-etale
Galois cover. -/
theorem exists_galoisCover_quotient_ker_eq
    (xi : Spec (.of Omega) ⟶ X)
    (G : Type v) [Finite G] [Group G] [TopologicalSpace G]
    [DiscreteTopology G]
    (phi : π₁ᵉᵗ(xi) →ₜ* G) :
    ∃ (W : FiniteEtale X) (hW : IsGalois W)
      (w : (fiber xi).obj W),
      letI : IsGalois W := hW
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w).ker = phi.ker := by
  let U : OpenNormalSubgroup π₁ᵉᵗ(xi) :=
    ProCGroups.ProC.OpenNormalSubgroup.ker phi
  obtain ⟨W, hW, w, hw⟩ :=
    exists_galois_object_point_stabilizer_eq_any_universe
      (C := FiniteEtale X) (fiber xi) U
  let : IsGalois W := hW
  refine ⟨W, hW, w, ?_⟩
  calc
    (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w).ker = MulAction.stabilizer π₁ᵉᵗ(xi) w :=
      EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_ker
        xi W hW w
    _ = (U : Subgroup π₁ᵉᵗ(xi)) := hw
    _ = phi.ker := rfl

/-- Two surjective group homomorphisms with the same source and kernel have
canonically isomorphic targets. -/
private noncomputable def targetMulEquivOfSurjectiveOfKerEq
    {P A B : Type*} [Group P] [Group A] [Group B]
    (q : P →* A) (phi : P →* B)
    (hq : Function.Surjective q) (hphi : Function.Surjective phi)
    (hker : q.ker = phi.ker) : A ≃* B :=
  (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective phi hphi))

private theorem targetMulEquivOfSurjectiveOfKerEq_comp
    {P A B : Type*} [Group P] [Group A] [Group B]
    (q : P →* A) (phi : P →* B)
    (hq : Function.Surjective q) (hphi : Function.Surjective phi)
    (hker : q.ker = phi.ker) :
    (targetMulEquivOfSurjectiveOfKerEq q phi hq hphi hker).toMonoidHom.comp q = phi := by
  apply MonoidHom.ext
  intro g
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_ofClass,
    Function.comp_apply]
  apply phi.eq_iff.mpr
  rw [← hker]
  apply q.eq_iff.mp
  exact hq.hasRightInverse.choose_spec (q g)

/-- Every continuous surjection from an etale fundamental group to an
explicit finite discrete group is represented by an actual pointed connected
finite-etale Galois cover.  The displayed deck-group equivalence identifies
the pointed-cover quotient with the prescribed homomorphism, not merely its
kernel or its abstract target. -/
theorem exists_galoisCover_quotient_mulEquiv
    (xi : Spec (.of Omega) ⟶ X)
    (G : Type v) [Finite G] [Group G] [TopologicalSpace G]
    [DiscreteTopology G]
    (phi : π₁ᵉᵗ(xi) →ₜ* G) (hphi : Function.Surjective phi) :
    ∃ (W : FiniteEtale X) (hW : IsGalois W)
      (w : (fiber xi).obj W) (e : (Aut W)ᵐᵒᵖ ≃* G),
      letI : IsGalois W := hW
      e.toMonoidHom.comp
          (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
            xi W hW w) = phi.toMonoidHom := by
  obtain ⟨W, hW, w, hker⟩ :=
    exists_galoisCover_quotient_ker_eq xi G phi
  let : IsGalois W := hW
  let q := EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
    xi W hW w
  have hq : Function.Surjective q :=
    EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_surjective
      xi W hW w
  let e : (Aut W)ᵐᵒᵖ ≃* G :=
    targetMulEquivOfSurjectiveOfKerEq q phi.toMonoidHom hq hphi hker
  refine ⟨W, hW, w, e, ?_⟩
  exact targetMulEquivOfSurjectiveOfKerEq_comp
    q phi.toMonoidHom hq hphi hker

/-- Two actual pointed Galois covers with the same subgroup in a common
quotient have canonically matching deck groups. Every deck transformation
has ambient lifts with exactly the same quotient label. -/
theorem exists_deckEquiv_of_common_quotient
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Omega' : Type u} [Field Omega'] [IsSepClosed Omega']
    (xi : Spec (.of Omega) ⟶ X) (yi : Spec (.of Omega') ⟶ Y)
    (W : FiniteEtale X) (hW : IsGalois W) (w : (fiber xi).obj W)
    (V : FiniteEtale Y) (hV : IsGalois V) (v : (fiber yi).obj V)
    {Q : Type*} [Group Q] (H : Subgroup Q) [H.Normal]
    (qX : π₁ᵉᵗ(xi) →* Q) (qY : π₁ᵉᵗ(yi) →* Q)
    (hqX : Function.Surjective qX) (hqY : Function.Surjective qY)
    (hw : MulAction.stabilizer π₁ᵉᵗ(xi) w = H.comap qX)
    (hv : MulAction.stabilizer π₁ᵉᵗ(yi) v = H.comap qY) :
    ∃ θ : Aut W ≃* Aut V, ∀ σ : Aut W,
      ∃ (g : π₁ᵉᵗ(xi)) (h : π₁ᵉᵗ(yi)),
        (fiber xi).map σ.asIso.hom w = g • w ∧
        (fiber yi).map (θ σ).asIso.hom v = h • v ∧ qX g = qY h := by
  let : IsGalois W := hW
  let : IsGalois V := hV
  let qW := EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom xi W hW w
  let qV := EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom yi V hV v
  let φX := (QuotientGroup.mk' H).comp qX
  let φY := (QuotientGroup.mk' H).comp qY
  have hqW : Function.Surjective qW :=
    EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_surjective xi W hW w
  have hqV : Function.Surjective qV :=
    EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_surjective yi V hV v
  have hφX : Function.Surjective φX := (QuotientGroup.mk'_surjective H).comp hqX
  have hφY : Function.Surjective φY := (QuotientGroup.mk'_surjective H).comp hqY
  have hkerW : qW.ker = φX.ker := by
    rw [EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_ker, hw]
    change H.comap qX = ((QuotientGroup.mk' H).comp qX).ker
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hkerV : qV.ker = φY.ker := by
    rw [EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_ker, hv]
    change H.comap qY = ((QuotientGroup.mk' H).comp qY).ker
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  let eW := targetMulEquivOfSurjectiveOfKerEq qW φX hqW hφX hkerW
  let eV := targetMulEquivOfSurjectiveOfKerEq qV φY hqV hφY hkerV
  have heW (g) : eW (qW g) = φX g :=
    DFunLike.congr_fun (targetMulEquivOfSurjectiveOfKerEq_comp qW φX hqW hφX hkerW) g
  have heV (h) : eV (qV h) = φY h :=
    DFunLike.congr_fun (targetMulEquivOfSurjectiveOfKerEq_comp qV φY hqV hφY hkerV) h
  let θop := eW.trans eV.symm
  let θ : Aut W ≃* Aut V := MulEquiv.unop θop
  have hθ (g h) (hgh : qX g = qY h) : θop (qW g) = qV h := by
    apply eV.injective
    change eV (eV.symm (eW (qW g))) = eV (qV h)
    rw [eV.apply_symm_apply, heW, heV]
    exact congrArg (QuotientGroup.mk' H) hgh
  refine ⟨θ, ?_⟩
  intro σ
  obtain ⟨g, hg⟩ := hqW (MulOpposite.op σ)
  obtain ⟨h, hh⟩ := hqY (qX g)
  have hdeck : qV h = MulOpposite.op (θ σ) := by
    rw [← hθ g h hh.symm, hg]
    rfl
  refine ⟨g, h, ?_, ?_, hh.symm⟩
  · have hpoint :=
      EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_evaluation xi W hW w g
    change (fiber xi).map (qW g).unop.asIso.hom w = g • w at hpoint
    rw [hg] at hpoint
    exact hpoint
  · have hpoint :=
      EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_evaluation yi V hV v h
    change (fiber yi).map (qV h).unop.asIso.hom v = h • v at hpoint
    rw [hdeck] at hpoint
    exact hpoint

/-- Matching the actual pointed deck quotients along a scheme morphism
recovers the original source cover as the actual pullback of the target
cover. The isomorphism preserves the given points under the canonical
pullback-fibre comparison. -/
theorem exists_pointedPullbackCoverIso_of_quotientLabels
    {Y : Scheme.{u}} [ConnectedSpace Y]
    (b : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (W : FiniteEtale X) (hW : IsGalois W) (w : (fiber xi).obj W)
    (V : FiniteEtale Y) (hV : IsGalois V) (v : (fiber (xi ≫ b)).obj V)
    (e : (Aut V)ᵐᵒᵖ ≃* (Aut W)ᵐᵒᵖ)
    (hcomp : e.toMonoidHom.comp
      ((EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        (xi ≫ b) V hV v).comp (fundamentalGroupHom b xi).toMonoidHom) =
        EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom xi W hW w) :
    ∃ j : W ≅ (pullback b).obj V,
      pointedPullbackFiberEquiv b xi (xi ≫ b) rfl V ((fiber xi).map j.hom w) = v := by
  let : IsGalois W := hW
  let : IsGalois V := hV
  let qW := EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom xi W hW w
  let qV := EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom (xi ≫ b) V hV v
  let eW := evaluationEquivOfIsGalois (fiber xi) W w
  let eV := evaluationEquivOfIsGalois (fiber (xi ≫ b)) V v
  let d : Aut W ≃* Aut V := MulEquiv.unop e.symm
  let E := eW.symm.trans (d.toEquiv.trans eV)
  have hE (γ : π₁ᵉᵗ(xi)) : E (γ • w) = fundamentalGroupHom b xi γ • v := by
    have hlabel : e.symm (qW γ) = qV (fundamentalGroupHom b xi γ) := by
      apply e.injective
      exact (e.apply_symm_apply (qW γ)).trans (DFunLike.congr_fun hcomp γ).symm
    change eV ((e.symm (qW γ)).unop) = _
    rw [hlabel]
    exact EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_evaluation
      (xi ≫ b) V hV v (fundamentalGroupHom b xi γ)
  let p := pointedPullbackFiberEquiv b xi (xi ≫ b) rfl V
  let EF := E.trans p.symm
  have hp (γ : π₁ᵉᵗ(xi)) (z : (fiber xi).obj ((pullback b).obj V)) :
      p (γ • z) = fundamentalGroupHom b xi γ • p z :=
    pointedPullbackFiberEquiv_smul b xi (xi ≫ b) rfl V γ z
  have hEF (γ : π₁ᵉᵗ(xi)) (z : (fiber xi).obj W) :
      EF (γ • z) = γ • EF z := by
    obtain ⟨δ, rfl⟩ := MulAction.exists_smul_eq π₁ᵉᵗ(xi) w z
    apply p.injective
    change p (p.symm (E (γ • δ • w))) = p (γ • p.symm (E (δ • w)))
    rw [p.apply_symm_apply, ← mul_smul, hE, hp, p.apply_symm_apply, hE,
      map_mul, mul_smul]
  let j := coverIsoOfEquivariantFiberEquiv (fiber xi) EF hEF
  refine ⟨j, ?_⟩
  rw [coverIsoOfEquivariantFiberEquiv_hom_apply]
  change p (p.symm (E w)) = v
  rw [p.apply_symm_apply]
  simpa only [one_smul, map_one] using hE 1

omit [ConnectedSpace X] in
/-- Mapping a deck subgroup through the equivalence in an explicit finite
quotient realization preserves its cardinality. -/
theorem quotientDeckMulEquiv_map_natCard
    {G : Type v} [Group G]
    {W : FiniteEtale X} (e : (Aut W)ᵐᵒᵖ ≃* G)
    (H : Subgroup (Aut W)ᵐᵒᵖ) :
    Nat.card (H.map e.toMonoidHom) = Nat.card H := by
  exact Subgroup.card_map_of_injective e.injective

omit [ConnectedSpace X] in
/-- Coprimality of a deck subgroup is unchanged after transport to an
explicit finite quotient group. -/
theorem quotientDeckMulEquiv_map_coprime_iff
    {G : Type v} [Group G]
    {W : FiniteEtale X} (e : (Aut W)ᵐᵒᵖ ≃* G)
    (H : Subgroup (Aut W)ᵐᵒᵖ) (n : ℕ) :
    Nat.Coprime (Nat.card (H.map e.toMonoidHom)) n ↔
      Nat.Coprime (Nat.card H) n := by
  rw [quotientDeckMulEquiv_map_natCard]

/-- The image of any source subgroup under an explicitly realized finite
quotient is exactly the image of its pointed-cover quotient subgroup under
the deck-group equivalence. -/
theorem quotientDeckMulEquiv_map_quotient_subgroup
    {G : Type v} [Group G]
    (xi : Spec (.of Omega) ⟶ X)
    (W : FiniteEtale X) (hW : IsGalois W)
    (w : (fiber xi).obj W) (e : (Aut W)ᵐᵒᵖ ≃* G)
    (phi : π₁ᵉᵗ(xi) →* G)
    (hcomp : e.toMonoidHom.comp
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w) = phi)
    (K : Subgroup π₁ᵉᵗ(xi)) :
    (K.map
        (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          xi W hW w)).map e.toMonoidHom = K.map phi := by
  rw [Subgroup.map_map, hcomp]

/-- Under an explicit finite-quotient realization, the image of every
source subgroup has the same cardinality in the prescribed target as in the
pointed deck quotient. -/
theorem quotientDeckMulEquiv_quotient_subgroup_natCard
    {G : Type v} [Group G]
    (xi : Spec (.of Omega) ⟶ X)
    (W : FiniteEtale X) (hW : IsGalois W)
    (w : (fiber xi).obj W) (e : (Aut W)ᵐᵒᵖ ≃* G)
    (phi : π₁ᵉᵗ(xi) →* G)
    (hcomp : e.toMonoidHom.comp
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w) = phi)
    (K : Subgroup π₁ᵉᵗ(xi)) :
    Nat.card (K.map phi) =
      Nat.card (K.map
        (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          xi W hW w)) := by
  rw [← quotientDeckMulEquiv_map_quotient_subgroup
    xi W hW w e phi hcomp K]
  exact quotientDeckMulEquiv_map_natCard e
    (K.map
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w))

/-- Hence coprimality of every source-subgroup image is equivalent in the
prescribed finite quotient and in its pointed deck-cover realization. -/
theorem quotientDeckMulEquiv_quotient_subgroup_coprime_iff
    {G : Type v} [Group G]
    (xi : Spec (.of Omega) ⟶ X)
    (W : FiniteEtale X) (hW : IsGalois W)
    (w : (fiber xi).obj W) (e : (Aut W)ᵐᵒᵖ ≃* G)
    (phi : π₁ᵉᵗ(xi) →* G)
    (hcomp : e.toMonoidHom.comp
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w) = phi)
    (K : Subgroup π₁ᵉᵗ(xi)) (n : ℕ) :
    Nat.Coprime (Nat.card (K.map phi)) n ↔
      Nat.Coprime
        (Nat.card (K.map
          (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
            xi W hW w))) n := by
  rw [quotientDeckMulEquiv_quotient_subgroup_natCard
    xi W hW w e phi hcomp K]

end AlgebraicGeometry.FiniteEtale

end
