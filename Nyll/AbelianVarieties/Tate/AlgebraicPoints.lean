/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPointsBaseChange
public import Nyll.AbelianVarieties.Geometry.AbelianSchemeBaseChange
public import Nyll.AbelianVarieties.Basic
public import Nyll.AbelianVarieties.Geometry.Torsion.Degree
public import Nyll.AbelianVarieties.Tate.Basis
public import Nyll.AbelianVarieties.Tate.FullTateModule
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Nyll.EtaleFundamentalGroups.GaloisCovers.Basic
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.FieldTheory.AlgebraicClosure
public import Nyll.AbelianVarieties.Tate.Representation
public import Nyll.AbelianVarieties.Tate.RestrictedComparison
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.SetTheory.Cardinal.Finite
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPoints
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Prime-power Tate bases of algebraic points

The geometric torsion cardinality theorem supplies the hypotheses for the existing
prime-power Tate basis construction. No torsion cardinality or rank is assumed separately.
The comparison with the existing restricted inverse limit also gives compactness
from the actual finite geometric torsion levels, without a characteristic-zero assumption.
The geometric point field may be separably closed; algebraic closure is not required.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry NeronModelInfra

universe u

namespace GoodReductionJacobian.RelativeGroupLaw

section AlgebraicallyClosedPoints

variable {K : Type u} [Field K] [IsAlgClosed K]
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
  (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
  (hA : AbelianSchemePropertyBundle K f) (g : ℕ) [SmoothOfRelativeDimension g f]

include hA

/-- The actual additive point group has the torsion cardinality given by the geometric
multiplication-degree theorem. -/
theorem natCard_algPoints_torsionBy (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc K) (n : ℤ)) = n ^ (2 * g) := by
  rw [AlgPoints.natCard_torsionBy, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  exact natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero K f L hc hA g n hn

/-- The prime-power Tate module of the algebraic point group has a basis of rank twice the
relative dimension, for any prime invertible in the ground field. -/
theorem nonempty_basis_primePowerTateModule (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0) :
    Nonempty (Module.Basis (Fin (2 * g)) ℤ_[p] (TateModule p (L.AlgPoints hc K))) := by
  apply TateModule.nonempty_basis_of_card_torsionBy p (2 * g)
  intro n
  apply L.natCard_algPoints_torsionBy hc hA g (p ^ n)
  rw [Nat.cast_pow]
  exact pow_ne_zero n hp

end AlgebraicallyClosedPoints

section AlgebraicallyClosedGeometricPoints

variable {K Ω : Type u} [Field K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
  (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
  (hA : AbelianSchemePropertyBundle K f) (g : ℕ) [SmoothOfRelativeDimension g f]

include hA

/-- Torsion cardinality for geometric points of an abelian variety over an arbitrary field.
The pullback projection transports the count from the algebraically closed base change. -/
private theorem natCard_geometricPoints_torsionBy_of_isAlgClosed (n : ℕ) (hn : (n : Ω) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc Ω) (n : ℤ)) = n ^ (2 * g) := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let G := L.baseChange ι
  have hG : G.IsCommutative := IsCommutative.baseChange ι hc
  have hB : AbelianSchemePropertyBundle Ω (Limits.pullback.snd f ι) :=
    hA.baseChange_of_field ι
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => SmoothOfRelativeDimension g h) :=
    smoothOfRelativeDimension_isStableUnderBaseChange g
  have : SmoothOfRelativeDimension g (Limits.pullback.snd f ι) :=
    hbc.of_isPullback (IsPullback.of_hasPullback f ι) inferInstance
  let e : G.AlgPoints hG Ω ≃+ L.AlgPoints hc Ω :=
    algPointsBaseChangeEquiv L hc G hG (fun _ _ _ => rfl)
  let et : Submodule.torsionBy ℤ (G.AlgPoints hG Ω) (n : ℤ) ≃
      Submodule.torsionBy ℤ (L.AlgPoints hc Ω) (n : ℤ) :=
    e.toEquiv.subtypeEquiv fun m => by
      simp only [Submodule.mem_torsionBy_iff]
      constructor
      · intro hm
        exact (map_zsmul e (n : ℤ) m).symm.trans ((congrArg e hm).trans e.map_zero)
      · intro hm
        apply e.injective
        exact (map_zsmul e (n : ℤ) m).trans (hm.trans e.map_zero.symm)
  exact (Nat.card_congr et).symm.trans (G.natCard_algPoints_torsionBy hG hB g n hn)

end AlgebraicallyClosedGeometricPoints

section SeparableGeometricPoints

variable {K Ω : Type u} [Field K] [Field Ω] [IsSepClosed Ω] [Algebra K Ω]
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
  (L : RelativeGroupLaw K f) (hc : L.IsCommutative)

private theorem natCard_torsionBy_eq_finrank [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ+) (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc Ω) ((n : ℕ) : ℤ)) =
      (L.schemeKerStr (n : ℕ)).finrank (IsLocalRing.closedPoint K) := by
  let X := L.finiteEtaleTorsion hc d n hn
  let e₁ : Submodule.torsionBy ℤ (L.AlgPoints hc Ω) ((n : ℕ) : ℤ) ≃
      ProCGroups.torsionLevel (L.AlgPoints hc Ω) n :=
    (Equiv.refl (L.AlgPoints hc Ω)).subtypeEquiv fun x => by
      change ((n : ℕ) : ℤ) • x = 0 ↔ (n : ℕ) • x = 0
      rw [natCast_zsmul]
  let e₂ := L.torsionLevelEquivAlgSchemeKerPoints hc Ω n
  let e₃ := schemeHomOverEquivOverHom (Spec.algebraMap K Ω) (L.schemeKerStr (n : ℕ))
  let e₄ := (FiniteEtale.fiberObjEquivHom (Spec.algebraMap K Ω) X).symm
  calc
    Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc Ω) ((n : ℕ) : ℤ)) =
        Nat.card ((FiniteEtale.fiber (Spec.algebraMap K Ω)).obj X) :=
      Nat.card_congr (e₁.trans (e₂.trans (e₃.trans e₄)))
    _ = X.hom.finrank ((Spec.algebraMap K Ω) (IsLocalRing.closedPoint Ω)) :=
      FiniteEtale.natCard_fiber_eq_finrank (Spec.algebraMap K Ω) X
    _ = (L.schemeKerStr (n : ℕ)).finrank (IsLocalRing.closedPoint K) := by
      change (L.schemeKerStr (n : ℕ)).finrank _ = _
      rw [Subsingleton.elim ((Spec.algebraMap K Ω) (IsLocalRing.closedPoint Ω))
        (IsLocalRing.closedPoint K)]

variable (hA : AbelianSchemePropertyBundle K f) (g : ℕ) [SmoothOfRelativeDimension g f]

include hA

/-- Prime-to-characteristic torsion has the geometric cardinality already over a
separably closed extension. The comparison through the actual finite étale kernel
transfers the degree calculation from an algebraic closure. -/
theorem natCard_geometricPoints_torsionBy (n : ℕ) (hn : (n : Ω) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc Ω) (n : ℤ)) = n ^ (2 * g) := by
  have hK : (n : K) ≠ 0 := by
    intro h
    apply hn
    rw [← map_natCast (algebraMap K Ω) n, h, map_zero]
  have hC : (n : AlgebraicClosure K) ≠ 0 := by
    intro h
    apply hK
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [map_natCast, map_zero]
    exact h
  have hpos : 0 < n := Nat.pos_of_ne_zero fun h => hn (by rw [h, Nat.cast_zero])
  have : IsProper f := hA.proper
  calc
    Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc Ω) (n : ℤ)) =
        (L.schemeKerStr n).finrank (IsLocalRing.closedPoint K) :=
      L.natCard_torsionBy_eq_finrank hc g ⟨n, hpos⟩ hK
    _ = Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc (AlgebraicClosure K)) (n : ℤ)) :=
      (L.natCard_torsionBy_eq_finrank hc g ⟨n, hpos⟩ hK).symm
    _ = n ^ (2 * g) :=
      L.natCard_geometricPoints_torsionBy_of_isAlgClosed hc hA g n hC

/-- The geometric prime-power Tate module has rank twice the relative dimension,
without assuming the ground field algebraically closed. -/
theorem nonempty_basis_geometricPrimePowerTateModule
    (p : ℕ) [Fact p.Prime] (hp : (p : Ω) ≠ 0) :
    Nonempty (Module.Basis (Fin (2 * g)) ℤ_[p] (TateModule p (L.AlgPoints hc Ω))) := by
  apply TateModule.nonempty_basis_of_card_torsionBy p (2 * g)
  intro n
  apply L.natCard_geometricPoints_torsionBy hc hA g (p ^ n)
  rw [Nat.cast_pow]
  exact pow_ne_zero n hp

include g in
/-- Each prime-to-characteristic geometric torsion level is finite, as a consequence of
its geometric cardinality, rather than an additional hypothesis. -/
theorem finite_geometricPoints_torsionLevel (n : ℕ+) (hn : (n : Ω) ≠ 0) :
    Finite (ProCGroups.torsionLevel (L.AlgPoints hc Ω) n) := by
  let e : ProCGroups.torsionLevel (L.AlgPoints hc Ω) n ≃
      Submodule.torsionBy ℤ (L.AlgPoints hc Ω) ((n : ℕ) : ℤ) :=
    (Equiv.refl (L.AlgPoints hc Ω)).subtypeEquiv fun x => by
      change (n : ℕ) • x = 0 ↔ ((n : ℕ) : ℤ) • x = 0
      rw [natCast_zsmul]
  apply Nat.finite_of_card_ne_zero
  rw [Nat.card_congr e, L.natCard_geometricPoints_torsionBy hc hA g (n : ℕ) hn]
  exact pow_ne_zero _ (Nat.ne_of_gt n.pos)

include g in
/-- The prime-power Tate module of geometric points is compact for its canonical
inverse-limit topology whenever the prime is invertible in the geometric field. -/
theorem compactSpace_geometricPrimePowerTateModule
    (p : ℕ) [Fact p.Prime] (hp : (p : Ω) ≠ 0) :
    CompactSpace (TateModule p (L.AlgPoints hc Ω)) := by
  let q : ℕ+ := ⟨p, (Fact.out : p.Prime).pos⟩
  have finiteLevels (n : Submonoid.powers q) :
      Finite (ProCGroups.torsionLevel (L.AlgPoints hc Ω) n.1) := by
    apply L.finite_geometricPoints_torsionLevel hc hA g n.1
    obtain ⟨k, hk⟩ := n.property
    rw [← hk]
    change (((p ^ k : ℕ) : Ω)) ≠ 0
    rw [Nat.cast_pow]
    exact pow_ne_zero k hp
  exact (TateModule.restrictedHomeomorph (L.AlgPoints hc Ω) p).symm.compactSpace

include g in
/-- For a geometric abelian-variety point group, triviality on its Tate module is
exactly pointwise triviality on every prime-power torsion subscheme's points. -/
theorem geometricPrimePowerTateRep_eq_one_iff
    (p : ℕ) [Fact p.Prime] (hp : (p : Ω) ≠ 0) (σ : Ω ≃ₐ[K] Ω) :
    TateModule.rep p (L.AlgPoints hc Ω) (Ω ≃ₐ[K] Ω) σ = 1 ↔
      ∀ n : ℕ, ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f,
        L.IsTorsionPoint _ (p ^ n) x →
          Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1 := by
  have hcard (n : ℕ) :
      Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc Ω) ((p ^ n : ℕ) : ℤ)) =
        (p ^ n) ^ (2 * g) := by
    apply L.natCard_geometricPoints_torsionBy hc hA g (p ^ n)
    rw [Nat.cast_pow]
    exact pow_ne_zero n hp
  rw [TateModule.rep_eq_one_iff_forall_torsionBy (2 * g) hcard]
  constructor
  · intro h n x hx
    let m : L.AlgPoints hc Ω := AlgPoints.ofPoint x
    have hm : m ∈ Submodule.torsionBy ℤ (L.AlgPoints hc Ω) ((p ^ n : ℕ) : ℤ) :=
      (AlgPoints.mem_torsionBy_iff (p ^ n) m).mpr hx
    have heq := congrArg (fun y : L.AlgPoints hc Ω => (AlgPoints.toPoint y).1) (h n m hm)
    exact heq
  · intro h n m hm
    apply AlgPoints.toPoint_injective
    apply Subtype.ext
    rw [AlgPoints.toPoint_smul_coe]
    exact h n (AlgPoints.toPoint m) ((AlgPoints.mem_torsionBy_iff (p ^ n) m).mp hm)

end SeparableGeometricPoints

end GoodReductionJacobian.RelativeGroupLaw
