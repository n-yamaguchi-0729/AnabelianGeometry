/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullback
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullbackCocycle
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMultiplicationAlgebraicPoints
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationTranslations
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMonodromy
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitTorsionFiber
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldMonodromyLift
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
public import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterComposition
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
public import Nyll.JacobianVarieties.Kummer.CohomologyPullback
public import Nyll.JacobianVarieties.WeilPairing.Divisorial

/-!
# The actual division cover fixes its multiplication point

A geometric point of the original parameter cover supplies a point of the
actual multiplication fibre through its retained map to the division
pullback. Field automorphisms act on this same point. Thus a stabilizer of
the original covering point has zero multiplication monodromy.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open AlgebraicCurve EtaleFundamentalGroups.Cohomology

namespace JacobianVarieties.Kummer

variable {K : Type u} [Field K] [IsSepClosed K] {C : Scheme.{u}} [IsIntegral C]
  {c : C ⟶ Spec (.of K)} {ε : SchemeHomOver (𝟙 (Spec (.of K))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
  [Smooth D.toBase] [IsProper D.toBase]
  (a : SchemeHomOver c D.toBase) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
  (Y : FiniteEtale C) (i : Y.left ⟶ h.divisionPullback a (n : ℕ))
  (hi : i ≫ h.divisionProjection a (n : ℕ) = Y.hom)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] [Algebra C.functionField Ω]

local notation "G" => h.relativeGroupLaw
local notation "hc" =>
  (h.relativeGroupLaw_isCommutative : RelativeGroupLaw.IsCommutative G)
local notation "η" => Spec.map (CommRingCat.ofHom (algebraMap C.functionField Ω))
local notation "q" => C.fromSpecStalk (genericPoint C)
local notation "W" => RelativeGroupLaw.UnitMultiplication.cover G hc (Subtype.mk n hn)

omit [IsSepClosed K] in
include hi in
/-- The original covering point, followed by the retained division point,
is a point of the original multiplication fibre. -/
def divisionGenericMultiplicationFiberLift
    (z : (FiniteEtale.fiber (η ≫ q)).obj Y) :
    (FiniteEtale.fiber (η ≫ q ≫ a.1)).obj W :=
  (FiniteEtale.fiberObjEquivHom (η ≫ q ≫ a.1) W).symm
    (Over.homMk
      ((FiniteEtale.fiberObjEquivHom (η ≫ q) Y z).left ≫ i ≫
        (h.divisionPoint a (n : ℕ)).1)
      (by
        have hi' : i ≫ pullback.fst a.1 ((G).schemeNsmul (n : ℕ)) = Y.hom := hi
        have hz : (FiniteEtale.fiberObjEquivHom (η ≫ q) Y z).left ≫ Y.hom = η ≫ q :=
          (FiniteEtale.fiberObjEquivHom (η ≫ q) Y z).w
        change ((FiniteEtale.fiberObjEquivHom (η ≫ q) Y z).left ≫ i ≫
          pullback.snd a.1 ((G).schemeNsmul (n : ℕ))) ≫ (G).schemeNsmul (n : ℕ) =
            η ≫ q ≫ a.1
        rw [Category.assoc, Category.assoc, ← pullback.condition,
          ← Category.assoc i, hi', ← Category.assoc]
        exact (congrArg (· ≫ a.1) hz).trans (Category.assoc _ _ _)))

omit [IsSepClosed K] in
/-- The multiplication lift has exactly the original geometric division
point as its underlying scheme morphism. -/
theorem divisionGenericMultiplicationFiberLift_left
    (z : (FiniteEtale.fiber (η ≫ q)).obj Y) :
    (FiniteEtale.fiberObjEquivHom (η ≫ q ≫ a.1) W
      (divisionGenericMultiplicationFiberLift h a n hn Y i hi z)).left =
        (FiniteEtale.fiberObjEquivHom (η ≫ q) Y z).left ≫ i ≫
          (h.divisionPoint a (n : ℕ)).1 := by
  unfold divisionGenericMultiplicationFiberLift
  rw [Equiv.apply_symm_apply]
  rfl

omit [IsSepClosed K] in
/-- The actual field action on the retained covering point induces the
actual field action on its original multiplication lift. -/
theorem divisionGenericMultiplicationFiberLift_field_action
    (σ : Ω ≃ₐ[C.functionField] Ω)
    (z : (FiniteEtale.fiber (η ≫ q)).obj Y) :
    let γ := toAut (FiniteEtale.fiber η) (Ω ≃ₐ[C.functionField] Ω) σ
    let gC := FiniteEtale.fundamentalGroupHom q η γ
    let gD := FiniteEtale.fundamentalGroupHom (q ≫ a.1) η γ
    gD.asIso.hom.app W (divisionGenericMultiplicationFiberLift h a n hn Y i hi z) =
      divisionGenericMultiplicationFiberLift h a n hn Y i hi (gC.asIso.hom.app Y z) := by
  intro γ gC gD
  apply (FiniteEtale.fiberObjEquivHom (η ≫ q ≫ a.1) W).injective
  apply Over.OverMorphism.ext
  rw [divisionGenericMultiplicationFiberLift_left h a n hn Y i hi (gC.asIso.hom.app Y z)]
  have hD := FiniteEtale.fundamentalGroupHom_field_fiberLift
    (q ≫ a.1) W σ (divisionGenericMultiplicationFiberLift h a n hn Y i hi z)
  have hC := FiniteEtale.fundamentalGroupHom_field_fiberLift q Y σ z
  change (FiniteEtale.fiberObjEquivHom (η ≫ q ≫ a.1) W
    (gD.asIso.hom.app W (divisionGenericMultiplicationFiberLift h a n hn Y i hi z))).left = _ at hD
  change (FiniteEtale.fiberObjEquivHom (η ≫ q) Y (gC.asIso.hom.app Y z)).left = _ at hC
  rw [hD, divisionGenericMultiplicationFiberLift_left h a n hn Y i hi z, hC]
  exact (Category.assoc _ _ _).symm

include i hi in
/-- Fixing the original parameter point fixes its actual multiplication
lift, so transport to the origin has zero actual torsion coordinate. -/
theorem divisionGenericMonodromy_eq_zero_of_fixes
    (τ : FiniteEtale.fiber (η ≫ q ≫ a.1) ≅
      FiniteEtale.fiber ((G).one (𝟙 (Spec (.of K)))).1)
    (σ : Ω ≃ₐ[C.functionField] Ω)
    (z : (FiniteEtale.fiber (η ≫ q)).obj Y)
    (hz : (FiniteEtale.fundamentalGroupHom q η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[C.functionField] Ω) σ)).asIso.hom.app Y z = z) :
    RelativeGroupLaw.UnitMultiplication.monodromy G hc ⟨n, hn⟩
      (continuousConjAut τ
        (FiniteEtale.fundamentalGroupHom (q ≫ a.1) η
          (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[C.functionField] Ω) σ))) = 0 := by
  let γ := toAut (FiniteEtale.fiber η) (Ω ≃ₐ[C.functionField] Ω) σ
  let g := FiniteEtale.fundamentalGroupHom (q ≫ a.1) η γ
  let v := divisionGenericMultiplicationFiberLift h a n hn Y i hi z
  have hv : g.asIso.hom.app W v = v :=
    (divisionGenericMultiplicationFiberLift_field_action h a n hn Y i hi σ z).trans
      (congrArg (divisionGenericMultiplicationFiberLift h a n hn Y i hi) hz)
  have hτg : τ.hom.app W (g.asIso.hom.app W v) =
      (continuousConjAut τ g) • τ.hom.app W v := by
    change τ.hom.app W (g.asIso.hom.app W v) =
      τ.hom.app W (g.asIso.hom.app W (τ.inv.app W (τ.hom.app W v)))
    exact (congrArg (fun x => τ.hom.app W (g.asIso.hom.app W x))
      (FintypeCat.hom_inv_id_apply (τ.app W) v)).symm
  have he := congrArg (RelativeGroupLaw.UnitMultiplication.fiberEquivTorsion G hc ⟨n, hn⟩)
    (hτg.symm.trans (congrArg (τ.hom.app W) hv))
  rw [RelativeGroupLaw.UnitMultiplication.fiberEquivTorsion_smul] at he
  exact add_right_cancel (he.trans (zero_add _).symm)

/-- On an original finite overlap, monodromy is the same constant torsion
point as the actual second-minus-first division difference. Both geometric
points are supplied by the original maps from that overlap. -/
theorem divisionGenericMonodromy_eq_of_constant_difference
    (Z : FiniteEtale C) (m₀ m₁ : Z ⟶ Y)
    (τ : FiniteEtale.fiber (η ≫ q ≫ a.1) ≅
      FiniteEtale.fiber ((G).one (𝟙 (Spec (.of K)))).1)
    (σ : Ω ≃ₐ[C.functionField] Ω)
    (z : (FiniteEtale.fiber (η ≫ q)).obj Z)
    (t : ProCGroups.torsionLevel ((G).AlgPoints hc K) n) :
    let s := Z.hom ≫ c
    let x : SchemeHomOver s (h.divisionStructure a (n : ℕ)) :=
      ⟨m₀.left ≫ i, by
        change (m₀.left ≫ i) ≫ (h.divisionProjection a (n : ℕ) ≫ c) = _
        rw [Category.assoc, ← Category.assoc i, hi, ← Category.assoc]
        exact congrArg (· ≫ c) (show m₀.left ≫ Y.hom = Z.hom from m₀.w)⟩
    let y : SchemeHomOver s (h.divisionStructure a (n : ℕ)) :=
      ⟨m₁.left ≫ i, by
        change (m₁.left ≫ i) ≫ (h.divisionProjection a (n : ℕ) ≫ c) = _
        rw [Category.assoc, ← Category.assoc i, hi, ← Category.assoc]
        exact congrArg (· ≫ c) (show m₁.left ≫ Y.hom = Z.hom from m₁.w)⟩
    let v : SchemeHomOver s (𝟙 (Spec (.of K))) := ⟨s, Category.comp_id s⟩
    postComp (RelativeGroupLaw.UnitMultiplication.torsionPointSection G hc ⟨n, hn⟩ t) v =
        h.divisionDifference a (n : ℕ) x y →
      (FiniteEtale.fundamentalGroupHom q η
          (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[C.functionField] Ω) σ)).asIso.hom.app Y
            ((FiniteEtale.fiber (η ≫ q)).map m₀ z) =
          (FiniteEtale.fiber (η ≫ q)).map m₁ z →
        RelativeGroupLaw.UnitMultiplication.monodromy G hc ⟨n, hn⟩
          (continuousConjAut τ
            (FiniteEtale.fundamentalGroupHom (q ≫ a.1) η
              (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[C.functionField] Ω) σ))) = t := by
  intro s x y v hconstant hz
  let z₀ := (FiniteEtale.fiber (η ≫ q)).map m₀ z
  let z₁ := (FiniteEtale.fiber (η ≫ q)).map m₁ z
  let v₀ := divisionGenericMultiplicationFiberLift h a n hn Y i hi z₀
  let v₁ := divisionGenericMultiplicationFiberLift h a n hn Y i hi z₁
  let t₀ := RelativeGroupLaw.UnitMultiplication.torsionPointSection G hc ⟨n, hn⟩ t
  let d := RelativeGroupLaw.UnitMultiplication.torsionDeckTranslation G hc ⟨n, hn⟩ t
  have htranslation : (postComp (h.divisionPoint a (n : ℕ)) x).1 ≫ (G).translate t₀ =
      (postComp (h.divisionPoint a (n : ℕ)) y).1 := by
    let : Group (SchemeHomOver s D.toBase) := (G).pointGroup s
    rw [(G).point_comp_translate s (postComp (h.divisionPoint a (n : ℕ)) x) t₀]
    change (postComp (h.divisionPoint a (n : ℕ)) x * postComp t₀ v).1 = _
    rw [hconstant]
    apply congrArg Subtype.val
    change (postComp (h.divisionPoint a (n : ℕ)) x) *
      ((postComp (h.divisionPoint a (n : ℕ)) y) *
        (postComp (h.divisionPoint a (n : ℕ)) x)⁻¹) =
          postComp (h.divisionPoint a (n : ℕ)) y
    have hcomm : postComp (h.divisionPoint a (n : ℕ)) x *
        postComp (h.divisionPoint a (n : ℕ)) y =
          postComp (h.divisionPoint a (n : ℕ)) y *
            postComp (h.divisionPoint a (n : ℕ)) x :=
      RelativeGroupLaw.IsCommutative.mul_comm hc s _ _
    rw [← mul_assoc, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hm₀ := congrArg (fun r : Over.mk (η ≫ q) ⟶ Y.toComma => r.left)
    (FiniteEtale.fiberObjEquivHom_naturality (η ≫ q) m₀ z).symm
  have hm₁ := congrArg (fun r : Over.mk (η ≫ q) ⟶ Y.toComma => r.left)
    (FiniteEtale.fiberObjEquivHom_naturality (η ≫ q) m₁ z).symm
  have hd := congrArg (fun r : Over.mk (η ≫ q ≫ a.1) ⟶ (W).toComma => r.left)
    (FiniteEtale.fiberObjEquivHom_naturality (η ≫ q ≫ a.1) d.asIso.hom v₀).symm
  change (FiniteEtale.fiberObjEquivHom (η ≫ q) Y z₀).left =
    (FiniteEtale.fiberObjEquivHom (η ≫ q) Z z).left ≫ m₀.left at hm₀
  change (FiniteEtale.fiberObjEquivHom (η ≫ q) Y z₁).left =
    (FiniteEtale.fiberObjEquivHom (η ≫ q) Z z).left ≫ m₁.left at hm₁
  change (FiniteEtale.fiberObjEquivHom (η ≫ q ≫ a.1) W
    ((FiniteEtale.fiber (η ≫ q ≫ a.1)).map d.asIso.hom v₀)).left =
      (FiniteEtale.fiberObjEquivHom (η ≫ q ≫ a.1) W v₀).left ≫ (G).translate t₀ at hd
  have hmap : v₁ = (FiniteEtale.fiber (η ≫ q ≫ a.1)).map d.asIso.hom v₀ := by
    apply (FiniteEtale.fiberObjEquivHom (η ≫ q ≫ a.1) W).injective
    apply Over.OverMorphism.ext
    rw [hd, divisionGenericMultiplicationFiberLift_left h a n hn Y i hi z₁,
      divisionGenericMultiplicationFiberLift_left h a n hn Y i hi z₀, hm₀, hm₁]
    let p := (FiniteEtale.fiberObjEquivHom (η ≫ q) Z z).left
    have ht : (m₀.left ≫ i ≫ (h.divisionPoint a (n : ℕ)).1) ≫ (G).translate t₀ =
        m₁.left ≫ i ≫ (h.divisionPoint a (n : ℕ)).1 := by
      calc
        _ = ((m₀.left ≫ i) ≫ (h.divisionPoint a (n : ℕ)).1) ≫ (G).translate t₀ :=
          congrArg (· ≫ (G).translate t₀) (Category.assoc _ _ _).symm
        _ = (m₁.left ≫ i) ≫ (h.divisionPoint a (n : ℕ)).1 := htranslation
        _ = _ := Category.assoc _ _ _
    calc
      p ≫ m₁.left ≫ i ≫ (h.divisionPoint a (n : ℕ)).1 =
          p ≫ ((m₀.left ≫ i ≫ (h.divisionPoint a (n : ℕ)).1) ≫ (G).translate t₀) :=
        congrArg (p ≫ ·) ht.symm
      _ = (p ≫ m₀.left ≫ i ≫ (h.divisionPoint a (n : ℕ)).1) ≫ (G).translate t₀ :=
        (Category.assoc _ _ _).symm
  let γ := toAut (FiniteEtale.fiber η) (Ω ≃ₐ[C.functionField] Ω) σ
  let g := FiniteEtale.fundamentalGroupHom (q ≫ a.1) η γ
  have hv : g.asIso.hom.app W v₀ = (FiniteEtale.fiber (η ≫ q ≫ a.1)).map d.asIso.hom v₀ :=
    (divisionGenericMultiplicationFiberLift_field_action h a n hn Y i hi σ z₀).trans
      ((congrArg (divisionGenericMultiplicationFiberLift h a n hn Y i hi) hz).trans hmap)
  have hτg : τ.hom.app W (g.asIso.hom.app W v₀) =
      (continuousConjAut τ g) • τ.hom.app W v₀ := by
    change τ.hom.app W (g.asIso.hom.app W v₀) =
      τ.hom.app W (g.asIso.hom.app W (τ.inv.app W (τ.hom.app W v₀)))
    exact (congrArg (fun r => τ.hom.app W (g.asIso.hom.app W r))
      (FintypeCat.hom_inv_id_apply (τ.app W) v₀)).symm
  have hτd := ConcreteCategory.congr_hom (τ.hom.naturality d.asIso.hom) v₀
  simp only [ConcreteCategory.comp_apply] at hτd
  have he := congrArg (RelativeGroupLaw.UnitMultiplication.fiberEquivTorsion G hc ⟨n, hn⟩)
    (hτg.symm.trans ((congrArg (τ.hom.app W) hv).trans hτd))
  rw [RelativeGroupLaw.UnitMultiplication.fiberEquivTorsion_smul G hc ⟨n, hn⟩
      (continuousConjAut τ g) (τ.hom.app W v₀),
    RelativeGroupLaw.UnitMultiplication.fiberEquiv_map_torsionDeckTranslation G hc ⟨n, hn⟩
      t (τ.hom.app W v₀)] at he
  exact add_right_cancel (he.trans (add_comm _ _))

include i hi in
/-- The character of the actual Abel--Jacobi pullback of a constructed
Weil class kills the stabilizer of every point of the original division
cover. The supplied character formula is the defining formula of the
classes in `exists_jacobian_weil_cohomology`. -/
theorem divisionWeilPullbackCharacter_eq_one_of_fixes
    [IsNormalIntegral C] [Normal C.functionField Ω]
    [GeometricallyConnected D.toBase]
    {F : Type u} [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (τn : Pic0.torsion K F (n : ℕ) ≃+
      ProCGroups.torsionLevel ((G).AlgPoints hc K) n)
    (w : DivisorialWeilPairingData K F (n : ℕ)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    let : ConnectedSpace D.P :=
      GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
    ∀ ν : Pic0.torsion K F (n : ℕ) →+
        Sheaf.H.{u} ((constantSheaf D.P.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1,
      (∀ (x : Pic0.torsion K F (n : ℕ))
        (g : π₁ᵉᵗ(((G).one (𝟙 (Spec (.of K)))).1)),
        ((finiteH1CharacterEquiv A ((G).one (𝟙 (Spec (.of K)))).1 (ν x)).toMul g :
          rootsOfUnity (n : ℕ) K).val.val =
            w.pair x (τn.symm
              (RelativeGroupLaw.UnitMultiplication.monodromy G hc ⟨n, hn⟩ g))) →
      ∀ (t : Pic0.torsion K F (n : ℕ))
        (z : (FiniteEtale.fiber (η ≫ q)).obj Y)
        (g : π₁ᵉᵗ(η ≫ q)),
        g.asIso.hom.app Y z = z →
          h1Character A (η ≫ q) (constantCohomologyPullback a.1 A 1 (ν t)) g = 1 := by
  intro htop hdiscrete A hAtop hAdiscrete hconnected ν hν t z g hg
  classical
  obtain ⟨σ, rfl⟩ := FiniteEtale.genericFieldAction_surjective C Ω g
  let γ := toAut (FiniteEtale.fiber η) (Ω ≃ₐ[C.functionField] Ω) σ
  let τ := Classical.choice
    (FiniteEtale.nonempty_fiber_iso (η ≫ q ≫ a.1) ((G).one (𝟙 (Spec (.of K)))).1)
  have hzero := divisionGenericMonodromy_eq_zero_of_fixes h a n hn Y i hi τ σ z hg
  have hchain := h1Character_pullback_fundamentalGroupHom_conj
    q a.1 η ((G).one (𝟙 (Spec (.of K)))).1 τ A (ν t) γ
  have hw := hν t
    (continuousConjAut τ (FiniteEtale.fundamentalGroupHom (q ≫ a.1) η γ))
  rw [hzero, map_zero, w.pair_zero_right] at hw
  apply Subtype.ext
  apply Units.ext
  exact (congrArg (fun ζ : rootsOfUnity (n : ℕ) K => ζ.val.val) hchain).trans hw

end JacobianVarieties.Kummer
