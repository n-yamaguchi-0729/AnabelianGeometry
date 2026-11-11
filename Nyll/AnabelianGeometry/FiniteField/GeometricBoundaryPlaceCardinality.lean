/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.GenusZeroConstantModel
public import Nyll.EtaleFundamentalGroups.Inertia.GeometricBoundaryPlaces
public import Nyll.SchemeTheory.LocalGeometry.RationalSectionCenters
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.SeparableClosure
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.CoefficientPullback
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# The original geometric boundary count in the actual geometric field

The prescribed constant closure and the constant subfield of the actual
ambient closure are compared over the original finite field. Each original
geometric boundary point then gives a rational section of the literal
constant base change. Sections with the same center agree, so these centers
are distinct before passing to the proved original point-place dictionary.

Consequently the geometric boundary count in the original theorem supplies
the boundary cardinality required by additive reconstruction on the actual
geometric constant compositum. No rationality of the original closed
boundary points is imposed.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open FunctionField FunctionField.RayClass EtaleFundamentalGroups.Inertia
open TopologicalSpace AlgebraicGeometry.SmoothProperCurve

namespace AnabelianGeometry.FiniteField

/-- The original geometric boundary is exactly the place boundary on the
literal geometric base change. Every closed point over the algebraically
closed coefficient field supplies its unique rational section, so the
comparison preserves the original geometric morphisms in both directions. -/
def geometricBoundaryPointEquiv_baseChangeBoundaryPlaces
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    {X U : Scheme.{u}} (c : X ⟶ Spec (.of k)) [GeometricallyIntegral c]
    [IsProper c] [SmoothOfRelativeDimension 1 c] (j : U ⟶ X) :
    let Y := pullback (Spec.algebraMap k κ) c
    let d := pullback.fst (Spec.algebraMap k κ) c
    let _ : IsIntegral Y :=
      GeometricallyIntegral.geometrically_isIntegral (f := c) (Spec.algebraMap k κ)
        (pullback.snd (Spec.algebraMap k κ) c) d
        (CategoryTheory.IsPullback.of_hasPullback (Spec.algebraMap k κ) c).flip
    let _ : Algebra κ Y.functionField := (baseToFunctionField d).toAlgebra
    let M := CurveModel.ofSmoothProperCurve d
    GeometricBoundaryPoint k κ c j ≃
      M.openBoundaryPlaces
        (EtaleFundamentalGroups.coefficientModelMap (Spec.algebraMap k κ) c j) := by
  intro Y d hIntegral alg M
  let b := Spec.algebraMap k κ
  let pr := pullback.snd b c
  let v := EtaleFundamentalGroups.coefficientModelMap b c j
  let P := NeronModelInfra.SchemeHomOver b c
  let Q := NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of κ))) d
  let e : P ≃ Q :=
    { toFun := fun p =>
        ⟨pullback.lift (𝟙 _) p.val ((Category.id_comp b).trans p.property.symm),
          pullback.lift_fst _ _ _⟩
      invFun := fun q => ⟨q.val ≫ pr, by
        change (q.val ≫ pullback.snd b c) ≫ c = b
        rw [Category.assoc, ← pullback.condition, ← Category.assoc,
          q.property, Category.id_comp]⟩
      left_inv := fun p => Subtype.ext (pullback.lift_snd _ _ _)
      right_inv := fun q => by
        apply Subtype.ext
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
          exact q.property.symm
        · exact pullback.lift_snd _ _ _ }
  let eP : P ≃ closedPoints Y := e.trans (pointEquivClosedPoint d)
  let eV : P ≃ Place κ Y.functionField := eP.trans M.placeEquiv
  have hrange : Set.range v = pr ⁻¹' Set.range j := by
    let sq := EtaleFundamentalGroups.coefficientBaseChange_isPullback b c j
    have hv : sq.isoPullback.hom ≫ pullback.fst pr j = v :=
      sq.isoPullback_hom_fst
    rw [← hv]
    change Set.range ((pullback.fst pr j) ∘ sq.isoPullback.hom) = _
    have hsurj : Function.Surjective sq.isoPullback.hom :=
      sq.isoPullback.hom.homeomorph.surjective
    rw [Set.range_comp, Set.range_eq_univ.mpr hsurj,
      Set.image_univ, Scheme.Pullback.range_fst]
  refine eV.subtypeEquiv ?_
  intro p
  change p.val (IsLocalRing.closedPoint κ) ∉ Set.range j ↔
    (M.placeEquiv.symm (M.placeEquiv (eP p))).val ∉ Set.range v
  have hpoint : (M.placeEquiv.symm (M.placeEquiv (eP p))).val = (eP p).val :=
    congrArg Subtype.val (M.placeEquiv.symm_apply_apply (eP p))
  rw [hpoint, hrange]
  have hcenter : pr (eP p).val = p.val (IsLocalRing.closedPoint κ) := by
    change ((e p).val ≫ pullback.snd b c) (IsLocalRing.closedPoint κ) = _
    exact congrArg (fun f : Spec (.of κ) ⟶ X => f (IsLocalRing.closedPoint κ))
      (pullback.lift_snd (𝟙 _) p.val ((Category.id_comp b).trans p.property.symm))
  change _ ↔ pr (eP p).val ∉ Set.range j
  rw [hcenter]

variable (k κ : Type u) [Field k] [Finite k] [Field κ]
  [Algebra k κ] [IsSepClosure k κ]
  {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (c : X ⟶ Spec (.of k)) [GeometricallyIntegral c]
  [IsProper c] [SmoothOfRelativeDimension 1 c]
  (j : U ⟶ X) [IsOpenImmersion j]

variable (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
  [Algebra k Ω] [IsSepClosed Ω]

local notation "F" => U.functionField
local notation "C" => separableClosure k Ω
local notation "G" => geometricConstantExtension k F Ω
local notation "Y" => (pullback c (specMap k C) : Scheme)
local notation "pr" => pullback.fst c (specMap k C)
local notation "cC" => pullback.snd c (specMap k C)
local notation "B" => GeometricBoundaryPoint k κ c j

attribute [local instance]
  EtaleFundamentalGroups.Inertia.geometricBoundaryConstants
  EtaleFundamentalGroups.Inertia.geometricBoundaryConstantTower

local notation "S" => Set.ofPred (fun W : Place C G =>
  openSourceBoundaryModulus c j (algebraicConstantPlaceRestrict (K := F) C F W) = 1)

/-- Every original geometric boundary point embeds into the actual
geometric-place boundary. The construction retains its original center
after projection from the literal constant base change. -/
theorem nonempty_geometricBoundaryPoint_embedding_places :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [IsScalarTower k U.functionField Ω], Nonempty (B ↪ S) := by
  intro baseAlgebra hTower
  let ε : κ ≃ₐ[k] C := IsSepClosure.equiv k κ C
  let t : Spec (.of C) ≅ Spec (.of κ) :=
    Scheme.Spec.mapIso ε.toRingEquiv.toCommRingCatIso.op
  have ht : t.hom ≫ Spec.algebraMap k κ = specMap k C := by
    change Spec.map (CommRingCat.ofHom ε.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k κ)) =
      Spec.map (CommRingCat.ofHom (algebraMap k C))
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact ε.commutes x
  let q (b : B) : Spec (.of C) ⟶ X := t.hom ≫ b.val.val
  have hq (b : B) : q b ≫ c = specMap k C := by
    change (t.hom ≫ b.val.val) ≫ c = _
    rw [Category.assoc, b.val.property]
    exact ht
  let s (b : B) : Spec (.of C) ⟶ Y :=
    pullback.lift (q b) (𝟙 (Spec (.of C)))
      ((hq b).trans (Category.id_comp (specMap k C)).symm)
  have hs (b : B) : s b ≫ cC = 𝟙 _ := pullback.lift_snd _ _ _
  have hclosed (b : B) : IsClosed ({s b (IsLocalRing.closedPoint C)} : Set Y) := by
    have : IsClosedImmersion (s b) := isClosedImmersion_of_comp_eq_id cC (s b) (hs b)
    have hrange : Set.range (s b) = {s b (IsLocalRing.closedPoint C)} :=
      Set.range_eq_singleton_iff.mpr (fun z => congrArg (s b) (Subsingleton.elim _ _))
    rw [← hrange]
    exact (s b).isClosedEmbedding.isClosed_range
  let z (b : B) : closedPoints Y :=
    ⟨s b (IsLocalRing.closedPoint C), mem_closedPoints_iff.mpr (hclosed b)⟩
  have hz : Function.Injective z := by
    intro b b' hbb'
    have hsections : s b = s b' :=
      Scheme.rationalSections_eq_of_center_eq cC (s b) (s b') (hs b) (hs b')
        (congrArg Subtype.val hbb')
    have hqeq : q b = q b' := by
      have h := congrArg (fun f : Spec (.of C) ⟶ Y => f ≫ pr) hsections
      simpa only [s, pullback.lift_fst] using h
    apply Subtype.ext
    apply Subtype.ext
    exact (cancel_epi t.hom).mp hqeq
  have hcenter (b : B) : pr (z b).val = b.val.val (IsLocalRing.closedPoint κ) := by
    change (s b ≫ pr) (IsLocalRing.closedPoint C) = _
    rw [show s b ≫ pr = q b from pullback.lift_fst _ _ _]
    change b.val.val (t.hom (IsLocalRing.closedPoint C)) = _
    exact congrArg b.val.val (Subsingleton.elim _ _)
  obtain ⟨e, he⟩ := exists_openSourceGeometricBoundaryPlaceEquiv c j Ω
  have hboundary (b : B) : e (z b) ∈ S := by
    apply (he (z b)).mpr
    rw [Scheme.Pullback.range_snd]
    change pr (z b).val ∉ Set.range j
    rw [hcenter]
    exact b.property
  exact ⟨⟨fun b => ⟨e (z b), hboundary b⟩,
    fun b b' h => hz (e.injective (congrArg Subtype.val h))⟩⟩

/-- The original geometric boundary hypothesis gives precisely the
cardinality hypothesis of Tamagawa reconstruction on the original
geometric constant compositum. -/
theorem geometricBoundaryPlace_encard_ge_three
    (hcard : 3 ≤ Nat.card B) :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [IsScalarTower k U.functionField Ω], 3 ≤ (S).encard := by
  intro baseAlgebra hTower
  have hnonzero : Nat.card B ≠ 0 :=
    (lt_of_lt_of_le (by decide : 0 < 3) hcard).ne'
  have : Finite B := Nat.finite_of_card_ne_zero hnonzero
  let : Fintype B := Fintype.ofFinite B
  obtain ⟨e⟩ := nonempty_geometricBoundaryPoint_embedding_places k κ c j Ω
  have hle := ENat.card_le_card_of_injective e.injective
  rw [ENat.card_eq_coe_fintype_card (α := B), Fintype.card_eq_nat_card] at hle
  have hthree : (3 : ℕ∞) ≤ (Nat.card B : ℕ∞) := by exact_mod_cast hcard
  exact hthree.trans hle

end AnabelianGeometry.FiniteField
