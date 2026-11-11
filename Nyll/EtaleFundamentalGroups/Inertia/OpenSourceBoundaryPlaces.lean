/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.ClosedPointSourceRayInertia
public import Nyll.AlgebraicCurves.Models.Charts.FiniteComplIsOpen
public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basic
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RayArtinRamification
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RayArtinSeparation
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# The actual finite boundary in the original open function field

The original open immersion gives a coefficient square on the actual
stalks. Thus its original closed points give the same supplied-field
places as their images in the compactification. The proper point-place
correspondence supplies every remaining place, and the geometric finite
complement supplies the finite reduced boundary modulus.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve SchemeTheory LocalClassFieldTheory
open TopologicalSpace

namespace EtaleFundamentalGroups.Inertia

attribute [local instance]
  Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicGeometry.FiniteEtale.genericPoint_isDominant

local instance integralOpenDominant
    {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j] : IsDominant j :=
  ⟨j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j⟩

local instance smoothOpenCurve
    {k : Type u} [Field k] {X U : Scheme.{u}}
    (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
    (j : U ⟶ X) [IsOpenImmersion j] : SmoothOfRelativeDimension 1 (j ≫ c) :=
  inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (j ≫ c))

/-- For the original canonical generic source, the supplied generic-stalk
isomorphism is literally the identity field isomorphism. -/
theorem genericFieldSourceRingEquiv_fromSpecStalk
    (X : Scheme.{u}) [IsIntegral X] :
    genericFieldSourceRingEquiv (X.fromSpecStalk (genericPoint X)) =
      RingEquiv.refl X.functionField := by
  have hcoeff :
      CommRingCat.ofHom
        (genericFieldSourceRingEquiv (X.fromSpecStalk (genericPoint X))).toRingHom =
      𝟙 X.functionField := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    have hsource :=
      genericFieldSourceIso_hom_fromSpecStalk (X.fromSpecStalk (genericPoint X))
    have hid : Spec.map (𝟙 X.functionField) ≫ X.fromSpecStalk (genericPoint X) =
        X.fromSpecStalk (genericPoint X) :=
      (congrArg (fun q : Spec X.functionField ⟶ Spec X.functionField =>
        q ≫ X.fromSpecStalk (genericPoint X)) (Spec.map_id X.functionField)).trans
          (Category.id_comp (X.fromSpecStalk (genericPoint X)))
    exact hsource.trans hid.symm
  apply RingEquiv.ext
  intro a
  exact congrArg (fun f : X.functionField ⟶ X.functionField => f.hom a) hcoeff

section StalkNaturality

variable {F : Type u} [Field F] {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j]
  (p : Spec (.of F) ⟶ U) [IsDominant p] [IsPreimmersion p]

/-- The actual supplied-source coefficient maps commute with the
original open-immersion stalk map. Both spectrum maps factor the same
original generic source, so monicity gives the coefficient equality. -/
theorem genericFieldSourceStalkMap_open (u : U) :
    let : Algebra (X.presheaf.stalk (j u)) F := genericFieldSourceStalkAlgebra (p ≫ j) (j u)
    let : Algebra (U.presheaf.stalk u) F := genericFieldSourceStalkAlgebra p u
    (algebraMap (U.presheaf.stalk u) F).comp (j.stalkMap u).hom =
      algebraMap (X.presheaf.stalk (j u)) F := by
  intro instXF instUF
  have hcoeff :
      CommRingCat.ofHom
        ((algebraMap (U.presheaf.stalk u) F).comp (j.stalkMap u).hom) =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk (j u)) F) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (j u))).mp
    change Spec.map (j.stalkMap u ≫
        CommRingCat.ofHom (algebraMap (U.presheaf.stalk u) F)) ≫
        X.fromSpecStalk (j u) = _
    let g : Spec (.of F) ⟶ Spec (U.presheaf.stalk u) :=
      Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk u) F))
    have hstalk : Spec.map (j.stalkMap u) ≫ X.fromSpecStalk (j u) =
        U.fromSpecStalk u ≫ j := Scheme.SpecMap_stalkMap_fromSpecStalk j
    have hU : g ≫ U.fromSpecStalk u = p := genericFieldSourceStalkMap_fromSpecStalk p u
    have hX : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (j u)) F)) ≫
        X.fromSpecStalk (j u) = p ≫ j :=
      genericFieldSourceStalkMap_fromSpecStalk (p ≫ j) (j u)
    exact (congrArg (fun q : Spec (.of F) ⟶ Spec (X.presheaf.stalk (j u)) =>
      q ≫ X.fromSpecStalk (j u))
        (Spec.map_comp (j.stalkMap u)
          (CommRingCat.ofHom (algebraMap (U.presheaf.stalk u) F)))).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun q : Spec (U.presheaf.stalk u) ⟶ X => g ≫ q) hstalk).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q : Spec (.of F) ⟶ U => q ≫ j) hU).trans hX.symm))))
  exact congrArg (fun q : X.presheaf.stalk (j u) ⟶ CommRingCat.of F => q.hom) hcoeff

/-- The two original local-ring images agree in the same supplied field. -/
theorem genericFieldSourceStalk_range_open (u : U) :
    let : Algebra (X.presheaf.stalk (j u)) F := genericFieldSourceStalkAlgebra (p ≫ j) (j u)
    let : Algebra (U.presheaf.stalk u) F := genericFieldSourceStalkAlgebra p u
    (algebraMap (X.presheaf.stalk (j u)) F).range =
      (algebraMap (U.presheaf.stalk u) F).range := by
  intro instXF instUF
  have : IsIso (j.stalkMap u) :=
    ((IsOpenImmersion.iff_isIso_stalkMap (f := j)).mp inferInstance).2 u
  have hsurj : Function.Surjective (j.stalkMap u).hom :=
    (ConcreteCategory.bijective_of_isIso (j.stalkMap u)).surjective
  have hcoeff := genericFieldSourceStalkMap_open j p u
  apply Subring.ext
  intro z
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(j.stalkMap u).hom a, (DFunLike.congr_fun hcoeff a).trans ha⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := hsurj b
    exact ⟨a, (DFunLike.congr_fun hcoeff a).symm.trans hb⟩

end StalkNaturality

section OpenPoints

variable {k : Type u} [Field k] {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The original open immersion sends a closed point of the smooth curve
to a closed point of the ambient smooth curve. A generic image would
make its actual DVR stalk a field through the original stalk isomorphism. -/
def openClosedPoint (u : closedPoints U) : closedPoints X := by
  have hne : j u.val ≠ genericPoint X := by
    intro h
    have : IsDiscreteValuationRing (U.presheaf.stalk u.val) :=
      SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed
        (j ≫ c) u.val (mem_closedPoints_iff.mp u.property)
    have : IsIso (j.stalkMap u.val) :=
      ((IsOpenImmersion.iff_isIso_stalkMap (f := j)).mp inferInstance).2 u.val
    let e := (asIso (j.stalkMap u.val)).commRingCatIsoToRingEquiv
    have hfield : IsField (X.presheaf.stalk (j u.val)) := by
      rw [h]
      exact Field.toIsField X.functionField
    exact IsDiscreteValuationRing.not_isField (U.presheaf.stalk u.val)
      (e.symm.toMulEquiv.isField hfield)
  exact ⟨j u.val, mem_closedPoints_iff.mpr
    (isClosed_singleton_of_ne_genericPoint c (j u.val) hne)⟩

/-- The constructed ambient closed point is the original image point. -/
theorem openClosedPoint_val (u : closedPoints U) :
    (openClosedPoint c j u).val = j u.val := rfl

variable {F : Type u} [Field F] [Algebra k F]
  (p : Spec (.of F) ⟶ U) [IsDominant p] [IsPreimmersion p]
  (hp : p ≫ (j ≫ c) = Spec.map (CommRingCat.ofHom (algebraMap k F)))

/-- Interior and ambient points give the same actual place in the
specified field; this follows from the original stalk coefficient square. -/
theorem closedPointSourcePlace_open (u : closedPoints U) :
    closedPointSourcePlace c (p ≫ j) ((Category.assoc p j c).trans hp)
        (openClosedPoint c j u) =
      closedPointSourcePlace (j ≫ c) p hp u := by
  apply Place.ext
  apply ValuationSubring.toSubring_injective
  let : Algebra (X.presheaf.stalk (j u.val)) F :=
    genericFieldSourceStalkAlgebra (p ≫ j) (j u.val)
  let : Algebra (U.presheaf.stalk u.val) F := genericFieldSourceStalkAlgebra p u.val
  calc
    (closedPointSourcePlace c (p ≫ j) ((Category.assoc p j c).trans hp)
        (openClosedPoint c j u)).toValuationSubring.toSubring =
      (algebraMap (X.presheaf.stalk (j u.val)) F).range :=
        (closedPointSourcePlace_range c (p ≫ j) ((Category.assoc p j c).trans hp)
          (openClosedPoint c j u)).symm
    _ = (algebraMap (U.presheaf.stalk u.val) F).range :=
      genericFieldSourceStalk_range_open j p u.val
    _ = (closedPointSourcePlace (j ≫ c) p hp u).toValuationSubring.toSubring :=
      closedPointSourcePlace_range (j ≫ c) p hp u

end OpenPoints

section CanonicalSource

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]

/-- The supplied-source construction recovers the original point-place
map when its source is the canonical generic point. -/
theorem closedPointSourcePlace_fromSpecStalk (x : closedPoints X) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    closedPointSourcePlace c (X.fromSpecStalk (genericPoint X))
        (fromSpecStalk_genericPoint_comp_base c) x = closedPointPlace c x := by
  intro baseAlgebra
  have hr := closedPointSourcePlace_range c (X.fromSpecStalk (genericPoint X))
    (fromSpecStalk_genericPoint_comp_base c) x
  change ((genericFieldSourceRingEquiv (X.fromSpecStalk (genericPoint X))).toRingHom.comp
    (algebraMap (X.presheaf.stalk x.val) X.functionField)).range = _ at hr
  rw [genericFieldSourceRingEquiv_fromSpecStalk X] at hr
  change (algebraMap (X.presheaf.stalk x.val) X.functionField).range = _ at hr
  apply Place.ext
  apply ValuationSubring.toSubring_injective
  exact hr.symm.trans (closedPointPlace_range c x)

end CanonicalSource

section GenericBoundary

variable {k : Type u} [Field k] {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] [IsProper c]
  (j : U ⟶ X) [IsOpenImmersion j]

variable {F : Type u} [Field F] [Algebra k F]
  (p : Spec (.of F) ⟶ U) [IsDominant p] [IsPreimmersion p]
  (hp : p ≫ (j ≫ c) = Spec.map (CommRingCat.ofHom (algebraMap k F)))

/-- The proper compactification's actual closed points, expressed as
places of the original supplied generic field. -/
def genericSourcePlaceEquiv : closedPoints X ≃ Place k F :=
  closedPointSourcePlaceEquiv c (p ≫ j) ((Category.assoc p j c).trans hp)

/-- At an original interior point, the compactification's supplied-field
place is exactly the supplied-source open-curve place. -/
theorem genericSourcePlaceEquiv_openClosedPoint (u : closedPoints U) :
    genericSourcePlaceEquiv c j p hp (openClosedPoint c j u) =
      closedPointSourcePlace (j ≫ c) p hp u :=
  closedPointSourcePlace_open c j p hp u

/-- A place belongs to the original boundary precisely when its actual
closed-point center is omitted by the original open immersion. -/
def genericSourceBoundaryPlaces : Set (Place k F) :=
  {v | ((genericSourcePlaceEquiv c j p hp).symm v).val ∉ Set.range j}

/-- The actual boundary is finite, using the original geometric open
complement and the actual point-place correspondence. -/
theorem genericSourceBoundaryPlaces_finite : (genericSourceBoundaryPlaces c j p hp).Finite := by
  let V : X.Opens := ⟨Set.range j, j.isOpenEmbedding.isOpen_range⟩
  have hV : (V : Set X).Nonempty :=
    ⟨j (Classical.choice (inferInstance : Nonempty U)), Set.mem_range_self _⟩
  have hf := finite_compl_of_isOpen c V hV
  have hi : Function.Injective
      (fun v : Place k F => ((genericSourcePlaceEquiv c j p hp).symm v).val) :=
    fun v w h => (genericSourcePlaceEquiv c j p hp).symm.injective (Subtype.ext h)
  exact Set.Finite.preimage hi.injOn hf

/-- A center is in the boundary exactly when its corresponding place is. -/
theorem genericSourcePlaceEquiv_mem_boundary_iff (x : closedPoints X) :
    genericSourcePlaceEquiv c j p hp x ∈ genericSourceBoundaryPlaces c j p hp ↔
      x.val ∉ Set.range j := by
  change ((genericSourcePlaceEquiv c j p hp).symm (genericSourcePlaceEquiv c j p hp x)).val ∉
    Set.range j ↔ _
  rw [(genericSourcePlaceEquiv c j p hp).symm_apply_apply]

/-- Every original open-curve point gives a place outside the boundary. -/
theorem closedPointSourcePlace_not_mem_genericSourceBoundary (u : closedPoints U) :
    closedPointSourcePlace (j ≫ c) p hp u ∉ genericSourceBoundaryPlaces c j p hp := by
  rw [← genericSourcePlaceEquiv_openClosedPoint c j p hp u,
    genericSourcePlaceEquiv_mem_boundary_iff]
  exact fun h => h ⟨u.val, rfl⟩

/-- Every place outside the actual boundary is the place of an original
closed point of the original open curve. -/
theorem exists_closedPointSourcePlace_of_not_mem_genericSourceBoundary
    (v : Place k F) (hv : v ∉ genericSourceBoundaryPlaces c j p hp) :
    ∃ u : closedPoints U, closedPointSourcePlace (j ≫ c) p hp u = v := by
  classical
  let x := (genericSourcePlaceEquiv c j p hp).symm v
  have hmem : x.val ∈ Set.range j := not_not.mp hv
  obtain ⟨u, hu⟩ := hmem
  have hpre : j ⁻¹' ({x.val} : Set X) = {u} := by
    apply Set.ext
    intro w
    change j w = x.val ↔ w = u
    rw [← hu]
    exact j.isOpenEmbedding.injective.eq_iff
  have hclosed : IsClosed ({u} : Set U) := by
    rw [← hpre]
    exact (mem_closedPoints_iff.mp x.property).preimage j.continuous
  let u' : closedPoints U := ⟨u, mem_closedPoints_iff.mpr hclosed⟩
  have hx : openClosedPoint c j u' = x := Subtype.ext hu
  refine ⟨u', ?_⟩
  calc
    closedPointSourcePlace (j ≫ c) p hp u' =
        genericSourcePlaceEquiv c j p hp (openClosedPoint c j u') :=
      (genericSourcePlaceEquiv_openClosedPoint c j p hp u').symm
    _ = genericSourcePlaceEquiv c j p hp x := congrArg (genericSourcePlaceEquiv c j p hp) hx
    _ = v := (genericSourcePlaceEquiv c j p hp).apply_symm_apply v

/-- The original reduced boundary modulus: one at the actual omitted
places and zero at exactly the original interior places. -/
def genericSourceBoundaryModulus : FunctionField.RayClass.Modulus k F := by
  classical
  exact Finsupp.ofSupportFinite
    (fun v : Place k F => if v ∈ genericSourceBoundaryPlaces c j p hp then 1 else 0)
    ((genericSourceBoundaryPlaces_finite c j p hp).subset (by
      intro v hv
      by_contra h
      exact hv (ite_eq_right h)))

open Classical in
/-- The actual modulus exponent is the boundary indicator. -/
theorem genericSourceBoundaryModulus_apply (v : Place k F) :
    genericSourceBoundaryModulus c j p hp v =
      if v ∈ genericSourceBoundaryPlaces c j p hp then 1 else 0 := rfl

/-- This actual boundary modulus is reduced. -/
theorem genericSourceBoundaryModulus_le_one (v : Place k F) :
    genericSourceBoundaryModulus c j p hp v ≤ 1 := by
  classical
  by_cases hv : v ∈ genericSourceBoundaryPlaces c j p hp
  · simpa only [genericSourceBoundaryModulus_apply, ite_eq_left hv] using (le_refl (1 : ℕ))
  · simpa only [genericSourceBoundaryModulus_apply, ite_eq_right hv] using (Nat.zero_le 1)

/-- Zero modulus exponent is precisely original interior membership. -/
theorem genericSourceBoundaryModulus_eq_zero_iff (v : Place k F) :
    genericSourceBoundaryModulus c j p hp v = 0 ↔ v ∉ genericSourceBoundaryPlaces c j p hp := by
  classical
  simp only [genericSourceBoundaryModulus_apply, ite_eq_right_iff, Nat.one_ne_zero]

/-- One modulus exponent is precisely original boundary membership. -/
theorem genericSourceBoundaryModulus_eq_one_iff (v : Place k F) :
    genericSourceBoundaryModulus c j p hp v = 1 ↔ v ∈ genericSourceBoundaryPlaces c j p hp := by
  classical
  rw [genericSourceBoundaryModulus_apply]
  by_cases hv : v ∈ genericSourceBoundaryPlaces c j p hp
  · rw [ite_eq_left hv]
    exact iff_of_true rfl hv
  · rw [ite_eq_right hv]
    exact iff_of_false Nat.zero_ne_one hv

/-- Reindex any family of subgroups or lattice elements at original
interior points by the actual zero-exponent places. -/
theorem iSup_closedPointSource_eq_iSup_genericBoundaryModulus_zero
    {A : Type*} [CompleteLattice A] (f : Place k F → A) :
    (⨆ u : closedPoints U, f (closedPointSourcePlace (j ≫ c) p hp u)) =
      ⨆ (v : Place k F) (_ : genericSourceBoundaryModulus c j p hp v = 0), f v := by
  apply le_antisymm
  · apply iSup_le
    intro u
    exact le_iSup_of_le (closedPointSourcePlace (j ≫ c) p hp u) (le_iSup_of_le
      ((genericSourceBoundaryModulus_eq_zero_iff c j p hp _).mpr
        (closedPointSourcePlace_not_mem_genericSourceBoundary c j p hp u)) le_rfl)
  · apply iSup_le
    intro v
    apply iSup_le
    intro hv
    obtain ⟨u, hu⟩ := exists_closedPointSourcePlace_of_not_mem_genericSourceBoundary c j p hp v
      ((genericSourceBoundaryModulus_eq_zero_iff c j p hp v).mp hv)
    rw [← hu]
    exact le_iSup (fun x : closedPoints U => f (closedPointSourcePlace (j ≫ c) p hp x)) u

/-- Reindex the actual closed boundary points by the actual
one-exponent places, using the proved proper point-place equivalence. -/
theorem iSup_genericBoundaryPoint_eq_iSup_genericBoundaryModulus_one
    {A : Type*} [CompleteLattice A] (f : Place k F → A) :
    (⨆ (x : closedPoints X) (_ : x.val ∉ Set.range j), f (genericSourcePlaceEquiv c j p hp x)) =
      ⨆ (v : Place k F) (_ : genericSourceBoundaryModulus c j p hp v = 1), f v := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    exact le_iSup_of_le (genericSourcePlaceEquiv c j p hp x) (le_iSup_of_le
      ((genericSourceBoundaryModulus_eq_one_iff c j p hp _).mpr
        ((genericSourcePlaceEquiv_mem_boundary_iff c j p hp x).mpr hx)) le_rfl)
  · apply iSup_le
    intro v
    apply iSup_le
    intro hv
    have hx : ((genericSourcePlaceEquiv c j p hp).symm v).val ∉ Set.range j :=
      (genericSourceBoundaryModulus_eq_one_iff c j p hp v).mp hv
    have h :
        f (genericSourcePlaceEquiv c j p hp ((genericSourcePlaceEquiv c j p hp).symm v)) ≤
          ⨆ (x : closedPoints X) (_ : x.val ∉ Set.range j),
            f (genericSourcePlaceEquiv c j p hp x) :=
      le_iSup_of_le ((genericSourcePlaceEquiv c j p hp).symm v)
        (le_iSup_of_le hx le_rfl)
    simpa only [Equiv.apply_symm_apply] using h

section Artin

variable [Finite k] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] [HasPrincipalDivisors k F]

/-- The actual ray subgroup in the specified generic field is generated
by units at the original interior points and principal units at the
original boundary points. -/
theorem artinRaySubgroup_genericSourceBoundary :
    FunctionField.RayClass.artinRaySubgroup (genericSourceBoundaryModulus c j p hp) =
      ((⨆ u : closedPoints U,
          FunctionField.RayClass.placeArtinUnitImage (closedPointSourcePlace (j ≫ c) p hp u) 0) ⊔
        (⨆ (x : closedPoints X) (_ : x.val ∉ Set.range j),
          FunctionField.RayClass.placeArtinUnitImage
            (genericSourcePlaceEquiv c j p hp x) 1)).topologicalClosure := by
  rw [FunctionField.RayClass.artinRaySubgroup_reduced_generators
    (genericSourceBoundaryModulus c j p hp) (genericSourceBoundaryModulus_le_one c j p hp),
    ← iSup_closedPointSource_eq_iSup_genericBoundaryModulus_zero c j p hp,
    ← iSup_genericBoundaryPoint_eq_iSup_genericBoundaryModulus_one c j p hp]

end Artin

end GenericBoundary

section Boundary

variable {k : Type u} [Field k] {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] [IsProper c]
  (j : U ⟶ X) [IsOpenImmersion j]

local notation "p₀" => U.fromSpecStalk (genericPoint U)
local notation "hp₀" => fromSpecStalk_genericPoint_comp_base (j ≫ c)

/-- The proper compactification's actual closed points, expressed as
places of the original open curve's function field. -/
def openSourcePlaceEquiv :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    closedPoints X ≃ Place k U.functionField := by
  intro baseAlgebra
  exact genericSourcePlaceEquiv c j p₀ hp₀

/-- At an original interior point, the compactification's supplied-field
place is exactly the original open-curve place. -/
theorem openSourcePlaceEquiv_openClosedPoint (u : closedPoints U) :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    openSourcePlaceEquiv c j (openClosedPoint c j u) = closedPointPlace (j ≫ c) u := by
  intro baseAlgebra
  exact (genericSourcePlaceEquiv_openClosedPoint c j p₀ hp₀ u).trans
      (closedPointSourcePlace_fromSpecStalk (j ≫ c) u)

/-- A place belongs to the original boundary precisely when its actual
closed-point center is omitted by the original open immersion. -/
def openSourceBoundaryPlaces :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    Set (Place k U.functionField) := by
  intro baseAlgebra
  exact genericSourceBoundaryPlaces c j p₀ hp₀

/-- The actual boundary is finite, using the original geometric open
complement and the actual point-place correspondence. -/
theorem openSourceBoundaryPlaces_finite :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    (openSourceBoundaryPlaces c j).Finite := by
  intro baseAlgebra
  exact genericSourceBoundaryPlaces_finite c j p₀ hp₀

/-- A center is in the boundary exactly when its corresponding place is. -/
theorem openSourcePlaceEquiv_mem_boundary_iff (x : closedPoints X) :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    openSourcePlaceEquiv c j x ∈ openSourceBoundaryPlaces c j ↔
      x.val ∉ Set.range j := by
  intro baseAlgebra
  exact genericSourcePlaceEquiv_mem_boundary_iff c j p₀ hp₀ x

/-- Every original open-curve point gives a place outside the boundary. -/
theorem closedPointPlace_not_mem_openSourceBoundary (u : closedPoints U) :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    closedPointPlace (j ≫ c) u ∉ openSourceBoundaryPlaces c j := by
  intro baseAlgebra
  simpa only [closedPointSourcePlace_fromSpecStalk, openSourceBoundaryPlaces] using
    closedPointSourcePlace_not_mem_genericSourceBoundary c j p₀ hp₀ u

/-- Every place outside the actual boundary is the place of an original
closed point of the original open curve. -/
theorem exists_closedPointPlace_of_not_mem_openSourceBoundary :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ v : Place k U.functionField, v ∉ openSourceBoundaryPlaces c j →
    ∃ u : closedPoints U, closedPointPlace (j ≫ c) u = v := by
  intro baseAlgebra v hv
  simpa only [closedPointSourcePlace_fromSpecStalk] using
    exists_closedPointSourcePlace_of_not_mem_genericSourceBoundary c j p₀ hp₀ v hv

/-- The original reduced boundary modulus: one at the actual omitted
places and zero at exactly the original interior places. -/
def openSourceBoundaryModulus :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    FunctionField.RayClass.Modulus k U.functionField := by
  intro baseAlgebra
  exact genericSourceBoundaryModulus c j p₀ hp₀

open Classical in
/-- The actual modulus exponent is the boundary indicator. -/
theorem openSourceBoundaryModulus_apply :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ v : Place k U.functionField,
    openSourceBoundaryModulus c j v =
      if v ∈ openSourceBoundaryPlaces c j then 1 else 0 := by
  intro baseAlgebra v
  exact rfl

/-- This actual boundary modulus is reduced. -/
theorem openSourceBoundaryModulus_le_one :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ v : Place k U.functionField,
    openSourceBoundaryModulus c j v ≤ 1 := by
  intro baseAlgebra v
  exact genericSourceBoundaryModulus_le_one c j p₀ hp₀ v

/-- Zero modulus exponent is precisely original interior membership. -/
theorem openSourceBoundaryModulus_eq_zero_iff :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ v : Place k U.functionField,
    openSourceBoundaryModulus c j v = 0 ↔ v ∉ openSourceBoundaryPlaces c j := by
  intro baseAlgebra v
  exact genericSourceBoundaryModulus_eq_zero_iff c j p₀ hp₀ v

/-- One modulus exponent is precisely original boundary membership. -/
theorem openSourceBoundaryModulus_eq_one_iff :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ v : Place k U.functionField,
    openSourceBoundaryModulus c j v = 1 ↔ v ∈ openSourceBoundaryPlaces c j := by
  intro baseAlgebra v
  exact genericSourceBoundaryModulus_eq_one_iff c j p₀ hp₀ v

/-- Reindex any family of subgroups or lattice elements at original
interior points by the actual zero-exponent places. -/
theorem iSup_closedPoint_eq_iSup_boundaryModulus_zero
    {A : Type*} [CompleteLattice A] :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ f : Place k U.functionField → A,
    (⨆ u : closedPoints U, f (closedPointPlace (j ≫ c) u)) =
      ⨆ (v : Place k U.functionField) (_ : openSourceBoundaryModulus c j v = 0), f v := by
  intro baseAlgebra f
  simpa only [closedPointSourcePlace_fromSpecStalk, openSourceBoundaryModulus] using
    iSup_closedPointSource_eq_iSup_genericBoundaryModulus_zero c j p₀ hp₀ f

/-- Reindex the actual closed boundary points by the actual
one-exponent places, using the proved proper point-place equivalence. -/
theorem iSup_boundaryPoint_eq_iSup_boundaryModulus_one
    {A : Type*} [CompleteLattice A] :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ f : Place k U.functionField → A,
    (⨆ (x : closedPoints X) (_ : x.val ∉ Set.range j), f (openSourcePlaceEquiv c j x)) =
      ⨆ (v : Place k U.functionField) (_ : openSourceBoundaryModulus c j v = 1), f v := by
  intro baseAlgebra f
  exact iSup_genericBoundaryPoint_eq_iSup_genericBoundaryModulus_one c j p₀ hp₀ f

section Artin

variable [Finite k]

/-- The native generic-kernel contribution is precisely the original
depth-zero local units at the zero-exponent places of the actual boundary. -/
theorem canonicalOpenFieldSource_ker_localUnits [IsNormalIntegral U] :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [Algebra (RatFunc k) U.functionField]
      [IsScalarTower k (RatFunc k) U.functionField]
      [FunctionField k U.functionField] [HasPrincipalDivisors k U.functionField],
    ((AlgebraicGeometry.FiniteEtale.fieldSourceAbsoluteGaloisHom U.functionField
      (SeparableClosure U.functionField) (U.fromSpecStalk (genericPoint U))).toMonoidHom.ker).map
        (ProCGroups.Abelian.TopologicalAbelianization.mk
          Gal(SeparableClosure U.functionField/U.functionField)) =
      (⨆ (v : Place k U.functionField) (_ : openSourceBoundaryModulus c j v = 0),
        FunctionField.RayClass.placeArtinUnitImage v 0).topologicalClosure := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors
  have hker := canonicalFieldSourceAbsoluteGaloisHom_ker_localUnits (j ≫ c)
  have hindex := iSup_closedPoint_eq_iSup_boundaryModulus_zero c j
    (fun v : Place k U.functionField => FunctionField.RayClass.placeArtinUnitImage v 0)
  exact hker.trans (congrArg
    (fun H : Subgroup (localAbsoluteAbelianProfinite U.functionField) =>
      H.topologicalClosure) hindex)

/-- The actual ray subgroup is generated by ordinary units at original
interior points and principal units at the original omitted points. -/
theorem artinRaySubgroup_openSourceBoundary :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [Algebra (RatFunc k) U.functionField]
      [IsScalarTower k (RatFunc k) U.functionField]
      [FunctionField k U.functionField] [HasPrincipalDivisors k U.functionField],
    FunctionField.RayClass.artinRaySubgroup (openSourceBoundaryModulus c j) =
      ((⨆ u : closedPoints U,
          FunctionField.RayClass.placeArtinUnitImage (closedPointPlace (j ≫ c) u) 0) ⊔
        (⨆ (x : closedPoints X) (_ : x.val ∉ Set.range j),
          FunctionField.RayClass.placeArtinUnitImage
            (openSourcePlaceEquiv c j x) 1)).topologicalClosure := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors
  simpa only [closedPointSourcePlace_fromSpecStalk, openSourceBoundaryModulus,
    openSourcePlaceEquiv] using artinRaySubgroup_genericSourceBoundary c j p₀ hp₀

end Artin

end Boundary

end EtaleFundamentalGroups.Inertia
