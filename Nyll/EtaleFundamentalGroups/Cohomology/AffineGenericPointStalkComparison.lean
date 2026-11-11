/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.AffineGenericUnitQuotient
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# The generic point stalk as the affine fraction field

For an affine integral scheme, the actual generic-point stalk is the function
field and is a fraction ring of the coordinate ring. The actual generic-point
unit quotient is therefore the quotient presented by the corresponding
fraction-field spectrum map.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace EtaleCohomology

variable (R : Type u) [CommRing R] [IsDomain R]

/-- The affine scheme associated with the coordinate ring. -/
noncomputable abbrev affineGenericPointScheme := Spec (CommRingCat.of R)

/-- The generic point of the affine integral scheme. -/
noncomputable abbrev affineGenericPoint : affineGenericPointScheme R :=
  genericPoint (affineGenericPointScheme R)

/-- The actual structure-sheaf stalk at the generic point. -/
noncomputable abbrev affineGenericPointStalk :=
  (affineGenericPointScheme R).presheaf.stalk (affineGenericPoint R)

noncomputable instance affineGenericPointStalkAlgebra :
    Algebra R (affineGenericPointStalk R) :=
  StructureSheaf.stalkAlgebra R (affineGenericPoint R)

/-- The canonical ring map from coordinates to the generic point stalk. -/
noncomputable def affineGenericPointGermMap :
    CommRingCat.of R ⟶ CommRingCat.of (affineGenericPointStalk R) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (affineGenericPointScheme R).presheaf.germ ⊤ (affineGenericPoint R) trivial

theorem affineGenericPointGermMap_eq_algebraMap :
    (affineGenericPointGermMap R).hom =
      algebraMap R (affineGenericPointStalk R) := by
  ext r
  rfl

/-- The local ring at the generic point of `Spec R` is a fraction ring of `R`. -/
theorem affineGenericPointStalk_isFractionRing :
    IsFractionRing R (affineGenericPointStalk R) :=
  functionField_isFractionRing_of_affine (CommRingCat.of R)

/-- On an affine scheme, `fromSpecStalk` at the generic point is induced by
the coordinate-ring map into the actual stalk. -/
theorem affineGenericPoint_fromSpecStalk_eq_specMap :
    (affineGenericPointScheme R).fromSpecStalk (affineGenericPoint R) =
      Spec.map (affineGenericPointGermMap R) := by
  rw [Spec.fromSpecStalk_eq']
  congr 1

/-- The actual étale quotient sheaf of generic-point units. -/
@[reducible] noncomputable def affineGenericPointUnitQuotient :
    Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u} :=
  etaleGenericUnitQuotient (Spec (CommRingCat.of R))

/-- The generic-unit quotient presented using the actual stalk as fraction ring. -/
noncomputable abbrev affineGenericPointStalkUnitQuotient :=
  cokernel (etaleMultiplicativeGroupToPushforward
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (affineGenericPointStalk R)))))

/-- The actual generic-point unit quotient on `Spec R` is presented by the
fraction-ring map into the actual generic-point stalk. -/
theorem affineGenericPointUnitQuotient_eq_stalkModel :
    affineGenericPointUnitQuotient R = affineGenericPointStalkUnitQuotient R := by
  dsimp [affineGenericPointUnitQuotient, affineGenericPointStalkUnitQuotient,
    etaleGenericUnitQuotient]
  change cokernel (etaleMultiplicativeGroupToPushforward
      ((affineGenericPointScheme R).fromSpecStalk (affineGenericPoint R))) = _
  rw [affineGenericPoint_fromSpecStalk_eq_specMap]
  congr 1

/-- Uniqueness of the fraction ring identifies the usual fraction field with
the actual generic-point stalk as an `R`-algebra. -/
noncomputable def affineGenericPointStalkFractionRingAlgEquiv :
    FractionRing R ≃ₐ[R] affineGenericPointStalk R := by
  letI : IsFractionRing R (affineGenericPointStalk R) :=
    affineGenericPointStalk_isFractionRing R
  exact IsFractionRing.algEquivOfAlgEquiv (AlgEquiv.refl : R ≃ₐ[R] R)

/-- The actual generic-point quotient sheaf is isomorphic to the established
quotient model defined using `FractionRing R`. This applies the existing
fraction-field restriction comparison to the identity étale square. -/
noncomputable def affineGenericPointUnitQuotientFractionRingIso :
    affineGenericPointUnitQuotient R ≅
      affineEtaleFractionRingUnitQuotient R := by
  letI : IsFractionRing R (affineGenericPointStalk R) :=
    affineGenericPointStalk_isFractionRing R
  letI : Algebra (FractionRing R) (affineGenericPointStalk R) :=
    (affineGenericPointStalkFractionRingAlgEquiv R).toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower R (FractionRing R) (affineGenericPointStalk R) := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    symm
    exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
      (AlgEquiv.refl : R ≃ₐ[R] R) r
  let i := Spec.map (CommRingCat.ofHom (algebraMap R R))
  let e := etaleRestrictionFractionFieldUnitQuotientIso
    R R (FractionRing R) (affineGenericPointStalk R)
  have hi : i = 𝟙 (affineGenericPointScheme R) := by
    dsimp [i]
    exact AlgebraicGeometry.Spec.map_id (CommRingCat.of R)
  have eId : (etaleRestriction (𝟙 (affineGenericPointScheme R)) AddCommGrpCat.{u}).obj
      (affineEtaleFractionRingUnitQuotient R) ≅
      cokernel (etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (affineGenericPointStalk R))))) := by
    simpa only [i, hi, affineEtaleFractionRingUnitQuotient] using e
  let hQ := affineGenericPointUnitQuotient_eq_stalkModel R
  let rid := (Functor.sheafPushforwardContinuousId AddCommGrpCat.{u}
    (affineGenericPointScheme R).smallEtaleTopology).app
      (affineEtaleFractionRingUnitQuotient R)
  exact (eqToIso hQ) ≪≫ eId.symm ≪≫ rid

end EtaleCohomology
