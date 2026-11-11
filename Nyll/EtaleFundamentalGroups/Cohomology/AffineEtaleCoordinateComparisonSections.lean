/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleCoordinateComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineGenericPointStalkComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorData
public import Nyll.EtaleFundamentalGroups.Cohomology.IntegralAffineEtaleBasis
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Coordinate values of the actual affine divisor comparison

The cover-dense extension defining the affine sheaf isomorphism restricts to
the original comparison on the integral affine basis. After passing to the
coordinate spectrum, its image is the original native object comparison.
The existing general coefficient theorem can then be applied over this common
source, without reconstructing any quotient or coefficient map.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

attribute [local irreducible] affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv

variable (R : Type u) [CommRing R] [IsDedekindDomain R] (hR : ¬ IsField R)
  [HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
    (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]

/-- The actual affine sheaf isomorphism recovers its original comparison on
the integral affine basis. -/
theorem affineClosedPointDivisorGenericUnitSheafIso_restrict :
    Functor.whiskerLeft (integralAffineEtaleInclusion (Spec (CommRingCat.of R))).op
        (affineClosedPointDivisorGenericUnitSheafIso R hR).hom.hom =
      (integralAffineClosedPointDivisorGenericUnitNatIso R hR).hom := by
  let I := integralAffineEtaleInclusion (Spec (CommRingCat.of R))
  let : I.IsCoverDense (Spec (CommRingCat.of R)).smallEtaleTopology :=
    integralAffineEtaleInclusion_isCoverDense R
  let : I.Full := by
    dsimp only [I, integralAffineEtaleInclusion]
    infer_instance
  exact Functor.IsCoverDense.sheafHom_restrict_eq (G := I)
    (integralAffineClosedPointDivisorGenericUnitNatIso R hR).hom

private theorem integralAffineCoordinateComparison_eq
    (A : (integralAffineEtaleObjectProperty
      (X := Spec (CommRingCat.of R))).FullSubcategory) :
    let S := Γ(A.obj.left, ⊤)
    let _ : IsDedekindDomain S := integralAffineCoordinate_isDedekindDomain R A
    let algRS : Algebra R S := (integralAffineCoordinateBaseMap R A).hom.toAlgebra
    let _ : Algebra.Etale R S :=
      RingHom.etale_algebraMap.mp (integralAffineCoordinateBaseMap_etale R A)
    let algRE : Algebra R (FractionRing S) :=
      ((algebraMap S (FractionRing S)).comp (algebraMap R S)).toAlgebra
    let _ : @IsScalarTower R S (FractionRing S) algRS.toSMul
        (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : @FaithfulSMul R (FractionRing S) algRE.toSMul :=
      (faithfulSMul_iff_algebraMap_injective R (FractionRing S)).mpr
        ((IsFractionRing.injective S (FractionRing S)).comp
          (FaithfulSMul.algebraMap_injective R S))
    let algKE : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
    let _ : @IsScalarTower R (FractionRing R) (FractionRing S)
        (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul :=
      FractionRing.isScalarTower_liftAlgebra R _
    let e := integralAffineCoordinateEtaleObjIso R A
    let D := closedPointDivisorSheaf (Spec (CommRingCat.of R))
    let Q := affineGenericPointUnitQuotient R
    integralAffineClosedPointDivisorGenericUnitObjectAddEquiv R hR A =
      (D.obj.mapIso e.op).symm.addCommGroupIsoToAddEquiv.trans
        ((affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv
          (R := R) (S := S) hR).trans
            (Q.obj.mapIso e.op).addCommGroupIsoToAddEquiv) := by
  intro S hS algRS hE algRE hRS hf algKE hKS e D Q
  rfl

private theorem transportAddEquiv_inv_apply
    {D₀ D Q₀ Q : AddCommGrpCat.{u}} (eD : D₀ ≅ D) (eQ : Q₀ ≅ Q)
    (a : D₀ ≃+ Q₀) (b : D ≃+ Q)
    (hb : b = eD.symm.addCommGroupIsoToAddEquiv.trans
      (a.trans eQ.addCommGroupIsoToAddEquiv))
    (s : D) (v : Q) (hv : v = b s) :
    eQ.inv v = a (eD.inv s) := by
  rw [hv, hb]
  exact ConcreteCategory.congr_hom eQ.hom_inv_id (a (eD.inv s))

/-- The actual sheaf comparison, transported to the coordinate spectrum,
recovers the original native object comparison. The algebra structures are
exactly those used to define the coordinate comparison. -/
theorem affineClosedPointDivisorGenericUnitSheafIso_coordinate
    (A : (integralAffineEtaleObjectProperty
      (X := Spec (CommRingCat.of R))).FullSubcategory) :
    let S := Γ(A.obj.left, ⊤)
    let _ : IsDedekindDomain S := integralAffineCoordinate_isDedekindDomain R A
    let algRS : Algebra R S := (integralAffineCoordinateBaseMap R A).hom.toAlgebra
    let _ : Algebra.Etale R S :=
      RingHom.etale_algebraMap.mp (integralAffineCoordinateBaseMap_etale R A)
    let algRE : Algebra R (FractionRing S) :=
      ((algebraMap S (FractionRing S)).comp (algebraMap R S)).toAlgebra
    let _ : @IsScalarTower R S (FractionRing S) algRS.toSMul
        (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : @FaithfulSMul R (FractionRing S) algRE.toSMul :=
      (faithfulSMul_iff_algebraMap_injective R (FractionRing S)).mpr
        ((IsFractionRing.injective S (FractionRing S)).comp
          (FaithfulSMul.algebraMap_injective R S))
    let algKE : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
    let _ : @IsScalarTower R (FractionRing R) (FractionRing S)
        (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul :=
      FractionRing.isScalarTower_liftAlgebra R _
    let e := integralAffineCoordinateEtaleObjIso R A
    let D := closedPointDivisorSheaf (Spec (CommRingCat.of R))
    let Q := affineGenericPointUnitQuotient R
    ∀ (s : D.obj.obj (op A.obj)),
      Q.obj.map e.inv.op
        ((affineClosedPointDivisorGenericUnitSheafIso R hR).hom.hom.app
          (op A.obj) s) =
      affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv
        (R := R) (S := S) hR (D.obj.map e.inv.op s) := by
  intro S hS algRS hE algRE hRS hf algKE hKS e D Q s
  have hb := congr_app
    (affineClosedPointDivisorGenericUnitSheafIso_restrict R hR) (op A)
  have hs := ConcreteCategory.congr_hom hb s
  change (affineClosedPointDivisorGenericUnitSheafIso R hR).hom.hom.app
      (op A.obj) s =
    integralAffineClosedPointDivisorGenericUnitObjectAddEquiv R hR A s at hs
  exact transportAddEquiv_inv_apply (D.obj.mapIso e.op) (Q.obj.mapIso e.op)
    (affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv (R := R) (S := S) hR)
    (integralAffineClosedPointDivisorGenericUnitObjectAddEquiv R hR A)
    (integralAffineCoordinateComparison_eq R hR A) s _ hs

end EtaleCohomology
