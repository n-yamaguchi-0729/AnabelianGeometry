/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Nyll.EtaleFundamentalGroups.Cohomology.IntegralAffineEtaleBasis
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorComparison
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Nyll.SchemeTheory.RingTheory.Etale.UnramifiedDedekind

/-!
# Coordinates on integral affine étale objects

Every integral affine object over an affine Dedekind base is canonically
isomorphic over the base to the spectrum of its ring of global sections. These
coordinate identifications commute with every arrow in the full subcategory.
This presents arbitrary arrows as the `Spec.map` of their global-section maps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace EtaleCohomology

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

variable (A : (integralAffineEtaleObjectProperty
  (X := Spec (CommRingCat.of R))).FullSubcategory)

/-- The affine spectrum presentation of an integral affine étale object. -/
noncomputable def integralAffineCoordinateIso :
    A.obj.left ≅ Spec Γ(A.obj.left, ⊤) := by
  exact @Scheme.isoSpec ((𝟭 Scheme).obj A.obj.left) (by simpa using A.property.1)

/-- The base map on global sections of an integral affine étale object. -/
noncomputable def integralAffineCoordinateBaseMap :
    CommRingCat.of R ⟶ Γ(A.obj.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ A.obj.hom.appTop

omit [IsDedekindDomain R] in
theorem integralAffineCoordinateBaseMap_etale :
    (integralAffineCoordinateBaseMap R A).hom.Etale := by
  let : IsAffine ((𝟭 Scheme).obj A.obj.left) := A.property.1
  let : IsAffine ((Functor.fromPUnit (Spec (CommRingCat.of R))).obj A.obj.right) := by
    cases A.obj.right
    exact isAffine_Spec (CommRingCat.of R)
  have he : ((A.obj.hom.appTop).hom).Etale := by
    exact (HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale)
      (f := A.obj.hom)).mp A.obj.prop
  change ((A.obj.hom.appTop).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.toRingHom |>.Etale
  exact RingHom.Etale.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm he

omit [IsDedekindDomain R] in
/-- Compatibility of the coordinate presentation with the structural map. -/
theorem integralAffineCoordinateSpecMap_eq :
    Spec.map (integralAffineCoordinateBaseMap R A) =
      (integralAffineCoordinateIso R A).inv ≫ A.obj.hom := by
  rw [integralAffineCoordinateBaseMap, Spec.map_comp, ← Scheme.isoSpec_Spec_inv]
  have hA : IsAffine ((𝟭 Scheme).obj A.obj.left) := by
    simpa using A.property.1
  exact @Scheme.isoSpec_inv_naturality A.obj.left (Spec (CommRingCat.of R))
    hA (isAffine_Spec _) A.obj.hom

/-- The coordinate presentation, as an object of the small étale site.
Its target is the same native object used by the divisor section comparison. -/
noncomputable abbrev integralAffineCoordinateEtaleObj :
    (Spec (CommRingCat.of R)).Etale := by
  let S := Γ(A.obj.left, ⊤)
  let algRS : Algebra R S := (integralAffineCoordinateBaseMap R A).hom.toAlgebra
  let : Algebra.Etale R S :=
    RingHom.etale_algebraMap.mp (integralAffineCoordinateBaseMap_etale R A)
  exact affineEtaleSpecObject (R := R) (S := S)

/-- The original étale object is canonically isomorphic to its coordinate
presentation over the base. -/
noncomputable def integralAffineCoordinateEtaleObjIso :
    A.obj ≅ integralAffineCoordinateEtaleObj R A := by
  let A' : MorphismProperty.Over @Etale ⊤ (Spec (CommRingCat.of R)) := A.obj
  let B' : MorphismProperty.Over @Etale ⊤ (Spec (CommRingCat.of R)) :=
    integralAffineCoordinateEtaleObj R A
  let e : A'.left ≅ B'.left := integralAffineCoordinateIso R A
  have h : (𝟭 Scheme).map e.hom ≫ B'.hom = A'.hom := by
    change (integralAffineCoordinateIso R A).hom ≫
      Spec.map (integralAffineCoordinateBaseMap R A) = A.obj.hom
    rw [integralAffineCoordinateSpecMap_eq]
    exact Iso.hom_inv_id_assoc _ _
  exact MorphismProperty.Over.isoMk (A := A') (B := B') e h

variable {A B : (integralAffineEtaleObjectProperty
  (X := Spec (CommRingCat.of R))).FullSubcategory} (f : A ⟶ B)

/-- The arrow induced by `f` between the coordinate presentations. -/
noncomputable def integralAffineCoordinateArrow :
    integralAffineCoordinateEtaleObj R A ⟶ integralAffineCoordinateEtaleObj R B :=
  (integralAffineCoordinateEtaleObjIso R A).inv ≫ f.hom ≫
    (integralAffineCoordinateEtaleObjIso R B).hom

omit [IsDedekindDomain R] in
/-- The base global-section maps compose along every arrow of the full
subcategory. -/
theorem integralAffineCoordinateBaseMap_comp :
    integralAffineCoordinateBaseMap R B ≫ Scheme.Hom.appTop f.hom.left =
      integralAffineCoordinateBaseMap R A := by
  have hw : f.hom.left ≫ B.obj.hom = A.obj.hom := f.hom.w
  have hh := congrArg Scheme.Hom.appTop hw
  rw [Scheme.Hom.comp_appTop] at hh
  dsimp [integralAffineCoordinateBaseMap]
  exact congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g) hh

omit [IsDedekindDomain R] in
/-- In coordinates, every arrow is the spectrum map of its map on global
sections. -/
theorem integralAffineCoordinateArrow_left_eq :
    (integralAffineCoordinateArrow R f).hom.left =
      Spec.map (Scheme.Hom.appTop f.hom.left) := by
  change (integralAffineCoordinateIso R A).inv ≫ f.hom.left ≫
      (integralAffineCoordinateIso R B).hom = Spec.map (Scheme.Hom.appTop f.hom.left)
  let hA : IsAffine ((𝟭 Scheme).obj A.obj.left) := by simpa using A.property.1
  let hB : IsAffine ((𝟭 Scheme).obj B.obj.left) := by simpa using B.property.1
  have h := @Scheme.isoSpec_hom_naturality _ _ hA hB f.hom.left
  have h' : (integralAffineCoordinateIso R A).hom ≫
      Spec.map (Scheme.Hom.appTop f.hom.left) =
      f.hom.left ≫ (integralAffineCoordinateIso R B).hom := by
    simpa [integralAffineCoordinateIso] using h
  calc
    (integralAffineCoordinateIso R A).inv ≫ f.hom.left ≫
        (integralAffineCoordinateIso R B).hom =
      (integralAffineCoordinateIso R A).inv ≫
        ((integralAffineCoordinateIso R A).hom ≫
          Spec.map (Scheme.Hom.appTop f.hom.left)) := by rw [h']
    _ = Spec.map (Scheme.Hom.appTop f.hom.left) := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The coordinate presentations form a functor, obtained by transporting
arrows along the objectwise coordinate isomorphisms. -/
noncomputable def integralAffineCoordinateEtaleFunctor :
    (integralAffineEtaleObjectProperty
      (X := Spec (CommRingCat.of R))).FullSubcategory ⥤
      (Spec (CommRingCat.of R)).Etale where
  obj A := integralAffineCoordinateEtaleObj R A
  map f := integralAffineCoordinateArrow R f
  map_id A := by simp [integralAffineCoordinateArrow]
  map_comp f g := by simp [integralAffineCoordinateArrow]

/-- The functor of coordinate presentations is naturally isomorphic to the
inclusion of the integral affine basis. -/
noncomputable def integralAffineCoordinateEtaleFunctorIso :
    integralAffineEtaleInclusion (Spec (CommRingCat.of R)) ≅
      integralAffineCoordinateEtaleFunctor R := by
  refine NatIso.ofComponents (fun A => integralAffineCoordinateEtaleObjIso R A) ?_
  intro A B f
  change f.hom ≫ (integralAffineCoordinateEtaleObjIso R B).hom =
    (integralAffineCoordinateEtaleObjIso R A).hom ≫
      ((integralAffineCoordinateEtaleObjIso R A).inv ≫ f.hom ≫
        (integralAffineCoordinateEtaleObjIso R B).hom)
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The coordinate ring of an integral affine étale object over a Dedekind
domain is Dedekind. No module-finiteness hypothesis is needed. -/
theorem integralAffineCoordinate_isDedekindDomain
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (A : (integralAffineEtaleObjectProperty
      (X := Spec (CommRingCat.of R))).FullSubcategory) :
    IsDedekindDomain Γ(A.obj.left, ⊤) := by
  let : IsIntegral A.obj.left := A.property.2
  let : Algebra R Γ(A.obj.left, ⊤) :=
    (integralAffineCoordinateBaseMap R A).hom.toAlgebra
  have he : (algebraMap R Γ(A.obj.left, ⊤)).Etale :=
    integralAffineCoordinateBaseMap_etale R A
  let : Algebra.Etale R Γ(A.obj.left, ⊤) :=
    RingHom.etale_algebraMap.mp he
  exact IsDedekindDomain.of_essFiniteType_formallyUnramified R Γ(A.obj.left, ⊤)

variable (A)

/-- The fraction-field scalar structure of the coordinate presentation.
The lift is constructed once here, so users of the coordinate comparison
retain the same algebra value instead of expanding the localization lift. -/
@[instance_reducible]
noncomputable def integralAffineCoordinateFractionFieldAlgebra :
    Algebra (FractionRing R) (FractionRing Γ(A.obj.left, ⊤)) := by
  let S := Γ(A.obj.left, ⊤)
  have hS : IsDedekindDomain S := integralAffineCoordinate_isDedekindDomain R A
  let algRS : Algebra R S := (integralAffineCoordinateBaseMap R A).hom.toAlgebra
  have hE : Algebra.Etale R S :=
    RingHom.etale_algebraMap.mp (integralAffineCoordinateBaseMap_etale R A)
  let algRE : Algebra R (FractionRing S) :=
    ((algebraMap S (FractionRing S)).comp (algebraMap R S)).toAlgebra
  have hf : @FaithfulSMul R (FractionRing S) algRE.toSMul :=
    (faithfulSMul_iff_algebraMap_injective R (FractionRing S)).mpr
      ((IsFractionRing.injective S (FractionRing S)).comp
        (FaithfulSMul.algebraMap_injective R S))
  exact FractionRing.liftAlgebra R (FractionRing S)

/-- The fixed coordinate fraction-field lift extends the original
coordinate map, as witnessed by its scalar tower. -/
theorem integralAffineCoordinateFractionFieldAlgebra_isScalarTower :
    let S := Γ(A.obj.left, ⊤)
    let _ : Algebra R S := (integralAffineCoordinateBaseMap R A).hom.toAlgebra
    let algRE : Algebra R (FractionRing S) :=
      ((algebraMap S (FractionRing S)).comp (algebraMap R S)).toAlgebra
    let algKE := integralAffineCoordinateFractionFieldAlgebra R A
    @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul := by
  intro S algRS algRE algKE
  have hS : IsDedekindDomain S := integralAffineCoordinate_isDedekindDomain R A
  have hE : Algebra.Etale R S :=
    RingHom.etale_algebraMap.mp (integralAffineCoordinateBaseMap_etale R A)
  have hf : @FaithfulSMul R (FractionRing S) algRE.toSMul :=
    (faithfulSMul_iff_algebraMap_injective R (FractionRing S)).mpr
      ((IsFractionRing.injective S (FractionRing S)).comp
        (FaithfulSMul.algebraMap_injective R S))
  exact FractionRing.isScalarTower_liftAlgebra R (FractionRing S)

/-- The actual divisor and generic-unit quotient sheaves have canonically
isomorphic sections on every integral affine object of the small étale site. -/
noncomputable def integralAffineClosedPointDivisorGenericUnitObjectAddEquiv
    (R : Type u) [CommRing R] [IsDedekindDomain R] (hR : ¬ IsField R)
    [HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (A : (integralAffineEtaleObjectProperty
      (X := Spec (CommRingCat.of R))).FullSubcategory) :
    (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj (op A.obj) ≃+
      (affineGenericPointUnitQuotient R).obj.obj (op A.obj) := by
  let S := Γ(A.obj.left, ⊤)
  let : IsDedekindDomain S := integralAffineCoordinate_isDedekindDomain R A
  let algRS : Algebra R S := (integralAffineCoordinateBaseMap R A).hom.toAlgebra
  letI := algRS
  let : Algebra.Etale R S :=
    RingHom.etale_algebraMap.mp (integralAffineCoordinateBaseMap_etale R A)
  let algRE : Algebra R (FractionRing S) :=
    ((algebraMap S (FractionRing S)).comp (algebraMap R S)).toAlgebra
  letI := algRE
  let hRS : @IsScalarTower R S (FractionRing S) algRS.toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let hfaith : @FaithfulSMul R (FractionRing S) algRE.toSMul :=
    (faithfulSMul_iff_algebraMap_injective R (FractionRing S)).mpr
      ((IsFractionRing.injective S (FractionRing S)).comp
        (FaithfulSMul.algebraMap_injective R S))
  let algKE : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
  letI := algKE
  let hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul :=
    FractionRing.isScalarTower_liftAlgebra R _
  let e := integralAffineCoordinateEtaleObjIso R A
  let D := closedPointDivisorSheaf (Spec (CommRingCat.of R))
  let Q := affineGenericPointUnitQuotient R
  let eD := (D.obj.mapIso e.op).symm
  let eQ := Q.obj.mapIso e.op
  exact eD.addCommGroupIsoToAddEquiv.trans
    ((affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv
      (R := R) (S := S) hR).trans eQ.addCommGroupIsoToAddEquiv)

end EtaleCohomology

namespace EtaleCohomology

attribute [local irreducible] affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv

private theorem transport_object_comparison
    {C : Type (u + 1)} [Category.{u} C]
    (D Q : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    {A B A' B' : C} (a : A ≅ A') (b : B ≅ B') (f : A ⟶ B)
    (eA : D.obj (op A') ≃+ Q.obj (op A'))
    (eB : D.obj (op B') ≃+ Q.obj (op B'))
    (h : ∀ x, eA (ConcreteCategory.hom
        (D.map (a.inv ≫ f ≫ b.hom).op) x) =
      ConcreteCategory.hom (Q.map (a.inv ≫ f ≫ b.hom).op) (eB x))
    (x : D.obj (op B)) :
    ConcreteCategory.hom (Q.map a.hom.op)
      (eA (ConcreteCategory.hom (D.map a.inv.op)
        (ConcreteCategory.hom (D.map f.op) x))) =
    ConcreteCategory.hom (Q.map f.op)
      (ConcreteCategory.hom (Q.map b.hom.op)
        (eB (ConcreteCategory.hom (D.map b.inv.op) x))) := by
  let m := a.inv ≫ f ≫ b.hom
  have hd : D.map f.op ≫ D.map a.inv.op = D.map b.inv.op ≫ D.map m.op := by
    rw [← D.map_comp, ← D.map_comp]
    congr 1
    simp only [m, ← op_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hq : Q.map m.op ≫ Q.map a.hom.op = Q.map b.hom.op ≫ Q.map f.op := by
    rw [← Q.map_comp, ← Q.map_comp]
    congr 1
    simp only [m, ← op_comp, Iso.hom_inv_id_assoc]
  have hd' := ConcreteCategory.congr_hom hd x
  have hq' := ConcreteCategory.congr_hom hq
    (eB (ConcreteCategory.hom (D.map b.inv.op) x))
  simp only [ConcreteCategory.comp_apply] at hd' hq'
  rw [hd', h]
  exact hq'

/-- The canonical comparisons on integral affine étale objects commute with
all arrows of the integral affine basis. -/
theorem integralAffineClosedPointDivisorGenericUnitObject_naturality
    (R : Type u) [CommRing R] [IsDedekindDomain R] (hR : ¬ IsField R)
    [HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    {A B : (integralAffineEtaleObjectProperty
      (X := Spec (CommRingCat.of R))).FullSubcategory}
    (f : A ⟶ B)
    (x : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj (op B.obj)) :
    integralAffineClosedPointDivisorGenericUnitObjectAddEquiv R hR A
      (ConcreteCategory.hom
        ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.map f.hom.op) x) =
    ConcreteCategory.hom ((affineGenericPointUnitQuotient R).obj.map f.hom.op)
      (integralAffineClosedPointDivisorGenericUnitObjectAddEquiv R hR B x) := by
  let S := Γ(B.obj.left, ⊤)
  let T := Γ(A.obj.left, ⊤)
  let : IsDedekindDomain S := integralAffineCoordinate_isDedekindDomain R B
  let : IsDedekindDomain T := integralAffineCoordinate_isDedekindDomain R A
  let algRS : Algebra R S := (integralAffineCoordinateBaseMap R B).hom.toAlgebra
  let algRT : Algebra R T := (integralAffineCoordinateBaseMap R A).hom.toAlgebra
  let algST : Algebra S T := (Scheme.Hom.appTop f.hom.left).hom.toAlgebra
  let : Algebra.Etale R S :=
    RingHom.etale_algebraMap.mp (integralAffineCoordinateBaseMap_etale R B)
  let : Algebra.Etale R T :=
    RingHom.etale_algebraMap.mp (integralAffineCoordinateBaseMap_etale R A)
  let : IsAffine A.obj.left := A.property.1
  let : IsAffine B.obj.left := B.property.1
  let : Algebra.Etale S T := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale)
      (f := f.hom.left)).mp inferInstance)
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => by
    exact congrArg (fun φ => φ.hom r) (integralAffineCoordinateBaseMap_comp R f).symm
  let algRFS : Algebra R (FractionRing S) :=
    ((algebraMap S (FractionRing S)).comp (algebraMap R S)).toAlgebra
  let : @IsScalarTower R S (FractionRing S) algRS.toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRFS.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : @FaithfulSMul R (FractionRing S) algRFS.toSMul :=
    (faithfulSMul_iff_algebraMap_injective R (FractionRing S)).mpr
      ((IsFractionRing.injective S (FractionRing S)).comp
        (FaithfulSMul.algebraMap_injective R S))
  let algKS : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
  let : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul algKS.toSMul algRFS.toSMul :=
    FractionRing.isScalarTower_liftAlgebra R _
  let algRFT : Algebra R (FractionRing T) :=
    ((algebraMap T (FractionRing T)).comp (algebraMap R T)).toAlgebra
  let : @IsScalarTower R T (FractionRing T) algRT.toSMul
      (inferInstance : Algebra T (FractionRing T)).toSMul algRFT.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : @FaithfulSMul R (FractionRing T) algRFT.toSMul :=
    (faithfulSMul_iff_algebraMap_injective R (FractionRing T)).mpr
      ((IsFractionRing.injective T (FractionRing T)).comp
        (FaithfulSMul.algebraMap_injective R T))
  let algKT : Algebra (FractionRing R) (FractionRing T) := FractionRing.liftAlgebra R _
  let : @IsScalarTower R (FractionRing R) (FractionRing T)
      (inferInstance : Algebra R (FractionRing R)).toSMul algKT.toSMul algRFT.toSMul :=
    FractionRing.isScalarTower_liftAlgebra R _
  let algSFT : Algebra S (FractionRing T) :=
    ((algebraMap T (FractionRing T)).comp (algebraMap S T)).toAlgebra
  let : @IsScalarTower S T (FractionRing T) algST.toSMul
      (inferInstance : Algebra T (FractionRing T)).toSMul algSFT.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : @FaithfulSMul S (FractionRing T) algSFT.toSMul :=
    (faithfulSMul_iff_algebraMap_injective S (FractionRing T)).mpr
      ((IsFractionRing.injective T (FractionRing T)).comp
        (FaithfulSMul.algebraMap_injective S T))
  let algL : Algebra (FractionRing S) (FractionRing T) := FractionRing.liftAlgebra S _
  let : @IsScalarTower S (FractionRing S) (FractionRing T)
      (inferInstance : Algebra S (FractionRing S)).toSMul algL.toSMul algSFT.toSMul :=
    FractionRing.isScalarTower_liftAlgebra S _
  let D := (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj
  let Q := (affineGenericPointUnitQuotient R).obj
  let a := integralAffineCoordinateEtaleObjIso R A
  let b := integralAffineCoordinateEtaleObjIso R B
  let eA := affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv
    (R := R) (S := T) hR
  let eB := affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv
    (R := R) (S := S) hR
  have hm : integralAffineCoordinateArrow R f =
      affineEtaleSpecObjectMap (R := R) (S := S) (T := T) := by
    exact MorphismProperty.Over.Hom.ext (integralAffineCoordinateArrow_left_eq R f)
  have hn : ∀ y, eA (ConcreteCategory.hom (D.map (a.inv ≫ f.hom ≫ b.hom).op) y) =
      ConcreteCategory.hom (Q.map (a.inv ≫ f.hom ≫ b.hom).op) (eB y) := by
    intro y
    change eA (ConcreteCategory.hom (D.map (integralAffineCoordinateArrow R f).op) y) =
      ConcreteCategory.hom (Q.map (integralAffineCoordinateArrow R f).op) (eB y)
    rw [hm]
    exact affineEtaleClosedPointDivisorGenericUnitObject_naturality R S T hR y
  exact transport_object_comparison D Q a b f.hom eA eB hn x

/-- The actual divisor and generic-unit quotient presheaves are naturally
isomorphic after restriction to the integral affine étale basis. -/
noncomputable def integralAffineClosedPointDivisorGenericUnitNatIso
    (R : Type u) [CommRing R] [IsDedekindDomain R] (hR : ¬ IsField R)
    [HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})] :
    (integralAffineEtaleInclusion (Spec (CommRingCat.of R))).op ⋙
        (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj ≅
      (integralAffineEtaleInclusion (Spec (CommRingCat.of R))).op ⋙
        (affineGenericPointUnitQuotient R).obj := by
  refine NatIso.ofComponents
    (fun A => (integralAffineClosedPointDivisorGenericUnitObjectAddEquiv
      R hR A.unop).toAddCommGrpIso) ?_
  intro A B f
  ext x
  exact integralAffineClosedPointDivisorGenericUnitObject_naturality R hR f.unop x

/-- Over an affine Dedekind scheme, the actual closed-point divisor sheaf is
isomorphic to the actual generic-point unit quotient sheaf. -/
noncomputable def affineClosedPointDivisorGenericUnitSheafIso
    (R : Type u) [CommRing R] [IsDedekindDomain R] (hR : ¬ IsField R)
    [HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})] :
    closedPointDivisorSheaf (Spec (CommRingCat.of R)) ≅
      affineGenericPointUnitQuotient R := by
  let I := integralAffineEtaleInclusion (Spec (CommRingCat.of R))
  let : I.IsCoverDense (Spec (CommRingCat.of R)).smallEtaleTopology :=
    integralAffineEtaleInclusion_isCoverDense R
  let : I.Full := by
    dsimp [I, integralAffineEtaleInclusion]
    infer_instance
  exact Functor.IsCoverDense.sheafIso (G := I)
    (integralAffineClosedPointDivisorGenericUnitNatIso R hR)

end EtaleCohomology
