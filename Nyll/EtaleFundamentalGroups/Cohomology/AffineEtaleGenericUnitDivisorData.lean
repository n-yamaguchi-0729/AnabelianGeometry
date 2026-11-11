/- 
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleClosedPointDivisorSections
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericUnitDivisorSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineGenericPointStalkComparison
public import Nyll.SchemeTheory.Affine.UnramifiedGenericFiber

/-!
# Affine étale generic-unit quotient sections

Compare the restriction of the base generic-unit quotient to an affine étale
object with the generic-unit quotient over the affine source, and combine this
with the closed-point divisor section equivalence.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open IsDedekindDomain
open EtaleFundamentalGroups.StrictHenselian
universe u
namespace EtaleCohomology

variable {R S : Type u} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]

/-- The component of the generic-stalk fraction-ring comparison, as an
AddEquiv on the top étale section over `Spec S`. -/
noncomputable def affineEtaleGenericStalkFractionRingSectionAddEquiv
    [algRE : Algebra R (FractionRing S)]
    [_hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [_hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul] :
    ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineGenericPointUnitQuotient R)).obj.obj
      (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) ≃+
    ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R)).obj.obj
      (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) := by
  let e := (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    AddCommGrpCat.{u}).mapIso (affineGenericPointUnitQuotientFractionRingIso R)
  let eP := (sheafToPresheaf (Spec (CommRingCat.of S)).smallEtaleTopology
    AddCommGrpCat.{u}).mapIso e
  exact etaleSectionIsoAddEquiv
    (A := ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineGenericPointUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
    (B := ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
    (eP.app (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))

/-- The actual generic-stalk comparison restricted to the étale site of an affine object. -/
noncomputable def affineEtaleGenericStalkFractionRingHom :
    (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineGenericPointUnitQuotient R) ⟶
    (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R) :=
  (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    AddCommGrpCat.{u}).map (affineGenericPointUnitQuotientFractionRingIso R).hom

omit [IsDedekindDomain S] in
/-- The restricted comparison commutes with every étale restriction map. -/
theorem affineEtaleGenericStalkFractionRingSection_naturality
    {V W : (Spec (CommRingCat.of S)).Etale} (m : V ⟶ W) :
    ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineGenericPointUnitQuotient R)).obj.map m.op ≫
        (affineEtaleGenericStalkFractionRingHom (R := R) (S := S)).hom.app (op V) =
    (affineEtaleGenericStalkFractionRingHom (R := R) (S := S)).hom.app (op W) ≫
      ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R)).obj.map m.op :=
  (affineEtaleGenericStalkFractionRingHom (R := R) (S := S)).hom.naturality m.op

/-- Sections of the base quotient restricted to `Spec S` identify with global
sections of the source's own generic-unit quotient. The map is the actual
fraction-field restriction isomorphism on the same étale object `Spec S`. -/
noncomputable def affineEtaleGenericUnitQuotientSectionAddEquiv
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul] :
    ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R)).obj.obj
      (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) ≃+
    (affineEtaleFractionRingUnitQuotient S).obj.obj
      (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) := by
  let e : (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R) ≅
        affineEtaleFractionRingUnitQuotient S :=
    affineEtaleFractionRingUnitQuotientIso R S
  let eP := (sheafToPresheaf (Spec (CommRingCat.of S)).smallEtaleTopology
    AddCommGrpCat.{u}).mapIso e
  exact etaleSectionIsoAddEquiv
    (A := ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
    (B := (affineEtaleFractionRingUnitQuotient S).obj.obj
      (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
    (eP.app (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))

/-- Under the generic-unit divisor comparison, the preceding same-object
section equivalence is exactly the existing finite-divisor equivalence. -/
theorem affineEtaleGenericUnitQuotientSectionAddEquiv_apply
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (D : HeightOneSpectrum S →₀ ℤ) :
    affineEtaleGenericUnitQuotientSectionAddEquiv (R := R) (S := S)
      (affineEtaleDivisorGenericUnitQuotientSectionEquiv R S D) =
    divisorGenericUnitQuotientGlobalSectionEquiv S D := by
  rw [affineEtaleDivisorGenericUnitQuotientSectionEquiv_apply
    (R := R) (S := S) (algRS := inferInstance) (algRE := algRE) (hRS := hRS)
    (algKE := algKE) (hKS := hKS)]
  dsimp (config := { instances := true }) only
    [affineEtaleGenericUnitQuotientSectionAddEquiv]
  rw [etaleSectionIsoAddEquiv_apply, Iso.app_hom,
    ← ConcreteCategory.comp_apply, Iso.inv_hom_id_app, ConcreteCategory.id_apply]
  rfl

/-- Actual sections of the base closed-point divisor sheaf on `Spec S` are
additively equivalent to global sections of the generic-unit quotient over
`Spec S`. This is the composition of the proved divisor equivalence and the
existing generic-unit divisor equivalence. -/
noncomputable def affineEtaleClosedPointDivisorToGenericUnitQuotientAddEquiv
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})] :
    ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) ≃+
    (affineEtaleFractionRingUnitQuotient S).obj.obj
      (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) :=
  (affineEtaleClosedPointDivisorSectionFinsuppAddEquiv
      (R := R) (S := S) hR).trans
    (divisorGenericUnitQuotientGlobalSectionEquiv S)

/-- Local comparison on the same affine étale object `Spec S`: actual sections
of the base closed-point divisor sheaf identify with sections of the base
generic-unit quotient restricted to that object. -/
noncomputable def affineEtaleClosedPointDivisorToRestrictedGenericUnitQuotientAddEquiv
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})] :
    ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) ≃+
    ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) :=
  (affineEtaleClosedPointDivisorSectionFinsuppAddEquiv
      (R := R) (S := S) hR).trans
    (affineEtaleDivisorGenericUnitQuotientSectionEquiv R S)

/-- On an affine étale object, the closed-point divisor sections identify with
sections of the restriction of the actual generic-point quotient sheaf. This
is the existing fraction-field comparison transported through the canonical
fraction-ring isomorphism from the generic stalk. -/
noncomputable def affineEtaleClosedPointDivisorToActualGenericUnitQuotientAddEquiv
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})] :
    ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) ≃+
    ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineGenericPointUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) := by
  exact (affineEtaleClosedPointDivisorToRestrictedGenericUnitQuotientAddEquiv
      (R := R) (S := S) hR).trans
    (affineEtaleGenericStalkFractionRingSectionAddEquiv (R := R) (S := S)).symm

/-- Compare the two actual base sheaves on the same affine étale object.
This transparent composite shares the bundled section groups of the
canonical top-object identification. -/
noncomputable def affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})] :
    ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) ≃+
    (affineGenericPointUnitQuotient R).obj.obj
      (op (Scheme.Etale.mk
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))) :=
  (affineEtaleClosedPointDivisorToActualGenericUnitQuotientAddEquiv
    (R := R) (S := S) hR).trans
      (etaleSectionIsoAddEquiv (etaleRestrictionTopObjectSectionIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (affineGenericPointUnitQuotient R)))

/-- Transport from the restricted actual generic quotient to the quotient
over the affine source, by first replacing the actual generic stalk with the
base fraction field and then applying the existing pullback-square
comparison. -/
noncomputable def affineEtaleActualGenericUnitQuotientToSourceAddEquiv
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul] :
    ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineGenericPointUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) ≃+
    (affineEtaleFractionRingUnitQuotient S).obj.obj
      (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) := by
  exact (affineEtaleGenericStalkFractionRingSectionAddEquiv (R := R) (S := S)).trans
    (affineEtaleGenericUnitQuotientSectionAddEquiv (R := R) (S := S))

/-- The composed AddEquiv is the same-object generic-unit restriction
comparison applied to the finite divisor read from the actual sheaf section. -/
theorem affineEtaleClosedPointDivisorToGenericUnitQuotient_is_restriction
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    affineEtaleGenericUnitQuotientSectionAddEquiv (R := R) (S := S)
      (affineEtaleDivisorGenericUnitQuotientSectionEquiv R S
        (affineEtaleClosedPointDivisorSectionFinsuppAddEquiv
          (R := R) (S := S) hR s)) =
    affineEtaleClosedPointDivisorToGenericUnitQuotientAddEquiv
      (R := R) (S := S) hR s := by
  rw [affineEtaleGenericUnitQuotientSectionAddEquiv_apply]
  rfl

/-- Applying the actual fraction-field restriction isomorphism to the local
base-quotient comparison gives the global quotient comparison over `Spec S`. -/
theorem affineEtaleClosedPointDivisorToRestrictedGenericUnitQuotient_compat
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    affineEtaleGenericUnitQuotientSectionAddEquiv (R := R) (S := S)
      (affineEtaleClosedPointDivisorToRestrictedGenericUnitQuotientAddEquiv
        (R := R) (S := S) hR s) =
    affineEtaleClosedPointDivisorToGenericUnitQuotientAddEquiv
      (R := R) (S := S) hR s := by
  rw [affineEtaleClosedPointDivisorToRestrictedGenericUnitQuotientAddEquiv]
  exact affineEtaleClosedPointDivisorToGenericUnitQuotient_is_restriction
    (R := R) (S := S) hR s

private theorem affineEtaleAddEquiv_trans_symm_apply
    {A B C D : AddCommGrpCat.{u}} (e : A ≃+ B) (f : B ≃+ C)
    (g : D ≃+ B) (x : D) :
    (e.trans f) (g.trans e.symm x) = f (g x) := by
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]

/-- The local actual-quotient comparison commutes with the shared restriction
components, and therefore recovers the source quotient comparison. -/
theorem affineEtaleClosedPointDivisorToActualGenericUnitQuotient_compat
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    affineEtaleActualGenericUnitQuotientToSourceAddEquiv (R := R) (S := S)
      (affineEtaleClosedPointDivisorToActualGenericUnitQuotientAddEquiv
        (R := R) (S := S) hR s) =
    affineEtaleClosedPointDivisorToGenericUnitQuotientAddEquiv
      (R := R) (S := S) hR s := by
  let e0 := affineEtaleGenericStalkFractionRingSectionAddEquiv (R := R) (S := S)
  let e1 := affineEtaleGenericUnitQuotientSectionAddEquiv (R := R) (S := S)
  let old := affineEtaleClosedPointDivisorToRestrictedGenericUnitQuotientAddEquiv
    (R := R) (S := S) hR
  have hcompat := affineEtaleClosedPointDivisorToRestrictedGenericUnitQuotient_compat
    (R := R) (S := S) hR s
  change (e0.trans e1) ((old.trans e0.symm) s) = _
  exact (affineEtaleAddEquiv_trans_symm_apply
    (A := ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineGenericPointUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
    (B := ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R)).obj.obj
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
    (C := (affineEtaleFractionRingUnitQuotient S).obj.obj
      (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
    (D := (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S))))
    e0 e1 old s).trans hcompat

/-- The combined actual-sheaf comparison reads each prime coefficient as the
coefficient of the corresponding generic-unit quotient section. -/
theorem affineEtaleClosedPointDivisorToGenericUnitQuotient_coefficient
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S))))
    (w : HeightOneSpectrum S) :
    genericUnitQuotientSectionCoefficient S w
      (affineEtaleClosedPointDivisorToGenericUnitQuotientAddEquiv
        (R := R) (S := S) hR s) =
    affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR w s := by
  change genericUnitQuotientSectionCoefficient S w
      (divisorGenericUnitQuotientSection S
        (affineEtaleClosedPointDivisorSectionFinsupp
          (R := R) (S := S) hR s)) = _
  rw [genericUnitQuotientSectionCoefficient_divisor]
  rfl

/-- The combined actual-sheaf/generic-quotient comparison is natural along a
tower of affine étale Dedekind domains. On generic sections the transition is
the existing fraction-field quotient map. -/
theorem affineEtaleClosedPointDivisorToGenericUnitQuotient_naturality
    {T : Type u} [CommRing T] [IsDedekindDomain T]
    [Algebra S T] [Algebra.Etale S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.Etale R T]
    [algST : Algebra S (FractionRing T)]
    [hST : @IsScalarTower S T (FractionRing T)
      (inferInstance : Algebra S T).toSMul
      (inferInstance : Algebra T (FractionRing T)).toSMul algST.toSMul]
    [algKT : Algebra (FractionRing S) (FractionRing T)]
    [hKT : @IsScalarTower S (FractionRing S) (FractionRing T)
      (inferInstance : Algebra S (FractionRing S)).toSMul
      algKT.toSMul algST.toSMul]
    [algRT : Algebra R (FractionRing T)]
    [_hRT : @IsScalarTower R T (FractionRing T)
      (inferInstance : Algebra R T).toSMul
      (inferInstance : Algebra T (FractionRing T)).toSMul algRT.toSMul]
    [algRKT : Algebra (FractionRing R) (FractionRing T)]
    [_hRKT : @IsScalarTower R (FractionRing R) (FractionRing T)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algRKT.toSMul algRT.toSMul]
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    affineEtaleClosedPointDivisorToGenericUnitQuotientAddEquiv
      (R := R) (S := T) hR
      (ConcreteCategory.hom
        ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.map
          (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op) s) =
    affineEtaleGenericUnitQuotientTopSectionMap S T
      (affineEtaleClosedPointDivisorToGenericUnitQuotientAddEquiv
        (R := R) (S := S) hR s) := by
  have hD := affineEtaleClosedPointDivisorSectionFinsuppAddEquiv_naturality
    (R := R) (S := S) (T := T) hR s
  let D := affineEtaleClosedPointDivisorSectionFinsuppAddEquiv
    (R := R) (S := S) hR s
  change divisorGenericUnitQuotientGlobalSectionEquiv T
      (affineEtaleClosedPointDivisorSectionFinsuppAddEquiv
        (R := R) (S := T) hR
        (ConcreteCategory.hom
          ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.map
            (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op) s)) =
    affineEtaleGenericUnitQuotientTopSectionMap S T
      (divisorGenericUnitQuotientGlobalSectionEquiv S D)
  rw [hD]
  exact (affineEtaleTopSectionMap_on_divisor (R := S) (S := T) D).symm

end EtaleCohomology

namespace EtaleCohomology

section AffineTower

variable (R S T : Type u)
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S]
  [CommRing T] [IsDedekindDomain T]
  [Algebra R S] [Algebra.Etale R S]
  [Algebra S T] [Algebra.Etale S T]
  [Algebra R T] [IsScalarTower R S T] [Algebra.Etale R T]
  [algRS : Algebra R (FractionRing S)]
  [hRS : @IsScalarTower R S (FractionRing S)
    (inferInstance : Algebra R S).toSMul
    (inferInstance : Algebra S (FractionRing S)).toSMul algRS.toSMul]
  [algKS : Algebra (FractionRing R) (FractionRing S)]
  [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
    (inferInstance : Algebra R (FractionRing R)).toSMul algKS.toSMul algRS.toSMul]
  [algST : Algebra S (FractionRing T)]
  [hST : @IsScalarTower S T (FractionRing T)
    (inferInstance : Algebra S T).toSMul
    (inferInstance : Algebra T (FractionRing T)).toSMul algST.toSMul]
  [algKT : Algebra (FractionRing S) (FractionRing T)]
  [hKT : @IsScalarTower S (FractionRing S) (FractionRing T)
    (inferInstance : Algebra S (FractionRing S)).toSMul algKT.toSMul algST.toSMul]
  [algRT : Algebra R (FractionRing T)]
  [hRT : @IsScalarTower R T (FractionRing T)
    (inferInstance : Algebra R T).toSMul
    (inferInstance : Algebra T (FractionRing T)).toSMul algRT.toSMul]
  [algRKT : Algebra (FractionRing R) (FractionRing T)]
  [hRKT : @IsScalarTower R (FractionRing R) (FractionRing T)
    (inferInstance : Algebra R (FractionRing R)).toSMul algRKT.toSMul algRT.toSMul]

/-- Fraction-field quotient comparisons commute with arrows between actual
affine objects of the base étale site. -/
theorem affineFractionQuotientObject_sections_tower :
    let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let j := Spec.map (CommRingCat.ofHom (algebraMap S T))
    let k := Spec.map (CommRingCat.ofHom (algebraMap R T))
    let W := (zariskiToEtale (Spec (CommRingCat.of T))).obj ⊤
    let WU := (zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤
    let t : (etalePostcompose j).obj W ⟶ WU :=
      (show (etalePostcompose j).obj W ⟶
          Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of S))) from
        MorphismProperty.Over.homMk ((etalePostcompose j).obj W).hom
          (Category.comp_id _)) ≫ (zariskiToEtaleTopIso _).inv
    let F := cokernel (etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
    let G := cokernel (etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S)))))
    F.obj.map (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op ≫
        F.obj.map (etalePostcomposeTopObjectIso k).hom.op ≫
        (affineEtaleFractionRingUnitQuotientIso R T).hom.hom.app (op W) =
      F.obj.map (etalePostcomposeTopObjectIso i).hom.op ≫
        (affineEtaleFractionRingUnitQuotientIso R S).hom.hom.app (op WU) ≫
        G.obj.map t.op ≫
        (affineEtaleFractionRingUnitQuotientIso S T).hom.hom.app (op W) := by
  intro i j k W WU t F G
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let p := Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S)))
  let q := Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap (FractionRing R) (FractionRing S)))
  let h := Spec.map (CommRingCat.ofHom
    (algebraMap (FractionRing S) (FractionRing T)))
  let l := Spec.map (CommRingCat.ofHom
    (algebraMap (FractionRing R) (FractionRing T)))
  have H : IsPullback p g i f :=
    EtaleFundamentalGroups.isPullback_spec_unramified_generic
      R S (FractionRing R) (FractionRing S)
  have H' : IsPullback q h j p :=
    EtaleFundamentalGroups.isPullback_spec_unramified_generic
      S T (FractionRing S) (FractionRing T)
  let : Etale g := MorphismProperty.of_isPullback (P := @Etale) H
    (show Etale i from inferInstance)
  let : Etale h := MorphismProperty.of_isPullback (P := @Etale) H'
    (show Etale j from inferInstance)
  have hi : j ≫ i = k := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact (IsScalarTower.algebraMap_apply R S T r).symm
  let : @IsScalarTower R S (FractionRing T)
      (inferInstance : Algebra R S).toSMul algST.toSMul algRT.toSMul :=
    IsScalarTower.of_algebraMap_eq fun r => by
      calc
        (algebraMap R (FractionRing T)) r =
            (algebraMap T (FractionRing T)) ((algebraMap R T) r) :=
          IsScalarTower.algebraMap_apply R T (FractionRing T) r
        _ = (algebraMap T (FractionRing T))
            ((algebraMap S T) ((algebraMap R S) r)) :=
          congrArg (algebraMap T (FractionRing T))
            (IsScalarTower.algebraMap_apply R S T r)
        _ = (algebraMap S (FractionRing T)) ((algebraMap R S) r) :=
          (IsScalarTower.algebraMap_apply S T (FractionRing T) _).symm
  let : @IsScalarTower R (FractionRing S) (FractionRing T)
      algRS.toSMul algKT.toSMul algRT.toSMul :=
    IsScalarTower.of_algebraMap_eq fun r => by
      calc
        (algebraMap R (FractionRing T)) r =
            (algebraMap S (FractionRing T)) ((algebraMap R S) r) :=
          IsScalarTower.algebraMap_apply R S (FractionRing T) r
        _ = (algebraMap (FractionRing S) (FractionRing T))
            ((algebraMap S (FractionRing S)) ((algebraMap R S) r)) :=
          IsScalarTower.algebraMap_apply S (FractionRing S) (FractionRing T) _
        _ = (algebraMap (FractionRing S) (FractionRing T))
            ((algebraMap R (FractionRing S)) r) :=
          congrArg (algebraMap (FractionRing S) (FractionRing T))
            (IsScalarTower.algebraMap_apply R S (FractionRing S) r).symm
  have hmaps : (algebraMap (FractionRing S) (FractionRing T)).comp
      (algebraMap (FractionRing R) (FractionRing S)) =
        algebraMap (FractionRing R) (FractionRing T) := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    change (algebraMap (FractionRing S) (FractionRing T))
      ((algebraMap (FractionRing R) (FractionRing S))
        ((algebraMap R (FractionRing R)) r)) = _
    rw [← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S),
      ← IsScalarTower.algebraMap_apply R (FractionRing S) (FractionRing T),
      ← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing T)]
  have hg : h ≫ g = l := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hmaps)
  have H'' : IsPullback q l k f :=
    EtaleFundamentalGroups.isPullback_spec_unramified_generic
      R T (FractionRing R) (FractionRing T)
  let : Etale l := MorphismProperty.of_isPullback (P := @Etale) H''
    (show Etale k from inferInstance)
  exact etaleRestrictionUnitQuotient_sections_tower_eq i j f p g q h H H' k l hi hg H''


/-- Naturality of a presheaf comparison with the fraction-unit quotient along an affine tower. -/
def affineQuotientSectionTowerNaturality
    (A : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})
    (e : A.obj ⟶ (affineEtaleFractionRingUnitQuotient R).obj) : Prop :=
    let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let j := Spec.map (CommRingCat.ofHom (algebraMap S T))
    let k := Spec.map (CommRingCat.ofHom (algebraMap R T))
    let W := (zariskiToEtale (Spec (CommRingCat.of T))).obj ⊤
    let WU := (zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤
    let t : (etalePostcompose j).obj W ⟶ WU :=
      (show (etalePostcompose j).obj W ⟶
          Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of S))) from
        MorphismProperty.Over.homMk ((etalePostcompose j).obj W).hom
          (Category.comp_id _)) ≫ (zariskiToEtaleTopIso _).inv
    let F := affineEtaleFractionRingUnitQuotient R
    let G := affineEtaleFractionRingUnitQuotient S
    let H := affineEtaleFractionRingUnitQuotient T
    let dRT : (etaleRestriction k AddCommGrpCat.{u}).obj F ≅ H :=
      affineEtaleFractionRingUnitQuotientIso R T
    let dRS : (etaleRestriction i AddCommGrpCat.{u}).obj F ≅ G :=
      affineEtaleFractionRingUnitQuotientIso R S
    let dST : (etaleRestriction j AddCommGrpCat.{u}).obj G ≅ H :=
      affineEtaleFractionRingUnitQuotientIso S T
    A.obj.map (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op ≫
        e.app (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap R T))))) ≫
        F.obj.map (etalePostcomposeTopObjectIso k).hom.op ≫
        dRT.hom.hom.app (op W) =
      (e.app (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap R S))))) ≫
        F.obj.map (etalePostcomposeTopObjectIso i).hom.op ≫
        dRS.hom.hom.app (op WU)) ≫
      (G.obj.map t.op ≫ dST.hom.hom.app (op W))

private theorem affineQuotient_sections_tower_natural
    (A : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})
    (e : A.obj ⟶ (affineEtaleFractionRingUnitQuotient R).obj) :
    affineQuotientSectionTowerNaturality R S T A e := by
  unfold affineQuotientSectionTowerNaturality
  intro i j k W WU t F G H dRT dRS dST
  have ht := affineFractionQuotientObject_sections_tower R S T
  exact naturality_section_composite e
    (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op _ _ _ ht


private theorem affineSection_square_apply
    {A B C Z : AddCommGrpCat.{u}}
    (a : A ⟶ B) (b : B ⟶ Z) (c : A ⟶ C) (d : C ⟶ Z)
    (w : a ≫ b = c ≫ d) (s : A) :
    ConcreteCategory.hom b (ConcreteCategory.hom a s) =
      ConcreteCategory.hom d (ConcreteCategory.hom c s) := by
  exact (ConcreteCategory.comp_apply a b s).symm.trans
    ((ConcreteCategory.congr_hom w s).trans (ConcreteCategory.comp_apply c d s))


/-- Evaluate affine tower naturality on a section before specializing the source sheaf. -/
theorem affineQuotient_sections_tower_apply
    (A : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})
    (e : A.obj ⟶ (affineEtaleFractionRingUnitQuotient R).obj)
    (s : A.obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let j := Spec.map (CommRingCat.ofHom (algebraMap S T))
    let k := Spec.map (CommRingCat.ofHom (algebraMap R T))
    let W := (zariskiToEtale (Spec (CommRingCat.of T))).obj ⊤
    let WU := (zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤
    let t : (etalePostcompose j).obj W ⟶ WU :=
      (show (etalePostcompose j).obj W ⟶
          Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of S))) from
        MorphismProperty.Over.homMk ((etalePostcompose j).obj W).hom
          (Category.comp_id _)) ≫ (zariskiToEtaleTopIso _).inv
    let b : A.obj.obj
          (op (Scheme.Etale.mk k)) ⟶
        (affineEtaleFractionRingUnitQuotient T).obj.obj (op W) :=
      e.app (op (Scheme.Etale.mk k)) ≫
        (affineEtaleFractionRingUnitQuotient R).obj.map
          (etalePostcomposeTopObjectIso k).hom.op ≫
        (affineEtaleFractionRingUnitQuotientIso R T).hom.hom.app (op W)
    let c : A.obj.obj
          (op (Scheme.Etale.mk i)) ⟶
        (affineEtaleFractionRingUnitQuotient S).obj.obj (op WU) :=
      e.app (op (Scheme.Etale.mk i)) ≫
        (affineEtaleFractionRingUnitQuotient R).obj.map
          (etalePostcomposeTopObjectIso i).hom.op ≫
        (affineEtaleFractionRingUnitQuotientIso R S).hom.hom.app (op WU)
    let d : (affineEtaleFractionRingUnitQuotient S).obj.obj (op WU) ⟶
        (affineEtaleFractionRingUnitQuotient T).obj.obj (op W) :=
      (affineEtaleFractionRingUnitQuotient S).obj.map t.op ≫
        (affineEtaleFractionRingUnitQuotientIso S T).hom.hom.app (op W)
    ConcreteCategory.hom b
        (ConcreteCategory.hom (A.obj.map
          (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op) s) =
      ConcreteCategory.hom d (ConcreteCategory.hom c s) := by
  intro i j k W WU t b c d
  exact affineSection_square_apply
    (A := A.obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S))))
    (B := A.obj.obj
      (op (Scheme.Etale.mk k)))
    (C := (affineEtaleFractionRingUnitQuotient S).obj.obj (op WU))
    (Z := (affineEtaleFractionRingUnitQuotient T).obj.obj (op W))
    (A.obj.map
      (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op)
    b c d (affineQuotient_sections_tower_natural R S T A e) s


/-- The actual generic-stalk comparison respects arrows of affine étale objects. -/
theorem affineActualGenericQuotientObject_sections_tower :
    affineQuotientSectionTowerNaturality R S T
      (affineGenericPointUnitQuotient R)
      (show affineGenericPointUnitQuotient R ≅ affineEtaleFractionRingUnitQuotient R from
        affineGenericPointUnitQuotientFractionRingIso R).hom.hom :=
  affineQuotient_sections_tower_natural R S T
    (affineGenericPointUnitQuotient R)
    (show affineGenericPointUnitQuotient R ≅ affineEtaleFractionRingUnitQuotient R from
      affineGenericPointUnitQuotientFractionRingIso R).hom.hom


end AffineTower

end EtaleCohomology

namespace EtaleCohomology
variable {R S : Type u} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]

/-- Identify actual sections on an affine object with the generic-unit
quotient over that object's own spectrum. The inverse top-object identification
is followed by the same restricted-section comparison used for divisors. -/
noncomputable def affineEtaleGenericUnitObjectToSourceAddEquiv
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul] :
    (affineGenericPointUnitQuotient R).obj.obj
      (op (Scheme.Etale.mk
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))) ≃+
    (affineEtaleFractionRingUnitQuotient S).obj.obj
      (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) :=
  etaleSectionIsoAddEquiv (etaleRestrictionComparisonSectionIso
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (affineGenericPointUnitQuotientFractionRingIso R)
    (affineEtaleFractionRingUnitQuotientIso R S))

end EtaleCohomology
