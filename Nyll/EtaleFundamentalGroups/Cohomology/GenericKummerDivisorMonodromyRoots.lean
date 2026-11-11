/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorRepresenter
public import Nyll.EtaleFundamentalGroups.Cohomology.GeometricUnitEvaluation
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Mathlib.CategoryTheory.Galois.Equivalence

/-!
# Actual generic roots of the original divisor monodromy

Evaluate the actual universal rational root at the actual generic
geometric fiber point of its original representing cover. Its power is
the specified original function-field unit. Original coefficient
translations and original generic Galois actions retain the actual
structural coefficient and the same field automorphism.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits Opposite
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  {n : ℕ} [NeZero n] (hn : 0 < n) (hnK : IsUnit (n : K))
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = n • d)
  (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] [IsSepClosed Ω]

local notation "j" => X.fromSpecStalk (genericPoint X)
local notation "η" => Spec.algebraMap X.functionField Ω
local notation "ξ" => η ≫ j
local notation "A" => AddCommGrpCat.of (Additive (rootsOfUnity n K))
local notation "P" => constantGenericKummerDivisorExtension c hn hnK d b hb
local notation "hP" => constantGenericKummerDivisorExtension_shortExact c hn hnK d b hb
local notation "V" => genericKummerDivisorCover c hn hnK d b hb
local notation "r" => genericKummerDivisorUniversalRoot c hn hnK d b hb

/-- The actual monodromy point lifted to the original generic-point
base change of the original representing cover. -/
def genericKummerDivisorMonodromyPoint
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ).obj.V) :
    Spec (.of Ω) ⟶ pullback (V).hom j :=
  pullback.lift (FiniteEtale.fiberObjEquivHom ξ V q).left η
    (FiniteEtale.fiberObjEquivHom ξ V q).w

/-- The root obtained from the same original monodromy point. -/
def genericKummerDivisorMonodromyRoot
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ).obj.V) : Ωˣ :=
  geometricUnitEvaluation (genericKummerDivisorMonodromyPoint c hn hnK d b hb Ω q) r

/-- Every actual monodromy root has the specified original
function-field unit as its nth power. -/
theorem genericKummerDivisorMonodromyRoot_pow
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ).obj.V) :
    genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω q ^ n =
      Units.map (algebraMap X.functionField Ω).toMonoidHom
        (genericPointUnitsH0Equiv X b).toMul := by
  let y := genericKummerDivisorMonodromyPoint c hn hnK d b hb Ω q
  let a := (genericPointUnitsH0Equiv X b).toMul
  have hy : y ≫ pullback.snd (V).hom j = η := pullback.lift_snd _ _ _
  have hη : (Scheme.ΓSpecIso (.of X.functionField)).inv ≫ (η).appTop ≫
      (Scheme.ΓSpecIso (.of Ω)).hom = CommRingCat.ofHom (algebraMap X.functionField Ω) := by
    change (Scheme.ΓSpecIso (.of X.functionField)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))).appTop ≫
      (Scheme.ΓSpecIso (.of Ω)).hom = _
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  calc
    geometricUnitEvaluation y r ^ n = geometricUnitEvaluation y (r ^ n) :=
      (map_pow (geometricUnitEvaluation y) r n).symm
    _ = geometricUnitEvaluation y
        (Units.map (((Scheme.ΓSpecIso (.of X.functionField)).inv ≫
          (pullback.snd (V).hom j).appTop).hom.toMonoidHom) a) :=
      congrArg (geometricUnitEvaluation y)
        (genericKummerDivisorUniversalRoot_pow c hn hnK d b hb)
    _ = Units.map (((Scheme.ΓSpecIso (.of X.functionField)).inv ≫
        (y ≫ pullback.snd (V).hom j).appTop ≫
        (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom) a :=
      geometricUnitEvaluation_structural (pullback.snd (V).hom j) y a
    _ = Units.map (algebraMap X.functionField Ω).toMonoidHom a := by
      rw [hy, hη]
      rfl

/-- The original coefficient torsor action multiplies the actual
generic root by its original structural root of unity. -/
theorem genericKummerDivisorMonodromyRoot_translation
    (ζ : rootsOfUnity n K)
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ).obj.V) :
    let _ := extensionMonodromyTorsor A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
    genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω
        (Multiplicative.ofAdd (Additive.ofMul ζ) • q) =
      Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫ (ξ ≫ c).appTop ≫
        (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom) (ζ : Kˣ) *
          genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω q := by
  intro coefficientTorsor
  let F := genericKummerDivisorLocalSystem c hn hnK d b hb
  let t : F ⟶ F := ObjectProperty.homMk
    (constantFiberTranslation A (P).f (P).g (P).zero (integerUnitSection X) (Additive.ofMul ζ))
  let k := (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse.map t
  let ke := (finiteEtaleToEtale X).map k
  let kg := ((etaleBaseChange j).map ke).left
  let p := FiniteEtale.fiberObjEquivHom ξ V q
  let y := genericKummerDivisorMonodromyPoint c hn hnK d b hb Ω q
  have ht : (FiniteEtale.fiber ξ).map k q =
      Multiplicative.ofAdd (Additive.ofMul ζ) • q :=
    translation_on_monodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
      (Additive.ofMul ζ) q
  have hp : p.left ≫ k.left =
      (FiniteEtale.fiberObjEquivHom ξ V
        (Multiplicative.ofAdd (Additive.ofMul ζ) • q)).left :=
    (congrArg (fun f => f.left) (FiniteEtale.fiberObjEquivHom_naturality ξ k q)).trans
      (congrArg (fun z => (FiniteEtale.fiberObjEquivHom ξ V z).left) ht)
  have hk₁ : kg ≫ pullback.fst (V).hom j = pullback.fst (V).hom j ≫ k.left := by
    dsimp only [kg, ke, etaleBaseChange]
    exact pullback.lift_fst _ _ _
  have hk₂ : kg ≫ pullback.snd (V).hom j = pullback.snd (V).hom j := by
    dsimp only [kg, ke, etaleBaseChange]
    exact pullback.lift_snd _ _ _
  have hy₁ : y ≫ pullback.fst (V).hom j = p.left := pullback.lift_fst _ _ _
  have hy₂ : y ≫ pullback.snd (V).hom j = η := pullback.lift_snd _ _ _
  have hy : genericKummerDivisorMonodromyPoint c hn hnK d b hb Ω
        (Multiplicative.ofAdd (Additive.ofMul ζ) • q) = y ≫ kg := by
    apply pullback.hom_ext
    · change pullback.lift _ η _ ≫ pullback.fst (V).hom j = _
      exact (pullback.lift_fst _ _ _).trans
        (hp.symm.trans
          ((congrArg (fun f => f ≫ k.left) hy₁.symm).trans
            ((Category.assoc y (pullback.fst (V).hom j) k.left).trans
              ((congrArg (fun f => y ≫ f) hk₁.symm).trans
                (Category.assoc y kg (pullback.fst (V).hom j)).symm))))
    · change pullback.lift _ η _ ≫ pullback.snd (V).hom j = _
      exact (pullback.lift_snd _ _ _).trans
        (hy₂.symm.trans
          ((congrArg (fun f => y ≫ f) hk₂.symm).trans
            (Category.assoc y kg (pullback.snd (V).hom j)).symm))
  have hbase : p.left ≫ ((V).hom ≫ c) = ξ ≫ c :=
    (Category.assoc p.left (V).hom c).symm.trans (congrArg (fun f => f ≫ c) p.w)
  calc
    genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω
        (Multiplicative.ofAdd (Additive.ofMul ζ) • q) =
      geometricUnitEvaluation (y ≫ kg) r := congrArg (fun z => geometricUnitEvaluation z r) hy
    _ = geometricUnitEvaluation y (Units.map kg.appTop.hom.toMonoidHom r) :=
      (geometricUnitEvaluation_pullback y kg r).symm
    _ = geometricUnitEvaluation y
        (Units.map (pullback.fst (V).hom j).appTop.hom.toMonoidHom
          (Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫
            ((V).hom ≫ c).appTop).hom.toMonoidHom) (ζ : Kˣ)) * r) :=
      congrArg (geometricUnitEvaluation y)
        (genericKummerDivisorUniversalRoot_translation c hn hnK d b hb ζ)
    _ = _ := by
      rw [map_mul, geometricUnitEvaluation_pullback, hy₁,
        geometricUnitEvaluation_structural, hbase]
      rfl

/-- Every automorphism of the actual generic geometric-point field changes
the universal root by that same field automorphism. The field need only
be separably closed; an algebraic closure is allowed in every characteristic. -/
theorem genericKummerDivisorMonodromyRoot_fieldAutomorphism
    (σ : Ω ≃ₐ[X.functionField] Ω)
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ).obj.V) :
    genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω
        (FiniteEtale.fundamentalGroupHom j η
          (FiniteEtale.fieldAutomorphismFiberAction X.functionField Ω σ) • q) =
      Units.map σ.toRingHom.toMonoidHom
        (genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω q) := by
  let y := genericKummerDivisorMonodromyPoint c hn hnK d b hb Ω q
  let ρ := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have hp := FiniteEtale.fundamentalGroupHom_point_of_point_action j η
    (FiniteEtale.fieldAutomorphismFiberAction X.functionField Ω σ) σ.toRingHom
    (FiniteEtale.fieldAutomorphismFiberAction_point X.functionField Ω σ) V q
  have hρ : ρ ≫ η = η := by
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) = _
    rw [← Spec.map_comp]
    apply congrArg (fun f : X.functionField →+* Ω => Spec.map (CommRingCat.ofHom f))
    exact RingHom.ext (fun a => σ.commutes a)
  have hy : genericKummerDivisorMonodromyPoint c hn hnK d b hb Ω
        (FiniteEtale.fundamentalGroupHom j η
          (FiniteEtale.fieldAutomorphismFiberAction X.functionField Ω σ) • q) = ρ ≫ y := by
    apply pullback.hom_ext
    · change pullback.lift _ η _ ≫ pullback.fst (V).hom j =
        (ρ ≫ pullback.lift _ η _) ≫ pullback.fst (V).hom j
      rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact hp
    · change pullback.lift _ η _ ≫ pullback.snd (V).hom j =
        (ρ ≫ pullback.lift _ η _) ≫ pullback.snd (V).hom j
      rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hρ]
  exact (congrArg (fun z => geometricUnitEvaluation z r) hy).trans
    (geometricUnitEvaluation_specMap y σ.toRingHom r)

/-- At a supplied separable closure the general point action is the
original absolute Galois action, with the same universal root. -/
theorem genericKummerDivisorMonodromyRoot_fieldSource
    [IsSepClosure X.functionField Ω] (σ : Gal(Ω/X.functionField))
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ).obj.V) :
    genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω
        (FiniteEtale.fieldSourceAbsoluteGaloisHom X.functionField Ω j σ • q) =
      Units.map σ.toRingHom.toMonoidHom
        (genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω q) :=
  genericKummerDivisorMonodromyRoot_fieldAutomorphism c hn hnK d b hb Ω σ q

end EtaleFundamentalGroups.Cohomology
