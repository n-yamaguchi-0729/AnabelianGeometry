/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverGenericCharacter
public import Nyll.AlgebraicCurves.Models.Kummer.CurveGenericKummerClass
public import Nyll.AlgebraicCurves.Models.Kummer.CurveKummerClassBasePoint
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorCharacter
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Normalization.Normal
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.FieldTheory.IsSepClosed

/-!
# The actual generic-divisor extension is the normalized Kummer class

The rational root in the actual power-divisor extension and a root in
the original normalized Kummer cover satisfy the same power equation.
Their original monodromy characters multiply that same nonzero root
by its Galois conjugate. Cancellation and generic-point detection
therefore identify the original derived classes. The final comparison
retains an arbitrary original geometric point.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open EtaleCohomology EtaleFundamentalGroups.Cohomology

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
  (M : CurveModel K F)

private theorem genericPoint_baseCoefficient
    (Ω : Type u) [Field Ω] [Algebra M.C.functionField Ω] :
    (Scheme.ΓSpecIso (.of K)).inv ≫
        ((Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
          M.C.fromSpecStalk (genericPoint M.C)) ≫ M.toBase).appTop ≫
        (Scheme.ΓSpecIso (.of Ω)).hom =
      CommRingCat.ofHom
        ((algebraMap M.C.functionField Ω).comp (baseToFunctionField M.toBase)) := by
  rw [Category.assoc, fromSpecStalk_genericPoint_comp_base,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

variable [IsAlgClosed K] (n : ℕ+) (hnK : IsUnit ((n : ℕ) : K))
  (u : Pic0.kummerUnits K F n) (D : Divisor K F)
  (hD : ∀ w : Place K F, w.ord (u.val : F) = (n : ℤ) * D w)

/-- At any actual separably closed generic point, the original
constant-root power-divisor extension is the original normalized-cover
cohomology class. No comparison of torsors or characters is assumed. -/
theorem constantGenericKummerDivisor_extClass_eq_kummerEtaleClass_generic
    (Ω : Type u) [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω] :
    let d := M.genericUnitDivisorH0Equiv.symm D
    let b := M.genericUnitsH0FieldEquiv.symm (Additive.ofMul u.val)
    let hb := M.genericUnitH0_powerDivisorEquation n u.val D hD
    (constantGenericKummerDivisorExtension_shortExact
      M.toBase n.pos hnK d b hb).extClass =
        M.kummerEtaleClass n u hnK
          (Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
            M.C.fromSpecStalk (genericPoint M.C)) := by
  intro d b hb
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let η := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
  let j := M.C.fromSpecStalk (genericPoint M.C)
  let ξ := η ≫ j
  let a := (constantGenericKummerDivisorExtension_shortExact
    M.toBase n.pos hnK d b hb).extClass
  obtain ⟨β, hβ, hχ⟩ := exists_root_h1Character_genericKummerDivisor
    M.toBase n.pos hnK d b hb Ω
  have hβ' : (β : Ω) ^ (n : ℕ) =
      algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F)) := by
    have h := hβ
    change β ^ (n : ℕ) = Units.map (algebraMap M.C.functionField Ω).toMonoidHom
      (genericPointUnitsH0Equiv M.C
        (M.genericUnitsH0FieldEquiv.symm (Additive.ofMul u.val))).toMul at h
    rw [M.genericPointUnitsH0Equiv_fieldUnit] at h
    exact congrArg Units.val h
  refine finiteH1_ext_genericFieldAction M.C Ω A a
    (M.kummerEtaleClass n u hnK ξ) ?_
  intro σ
  let g := FiniteEtale.fundamentalGroupHom j η
    (toAut (FiniteEtale.fiber η) Gal(Ω/M.C.functionField) σ)
  have hJ : FiniteEtale.fieldSourceAbsoluteGaloisHom M.C.functionField Ω j σ = g := by
    change FiniteEtale.fundamentalGroupHom j η
      (toAutHomeo (FiniteEtale.fiber η) Gal(Ω/M.C.functionField) σ) = _
    exact congrArg (FiniteEtale.fundamentalGroupHom j η) (toAutHomeo_apply _ σ)
  change h1Character A ξ a g = h1Character A ξ (M.kummerEtaleClass n u hnK ξ) g
  rw [M.h1Character_kummerEtaleClass n u hnK ξ]
  apply Subtype.ext
  apply Units.ext
  apply (baseToFunctionField M.toBase).injective
  apply (algebraMap M.C.functionField Ω).injective
  apply mul_right_cancel₀ β.ne_zero
  have hnew := congrArg Units.val (hχ σ)
  rw [genericPoint_baseCoefficient M Ω, hJ] at hnew
  exact hnew.trans
    (M.kummerMonodromyCharacter_generic_mul_root n u (β : Ω) hβ' hnK σ).symm

/-- The actual power-divisor extension is the original normalized
Kummer cohomology class at any original geometric base point. -/
theorem constantGenericKummerDivisor_extClass_eq_kummerEtaleClass
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M.C) :
    let d := M.genericUnitDivisorH0Equiv.symm D
    let b := M.genericUnitsH0FieldEquiv.symm (Additive.ofMul u.val)
    let hb := M.genericUnitH0_powerDivisorEquation n u.val D hD
    (constantGenericKummerDivisorExtension_shortExact
      M.toBase n.pos hnK d b hb).extClass = M.kummerEtaleClass n u hnK ξ := by
  intro d b hb
  let Ωg := SeparableClosure M.C.functionField
  have : IsSepClosure M.C.functionField Ωg :=
    separableClosure.isSepClosure M.C.functionField (AlgebraicClosure M.C.functionField)
  let ξg := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ωg)) ≫
    M.C.fromSpecStalk (genericPoint M.C)
  exact (M.constantGenericKummerDivisor_extClass_eq_kummerEtaleClass_generic
    n hnK u D hD Ωg).trans (M.kummerEtaleClass_basePoint n u hnK ξg ξ)

end AlgebraicCurve.CurveModel
