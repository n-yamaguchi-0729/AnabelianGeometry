/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalArithmeticScalarRoots
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationSquareNamedTransport
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticScalarFiniteBaseCoverIso

/-! # The same rooted arithmetic square transport over its actual scalar field

Specialize the already constructed rooted transport to degree two. Remove its
unit exponent before unpacking the dependent fibers. The original root
coordinates, torsors, Isom map, base point and scalar radical are retained,
and the same scalar field constructs the actual pulled-back cover isomorphism.
No comparison of arbitrary square roots or their complements is postulated.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Cohomology
open scoped RatFunc FintypeCatDiscrete
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
attribute [local instance] Classical.propDecidable

namespace AnabelianGeometry.WeightFiltration

local instance finiteSquareArithmeticChart_isOpenImmersion
    (k : Type) [Field k] (s : Finset (Projectivization k (k × k))) :
    IsOpenImmersion (show (rationalConfigurationOpen s : Scheme) ⟶
      (projectiveLineRatFuncModel k).C from (rationalConfigurationOpen s).ι) := by
  change IsOpenImmersion (rationalConfigurationOpen s).ι
  infer_instance

local instance (priority := 2000) finiteSquareSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

local instance finiteSquareOverCategory (S : Scheme) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S

local instance finiteSquareHasPullbacksAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteSquareStableUnderBaseChangeAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

/-- The original rooted square transport together with its actual finite-base
cover isomorphism; every previously selected witness remains in the scope. -/
def RationalConfigurationArithmeticSquareTransportWithFiniteBase
    (k κ : Type) [Field k] [CharZero k] [Field κ] [Algebra k κ]
    [IsAlgClosed κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k)))
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (us : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces
        (rationalConfigurationOpen s).ι) (2 : ℕ+))
    (ut : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces
        (rationalConfigurationOpen t).ι) (2 : ℕ+))
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂) : Prop :=
  let _ : Algebra (rationalConfigurationOpen s : Scheme).functionField Ω₁ :=
    rationalConfigurationOriginalAmbientAlgebra k κ s Ω₁
  let _ : Algebra (rationalConfigurationOpen t : Scheme).functionField Ω₂ :=
    rationalConfigurationOriginalAmbientAlgebra k κ t Ω₂
  let _ : Algebra (RatFunc k) Ω₁ := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω₁
  let _ : Algebra (RatFunc k) Ω₂ := rationalConfigurationArithmeticAmbientAlgebra k κ t Ω₂
  let _ : Algebra κ Ω₁ := rationalConfigurationConstantAmbientAlgebra k κ s Ω₁
  let _ : Algebra κ Ω₂ := rationalConfigurationConstantAmbientAlgebra k κ t Ω₂
  let _ : IsSepClosure (rationalConfigurationOpen s : Scheme).functionField Ω₁ :=
    (rationalConfigurationOriginalField_suppliers k κ s Ω₁).2.2.2.2.1
  let _ : IsSepClosure (rationalConfigurationOpen t : Scheme).functionField Ω₂ :=
    (rationalConfigurationOriginalField_suppliers k κ t Ω₂).2.2.2.2.1
  let hn : IsUnit ((2 : ℕ) : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (show (2 : ℕ) ≠ 0 from by decide))
  let M := projectiveLineRatFuncModel k
  let iS : (rationalConfigurationOpen s : Scheme) ⟶ M.C := (rationalConfigurationOpen s).ι
  let _ : IsOpenImmersion iS := finiteSquareArithmeticChart_isOpenImmersion k s
  let iT : (rationalConfigurationOpen t : Scheme) ⟶ M.C := (rationalConfigurationOpen t).ι
  let _ : IsOpenImmersion iT := finiteSquareArithmeticChart_isOpenImmersion k t
  let ξs := rationalConfigurationArithmeticBasePoint k κ s Ω₁
  let ξt := rationalConfigurationArithmeticBasePoint k κ t Ω₂
  let Fs := fiber ξs
  let Ft := fiber ξt
  let AS := M.openKummerCover (M.openBoundaryPlaces iS) (2 : ℕ+) hn us iS
    (rationalConfigurationOpen_denseRange k s) (M.place_not_mem_openBoundaryPlaces iS)
  let ATs := (coverTransportOfAutEquiv Fs Ft eP).functor.obj AS
  let ea := coverTransportFiberEquiv Fs Ft eP AS
  let AT := M.openKummerCover (M.openBoundaryPlaces iT) (2 : ℕ+) hn
    ut iT
    (rationalConfigurationOpen_denseRange k t) (M.place_not_mem_openBoundaryPlaces iT)
  ∃ ts : Torsor (rootsOfUnity (2 : ℕ) κ) (Fs.obj AS),
  ∃ tt : Torsor (rootsOfUnity (2 : ℕ) κ) (Ft.obj AT),
    letI := ts
    letI := tt
    letI := transportedFiberTorsor ea
    ArithmeticFiberRootCoordinate κ (rationalConfigurationOpen s : Scheme) Ω₁
      (2 : ℕ) AS ξs (algebraMap (RatFunc k) Ω₁ (us.val : RatFunc k))
      (algebraMap κ Ω₁) ts ∧
    ArithmeticFiberRootCoordinate κ (rationalConfigurationOpen t : Scheme) Ω₂
      (2 : ℕ) AT ξt
      (algebraMap (RatFunc k) Ω₂ (ut.val : RatFunc k))
      (algebraMap κ Ω₂) tt ∧
    (∀ (p : rationalConfigurationArithmeticGroup k κ s Ω₁)
        (ζ : rootsOfUnity (2 : ℕ) κ) (x : Fs.obj AS),
      p • (ζ • x) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
          ξs p).toRingHom (2 : ℕ) ζ • (p • x)) ∧
    (∀ (p : rationalConfigurationArithmeticGroup k κ t Ω₂)
        (ζ : rootsOfUnity (2 : ℕ) κ) (x : Ft.obj AT),
      p • (ζ • x) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
          ξt p).toRingHom (2 : ℕ) ζ • (p • x)) ∧
    (∀ (p : rationalConfigurationArithmeticGroup k κ t Ω₂)
        (ζ : rootsOfUnity (2 : ℕ) κ) (x : Ft.obj ATs),
      p • (ζ • x) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
          ξt p).toRingHom (2 : ℕ) ζ • (p • x)) ∧
    ∃ E : Ft.obj ATs ≃ Ft.obj AT,
      (∀ (ζ : rootsOfUnity (2 : ℕ) κ) x, E (ζ • x) = ζ • E x) ∧
      (∀ (δ : rationalConfigurationGeometricGroup k κ t Ω₂) x,
        E (rationalConfigurationGeometricInclusion k κ t Ω₂ δ • x) =
          rationalConfigurationGeometricInclusion k κ t Ω₂ δ • E x) ∧
      ∃ x₀ : Ft.obj ATs, ∃ a : kˣ, ∃ β : κˣ,
        β ^ (2 : ℕ) = Units.map (algebraMap k κ).toMonoidHom a ∧
        (∀ p : rationalConfigurationArithmeticGroup k κ t Ω₂,
          _root_.KummerTheory.rootQuotient (K := k) β
              (arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
                ξt p) =
            ((p • E (p⁻¹ • x₀)) /ₛ E x₀ : rootsOfUnity (2 : ℕ) κ).val) ∧
        let Kβ := quadraticScalarField k κ β
        let fT := (rationalConfigurationOpen t).ι ≫ π k 1
        let b := Limits.pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap k Kβ))) fT
        let xiG := (rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ω₂
        let xiE := scalarFiniteBasePoint k κ Kβ (rationalConfigurationOpen t : Scheme) fT xiG
        let hp := scalarFiniteBasePoint_comp_snd
          k κ Kβ (rationalConfigurationOpen t : Scheme) fT xiG
        ∃ j : (FiniteEtale.pullback b).obj ATs ≅ (FiniteEtale.pullback b).obj AT,
          ∀ x : (fiber xiE).obj ((FiniteEtale.pullback b).obj ATs),
            pointedPullbackFiberEquiv b xiE ξt hp AT ((fiber xiE).map j.hom x) =
              E (pointedPullbackFiberEquiv b xiE ξt hp ATs x)

/-- The existing rooted transport supplies the strengthened square conclusion. -/
theorem arithmeticSquareTransport_with_finiteBase_of_rootedScalar
    (k κ : Type) [Field k] [NumberField k] [Field κ] [Algebra k κ]
    [IsAlgClosed κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k)))
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (us : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces
        (rationalConfigurationOpen s).ι) (2 : ℕ+))
    (ut : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces
        (rationalConfigurationOpen t).ι) (2 : ℕ+))
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (h : RationalConfigurationArithmeticScalarTransportWithRoots
      k κ s t Ω₁ Ω₂ (2 : ℕ+) us ut eP) :
    RationalConfigurationArithmeticSquareTransportWithFiniteBase
      k κ s t Ω₁ Ω₂ us ut eP := by
  unfold RationalConfigurationArithmeticSquareTransportWithFiniteBase
  intro A_s A_t B_s B_t C_s C_t sep_s sep_t hn M iS hiS iT hiT ξs ξt Fs Ft AS ATs ea AT
  obtain ⟨u, hu⟩ := h
  have he : (u : ZMod ((2 : ℕ+) : ℕ)).val = 1 := zmod_two_unit_val_eq_one u
  have hpow : ut ^ (u : ZMod ((2 : ℕ+) : ℕ)).val = ut := by
    rw [he, pow_one]
  rw [hpow] at hu
  obtain ⟨ts, tt, hrootS, hrootT, hSsemi, hTsemi, hEsemi,
    E, hEμ, hEH, x₀, a, β, hβn, hβ⟩ := hu
  let : Torsor (rootsOfUnity 2 κ) (Fs.obj AS) := ts
  let : Torsor (rootsOfUnity 2 κ)
      ((fiber ((rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ω₂ ≫
        Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
          ((rationalConfigurationOpen t).ι ≫ π k 1))).obj AT) := tt
  let : Torsor (rootsOfUnity 2 κ)
      ((fiber ((rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ω₂ ≫
        Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
          ((rationalConfigurationOpen t).ι ≫ π k 1))).obj ATs) := transportedFiberTorsor ea
  refine ⟨ts, tt, hrootS, hrootT, hSsemi, hTsemi, hEsemi,
    E, hEμ, hEH, x₀, a, β, hβn, hβ, ?_⟩
  exact quadraticScalar_actual_finiteBase_coverIso
    k κ (rationalConfigurationOpen t : Scheme)
    ((rationalConfigurationOpen t).ι ≫ π k 1)
    ((rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ω₂)
    ATs AT hEsemi hTsemi E hEμ x₀ a β hβn hβ

end AnabelianGeometry.WeightFiltration
