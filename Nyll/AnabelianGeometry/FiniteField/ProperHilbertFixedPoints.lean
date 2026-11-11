/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.PicardNormAnnihilation
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertMonodromyFixed
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertMonodromyNorm
public import Nyll.AlgebraicCurves.Models.ConstantPointPlace
public import Nyll.AlgebraicCurves.Models.ConstantFrobeniusEmbedding
public import Nyll.AlgebraicCurves.Models.Construction.ConstantModelGenericSource
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.EtaleFundamentalGroups.Normalization.ConstantHilbertClassField
public import Nyll.EtaleFundamentalGroups.GaloisCovers.GeometricFiniteGaloisMonodromy
public import Nyll.EtaleFundamentalGroups.GaloisCovers.GenericLiftFieldEmbedding
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceStalk
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteConstantsInClosure
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantReindex
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ConstantHilbertPicard
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertClassFieldConstruction
public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension

/-!
# Native proper Frobenius fixedness kills the actual pointed Hilbert image

An element fixed in the original geometric abelianization gives an actual
fixed upper Hilbert--Picard class. The upper constant extension is chosen
with degree equal to its period times the cardinality of the original
geometric Picard fixed subgroup. Its actual norm vanishes, so norm
reciprocity makes the original source act trivially on the lower pointed
Hilbert field. All finite covers and coefficient squares are constructed
from the given proper curve and the specified ambient field.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve EtaleFundamentalGroups
open ProCGroups.Abelian
open scoped IsMulCommutative

namespace AnabelianGeometry.FiniteField

attribute [local instance]
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

attribute [local instance] AlgebraicGeometry.FiniteEtale.genericPoint_isDominant

private theorem originalCurveModel_genericSource
    {k : Type uGeom} [Field k] {C : Scheme.{uGeom}} [IsIntegral C]
    (c : C ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    let M : CurveModel k C.functionField := CurveModel.ofSmoothProperCurve c
    Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
        M.C.fromSpecStalk (genericPoint M.C) = C.fromSpecStalk (genericPoint C) := by
  intro baseAlgebra M
  change Spec.map (𝟙 (.of C.functionField)) ≫ C.fromSpecStalk (genericPoint C) = _
  rw [Spec.map_id, Category.id_comp]

private theorem semilinearRestrictScalars_pow_fixed
    (k K L : Type uGeom) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    (ψ : L ≃ₐ[K] L) (w : Place k L)
    (hw : SemilinearAut.ofAlgAut (ψ.restrictScalars k) • w = w) (n : ℕ) :
    SemilinearAut.ofAlgAut ((ψ ^ n).restrictScalars k) • w = w := by
  let f : (L ≃ₐ[K] L) →* SemilinearAut k L :=
    SemilinearAut.ofAlgAut.comp (AlgEquiv.restrictScalarsHom k)
  have hfixed (t : ℕ) : f ψ ^ t • w = w := by
    induction t with
    | zero => rw [pow_zero, one_smul]
    | succ t ih =>
        rw [pow_succ', mul_smul, ih]
        exact hw
  change f (ψ ^ n) • w = w
  rw [map_pow]
  exact hfixed n

-- The final fixedness and norm calculation uses only abstract fields and groups.
-- The proper-curve construction below supplies its monodromy and norm theorem.
private theorem hilbertSource_fixed_of_native_fixed_and_annihilating_norm
    {k E K L Ω : Type uGeom}
    [Field k] [Finite k] [Field E] [Field K] [Field L] [Field Ω]
    [algkK : Algebra k K] [algkL : Algebra k L] [algKL : Algebra K L]
    [towerKL : IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Algebra k E] [Module.Finite k E] [Algebra E L] [IsScalarTower k E L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L] [HasPrincipalDivisors E L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    {P Γ : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [Group Γ]
    (v : Place k K) (hv : v.deg = 1) (w : Place E L) (hw : w.deg = 1)
    (hrestrict : w.restrictConstants K = v) :
    let H₀ := FunctionField.hilbertClassField k K {v} (Finset.singleton_nonempty _)
    let H₁ := FunctionField.hilbertClassField k L {w.forgetConstants (K := k)}
      (Finset.singleton_nonempty _)
    ∀ (q : Gal(Ω/K) →* P) (π : P →* Γ)
      (i₀ : H₀.val →ₐ[K] Ω) (i₁ : H₁.val →ₐ[L] Ω)
      (χ : π.ker →ₜ* Gal(H₁.val/L))
      (_ : ∀ (σ : Gal(Ω/K)) (hσ : π (q σ) = 1) (a : H₁.val),
        i₁ (χ ⟨q σ, hσ⟩ a) = σ (i₁ a))
      (ρ : Gal(Ω/K)) (ψ : L ≃ₐ[k] L) (g : SemilinearAut E L)
      (_ : ψ.toRingEquiv = SemilinearAut.toRingAut g)
      (_ : ∀ a : L, ρ (algebraMap L Ω a) = algebraMap L Ω (ψ a))
      (_ : SemilinearAut.ofAlgAut ψ • w.forgetConstants (K := k) =
        w.forgetConstants (K := k))
      (_ : ∀ x : Pic E L, H1Gm.degree E L x = 0 → g • x = x →
        Pic.normConstants k E K L x = 0)
      (σ : Gal(Ω/K)) (hσ : π (q σ) = 1),
      TopologicalAbelianization.mk π.ker
          (MulAut.conjNormal (q ρ) ⟨q σ, hσ⟩) =
        TopologicalAbelianization.mk π.ker ⟨q σ, hσ⟩ →
      ∀ a : H₀.val, σ (i₀ a) = i₀ a := by
  intro H₀ H₁ q π i₀ i₁ χ hχ ρ ψ g hfield hambient hplace hnorm σ hσ hfixed
  have hpicfixed := FunctionField.constantHilbertPicard_fixed_of_native_conjugation
    w hw q π i₁ χ hχ ρ ψ g hfield hambient hplace σ hσ hfixed
  let x := ((FunctionField.constantHilbertClassFieldGaloisEquivPic0 k E L w hw)
    (χ ⟨q σ, hσ⟩)).toAdd
  have hPicfixed : g • H1Gm.ofPic0 E L x = H1Gm.ofPic0 E L x :=
    (H1Gm.ofPic0_smul g x).symm.trans (congrArg (H1Gm.ofPic0 E L) hpicfixed)
  have hnormzero : Pic.normConstants k E K L (H1Gm.ofPic0 E L x) = 0 :=
    hnorm (H1Gm.ofPic0 E L x) (H1Gm.degree_ofPic0 E L x) hPicfixed
  let aH₀Ω : Algebra H₀.val Ω := i₀.toRingHom.toAlgebra
  have hKH₀Ω : IsScalarTower K H₀.val Ω :=
    IsScalarTower.of_algebraMap_eq (fun a => (i₀.commutes a).symm)
  let σ₀ := AlgEquiv.restrictNormalHom H₀.val σ
  have hσ₀ (a : H₀.val) : i₀ (σ₀ a) = σ (i₀ a) :=
    AlgEquiv.restrictNormal_commutes σ H₀.val a
  have hnormsource := FunctionField.constantHilbertPicard_norm_of_common_source
    (k := k) (C := k) (E := E) (K := K) (L := L)
      v hv w hw hrestrict Ω i₀ i₁ σ.toRingEquiv σ₀
      (χ ⟨q σ, hσ⟩) hσ₀ (hχ σ hσ)
  have hPiczero :
      ((FunctionField.constantHilbertClassFieldGaloisEquivPic0 k k K v hv) σ₀).toAdd = 0 :=
    (H1Gm.ofPic0_injective k K)
      (hnormsource.trans (hnormzero.trans (map_zero (H1Gm.ofPic0 k K)).symm))
  have hσzero : σ₀ = 1 := by
    apply (FunctionField.constantHilbertClassFieldGaloisEquivPic0 k k K v hv).injective
    exact (Multiplicative.toAdd.injective hPiczero).trans
      (map_one (FunctionField.constantHilbertClassFieldGaloisEquivPic0 k k K v hv)).symm
  intro a
  rw [← hσ₀, hσzero]
  rfl

/-- Fixedness of an original geometric abelian source class under an
actual Frobenius lift forces that source to fix every coefficient of the
actual pointed Hilbert field. No finite family, norm comparison, or upper
fixed-point theorem is an input. -/
theorem properHilbertSource_fixed_of_geometricAbelianization_fixed
    (k κ : Type uGeom) [Field k] [Fintype k] [Field κ]
    [Algebra k κ] [IsSepClosure k κ] [IsAlgClosed κ]
    {C : Scheme.{uGeom}} [IsIntegral C] [IsNormalIntegral C] [IsLocallyNoetherian C]
    (c : C ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c] :
    let _ : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    let _ : IsCurveOver k C.functionField :=
      isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
        (RingEquiv.refl _) (fun _ => rfl)
    ∀ [Algebra (RatFunc k) C.functionField]
      [IsScalarTower k (RatFunc k) C.functionField]
      [FunctionField k C.functionField]
      (v : Place k C.functionField) (_ : v.deg = 1),
    let H₀ := FunctionField.hilbertClassField k C.functionField {v}
      (Finset.singleton_nonempty _)
    ∀ (Ω : Type uGeom) [Field Ω] [Algebra k Ω] [Algebra C.functionField Ω] [Algebra κ Ω]
      [IsScalarTower k C.functionField Ω] [IsScalarTower k κ Ω]
      [IsSepClosure C.functionField Ω] [IsSepClosed Ω]
      (i₀ : H₀.val →ₐ[C.functionField] Ω),
    let j := C.fromSpecStalk (genericPoint C)
    let π := arithmeticFundamentalGroupHom k κ c (ξ C.functionField Ω ≫ j)
    let q := fieldSourceAbsoluteGaloisHom C.functionField Ω j
    ∀ (ρ σ : Gal(Ω/C.functionField)) (n : ℕ) (_ : n ≠ 0)
      (_ : ∀ a : κ, ρ (algebraMap κ Ω a) =
        algebraMap κ Ω (((FiniteField.frobeniusAlgEquivOfAlgebraic k κ) ^ n) a))
      (hσ : π (q σ) = 1),
      TopologicalAbelianization.mk π.toMonoidHom.ker
          (MulAut.conjNormal (q ρ) ⟨q σ, hσ⟩) =
        TopologicalAbelianization.mk π.toMonoidHom.ker ⟨q σ, hσ⟩ →
      ∀ a : H₀.val, σ (i₀ a) = i₀ a := by
  intro akK hcurve aRK hkRK hfunction v hv H₀ Ω hΩ akΩ aKΩ aκΩ hkKΩ hkκΩ
    hsepΩ hclosedΩ i₀ j π q ρ σ n hn hρ hσ hfixed
  let K : Type uGeom := C.functionField
  have hft : Algebra.EssFiniteType k K := essFiniteType_functionField c
  let M₀ : CurveModel k K := CurveModel.ofSmoothProperCurve c
  have hM₀geom : GeometricallyIntegral M₀.toBase := by
    change GeometricallyIntegral c
    infer_instance
  let Cκ := pullback c (specMap k κ)
  let cκ := pullback.snd c (specMap k κ)
  have hCκIntegral : IsIntegral Cκ := isIntegral_pullback_Spec_field k c (specMap k κ)
  let aκF : Algebra κ Cκ.functionField := (baseToFunctionField cκ).toAlgebra
  have hcurveκ : IsCurveOver κ Cκ.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cκ
      (RingEquiv.refl _) (fun _ => rfl)
  let M : CurveModel κ Cκ.functionField := CurveModel.ofSmoothProperCurve cκ
  let e : M.C ≅ pullback M₀.toBase (specMap k κ) := Iso.refl _
  have he : e.hom ≫ pullback.snd M₀.toBase (specMap k κ) = M.toBase :=
    Category.id_comp _
  let S := M₀.constantPicardZeroFixedSubgroup M e he n
  have hSfinite : Finite S := M₀.finite_constantPicardZeroFixedSubgroup M e he n hn
  let d := n * Nat.card S
  have hd : d ≠ 0 := Nat.mul_ne_zero hn Nat.card_pos.ne'
  have hdinst : NeZero d := ⟨hd⟩
  let E := FunctionField.finiteConstantsInClosure k κ d
  have hEfinite : Finite E := FunctionField.finite_finiteConstantsInClosure k κ d
  let hEfintype : Fintype E := Fintype.ofFinite E
  have hEdegree : Module.finrank k E = n * Nat.card S :=
    FunctionField.finrank_finiteConstantsInClosure k κ d
  let CE := pullback c (specMap k E)
  let cE := pullback.snd c (specMap k E)
  have hCEIntegral : IsIntegral CE := isIntegral_pullback_Spec_field k c (specMap k E)
  let L : Type uGeom := CE.functionField
  let aEL : Algebra E L := (baseToFunctionField cE).toAlgebra
  let ME : CurveModel E L := CurveModel.ofSmoothProperCurve cE
  let akL : Algebra k L := ((algebraMap E L).comp (algebraMap k E)).toAlgebra
  have hkEL : IsScalarTower k E L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let aKL : Algebra K L := M₀.constantModelAlgebra ME (Iso.refl _)
  have hkKL : IsScalarTower k K L :=
    M₀.constantModel_isScalarTower ME (Iso.refl _) (Category.id_comp _)
  have hKL : FiniteDimensional K L ∧ _root_.IsGalois K L ∧
      Module.finrank K L = Module.finrank k E :=
    M₀.constantFiniteExtension_properties M e he E
  have hKLfinite : FiniteDimensional K L := hKL.1
  have hKLgalois : _root_.IsGalois K L := hKL.2.1
  have hKLcyclic : IsCyclic Gal(L/K) := isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨M₀.constantFiniteFrobenius M e he E, M₀.zpowers_constantFiniteFrobenius_eq_top M e he E⟩
  have hKLab : IsAbelianGalois K L := IsAbelianGalois.of_isCyclic K L
  have hcurveE : IsCurveOver E L :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cE
      (RingEquiv.refl _) (fun _ => rfl)
  have hprincipalL : HasPrincipalDivisors k L :=
    FunctionField.hasPrincipalDivisors_of_extendedConstants k E L
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfunctionL : FunctionField k L := presentation.property.2
  obtain ⟨(w : Place E L), hw, hrestrict, _, _, hwforget⟩ :=
    M₀.exists_constantFinitePointPlace M e he E v hv
  let aEκ : Algebra E κ := IntermediateField.toAlgebra E.toIntermediateField
  let aEΩ : Algebra E Ω := ((algebraMap κ Ω).comp (algebraMap E κ)).toAlgebra
  let smulEκ : SMul E κ := aEκ.toSMul
  let smulEΩ : SMul E Ω := aEΩ.toSMul
  have hEκΩ : IsScalarTower E κ Ω :=
    IsScalarTower.of_algebraMap_eq (R := E) (S := κ) (A := Ω) (fun _ => rfl)
  have hkEΩ : IsScalarTower k E Ω :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := E) (A := Ω) (fun a => by
    rw [IsScalarTower.algebraMap_apply k κ Ω,
      IsScalarTower.algebraMap_apply k E κ]; rfl)
  have hjbase : j ≫ c = ξ k K := fromSpecStalk_genericPoint_comp_base c
  obtain ⟨iL, hiLC, hiLE⟩ := exists_constantGenericFunctionFieldEmbedding
    k K E Ω c j hjbase
  have hgeneric : Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ j =
      CE.fromSpecStalk (genericPoint CE) ≫ pullback.fst c (specMap k E) := by
    have h := M₀.constantModelAlgebra_genericSource ME (Iso.refl _)
    rw [originalCurveModel_genericSource c, originalCurveModel_genericSource cE] at h
    change Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        C.fromSpecStalk (genericPoint C) =
      CE.fromSpecStalk (genericPoint CE) ≫ (𝟙 CE) ≫ pullback.fst c (specMap k E) at h
    simpa only [Category.id_comp] using h
  have hiLK : iL.comp (algebraMap K L) = algebraMap K Ω := by
    have hspec : Spec.map (CommRingCat.ofHom (iL.comp (algebraMap K L))) =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      apply (cancel_mono j).mp
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hgeneric]
      exact hiLC
    exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of Ω => f.hom)
      (Spec.map_injective hspec)
  let aLΩ : Algebra L Ω := iL.toAlgebra
  have hKLΩ : IsScalarTower K L Ω :=
    IsScalarTower.of_algebraMap_eq (fun a => (RingHom.congr_fun hiLK a).symm)
  have hELΩ : IsScalarTower E L Ω :=
    IsScalarTower.of_algebraMap_eq (fun a => (RingHom.congr_fun hiLE a).symm)
  let H₁ := FunctionField.hilbertClassField k L {w.forgetConstants (K := k)}
    (Finset.singleton_nonempty _)
  let aKH₁ : Algebra K H₁.val := ((algebraMap L H₁.val).comp (algebraMap K L)).toAlgebra
  let mKH₁ : Module K H₁.val := aKH₁.toModule
  have hKLH₁ : IsScalarTower K L H₁.val := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hLH₁finite : FiniteDimensional L H₁.val :=
    ClassFieldTheory.FiniteAbelianLocalExtension.finiteDimensional H₁
  have hKH₁finite : FiniteDimensional K H₁.val := Module.Finite.trans L H₁.val
  let i₁ : H₁.val →ₐ[L] Ω := IsSepClosed.lift
  have hnormEtale := constantHilbertClassField_normalization_finiteEtale k E cE w
  have hEtaleH₁ : IsFiniteEtale (CE.genericExtensionMorphism H₁.val).fromNormalization :=
    hnormEtale.2
  have hfiniteBase : IsFiniteEtale (specMap k E) := constantField_specMap_isFiniteEtale k E
  let W : FiniteEtale C := FiniteEtale.mk
    ((CE.genericExtensionMorphism H₁.val).fromNormalization ≫
      pullback.fst c (specMap k E))
  let η := (CE.genericExtensionMorphism H₁.val).toNormalization
  have hηPreimmersion : IsPreimmersion η :=
    genericExtensionNormalization_toNormalization_isPreimmersion CE H₁.val
  have hη : η ≫ W.hom = Spec.map (CommRingCat.ofHom (algebraMap K H₁.val)) ≫ j := by
    change η ≫ (CE.genericExtensionMorphism H₁.val).fromNormalization ≫
      pullback.fst c (specMap k E) = _
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
    change (Spec.map (CommRingCat.ofHom (algebraMap L H₁.val)) ≫
      CE.fromSpecStalk (genericPoint CE)) ≫ pullback.fst c (specMap k E) = _
    rw [Category.assoc, ← hgeneric, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hbase : (ξ K Ω ≫ j) ≫ c = ξ k Ω := by
    rw [Category.assoc, hjbase, fieldGeometricPoint_comp k K Ω]
  have hgen : Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ :=
    (M₀.constantModel_isIntegral_and_adjoin ME (Iso.refl _) (Category.id_comp _)).2
  obtain ⟨χ, hχ⟩ := @exists_geometricFiniteGaloisMonodromy
    k K κ Ω E L H₁.val
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    akK inferInstance akΩ aKΩ aκΩ hkKΩ hkκΩ inferInstance hsepΩ hclosedΩ
    aEκ aEΩ hEκΩ aKL aEL aLΩ hKLΩ hELΩ
    inferInstance aKH₁ hKLH₁ hKH₁finite
    (ClassFieldTheory.FiniteAbelianLocalExtension.finiteDimensional H₁)
    (ClassFieldTheory.FiniteAbelianLocalExtension.isAbelianGalois H₁).toIsGalois
    C inferInstance inferInstance c j inferInstance inferInstance
    hbase hgen W η hηPreimmersion hη i₁
  let ψ : L ≃ₐ[K] L := M₀.constantFiniteFrobenius M e he E
  let φ : SemilinearAut E L := M₀.constantFiniteSemilinearFrobenius M e he E
  have hambient (a : L) : ρ (algebraMap L Ω a) =
      algebraMap L Ω ((ψ ^ n) a) :=
    M₀.constantFiniteFrobenius_pow_ambient M e he E Ω iL
      (RingHom.congr_fun hiLK) (RingHom.congr_fun hiLE) ρ n hρ a
  have hfield : ((ψ ^ n).restrictScalars k).toRingEquiv =
      SemilinearAut.toRingAut (φ ^ n) := by
    ext a
    exact M₀.constantFiniteFrobenius_pow_eq_semilinear_smul M e he E n a
  have hplacepow : SemilinearAut.ofAlgAut ((ψ ^ n).restrictScalars k) •
      w.forgetConstants (K := k) = w.forgetConstants (K := k) :=
    semilinearRestrictScalars_pow_fixed k K L ψ
      (w.forgetConstants (K := k)) hwforget n
  exact hilbertSource_fixed_of_native_fixed_and_annihilating_norm
    (k := k) (E := E) (K := K) (L := L)
    (algkK := akK) (algkL := akL) (algKL := aKL) (towerKL := hkKL)
    v hv w hw hrestrict q.toMonoidHom π.toMonoidHom i₀ i₁ χ hχ ρ
    ((ψ ^ n).restrictScalars k) (φ ^ n) hfield hambient hplacepow
    (fun x hx hfixedx =>
      M₀.constantPicardNorm_eq_zero_of_fixed_of_finrank M e he n hn E hEdegree
        x hx hfixedx)
    σ hσ hfixed

end AnabelianGeometry.FiniteField
