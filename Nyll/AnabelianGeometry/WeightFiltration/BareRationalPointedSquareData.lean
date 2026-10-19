/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalOrderTwoSquareInputs
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareCommonRootFieldPointedTransport
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareFiniteBaseFiberTransport

/-!
# Pointed square data for rational configurations
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.ProjectiveLine CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete RatFunc
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

local instance pointedSquareOverCategory (S : Scheme) :
    Category (MorphismProperty.Over (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S
local instance pointedSquareHasPullbacksAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩
local instance pointedSquareStableUnderBaseChangeAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

local instance pointedSquareChart_isOpenImmersion
    (k : Type) [Field k] (s : Finset (Projectivization k (k × k))) :
    IsOpenImmersion (show (rationalConfigurationOpen s : Scheme) ⟶
      (projectiveLineRatFuncModel k).C from (rationalConfigurationOpen s).ι) := by
  change IsOpenImmersion (rationalConfigurationOpen s).ι
  infer_instance

theorem bare_rationalConfiguration_same_punctures_pointed_square_data
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) γ) :
    ∃ eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
        rationalConfigurationGeometricGroup k κ t Ω₂,
      (∀ v, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ v) =
        eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v)) ∧
      ∃ σ : s ≃ t,
        (∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
          (rationalConfigurationChosenInertia k κ s Ω₁
            (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
          (rationalConfigurationChosenInertia k κ t Ω₂
            (rationalConfigurationBoundaryPlace k κ t (σ p))).map
              (MulAut.conj a).toMonoidHom) ∧
        (∀ (a b c₀ c : s), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : kˣ,
        (A : k) = crossRatio a.val b.val c₀.val c.val ∧
        (B : k) = crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B) ∧
        ∀ a b : s,
          ∃ Vs₀ Vsinf : (projectiveLineRatFuncModel k).openBoundaryPlaces
              (rationalConfigurationOpen s).ι,
          ∃ Vt₀ Vtinf : (projectiveLineRatFuncModel k).openBoundaryPlaces
              (rationalConfigurationOpen t).ι,
          ∃ f g : RatFunc k, f ≠ 0 ∧ g ≠ 0 ∧
          (∀ V : Place k (RatFunc k),
            V.ord f = (if V = Vs₀.val then 1 else 0) -
              (if V = Vsinf.val then 1 else 0)) ∧
          (∀ V : Place k (RatFunc k),
            V.ord g = (if V = Vt₀.val then 1 else 0) -
              (if V = Vtinf.val then 1 else 0)) ∧
          (∀ W : Place κ (RatFunc κ),
            W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
              (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
              (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) ∧
          (∀ W : Place κ (RatFunc κ),
            W.ord (algebraMap (RatFunc k) (RatFunc κ) g) =
              (if W = (rationalConfigurationBoundaryPlace k κ t (σ a)).val then 1 else 0) -
              (if W = (rationalConfigurationBoundaryPlace k κ t (σ b)).val then 1 else 0)) ∧
          let n : ℕ+ := 2
          let hn : IsUnit ((n : ℕ) : κ) := isUnit_iff_ne_zero.mpr
            (Nat.cast_ne_zero.mpr (show (2 : ℕ) ≠ 0 from by decide))
            ∃ us : Pic0.openKummerUnits k (RatFunc k)
              ((projectiveLineRatFuncModel k).openBoundaryPlaces
                (rationalConfigurationOpen s).ι) n,
            ∃ ut : Pic0.openKummerUnits k (RatFunc k)
              ((projectiveLineRatFuncModel k).openBoundaryPlaces
                (rationalConfigurationOpen t).ι) n,
            ∃ ws : Pic0.openKummerUnits κ (RatFunc κ)
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ s)) n,
            ∃ wt : Pic0.openKummerUnits κ (RatFunc κ)
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ t)) n,
              (us.val : RatFunc k) = f ∧ (ut.val : RatFunc k) = g ∧
              (ws.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) f ∧
              (wt.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) g ∧
              (∀ x : s, rationalConfigurationNamedResidue k κ s Ω₁ n hn ws
                (rationalConfigurationBoundaryPlace k κ s x) =
                  (if x = a then 1 else 0) - (if x = b then 1 else 0)) ∧
              (∀ p, rationalConfigurationNamedResidue k κ t Ω₂ n hn wt p =
                rationalConfigurationNamedResidue k κ s Ω₁ n hn ws
                  (rationalConfigurationBoundaryPlaceEquiv k κ s
                    (σ.symm ((rationalConfigurationBoundaryPlaceEquiv k κ t).symm p)))) ∧
              RationalConfigurationNamedTransport k κ s t Ω₁ Ω₂ n hn ws wt eΔ ∧
              RationalConfigurationArithmeticScalarTransportWithRoots
                k κ s t Ω₁ Ω₂ n us ut eP ∧
              RationalConfigurationArithmeticSquareTransportWithFiniteBase
                k κ s t Ω₁ Ω₂ us ut eP ∧
              ∃ (ρS : s → κ) (ρT : t → κ),
                (∀ x : s, ρS x ^ 2 = algebraMap k κ
                  ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt
                    (us.val : RatFunc k))) ∧
                (∀ x : t, ρT x ^ 2 = algebraMap k κ
                  ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt
                    (ut.val : RatFunc k))) ∧
                  let fs := (rationalConfigurationOpen s).ι ≫ π k 1
                  let ft := (rationalConfigurationOpen t).ι ≫ π k 1
                  let xs := rationalConfigurationArithmeticBasePoint k κ s Ω₁
                  let xt := rationalConfigurationArithmeticBasePoint k κ t Ω₂
                  let hn : IsUnit ((2 : ℕ) : k) :=
                    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (show (2 : ℕ) ≠ 0 from by decide))
                  let M := projectiveLineRatFuncModel k
                  let AS := M.openKummerCover (M.openBoundaryPlaces (rationalConfigurationOpen s).ι)
                    (2 : ℕ+) hn us (rationalConfigurationOpen s).ι
                    (rationalConfigurationOpen_denseRange k s)
                    (M.place_not_mem_openBoundaryPlaces (rationalConfigurationOpen s).ι)
                  let AT := M.openKummerCover (M.openBoundaryPlaces (rationalConfigurationOpen t).ι)
                    (2 : ℕ+) hn ut (rationalConfigurationOpen t).ι
                    (rationalConfigurationOpen_denseRange k t)
                    (M.place_not_mem_openBoundaryPlaces (rationalConfigurationOpen t).ι)
                  ∃ (a : kˣ) (β : κˣ), β ^ 2 = Units.map (algebraMap k κ).toMonoidHom a ∧
                    let E := quadraticBoundaryCoordinateField k κ β (Sum.elim ρS ρT)
                    let _hFD : FiniteDimensional k E :=
                      quadraticBoundaryCoordinateField_finiteDimensional k κ β (Sum.elim ρS ρT)
                    let _hsep : Algebra.IsSeparable k E := inferInstance
                    let _hFE : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
                      constantField_specMap_isFiniteEtale k E
                    let _hEC : IsSepClosure E κ :=
                      ⟨IsSepClosure.sep_closed k,
                        Algebra.isSeparable_tower_top_of_isSeparable k E κ⟩
                    let ys : Spec (.of Ω₁) ⟶ Limits.pullback
                        (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs :=
                      arithmeticConstantFieldLift k E κ fs xs
                    let yt : Spec (.of Ω₂) ⟶ Limits.pullback
                        (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft :=
                      arithmeticConstantFieldLift k E κ ft xt
                    let bs : Limits.pullback
                        (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs ⟶
                        (rationalConfigurationOpen s : Scheme) :=
                      ((pullback fs).obj (originalConstantFieldCover k E)).hom
                    let bt : Limits.pullback
                        (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft ⟶
                        (rationalConfigurationOpen t : Scheme) :=
                      ((pullback ft).obj (originalConstantFieldCover k E)).hom
                    let hs := arithmeticConstantFieldLift_comp k E κ fs xs
                    let ht := arithmeticConstantFieldLift_comp k E κ ft xt
                    let αE : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt) :=
                      arithmeticConstantFieldCoverGroupTransport k E κ fs ft xs xt eP hP
                    ∃ (rS : s → E) (rT : t → E),
                      (∀ x : s, (rS x : κ) = ρS x) ∧ (∀ x : t, (rT x : κ) = ρT x) ∧
                      (∀ x : s, rS x ^ 2 = algebraMap k E
                        ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt
                          (us.val : RatFunc k))) ∧
                      (∀ x : t, rT x ^ 2 = algebraMap k E
                        ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt
                          (ut.val : RatFunc k))) ∧
                    ∃ (θ : (fiber xt).obj
                        ((coverTransportOfAutEquiv (fiber xs) (fiber xt) eP).functor.obj AS) ≃
                      (fiber xt).obj AT)
                      (x₀ : (fiber xt).obj
                        ((coverTransportOfAutEquiv (fiber xs) (fiber xt) eP).functor.obj AS)),
                      let wE : (fiber ys).obj ((pullback bs).obj AS) :=
                        (pointedPullbackFiberEquiv bs ys xs hs AS).symm
                          (coverTransportFiberEquiv (fiber xs) (fiber xt) eP AS x₀)
                      let cs := Limits.pullback.fst (originalConstantFieldCover k E).hom fs
                      let ct := Limits.pullback.fst (originalConstantFieldCover k E).hom ft
                      let GS := Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) cs
                      let GT := Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ct
                      let _hGS : IsIntegral GS := rationalConfiguration_coefficientTower_isIntegral
                        k E κ s
                      let _hGT : IsIntegral GT := rationalConfiguration_coefficientTower_isIntegral
                        k E κ t
                      ∃ (jS : κ →+* Ω₁) (aS : GS.functionField →+* Ω₁)
                        (jT : κ →+* Ω₂) (aT : GT.functionField →+* Ω₂),
                        jS.comp (algebraMap E κ) = (Spec.preimage (ys ≫ cs)).hom ∧
                        jT.comp (algebraMap E κ) = (Spec.preimage (yt ≫ ct)).hom ∧
                        let _A_S : Algebra GS.functionField Ω₁ := aS.toAlgebra
                        let _A_T : Algebra GT.functionField Ω₂ := aT.toAlgebra
                        IsAlgClosure GS.functionField Ω₁ ∧ IsAlgClosure GT.functionField Ω₂ ∧
                        GS.genericExtensionMorphism Ω₁ ≫ Limits.pullback.fst _ cs =
                          Spec.map (CommRingCat.ofHom jS) ∧
                        GT.genericExtensionMorphism Ω₂ ≫ Limits.pullback.fst _ ct =
                          Spec.map (CommRingCat.ofHom jT) ∧
                        GS.genericExtensionMorphism Ω₁ ≫ Limits.pullback.snd _ cs = ys ∧
                        GT.genericExtensionMorphism Ω₂ ≫ Limits.pullback.snd _ ct = yt ∧
                      ∃ c : π₁ᵉᵗ(yt),
                      let eE :=
                        namedSquareFiniteBaseFiberEquiv bs bt ys yt xs xt hs ht eP AS AT θ
                      (∀ g, arithmeticFundamentalGroupHom E κ
                        (Limits.pullback.fst (originalConstantFieldCover k E).hom ft) yt
                        (ProCGroups.innerCorrectedGroupEquiv αE c g) =
                          arithmeticFundamentalGroupHom E κ
                            (Limits.pullback.fst (originalConstantFieldCover k E).hom fs) ys g) ∧
                      fiberEquivariant ys yt ((pullback bs).obj AS) ((pullback bt).obj AT)
                        (ProCGroups.innerCorrectedGroupEquiv αE c)
                        (ProCGroups.innerCorrectedFiberEquiv eE c) ∧
                      pointedPullbackFiberEquiv bs ys xs hs AS wE =
                        coverTransportFiberEquiv (fiber xs) (fiber xt) eP AS x₀ := by
  obtain ⟨eΔ, hΔ, σ, hI, hclasses, hpairs⟩ :=
    bare_rationalConfiguration_orderTwo_square_inputs k κ s t hs ht Ω₁ Ω₂ eP hP
  refine ⟨eΔ, hΔ, σ, hI, hclasses, fun a b => ?_⟩
  obtain ⟨Vs₀, Vsinf, Vt₀, Vtinf, f, g, hf, hg, hfa, hga, hfg, hgg, hall⟩ :=
    hpairs a b
  refine ⟨Vs₀, Vsinf, Vt₀, Vtinf, f, g, hf, hg, hfa, hga, hfg, hgg, ?_⟩
  intro n hn
  obtain ⟨us, ut, ws, wt, hus, hut, hws, hwt, hvector, hres, hgeom,
    hscalar, hsquare⟩ := hall
  refine ⟨us, ut, ws, wt, hus, hut, hws, hwt, hvector, hres, hgeom,
    hscalar, hsquare, ?_⟩
  have hrootsS : ∀ x : s, ∃ r : κ, r ^ 2 = algebraMap k κ
      ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt
        (us.val : RatFunc k)) := by
    intro x
    exact IsAlgClosed.exists_pow_nat_eq _ (show 0 < (2 : ℕ) from by decide)
  have hrootsT : ∀ x : t, ∃ r : κ, r ^ 2 = algebraMap k κ
      ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt
        (ut.val : RatFunc k)) := by
    intro x
    exact IsAlgClosed.exists_pow_nat_eq _ (show 0 < (2 : ℕ) from by decide)
  choose ρS hρS using hrootsS
  choose ρT hρT using hrootsT
  refine ⟨ρS, ρT, hρS, hρT, ?_⟩
  exact namedSquare_originalScalar_exists_commonRootField_pointed_transport
    k κ s t Ω₁ Ω₂ us ut eP hP hsquare ρS ρT hρS hρT

end AnabelianGeometry.WeightFiltration
