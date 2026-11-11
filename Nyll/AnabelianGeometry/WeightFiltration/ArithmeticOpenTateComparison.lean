/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Kummer.ArithmeticTateComparison
public import Nyll.AnabelianGeometry.WeightFiltration.TorsionTateSpecialization
public import Nyll.AnabelianGeometry.WeightFiltration.FinitelyGeneratedNormalGoodModel
public import Nyll.SchemeTheory.FunctionFields.GenericPointNaturality
public import Nyll.SchemeTheory.FunctionFields.OpenImmersion
public import Mathlib.FieldTheory.Separable
public import Nyll.ProCGroups.Abelian.FullTateModule
public import Nyll.ProCGroups.Abelian.FullTateModuleMap
public import Nyll.ProCGroups.Abelian.RestrictedTateModule
public import Nyll.ProCGroups.Abelian.RestrictedTateTransport
public import Nyll.SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization

/-!
# The arithmetic Tate comparison at an open curve's generic point

The function-field isomorphism of the original open immersion transports
its supplied separable closure. The actual generic-point square then gives
the existing proper Tate comparison at the required compactification point.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.FiniteEtale NeronModelInfra GoodReductionJacobian
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

/-- The existing equivariant Tate comparison uses the actual image of an
open generic point, without a further choice of a fiber-functor isomorphism. -/
theorem exists_arithmetic_fullTate_equiv_at_open_generic
    {k K : Type} [Field k] [Field K] [IsAlgClosed K] [CharZero K]
    [Algebra k K] [IsSepClosure k K]
    {C : Scheme} (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (D : RelativePic0Designation k c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase] :
    let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    let : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c
    let Y := pullback c (specMap k K)
    let : IsIntegral Y := isIntegral_pullback_Spec_field k c (specMap k K)
    let s := pullbackSymmetry c (specMap k K)
    let : IsIntegral (pullback (specMap k K) c) := IsIntegral.of_isIso s.hom
    let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative :=
      RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
    ∀ (X : Scheme) [IsIntegral X] (j : X ⟶ pullback (specMap k K) c)
      [IsOpenImmersion j] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
      [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω],
    let xi := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)
    ∃ E : TopologicalAbelianization (Aut (fiber (xi ≫ j))) ≃ₜ*
        Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)),
      ∀ (σ : K ≃ₐ[k] K) (x : TopologicalAbelianization (Aut (fiber (xi ≫ j)))),
        E (geometricAbelianGaloisAction k K C c (xi ≫ j) σ x) =
          ProCGroups.FullTateModule.mapHom
            (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom) (E x) := by
  intro hcompact hqs Y hY s hYL G hc X hX j hj Ω hΩ hΩclosed hFΩ hsep xi
  let v := j ≫ s.inv
  let e := v.functionFieldRingEquivOfIsOpenImmersion
  let : Algebra Y.functionField Ω :=
    ((algebraMap X.functionField Ω).comp e.toRingHom).toAlgebra
  let : Algebra.IsSeparable Y.functionField Ω :=
    Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl Ω) (by
      ext z
      change algebraMap X.functionField Ω (e (e.symm z)) = algebraMap X.functionField Ω z
      rw [e.apply_symm_apply])
  let : IsSepClosure Y.functionField Ω :=
    { sep_closed := inferInstance
      separable := inferInstance }
  have hv : DenseRange v := v.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _
  let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
  let ηY := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω))
  let qY := Y.fromSpecStalk (genericPoint Y)
  have hη : ηY = η ≫ Spec.map (CommRingCat.ofHom e.toRingHom) :=
    Spec.map_comp _ _
  have hq : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ qY =
      X.fromSpecStalk (genericPoint X) ≫ v := functionFieldMap_genericPoint v hv
  have hpoint : (ηY ≫ qY) ≫ s.hom = xi ≫ j := by
    rw [hη, Category.assoc η, hq]
    simp only [v, xi, η, Category.assoc, s.inv_hom_id, Category.comp_id]
  have hT := JacobianVarieties.Kummer.exists_arithmetic_abelJacobi_fullTate_equiv
    (k := k) (K := K) c ε D hD Ω
  change ∃ E : TopologicalAbelianization (Aut (fiber ((ηY ≫ qY) ≫ s.hom))) ≃ₜ*
      Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)),
    ∀ (σ : K ≃ₐ[k] K)
      (x : TopologicalAbelianization (Aut (fiber ((ηY ≫ qY) ≫ s.hom)))),
      E (geometricAbelianGaloisAction k K C c ((ηY ≫ qY) ≫ s.hom) σ x) =
        ProCGroups.FullTateModule.mapHom
          (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom) (E x) at hT
  rw [hpoint] at hT
  exact hT

/-- A smooth proper model of the original Jacobian makes valuation inertia
act trivially on the curve's geometric pro-Sigma abelianization whenever the
model's residue characteristic lies outside Sigma. -/
theorem geometricSigmaAbelianGaloisAction_inertia_eq_one
    {R k K : Type} [CommRing R] [IsLocalRing R]
    [Field k] [Field K] [IsAlgClosed K]
    [Algebra R k] [Algebra k K] [Algebra R K] [IsScalarTower R k K]
    [IsSepClosure k K]
    {C : Scheme} (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (D : RelativePic0Designation k c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    {A : Scheme} {a : A ⟶ Spec (.of R)} [IsProper a] [Smooth a]
    (G : RelativeGroupLaw R a) (hc : G.IsCommutative)
    (π : D.P ⟶ A)
    (hπ : IsPullback π D.toBase a (Spec.map (CommRingCat.ofHom (algebraMap R k))))
    (hmul :
      let J := RepresentsRelSubPic.relativeGroupLaw
        (P := algEquivZeroGroupCut c ε) hD
      ∀ (T : Scheme) (t : T ⟶ Spec (.of k))
        (P Q : SchemeHomOver t D.toBase),
        (J.mul t P Q).val ≫ π =
          (G.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)))
            ⟨P.val ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, P.property]⟩
            ⟨Q.val ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, Q.property]⟩).val)
    (V : ValuationSubring K) [HenselianLocalRing V]
    [Algebra R V] [IsScalarTower R V K]
    (Sigma : Set ℕ) (p : ℕ) [CharP (IsLocalRing.ResidueField R) p]
    (hp : p ∉ Sigma) :
    let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    let : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c
    let Y := pullback c (specMap k K)
    let : IsIntegral Y := isIntegral_pullback_Spec_field k c (specMap k K)
    let s := pullbackSymmetry c (specMap k K)
    let : IsIntegral (pullback (specMap k K) c) := IsIntegral.of_isIso s.hom
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra Y.functionField Ω]
      [IsAlgClosure Y.functionField Ω],
    let xi := (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)) ≫ s.hom
    ∀ d : V.inertiaSubgroup k,
      geometricSigmaAbelianGaloisAction k K C c xi Sigma d.val = 1 := by
  intro hcompact hqs Y hY s hYL Ω hΩ hΩclosed hFΩ hclosure xi d
  let J := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
  let hJ : J.IsCommutative :=
    RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
  have hI (n : ProCGroups.sigmaTorsionIndices Sigma) : IsUnit ((n.val : ℕ) : K) := by
    simpa only [map_natCast] using
      (ProCGroups.sigmaTorsionIndices.isUnit_natCast (R := R) p Sigma hp n).map
        (algebraMap R K)
  obtain ⟨E, hE⟩ := JacobianVarieties.Kummer.exists_arithmetic_abelJacobi_sigmaTate_equiv
    (k := k) (K := K) c ε D hD Sigma hI Ω
  let B := RelativeGroupLaw.algPointsPullbackEquiv G hc J hJ π hπ hmul K
  let tB := ProCGroups.RestrictedTateModule.mapEquiv
    (S := ProCGroups.sigmaTorsionIndices Sigma) B
  have hB (x : Multiplicative (ProCGroups.RestrictedTateModule
      (J.AlgPoints hJ K) (ProCGroups.sigmaTorsionIndices Sigma))) :
      tB (ProCGroups.RestrictedTateModule.mapHom
          (RelativeGroupLaw.AlgPoints.map (L := J) (hc := hJ) (d.val : K ≃ₐ[k] K).toAlgHom) x) =
        G.restrictedTateCoefficientMap hc ((d.val : K ≃ₐ[k] K).restrictScalars R).toAlgHom
          (ProCGroups.sigmaTorsionIndices Sigma) (tB x) := by
    apply Multiplicative.toAdd.injective
    apply ProCGroups.RestrictedTateModule.ext
    intro n
    exact RelativeGroupLaw.algPointsPullbackEquiv_equivariant
      G hc J hJ π hπ hmul K d.val
      (ProCGroups.RestrictedTateModule.evaluation (J.AlgPoints hJ K)
        (ProCGroups.sigmaTorsionIndices Sigma) n (Multiplicative.toAdd x))
  have hfixed (x : Multiplicative (ProCGroups.RestrictedTateModule
      (J.AlgPoints hJ K) (ProCGroups.sigmaTorsionIndices Sigma))) :
      ProCGroups.RestrictedTateModule.mapHom
        (RelativeGroupLaw.AlgPoints.map (L := J) (hc := hJ) (d.val : K ≃ₐ[k] K).toAlgHom) x =
        x := by
    apply tB.injective
    exact (hB x).trans (congrArg (fun f => f (tB x))
      (G.restrictedTateCoefficientMap_sigma_inertia_eq_id hc V k Sigma p hp d))
  apply MulEquiv.ext
  intro x
  apply E.injective
  exact (hE d.val x).trans (hfixed (E x))

section FinitelyGenerated

open EtaleFundamentalGroups.StrictHenselian EtaleFundamentalGroups.Inertia

attribute [local instance] normalizationInertiaImageAction

/-- A finitely generated characteristic-zero field supplies a normal local
finite-residue model, avoiding a prescribed finite set of primes, whose
original normalization inertia acts trivially on the curve's geometric
pro-Sigma abelianization. The model and its good-reduction comparison are
constructed from the represented Jacobian. -/
theorem exists_finitelyGenerated_sigma_inertia_trivial_good_model
    (k K : Type) [Field k] [CharZero k] [Field.FG k]
    [Field K] [Algebra k K] [IsAlgClosure k K]
    {C : Scheme} (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (D : RelativePic0Designation k c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (Sigma : Finset ℕ) :
    ∃ T : Subalgebra ℤ k, T.FG ∧ IsIntegrallyClosed T ∧
      ∃ (hfrac : IsFractionRing T k) (m : Ideal T) (hm : m.IsMaximal),
        let _ : IsFractionRing T k := hfrac
        let _ : m.IsMaximal := hm
        let H := Localization.AtPrime m
        let _ : Algebra H k :=
          EtaleFundamentalGroups.localizationAtPrimeToFractionFieldAlgebra (K := k) m
        ∃ hfracH : IsFractionRing H k,
          IsIntegrallyClosed H ∧ Finite (IsLocalRing.ResidueField H) ∧
          (ringChar (IsLocalRing.ResidueField H)).Prime ∧
          ringChar (IsLocalRing.ResidueField H) ∉ Sigma ∧
          let _ : IsFractionRing H k := hfracH
          let _ : Algebra H K := ((algebraMap k K).comp (algebraMap H k)).toAlgebra
          let _ : IsScalarTower H k K :=
            IsScalarTower.of_algebraMap_eq' (R := H) (S := k) (A := K) rfl
          ∀ (Q : Ideal (integralClosure H K)) [Q.IsPrime],
          let _ : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
          let _ : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c
          let Y := pullback c (specMap k K)
          let _ : IsIntegral Y := isIntegral_pullback_Spec_field k c (specMap k K)
          let s := pullbackSymmetry c (specMap k K)
          let _ : IsIntegral (pullback (specMap k K) c) := IsIntegral.of_isIso s.hom
          ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra Y.functionField Ω]
            [IsAlgClosure Y.functionField Ω],
          let xi := (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
            Y.fromSpecStalk (genericPoint Y)) ≫ s.hom
          ∀ (σ : Gal(K/k)), σ ∈ Q.inertia Gal(K/k) →
            geometricSigmaAbelianGaloisAction k K C c xi (Sigma : Set ℕ) σ = 1 := by
  classical
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  let J := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
  let hJ : J.IsCommutative :=
    RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
  have hDmodel : AbelianSchemePropertyBundle k D.toBase :=
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := fun s => D.toBase.isConnected_preimage_singleton s
      hasGroupLaw := ⟨J⟩ }
  let primes := Sigma.filter Nat.Prime
  let ell := primes.prod id
  have hell : ell ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq =>
    (Finset.mem_filter.mp hq).2.ne_zero)
  obtain ⟨T, hT, hnormalT, hfrac, m, hm, hmodel⟩ :=
    J.exists_finitelyGenerated_normal_local_good_model k inferInstance hJ hDmodel ell hell
  refine ⟨T, hT, hnormalT, hfrac, m, hm, ?_⟩
  intro fraction maximal H localAlgebra
  obtain ⟨hdom, hlocal, _, hnormal, hfracH, hfinite, _, hprime, hnotdvd,
      A, a, G, π, hπ, hG, hc, hmul⟩ := hmodel
  have : IsDomain H := hdom
  have : IsLocalRing H := hlocal
  have : IsFractionRing H k := hfracH
  have hp : ringChar (IsLocalRing.ResidueField H) ∉ Sigma := by
    intro hmem
    exact hnotdvd (Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨hmem, hprime⟩))
  refine ⟨hfracH, hnormal, hfinite, hprime, hp, ?_⟩
  intro actualCoefficients actualTower
  have : Smooth a := hG.smooth
  have : IsProper a := hG.proper
  intro Q hQ hcompact hqs Y hY s hYL Ω hΩ hΩclosed hFΩ hclosure xi σ hσ
  have hI (n : ProCGroups.sigmaTorsionIndices (Sigma : Set ℕ)) :
      IsUnit ((n.val : ℕ) : H) :=
    ProCGroups.sigmaTorsionIndices.isUnit_natCast
      (ringChar (IsLocalRing.ResidueField H)) (Sigma : Set ℕ) hp n
  have hIK (n : ProCGroups.sigmaTorsionIndices (Sigma : Set ℕ)) :
      IsUnit ((n.val : ℕ) : K) := by
    rw [← map_natCast (algebraMap H K) (n.val : ℕ)]
    exact (hI n).map (algebraMap H K)
  obtain ⟨E, hE⟩ := JacobianVarieties.Kummer.exists_arithmetic_abelJacobi_sigmaTate_equiv
    (k := k) (K := K) c ε D hD (Sigma : Set ℕ) hIK Ω
  let B := RelativeGroupLaw.algPointsPullbackEquiv G hc J hJ π hπ hmul K
  let tB := ProCGroups.RestrictedTateModule.mapEquiv
    (S := ProCGroups.sigmaTorsionIndices (Sigma : Set ℕ)) B
  have hB (x : Multiplicative (ProCGroups.RestrictedTateModule
      (J.AlgPoints hJ K) (ProCGroups.sigmaTorsionIndices (Sigma : Set ℕ)))) :
      tB (ProCGroups.RestrictedTateModule.mapHom
          (RelativeGroupLaw.AlgPoints.map (L := J) (hc := hJ) σ.toAlgHom) x) =
        G.restrictedTateCoefficientMap hc (σ.restrictScalars H).toAlgHom
          (ProCGroups.sigmaTorsionIndices (Sigma : Set ℕ)) (tB x) := by
    apply Multiplicative.toAdd.injective
    apply ProCGroups.RestrictedTateModule.ext
    intro n
    exact RelativeGroupLaw.algPointsPullbackEquiv_equivariant
      G hc J hJ π hπ hmul K σ
      (ProCGroups.RestrictedTateModule.evaluation (J.AlgPoints hJ K)
        (ProCGroups.sigmaTorsionIndices (Sigma : Set ℕ)) n (Multiplicative.toAdd x))
  have hfixed (x : Multiplicative (ProCGroups.RestrictedTateModule
      (J.AlgPoints hJ K) (ProCGroups.sigmaTorsionIndices (Sigma : Set ℕ)))) :
      ProCGroups.RestrictedTateModule.mapHom
        (RelativeGroupLaw.AlgPoints.map (L := J) (hc := hJ) σ.toAlgHom) x = x := by
    apply tB.injective
    exact (hB x).trans (congrArg (fun f => f (tB x))
      (G.restrictedTateCoefficientMap_normalization_inertia_eq_id hc k K Q
        (ProCGroups.sigmaTorsionIndices (Sigma : Set ℕ)) hI σ hσ))
  apply MulEquiv.ext
  intro x
  apply E.injective
  exact (hE σ x).trans (hfixed (E x))

end FinitelyGenerated

end AnabelianGeometry.WeightFiltration
