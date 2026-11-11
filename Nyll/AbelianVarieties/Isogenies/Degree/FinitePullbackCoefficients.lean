/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_endDegree_mul_coeff_of_forall_eulerChar_tensorPow_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.EndDegree
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.EulerCharacteristic.OModulePresheafEulerChar
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.Complexes.OModulePresheafOfModules
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.Complexes.OModulePresheafTensor
public import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions
public import Nyll.AlgebraicCurves.Geometry.Schemes.Covers.OrderedAffineCoverComap
public import Nyll.AlgebraicCurves.Cohomology.Cech.Comparison.EquivModulesQuasicoherent
public import Nyll.AlgebraicCurves.Cohomology.Cech.Comparison.EquivModulesPullbackComapTwistPushforwardUnit
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.Complexes.CoeffEqRankAtStalkMulCoeff
public import Nyll.SchemeTheory.Morphisms.SmoothRelativeDimension
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFinite
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemeFlatFinite
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSurjectiveEndDegreeEqFinrank
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemeIsIntegral
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowerIsomorphisms
public import Nyll.AlgebraicCurves.Cohomology.Cech.Comparison.EquivModulesIso
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.EulerCharacteristic.SheafEulerPolynomialTwistTensorPowEq
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.Coherent.QuasicoherentModules
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor

/-!
# Euler coefficients for an endomorphism with finite kernel

The common section-localization, finite pushforward, stalk-rank and twist comparison
proofs use the original presheaves and scalar structures. The finite-kernel coefficient
formula works over an arbitrary field; no algebraic closure is assumed here.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace Opposite Polynomial

namespace JacobianVarieties.Picard.Proofs.EndDegreeCoefficient.P2mDegLead

open AlgebraicGeometry.OModulePresheaf

section Chi

variable {R : Type u} [CommRing R]

theorem eulerChar_eq_of_equiv {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (F' : OModulePresheaf π') (K : V.OrderedAffineCover) (K' :
      V'.OrderedAffineCover)
    (hcard : Fintype.card K.ι = Fintype.card K'.ι)
    (h0 : Nonempty (F.H0 K ≃ₗ[R] F'.H0 K')) (hs : ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] F'.HSucc K'
      i)) :
    F.eulerChar K = F'.eulerChar K' := by
  have h : ∀ i, F.cechFinrank K i = F'.cechFinrank K' i := by
    intro i
    cases i with
    | zero => obtain ⟨e⟩ := h0; exact e.finrank_eq
    | succ j => obtain ⟨e⟩ := hs j; exact e.finrank_eq
  rw [eulerChar_def, eulerChar_def, hcard]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem eulerChar_ofModules_congr {V : Scheme.{u}} {π π' : V ⟶ Spec (.of R)} (h : π = π')
    (X : V.Modules)
    (K : V.OrderedAffineCover) : (ofModules π X).eulerChar K = (ofModules π' X).eulerChar K := by
  subst h; rfl

theorem isQuasicoherent_ofModules_congr {V : Scheme.{u}} {π π' : V ⟶ Spec (.of R)} (h : π = π')
    (X : V.Modules)
    (hq : (ofModules π' X).IsQuasicoherent) : (ofModules π X).IsQuasicoherent := by
  subst h; exact hq

end Chi

section PushUnit

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

theorem preimage_eq_bot (U : V.Opens) (hU : (U : Set V) = ∅) : ι ⁻¹ᵁ U = ⊥ := by
  ext z
  simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, Opens.coe_bot,
    Set.mem_empty_iff_false, iff_false]
  intro hz
  have : ι.base z ∈ (U : Set V) := hz
  rw [hU] at this
  exact this

theorem subsingleton_sections_of_eq_bot (W : Z.Opens) (h : W = ⊥) : Subsingleton Γ(Z, W) := by
  subst h
  infer_instance

theorem supportedIn_top : (pushforwardUnit π ι).SupportedIn ⊤ := fun U hU =>
  subsingleton_sections_of_eq_bot (ι ⁻¹ᵁ U.1)
    (preimage_eq_bot ι U.1 (by simpa only [Closeds.coe_top, Set.inter_univ] using hU))

theorem res_rfl (W : Z.Opens) (x : Γ(Z, W)) : Z.presheaf.map (homOfLE (le_refl W)).op x = x := by
  rw [Subsingleton.elim (homOfLE (le_refl W)).op (𝟙 (op W)), Z.presheaf.map_id]; rfl

theorem appLE_rfl_apply (U : V.Opens) (a : Γ(V, U)) : ι.appLE U (ι ⁻¹ᵁ U) le_rfl a = ι.app U a := by
  change Z.presheaf.map (homOfLE (le_refl _)).op (ι.app U a) = _
  exact res_rfl (ι ⁻¹ᵁ U) _

theorem isCoherent [IsFinite ι] : (pushforwardUnit π ι).IsCoherent := by
  intro U
  have hfin : (ι.app U.1).hom.Finite := IsFinite.finite_app ι U.1 U.2
  have heq : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl = ι.app U.1 := by
    ext a; exact appLE_rfl_apply ι U.1 a
  let : Algebra Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have hfin' : Module.Finite Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Finite := by rw [heq]; exact hfin
    exact this
  exact hfin'

theorem loc_core [IsAffineHom ι] (U : V.affineOpens) (g : Γ(Z, ι ⁻¹ᵁ U.1)) (W' : Z.Opens)
    (hle : W' ≤ ι ⁻¹ᵁ U.1)
    (hW' : W' = Z.basicOpen g) :
    (∀ x : Γ(Z, W'), ∃ (n : ℕ) (y : Γ(Z, ι ⁻¹ᵁ U.1)),
        Z.presheaf.map (homOfLE hle).op y = Z.presheaf.map (homOfLE hle).op (g ^ n) * x) ∧
      (∀ y : Γ(Z, ι ⁻¹ᵁ U.1), Z.presheaf.map (homOfLE hle).op y = 0 → ∃ n : ℕ, g ^ n * y = 0) := by
  subst hW'
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  have : IsLocalization.Away g Γ(Z, Z.basicOpen g) := hW.isLocalization_basicOpen g
  have halg : ∀ y : Γ(Z, ι ⁻¹ᵁ U.1),
      algebraMap Γ(Z, ι ⁻¹ᵁ U.1) Γ(Z, Z.basicOpen g) y =
        Z.presheaf.map (homOfLE hle).op y := fun y => by
    rw [Subsingleton.elim (homOfLE hle) (homOfLE (Z.basicOpen_le g))]; rfl
  constructor
  · intro x
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g) x
    refine ⟨n, y, ?_⟩
    rw [← halg, ← halg, ← h, mul_comm]
  · intro y hy
    rw [← halg] at hy
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp hy
    exact ⟨n, hn⟩

theorem preimage_basicOpen_eq (U : V.affineOpens) (f : Γ(V, U.1)) :
    ι ⁻¹ᵁ V.basicOpen f = Z.basicOpen (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f) := by
  rw [appLE_rfl_apply]; exact Scheme.preimage_basicOpen ι f

theorem pre_le (U : V.affineOpens) (f : Γ(V, U.1)) : ι ⁻¹ᵁ V.basicOpen f ≤ ι ⁻¹ᵁ U.1 :=
  fun _ hx => V.basicOpen_le f hx

theorem smul_basicOpen (U : V.affineOpens) (f : Γ(V, U.1)) (a : Γ(V, U.1))
    (x : Γ(Z, ι ⁻¹ᵁ V.basicOpen f)) :
    ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom a •
        (show (pushforwardUnit π ι).obj (V.basicOpen f) from x)) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from
        Z.presheaf.map (homOfLE (pre_le ι U f)).op (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a) * x) := by
  change ι.appLE (V.basicOpen f) (ι ⁻¹ᵁ V.basicOpen f) le_rfl ((V.presheaf.map (homOfLE
    (V.basicOpen_le f)).op) a) * x
    = _
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

theorem smul_top (U : V.affineOpens) (a : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (a • (show (pushforwardUnit π ι).obj U.1 from y)) =
      (show (pushforwardUnit π ι).obj U.1 from ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a * y) := rfl

theorem res_eq (U : V.affineOpens) (f : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (pushforwardUnit π ι).res (V.basicOpen_le f) (show (pushforwardUnit π ι).obj U.1 from y) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from Z.presheaf.map (homOfLE (pre_le ι U
        f)).op y) := by
  change Z.presheaf.map _ y = _
  rw [Subsingleton.elim (homOfLE ((Opens.map ι.base).monotone (V.basicOpen_le f))) (homOfLE (pre_le
    ι U f))]

theorem isQuasicoherent [IsAffineHom ι] : (pushforwardUnit π ι).IsQuasicoherent := by
  intro U f
  set g : Γ(Z, ι ⁻¹ᵁ U.1) := ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f with hg
  obtain ⟨h1, h2⟩ := loc_core ι U g (ι ⁻¹ᵁ V.basicOpen f) (pre_le ι U f) (preimage_basicOpen_eq ι U
    f)
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := h1 x
    refine ⟨n, y, ?_⟩
    have heval : Z.presheaf.map (homOfLE (pre_le ι U f)).op y =
        Z.presheaf.map (homOfLE (pre_le ι U f)).op
          (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n)) *
          (show Γ(Z, ι ⁻¹ᵁ V.basicOpen f) from x) := by
      rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
      exact hy
    exact (res_eq π ι U f y).trans
      (heval.trans (smul_basicOpen π ι U f (f ^ n) x).symm)
  · intro y hy
    have hy' : Z.presheaf.map (homOfLE (pre_le ι U f)).op y = 0 :=
      (res_eq π ι U f y).symm.trans hy
    obtain ⟨n, hn⟩ := h2 y hy'
    refine ⟨n, ?_⟩
    have heval : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n) *
        (show Γ(Z, ι ⁻¹ᵁ U.1) from y) = 0 := by
      rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
      exact hn
    exact (smul_top π ι U (f ^ n) y).trans heval

end PushUnit

section Rank

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

theorem finrank_comp_iso {X Y Y' : Scheme.{u}} (g : X ⟶ Y) [Flat g] [IsFinite g] (e : Y ≅ Y')
    (z : Y') :
    Scheme.Hom.finrank (g ≫ e.hom) z = Scheme.Hom.finrank g (e.inv.base z) := by
  have sq : IsPullback (𝟙 X) (g ≫ e.hom) g e.inv := IsPullback.of_horiz_isIso
    ⟨by simp only [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ sq z

theorem rankAtStalk_pushforwardUnit_obj [IsFinite ι] [Flat ι] (U : V.affineOpens) (r : ℕ)
    (hr : ∀ y : V, Scheme.Hom.finrank ι y = r) (𝔭 : PrimeSpectrum Γ(V, U.1)) :
    Module.rankAtStalk (R := Γ(V, U.1)) ((pushforwardUnit π ι).obj U.1) 𝔭 = r := by
  have heq : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl = ι.app U.1 := Scheme.Hom.appLE_eq_app ι
  let alg : Algebra Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have : Module.Finite Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Finite := by
      rw [heq]
      exact IsFinite.finite_app ι U.1 U.2
    exact this
  have : Module.Flat Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) (f := ι) inferInstance U ⟨ι ⁻¹ᵁ U.1, U.2.preimage ι⟩
        le_rfl
    exact this
  have key := Scheme.Hom.finrank_SpecMap_algebraMap Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) 𝔭
  have hmap : CommRingCat.ofHom (algebraMap Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1)) = ι.app U.1 := by
    rw [← heq]; rfl
  rw [hmap] at key
  have hU : IsAffineOpen U.1 := U.2
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  have hnat : Spec.map (ι.app U.1) = hW.isoSpec.inv ≫ ((ι ∣_ U.1) ≫ hU.isoSpec.hom) := by
    rw [IsAffineOpen.isoSpec_hom, ← Scheme.Opens.toSpecΓ_naturality, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_toSpecΓ, Category.id_comp]
  have hfr : Scheme.Hom.finrank (Spec.map (ι.app U.1)) 𝔭 = r := by
    let z : Spec Γ(V, U.1) := 𝔭
    change Scheme.Hom.finrank (Spec.map (ι.app U.1)) z = r
    rw [hnat, Scheme.Hom.finrank_comp_left_of_isIso, finrank_comp_iso,
      Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict ι U.1).flip]
    exact hr _
  rw [hfr] at key
  exact key.symm

end Rank

section Setup

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem connectedSpace (hA : AbelianSchemePropertyBundle K f) : ConnectedSpace A := by
  have h := hA.connectedFibres (IsLocalRing.closedPoint K)
  have h' : _root_.IsConnected (Set.univ : Set A) := by
    convert h using 1
    exact (Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _).symm
  exact connectedSpace_iff_univ.mpr h'

theorem krullDim_top_le (g : ℕ) [SmoothOfRelativeDimension g f] :
    topologicalKrullDim ((⊤ : Closeds A) : Set A) ≤ g :=
  (Topology.IsInducing.topologicalKrullDim_le (Topology.IsEmbedding.subtypeVal.isInducing)).trans
    (SmoothOfRelativeDimension.topologicalKrullDim_le f g)

theorem exists_chart_prime [IsIntegral A] [Nonempty A] (𝒦 : A.OrderedAffineCover) :
    ∃ (U₀ : A.affineOpens) (𝔭 : PrimeSpectrum Γ(A, U₀.1)), (∃ i, U₀.1 = 𝒦.U i) ∧ 𝔭.asIdeal = ⊥ := by
  obtain ⟨a⟩ := (inferInstance : Nonempty A)
  have ha : a ∈ (⊤ : A.Opens) := trivial
  rw [← 𝒦.iSup_eq_top, Opens.mem_iSup] at ha
  obtain ⟨i, hi⟩ := ha
  have : Nonempty (𝒦.U i) := ⟨⟨a, hi⟩⟩
  exact ⟨⟨𝒦.U i, 𝒦.isAffineOpen i⟩, ⟨⊥, Ideal.isPrime_bot⟩, ⟨i, rfl⟩, rfl⟩

end Setup

section Chain

variable {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))

theorem isInvertible_tensorPow {𝓛 : A.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (n : ℕ) :
    Scheme.Modules.IsInvertible (𝓛.tensorPow n) :=
  Scheme.Modules.IsInvertible.tensorPow h𝓛 n

variable [IsSeparated f] (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 :
  Scheme.Modules.IsInvertible 𝓛)
  (γ : SchemeHomOver f f) [IsAffineHom γ.1]

include h𝓛 in
theorem eulerChar_twist_eq (m : ℕ) :
    ((pushforwardUnit f γ.1).twist (𝓛.tensorPow m)).eulerChar 𝒦 =
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)).eulerChar 𝒦 := by
  have hN : Scheme.Modules.IsInvertible (𝓛.tensorPow m) := isInvertible_tensorPow h𝓛 m
  have e1 : ((pushforwardUnit f γ.1).twist (𝓛.tensorPow m)).eulerChar 𝒦 =
      (ofModules (γ.1 ≫ f) ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).eulerChar (𝒦.comap
        γ.1) := by
    obtain ⟨h0, hs⟩ := nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit f γ.1 𝒦
      (𝓛.tensorPow m) hN.1
    exact (eulerChar_eq_of_equiv (ofModules (γ.1 ≫ f) ((Scheme.Modules.pullback γ.1).obj
      (𝓛.tensorPow m)))
      ((pushforwardUnit f γ.1).twist (𝓛.tensorPow m)) (𝒦.comap γ.1) 𝒦 rfl h0 hs).symm
  have e2 := eulerChar_ofModules_congr γ.2 ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))
    (𝒦.comap γ.1)
  have hq : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).IsQuasicoherent :=
    isQuasicoherent_ofModules_of_locallyTrivial f _ (hN.pullback γ.1).1
  have e3 : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).eulerChar (𝒦.comap
    γ.1) =
      (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).eulerChar 𝒦 := by
    obtain ⟨h0, hs⟩ := nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated f
      ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m)) hq (𝒦.comap γ.1) 𝒦
    exact eulerChar_eq_of_equiv (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m)))
      (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))) (𝒦.comap γ.1) 𝒦 rfl h0 hs
  have e4 : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).eulerChar 𝒦 =
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)).eulerChar 𝒦 := by
    obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso γ.1 𝓛 m
    obtain ⟨h0, hs, -⟩ := nonempty_cechEquiv_ofModules_of_iso f e 𝒦
    exact eulerChar_eq_of_equiv (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m)))
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)) 𝒦 𝒦 rfl h0 hs
  rw [e1, e2, e3, e4]

end Chain

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

section FiniteKernel

variable (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
  (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
  (g : ℕ) [SmoothOfRelativeDimension g f]
  (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
  (γ : SchemeHomOver f f)
  (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
      L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
  (hfin : IsFinite (L.endKerStr γ))
  (p q : Polynomial ℚ)
  (hp : ∀ m : ℕ, ((OModulePresheaf.ofModules f
      (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)).eulerChar 𝒦 : ℚ) = p.eval (m : ℚ))
  (hq : ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ))

include hA hγ hfin hp hq h𝓛 in
/-- A finite-kernel endomorphism scales the Euler coefficient by its actual degree. -/
theorem coeff_eq_endDegree_mul_coeff_of_isFinite : p.coeff g = (L.endDegree γ : ℚ) * q.coeff g := by
  classical
  have : IsProper f := hA.proper
  have : Smooth f := hA.smooth
  have : ConnectedSpace A := connectedSpace hA
  have : IsIntegral A := AbelianSchemePropertyBundle.isIntegral_of_field hA
  have : IsFinite (L.endKerStr γ) := hfin
  have : IsFinite γ.1 := RelativeGroupLaw.isFinite_of_isFinite_endKerStr K f L γ hγ
  have : Flat γ.1 := AbelianSchemePropertyBundle.flat_of_isFinite K hA γ
  obtain ⟨-, -, hrank⟩ := RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
    K f L γ
  set G : OModulePresheaf f := pushforwardUnit f γ.1 with hG
  have hGc : G.IsCoherent := isCoherent f γ.1
  have hGq : G.IsQuasicoherent := isQuasicoherent f γ.1
  have hGs : G.SupportedIn ⊤ := supportedIn_top f γ.1
  obtain ⟨p', -, hp'⟩ := exists_polynomial_forall_eulerChar_twist_tensorPow_eq f 𝒦 G hGc hGq ⊤ hGs g
    (krullDim_top_le (f := f) g) 𝓛 h𝓛.1
  have hpp : p' = p := by
    refine Polynomial.eq_of_infinite_eval_eq p' p
      ((Set.infinite_range_of_injective Nat.cast_injective).mono ?_)
    rintro _ ⟨m, rfl⟩
    change p'.eval (m : ℚ) = p.eval (m : ℚ)
    rw [← hp' m, ← hp m, hG, eulerChar_twist_eq f 𝒦 𝓛 h𝓛 γ m]
  obtain ⟨U₀, 𝔭, -, h𝔭⟩ := exists_chart_prime (A := A) 𝒦
  have hlead := coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq f 𝒦 𝓛 h𝓛.1 g
    (SmoothOfRelativeDimension.topologicalKrullDim_le f g) q hq G hGc hGq p' hp' U₀ 𝔭 h𝔭
  have hrk : Module.rankAtStalk (R := Γ(A, U₀.1)) (G.obj U₀.1) 𝔭 = L.endDegree γ :=
    rankAtStalk_pushforwardUnit_obj f γ.1 U₀ (L.endDegree γ) (fun y => (hrank y).symm) 𝔭
  rw [← hpp, hlead, hrk]

end FiniteKernel

end JacobianVarieties.Picard.Proofs.EndDegreeCoefficient.P2mDegLead
