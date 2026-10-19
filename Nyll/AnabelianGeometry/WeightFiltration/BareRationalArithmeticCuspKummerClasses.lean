/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalThirdCuspFiberCoordinates
import Nyll.AnabelianGeometry.WeightFiltration.FixedRationalCuspDecompositionTransport
import Nyll.AnabelianGeometry.WeightFiltration.FixedLabelCuspKummerClass
import Nyll.EtaleFundamentalGroups.Cohomology.IsomCuspCoordinateRatios
import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroValuePower
import Nyll.JacobianVarieties.Kummer.RationalConfigurationPairKummerAllOrders
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairOrders

/-! # Actual cusp Kummer classes with the original scalar

The original scalar transport is unpacked once. Both fixed arithmetic labels
are chosen before the cusp. The original point in its transported fiber is
used at every cusp, and the prescribed geometric conjugator moves its target
point. No new scalar or generic radical is selected at another cusp.
-/
noncomputable section
open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups.Cohomology
open scoped RatFunc FintypeCatDiscrete

namespace AnabelianGeometry.WeightFiltration
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra

local instance (priority := 2000) cuspClassesSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

@[instance_reducible]
private def cuspRootsAction
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] (n : ℕ) :
    MulDistribMulAction Gal(κ/k) (rootsOfUnity n κ) where
  smul σ ζ := restrictRootsOfUnity σ.toRingHom n ζ
  one_smul ζ := by apply Subtype.ext; apply Units.ext; rfl
  mul_smul σ τ ζ := by apply Subtype.ext; apply Units.ext; rfl
  smul_one σ := (restrictRootsOfUnity σ.toRingHom n).map_one
  smul_mul σ ζ ε := (restrictRootsOfUnity σ.toRingHom n).map_mul ζ ε

/-- At one actual cusp, compose the same Isom-displacement calculation with
fixed-label descent. Only the lift `p` varies with the Galois automorphism;
the two radical coordinates are fixed at `x₀` and `γ • e.val x₀` beforehand.
This helper is private because supplying its decomposition and coordinate
premises is the responsibility of the actual named-cover caller. -/
private theorem sameIsom_cusp_class_of_actual_coordinates
    {k κ : Type} {P X Y : Type*} [Field k] [Field κ] [Algebra k κ] [IsGalois k κ]
    [Group P] (n : ℕ+)
    [MulDistribMulAction Gal(κ/k) (rootsOfUnity (n : ℕ) κ)]
    [Torsor (rootsOfUnity (n : ℕ) κ) X]
    [Torsor (rootsOfUnity (n : ℕ) κ) Y]
    [MulAction P X] [MulAction P Y]
    (q : P →* Gal(κ/k))
    (hX : ∀ (p : P) (ζ : rootsOfUnity (n : ℕ) κ) (x : X),
      p • (ζ • x) = (q p • ζ) • (p • x))
    (hY : ∀ (p : P) (ζ : rootsOfUnity (n : ℕ) κ) (y : Y),
      p • (ζ • y) = (q p • ζ) • (p • y))
    (e : KernelTorsorIso (X := X) (Y := Y) q (rootsOfUnity (n : ℕ) κ))
    (x₀ : X) (a : kˣ) (β : κˣ)
    (hβ : β ^ (n : ℕ) = Units.map (algebraMap k κ).toMonoidHom a)
    (hdisp : ∀ p : P,
      _root_.KummerTheory.rootQuotient (K := k) β (q p) =
        ((p • e.val (p⁻¹ • x₀)) /ₛ e.val x₀ : rootsOfUnity (n : ℕ) κ).val)
    (αs αt : Gal(κ/k)) (v vt : (ZMod (n : ℕ))ˣ)
    (hv : ∀ ζ : rootsOfUnity (n : ℕ) κ,
      (αt * αs⁻¹) (ζ.val : κ) = (ζ.val : κ) ^ (v : ZMod (n : ℕ)).val)
    (hvt : ∀ ζ : rootsOfUnity (n : ℕ) κ,
      αt (ζ.val : κ) = (ζ.val : κ) ^ (vt : ZMod (n : ℕ)).val)
    (D : Subgroup P)
    (hD : Function.Surjective (fun p : D => q p.val))
    (γ : P) (hγ : q γ = 1)
    (f g : kˣ) (S : X → κ) (T : Y → κ)
    (hSn : ∀ x, S x ^ (n : ℕ) = algebraMap k κ (f : k))
    (hTn : ∀ y, T y ^ (n : ℕ) = algebraMap k κ (g : k))
    (hSμ : ∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
      S (ζ • x) = αs (ζ.val : κ) * S x)
    (hTμ : ∀ (ζ : rootsOfUnity (n : ℕ) κ) y,
      T (ζ • y) = αt (ζ.val : κ) * T y)
    (hSD : ∀ (p : P), p ∈ D → ∀ x, S (p • x) = q p (S x))
    (hTD : ∀ (p : P), p ∈ D → ∀ y,
      T ((γ * p * γ⁻¹) • y) = q p (T y)) :
    ∃ d : kˣ,
      g = a ^ (vt : ZMod (n : ℕ)).val * f ^ (v : ZMod (n : ℕ)).val * d ^ (n : ℕ) := by
  have hS0 : S x₀ ≠ 0 := by
    intro hz
    have h := hSn x₀
    rw [hz, zero_pow n.ne_zero] at h
    exact ((map_ne_zero (algebraMap k κ)).mpr f.ne_zero) h.symm
  have hT0 : T (γ • e.val x₀) ≠ 0 := by
    intro hz
    have h := hTn (γ • e.val x₀)
    rw [hz, zero_pow n.ne_zero] at h
    exact ((map_ne_zero (algebraMap k κ)).mpr g.ne_zero) h.symm
  let rs : κˣ := Units.mk0 (S x₀) hS0
  let rt : κˣ := Units.mk0 (T (γ • e.val x₀)) hT0
  have hrs : rs ^ (n : ℕ) = Units.map (algebraMap k κ).toMonoidHom f := by
    apply Units.ext
    exact hSn x₀
  have hrt : rt ^ (n : ℕ) = Units.map (algebraMap k κ).toMonoidHom g := by
    apply Units.ext
    exact hTn (γ • e.val x₀)
  apply _root_.KummerTheory.cusp_class_of_fixed_label_radical_ratios
    (n : ℕ) (v : ZMod (n : ℕ)).val (vt : ZMod (n : ℕ)).val
    a f g β rs rt hβ hrs hrt
  intro σ
  obtain ⟨p, hp⟩ := hD σ
  change q p.val = σ at hp
  have hratio := KernelTorsorIso.cusp_coordinate_ratio_with_kernel_conjugator
    (n : ℕ) q hX hY e x₀ x₀ p.val γ hγ αs αt S T hSμ hTμ
    (hSD p.val p.property x₀) (hTD p.val p.property (γ • e.val x₀)) hS0 hT0
  dsimp only at hratio
  have hdispVal : q p.val (β : κ) / (β : κ) =
      (((p.val • e.val (p.val⁻¹ • x₀)) /ₛ e.val x₀ :
        rootsOfUnity (n : ℕ) κ).val : κ) := by
    simpa only [_root_.KummerTheory.rootQuotient, AlgEquiv.smul_units_def,
      Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_ofClass] using
      congrArg (fun z : κˣ => (z : κ)) (hdisp p.val)
  rw [← hdispVal, hp] at hratio
  change σ (rt : κ) / (rt : κ) =
    αt (σ (β : κ) / (β : κ)) *
      αt (αs.symm (σ (rs : κ) / (rs : κ))) at hratio
  have hβlabel := _root_.KummerTheory.label_change_radical_ratio_power
    (n : ℕ) (vt : ZMod (n : ℕ)).val αt hvt a β hβ σ
  have hslabel := _root_.KummerTheory.label_change_radical_ratio_power
    (n : ℕ) (v : ZMod (n : ℕ)).val (αt * αs⁻¹) hv f rs hrs σ
  change αt (αs.symm (σ (rs : κ) / (rs : κ))) =
    (σ (rs : κ) / (rs : κ)) ^ (v : ZMod (n : ℕ)).val at hslabel
  rw [hβlabel, hslabel] at hratio
  exact hratio


/-- Same covers, exponent, Isom, scalar and fiber point give a class relation
at every third rational cusp. The two coefficient units are common to all cusps. -/
theorem rationalConfiguration_scalarRoots_cusp_classes
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
    (eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ω₂)
    (hP : ∀ p, arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP p) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) p)
    (hΔ : ∀ p, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ p) =
      eP (rationalConfigurationGeometricInclusion k κ s Ω₁ p))
    (σ : s ≃ t)
    (hI : ∀ c : s, ∃ d : rationalConfigurationGeometricGroup k κ t Ω₂,
      (rationalConfigurationChosenInertia k κ s Ω₁
        (rationalConfigurationBoundaryPlace k κ s c)).map eΔ.toMonoidHom =
      (rationalConfigurationChosenInertia k κ t Ω₂
        (rationalConfigurationBoundaryPlace k κ t (σ c))).map (MulAut.conj d).toMonoidHom)
    (a b : s) (n : ℕ+)
    (us : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen s).ι) n)
    (ut : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen t).ι) n)
    (hordS : ∀ P : Place κ (RatFunc κ),
      P.ord (algebraMap (RatFunc k) (RatFunc κ) (us.val : RatFunc k)) =
        (if P = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if P = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0))
    (hordT : ∀ P : Place κ (RatFunc κ),
      P.ord (algebraMap (RatFunc k) (RatFunc κ) (ut.val : RatFunc k)) =
        (if P = (rationalConfigurationBoundaryPlace k κ t (σ a)).val then 1 else 0) -
        (if P = (rationalConfigurationBoundaryPlace k κ t (σ b)).val then 1 else 0))
    (H : RationalConfigurationArithmeticScalarTransportWithRoots
      k κ s t Ω₁ Ω₂ n us ut eP) :
    ∃ u v vt : (ZMod (n : ℕ))ˣ, ∃ A : kˣ, ∃ β : κˣ,
      β ^ (n : ℕ) = Units.map (algebraMap k κ).toMonoidHom A ∧
      ∀ (c : s), c ≠ a → c ≠ b →
        let Vs := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
          (rationalConfigurationBoundaryPlace k κ s c)).choose
        let Vt := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ t
          (rationalConfigurationBoundaryPlace k κ t (σ c))).choose
        ∃ d : kˣ,
          Vt.evalAt (ut.val : RatFunc k) ^ (u : ZMod (n : ℕ)).val =
            (A : k) ^ (vt : ZMod (n : ℕ)).val *
              Vs.evalAt (us.val : RatFunc k) ^ (v : ZMod (n : ℕ)).val * (d : k) ^ (n : ℕ) := by
  let : Algebra (rationalConfigurationOpen s : Scheme).functionField Ω₁ :=
    rationalConfigurationOriginalAmbientAlgebra k κ s Ω₁
  let : Algebra (rationalConfigurationOpen t : Scheme).functionField Ω₂ :=
    rationalConfigurationOriginalAmbientAlgebra k κ t Ω₂
  let : Algebra (RatFunc k) Ω₁ := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω₁
  let : Algebra (RatFunc k) Ω₂ := rationalConfigurationArithmeticAmbientAlgebra k κ t Ω₂
  let : Algebra κ Ω₁ := rationalConfigurationConstantAmbientAlgebra k κ s Ω₁
  let : Algebra κ Ω₂ := rationalConfigurationConstantAmbientAlgebra k κ t Ω₂
  let : IsSepClosure (rationalConfigurationOpen s : Scheme).functionField Ω₁ :=
    (rationalConfigurationOriginalField_suppliers k κ s Ω₁).2.2.2.2.1
  let : IsSepClosure (rationalConfigurationOpen t : Scheme).functionField Ω₂ :=
    (rationalConfigurationOriginalField_suppliers k κ t Ω₂).2.2.2.2.1
  obtain ⟨u, ts, tt, hrootS, hrootT, _hSsemi, hTsemi, hEsemi,
    E, hEμ, hEH, x₀, A, β, hβn, hβ⟩ := H
  let := ts
  let := tt
  let hn : IsUnit ((n : ℕ) : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
  let M := projectiveLineRatFuncModel k
  let iS : (rationalConfigurationOpen s : Scheme) ⟶ M.C := (rationalConfigurationOpen s).ι
  let iT : (rationalConfigurationOpen t : Scheme) ⟶ M.C := (rationalConfigurationOpen t).ι
  let : IsOpenImmersion iS := rootedScalarArithmeticChart_isOpenImmersion k s
  let : IsOpenImmersion iT := rootedScalarArithmeticChart_isOpenImmersion k t
  let Fs := fiber (rationalConfigurationArithmeticBasePoint k κ s Ω₁)
  let Ft := fiber (rationalConfigurationArithmeticBasePoint k κ t Ω₂)
  let AS := M.openKummerCover (M.openBoundaryPlaces iS) n hn us iS
    (rationalConfigurationOpen_denseRange k s) (M.place_not_mem_openBoundaryPlaces iS)
  let AT := M.openKummerCover (M.openBoundaryPlaces iT) n hn
    (ut ^ (u : ZMod (n : ℕ)).val) iT
    (rationalConfigurationOpen_denseRange k t) (M.place_not_mem_openBoundaryPlaces iT)
  let ATs := (coverTransportOfAutEquiv Fs Ft eP).functor.obj AS
  let ea := coverTransportFiberEquiv Fs Ft eP AS
  let := transportedFiberTorsor ea
  let := cuspRootsAction k κ (n : ℕ)
  let q := arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
    (rationalConfigurationArithmeticBasePoint k κ t Ω₂)
  let inc := rationalConfigurationGeometricInclusion k κ t Ω₂
  have hSord : ∀ P : Place κ (RatFunc κ),
      P.ord (algebraMap (RatFunc k) (RatFunc κ) (us.val : RatFunc k)) =
        (1 : ℤ) * ((if P = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
          (if P = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) := by
    intro P
    simpa only [one_mul] using hordS P
  have hTord : ∀ P : Place κ (RatFunc κ),
      P.ord (algebraMap (RatFunc k) (RatFunc κ)
        ((ut ^ (u : ZMod (n : ℕ)).val).val : RatFunc k)) =
      ((u : ZMod (n : ℕ)).val : ℤ) *
        ((if P = (rationalConfigurationBoundaryPlace k κ t (σ a)).val then 1 else 0) -
          (if P = (rationalConfigurationBoundaryPlace k κ t (σ b)).val then 1 else 0)) := by
    intro P
    change P.ord (algebraMap (RatFunc k) (RatFunc κ)
      ((ut.val : RatFunc k) ^ (u : ZMod (n : ℕ)).val)) = _
    rw [map_pow]
    simpa only [zpow_natCast, hordT] using
      P.ord_zpow (algebraMap (RatFunc k) (RatFunc κ) (ut.val : RatFunc k))
        ((u : ZMod (n : ℕ)).val : ℤ)
  obtain ⟨αs, hSc⟩ := rationalConfiguration_pair_thirdCusp_fiberCoordinates
    k κ s a b Ω₁ 1 n us hSord AS ts hrootS
  obtain ⟨αt, hTc⟩ := rationalConfiguration_pair_thirdCusp_fiberCoordinates
    k κ t (σ a) (σ b) Ω₂ ((u : ZMod (n : ℕ)).val : ℤ) n
      (ut ^ (u : ZMod (n : ℕ)).val) hTord AT tt hrootT
  obtain ⟨v, hv⟩ := _root_.KummerTheory.exists_unit_power_of_fixed_galois_label n
    (αt * αs⁻¹)
  obtain ⟨vt, hvt⟩ := _root_.KummerTheory.exists_unit_power_of_fixed_galois_label n αt
  let ξG := (rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ω₂
  have hex := arithmetic_exactSequence_of_isSepClosure k κ
    (rationalConfigurationOpen t : Scheme) ((rationalConfigurationOpen t).ι ≫ π k 1) ξG
  have heker : ∀ p : rationalConfigurationArithmeticGroup k κ t Ω₂,
      q p = 1 → ∀ x, E (p • x) = p • E x := by
    intro p hp x
    have hpker : p ∈ q.toMonoidHom.ker := hp
    have hprange : p ∈ inc.toMonoidHom.range := hex.2.2 ▸ hpker
    obtain ⟨d, rfl⟩ := hprange
    exact hEH d x
  let e : KernelTorsorIso (X := Ft.obj ATs) (Y := Ft.obj AT)
      q.toMonoidHom (rootsOfUnity (n : ℕ) κ) := ⟨E, hEμ, heker⟩
  refine ⟨u, v, vt, A, β, hβn, ?_⟩
  intro c hca hcb Vs Vt
  have htca : σ c ≠ σ a := fun h => hca (σ.injective h)
  have htcb : σ c ≠ σ b := fun h => hcb (σ.injective h)
  obtain ⟨huS, S₀, hSpow, hSscale, hSD⟩ := hSc c hca hcb
  obtain ⟨huTpow, T, hTpow, hTscale, hTD⟩ := hTc (σ c) htca htcb
  let hVs : Vs.IsRational :=
    (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
      (rationalConfigurationBoundaryPlace k κ s c)).choose_spec.1
  let hVt : Vt.IsRational :=
    (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ t
      (rationalConfigurationBoundaryPlace k κ t (σ c))).choose_spec.1
  have huT : Vt.ord (ut.val : RatFunc k) = 0 := by
    rw [← (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ t
      (rationalConfigurationBoundaryPlace k κ t (σ c))).choose_spec.2 (ut.val : RatFunc k)]
    exact rationalConfiguration_pair_order_eq_zero_at_other_label
      k κ t (σ a) (σ b) (σ c) htca htcb (ut.val : RatFunc k) hordT
  let f : kˣ := Vs.ordZeroValue hVs us.val huS
  let g : kˣ := Vt.ordZeroValue hVt ut.val huT ^ (u : ZMod (n : ℕ)).val
  have hgvalue : Vt.ordZeroValue hVt
      (ut ^ (u : ZMod (n : ℕ)).val).val huTpow = g :=
    Place.ordZeroValue_pow Vt hVt ut.val (u : ZMod (n : ℕ)).val huT huTpow
  let S : Ft.obj ATs → κ := fun x => S₀ (ea x)
  have hSroot (x : Ft.obj ATs) : S x ^ (n : ℕ) = algebraMap k κ (f : k) := hSpow (ea x)
  have hTroot (y : Ft.obj AT) : T y ^ (n : ℕ) = algebraMap k κ (g : k) := by
    rw [← hgvalue]
    exact hTpow y
  have hSscale' (ζ : rootsOfUnity (n : ℕ) κ) (x : Ft.obj ATs) :
      S (ζ • x) = αs (ζ.val : κ) * S x := by
    change S₀ (ea (ea.symm (ζ • ea x))) = _
    rw [ea.apply_symm_apply]
    exact hSscale ζ (ea x)
  let Ds := rationalConfigurationChosenDecomposition k κ s Ω₁
    (rationalConfigurationBoundaryPlace k κ s c)
  let Dt := rationalConfigurationChosenDecomposition k κ t Ω₂
    (rationalConfigurationBoundaryPlace k κ t (σ c))
  let D := Ds.map eP.toMonoidHom
  have hqD : ∀ τ : Gal(κ/k), ∃ p : rationalConfigurationArithmeticGroup k κ t Ω₂,
      p ∈ D ∧ q p = τ := by
    intro τ
    obtain ⟨p, hp⟩ := rationalConfigurationChosenDecomposition_arithmetic_surjective
      k κ s Ω₁ (rationalConfigurationBoundaryPlace k κ s c) τ
    exact ⟨eP p.val, ⟨p.val, p.property, rfl⟩, (hP p.val).trans hp⟩
  obtain ⟨d, hd⟩ := hI c
  have hD : D = Dt.map (MulAut.conj (inc d)).toMonoidHom :=
    rationalConfigurationChosenDecomposition_map_of_inertia
      k κ s t hs ht Ω₁ Ω₂ eP eΔ hΔ
      (rationalConfigurationBoundaryPlace k κ s c)
      (rationalConfigurationBoundaryPlace k κ t (σ c)) d hd
  let γ := (inc d)⁻¹
  have hqγ : q γ = 1 := by
    have hker : q.toMonoidHom.ker = inc.toMonoidHom.range := hex.2.2
    have hqinc : inc d ∈ q.toMonoidHom.ker := by
      rw [hker]
      exact ⟨d, rfl⟩
    change q ((inc d)⁻¹) = 1
    rw [map_inv, show q (inc d) = 1 from hqinc, inv_one]
  have hSource (p : rationalConfigurationArithmeticGroup k κ t Ω₂) (hp : p ∈ D)
      (x : Ft.obj ATs) : S (p • x) = q p (S x) := by
    obtain ⟨ps, hps, rfl⟩ := hp
    change S₀ (ea (eP ps • x)) = _
    rw [coverTransportFiberEquiv_smul, eP.symm_apply_apply, hSD ps hps]
    exact congrArg (fun τ : Gal(κ/k) => τ (S₀ (ea x))) (hP ps).symm
  have hTarget (p : rationalConfigurationArithmeticGroup k κ t Ω₂) (hp : p ∈ D)
      (y : Ft.obj AT) : T ((γ * p * γ⁻¹) • y) = q p (T y) := by
    have hmem : γ * p * γ⁻¹ ∈ Dt := by
      rw [hD] at hp
      obtain ⟨pt, hpt, hptEq⟩ := hp
      have hpEq : p = inc d * pt * (inc d)⁻¹ := hptEq.symm
      have hconj : γ * p * γ⁻¹ = pt := by
        rw [hpEq]
        simp only [γ, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      rw [hconj]
      exact hpt
    rw [hTD _ hmem]
    change q (γ * p * γ⁻¹) (T y) = q p (T y)
    have hqconj : q (γ * p * γ⁻¹) = q p := by
      simp only [map_mul, map_inv, hqγ, one_mul, inv_one, mul_one]
    exact congrArg (fun τ : Gal(κ/k) => τ (T y)) hqconj
  have hqD' : Function.Surjective (fun p : D => q.toMonoidHom p.val) := by
    intro τ
    obtain ⟨p, hp, hq⟩ := hqD τ
    exact ⟨⟨p, hp⟩, hq⟩
  obtain ⟨dc, hdc⟩ := sameIsom_cusp_class_of_actual_coordinates
    (k := k) (κ := κ) (P := rationalConfigurationArithmeticGroup k κ t Ω₂)
    (X := Ft.obj ATs) (Y := Ft.obj AT)
    (n := n) (q := q.toMonoidHom) (hX := hEsemi) (hY := hTsemi)
    (e := e) (x₀ := x₀) (a := A) (β := β) (hβ := hβn) (hdisp := hβ)
    (αs := αs) (αt := αt) (v := v) (vt := vt) (hv := hv) (hvt := hvt)
    (D := D) (hD := hqD') (γ := γ) (hγ := hqγ)
    (f := f) (g := g) (S := S) (T := T)
    (hSn := hSroot) (hTn := hTroot) (hSμ := hSscale') (hTμ := hTscale)
    (hSD := hSource) (hTD := hTarget)
  exact ⟨dc, congrArg Units.val hdc⟩

end AnabelianGeometry.WeightFiltration
