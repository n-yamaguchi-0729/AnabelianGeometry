/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenCurveCoverTorsor
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldMonodromyLift
import Mathlib.RingTheory.AdjoinRoot

/-!
# Generic-function coordinates on original arithmetic Kummer fibers

The local root/h coordinate is multiplied by the actual generic value of h.
The resulting coordinate has nth power equal to the specified generic value
of w, and retains the original root-scaling and generic Galois actions.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open JacobianVarieties.Kummer Opposite TopologicalSpace
open AlgebraicCurves.Geometry.Schemes.Proofs
open exists_root_fromNormalization_kummer_existsUnique_lift.KummerLift
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel.OpenKummer

private theorem specAutomorphism_eval_appTop
    {Ω : Type} [Field Ω] (σ : Ω ≃+* Ω) (v : Γ(Spec (.of Ω), ⊤)) :
    (Scheme.ΓSpecIso (.of Ω)).hom
        ((Spec.map (CommRingCat.ofHom σ.toRingHom)).appTop v) =
      σ ((Scheme.ΓSpecIso (.of Ω)).hom v) := by
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ.toRingHom)) v

private theorem rootCoordinate_precomp_field
    {Ω : Type} [Field Ω] {Y : Scheme} (V : Y.Opens) (T : Γ(Y, V))
    (σ : Ω ≃+* Ω) (s s' : Spec (.of Ω) ⟶ Y)
    (hs : s ⁻¹ᵁ V = ⊤) (hs' : s' ⁻¹ᵁ V = ⊤)
    (he : s' = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ s) :
    (Scheme.ΓSpecIso (.of Ω)).hom (s'.appLE V ⊤ hs'.ge T) =
      σ ((Scheme.ΓSpecIso (.of Ω)).hom (s.appLE V ⊤ hs.ge T)) := by
  subst s'
  let d := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have h := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE d s V ⊤ ⊤ hs.ge le_top) T
  change d.appLE ⊤ ⊤ le_top (s.appLE V ⊤ hs.ge T) =
    (d ≫ s).appLE V ⊤ hs'.ge T at h
  have htop : d.appLE ⊤ ⊤ le_top = d.appTop := d.appLE_eq_app
  have hv := ConcreteCategory.congr_hom htop (s.appLE V ⊤ hs.ge T)
  exact (congrArg (Scheme.ΓSpecIso (.of Ω)).hom (h.symm.trans hv)).trans
    (specAutomorphism_eval_appTop σ _)

/-- Evaluate a retained generic section equation on a literal affine point.
Only the composite point must land entirely in the selected open. -/
private theorem genericSection_point_evaluation
    {A Ω : Type} [CommRing A] [Field Ω]
    {Y : Scheme} (r : Spec (.of A) ⟶ Y)
    (W : Y.Opens) (T : Γ(Y, W)) (a : A)
    (hT : r.app W T =
      (Spec (.of A)).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso (.of A)).inv a))
    (l : A →+* Ω)
    (hrβ : (Spec.map (CommRingCat.ofHom l) ≫ r) ⁻¹ᵁ W = ⊤) :
    (Scheme.ΓSpecIso (.of Ω)).hom
      ((Spec.map (CommRingCat.ofHom l) ≫ r).appLE W ⊤ hrβ.ge T) = l a := by
  let d := Spec.map (CommRingCat.ofHom l)
  let v := (Scheme.ΓSpecIso (.of A)).inv a
  have hpull : (d ≫ r).app W T =
      (Spec (.of Ω)).presheaf.map (homOfLE le_top).op (d.appTop v) := by
    change d.app (r ⁻¹ᵁ W) (r.app W T) = _
    rw [hT]
    exact app_map d (homOfLE le_top) (homOfLE le_top) v
  have hcoord : (d ≫ r).appLE W ⊤ hrβ.ge T = d.appTop v :=
    appLE_of_app (d ≫ r) W hrβ T (d.appTop v) hpull
  have hnat := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom l)) v
  change (Scheme.ΓSpecIso (.of Ω)).hom (d.appTop v) =
    l ((Scheme.ΓSpecIso (.of A)).hom ((Scheme.ΓSpecIso (.of A)).inv a)) at hnat
  rw [Iso.inv_hom_id_apply] at hnat
  exact (congrArg (Scheme.ΓSpecIso (.of Ω)).hom hcoord).trans hnat


/-- The original arithmetic Kummer fiber is the full set of roots of the
actual generic value of `w`. Both the existing root-scaling and the original
generic Galois action are retained under the same coordinate equivalence. -/
theorem exists_arithmeticKummerFiber_genericRootEquiv
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (w : Pic0.openKummerUnits K F S n)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hi : ∀ (y : X) (x : closedPoints M.C), x.val = j y → M.placeOfPoint x ∉ S)
    (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] [Algebra X.functionField Ω]
    [IsSepClosure X.functionField Ω] :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let W := M.openKummerCover S n hn w j hj hi
    let g := j.functionFieldMap hj (M.ffEquiv (w.val : F))
    letI := kummerGeometricRootAction M S n w j hj hi hn ξ
    ∃ e : (FiniteEtale.fiber ξ).obj W ≃
        {β : Ω // β ^ (n : ℕ) = algebraMap X.functionField Ω g},
      (∀ (ζ : rootsOfUnity (n : ℕ) K) x,
        (e (ζ • x)).val = pointScalar (j ≫ M.toBase) ξ (ζ.val : K) * (e x).val) ∧
      ∀ (σ : Ω ≃ₐ[X.functionField] Ω) x,
        (e (FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
          (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ) • x)).val =
          σ (e x).val := by
  intro η ξ W g
  let := kummerGeometricRootAction M S n w j hj hi hn ξ
  let A := AdjoinRoot (Polynomial.X ^ (n : ℕ) - Polynomial.C g)
  let f := M.openKummerGenericMap S n w j hj
  let π := f.fromNormalization
  obtain ⟨V, _hV, hxV, h, hh, v, _hv, T, hTpow, hTgen, hlift⟩ :=
    exists_kummer_root_chart M S n w j hj hi hn (ξ default)
  have : Nonempty V := ⟨⟨ξ default, hxV⟩⟩
  have hξ : ξ ⁻¹ᵁ V = ⊤ := point_preimage_top ξ V hxV
  let l := fiberLiftEquiv ξ W
  let c : {s : Spec (.of Ω) ⟶ f.normalization // s ≫ π = ξ} → Γ(Spec (.of Ω), ⊤) :=
    rootLiftCoordinate π V ξ hξ T
  let q : (FiniteEtale.fiber ξ).obj W → Ω :=
    fun x => (Scheme.ΓSpecIso (.of Ω)).hom (c (l x))
  have hqinj : Function.Injective q := by
    intro x y hxy
    apply l.injective
    apply rootLiftCoordinate_injective π V ξ hξ T (n : ℕ) v hTpow (hlift _ ξ hξ)
    exact (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.injective hxy
  have hqpow (x y : (FiniteEtale.fiber ξ).obj W) : q x ^ (n : ℕ) = q y ^ (n : ℕ) := by
    change ((Scheme.ΓSpecIso (.of Ω)).hom (c (l x))) ^ (n : ℕ) =
      ((Scheme.ΓSpecIso (.of Ω)).hom (c (l y))) ^ (n : ℕ)
    rw [← map_pow, ← map_pow]
    exact congrArg (Scheme.ΓSpecIso (.of Ω)).hom
      ((rootLiftCoordinate_pow π V ξ hξ T (n : ℕ) v hTpow (l x)).trans
        (rootLiftCoordinate_pow π V ξ hξ T (n : ℕ) v hTpow (l y)).symm)
  let R := {β : Ω // β ^ (n : ℕ) = algebraMap X.functionField Ω g}
  let ρ (β : R) : A →ₐ[X.functionField] Ω :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId X.functionField Ω) β.val (by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      exact sub_eq_zero.mpr β.property)
  let rpoint (β : R) : Spec (.of Ω) ⟶ f.normalization :=
    Spec.map (CommRingCat.ofHom (ρ β).toRingHom) ≫ f.toNormalization
  have hover (β : R) : rpoint β ≫ π = ξ := by
    dsimp only [rpoint]
    rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
    change Spec.map (CommRingCat.ofHom (ρ β).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField A)) ≫
        X.fromSpecStalk (genericPoint X)) = _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hmap : (ρ β).toRingHom.comp (algebraMap X.functionField A) =
        algebraMap X.functionField Ω := by
      ext b
      exact (ρ β).commutes b
    exact congrArg (fun φ : X.functionField →+* Ω =>
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X)) hmap
  let r (β : R) : (FiniteEtale.fiber ξ).obj W := l.symm ⟨rpoint β, hover β⟩
  have hr (β : R) : q (r β) = algebraMap X.functionField Ω h⁻¹ * β.val := by
    have hp : (rpoint β) ⁻¹ᵁ (π ⁻¹ᵁ V) = ⊤ :=
      rootLift_preimage π V ξ hξ ⟨rpoint β, hover β⟩
    have heval := genericSection_point_evaluation f.toNormalization (π ⁻¹ᵁ V) T
      (algebraMap X.functionField A h⁻¹ * AdjoinRoot.root _) hTgen (ρ β).toRingHom hp
    change (Scheme.ΓSpecIso (.of Ω)).hom (c (l (l.symm ⟨rpoint β, hover β⟩))) = _
    refine (congrArg (fun z => (Scheme.ΓSpecIso (.of Ω)).hom (c z))
      (l.apply_symm_apply ⟨rpoint β, hover β⟩)).trans (heval.trans ?_)
    have hρroot : ρ β (AdjoinRoot.root _) = β.val :=
      AdjoinRoot.liftAlgHom_root _ _ _ _
    change ρ β (algebraMap X.functionField A h⁻¹ * AdjoinRoot.root _) = _
    rw [map_mul, AlgHom.commutes, hρroot]
  let H : Ω := algebraMap X.functionField Ω h
  have hH : H ≠ 0 := (map_ne_zero (algebraMap X.functionField Ω)).mpr hh
  let Q (x : (FiniteEtale.fiber ξ).obj W) : Ω := H * q x
  have hQr (β : R) : Q (r β) = β.val := by
    change H * q (r β) = β.val
    rw [hr]
    change algebraMap X.functionField Ω h *
      (algebraMap X.functionField Ω h⁻¹ * β.val) = β.val
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hh, map_one, one_mul]
  have hQinj : Function.Injective Q := by
    intro x y hxy
    exact hqinj (mul_left_cancel₀ hH hxy)
  have hnΩ : IsUnit ((n : ℕ) : Ω) := by
    simpa only [map_natCast] using hn.map (pointScalar (j ≫ M.toBase) ξ)
  let : NeZero ((n : ℕ) : Ω) := ⟨hnΩ.ne_zero⟩
  obtain ⟨β₀, hβ₀⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap X.functionField Ω g) (n : ℕ)
  let b : R := ⟨β₀, hβ₀⟩
  have hQpow (x : (FiniteEtale.fiber ξ).obj W) :
      Q x ^ (n : ℕ) = algebraMap X.functionField Ω g := by
    calc
      Q x ^ (n : ℕ) = H ^ (n : ℕ) * q x ^ (n : ℕ) := mul_pow _ _ _
      _ = H ^ (n : ℕ) * q (r b) ^ (n : ℕ) :=
        congrArg (H ^ (n : ℕ) * ·) (hqpow x (r b))
      _ = Q (r b) ^ (n : ℕ) := (mul_pow _ _ _).symm
      _ = b.val ^ (n : ℕ) := congrArg (· ^ (n : ℕ)) (hQr b)
      _ = algebraMap X.functionField Ω g := b.property
  let e : (FiniteEtale.fiber ξ).obj W ≃ R := {
    toFun := fun x => ⟨Q x, hQpow x⟩
    invFun := r
    left_inv := fun x => hQinj (hQr ⟨Q x, hQpow x⟩)
    right_inv := fun β => Subtype.ext (hQr β) }
  refine ⟨e, ?_, ?_⟩
  · intro ζ x
    have hscaleq : q (ζ • x) = pointScalar (j ≫ M.toBase) ξ (ζ.val : K) * q x := by
      let d := kummerNormalizationRootScale M S n w j hj ζ
      have hd : d.hom ≫ π = π :=
        EtaleFundamentalGroups.Inertia.normalizationSourceIso_hom_fromNormalization _ _ _ _
      have hpre : π ⁻¹ᵁ V ≤ d.hom ⁻¹ᵁ (π ⁻¹ᵁ V) := by
        rw [← Scheme.Hom.comp_preimage, hd]
      have hscale := kummerNormalizationRootScale_localRoot M S n w j hj V h T hTgen ζ
      have hcoord := rootLiftCoordinate_comp π V ξ hξ T d.hom hd hpre
        ((j ≫ M.toBase).appLE ⊤ V le_top ((Scheme.ΓSpecIso (.of K)).inv (ζ.val : K)))
        hscale (l x)
      have hl : l (ζ • x) =
          ⟨(l x).1 ≫ d.hom,
            (Category.assoc _ _ _).trans ((congrArg ((l x).1 ≫ ·) hd).trans (l x).2)⟩ := by
        apply Subtype.ext
        exact fiberLiftEquiv_naturality ξ (kummerCoverRootScale M S n w j hj hi hn ζ).hom x
      change (Scheme.ΓSpecIso (.of Ω)).hom (c (l (ζ • x))) = _
      rw [hl]
      change (Scheme.ΓSpecIso (.of Ω)).hom (rootLiftCoordinate π V ξ hξ T _) = _
      apply (congrArg (Scheme.ΓSpecIso (.of Ω)).hom hcoord).trans
      apply (map_mul (Scheme.ΓSpecIso (.of Ω)).hom.hom _ _).trans
      exact congrArg (fun z : Γ(Spec (.of Ω), ⊤) =>
        (Scheme.ΓSpecIso (.of Ω)).hom z * q x)
        (appLE_baseScalar (j ≫ M.toBase) ξ V hξ ((Scheme.ΓSpecIso (.of K)).inv (ζ.val : K)))
    change H * q (ζ • x) = pointScalar (j ≫ M.toBase) ξ (ζ.val : K) * (H * q x)
    rw [hscaleq, mul_left_comm]
  · intro σ x
    let a := FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)
    have hl : (l (a • x)).val =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (l x).val :=
      FiniteEtale.fundamentalGroupHom_field_fiberLift
        (X.fromSpecStalk (genericPoint X)) W σ x
    have hq : q (a • x) = σ (q x) :=
      rootCoordinate_precomp_field (π ⁻¹ᵁ V) T σ.toRingEquiv
        (l x).val (l (a • x)).val (rootLift_preimage π V ξ hξ (l x))
        (rootLift_preimage π V ξ hξ (l (a • x))) hl
    change H * q (a • x) = σ (H * q x)
    rw [hq, map_mul, show σ H = H from σ.commutes h]

end AlgebraicCurve.CurveModel.OpenKummer
