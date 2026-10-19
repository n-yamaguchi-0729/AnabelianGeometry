/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.RatFuncRationalCuspInertiaImage
import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspArithmeticNormalizer

/-! # Normalizers of actual geometric rational cusps -/

noncomputable section
open AlgebraicCurve AlgebraicGeometry CategoryTheory SchemeTheory
open AlgebraicGeometry.FiniteEtale
open AnabelianGeometry.KummerTheory
open scoped RatFunc
attribute [local instance] Polynomial.algebra

namespace EtaleFundamentalGroups.Inertia
attribute [local instance] normalizationCommAlgGaloisAction
local instance (priority := 2000) {R K : Type*} [CommSemiring R] [Field K]
    [Algebra R (RatFunc K)] : SMul R (RatFunc K) :=
  (inferInstance : Algebra R (RatFunc K)).toSMul
universe u

private theorem rationalPlace_residueRetraction
    {k : Type u} [Field k] (V : Place k (RatFunc k)) (hV : V.IsRational) :
    ∃ r : V.toValuationSubring →ₐ[k] k,
      RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal V.toValuationSubring := by
  let e : k ≃ₐ[k] V.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId k V.ResidueField)
      ⟨V.algebraMap_residueField_injective, hV⟩
  let r : V.toValuationSubring →ₐ[k] k := e.symm.toAlgHom.comp
    (IsScalarTower.toAlgHom k V.toValuationSubring V.ResidueField)
  refine ⟨r, ?_⟩
  ext a
  change e.symm (IsLocalRing.residue V.toValuationSubring a) = 0 ↔
    a ∈ IsLocalRing.maximalIdeal V.toValuationSubring
  rw [← IsLocalRing.residue_eq_zero_iff]
  constructor
  · intro h
    exact e.symm.injective (h.trans (map_zero e.symm).symm)
  · intro h
    rw [h, map_zero]

variable {k κ Ω : Type u} [Field k] [Field κ] [Field Ω]
  [Algebra k κ] [Algebra (RatFunc k) Ω] [Algebra (RatFunc κ) Ω]
  [IsScalarTower (RatFunc k) (RatFunc κ) Ω]
  [IsAlgClosed κ] [IsAlgClosure k κ] [IsSepClosure k κ]
  (V : Place k (RatFunc k)) (hV : V.IsRational)
  (W : Place κ (RatFunc κ))
  (hord : ∀ x : RatFunc k,
    W.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x)
  [Algebra V.toValuationSubring Ω] [Algebra W.toValuationSubring Ω]
  [IsScalarTower V.toValuationSubring (RatFunc k) Ω]
  [IsScalarTower W.toValuationSubring (RatFunc κ) Ω]
  [Algebra k Ω] [Algebra κ Ω]
  [IsScalarTower k κ Ω] [IsScalarTower k (RatFunc k) Ω]
  [IsScalarTower κ (RatFunc κ) Ω]
  [IsGalois (RatFunc k) Ω] [Algebra.IsAlgebraic (RatFunc κ) Ω]
  [IsSepClosure (RatFunc k) Ω] [IsSepClosure (RatFunc κ) Ω] [IsSepClosed Ω]

/-- Every arithmetic Galois element has a lift normalizing the same geometric
cusp image. Qgeom is the literal integral-base contraction of Q. -/
theorem ratFunc_rationalPlace_geometric_normalizer_full_image
    (Q : Ideal (normalizationCommAlgCat V.toValuationSubring Ω)) [Q.IsMaximal]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of k)) (u : Y ⟶ X)
    (jgeom : Spec (.of (RatFunc κ)) ⟶ Y)
    (jarith : Spec (.of (RatFunc k)) ⟶ X)
    (hpoint : (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom) ≫ u =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith)
    (hbase : (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    let e := ratFuncRationalPlaceNormalizationEquiv V hV W hord (Ω := Ω)
    let Qgeom := Q.comap e.toRingHom
    let qgeom := fieldSourceAbsoluteGaloisHom (RatFunc κ) Ω jgeom
    let i := (pointedFundamentalGroupHom u
      (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom)
      (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith) hpoint).toMonoidHom
    let I := ((Qgeom.inertia Gal(Ω/RatFunc κ)).map qgeom.toMonoidHom).map i
    ∀ τ : Gal(κ/k), ∃ γ :
        Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith)),
      γ ∈ Subgroup.normalizer (I : Set _) ∧
      arithmeticFundamentalGroupHom k κ f
        (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith) γ = τ := by
  intro e Qgeom qgeom i I
  let : IsScalarTower k V.toValuationSubring Ω :=
    IsScalarTower.of_algebraMap_eq
      (R := k) (S := V.toValuationSubring) (A := Ω) (fun a => by
      calc
        algebraMap k Ω a =
            algebraMap (RatFunc k) Ω (algebraMap k (RatFunc k) a) :=
          IsScalarTower.algebraMap_apply k (RatFunc k) Ω a
        _ = algebraMap V.toValuationSubring Ω
            (algebraMap k V.toValuationSubring a) :=
          (IsScalarTower.algebraMap_apply V.toValuationSubring (RatFunc k) Ω
            (algebraMap k V.toValuationSubring a)).symm)
  obtain ⟨r, hr⟩ := rationalPlace_residueRetraction V hV
  have hI : I = (Q.inertia Gal(Ω/RatFunc k)).map
      (fieldSourceAbsoluteGaloisHom (RatFunc k) Ω jarith).toMonoidHom :=
    ratFunc_rationalPlace_pointed_inertia_image V hV W hord Q u jgeom jarith hpoint
  intro τ
  obtain ⟨γ, hγ, hτ⟩ := rationalCusp_arithmetic_normalizer_full_image
    k V.toValuationSubring (RatFunc k) κ Ω Q r hr f jarith hbase τ
  refine ⟨γ, ?_, hτ⟩
  simpa only [hI] using hγ

end EtaleFundamentalGroups.Inertia
