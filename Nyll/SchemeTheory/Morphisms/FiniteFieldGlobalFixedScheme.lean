/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.FiniteFieldFrobeniusFixedScheme
public import Nyll.SchemeTheory.Morphisms.FiniteFieldRelativeFixedScheme
public import Nyll.SchemeTheory.Morphisms.Frobenius
public import Nyll.SchemeTheory.Morphisms.FrobeniusOver
public import Nyll.SchemeTheory.Etale.Neighborhoods
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.RingTheory.RingHom.FiniteType

/-!
# Frobenius fixed schemes of finite-type separated schemes

The actual equalizer of a positive Frobenius power and the identity is
finite étale over the finite base field. The affine calculation is transported
through the pullback of an affine open cover. Its geometric base change is
the actual equalizer of the corresponding relative Frobenius power.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Restricting an endomorphism along an invariant monomorphism restricts its
actual fixed scheme. Both limit statements are supplied by the existing
equalizer precomposition and monomorphism postcomposition constructions. -/
theorem exists_fixedEqualizerPullbackIso
    {U X : Scheme.{u}} (j : U ⟶ X) [Mono j]
    (v : U ⟶ U) (w : X ⟶ X) (hw : v ≫ j = j ≫ w) :
    ∃ e : equalizer v (𝟙 U) ≅ pullback (equalizer.ι w (𝟙 X)) j,
      e.hom ≫ pullback.snd (equalizer.ι w (𝟙 X)) j = equalizer.ι v (𝟙 U) := by
  have hc : equalizer.ι v (𝟙 U) ≫ (j ≫ w) =
      equalizer.ι v (𝟙 U) ≫ (j ≫ 𝟙 X) := by
    rw [← hw, ← Category.assoc, equalizer.condition]
    simp only [Category.comp_id]
  have hlocal : IsLimit (Fork.ofι (equalizer.ι v (𝟙 U)) hc) := by
    refine Fork.isLimitOfIsos _
      (isEqualizerCompMono (equalizerIsEqualizer v (𝟙 U)) j)
      (Fork.ofι (equalizer.ι v (𝟙 U)) hc)
      (Iso.refl U) (Iso.refl X) (Iso.refl _) ?_ ?_ ?_
    · simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using hw.symm
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · simp only [Iso.refl_hom, Fork.ι_ofι, Category.id_comp, Category.comp_id]
      rfl
  let hrestrict := isLimitPrecompFork j (equalizerIsEqualizer w (𝟙 X))
    (pullback.isLimit (equalizer.ι w (𝟙 X)) j)
  refine ⟨hlocal.conePointUniqueUpToIso hrestrict, ?_⟩
  exact IsLimit.conePointUniqueUpToIso_hom_comp hlocal hrestrict
    WalkingParallelPair.zero

private theorem finiteFieldFrobenius_pow_naturality
    (k : Type u) [Field k] [Fintype k] {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (j : U ⟶ X) (m : ℕ) :
    ((End.of (U.finiteFieldFrobenius k)) ^ m).asHom ≫ j =
      j ≫ ((End.of (X.finiteFieldFrobenius k)) ^ m).asHom := by
  induction m with
  | zero => simp only [pow_zero, End.one_asHom, Category.id_comp, Category.comp_id]
  | succ m ih =>
      rw [pow_succ', End.mul_asHom, Category.assoc,
        Scheme.finiteFieldFrobenius_naturality, ← Category.assoc, ih,
        Category.assoc, pow_succ', End.mul_asHom]

private theorem affine_finiteFieldFrobenius_fixedScheme_etale
    (k : Type u) [Field k] [Fintype k] (A : CommRingCat.{u})
    [(Spec A).Over (Spec (.of k))]
    [LocallyOfFiniteType (Spec A ↘ Spec (.of k))] (m : ℕ) (hm : 0 < m) :
    Etale (equalizer.ι
      (((End.of ((Spec A).finiteFieldFrobenius k)) ^ m).asHom)
      (𝟙 (Spec A)) ≫ (Spec A ↘ Spec (.of k))) := by
  let φ : CommRingCat.of k ⟶ A := Spec.preimage (Spec A ↘ Spec (.of k))
  let : Algebra k A := φ.hom.toAlgebra
  have hφ : Spec.algebraMap k A = (Spec A ↘ Spec (.of k)) :=
    Spec.map_preimage _
  have hft : LocallyOfFiniteType (Spec.algebraMap k A) := hφ.symm ▸ inferInstance
  have : Algebra.FiniteType k A := RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft)
  rw [← hφ]
  exact (finiteFieldFrobenius_fixedScheme_finite_etale k A m hm).2

namespace Scheme

variable (k : Type u) [Field k] [Fintype k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]

private theorem finiteFieldFrobenius_fixedScheme_etale
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (m : ℕ) (hm : 0 < m) :
    Etale (equalizer.ι (((End.of (X.finiteFieldFrobenius k)) ^ m).asHom) (𝟙 X) ≫
      (X ↘ Spec (.of k))) := by
  let f := X ↘ Spec (.of k)
  let v := ((End.of (X.finiteFieldFrobenius k)) ^ m).asHom
  let ι := equalizer.ι v (𝟙 X)
  let 𝒰 := X.affineOpenCover
  have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := (@Etale : MorphismProperty Scheme.{u}))
    (𝒰.openCover.pullback₁ ι)).mpr
  intro i
  let A := 𝒰.X i
  let j : Spec A ⟶ X := 𝒰.f i
  let : (Spec A).Over (Spec (.of k)) := ⟨j ≫ f⟩
  have : IsOpenImmersion j := 𝒰.map_prop i
  have : LocallyOfFiniteType (Spec A ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ f))
  let vU := ((End.of ((Spec A).finiteFieldFrobenius k)) ^ m).asHom
  obtain ⟨e, he⟩ := exists_fixedEqualizerPullbackIso j vU v
    (finiteFieldFrobenius_pow_naturality k j m)
  change Etale (pullback.fst ι j ≫ ι ≫ f)
  have hcomp : e.hom ≫ (pullback.fst ι j ≫ ι ≫ f) =
      equalizer.ι vU (𝟙 (Spec A)) ≫ j ≫ f := by
    calc
      _ = e.hom ≫ (pullback.snd ι j ≫ j) ≫ f := by
        rw [← Category.assoc (pullback.fst ι j), pullback.condition]
      _ = (e.hom ≫ pullback.snd ι j) ≫ j ≫ f := by
        simp only [Category.assoc]
      _ = _ := by rw [he]
  have : Etale (equalizer.ι vU (𝟙 (Spec A)) ≫ j ≫ f) :=
    affine_finiteFieldFrobenius_fixedScheme_etale k A m hm
  have hq : pullback.fst ι j ≫ ι ≫ f =
      e.inv ≫ (equalizer.ι vU (𝟙 (Spec A)) ≫ j ≫ f) := by
    rw [← hcomp, e.inv_hom_id_assoc]
  rw [hq]
  infer_instance

/-- For a quasi-compact separated scheme locally of finite type over a finite
field, the actual fixed scheme of every positive Frobenius power is finite
étale. In particular this applies to every proper scheme over that field. -/
theorem finiteFieldFrobenius_globalFixedScheme_finite_etale
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (m : ℕ) (hm : 0 < m) :
    IsFinite (equalizer.ι (((End.of (X.finiteFieldFrobenius k)) ^ m).asHom) (𝟙 X) ≫
      (X ↘ Spec (.of k))) ∧
      Etale (equalizer.ι (((End.of (X.finiteFieldFrobenius k)) ^ m).asHom) (𝟙 X) ≫
        (X ↘ Spec (.of k))) := by
  have : X.IsSeparated := ⟨by
    rw [← terminal.comp_from (X ↘ Spec (.of k))]
    infer_instance⟩
  have : Etale (equalizer.ι (((End.of (X.finiteFieldFrobenius k)) ^ m).asHom) (𝟙 X) ≫
      (X ↘ Spec (.of k))) :=
    finiteFieldFrobenius_fixedScheme_etale k X m hm
  exact ⟨SchemeTheory.EtaleNeighborhoods.FiniteEtale.isFinite_of_etale _, inferInstance⟩

/-- The actual equalizer on the geometric constant extension is finite étale,
obtained by base-changing the fixed scheme over the original finite field. -/
theorem constantBaseChangeFrobenius_globalFixedScheme_finite_etale
    (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (m : ℕ) (hm : 0 < m) :
    let Y := pullback (X ↘ Spec (.of k)) (Spec.algebraMap k Ω)
    let G := constantBaseChangeFrobenius k Ω X
    let g := pullback.snd (X ↘ Spec (.of k)) (Spec.algebraMap k Ω)
    IsFinite (equalizer.ι (((End.of G) ^ m).asHom) (𝟙 Y) ≫ g) ∧
      Etale (equalizer.ι (((End.of G) ^ m).asHom) (𝟙 Y) ≫ g) := by
  intro Y G g
  obtain ⟨hfinite, hetale⟩ := finiteFieldFrobenius_globalFixedScheme_finite_etale k X m hm
  exact constantBaseChangeFrobenius_fixedScheme_finite_etale k Ω X m hfinite hetale

end Scheme

end AlgebraicGeometry
