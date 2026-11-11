/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Nyll.SchemeTheory.RingTheory.Henselian.FiniteFlatPointReduction
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# The coordinate algebra of an actual finite scheme

The relative Gamma functor supplies the coefficient algebra structure.
Finiteness follows from the actual finite structure morphism. Over a field,
the scheme-theoretic finite flat rank is its vector-space dimension.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace SchemeTheory.Affine.FiniteScheme

variable {R : Type u} [CommRing R] {Z : Scheme.{u}}

/-- The actual global sections, with their relative Gamma algebra structure. -/
abbrev coordinateAlgebra (q : Z ⟶ Spec (CommRingCat.of R)) : CommAlgCat.{u} R :=
  ((algΓ (CommRingCat.of R)).obj (Over.mk q)).unop

theorem coordinateAlgebra_algebraMap (q : Z ⟶ Spec (CommRingCat.of R)) :
    algebraMap R (coordinateAlgebra q) =
      q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := rfl

/-- The coordinate algebra is finite over the original coefficient ring. -/
instance coordinateAlgebra_finite (q : Z ⟶ Spec (CommRingCat.of R)) [IsFinite q] :
    Module.Finite R (coordinateAlgebra q) := by
  apply RingHom.finite_algebraMap.mp
  rw [coordinateAlgebra_algebraMap]
  exact RingHom.Finite.comp q.finite_appTop
    (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)

/-- The affine presentation is the actual global-sections isomorphism. -/
def coordinateIso (q : Z ⟶ Spec (CommRingCat.of R)) [IsFinite q] :
    Z ≅ Spec (CommRingCat.of (coordinateAlgebra q)) := by
  let : IsAffine Z := isAffine_of_isAffineHom q
  exact Z.isoSpec

/-- The global-sections presentation preserves the given structure map. -/
@[reassoc] theorem coordinateIso_toBase
    (q : Z ⟶ Spec (CommRingCat.of R)) [IsFinite q] :
    (coordinateIso q).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (coordinateAlgebra q))) = q := by
  let : IsAffine Z := isAffine_of_isAffineHom q
  have hn := Scheme.isoSpec_hom_naturality q
  rw [Scheme.isoSpec_Spec_hom] at hn
  change Z.isoSpec.hom ≫ Spec.map
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appTop) = q
  rw [Spec.map_comp, ← Category.assoc, hn, Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- A residue point of an actual finite flat scheme lifts through a valuation
ring in an algebraically closed field, with the original coefficient map. -/
theorem exists_valuationPointLift
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (V : ValuationSubring Ω)
    [Algebra R V] [Algebra R (IsLocalRing.ResidueField V)]
    [IsScalarTower R V (IsLocalRing.ResidueField V)]
    (q : Z ⟶ Spec (CommRingCat.of R)) [IsFinite q] [Flat q]
    (y : NeronModelInfra.SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField V)))) q) :
    ∃ z : NeronModelInfra.SchemeHomOver
        (Spec.map (CommRingCat.ofHom (algebraMap R V))) q,
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫ z.1 = y.1 := by
  let B := coordinateAlgebra q
  let e := coordinateIso q
  let a := CommRingCat.ofHom (algebraMap R B)
  have he : Spec.map a = e.inv ≫ q :=
    e.eq_inv_comp.mpr (coordinateIso_toBase q)
  have : Flat (Spec.map a) := by rw [he]; infer_instance
  have hflat : a.hom.Flat :=
    (Flat.SpecMap_iff (f := a)).mp (inferInstance : Flat (Spec.map a))
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.mp hflat
  let ψ₀ := Spec.preimage (y.1 ≫ e.hom)
  have hψ₀ : a ≫ ψ₀ = CommRingCat.ofHom
      (algebraMap R (IsLocalRing.ResidueField V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Category.assoc, coordinateIso_toBase q, y.2]
  let ψ : B →ₐ[R] IsLocalRing.ResidueField V :=
    { toRingHom := ψ₀.hom
      commutes' r := congrArg (fun f : CommRingCat.of R ⟶
        CommRingCat.of (IsLocalRing.ResidueField V) => f r) hψ₀ }
  obtain ⟨φ, hφ⟩ := surjective_finiteFlat_valuationPointReduction_of_algebra R V B ψ
  have hφbase : a ≫ CommRingCat.ofHom φ.toRingHom =
      CommRingCat.ofHom (algebraMap R V) := by
    apply CommRingCat.hom_ext
    change φ.toRingHom.comp (algebraMap R B) = algebraMap R V
    exact φ.comp_algebraMap
  let z : NeronModelInfra.SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R V))) q :=
    ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ e.inv, by
      rw [Category.assoc, ← he, ← Spec.map_comp, hφbase]⟩
  have hreduce : CommRingCat.ofHom φ.toRingHom ≫
      CommRingCat.ofHom (IsLocalRing.residue V) = ψ₀ := by
    ext b
    exact AlgHom.congr_fun hφ b
  refine ⟨z, ?_⟩
  change Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ e.inv) = y.1
  rw [← Category.assoc, ← Spec.map_comp, hreduce, Spec.map_preimage,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A finite scheme has finitely many points over any field extension of its
coefficient ring, including when the finite scheme is nonreduced. -/
theorem finite_fieldPoints (Ω : Type u) [Field Ω] [Algebra R Ω]
    (q : Z ⟶ Spec (CommRingCat.of R)) [IsFinite q] :
    Finite (NeronModelInfra.SchemeHomOver (Spec.algebraMap R Ω) q) := by
  let B := coordinateAlgebra q
  let e := coordinateIso q
  let toAffine : NeronModelInfra.SchemeHomOver (Spec.algebraMap R Ω) q →
      NeronModelInfra.SchemeHomOver (Spec.algebraMap R Ω) (Spec.algebraMap R B) :=
    fun x => ⟨x.1 ≫ e.hom, by
      rw [Category.assoc, coordinateIso_toBase q, x.2]⟩
  let eqv := Spec.homEquivAlgHom (R := R) (A := B) (B := Ω)
  have : Finite (B →ₐ[R] Ω) := inferInstance
  apply Finite.of_injective (fun x => eqv (toAffine x))
  intro x y h
  apply Subtype.ext
  exact (cancel_mono e.hom).mp (congrArg Subtype.val (eqv.injective h))

variable {K : Type u} [Field K]

/-- Over a field, finite flat rank equals the dimension of the actual
coordinate algebra, including for nonreduced finite schemes. -/
theorem finrank_coordinateAlgebra (q : Z ⟶ Spec (CommRingCat.of K))
    [IsFinite q] [Flat q] :
    Module.finrank K (coordinateAlgebra q) = q.finrank (IsLocalRing.closedPoint K) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (coordinateAlgebra q)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap K (coordinateAlgebra q)))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  conv_rhs => rw [← coordinateIso_toBase q]
  rw [Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

end SchemeTheory.Affine.FiniteScheme
