/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.KummerRootCover
public import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.RootScaling
public import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIso

/-!
# Native fibers of the original affine Kummer cover

The finite étale object is the spectrum of the original algebra
`R[T]/(T^n-a)`. Its native fiber is identified with the actual roots in the
given geometric-point field. The comparison retains both the original deck
scalings and precomposition by field automorphisms.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open EtaleCohomology JacobianVarieties.Kummer

namespace AnabelianGeometry.FiniteField.NativeKummer

private theorem preimage_comp_map_apply {S T U : CommRingCat.{u}}
    (f : Spec S ⟶ Spec T) (g : U ⟶ T) (r : U) :
    (Spec.preimage (f ≫ Spec.map g)).hom r = (Spec.preimage f).hom (g.hom r) := by
  rw [Spec.preimage_comp, Spec.preimage_map]
  rfl

private theorem preimage_map_comp_apply {S T U : CommRingCat.{u}}
    (f : T ⟶ S) (g : Spec T ⟶ Spec U) (r : U) :
    (Spec.preimage (Spec.map f ≫ g)).hom r = f.hom ((Spec.preimage g).hom r) := by
  rw [Spec.preimage_comp, Spec.preimage_map]
  rfl

variable {R : Type u} [CommRing R] (n : ℕ+) (a : Rˣ) (hn : IsUnit ((n : ℕ) : R))

/-- The original finite étale root cover, including reducible root algebras. -/
def cover : FiniteEtale (Spec (CommRingCat.of R)) := by
  have : IsFiniteEtale (Spec.algebraMap R (kummerRootAlgebra (n : ℕ) a)) :=
    kummerRootCover_isFiniteEtale (n : ℕ) a hn
  exact FiniteEtale.mk (Spec.algebraMap R (kummerRootAlgebra (n : ℕ) a))

/-- An actual root scaling gives an automorphism of the original finite étale object. -/
def deck (ζ : rootsOfUnity (n : ℕ) R) : Aut (cover n a hn) :=
  Aut.of <| MorphismProperty.Over.isoMk
    (Scheme.Spec.mapIso (kummerRootScaleEquiv (n : ℕ) (a : R) ζ).toRingEquiv.toCommRingCatIso.op)
    (by
      change Spec.map (CommRingCat.ofHom
          (kummerRootScale (n : ℕ) (a : R) ζ).toRingHom) ≫
        Spec.algebraMap R (kummerRootAlgebra (n : ℕ) a) =
          Spec.algebraMap R (kummerRootAlgebra (n : ℕ) a)
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      exact (kummerRootScale (n : ℕ) (a : R) ζ).comp_algebraMap)

variable (Ω : Type u) [Field Ω] [Algebra R Ω] [IsSepClosed Ω]

local notation "xi" => Spec.algebraMap R Ω
local notation "V" => cover n a hn
local notation "P" => ObjectProperty.FullSubcategory.obj
  (Functor.obj (FiniteEtale.fiber (Spec.algebraMap R Ω)) (cover n a hn) : FintypeCat)
local notation "B" => kummerRootAlgebra (n : ℕ) a

/-- Native fiber points are the algebra homomorphisms from the same root algebra. -/
def pointAlgEquiv : P ≃ (B →ₐ[R] Ω) :=
  (FiniteEtale.fiberObjEquivHom xi V).trans
    (({ toFun := fun w => ⟨w.left, Over.w w⟩
        invFun := fun w => Over.homMk w.val w.property
        left_inv := fun _ => Over.OverMorphism.ext rfl
        right_inv := fun _ => Subtype.ext rfl } :
      (Over.mk xi ⟶ (V).toComma) ≃
        {w : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of B) //
          w ≫ Spec.algebraMap R B = xi}).trans Spec.homEquivAlgHom)

/-- Evaluation at the actual adjoined root is a coordinate on the native fiber. -/
def coordinate (z : P) : Ω :=
  pointAlgEquiv n a hn Ω z (AdjoinRoot.root _)

/-- The native coordinate satisfies the original polynomial, with its original coefficient. -/
theorem coordinate_pow (z : P) :
    coordinate n a hn Ω z ^ (n : ℕ) = algebraMap R Ω (a : R) :=
  (map_pow (pointAlgEquiv n a hn Ω z) _ _).symm.trans
    ((congrArg (pointAlgEquiv n a hn Ω z) (kummerRootAlgebra_root_pow (n : ℕ) a)).trans
      ((pointAlgEquiv n a hn Ω z).commutes (a : R)))

/-- These coordinates identify the native fiber with all roots of the original polynomial. -/
def rootEquiv : P ≃ {r : Ω // r ^ (n : ℕ) = algebraMap R Ω (a : R)} where
  toFun z := ⟨coordinate n a hn Ω z, coordinate_pow n a hn Ω z⟩
  invFun r := (pointAlgEquiv n a hn Ω).symm
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId R Ω) r.val (by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      exact sub_eq_zero.mpr r.property))
  left_inv z := by
    apply (pointAlgEquiv n a hn Ω).injective
    rw [Equiv.apply_symm_apply]
    apply AdjoinRoot.algHom_ext
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  right_inv r := by
    apply Subtype.ext
    change (pointAlgEquiv n a hn Ω
      ((pointAlgEquiv n a hn Ω).symm _)) (AdjoinRoot.root _) = r.val
    rw [Equiv.apply_symm_apply]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Root coordinates distinguish the actual native fiber points. -/
theorem coordinate_injective : Function.Injective (coordinate n a hn Ω) := by
  intro x y h
  exact (rootEquiv n a hn Ω).injective (Subtype.ext h)

/-- The original unit ensures that every native coordinate is nonzero. -/
theorem coordinate_ne_zero (z : P) : coordinate n a hn Ω z ≠ 0 := by
  intro hz
  have hpow := coordinate_pow n a hn Ω z
  rw [hz, zero_pow n.ne_zero] at hpow
  exact (a.isUnit.map (algebraMap R Ω)).ne_zero hpow.symm

/-- Separability at the given invertible exponent supplies every native fiber. -/
theorem fiber_nonempty : Nonempty P := by
  have : NeZero ((n : ℕ) : Ω) := ⟨(by
    have h := hn.map (algebraMap R Ω)
    simpa only [map_natCast] using h.ne_zero)⟩
  obtain ⟨r, hr⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap R Ω (a : R)) (n : ℕ)
  exact ⟨(rootEquiv n a hn Ω).symm ⟨r, hr⟩⟩

/-- The actual covering automorphism scales the actual native root coordinate. -/
theorem coordinate_deck (ζ : rootsOfUnity (n : ℕ) R) (z : P) :
    coordinate n a hn Ω ((FiniteEtale.fiber xi).map (deck n a hn ζ).asIso.hom z) =
      algebraMap R Ω (ζ.val : R) * coordinate n a hn Ω z := by
  let w := FiniteEtale.fiberObjEquivHom xi V z
  have hw := congrArg (fun v : Over.mk xi ⟶ (V).toComma => v.left)
    (FiniteEtale.fiberObjEquivHom_naturality xi (deck n a hn ζ).asIso.hom z).symm
  have h := congrArg (fun s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of B) =>
    (Spec.preimage s).hom (AdjoinRoot.root _)) hw
  change coordinate n a hn Ω ((FiniteEtale.fiber xi).map (deck n a hn ζ).asIso.hom z) =
    (Spec.preimage (w.left ≫ (deck n a hn ζ).asIso.hom.left)).hom (AdjoinRoot.root _) at h
  have hs : (Spec.preimage (w.left ≫ (deck n a hn ζ).asIso.hom.left)).hom
      (AdjoinRoot.root _) =
      pointAlgEquiv n a hn Ω z (kummerRootScale (n : ℕ) (a : R) ζ (AdjoinRoot.root _)) := by
    exact preimage_comp_map_apply w.left
      (CommRingCat.ofHom (kummerRootScale (n : ℕ) (a : R) ζ).toRingHom)
      (AdjoinRoot.root _)
  exact h.trans (hs.trans (by
    rw [kummerRootScale_root, map_mul, AlgHom.commutes]
    rfl))

omit [IsSepClosed Ω] in
/-- The original arithmetic monodromy commutes with every actual deck scaling. -/
theorem monodromy_deck (γ : π₁ᵉᵗ(xi)) (ζ : rootsOfUnity (n : ℕ) R) (z : P) :
    γ • (FiniteEtale.fiber xi).map (deck n a hn ζ).asIso.hom z =
      (FiniteEtale.fiber xi).map (deck n a hn ζ).asIso.hom (γ • z) :=
  mulAction_naturality _ _ _ _

/-- The source-field operation acts on the same root coordinate by its given
field automorphism. The hypothesis only closes the actual source map at the base point. -/
theorem coordinate_sourceAut (σ : Ω ≃+* Ω)
    (hσ : (Scheme.Spec.mapIso σ.toCommRingCatIso.op).hom ≫ xi = xi) (z : P) :
    coordinate n a hn Ω
      ((FiniteEtale.fiberSourceIso xi (Scheme.Spec.mapIso σ.toCommRingCatIso.op) ≪≫
        eqToIso (congrArg FiniteEtale.fiber hσ)).hom.app V z) =
      σ (coordinate n a hn Ω z) := by
  have h := congrArg (fun s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of B) =>
    (Spec.preimage s).hom (AdjoinRoot.root _))
    (FiniteEtale.fiberSourceIso_aut_point xi
      (Scheme.Spec.mapIso σ.toCommRingCatIso.op) hσ V z)
  change coordinate n a hn Ω _ =
    (Spec.preimage (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      (FiniteEtale.fiberObjEquivHom xi V z).left)).hom (AdjoinRoot.root _) at h
  exact h.trans (preimage_map_comp_apply (CommRingCat.ofHom σ.toRingHom)
    (FiniteEtale.fiberObjEquivHom xi V z).left (AdjoinRoot.root _))

end AnabelianGeometry.FiniteField.NativeKummer
