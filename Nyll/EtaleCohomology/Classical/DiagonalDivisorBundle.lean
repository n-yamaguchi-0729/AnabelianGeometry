/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Picard.AbelJacobi.AbelJacobiFamily
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModule
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealMulModuleIsoTensor
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierInvertibility
public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.PointKernelPullback
public import Nyll.EtaleCohomology.Classical.DiagonalPointSectionIdeals
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.SchemeTheory.Divisors.CartierProducts
public import Nyll.SchemeTheory.Divisors.FlatPullback
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The actual divisor bundle of the normalized diagonal

The two original projection pullbacks of the point ideal are effective
Cartier ideals by actual flatness. Their product is the effective edge
divisor. The original diagonal bundle tensored with that product ideal
is the existing Abel–Jacobi family with its second point ideal factor.
The comparison uses the actual constant-graph kernel equality.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

namespace EtaleCohomology

section Divisors

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
  [SmoothOfRelativeDimension 1 f] (p : S ⟶ X) (hp : p ≫ f = 𝟙 S)

/-- The original point ideal pulled back under the first projection,
with its Cartier property supplied by actual flatness. -/
def productPointFstEffectiveCartierDivisor : Scheme.EffectiveCartierDivisor (pullback f f) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  exact ⟨p.ker.comap (pullback.fst f f),
    (sectionEffectiveCartierDivisor f p hp).2.comap_of_flat (pullback.fst f f)⟩

/-- The same original point ideal pulled back under the second
projection of the actual scheme product. -/
def productPointSndEffectiveCartierDivisor : Scheme.EffectiveCartierDivisor (pullback f f) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  exact ⟨p.ker.comap (pullback.snd f f),
    (sectionEffectiveCartierDivisor f p hp).2.comap_of_flat (pullback.snd f f)⟩

/-- The two actual point pullbacks form the effective divisor whose
original cycle class is the sum of the two geometric edge classes. -/
def diagonalEdgeEffectiveCartierDivisor : Scheme.EffectiveCartierDivisor (pullback f f) :=
  ⟨(productPointFstEffectiveCartierDivisor f p hp).1 *
      (productPointSndEffectiveCartierDivisor f p hp).1,
    (productPointFstEffectiveCartierDivisor f p hp).2.mul
      (productPointSndEffectiveCartierDivisor f p hp).2⟩

/-- The original first point pullback has exactly the original
constant-graph ideal used by the Abel–Jacobi family. -/
theorem productPointFstEffectiveCartierDivisor_ideal :
    (productPointFstEffectiveCartierDivisor f p hp).1 =
      (graphOver f (f ≫ p) (by rw [Category.assoc, hp, Category.comp_id])).ker :=
  pointKernel_comap_fst f f p hp

end Divisors

/-- The signed divisor bundle of the actual normalized diagonal is
the original Abel–Jacobi family with the actual second point ideal.
No equality of cohomological comparison maps is an input. -/
theorem diagonalMiddleDivisorBundle_iso_ajFamily
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    Nonempty
      ((graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
          (diagonalEdgeEffectiveCartierDivisor f p hp).1.module ≅
        RelPicard.ajFamily (a := f) ⟨p, hp⟩ ⊗
          (productPointSndEffectiveCartierDivisor f p hp).1.module) := by
  let D := graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)
  let A := productPointFstEffectiveCartierDivisor f p hp
  let B := productPointSndEffectiveCartierDivisor f p hp
  have hA : A.1.IsInvertible := A.2.isInvertible
  have hB : B.1.IsInvertible := B.2.isInvertible
  obtain ⟨eAB⟩ := hA.nonempty_mul_module_iso_tensor hB
  let eA : A.1.module ≅ (RelPicard.constDiv (a := f) ⟨p, hp⟩).idealModule :=
    eqToIso (congrArg (fun I : (pullback f f).IdealSheafData => I.module)
      (pointKernel_comap_fst f f p hp))
  exact ⟨(Iso.refl D.1.invModule ⊗ᵢ eAB) ≪≫
    (α_ D.1.invModule A.1.module B.1.module).symm ≪≫
    ((Iso.refl D.1.invModule ⊗ᵢ eA) ⊗ᵢ Iso.refl B.1.module)⟩

end EtaleCohomology
