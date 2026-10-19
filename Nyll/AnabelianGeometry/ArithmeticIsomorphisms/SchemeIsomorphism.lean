/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.GeometricBasePoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticNaturality
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.SchemeTheory.Pi1.Affine.Over

/-! # Scheme isomorphisms with arbitrary arithmetic base points

Pullback along the given scheme isomorphism induces the group isomorphism.
The target fibre comparison is constructed and corrected arithmetically;
no identification of independently chosen geometric points is assumed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.ArithmeticIsomorphisms

/-- A scheme isomorphism over k induces an arithmetic-preserving topological
group isomorphism at any two geometric base points. The output retains a
fibre comparison which realizes the group map by the original pullback. -/
theorem exists_arithmetic_groupEquiv_of_schemeIso
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [GeometricallyConnected g]
    (I : X ≅ Y) (hI : I.hom ≫ g = f)
    {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ Y) :
    ∃ α : π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(y),
      (∃ t : fiber (x ≫ I.hom) ≅ fiber y,
        ∀ a : π₁ᵉᵗ(x), α a = continuousConjAut t (fundamentalGroupHom I.hom x a)) ∧
      ∀ a : π₁ᵉᵗ(x),
        arithmeticFundamentalGroupHom k K g y (α a) =
          arithmeticFundamentalGroupHom k K f x a := by
  let : ConnectedSpace Y := GeometricallyConnected.connectedSpace_of_subsingleton g
  let : ConnectedSpace X := I.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  let E : FiniteEtale Y ≌ FiniteEtale X :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ I.symm
  have : (pullback I.hom).IsEquivalence := E.isEquivalence_functor
  let e : π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(x ≫ I.hom) :=
    fundamentalGroupEquivOfPullbackEquivalence I.hom x
  obtain ⟨t, ht⟩ := exists_arithmetic_preserving_fiberIso k K g (x ≫ I.hom) y
  refine ⟨e.trans (continuousConjAut t), ⟨t, fun _ => rfl⟩, fun a => ?_⟩
  calc
    arithmeticFundamentalGroupHom k K g y
        ((e.trans (continuousConjAut t)) a) =
      arithmeticFundamentalGroupHom k K g (x ≫ I.hom)
        (fundamentalGroupHom I.hom x a) := ht (e a)
    _ = arithmeticFundamentalGroupHom k K (I.hom ≫ g) x a :=
      arithmeticFundamentalGroupHom_comp k K I.hom g x a
    _ = arithmeticFundamentalGroupHom k K f x a := by rw [hI]

end AnabelianGeometry.ArithmeticIsomorphisms
