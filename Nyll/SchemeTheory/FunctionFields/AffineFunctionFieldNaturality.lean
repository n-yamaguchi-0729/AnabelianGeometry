/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.Functoriality

/-!
# Function-field naturality on affine schemes

Injective maps of commutative rings induce dense maps of spectra. For domains,
the resulting function-field map agrees with the original map on coefficients.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {A B : Type u} [CommRing A] [CommRing B]

/-- An injective ring homomorphism induces a dense map of affine schemes. -/
theorem affineSpecMap_denseRange_of_injective
    (f : A →+* B) (hf : Function.Injective f) :
    DenseRange (Spec.map (CommRingCat.ofHom f)) := by
  change DenseRange (PrimeSpectrum.comap f)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2
  exact le_trans
    (le_of_eq ((RingHom.injective_iff_ker_eq_bot f).mp hf)) bot_le

/-- The canonical affine algebra from the explicitly typed stalk map. -/
local instance affineFunctionFieldAlgebra
    (R : Type u) [CommRing R] [IsDomain R] :
    Algebra R (Spec (CommRingCat.of R)).functionField := by
  let ρ : R →+* (Spec (CommRingCat.of R)).functionField :=
    (StructureSheaf.toStalk R
      (show PrimeSpectrum.Top R from genericPoint (Spec (CommRingCat.of R)))).hom
  exact ρ.toAlgebra

/-- On coefficients, the function-field map of a dense affine morphism is
the ring homomorphism that defines that morphism. -/
theorem affineSpecMap_functionFieldMap_algebraMap
    [IsDomain A] [IsDomain B]
    (f : A →+* B) (hf : DenseRange (Spec.map (CommRingCat.ofHom f))) (a : A) :
    functionFieldMap (Spec.map (CommRingCat.ofHom f)) hf
        (algebraMap A (Spec (CommRingCat.of A)).functionField a) =
      algebraMap B (Spec (CommRingCat.of B)).functionField (f a) := by
  let : Nonempty (⊤ : (Spec (CommRingCat.of A)).Opens) :=
    ⟨⟨genericPoint (Spec (CommRingCat.of A)), trivial⟩⟩
  let : Nonempty (⊤ : (Spec (CommRingCat.of B)).Opens) :=
    ⟨⟨genericPoint (Spec (CommRingCat.of B)), trivial⟩⟩
  have hnat := functionFieldMap_comp_germToFunctionField_top
    (Spec.map (CommRingCat.ofHom f)) hf
  have hglobal :
      (Spec.map (CommRingCat.ofHom f)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv (f a) := by
    exact (congrArg
      (fun φ : CommRingCat.of A ⟶ Γ(Spec (CommRingCat.of B), ⊤) => φ a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm
  calc
    _ = (Spec (CommRingCat.of B)).germToFunctionField ⊤
        ((Spec.map (CommRingCat.ofHom f)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) := by
      exact DFunLike.congr_fun hnat ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)
    _ = (Spec (CommRingCat.of B)).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (f a)) := by rw [hglobal]
    _ = _ := rfl

end AlgebraicGeometry.Scheme.Hom
