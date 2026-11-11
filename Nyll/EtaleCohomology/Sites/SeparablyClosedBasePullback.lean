/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.ConnectedModuleConstants
public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Nyll.EtaleCohomology.Sites.PushforwardGlobalSections
public import Nyll.EtaleCohomology.Sites.SeparablyClosedFieldSheaves
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Pullback from a separably closed field to a connected scheme

The constant-module functor on the field spectrum is fully faithful and
essentially surjective. Its composition with actual inverse image is the
constant-module functor on the connected source, again fully faithful.
Thus actual inverse image is fully faithful, and its original unit gives
an isomorphism on global sections. No finite-type, finiteness or
constructibility hypothesis is needed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Actual inverse image from a separably closed field to any connected
scheme is fully faithful for arbitrary coefficient modules. -/
def etalePullbackFullyFaithful_of_isSepClosed_base
    (k : Type u) [Field k] [IsSepClosed k]
    {Y : Scheme.{u}} [ConnectedSpace Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) (Λ : Type u) [CommRing Λ] :
    (etalePullback p Λ).FullyFaithful := by
  let S : Scheme.{u} := Spec (CommRingCat.of k)
  let C₀ := constantSheaf S.smallEtaleTopology (ModuleCat.{u} Λ)
  let P := etalePullback p Λ
  let h₀ := etaleConstantModuleSheafFullyFaithful S Λ
  let h₁ := etaleConstantModuleSheafFullyFaithful Y Λ
  let hcomp : (C₀ ⋙ P).FullyFaithful := h₁.ofIso (etalePullbackConstantIso p Λ).symm
  have : C₀.EssSurj := ⟨fun G =>
    ⟨G.obj.obj (op (etaleBaseObject S)),
      ⟨etaleModuleSheafConstantIso_of_isSepClosed k Λ G⟩⟩⟩
  have : P.Full := P.full_of_comp_essSurj C₀ (by
    intro M N φ
    exact ⟨C₀.map (hcomp.preimage φ), hcomp.map_preimage φ⟩)
  have : P.Faithful := P.faithful_of_comp_essSurj C₀ (by
    intro M N f g hfg
    obtain ⟨f₀, rfl⟩ := h₀.map_surjective f
    obtain ⟨g₀, rfl⟩ := h₀.map_surjective g
    exact congrArg C₀.map (hcomp.map_injective hfg))
  exact Functor.FullyFaithful.ofFullyFaithful P

/-- Pullback along the structure morphism of a connected scheme over a
separably closed field preserves the actual module of global sections. -/
theorem etalePullbackGlobalSectionsMap_isIso_of_isSepClosed_base
    (k : Type u) [Field k] [IsSepClosed k]
    {Y : Scheme.{u}} [ConnectedSpace Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso (etalePullbackGlobalSectionsMap p Λ F) := by
  let h := etalePullbackFullyFaithful_of_isSepClosed_base k p Λ
  have : (etalePullback p Λ).Full := h.full
  have : (etalePullback p Λ).Faithful := h.faithful
  let η : F ⟶ (etalePushforward p Λ).obj ((etalePullback p Λ).obj F) :=
    (etalePullbackPushforwardAdjunction p Λ).unit.app F
  have : IsIso η := inferInstanceAs
    (IsIso ((etalePullbackPushforwardAdjunction p Λ).unit.app F))
  have : IsIso (η.hom.app (op (Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of k)))))) :=
    inferInstanceAs (IsIso (((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
      (ModuleCat.{u} Λ)).obj (op (Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of k)))))).map η))
  rw [← etalePullbackGlobalSectionsMap_eq_unit]
  change IsIso (η.hom.app _ ≫ (etalePushforwardGlobalSectionsIso p Λ
    ((etalePullback p Λ).obj F)).hom)
  infer_instance

end EtaleCohomology
