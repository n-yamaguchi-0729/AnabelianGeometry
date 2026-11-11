/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
public import Nyll.EtaleCohomology.Sites.PushforwardGlobalSections
public import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Injectivity of inverse image along an arbitrary surjection

Geometric points chosen on the source give a conservative family on the
target after composition with a surjective morphism. At each such point,
the actual inverse-image unit followed by its direct-image stalk component
is an isomorphism. Hence the unit is a monomorphism, and the actual map on
global sections is injective. No finiteness or flatness assumption is used.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- For every surjection of schemes, the actual inverse-image/direct-image
unit is a monomorphism for arbitrary coefficient modules. -/
theorem etaleSurjective_unit_mono
    {X Y : Scheme.{u}} (q : Y ⟶ X) [Surjective q]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Mono ((etalePullbackPushforwardAdjunction q Λ).unit.app F) := by
  let Ω : Y → Type u := fun y => AlgebraicClosure (Y.residueField y)
  let s : ∀ y : Y, Spec (CommRingCat.of (Ω y)) ⟶ Y := fun y =>
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (Ω y))) ≫
      Y.fromSpecResidueField y
  have hs (y : Y) : s y default = y := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply y _
  let t : ∀ y : Y, Spec (CommRingCat.of (Ω y)) ⟶ X := fun y => s y ≫ q
  have hcover : ⋃ y : Y, Set.range (t y) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, rfl⟩ := q.surjective x
    refine Set.mem_iUnion.mpr ⟨y, default, ?_⟩
    exact (Scheme.Hom.comp_apply (s y) q default).trans (congrArg q (hs y))
  have hpoints := Scheme.isConservative_pointSmallEtale t hcover
  apply ((hpoints.jointlyReflectMonomorphisms (ModuleCat.{u} Λ)).mono_iff _).mpr
  rintro ⟨_, ⟨y⟩⟩
  change Mono ((Scheme.pointSmallEtale (s y ≫ q)).sheafFiber.map
    ((etalePullbackPushforwardAdjunction q Λ).unit.app F))
  let a := (Scheme.pointSmallEtale (s y ≫ q)).sheafFiber.map
    ((etalePullbackPushforwardAdjunction q Λ).unit.app F)
  let b := etalePushforwardStalkComponent q (s y ≫ q) ⟨s y, rfl⟩
    ((etalePullback q Λ).obj F)
  have hab : IsIso (a ≫ b) := etalePullbackUnit_stalkComponent_isIso q (s y) Λ F
  apply (ModuleCat.mono_iff_injective a).mpr
  intro v w hvw
  apply (ModuleCat.mono_iff_injective (a ≫ b)).mp inferInstance
  exact congrArg b hvw

/-- Pullback on actual global sections is injective along every surjective
scheme morphism, for every étale module sheaf. -/
theorem etaleSurjective_globalSections_injective
    {X Y : Scheme.{u}} (q : Y ⟶ X) [Surjective q]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Function.Injective (etalePullbackGlobalSectionsMap q Λ F) := by
  let η : F ⟶ (etalePushforward q Λ).obj ((etalePullback q Λ).obj F) :=
    (etalePullbackPushforwardAdjunction q Λ).unit.app F
  have : Mono η := etaleSurjective_unit_mono q Λ F
  have : Mono η.hom := inferInstanceAs (Mono ((sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u} Λ)).map η))
  rw [← etalePullbackGlobalSectionsMap_eq_unit]
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

end EtaleCohomology
