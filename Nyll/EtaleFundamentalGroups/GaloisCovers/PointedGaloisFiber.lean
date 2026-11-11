/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.IsSepClosed

/-!
# A rational point splits the actual fiber of a Galois cover

The native deck transformations act transitively on every geometric fiber.
If one lift of a rational base point is rational, its deck orbit supplies
rational lifts through every original point of that fiber.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Every original point above a separably closed geometric point is reached
by an actual lift of that geometric point. -/
theorem exists_geometricPoint_lift_through
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (Y : FiniteEtale X) (xi : Spec (.of Ω) ⟶ X)
    (y : Y.left) (hy : Y.hom y = xi (IsLocalRing.closedPoint Ω)) :
    ∃ q : Spec (.of Ω) ⟶ Y.left,
      q ≫ Y.hom = xi ∧ q (IsLocalRing.closedPoint Ω) = y := by
  obtain ⟨z, hzy, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := Y.hom) (g := xi) y (IsLocalRing.closedPoint Ω) hy
  have : IsFiniteEtale (𝟙 (Spec (.of Ω))) := .mk
  let T : FiniteEtale (Spec (.of Ω)) := FiniteEtale.mk (𝟙 (Spec (.of Ω)))
  let Z : FiniteEtale (Spec (.of Ω)) := (pullback xi).obj Y
  let t : T ⟶ Z := (forgetScheme Ω).preimage
    (FintypeCat.homMk fun _ => z)
  have ht : t.left (IsLocalRing.closedPoint Ω) = z := by
    have hm : (forgetScheme Ω).map t = FintypeCat.homMk (fun _ => z) :=
      Functor.map_preimage _ _
    exact congrArg (fun h : (forgetScheme Ω).obj T ⟶ (forgetScheme Ω).obj Z =>
      h (IsLocalRing.closedPoint Ω)) hm
  refine ⟨t.left ≫ Limits.pullback.fst Y.hom xi, ?_, ?_⟩
  · let r : Spec (.of Ω) ⟶ Limits.pullback Y.hom xi := t.left
    have hw : r ≫ Limits.pullback.snd Y.hom xi = 𝟙 _ := t.w
    have hsquare : Limits.pullback.fst Y.hom xi ≫ Y.hom =
        Limits.pullback.snd Y.hom xi ≫ xi := Limits.pullback.condition
    calc
      (r ≫ Limits.pullback.fst Y.hom xi) ≫ Y.hom =
          r ≫ (Limits.pullback.fst Y.hom xi ≫ Y.hom) := Category.assoc _ _ _
      _ = r ≫ (Limits.pullback.snd Y.hom xi ≫ xi) :=
        congrArg (fun f => r ≫ f) hsquare
      _ = (r ≫ Limits.pullback.snd Y.hom xi) ≫ xi := (Category.assoc _ _ _).symm
      _ = (𝟙 _) ≫ xi := congrArg (fun f => f ≫ xi) hw
      _ = xi := Category.id_comp xi
  · change Limits.pullback.fst Y.hom xi (t.left (IsLocalRing.closedPoint Ω)) = y
    exact (congrArg (Limits.pullback.fst Y.hom xi) ht).trans hzy

/-- One rational lift of a rational point of the base gives rational lifts
through every point of the original Galois fiber. -/
theorem exists_rationalPoint_lift_through_of_isGalois
    {k : Type u} [Field k] {X : Scheme.{u}} [ConnectedSpace X]
    (Y : FiniteEtale X) [IsGalois Y]
    (ε : Spec (.of k) ⟶ X) (s : Spec (.of k) ⟶ Y.left)
    (hs : s ≫ Y.hom = ε) (y : Y.left)
    (hy : Y.hom y = ε (IsLocalRing.closedPoint k)) :
    ∃ t : Spec (.of k) ⟶ Y.left,
      t ≫ Y.hom = ε ∧ t (IsLocalRing.closedPoint k) = y := by
  let Ω := SeparableClosure k
  let b : Spec (.of Ω) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let xi : Spec (.of Ω) ⟶ X := b ≫ ε
  have hb : b (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint k :=
    Subsingleton.elim _ _
  have hyxi : Y.hom y = xi (IsLocalRing.closedPoint Ω) := by
    change Y.hom y = ε (b (IsLocalRing.closedPoint Ω))
    rw [hb]
    exact hy
  obtain ⟨q, hq, hqy⟩ := exists_geometricPoint_lift_through Y xi y hyxi
  let p₀ : Over.mk xi ⟶ Y.toComma := Over.homMk (b ≫ s) (by
    exact (Category.assoc _ _ _).trans (congrArg (b ≫ ·) hs))
  let p₁ : Over.mk xi ⟶ Y.toComma := Over.homMk q hq
  let F := fiber xi
  let a₀ : F.obj Y := (fiberObjEquivHom xi Y).symm p₀
  let a₁ : F.obj Y := (fiberObjEquivHom xi Y).symm p₁
  obtain ⟨σ, hσ⟩ := (evaluationEquivOfIsGalois F Y a₀).surjective a₁
  have hσ' : F.map σ.asIso.hom a₀ = a₁ := by
    simpa only [evaluationEquivOfIsGalois_apply] using hσ
  have hpoint : p₀ ≫ σ.asIso.hom.hom = p₁ := by
    calc
      p₀ ≫ σ.asIso.hom.hom = (fiberObjEquivHom xi Y a₀) ≫ σ.asIso.hom.hom := by
        rw [Equiv.apply_symm_apply]
      _ = fiberObjEquivHom xi Y (F.map σ.asIso.hom a₀) :=
        fiberObjEquivHom_naturality xi σ.asIso.hom a₀
      _ = p₁ := by rw [hσ', Equiv.apply_symm_apply]
  have hleft : (b ≫ s) ≫ σ.asIso.hom.left = q :=
    congrArg (fun f : Over.mk xi ⟶ Y.toComma => f.left) hpoint
  refine ⟨s ≫ σ.asIso.hom.left, ?_, ?_⟩
  · have hw : σ.asIso.hom.left ≫ Y.hom = Y.hom := σ.asIso.hom.w
    exact (Category.assoc _ _ _).trans ((congrArg (s ≫ ·) hw).trans hs)
  · have hpointy := congrArg (fun f : Spec (.of Ω) ⟶ Y.left =>
      f (IsLocalRing.closedPoint Ω)) hleft
    change σ.asIso.hom.left (s (b (IsLocalRing.closedPoint Ω))) =
      q (IsLocalRing.closedPoint Ω) at hpointy
    rw [hb, hqy] at hpointy
    exact hpointy

end AlgebraicGeometry.FiniteEtale
