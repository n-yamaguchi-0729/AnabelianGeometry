/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.ContinuousHomComparison

/-! # Natural isomorphisms of finite-cover functors and conjugation

A natural isomorphism between the functors induced by two continuous group
maps gives one conjugator for the entire group map. Conversely a conjugator
constructs a natural isomorphism on every finite continuous action.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u₁ u₂ v₁ v₂ w

variable {C : Type u₁} [Category.{u₂} C]
  {C' : Type v₁} [Category.{v₂} C']
  {F : C ⥤ FintypeCat.{w}} {F' : C' ⥤ FintypeCat.{w}}

/-- Transporting a comparison along an actual natural isomorphism of functors
preserves the resulting homomorphism of automorphism groups. -/
theorem autHomOfCompIso_transport
    (H J : C ⥤ C') (a : H ≅ J) (t : J ⋙ F' ≅ F) (g : Aut F') :
    autHomOfCompIso H (Functor.isoWhiskerRight a F' ≪≫ t) g =
      autHomOfCompIso J t g := by
  ext X x
  change (t.hom.app X)
      (F'.map (a.hom.app X)
        ((g.hom.app (H.obj X))
          (F'.map (a.inv.app X) ((t.inv.app X) x)))) =
    (t.hom.app X) ((g.hom.app (J.obj X)) ((t.inv.app X) x))
  have hcancel : F'.map (a.inv.app X) ≫ F'.map (a.hom.app X) =
      𝟙 (F'.obj (J.obj X)) := by
    rw [← F'.map_comp, a.inv_hom_id_app]
    exact F'.map_id _
  have hx := ConcreteCategory.congr_hom hcancel ((t.inv.app X) x)
  have hn := ConcreteCategory.congr_hom (g.hom.naturality (a.hom.app X))
    (F'.map (a.inv.app X) ((t.inv.app X) x))
  change (g.hom.app (J.obj X))
      (F'.map (a.hom.app X) (F'.map (a.inv.app X) ((t.inv.app X) x))) =
    F'.map (a.hom.app X)
      ((g.hom.app (H.obj X)) (F'.map (a.inv.app X) ((t.inv.app X) x))) at hn
  change F'.map (a.hom.app X) (F'.map (a.inv.app X) ((t.inv.app X) x)) =
    (t.inv.app X) x at hx
  rw [hx] at hn
  exact congrArg (fun y => (t.hom.app X) y) hn.symm

variable [GaloisCategory C] [GaloisCategory C'] [FiberFunctor F] [FiberFunctor F']

omit [GaloisCategory C] [FiberFunctor F] in
/-- A common conjugator constructs the natural isomorphism of induced cover functors. -/
def functorIsoOfConjugator
    (α β : Aut F' →ₜ* Aut F) (c : Aut F)
    (h : ∀ g : Aut F', β g = c * α g * c⁻¹) :
    functorOfContinuousHom F F' α ≅ functorOfContinuousHom F F' β := by
  let E : functorToContAction F ⋙ ContAction.res FintypeCat α ≅
      functorToContAction F ⋙ ContAction.res FintypeCat β :=
    NatIso.ofComponents
      (fun X => ObjectProperty.isoMk _
        (Action.mkIso (c.app X) (fun g => by
          apply ConcreteCategory.hom_ext
          intro x
          change (c.hom.app X) (((α g).hom.app X) x) =
            ((β g).hom.app X) ((c.hom.app X) x)
          change ((c * α g).hom.app X) x = ((β g * c).hom.app X) x
          rw [h g]
          simp only [mul_assoc, inv_mul_cancel, mul_one])))
      (fun {X Y} f => by
        ext : 2
        exact c.hom.naturality f)
  exact
    (Functor.associator (functorToContAction F) (ContAction.res FintypeCat α)
      (functorToContAction F').asEquivalence.inverse).symm ≪≫
      Functor.isoWhiskerRight E (functorToContAction F').asEquivalence.inverse ≪≫
      Functor.associator (functorToContAction F) (ContAction.res FintypeCat β)
        (functorToContAction F').asEquivalence.inverse

omit [GaloisCategory C] [FiberFunctor F] in
/-- Natural isomorphism of the induced finite-cover functors is equivalent to
conjugacy of the original continuous homomorphisms by one target element. -/
theorem nonempty_functorIso_iff_conjugate
    (α β : Aut F' →ₜ* Aut F) :
    Nonempty (functorOfContinuousHom F F' α ≅ functorOfContinuousHom F F' β) ↔
      ∃ c : Aut F, ∀ g : Aut F', β g = c * α g * c⁻¹ := by
  constructor
  · rintro ⟨a⟩
    let tα := comparisonIsoOfContinuousHom F F' α
    let tβ := comparisonIsoOfContinuousHom F F' β
    let t := Functor.isoWhiskerRight a F' ≪≫ tβ
    refine ⟨tα.symm ≪≫ t, ?_⟩
    intro g
    have ht : autHomOfCompIso (functorOfContinuousHom F F' α) t g = β g := by
      rw [autHomOfCompIso_transport]
      exact DFunLike.congr_fun (autHomOfCompIso_comparisonIsoOfContinuousHom F F' β) g
    have hc := autHomOfCompIso_eq_conj
      (functorOfContinuousHom F F' α) tα t g
    have hα : autHomOfCompIso (functorOfContinuousHom F F' α) tα g = α g :=
      DFunLike.congr_fun (autHomOfCompIso_comparisonIsoOfContinuousHom F F' α) g
    rw [hα] at hc
    exact ht.symm.trans hc
  · rintro ⟨c, hc⟩
    exact ⟨functorIsoOfConjugator α β c hc⟩

end AnabelianGeometry.ArithmeticIsomorphisms
