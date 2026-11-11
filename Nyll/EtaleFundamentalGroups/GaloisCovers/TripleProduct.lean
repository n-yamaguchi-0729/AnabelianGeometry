/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.SelfProduct

/-!
# Actual deck graphs in the triple product

Pairs of successive deck transformations decompose the triple product of
a Galois object. This gives the actual geometric test family for the
degree-one Cech cocycle identity.
-/

@[expose] public section

noncomputable section
universe u v w
open CategoryTheory Limits

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]

/-- The graph of two successive actual deck transformations. -/
def galoisTripleGraph (X : C) (σ τ : Aut X) : X ⟶ X ⨯ (X ⨯ X) :=
  prod.lift (𝟙 X) (prod.lift σ.asIso.hom (σ.asIso.hom ≫ τ.asIso.hom))

/-- The coproduct of the actual successive deck graphs. -/
def galoisTripleProductMap (X : C) [IsGalois X] :
    (∐ fun _ : Aut X × Aut X => X) ⟶ X ⨯ (X ⨯ X) :=
  Sigma.desc fun p => galoisTripleGraph X p.1 p.2

/-- The triple deck-graph map is an isomorphism, proved on the actual
fiber functor using the simply transitive deck action. -/
theorem galoisTripleProductMap_isIso
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (X : C) [IsGalois X] : IsIso (galoisTripleProductMap X) := by
  let T : C ⥤ Type w := F ⋙ FintypeCat.incl
  have hrep : ∀ a : F.obj (∐ fun _ : Aut X × Aut X => X),
      ∃ (p : Aut X × Aut X) (x : F.obj X),
        F.map (Sigma.ι (fun _ : Aut X × Aut X => X) p) x = a := by
    intro a
    obtain ⟨p, x, hx⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfHasCoproductOfPreservesColimit T (fun _ : Aut X × Aut X => X)) a
    exact ⟨p.as, x, hx⟩
  let a (p : Aut X × Aut X) (x : F.obj X) :=
    F.map (galoisTripleProductMap X)
      (F.map (Sigma.ι (fun _ : Aut X × Aut X => X) p) x)
  have h₀ (p : Aut X × Aut X) (x : F.obj X) :
      F.map prod.fst (a p x) = x := by
    simp only [a, galoisTripleProductMap, galoisTripleGraph,
      ← FintypeCat.comp_apply, ← Functor.map_comp,
      Sigma.ι_comp_desc, prod.lift_fst, Functor.map_id, FintypeCat.id_apply]
  have h₁ (p : Aut X × Aut X) (x : F.obj X) :
      F.map (prod.snd ≫ prod.fst) (a p x) = F.map p.1.asIso.hom x := by
    simp only [a, galoisTripleProductMap, galoisTripleGraph,
      ← FintypeCat.comp_apply, ← Functor.map_comp,
      Sigma.ι_comp_desc, ← Category.assoc, prod.lift_snd, prod.lift_fst]
  have h₂ (p : Aut X × Aut X) (x : F.obj X) :
      F.map (prod.snd ≫ prod.snd) (a p x) =
        F.map p.2.asIso.hom (F.map p.1.asIso.hom x) := by
    simp only [a, galoisTripleProductMap, galoisTripleGraph,
      ← FintypeCat.comp_apply, ← Functor.map_comp,
      Sigma.ι_comp_desc, ← Category.assoc, prod.lift_snd]
  have hext {b c : F.obj (X ⨯ (X ⨯ X))}
      (h₀ : F.map prod.fst b = F.map prod.fst c)
      (h₁ : F.map (prod.snd ≫ prod.fst) b = F.map (prod.snd ≫ prod.fst) c)
      (h₂ : F.map (prod.snd ≫ prod.snd) b = F.map (prod.snd ≫ prod.snd) c) :
      b = c := by
    apply Concrete.isLimit_ext (pair X (X ⨯ X) ⋙ F)
      (isLimitOfPreserves F (limit.isLimit (pair X (X ⨯ X))))
    rintro ⟨j⟩
    cases j with
    | left => exact h₀
    | right =>
      apply Concrete.isLimit_ext (pair X X ⋙ F)
        (isLimitOfPreserves F (limit.isLimit (pair X X)))
      rintro ⟨k⟩
      cases k with
      | left =>
        change F.map prod.fst (F.map prod.snd b) = F.map prod.fst (F.map prod.snd c)
        simpa only [Functor.map_comp, FintypeCat.comp_apply] using h₁
      | right =>
        change F.map prod.snd (F.map prod.snd b) = F.map prod.snd (F.map prod.snd c)
        simpa only [Functor.map_comp, FintypeCat.comp_apply] using h₂
  have hbij : Function.Bijective (F.map (galoisTripleProductMap X)) := by
    constructor
    · intro b c h
      obtain ⟨p, x, rfl⟩ := hrep b
      obtain ⟨q, y, rfl⟩ := hrep c
      change a p x = a q y at h
      have hxy : x = y := by
        have h' : F.map prod.fst (a p x) = F.map prod.fst (a q y) :=
          congrArg (F.map prod.fst) h
        rw [h₀, h₀] at h'
        exact h'
      subst y
      have hpq₁ : p.1 = q.1 := by
        apply evaluation_aut_injective_of_isConnected F X x
        have h' : F.map (prod.snd ≫ prod.fst) (a p x) =
            F.map (prod.snd ≫ prod.fst) (a q x) :=
          congrArg (F.map (prod.snd ≫ prod.fst)) h
        rw [h₁, h₁] at h'
        exact h'
      have hpq₂ : p.2 = q.2 := by
        apply evaluation_aut_injective_of_isConnected F X (F.map p.1.asIso.hom x)
        have h' : F.map (prod.snd ≫ prod.snd) (a p x) =
            F.map (prod.snd ≫ prod.snd) (a q x) :=
          congrArg (F.map (prod.snd ≫ prod.snd)) h
        rw [h₂, h₂, ← hpq₁] at h'
        exact h'
      have hpq : p = q := Prod.ext hpq₁ hpq₂
      subst q
      rfl
    · intro z
      let x := F.map (prod.fst : X ⨯ (X ⨯ X) ⟶ X) z
      let y := F.map (prod.snd ≫ prod.fst : X ⨯ (X ⨯ X) ⟶ X) z
      let t := F.map (prod.snd ≫ prod.snd : X ⨯ (X ⨯ X) ⟶ X) z
      obtain ⟨σ, hσ⟩ := evaluation_aut_surjective_of_isGalois F X x y
      obtain ⟨τ, hτ⟩ := evaluation_aut_surjective_of_isGalois F X y t
      refine ⟨F.map (Sigma.ι (fun _ : Aut X × Aut X => X) (σ, τ)) x, ?_⟩
      apply hext
      · exact h₀ (σ, τ) x
      · exact (h₁ (σ, τ) x).trans hσ
      · exact (h₂ (σ, τ) x).trans ((congrArg (F.map τ.asIso.hom) hσ).trans hτ)
  have : IsIso (F.map (galoisTripleProductMap X)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact isIso_of_reflects_iso (galoisTripleProductMap X) F

/-- The canonical actual triple-product deck decomposition. -/
def galoisTripleProductIso (X : C) [IsGalois X] :
    (∐ fun _ : Aut X × Aut X => X) ≅ X ⨯ (X ⨯ X) := by
  have : IsIso (galoisTripleProductMap X) :=
    galoisTripleProductMap_isIso (CategoryTheory.GaloisCategory.getFiberFunctor C) X
  exact asIso (galoisTripleProductMap X)

/-- Each coproduct inclusion maps to its actual successive deck graph. -/
theorem galoisTripleProductIso_ι (X : C) [IsGalois X] (p : Aut X × Aut X) :
    Sigma.ι (fun _ : Aut X × Aut X => X) p ≫ (galoisTripleProductIso X).hom =
      galoisTripleGraph X p.1 p.2 :=
  Sigma.ι_comp_desc _ p

end CategoryTheory.PreGaloisCategory
