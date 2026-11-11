/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.FpqcIsomorphismDescent
public import Nyll.EtaleFundamentalGroups.GaloisCovers.SelfProduct
public import Nyll.SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Deck invariance supplies the actual Cech equality

The self-product of a Galois finite-etale cover is decomposed by its actual
deck graphs. Since the forgetful functor preserves these finite coproducts,
equality along the graphs determines scheme morphisms into any scheme.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u

/-- The categorical product of two finite-etale covers has the actual
scheme-theoretic fibre product as its underlying scheme. -/
theorem finiteEtale_product_isPullback {S : Scheme.{u}} (W V : FiniteEtale S) :
    IsPullback (prod.fst : W ⨯ V ⟶ W).left
      (prod.snd : W ⨯ V ⟶ V).left W.hom V.hom :=
  Over.isPullback_of_binaryFan_isLimit _
    (isLimitOfHasBinaryProductOfPreservesLimit (FiniteEtale.forget S) W V)

/-- Invariance under every actual deck transformation implies equality on
the two actual projections of the Cech relation, for an arbitrary target. -/
theorem cech_eq_of_deck_invariant
    {S Y : Scheme.{u}} [ConnectedSpace S]
    (W : FiniteEtale S) [IsGalois W] (a : W.left ⟶ Y)
    (ha : ∀ σ : Aut W, σ.asIso.hom.left ≫ a = a) :
    pullback.fst W.hom W.hom ≫ a = pullback.snd W.hom W.hom ≫ a := by
  let J := FiniteEtale.forget S ⋙ Over.forget S
  let E := galoisSelfProductIso W
  let P := (finiteEtale_product_isPullback W W).isoPullback
  apply (cancel_epi P.hom).1
  change P.hom ≫ pullback.fst W.hom W.hom ≫ a =
    P.hom ≫ pullback.snd W.hom W.hom ≫ a
  rw [← Category.assoc, IsPullback.isoPullback_hom_fst,
    ← Category.assoc, IsPullback.isoPullback_hom_snd]
  apply (cancel_epi (J.map E.hom)).1
  apply (isColimitOfHasCoproductOfPreservesColimit J (fun _ : Aut W => W)).hom_ext
  rintro ⟨σ⟩
  have hfst : J.map (Sigma.ι (fun _ : Aut W => W) σ) ≫
      J.map E.hom ≫ J.map (prod.fst : W ⨯ W ⟶ W) = 𝟙 W.left := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc,
      galoisSelfProductIso_ι, prod.lift_fst]
    exact J.map_id W
  have hsnd : J.map (Sigma.ι (fun _ : Aut W => W) σ) ≫
      J.map E.hom ≫ J.map (prod.snd : W ⨯ W ⟶ W) = σ.asIso.hom.left := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc,
      galoisSelfProductIso_ι, prod.lift_snd]
    rfl
  change J.map (Sigma.ι (fun _ : Aut W => W) σ) ≫
      J.map E.hom ≫ J.map (prod.fst : W ⨯ W ⟶ W) ≫ a =
    J.map (Sigma.ι (fun _ : Aut W => W) σ) ≫
      J.map E.hom ≫ J.map (prod.snd : W ⨯ W ⟶ W) ≫ a
  calc
    _ = a := by
      exact (congrArg (J.map (Sigma.ι (fun _ : Aut W => W) σ) ≫ ·)
        (Category.assoc (J.map E.hom) (J.map (prod.fst : W ⨯ W ⟶ W)) a).symm).trans
          ((Category.assoc _ _ a).symm.trans
            ((congrArg (fun b => b ≫ a) hfst).trans (Category.id_comp a)))
    _ = σ.asIso.hom.left ≫ a := (ha σ).symm
    _ = _ := by
      exact ((congrArg (J.map (Sigma.ι (fun _ : Aut W => W) σ) ≫ ·)
        (Category.assoc (J.map E.hom) (J.map (prod.snd : W ⨯ W ⟶ W)) a).symm).trans
          ((Category.assoc _ _ a).symm.trans
            (congrArg (fun b => b ≫ a) hsnd))).symm

/-- Deck invariance of a base-changed isomorphism supplies the Cech hypothesis
of actual fpqc descent. Invariance is required only after projection to the
target downstairs, so an equivariant isomorphism provides precisely this input. -/
theorem exists_schemeIso_of_fpqc_deck_invariant
    {S S' X Y : Scheme.{u}} [ConnectedSpace X]
    (s : S' ⟶ S) [IsFiniteEtale s] [Surjective s]
    (fX : X ⟶ S) (fY : Y ⟶ S)
    [IsGalois (FiniteEtale.mk (pullback.fst fX s))]
    (i : pullback fX s ≅ pullback fY s)
    (hi : i.hom ≫ pullback.snd fY s = pullback.snd fX s)
    (hdeck : ∀ σ : Aut (FiniteEtale.mk (pullback.fst fX s)),
      σ.asIso.hom.left ≫ i.hom ≫ pullback.fst fY s = i.hom ≫ pullback.fst fY s) :
    ∃ I : X ≅ Y, I.hom ≫ fY = fX ∧
      pullback.fst fX s ≫ I.hom = i.hom ≫ pullback.fst fY s := by
  apply exists_schemeIso_of_fpqc_cocycle s fX fY i hi
  exact cech_eq_of_deck_invariant (FiniteEtale.mk (pullback.fst fX s))
    (i.hom ≫ pullback.fst fY s) hdeck

/-- A deck-invariant morphism from a surjective Galois finite-etale cover
factors uniquely through its original base. The factorization is obtained
from the actual Cech relation of the cover. -/
theorem exists_unique_hom_of_galois_deck_invariant
    {X Y : Scheme.{u}} [ConnectedSpace X]
    (W : FiniteEtale X) [IsGalois W] [Surjective W.hom]
    (a : W.left ⟶ Y) (ha : ∀ σ : Aut W, σ.asIso.hom.left ≫ a = a) :
    ∃! f : X ⟶ Y, W.hom ≫ f = a := by
  have hc := cech_eq_of_deck_invariant W a ha
  have hw : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ W.left),
      g₁ ≫ W.hom = g₂ ≫ W.hom → g₁ ≫ a = g₂ ≫ a := by
    intro Z g₁ g₂ hg
    have h := congrArg (fun b => pullback.lift g₁ g₂ hg ≫ b) hc
    simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using h
  have : EffectiveEpi W.hom := inferInstance
  let f := EffectiveEpi.desc W.hom a hw
  have hf : W.hom ≫ f = a := EffectiveEpi.fac W.hom a hw
  exact ⟨f, hf, fun g hg => (cancel_epi W.hom).mp (hg.trans hf.symm)⟩

/-- An equivariant isomorphism of two actual Galois covers descends to a
unique isomorphism of their bases. The covers need not be constant covers
or be presented as pullbacks from a common coefficient extension. -/
theorem exists_unique_schemeIso_of_galois_cover_equivariant
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    (W : FiniteEtale X) (V : FiniteEtale Y)
    [IsGalois W] [IsGalois V] [Surjective W.hom] [Surjective V.hom]
    (i : W.left ≅ V.left) (θ : Aut W ≃* Aut V)
    (hequiv : ∀ σ : Aut W,
      σ.asIso.hom.left ≫ i.hom = i.hom ≫ (θ σ).asIso.hom.left) :
    ∃! I : X ≅ Y, W.hom ≫ I.hom = i.hom ≫ V.hom := by
  have hforward (σ : Aut W) :
      σ.asIso.hom.left ≫ (i.hom ≫ V.hom) = i.hom ≫ V.hom := by
    have hdeck : (θ σ).asIso.hom.left ≫ V.hom = V.hom :=
      MorphismProperty.Over.w (θ σ).asIso.hom
    calc
      _ = (σ.asIso.hom.left ≫ i.hom) ≫ V.hom := (Category.assoc _ _ _).symm
      _ = (i.hom ≫ (θ σ).asIso.hom.left) ≫ V.hom :=
        congrArg (fun b => b ≫ V.hom) (hequiv σ)
      _ = i.hom ≫ ((θ σ).asIso.hom.left ≫ V.hom) := Category.assoc _ _ _
      _ = _ := congrArg (fun b => i.hom ≫ b) hdeck
  obtain ⟨f, hf, huniq⟩ :=
    exists_unique_hom_of_galois_deck_invariant W (i.hom ≫ V.hom) hforward
  have hbackward (τ : Aut V) :
      τ.asIso.hom.left ≫ (i.inv ≫ W.hom) = i.inv ≫ W.hom := by
    have h := hequiv (θ.symm τ)
    rw [θ.apply_symm_apply] at h
    have hinv : τ.asIso.hom.left ≫ i.inv = i.inv ≫ (θ.symm τ).asIso.hom.left := by
      apply (cancel_epi i.hom).mp
      calc
        i.hom ≫ (τ.asIso.hom.left ≫ i.inv) =
            ((θ.symm τ).asIso.hom.left ≫ i.hom) ≫ i.inv := by
          rw [h, Category.assoc]
        _ = (θ.symm τ).asIso.hom.left := by
          rw [Category.assoc, i.hom_inv_id, Category.comp_id]
        _ = i.hom ≫ (i.inv ≫ (θ.symm τ).asIso.hom.left) := by
          rw [i.hom_inv_id_assoc]
    have hdeck : (θ.symm τ).asIso.hom.left ≫ W.hom = W.hom :=
      MorphismProperty.Over.w (θ.symm τ).asIso.hom
    calc
      _ = (τ.asIso.hom.left ≫ i.inv) ≫ W.hom := (Category.assoc _ _ _).symm
      _ = (i.inv ≫ (θ.symm τ).asIso.hom.left) ≫ W.hom :=
        congrArg (fun b => b ≫ W.hom) hinv
      _ = i.inv ≫ ((θ.symm τ).asIso.hom.left ≫ W.hom) := Category.assoc _ _ _
      _ = _ := congrArg (fun b => i.inv ≫ b) hdeck
  obtain ⟨g, hg, _⟩ :=
    exists_unique_hom_of_galois_deck_invariant V (i.inv ≫ W.hom) hbackward
  have hfg : f ≫ g = 𝟙 X := by
    apply (cancel_epi W.hom).mp
    calc
      W.hom ≫ (f ≫ g) = (W.hom ≫ f) ≫ g := (Category.assoc _ _ _).symm
      _ = i.hom ≫ (V.hom ≫ g) := by rw [hf, Category.assoc]
      _ = W.hom := by rw [hg, i.hom_inv_id_assoc]
      _ = W.hom ≫ 𝟙 X := (Category.comp_id _).symm
  have hgf : g ≫ f = 𝟙 Y := by
    apply (cancel_epi V.hom).mp
    calc
      V.hom ≫ (g ≫ f) = (V.hom ≫ g) ≫ f := (Category.assoc _ _ _).symm
      _ = i.inv ≫ (W.hom ≫ f) := by rw [hg, Category.assoc]
      _ = V.hom := by rw [hf, i.inv_hom_id_assoc]
      _ = V.hom ≫ 𝟙 Y := (Category.comp_id _).symm
  let I : X ≅ Y := ⟨f, g, hfg, hgf⟩
  exact ⟨I, hf, fun J hJ => Iso.ext (huniq J.hom hJ)⟩

end AnabelianGeometry.ArithmeticIsomorphisms
