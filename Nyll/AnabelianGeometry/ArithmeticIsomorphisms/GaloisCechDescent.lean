/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.FpqcIsomorphismDescent
import Nyll.EtaleFundamentalGroups.GaloisCovers.SelfProduct
import Nyll.SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Deck invariance supplies the actual Cech equality

The self-product of a Galois finite-etale cover is decomposed by its actual
deck graphs. Since the forgetful functor preserves these finite coproducts,
equality along the graphs determines scheme morphisms into any scheme.
-/

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
    (ha : ∀ σ : Aut W, σ.hom.left ≫ a = a) :
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
      J.map E.hom ≫ J.map (prod.snd : W ⨯ W ⟶ W) = σ.hom.left := by
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
    _ = σ.hom.left ≫ a := (ha σ).symm
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
      σ.hom.left ≫ i.hom ≫ pullback.fst fY s = i.hom ≫ pullback.fst fY s) :
    ∃ I : X ≅ Y, I.hom ≫ fY = fX ∧
      pullback.fst fX s ≫ I.hom = i.hom ≫ pullback.fst fY s := by
  apply exists_schemeIso_of_fpqc_cocycle s fX fY i hi
  exact cech_eq_of_deck_invariant (FiniteEtale.mk (pullback.fst fX s))
    (i.hom ≫ pullback.fst fY s) hdeck

end AnabelianGeometry.ArithmeticIsomorphisms
