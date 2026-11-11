/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianPushforwardComposition
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.UnitDirectImageSquares
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Rational unit sections through an arbitrary commuting square

The actual unit direct-image square carries a source-field unit to its
image under the specified field map. The square need not be cartesian:
its actual second projections and the original Γ–Spec naturality suffice.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Original rational unit sections pull back through the original
direct-image square by the specified homomorphism of their source rings. -/
theorem rationalUnitDirectImageSection_square
    {R S : Type u} [CommRing R] [CommRing S]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (i : Spec (.of R) ⟶ X) (j : Spec (.of S) ⟶ Y) (φ : R →+* S)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ i = j ≫ f)
    {V : X.Etale} {W : Y.Etale} (l : W.left ⟶ V.left)
    (hl : l ≫ V.hom = W.hom ≫ f) (a : Additive Rˣ) :
    ((etaleAbelianPushforward j).obj (etaleMultiplicativeGroupSheaf (Spec (.of S)))).obj.map
        (etaleBaseChangeLift f l hl).op
          ((etaleUnitDirectImageSquareMap i f j
            (Spec.map (CommRingCat.ofHom φ)) h).hom.app (op V)
              (rationalUnitDirectImageSection i V a)) =
      rationalUnitDirectImageSection j W
        (Additive.ofMul (Units.map φ.toMonoidHom a.toMul)) := by
  let g : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom φ)
  let m : W ⟶ (etaleBaseChange f).obj V := etaleBaseChangeLift f l hl
  let k₀ : pullback V.hom (j ≫ f) ⟶ pullback V.hom i :=
    etaleUnitDirectImageOverSchemeMap i (j ≫ f) g h V
  let e := (MorphismProperty.Over.pullbackComp
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) j f).app V
  let e' : pullback V.hom (j ≫ f) ≅ pullback (pullback.snd V.hom f) j :=
    (Scheme.Etale.forget (Spec (CommRingCat.of S)) ⋙
      CategoryTheory.Over.forget (Spec (CommRingCat.of S))).mapIso e
  let k : pullback W.hom j ⟶ pullback (pullback.snd V.hom f) j :=
    ((etaleBaseChange j).map m).left
  let b : pullback W.hom j ⟶ pullback V.hom i := k ≫ e'.inv ≫ k₀
  have hk₀ : k₀ ≫ pullback.snd V.hom i = pullback.snd V.hom (j ≫ f) ≫ g :=
    pullback.lift_snd _ _ _
  have he : e'.inv ≫ pullback.snd V.hom (j ≫ f) =
      pullback.snd (pullback.snd V.hom f) j :=
    MorphismProperty.Over.w
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) e.inv
  have hk : k ≫ pullback.snd (pullback.snd V.hom f) j = pullback.snd W.hom j :=
    pullback.lift_snd _ _ _
  have hb : b ≫ pullback.snd V.hom i = pullback.snd W.hom j ≫ g := by
    change (k ≫ e'.inv ≫ k₀) ≫ pullback.snd V.hom i = _
    rw [Category.assoc, Category.assoc, hk₀, ← Category.assoc e'.inv,
      he, ← Category.assoc, hk]
  have hr : ((Scheme.ΓSpecIso (.of R)).inv ≫ (pullback.snd V.hom i).appTop) ≫
      b.appTop = CommRingCat.ofHom φ ≫
        ((Scheme.ΓSpecIso (.of S)).inv ≫ (pullback.snd W.hom j).appTop) := by
    calc
      _ = (Scheme.ΓSpecIso (.of R)).inv ≫
          (b ≫ pullback.snd V.hom i).appTop :=
        Category.assoc (Scheme.ΓSpecIso (.of R)).inv (pullback.snd V.hom i).appTop b.appTop
      _ = (Scheme.ΓSpecIso (.of R)).inv ≫
          (pullback.snd W.hom j ≫ g).appTop :=
        congrArg (fun t : pullback W.hom j ⟶ Spec (CommRingCat.of R) =>
          (Scheme.ΓSpecIso (.of R)).inv ≫ t.appTop) hb
      _ = ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop) ≫
          (pullback.snd W.hom j).appTop := by
            rw [Scheme.Hom.comp_appTop, Category.assoc]
      _ = _ := by
        rw [← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ), Category.assoc]
  change ((etaleAbelianPushforward j).obj (etaleMultiplicativeGroupSheaf (Spec (.of S)))).obj.map
    m.op (((etaleAbelianPushforwardCompIso j f).inv.app
      (etaleMultiplicativeGroupSheaf (Spec (.of S)))).hom.app (op V)
        ((etaleUnitDirectImageOverMap i (j ≫ f) g h).hom.app (op V)
          (rationalUnitDirectImageSection i V a))) = _
  rw [etaleAbelianPushforwardCompIso_inv_app]
  apply Additive.toMul.injective
  apply Units.ext
  exact ConcreteCategory.congr_hom hr a.toMul.val

end EtaleCohomology
