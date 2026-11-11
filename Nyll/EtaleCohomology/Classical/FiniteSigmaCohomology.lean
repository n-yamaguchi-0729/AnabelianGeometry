/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Constructible.SigmaRepresenter
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Actual cohomology on finite disjoint unions

The original free abelian sheaf represented by a disjoint union is the
coproduct of the original component sheaves. Its universal property is
proved by the existing actual gluing of sections, with the original
component inclusions as its arrows. For a finite family this is a
biproduct, so native Ext gives the actual componentwise cohomology
comparison in every degree.

The comparison is the original cohomology presheaf restriction in each
coordinate and is natural in the coefficient sheaf. In particular it
retains the original finite coefficient reduction maps.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Etale)

/-- The actual morphism induced by gluing sections on the disjoint union. -/
def etaleSigmaFreeAbelianDesc
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : ∀ i, (freeAbelianSheafYoneda X.smallEtaleTopology).obj (U i) ⟶ F) :
    (freeAbelianSheafYoneda X.smallEtaleTopology).obj (etaleSigma U) ⟶ F :=
  (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology (etaleSigma U) F).symm
    (etaleSigmaSection U
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F)
      (fun i => freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology (U i) F (a i)))

/-- The glued morphism restricts to its prescribed component morphism. -/
theorem etaleSigmaFreeAbelianDesc_comp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : ∀ i, (freeAbelianSheafYoneda X.smallEtaleTopology).obj (U i) ⟶ F) (i : ι) :
    (freeAbelianSheafYoneda X.smallEtaleTopology).map (etaleSigmaInj U i) ≫
        etaleSigmaFreeAbelianDesc U F a = a i := by
  let G : Sheaf X.smallEtaleTopology (Type u) :=
    (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F
  let s : ∀ j, G.obj.obj (op (U j)) :=
    fun j => freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology (U j) F (a j)
  let t : F.obj.obj (op (etaleSigma U)) := etaleSigmaSection U G s
  let e : ((freeAbelianSheafYoneda X.smallEtaleTopology).obj (etaleSigma U) ⟶ F) ≃
      F.obj.obj (op (etaleSigma U)) :=
    freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology (etaleSigma U) F
  have hd : e (etaleSigmaFreeAbelianDesc U F a) = t := e.apply_symm_apply t
  apply (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology (U i) F).injective
  exact (freeAbelianSheafYonedaHomEquiv_precomp X.smallEtaleTopology
    (etaleSigmaInj U i) F (etaleSigmaFreeAbelianDesc U F a)).trans
      ((congrArg (fun z : F.obj.obj (op (etaleSigma U)) =>
        F.obj.map (etaleSigmaInj U i).op z) hd).trans
          (etaleSigmaSection_restrict U G s i))

/-- Actual disjoint-union section gluing supplies the original free
abelian representables' coproduct, with its actual inclusion arrows. -/
def etaleSigmaFreeAbelianIsColimit :
    IsColimit (Cofan.mk
      ((freeAbelianSheafYoneda X.smallEtaleTopology).obj (etaleSigma U))
      (fun i => (freeAbelianSheafYoneda X.smallEtaleTopology).map (etaleSigmaInj U i))) where
  desc s := etaleSigmaFreeAbelianDesc U s.pt (fun i => s.ι.app ⟨i⟩)
  fac s i := etaleSigmaFreeAbelianDesc_comp U s.pt (fun j => s.ι.app ⟨j⟩) i.as
  uniq s m hm := by
    apply (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology (etaleSigma U) s.pt).injective
    apply etaleSigmaSection_ext U
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj s.pt)
    intro i
    change s.pt.obj.map (etaleSigmaInj U i).op
        (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology (etaleSigma U) s.pt m) =
      s.pt.obj.map (etaleSigmaInj U i).op
        (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology (etaleSigma U) s.pt
          (etaleSigmaFreeAbelianDesc U s.pt (fun j => s.ι.app ⟨j⟩)))
    rw [← freeAbelianSheafYonedaHomEquiv_precomp,
      ← freeAbelianSheafYonedaHomEquiv_precomp,
      etaleSigmaFreeAbelianDesc_comp]
    exact congrArg (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology (U i) s.pt)
      (hm ⟨i⟩)

variable [Fintype ι]

/-- The original cohomology of a finite disjoint union is the product
of the original component cohomologies, in every degree. -/
def etaleFiniteSigmaCohomologyEquiv
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H'.{u} F n (etaleSigma U) ≃+ ∀ i, Sheaf.H'.{u} F n (U i) :=
  Ext.biproductAddEquiv
    (biconeIsBilimitOfColimitCoconeOfIsColimit (etaleSigmaFreeAbelianIsColimit U)) F n

/-- Each coordinate is the actual original cohomology restriction. -/
theorem etaleFiniteSigmaCohomologyEquiv_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (a : Sheaf.H'.{u} F n (etaleSigma U)) (i : ι) :
    etaleFiniteSigmaCohomologyEquiv U F n a i =
      (F.cohomologyPresheaf n).map (etaleSigmaInj U i).op a := rfl

/-- The finite-union comparison commutes with every original
coefficient morphism, including the original cyclic reductions. -/
theorem etaleFiniteSigmaCohomologyEquiv_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (η : F ⟶ G) (n : ℕ)
    (a : Sheaf.H'.{u} F n (etaleSigma U)) (i : ι) :
    etaleFiniteSigmaCohomologyEquiv U G n
        (((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology n).map η).app
          (op (etaleSigma U)) a) i =
      ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology n).map η).app (op (U i))
        (etaleFiniteSigmaCohomologyEquiv U F n a i) :=
  (ConcreteCategory.congr_hom
    (((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology n).map η).naturality
      (etaleSigmaInj U i).op) a).symm

end EtaleCohomology
