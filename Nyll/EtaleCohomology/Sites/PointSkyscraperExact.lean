/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exact point skyscrapers and their actual small products

For coefficients with exact products, a point skyscraper sends an epimorphism
to an epimorphism on every section. The same holds for the functor sending a
family of coefficients to the product of their point skyscrapers: evaluation
of the actual sheaf product is compared with the product of evaluations.

Only products in the coefficient category are assumed exact. No exactness of
arbitrary products of sheaves is used.
-/

@[expose] public section

noncomputable section

universe u v w uA

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type uA} [Category.{w} A] [Abelian A] [HasLimits A]
  [HasColimitsOfSize.{w, w} A] [AB4Star A] [HasSheafify J A]

omit [HasColimitsOfSize.{w, w} A] in
private theorem epi_pi_map {ι : Type w} {M N : ι → A}
    (f : ∀ i, M i ⟶ N i) [∀ i, Epi (f i)] : Epi (Limits.Pi.map f) := by
  let δ : Discrete.functor M ⟶ Discrete.functor N :=
    Discrete.natTrans (fun i => f i.as)
  have : ∀ i : Discrete ι, Epi (δ.app i) := fun i => inferInstanceAs (Epi (f i.as))
  have : Epi δ := NatTrans.epi_of_epi_app δ
  change Epi ((lim (J := Discrete ι) (C := A)).map δ)
  infer_instance

omit [HasColimitsOfSize.{w, w} A] [HasSheafify J A] in
/-- A native skyscraper sends a coefficient epimorphism to an epimorphism
on every actual presheaf section. -/
theorem skyscraperSheafFunctor_map_app_epi (Φ : Point.{w} J)
    {M N : A} (f : M ⟶ N) [Epi f] (U : Cᵒᵖ) :
    Epi (((Φ.skyscraperSheafFunctor.map f).hom).app U) := by
  change Epi (Limits.Pi.map (fun _ : Φ.fiber.obj U.unop => f))
  exact epi_pi_map (fun _ : Φ.fiber.obj U.unop => f)

instance skyscraperSheafFunctor_preservesEpimorphisms (Φ : Point.{w} J) :
    (Φ.skyscraperSheafFunctor (A := A)).PreservesEpimorphisms where
  preserves f _ := by
    have : ∀ U : Cᵒᵖ, Epi (((Φ.skyscraperSheafFunctor.map f).hom).app U) :=
      fun U => skyscraperSheafFunctor_map_app_epi Φ f U
    have : Epi ((Φ.skyscraperSheafFunctor.map f).hom) := NatTrans.epi_of_epi_app _
    infer_instance

instance skyscraperSheafFunctor_preservesHomology (Φ : Point.{w} J) :
    (Φ.skyscraperSheafFunctor (A := A)).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

variable {ι : Type w} (Φ : ι → Point.{w} J)

/-- The actual family of fiber functors, with its values bundled as a
diagram over the discrete indexing category. -/
def familySheafFiber : Sheaf J A ⥤ (Discrete ι ⥤ A) where
  obj F := Discrete.functor (fun i => (Φ i).sheafFiber.obj F)
  map f := Discrete.natTrans (fun i => (Φ i.as).sheafFiber.map f)
  map_id F := by
    apply NatTrans.ext
    funext i
    exact (Φ i.as).sheafFiber.map_id F
  map_comp f g := by
    apply NatTrans.ext
    funext i
    exact (Φ i.as).sheafFiber.map_comp f g

/-- The product of the native skyscraper sheaves attached to a small
family of points and their respective coefficient objects. -/
def familySkyscraperSheafFunctor : (Discrete ι ⥤ A) ⥤ Sheaf J A :=
  Functor.pi' (fun i => (evaluation (Discrete ι) A).obj (Discrete.mk i) ⋙
    (Φ i).skyscraperSheafFunctor) ⋙ Limits.Pi.functor ι

/-- The product of skyscraper adjunctions on the original family of fibers. -/
def familySkyscraperHomEquiv (F : Sheaf J A) (M : Discrete ι ⥤ A) :
    (Discrete.functor (fun i => (Φ i).sheafFiber.obj F) ⟶ M) ≃
      (F ⟶ ∏ᶜ (fun i => (Φ i).skyscraperSheafFunctor.obj (M.obj (Discrete.mk i)))) where
  toFun f := Limits.Pi.lift (fun i =>
    ((Φ i).skyscraperSheafAdjunction.homEquiv F (M.obj (Discrete.mk i)))
      (f.app (Discrete.mk i)))
  invFun g := Discrete.natTrans (fun i =>
    ((Φ i.as).skyscraperSheafAdjunction.homEquiv F (M.obj i)).symm
      (g ≫ Limits.Pi.π
        (fun j => (Φ j).skyscraperSheafFunctor.obj (M.obj (Discrete.mk j))) i.as))
  left_inv f := by
    apply NatTrans.ext
    funext i
    cases i with
    | mk i =>
      change ((Φ i).skyscraperSheafAdjunction.homEquiv F (M.obj (Discrete.mk i))).symm
        (Limits.Pi.lift
          (fun j => ((Φ j).skyscraperSheafAdjunction.homEquiv F (M.obj (Discrete.mk j)))
            (f.app (Discrete.mk j))) ≫
          Limits.Pi.π
            (fun j => (Φ j).skyscraperSheafFunctor.obj (M.obj (Discrete.mk j))) i) =
        f.app (Discrete.mk i)
      rw [Limits.Pi.lift_comp_π, Equiv.symm_apply_apply]
  right_inv g := by
    apply Limits.Pi.hom_ext
    intro i
    rw [Limits.Pi.lift_comp_π]
    exact Equiv.apply_symm_apply
      ((Φ i).skyscraperSheafAdjunction.homEquiv F (M.obj (Discrete.mk i))) _

/-- The family of actual fibers is left adjoint to the actual product of
the corresponding native skyscraper sheaves. -/
def familySkyscraperSheafAdjunction :
    familySheafFiber Φ (A := A) ⊣ familySkyscraperSheafFunctor Φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := familySkyscraperHomEquiv Φ
      homEquiv_naturality_left_symm := by
        intro F G M f g
        change G ⟶ ∏ᶜ
          (fun j => (Φ j).skyscraperSheafFunctor.obj (M.obj (Discrete.mk j))) at g
        apply NatTrans.ext
        funext i
        change ((Φ i.as).skyscraperSheafAdjunction.homEquiv F (M.obj i)).symm
          ((f ≫ g) ≫ Limits.Pi.π
            (fun j => (Φ j).skyscraperSheafFunctor.obj (M.obj (Discrete.mk j))) i.as) =
          (Φ i.as).sheafFiber.map f ≫
            ((Φ i.as).skyscraperSheafAdjunction.homEquiv G (M.obj i)).symm
              (g ≫ Limits.Pi.π
                (fun j => (Φ j).skyscraperSheafFunctor.obj (M.obj (Discrete.mk j))) i.as)
        rw [Category.assoc]
        exact (Φ i.as).skyscraperSheafAdjunction.homEquiv_naturality_left_symm f _
      homEquiv_naturality_right := by
        intro F M N f g
        change Discrete.functor (fun i => (Φ i).sheafFiber.obj F) ⟶ M at f
        apply Limits.Pi.hom_ext
        intro i
        change Limits.Pi.lift
            (fun j => ((Φ j).skyscraperSheafAdjunction.homEquiv F (N.obj (Discrete.mk j)))
              (f.app (Discrete.mk j) ≫ g.app (Discrete.mk j))) ≫
            Limits.Pi.π
              (fun j => (Φ j).skyscraperSheafFunctor.obj (N.obj (Discrete.mk j))) i =
          (Limits.Pi.lift
            (fun j => ((Φ j).skyscraperSheafAdjunction.homEquiv F (M.obj (Discrete.mk j)))
              (f.app (Discrete.mk j))) ≫
            Limits.Pi.map (fun j => (Φ j).skyscraperSheafFunctor.map
              (g.app (Discrete.mk j)))) ≫
          Limits.Pi.π
            (fun j => (Φ j).skyscraperSheafFunctor.obj (N.obj (Discrete.mk j))) i
        rw [Category.assoc, Limits.Pi.map_π, ← Category.assoc,
          Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π]
        exact (Φ i).skyscraperSheafAdjunction.homEquiv_naturality_right
          (f.app (Discrete.mk i)) (g.app (Discrete.mk i)) }

instance familySkyscraperSheafFunctor_isRightAdjoint :
    (familySkyscraperSheafFunctor Φ (A := A)).IsRightAdjoint :=
  (familySkyscraperSheafAdjunction Φ).isRightAdjoint

omit [HasColimitsOfSize.{w, w} A] [HasSheafify J A] in
private theorem epi_map_pi_of_sectionwise_epi
    (U : Cᵒᵖ) {M N : ι → Sheaf J A} (f : ∀ i, M i ⟶ N i)
    [∀ i, Epi ((f i).hom.app U)] :
    Epi ((Limits.Pi.map f).hom.app U) := by
  let E : Sheaf J A ⥤ A :=
    sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj U
  have h : E.map (Limits.Pi.map f) ≫ piComparison E N =
      piComparison E M ≫ Limits.Pi.map (fun i => E.map (f i)) := by
    apply Limits.Pi.hom_ext
    intro i
    rw [Category.assoc, piComparison_comp_π, ← E.map_comp, Limits.Pi.map_π,
      E.map_comp, Category.assoc, Limits.Pi.map_π, ← Category.assoc, piComparison_comp_π]
  have : ∀ i, Epi (E.map (f i)) := fun i => inferInstanceAs (Epi ((f i).hom.app U))
  have : Epi (Limits.Pi.map (fun i => E.map (f i))) :=
    epi_pi_map (fun i => E.map (f i))
  have : Epi (E.map (Limits.Pi.map f) ≫ piComparison E N) := by
    rw [h]
    infer_instance
  exact (epi_comp_iff_of_isIso (E.map (Limits.Pi.map f)) (piComparison E N)).mp inferInstance

omit [HasColimitsOfSize.{w, w} A] [HasSheafify J A] in
/-- Evaluating the actual product of point skyscrapers sends every
coefficient-family epimorphism to an epimorphism in the coefficient category. -/
theorem familySkyscraperSheafFunctor_map_app_epi
    {M N : Discrete ι ⥤ A} (f : M ⟶ N) [Epi f] (U : Cᵒᵖ) :
    Epi ((((familySkyscraperSheafFunctor Φ).map f).hom).app U) := by
  have : ∀ i : ι, Epi ((((Φ i).skyscraperSheafFunctor.map
      (f.app (Discrete.mk i))).hom).app U) :=
    fun i => skyscraperSheafFunctor_map_app_epi (Φ i) (f.app (Discrete.mk i)) U
  exact epi_map_pi_of_sectionwise_epi U
    (fun i => (Φ i).skyscraperSheafFunctor.map (f.app (Discrete.mk i)))

instance familySkyscraperSheafFunctor_preservesEpimorphisms :
    (familySkyscraperSheafFunctor Φ (A := A)).PreservesEpimorphisms where
  preserves f _ := by
    have : ∀ U : Cᵒᵖ,
        Epi ((((familySkyscraperSheafFunctor Φ).map f).hom).app U) :=
      fun U => familySkyscraperSheafFunctor_map_app_epi Φ f U
    have : Epi (((familySkyscraperSheafFunctor Φ).map f).hom) :=
      NatTrans.epi_of_epi_app _
    infer_instance

instance familySkyscraperSheafFunctor_preservesHomology :
    (familySkyscraperSheafFunctor Φ (A := A)).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

end CategoryTheory.GrothendieckTopology.Point
