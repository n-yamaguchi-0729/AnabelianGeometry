/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The actual Frobenius twist on roots-of-unity coefficients

Arithmetic Frobenius acts on the original roots of unity by the cardinality
of the finite base field. Its map on constant-root cohomology is therefore
multiplication by that cardinality in every degree. The inverse arithmetic
coefficient map is its actual inverse, without a compatibility assumption
on any chosen primitive-root coordinates.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

private theorem additiveFunctor_map_nsmul_id_apply
    (H : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}) [H.Additive]
    {A : AddCommGrpCat.{u}} (f : A ⟶ A) (m : ℕ)
    (hf : f = m • 𝟙 A) (a : H.obj A) : H.map f a = m • a := by
  have hm : H.map f = m • 𝟙 (H.obj A) :=
    (congrArg H.map hf).trans (H.map_nsmul.trans (congrArg (m • ·) (H.map_id A)))
  have hv : (m • 𝟙 (H.obj A)) a = m • a := rfl
  exact (ConcreteCategory.congr_hom hm a).trans hv

private theorem functor_comp_apply_eq_self
    (H : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u})
    {A : AddCommGrpCat.{u}} (f g : A ⟶ A)
    (h : f ≫ g = 𝟙 A) (a : H.obj A) : H.map g (H.map f a) = a := by
  have hm : H.map f ≫ H.map g = 𝟙 (H.obj A) :=
    (H.map_comp f g).symm.trans ((congrArg H.map h).trans (H.map_id A))
  exact (CategoryTheory.comp_apply (H.map f) (H.map g) a).symm.trans
    ((ConcreteCategory.congr_hom hm a).trans (ConcreteCategory.id_apply a))

variable (k K : Type u) [Field k] [Fintype k] [Field K] [Algebra k K]
  [Algebra.IsAlgebraic k K]

/-- Actual arithmetic Frobenius on the original roots of unity is
multiplication by the cardinality of the finite field in additive notation. -/
theorem rootsOfUnityFrobeniusCoefficient_eq_nsmul (n : ℕ) :
    AddCommGrpCat.ofHom
        (restrictRootsOfUnity
          (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom n).toAdditive =
      (Fintype.card k) • 𝟙 (AddCommGrpCat.of (Additive (rootsOfUnity n K))) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro ζ
  apply Additive.toMul.injective
  apply rootsOfUnity.coe_injective
  let μ : rootsOfUnity n K :=
    Additive.toMul (show Additive (rootsOfUnity n K) from ζ)
  exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic k K) ((μ : Kˣ) : K)

/-- The actual inverse arithmetic root map followed by arithmetic
Frobenius is the identity coefficient morphism. -/
theorem rootsOfUnityInverseFrobeniusCoefficient_comp (n : ℕ) :
    AddCommGrpCat.ofHom
        (restrictRootsOfUnity
          (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm.toRingHom n).toAdditive ≫
      AddCommGrpCat.ofHom
        (restrictRootsOfUnity
          (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom n).toAdditive =
      𝟙 (AddCommGrpCat.of (Additive (rootsOfUnity n K))) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro ζ
  apply Additive.toMul.injective
  apply rootsOfUnity.coe_injective
  let μ : rootsOfUnity n K :=
    Additive.toMul (show Additive (rootsOfUnity n K) from ζ)
  exact (FiniteField.frobeniusAlgEquivOfAlgebraic k K).apply_symm_apply ((μ : Kˣ) : K)

/-- The original coefficient action on constant-root cohomology is
multiplication by the finite-field cardinality in every degree. -/
theorem rootsOfUnityCohomology_frobeniusCoefficient
    (X : Scheme.{u}) (n i : ℕ)
    (a : Sheaf.H.{u} (J := X.smallEtaleTopology)
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (.of (Additive (rootsOfUnity n K)))) i) :
    Sheaf.H.map (J := X.smallEtaleTopology)
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (AddCommGrpCat.ofHom (restrictRootsOfUnity
          (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom n).toAdditive)) i a =
      (Fintype.card k) • a := by
  let A : AddCommGrpCat.{u} := AddCommGrpCat.of (Additive (rootsOfUnity n K))
  let H : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      Sheaf.functorH.{u} X.smallEtaleTopology i
  let β : A ⟶ A := AddCommGrpCat.ofHom (restrictRootsOfUnity
    (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom n).toAdditive
  exact additiveFunctor_map_nsmul_id_apply H β (Fintype.card k)
    (rootsOfUnityFrobeniusCoefficient_eq_nsmul k K n) a

/-- The actual inverse arithmetic coefficient map cancels the
cardinality action on the original cohomology in every degree. -/
theorem rootsOfUnityCohomology_inverseFrobeniusCoefficient_cancel
    (X : Scheme.{u}) (n i : ℕ)
    (a : Sheaf.H.{u} (J := X.smallEtaleTopology)
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (.of (Additive (rootsOfUnity n K)))) i) :
    (Fintype.card k) •
        Sheaf.H.map (J := X.smallEtaleTopology)
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
          (AddCommGrpCat.ofHom (restrictRootsOfUnity
            (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm.toRingHom n).toAdditive)) i a =
      a := by
  let A : AddCommGrpCat.{u} := AddCommGrpCat.of (Additive (rootsOfUnity n K))
  let H : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      Sheaf.functorH.{u} X.smallEtaleTopology i
  let α : A ⟶ A := AddCommGrpCat.ofHom (restrictRootsOfUnity
    (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm.toRingHom n).toAdditive
  let β : A ⟶ A := AddCommGrpCat.ofHom (restrictRootsOfUnity
    (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom n).toAdditive
  exact (rootsOfUnityCohomology_frobeniusCoefficient k K X n i (H.map α a)).symm.trans
    (functor_comp_apply_eq_self H α β (rootsOfUnityInverseFrobeniusCoefficient_comp k K n) a)

end EtaleCohomology
