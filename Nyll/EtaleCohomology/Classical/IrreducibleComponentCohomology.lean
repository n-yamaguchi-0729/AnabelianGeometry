/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionNaturality
public import Nyll.EtaleCohomology.Classical.FiniteSigmaCohomology
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Constructible.SigmaRepresenter
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentDecomposition
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Actual cohomology on the original geometric components

The actual reduced components of a locally Noetherian scheme with
domain stalks are objects of its original small etale site. Their
actual union is terminal because the original component inclusions
give the proved scheme isomorphism. For a Noetherian scheme this gives
the actual finite component decomposition of native sheaf cohomology.

Each coordinate is the original cohomology-presheaf restriction,
followed by the original comparison with cohomology of the restricted
sheaf on the actual component scheme. No decomposition or cohomology
comparison is assumed as additional data.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology

section LocallyNoetherian

variable (X : Scheme.{u}) [IsLocallyNoetherian X]
  (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x))

/-- Each original reduced component is an actual object of the
original small etale site, through its original inclusion. -/
def reducedIrreducibleComponentEtale (Z : irreducibleComponents X) : X.Etale := by
  have : IsOpenImmersion (X.reducedIrreducibleComponentι Z.1 Z.2) :=
    X.reducedIrreducibleComponentι_isOpenImmersion hdom Z.1 Z.2
  exact Scheme.Etale.mk (X.reducedIrreducibleComponentι Z.1 Z.2)

/-- The actual union of the original etale components is terminal
in the original small site, by the proved scheme decomposition. -/
def reducedIrreducibleComponentsEtaleIsTerminal :
    IsTerminal (etaleSigma (reducedIrreducibleComponentEtale X hdom)) := by
  let S := etaleSigma (reducedIrreducibleComponentEtale X hdom)
  have : IsIso S.hom :=
    X.reducedIrreducibleComponentsToScheme_isIso hdom
  let : ∀ V : X.Etale, Unique (V ⟶ S) := fun V =>
    { default := MorphismProperty.Over.homMk (V.hom ≫ inv S.hom) (by
        rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id])
      uniq a := by
        apply MorphismProperty.Over.Hom.ext
        apply (cancel_mono S.hom).mp
        change a.left ≫ S.hom = (V.hom ≫ inv S.hom) ≫ S.hom
        rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        exact a.w }
  exact IsTerminal.ofUnique S

end LocallyNoetherian

variable (X : Scheme.{u}) [IsNoetherian X]
  (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x))

/-- Actual global sheaf cohomology decomposes over the original
finite component schemes, with their actual restricted coefficients. -/
def reducedIrreducibleComponentsCohomologyEquiv
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} F n ≃+
      ∀ Z : irreducibleComponents X,
        Sheaf.H.{u}
          ((etaleRestriction (reducedIrreducibleComponentEtale X hdom Z).hom
            AddCommGrpCat.{u}).obj F) n := by
  let : Fintype (irreducibleComponents X) := X.irreducibleComponentsFintype
  let U := reducedIrreducibleComponentEtale X hdom
  exact (sheafCohomologyTerminalEquiv X.smallEtaleTopology
    (reducedIrreducibleComponentsEtaleIsTerminal X hdom) F n).trans
      ((etaleFiniteSigmaCohomologyEquiv U F n).trans
        (AddEquiv.piCongrRight fun Z => etaleCohomologyPresheafRestrictionEquiv (U Z) F n))

/-- Each component coordinate is the original restriction of native
cohomology, under the proved original localized-site comparison. -/
theorem reducedIrreducibleComponentsCohomologyEquiv_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (a : Sheaf.H.{u} F n) (Z : irreducibleComponents X) :
    reducedIrreducibleComponentsCohomologyEquiv X hdom F n a Z =
      etaleCohomologyPresheafRestrictionEquiv
        (reducedIrreducibleComponentEtale X hdom Z) F n
          ((F.cohomologyPresheaf n).map
            (etaleSigmaInj (reducedIrreducibleComponentEtale X hdom) Z).op
              (sheafCohomologyTerminalEquiv X.smallEtaleTopology
                (reducedIrreducibleComponentsEtaleIsTerminal X hdom) F n a)) := rfl

/-- The actual finite component comparison preserves every original
coefficient map, including all original cyclic coefficient reductions. -/
theorem reducedIrreducibleComponentsCohomologyEquiv_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) (a : Sheaf.H.{u} F n)
    (Z : irreducibleComponents X) :
    reducedIrreducibleComponentsCohomologyEquiv X hdom G n (Sheaf.H.map φ n a) Z =
      Sheaf.H.map
        ((etaleRestriction (reducedIrreducibleComponentEtale X hdom Z).hom
          AddCommGrpCat.{u}).map φ) n
        (reducedIrreducibleComponentsCohomologyEquiv X hdom F n a Z) := by
  rw [reducedIrreducibleComponentsCohomologyEquiv_apply,
    reducedIrreducibleComponentsCohomologyEquiv_apply,
    sheafCohomologyTerminalEquiv_naturality]
  have h := ConcreteCategory.congr_hom
    (((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology n).map φ).naturality
      (etaleSigmaInj (reducedIrreducibleComponentEtale X hdom) Z).op)
        (sheafCohomologyTerminalEquiv X.smallEtaleTopology
          (reducedIrreducibleComponentsEtaleIsTerminal X hdom) F n a)
  exact (congrArg
    (fun z : Sheaf.H'.{u} G n (reducedIrreducibleComponentEtale X hdom Z) =>
      etaleCohomologyPresheafRestrictionEquiv
        (reducedIrreducibleComponentEtale X hdom Z) G n z) h.symm).trans
      (etaleCohomologyPresheafRestrictionEquiv_naturality
        (reducedIrreducibleComponentEtale X hdom Z) φ n
        ((F.cohomologyPresheaf n).map
          (etaleSigmaInj (reducedIrreducibleComponentEtale X hdom) Z).op
            (sheafCohomologyTerminalEquiv X.smallEtaleTopology
              (reducedIrreducibleComponentsEtaleIsTerminal X hdom) F n a)))

end EtaleCohomology
