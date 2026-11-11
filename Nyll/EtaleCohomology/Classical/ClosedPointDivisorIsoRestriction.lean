/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.JacobsonSpace

/-!
# Transport of the actual divisor sheaf along a chart isomorphism

The residue-field map of the scheme isomorphism gives the cartesian square
for each closed-point summand. Existing restriction base change and constant
sheaf comparison provide the summand isomorphism. The whole divisor sheaf
is transported by preserving and reindexing its original coproduct.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace EtaleCohomology

variable {U X : Scheme.{u}} (e : U ≅ X)

/-- The original residue-field square transports a closed-point summand
along a scheme isomorphism. -/
def closedPointDivisorSummandIsoRestrictionIso (y : closedPoints U) :
    (etaleRestriction e.hom AddCommGrpCat.{u}).obj
        (closedPointDivisorSummand X
          ((e.hom.homeomorph.sets
            e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv y)) ≅
      closedPointDivisorSummand U y := by
  let x : closedPoints X := (e.hom.homeomorph.sets
    e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv y
  let g : Spec (U.residueField y.1) ⟶ Spec (X.residueField x.1) :=
    Spec.map (e.hom.residueFieldMap y.1)
  have : IsIso (e.hom.residueFieldMap y.1) := inferInstance
  have : IsIso g := inferInstanceAs (IsIso (Spec.map (e.hom.residueFieldMap y.1)))
  have hg : Etale g := inferInstance
  have H : IsPullback (closedPointResidueFieldMap U y) g e.hom
      (closedPointResidueFieldMap X x) := by
    apply IsPullback.of_vert_isIso
    exact ⟨(e.hom.SpecMap_residueFieldMap_fromSpecResidueField y.1).symm⟩
  let C := (constantSheaf (Spec (X.residueField x.1)).smallEtaleTopology
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  let k : (etaleRestriction g AddCommGrpCat.{u}).obj C ≅
      (constantSheaf (Spec (U.residueField y.1)).smallEtaleTopology
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    (Sites.constantSheafCompLeftAdjointIso (etaleBaseChange g) AddCommGrpCat.{u}
      terminalIsTerminal
      (terminalIsTerminal.isTerminalObj (etaleBaseChange g)
        (⊤_ (Spec (X.residueField x.1)).Etale))
      (etaleRestriction g AddCommGrpCat.{u})
      (etaleRestrictionPushforwardAdjunction g AddCommGrpCat.{u})).app
        (AddCommGrpCat.of (ULift.{u} ℤ))
  exact (@etaleRestrictionPushforwardBaseChangeIsoOfIsPullback
      X (Spec (X.residueField x.1)) U e.hom (inferInstance : Etale e.hom)
      (closedPointResidueFieldMap X x) AddCommGrpCat.{u} inferInstance
      (Spec (U.residueField y.1)) (closedPointResidueFieldMap U y) g hg H).app C ≪≫
    (etaleAbelianPushforward (closedPointResidueFieldMap U y)).mapIso k

/-- The actual closed-point divisor sheaf is preserved by a scheme
isomorphism, through its native residue-field maps. -/
def closedPointDivisorIsoRestrictionIso :
    (etaleRestriction e.hom AddCommGrpCat.{u}).obj (closedPointDivisorSheaf X) ≅
      closedPointDivisorSheaf U := by
  let R := etaleRestriction e.hom AddCommGrpCat.{u}
  have : R.IsLeftAdjoint :=
    ⟨_, ⟨etaleRestrictionPushforwardAdjunction e.hom AddCommGrpCat.{u}⟩⟩
  have : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape X
  have : HasColimitsOfShape (Discrete (closedPoints U))
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape U
  have : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :=
    @CategoryTheory.Sheaf.instHasColimitsOfShape U.Etale _ U.smallEtaleTopology
      AddCommGrpCat.{u} _ (Discrete (closedPoints X)) _ inferInstance inferInstance
  let t : closedPoints U ≃ closedPoints X :=
    (e.hom.homeomorph.sets e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv
  let A := fun x : closedPoints X => R.obj (closedPointDivisorSummand X x)
  let d : Discrete.functor (A ∘ t) ≅ Discrete.functor (closedPointDivisorSummand U) :=
    Discrete.natIso (fun y => closedPointDivisorSummandIsoRestrictionIso e y.as)
  change R.obj (∐ (closedPointDivisorSummand X)) ≅ ∐ (closedPointDivisorSummand U)
  exact PreservesCoproduct.iso R (closedPointDivisorSummand X) ≪≫
    (Sigma.reindex t A).symm ≪≫ HasColimit.isoOfNatIso d

/-- The chart transport of the whole divisor sheaf preserves the original
inclusion of each residue-field summand. -/
theorem closedPointDivisorIsoRestrictionIso_injection (y : closedPoints U) :
    (etaleRestriction e.hom AddCommGrpCat.{u}).map
        (closedPointDivisorSheafInjection X
          ((e.hom.homeomorph.sets
            e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv y)) ≫
      (closedPointDivisorIsoRestrictionIso e).hom =
    (closedPointDivisorSummandIsoRestrictionIso e y).hom ≫
      closedPointDivisorSheafInjection U y := by
  let R := etaleRestriction e.hom AddCommGrpCat.{u}
  have : R.IsLeftAdjoint :=
    ⟨_, ⟨etaleRestrictionPushforwardAdjunction e.hom AddCommGrpCat.{u}⟩⟩
  have : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape X
  have : HasColimitsOfShape (Discrete (closedPoints U))
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape U
  have : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :=
    @CategoryTheory.Sheaf.instHasColimitsOfShape U.Etale _ U.smallEtaleTopology
      AddCommGrpCat.{u} _ (Discrete (closedPoints X)) _ inferInstance inferInstance
  let t : closedPoints U ≃ closedPoints X :=
    (e.hom.homeomorph.sets e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv
  let F := closedPointDivisorSummand X
  let A := fun x : closedPoints X => R.obj (F x)
  let d : Discrete.functor (A ∘ t) ≅ Discrete.functor (closedPointDivisorSummand U) :=
    Discrete.natIso (fun z => closedPointDivisorSummandIsoRestrictionIso e z.as)
  have hpres : R.map (Sigma.ι F (t y)) ≫
      (PreservesCoproduct.iso R F).hom = Sigma.ι A (t y) := by
    rw [← cancel_mono (PreservesCoproduct.iso R F).inv,
      Category.assoc, Iso.hom_inv_id, Category.comp_id,
      PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  change R.map (Sigma.ι F (t y)) ≫
      (PreservesCoproduct.iso R F ≪≫ (Sigma.reindex t A).symm ≪≫
        HasColimit.isoOfNatIso d).hom = _
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  rw [hpres, Sigma.ι_reindex_inv t A y]
  exact HasColimit.ι_isoOfNatIso_hom d ⟨y⟩

end EtaleCohomology
