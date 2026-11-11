/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FunctionFields.GenericFieldSource
public import Nyll.SchemeTheory.Normalization.GenericFiber.GenericExtension
public import Nyll.SchemeTheory.LocalGeometry.SmoothnessDefect

/-!
# Local rings inside an actual generic field source

A dominant preimmersion from a field spectrum identifies that field with
the function field. Every local ring therefore has that same field of
fractions, through a map whose spectrum factors the original morphism.
An actual equality over the base proves compatibility with its structural
coefficients. The generic source of an algebraic normalization supplies
the required preimmersion by its canonical generic-fibre pullback.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NeronModelInfra

namespace EtaleFundamentalGroups

universe u

section Stalk

variable {C : Scheme.{u}} [IsIntegral C] {L : Type u} [Field L]
  (p : Spec (.of L) ⟶ C) [IsDominant p] [IsPreimmersion p] (z : C)

/-- The local-ring algebra in the specified generic source uses its actual
generic-stalk isomorphism. -/
@[reducible]
def genericFieldSourceStalkAlgebra : Algebra (C.presheaf.stalk z) L :=
  let : Algebra C.functionField L := (genericFieldSourceRingEquiv p).toRingHom.toAlgebra
  C.stalkExtensionAlgebra z L

/-- The specified generic field is the fraction field of each local ring. -/
theorem genericFieldSourceStalk_isFractionRing :
    let : Algebra (C.presheaf.stalk z) L := genericFieldSourceStalkAlgebra p z
    IsFractionRing (C.presheaf.stalk z) L := by
  intro stalkFieldAlgebra
  exact IsFractionRing.of_algEquiv
    (AlgEquiv.ofRingEquiv (f := genericFieldSourceRingEquiv p) (fun _ => rfl))

/-- The spectrum of the local-ring coefficient map factors the original
generic morphism, with its original field source. -/
@[reassoc]
theorem genericFieldSourceStalkMap_fromSpecStalk :
    let : Algebra (C.presheaf.stalk z) L := genericFieldSourceStalkAlgebra p z
    Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk z) L)) ≫
      C.fromSpecStalk z = p := by
  intro stalkFieldAlgebra
  let s : C.presheaf.stalk z ⟶ C.functionField :=
    C.presheaf.stalkSpecializes (genericPoint_specializes z)
  let e : C.functionField ⟶ CommRingCat.of L :=
    CommRingCat.ofHom (genericFieldSourceRingEquiv p).toRingHom
  have hcoeff : CommRingCat.ofHom (algebraMap (C.presheaf.stalk z) L) = s ≫ e := rfl
  have hs : Spec.map s ≫ C.fromSpecStalk z = C.fromSpecStalk (genericPoint C) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes z)
  calc
    Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk z) L)) ≫
        C.fromSpecStalk z = Spec.map (s ≫ e) ≫ C.fromSpecStalk z :=
      congrArg (fun f : C.presheaf.stalk z ⟶ CommRingCat.of L =>
        Spec.map f ≫ C.fromSpecStalk z) hcoeff
    _ = (Spec.map e ≫ Spec.map s) ≫ C.fromSpecStalk z :=
      congrArg (fun f : Spec (.of L) ⟶ Spec (C.presheaf.stalk z) =>
        f ≫ C.fromSpecStalk z) (Spec.map_comp s e)
    _ = Spec.map e ≫ (Spec.map s ≫ C.fromSpecStalk z) := Category.assoc _ _ _
    _ = Spec.map e ≫ C.fromSpecStalk (genericPoint C) :=
      congrArg (fun f => Spec.map e ≫ f) hs
    _ = p := genericFieldSourceIso_hom_fromSpecStalk p

variable {k : Type u} [CommRing k] [Algebra k L]
  (c : C ⟶ Spec (.of k))

/-- The literal structural equality of the generic morphism supplies the
constant-field scalar tower on every local ring. -/
theorem genericFieldSourceStalk_isScalarTower
    (hp : p ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    let : Algebra k (C.presheaf.stalk z) := stalkAlgebra c z
    let : Algebra (C.presheaf.stalk z) L := genericFieldSourceStalkAlgebra p z
    IsScalarTower k (C.presheaf.stalk z) L := by
  intro baseStalkAlgebra stalkFieldAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  have h : CommRingCat.ofHom (algebraMap k L) =
      CommRingCat.ofHom (algebraMap k (C.presheaf.stalk z)) ≫
        CommRingCat.ofHom (algebraMap (C.presheaf.stalk z) L) := by
    apply Spec.map_injective
    rw [Spec.map_comp,
      ← fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra c z,
      ← Category.assoc, genericFieldSourceStalkMap_fromSpecStalk p z, hp]
  exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of L => f.hom) h

end Stalk

/-- The actual field source of an algebraic generic normalization is a
preimmersion, by its canonical identification with the generic pullback. -/
instance genericExtensionNormalization_toNormalization_isPreimmersion
    (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L]
    [Algebra X.functionField L] [Algebra.IsAlgebraic X.functionField L] :
    IsPreimmersion (X.genericExtensionMorphism L).toNormalization := by
  rw [← genericExtensionNormalizationFiberIso_hom_fst X L]
  infer_instance

end EtaleFundamentalGroups
