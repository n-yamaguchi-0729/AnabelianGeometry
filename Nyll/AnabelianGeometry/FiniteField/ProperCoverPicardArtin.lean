/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.ProperCoverRamification
public import Nyll.EtaleFundamentalGroups.GaloisCovers.LocalArtinAction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.UnramifiedNormPicard
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Picard reciprocity for an original proper finite étale cover

For an actual finite abelian Galois cover of a smooth proper curve, derive
unramifiedness at every original place and apply the proved unramified
Picard norm comparison. The resulting equivalence lands in the original
opposite deck group. Its formula on every idele-class representative is
the existing finite-cover Artin map, preserving native monodromy.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry AlgebraicCurve
open FunctionField EtaleFundamentalGroups

namespace AnabelianGeometry.FiniteField

attribute [local instance]
  EtaleFundamentalGroups.finiteCoverIdeleClassMulOneClass
  EtaleFundamentalGroups.finiteCoverIdeleClassGroup

/-- Unramified Picard norm reciprocity in the original finite Galois group. -/
def unramifiedPicardNormGaloisEquiv
    (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    (hram : ∀ w : Place k L, w.ramificationIndex K = 1) :
    (Multiplicative (Pic k K) ⧸
      (Pic.norm (k := k) (K := K) (L := L)).toMultiplicative.range) ≃* Gal(L/K) :=
  (IdeleClassGroup.normQuotientEquivPicard_of_unramified hram).symm.trans
    (abelianFiniteNormQuotientEquiv k K L)

private theorem unramifiedPicardNormGaloisEquiv_mk
    (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    (hram : ∀ w : Place k L, w.ramificationIndex K = 1)
    (z : IdeleClassGroup k K) :
    unramifiedPicardNormGaloisEquiv k K L hram
        (QuotientGroup.mk (IdeleClassGroup.divisorClass z)) = abelianFiniteArtin k K L z := by
  let e := IdeleClassGroup.normQuotientEquivPicard_of_unramified hram
  have he : e (QuotientGroup.mk z) =
      QuotientGroup.mk (IdeleClassGroup.divisorClass z) := rfl
  change abelianFiniteNormQuotientEquiv k K L
    (e.symm (QuotientGroup.mk (IdeleClassGroup.divisorClass z))) = _
  rw [← he, e.symm_apply_apply]
  rfl

/-- Transport unramified Picard norm reciprocity to the supplied actual deck group.
The construction is performed with abstract coefficient fields, before scheme
function-field owners are instantiated. -/
def unramifiedPicardNormDeckEquiv
    (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    (hram : ∀ w : Place k L, w.ramificationIndex K = 1)
    {D : Type} [Group D] (eDeck : D ≃* Gal(L/K)) :
    (Multiplicative (Pic k K) ⧸
      (Pic.norm (k := k) (K := K) (L := L)).toMultiplicative.range) ≃* D :=
  (unramifiedPicardNormGaloisEquiv k K L hram).trans eDeck.symm

/-- Evaluation of the actual norm-to-deck construction uses only its two
original field and deck components. -/
theorem unramifiedPicardNormDeckEquiv_apply
    (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    (hram : ∀ w : Place k L, w.ramificationIndex K = 1)
    {D : Type} [Group D] (eDeck : D ≃* Gal(L/K))
    (q : Multiplicative (Pic k K) ⧸
      (Pic.norm (k := k) (K := K) (L := L)).toMultiplicative.range) :
    unramifiedPicardNormDeckEquiv k K L hram eDeck q =
      eDeck.symm (unramifiedPicardNormGaloisEquiv k K L hram q) := rfl

variable {k : Type} [Field k] [Finite k] {X : Scheme}
  [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
  (c : X ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
  (W : FiniteEtale X) [IsGalois W]

/-- The original Picard norm quotient is the original opposite deck group.
The rational parameter is only the standard function-field presentation
needed by existing reciprocity; the ground-field algebra is the literal
one induced by the given structural morphism. -/
def properFiniteEtaleCoverPicardNormEquiv :
    let _ : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let _ : Algebra X.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    let _ : Algebra k W.left.functionField :=
      ((algebraMap X.functionField W.left.functionField).comp
        (algebraMap k X.functionField)).toAlgebra
    have _ : FiniteDimensional X.functionField W.left.functionField :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    have _ : IsScalarTower k X.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField] [FunctionField k X.functionField]
      [IsAbelianGalois X.functionField W.left.functionField],
    have _ : HasPrincipalDivisors k X.functionField :=
      (FunctionField.isCurveOver k X.functionField).toHasPrincipalDivisors
    have _ : HasPrincipalDivisors k W.left.functionField :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver
        k X.functionField W.left.functionField).toHasPrincipalDivisors
    let _ : Algebra (RatFunc k) W.left.functionField :=
      ((algebraMap X.functionField W.left.functionField).comp
        (algebraMap (RatFunc k) X.functionField)).toAlgebra
    have _ : IsScalarTower (RatFunc k) X.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have _ : IsScalarTower k (RatFunc k) W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun a =>
        congrArg (algebraMap X.functionField W.left.functionField)
          (IsScalarTower.algebraMap_apply k (RatFunc k) X.functionField a)
    have _ : FunctionField k W.left.functionField :=
      FiniteDimensional.trans (RatFunc k) X.functionField W.left.functionField
    (Multiplicative (Pic k X.functionField) ⧸
      (Pic.norm (k := k) (K := X.functionField)
        (L := W.left.functionField)).toMultiplicative.range) ≃* (Aut W)ᵐᵒᵖ := by
  intro integral aXL akX akL hXL hkXL aR hkRX hFX hAb hPX hPL aRL hRXL hkRL hFL
  have hram (w : Place k W.left.functionField) :
      w.ramificationIndex X.functionField = 1 :=
    properFiniteEtale_ramificationIndex_eq_one c W w
  exact unramifiedPicardNormDeckEquiv k X.functionField W.left.functionField hram
    (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance)

attribute [local irreducible]
  unramifiedPicardNormGaloisEquiv
  unramifiedPicardNormDeckEquiv
  EtaleFundamentalGroups.finiteEtaleCoverArtin

/-- On an original divisor-class representative, the Picard quotient
equivalence is exactly the original finite-cover Artin map. -/
theorem properFiniteEtaleCoverPicardNormEquiv_mk :
    let _ : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let _ : Algebra X.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    let _ : Algebra k W.left.functionField :=
      ((algebraMap X.functionField W.left.functionField).comp
        (algebraMap k X.functionField)).toAlgebra
    have _ : FiniteDimensional X.functionField W.left.functionField :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    have _ : IsScalarTower k X.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField] [FunctionField k X.functionField]
      [IsAbelianGalois X.functionField W.left.functionField],
    have _ : HasPrincipalDivisors k X.functionField :=
      (FunctionField.isCurveOver k X.functionField).toHasPrincipalDivisors
    have _ : HasPrincipalDivisors k W.left.functionField :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver
        k X.functionField W.left.functionField).toHasPrincipalDivisors
    let _ : Algebra (RatFunc k) W.left.functionField :=
      ((algebraMap X.functionField W.left.functionField).comp
        (algebraMap (RatFunc k) X.functionField)).toAlgebra
    have _ : IsScalarTower (RatFunc k) X.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have _ : IsScalarTower k (RatFunc k) W.left.functionField :=
      IsScalarTower.of_algebraMap_eq fun a =>
        congrArg (algebraMap X.functionField W.left.functionField)
          (IsScalarTower.algebraMap_apply k (RatFunc k) X.functionField a)
    have _ : FunctionField k W.left.functionField :=
      FiniteDimensional.trans (RatFunc k) X.functionField W.left.functionField
    ∀ z : IdeleClassGroup k X.functionField,
      properFiniteEtaleCoverPicardNormEquiv c W
        (QuotientGroup.mk (IdeleClassGroup.divisorClass z)) = finiteEtaleCoverArtin W k z := by
  intro integral aXL akX akL hXL hkXL aR hkRX hFX hAb hPX hPL aRL hRXL hkRL hFL z
  have hram (w : Place k W.left.functionField) :
      w.ramificationIndex X.functionField = 1 :=
    properFiniteEtale_ramificationIndex_eq_one c W w
  let eDeck : (Aut W)ᵐᵒᵖ ≃* Gal(W.left.functionField/X.functionField) :=
    finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance
  let eNorm :
      (Multiplicative (Pic k X.functionField) ⧸
        (Pic.norm (k := k) (K := X.functionField)
          (L := W.left.functionField)).toMultiplicative.range) ≃*
        Gal(W.left.functionField/X.functionField) :=
    unramifiedPicardNormGaloisEquiv k X.functionField W.left.functionField hram
  have hNorm : eNorm (QuotientGroup.mk (IdeleClassGroup.divisorClass z)) =
      abelianFiniteArtin k X.functionField W.left.functionField z :=
    unramifiedPicardNormGaloisEquiv_mk k X.functionField W.left.functionField hram z
  calc
    properFiniteEtaleCoverPicardNormEquiv c W
        (QuotientGroup.mk (IdeleClassGroup.divisorClass z)) =
        eDeck.symm (eNorm (QuotientGroup.mk (IdeleClassGroup.divisorClass z))) :=
      unramifiedPicardNormDeckEquiv_apply k X.functionField W.left.functionField hram eDeck
        (QuotientGroup.mk (IdeleClassGroup.divisorClass z))
    _ = eDeck.symm (abelianFiniteArtin k X.functionField W.left.functionField z) :=
      congrArg eDeck.symm hNorm
    _ = finiteEtaleCoverArtin W k z := (finiteEtaleCoverArtin_apply W k z).symm

end AnabelianGeometry.FiniteField
