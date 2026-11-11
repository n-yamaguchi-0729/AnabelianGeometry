/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.ConstantFieldInclusionFiberPoint
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Actual compactifications after finite constant-field base change

The compactification is the literal constant-field pullback of the original
proper model. Its map from the actual constant cover is the original
coefficient model map. Connectedness follows from geometric connectedness;
normality, integrality and local Noetherianity follow from its finite étale
map to the original normal model. Both original projection squares are retained.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry EtaleFundamentalGroups

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
  [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
  {X U : Scheme.{u}} (c : X ⟶ Spec (.of k)) (j : U ⟶ X)

/-- The actual finite constant-field pullback of the compactification. -/
abbrev constantBaseChangeCompactification : Scheme.{u} :=
  ((pullback c).obj (originalConstantFieldCover k E)).left

/-- The original structural map of the pullback to its actual constant field. -/
abbrev constantBaseChangeCompactificationStructure :
    constantBaseChangeCompactification k E c ⟶ Spec (.of E) :=
  Limits.pullback.fst (originalConstantFieldCover k E).hom c

/-- The original coefficient extension of the open immersion. Its domain is
the literal constant cover used by the arithmetic covering-group comparison. -/
abbrev constantBaseChangeOpen :
    ((pullback (j ≫ c)).obj (originalConstantFieldCover k E)).left ⟶
      constantBaseChangeCompactification k E c :=
  coefficientModelMap (originalConstantFieldCover k E).hom c j

/-- The open map retains the original structural map to `Spec E`. -/
@[reassoc]
theorem constantBaseChangeOpen_structure :
    constantBaseChangeOpen k E c j ≫ constantBaseChangeCompactificationStructure k E c =
      Limits.pullback.fst (originalConstantFieldCover k E).hom (j ≫ c) :=
  Limits.pullback.lift_fst _ _ _

/-- The open map also retains the original projection to the compactification. -/
@[reassoc]
theorem constantBaseChangeOpen_original :
    constantBaseChangeOpen k E c j ≫
        ((pullback c).obj (originalConstantFieldCover k E)).hom =
      ((pullback (j ≫ c)).obj (originalConstantFieldCover k E)).hom ≫ j :=
  Limits.pullback.lift_snd _ _ _

instance constantBaseChangeOpen_isOpenImmersion [IsOpenImmersion j] :
    IsOpenImmersion (constantBaseChangeOpen k E c j) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (show MorphismProperty Scheme from IsOpenImmersion))
    (coefficientBaseChange_isPullback (originalConstantFieldCover k E).hom c j).flip
    (inferInstance : IsOpenImmersion j)

instance constantBaseChangeOpen_quasiCompact [QuasiCompact j] :
    QuasiCompact (constantBaseChangeOpen k E c j) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (show MorphismProperty Scheme from @QuasiCompact))
    (coefficientBaseChange_isPullback (originalConstantFieldCover k E).hom c j).flip
    (inferInstance : QuasiCompact j)

instance constantBaseChangeOpen_quasiSeparated [QuasiSeparated j] :
    QuasiSeparated (constantBaseChangeOpen k E c j) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (show MorphismProperty Scheme from @QuasiSeparated))
    (coefficientBaseChange_isPullback (originalConstantFieldCover k E).hom c j).flip
    (inferInstance : QuasiSeparated j)

instance constantBaseChangeCompactification_isProper [IsProper c] :
    IsProper (constantBaseChangeCompactificationStructure k E c) :=
  inferInstanceAs (IsProper (Limits.pullback.fst (originalConstantFieldCover k E).hom c))

instance constantBaseChangeCover_isConnected [GeometricallyConnected c] :
    IsConnected ((pullback c).obj (originalConstantFieldCover k E)) := by
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton c
  have : ConnectedSpace (constantBaseChangeCompactification k E c) :=
    GeometricallyConnected.geometrically_connectedSpace
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      (Limits.pullback.snd (originalConstantFieldCover k E).hom c)
      (Limits.pullback.fst (originalConstantFieldCover k E).hom c)
      (IsPullback.of_hasPullback (originalConstantFieldCover k E).hom c).flip
  exact isConnected_of_connectedSpace_left _

instance constantBaseChangeCompactification_isIntegral
    [IsIntegral X] [IsNormalIntegral X] [GeometricallyConnected c] :
    IsIntegral (constantBaseChangeCompactification k E c) :=
  isIntegral_left_of_isConnected_finiteEtale ((pullback c).obj (originalConstantFieldCover k E))

instance constantBaseChangeCompactification_isNormalIntegral
    [IsIntegral X] [IsNormalIntegral X] [GeometricallyConnected c] :
    IsNormalIntegral (constantBaseChangeCompactification k E c) :=
  isNormalIntegral_left_of_isConnected_finiteEtale
    ((pullback c).obj (originalConstantFieldCover k E))

instance constantBaseChangeCompactification_isLocallyNoetherian [IsLocallyNoetherian X] :
    IsLocallyNoetherian (constantBaseChangeCompactification k E c) :=
  isLocallyNoetherian_left_finiteEtale ((pullback c).obj (originalConstantFieldCover k E))

end AlgebraicGeometry.FiniteEtale
