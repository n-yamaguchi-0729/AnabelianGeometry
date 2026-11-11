/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_perfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantSeparatingParameter
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.SeparatingTranscendental

/-!
# Exists finite Dimensional is Separable adjoin of constant Field Extension of perfect Field
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs
namespace Exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_perfectField

open IntermediateField

end Exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_perfectField
end AlgebraicCurves.FunctionFields.Proofs

namespace AlgebraicCurve



open _root_.AlgebraicCurves.FunctionFields.Proofs in
open Exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_perfectField in
open IntermediateField in
theorem exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_perfectField
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [PerfectField K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (_hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    ∃ t' : F', FiniteDimensional (IntermediateField.adjoin K' ({t'} : Set F')) F' ∧
      Algebra.IsSeparable (IntermediateField.adjoin K' ({t'} : Set F')) F' := by
  classical
  obtain ⟨x, hx, hxfin⟩ := hfg
  obtain ⟨t, _ht_trans, ht_fin, ht_sep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField hx hxfin
  have hfin : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := ht_fin
  have hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := ht_sep
  exact ⟨algebraMap F F' t, finite_separable_adjoin_constantBaseChange
    (K := K) (F := F) (K' := K') (F' := F') t hgen⟩
end AlgebraicCurve
end ProofImplementation
