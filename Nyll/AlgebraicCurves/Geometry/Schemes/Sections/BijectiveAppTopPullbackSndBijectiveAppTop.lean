/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.BaseChange.AffineGlobalSections

/-!
# bijective app Top pullback snd of bijective app Top
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.bijective_appTop_pullback_snd_of_bijective_appTop

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct in
theorem _root_.AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (A : Type u) [CommRing A] [Algebra k A] :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom :=
  FBC0.bijective_appTop_snd fX hX A
end AlgebraicCurves.Geometry.Schemes.Proofs.bijective_appTop_pullback_snd_of_bijective_appTop
end ProofImplementation
