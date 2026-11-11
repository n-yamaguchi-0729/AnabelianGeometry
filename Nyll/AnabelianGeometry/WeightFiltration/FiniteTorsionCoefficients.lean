/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.FiniteTorsion
public import Nyll.AnabelianGeometry.WeightFiltration.TorsionCoefficientMaps
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.LocalRing.Module
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Finite torsion over field-valued coefficients

At every invertible index the actual torsion kernel is finite étale over
the local base. Its section algebra is finite free, hence has only finitely
many algebra maps to a field. No algebraic-closedness assumption is needed.
-/

@[expose] public section

/- The public theorem `GoodReductionJacobian.RelativeGroupLaw.finite_torsionLevel_of_isUnit`
is supplied by the lower finite-torsion owner imported above. -/
