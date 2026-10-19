/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineDensity
import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveLineSmooth
import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
import Nyll.SchemeTheory.Normalization.Normal
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Geometry of the actual rational-configuration open

All properties concern the original open and its literal coefficient pullback.
Integrality follows from their actual open immersions into projective lines.
Smoothness supplies normal stalks and local Noetherianity. Properness of the
projective line and quasi-compactness of open immersions into a locally
Noetherian scheme supply compactness. No replacement scheme or additional
geometric hypothesis is introduced.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

section Arithmetic

variable (k : Type) [Field k]
  (s : Finset (Projectivization k (k × k)))

/-- The actual arithmetic open is smooth over its original coefficient field. -/
instance rationalConfigurationOpen_smooth :
    Smooth ((rationalConfigurationOpen s).ι ≫ π k 1) := by
  let : SmoothOfRelativeDimension 1 (π k 1) :=
    projectiveLine_smoothOfRelativeDimension k
  let : Smooth (π k 1) := SmoothOfRelativeDimension.smooth 1 (π k 1)
  infer_instance

instance rationalConfigurationOpen_isLocallyNoetherian :
    IsLocallyNoetherian (rationalConfigurationOpen s : Scheme) :=
  LocallyOfFiniteType.isLocallyNoetherian ((rationalConfigurationOpen s).ι ≫ π k 1)

/-- The inclusion is quasi-compact because its actual target is locally Noetherian. -/
instance rationalConfigurationOpen_quasiCompact :
    QuasiCompact (rationalConfigurationOpen s).ι := by
  let : SmoothOfRelativeDimension 1 (π k 1) :=
    projectiveLine_smoothOfRelativeDimension k
  let : Smooth (π k 1) := SmoothOfRelativeDimension.smooth 1 (π k 1)
  let : IsLocallyNoetherian (projectiveLineScheme k) :=
    LocallyOfFiniteType.isLocallyNoetherian (π k 1)
  infer_instance

instance rationalConfigurationOpen_quasiSeparated :
    QuasiSeparated (rationalConfigurationOpen s).ι := by
  infer_instance

instance rationalConfigurationOpen_compactSpace :
    CompactSpace (rationalConfigurationOpen s : Scheme) := by
  let : CompactSpace (projectiveLineScheme k) :=
    QuasiCompact.compactSpace_of_compactSpace (π k 1)
  exact QuasiCompact.compactSpace_of_compactSpace (rationalConfigurationOpen s).ι

instance rationalConfigurationOpen_quasiSeparatedSpace :
    QuasiSeparatedSpace (rationalConfigurationOpen s : Scheme) := by
  infer_instance

variable [Infinite k]

instance rationalConfigurationOpen_isIntegral :
    IsIntegral (rationalConfigurationOpen s : Scheme) := by
  let : IsIntegral (projectiveLineScheme k) := projectiveSpace_isIntegral k 1
  let : Nonempty (rationalConfigurationOpen s : Scheme) :=
    rationalConfigurationOpen_nonempty k s
  exact isIntegral_of_isOpenImmersion (rationalConfigurationOpen s).ι

instance rationalConfigurationOpen_isNormalIntegral :
    IsNormalIntegral (rationalConfigurationOpen s : Scheme) := by
  let : IsIntegrallyClosed Γ(Spec (.of k), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  exact IsNormalIntegral.of_stalks (rationalConfigurationOpen s : Scheme)
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk
      ((rationalConfigurationOpen s).ι ≫ π k 1) x).2)

instance rationalConfigurationOpen_connectedSpace :
    ConnectedSpace (rationalConfigurationOpen s : Scheme) := by
  infer_instance

end Arithmetic

section Geometric

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]
  (s : Finset (Projectivization k (k × k)))

/-- The original coefficient projection of the literal pullback is smooth. -/
instance rationalConfigurationBaseChange_smooth :
    Smooth (Limits.pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)) := by
  infer_instance

instance rationalConfigurationBaseChange_isLocallyNoetherian :
    IsLocallyNoetherian (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) :=
  LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst
    (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    ((rationalConfigurationOpen s).ι ≫ π k 1))

/-- The canonical geometric chart is quasi-compact, with no chart hypothesis. -/
instance rationalConfigurationBaseChangeChart_quasiCompact :
    QuasiCompact (rationalConfigurationBaseChangeChart k κ s) := by
  let : SmoothOfRelativeDimension 1 (π κ 1) :=
    projectiveLine_smoothOfRelativeDimension κ
  let : Smooth (π κ 1) := SmoothOfRelativeDimension.smooth 1 (π κ 1)
  let : IsLocallyNoetherian (projectiveLineScheme κ) :=
    LocallyOfFiniteType.isLocallyNoetherian (π κ 1)
  infer_instance

instance rationalConfigurationBaseChangeChart_quasiSeparated :
    QuasiSeparated (rationalConfigurationBaseChangeChart k κ s) := by
  infer_instance

instance rationalConfigurationBaseChange_compactSpace :
    CompactSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) := by
  let : CompactSpace (projectiveLineScheme κ) :=
    QuasiCompact.compactSpace_of_compactSpace (π κ 1)
  exact QuasiCompact.compactSpace_of_compactSpace
    (rationalConfigurationBaseChangeChart k κ s)

instance rationalConfigurationBaseChange_quasiSeparatedSpace :
    QuasiSeparatedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) := by
  infer_instance

variable [Infinite k]

instance rationalConfigurationBaseChange_isIntegral :
    IsIntegral (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) := by
  let : IsIntegral (projectiveLineScheme κ) := projectiveSpace_isIntegral κ 1
  let : Nonempty (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) :=
    rationalConfigurationBaseChange_nonempty k κ s
  exact isIntegral_of_isOpenImmersion (rationalConfigurationBaseChangeChart k κ s)

instance rationalConfigurationBaseChange_isNormalIntegral :
    IsNormalIntegral (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) := by
  let : IsIntegrallyClosed Γ(Spec (.of κ), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of κ)).symm.commRingCatIsoToRingEquiv
  exact IsNormalIntegral.of_stalks
    (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme)
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk
      (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) x).2)

instance rationalConfigurationBaseChange_connectedSpace :
    ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) := by
  infer_instance

end Geometric

end AlgebraicGeometry.ProjSpace
