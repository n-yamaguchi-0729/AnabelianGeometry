/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.FieldMap
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBoundary
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # The actual rational configuration after extension of constants

Extending each homogeneous coordinate gives the exact new puncture set.
The scalar extension of the original open is isomorphic to this new open,
with the actual ambient chart and coefficient projection retained.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.ProjectiveLine

variable (k E : Type) [Field k] [Field E] [Algebra k E]

/-- Extend the coordinates of every puncture without identifying any labels. -/
def configurationScalarExtension (s : Finset (Projectivization k (k × k))) :
    Finset (Projectivization E (E × E)) :=
  s.map ⟨projectiveFieldMap (algebraMap k E), projectiveFieldMap_injective _⟩

theorem configurationScalarExtension_card (s : Finset (Projectivization k (k × k))) :
    (configurationScalarExtension k E s).card = s.card := Finset.card_map _

/-- The projective coordinate extension is the actual geometric puncture point. -/
theorem projectiveRationalPoint_projectiveFieldMap
    (p : Projectivization k (k × k)) :
    projectiveRationalPoint (projectiveFieldMap (algebraMap k E) p) =
      rationalConfigurationGeometricPoint k E p := by
  exact (congrArg
    (fun q => projectiveRationalPoint (projectiveFieldMap (algebraMap k E) q))
    p.mk_rep.symm).trans
      ((congrArg projectiveRationalPoint
        (projectiveFieldMap_mk (algebraMap k E) p.rep p.rep_nonzero)).trans
          (projectiveRationalPoint_mk _ _))

theorem rationalConfiguration_scalarExtension_range
    (s : Finset (Projectivization k (k × k))) :
    Set.range (rationalConfigurationBaseChangeChart k E s) =
      Set.range (rationalConfigurationOpen (configurationScalarExtension k E s)).ι := by
  classical
  ext x
  rw [mem_range_rationalConfigurationBaseChangeChart_iff]
  constructor
  · intro hx
    have hxopen : x ∈ rationalConfigurationOpen (configurationScalarExtension k E s) := by
      apply (mem_rationalConfigurationOpen_iff _ x).mpr
      intro p hp hxp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hp
      exact hx a ha (hxp.trans (projectiveRationalPoint_projectiveFieldMap k E a))
    exact ⟨⟨x, hxopen⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    intro a ha hya
    have h := (mem_rationalConfigurationOpen_iff _ y.val).mp y.property
    exact h (projectiveFieldMap (algebraMap k E) a)
      (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
      (hya.trans (projectiveRationalPoint_projectiveFieldMap k E a).symm)

/-- Scalar extension of the original open, using its unchanged ambient chart. -/
def rationalConfigurationScalarExtensionIso
    (s : Finset (Projectivization k (k × k))) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) ≅
      (rationalConfigurationOpen (configurationScalarExtension k E s) : Scheme) :=
  IsOpenImmersion.isoOfRangeEq (rationalConfigurationBaseChangeChart k E s)
    (rationalConfigurationOpen (configurationScalarExtension k E s)).ι
    (rationalConfiguration_scalarExtension_range k E s)

theorem rationalConfigurationScalarExtensionIso_hom_chart
    (s : Finset (Projectivization k (k × k))) :
    (rationalConfigurationScalarExtensionIso k E s).hom ≫
        (rationalConfigurationOpen (configurationScalarExtension k E s)).ι =
      rationalConfigurationBaseChangeChart k E s :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem rationalConfigurationScalarExtensionIso_hom_base
    (s : Finset (Projectivization k (k × k))) :
    (rationalConfigurationScalarExtensionIso k E s).hom ≫
        ((rationalConfigurationOpen (configurationScalarExtension k E s)).ι ≫ π E 1) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) := by
  rw [← Category.assoc, rationalConfigurationScalarExtensionIso_hom_chart]
  exact rationalConfigurationBaseChangeChart_comp_π k E s

end AnabelianGeometry.ProjectiveLine
