/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.SpecFlatBaseChangeSections

/-!
# The canonical tensor-to-sections map before imposing quasi-compactness

The map exists for every scheme over an affine base. On quasi-compact,
quasi-separated schemes with flat base change it is the existing
section equivalence. This distinction permits passage to affine
refinements in the actual geometric-stalk diagram.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The actual two maps to pullback sections agree on the original base ring. -/
theorem specPullbackSections_comm :
    CommRingCat.ofHom (algebraMap R A) ≫
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) ≫
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have h :
      g.appTop ≫ (pullback.snd f g).appTop =
        f.appTop ≫ (pullback.fst f g).appTop :=
    (Scheme.Hom.comp_appTop (pullback.snd f g) g).symm.trans
      ((congrArg (fun k : pullback f g ⟶ Spec (CommRingCat.of R) => k.appTop)
        (pullback.condition (f := f) (g := g)).symm).trans
          (Scheme.Hom.comp_appTop (pullback.fst f g) f))
  rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc, h,
    ← Category.assoc]

/-- The canonical map from the tensor product to actual pullback sections.
No quasi-compactness or separatedness is needed to define it. -/
def specPullbackSectionsTensorMap :
    let : Algebra R Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    CommRingCat.of (A ⊗[R] Γ(X, ⊤)) ⟶
      Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))), ⊤) := by
  intro hRX
  exact (CommRingCat.isPushout_tensorProduct R A Γ(X, ⊤)).desc
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop)
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop
    (specPullbackSections_comm (A := A) f)

/-- On the left tensor factor, the canonical map is the actual base map. -/
theorem specPullbackSectionsTensorMap_left :
    let : Algebra R Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
        specPullbackSectionsTensorMap (A := A) f =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop := by
  intro hRX
  exact (CommRingCat.isPushout_tensorProduct R A Γ(X, ⊤)).inl_desc _ _ _

/-- On the right tensor factor, the canonical map is the actual restriction. -/
theorem specPullbackSectionsTensorMap_right :
    let : Algebra R Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫
        specPullbackSectionsTensorMap (A := A) f =
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop := by
  intro hRX
  exact (CommRingCat.isPushout_tensorProduct R A Γ(X, ⊤)).inr_desc _ _ _

variable [Module.Flat R A] [QuasiCompact f] [QuasiSeparated f]

/-- Where flat base change on sections applies, the canonical map agrees
with the already constructed equivalence. -/
theorem specPullbackSectionsTensorMap_eq_equiv :
    let : Algebra R Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    let : Algebra A Γ(pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap R A))), ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop).hom.toAlgebra
    specPullbackSectionsTensorMap (A := A) f =
      CommRingCat.ofHom (specPullbackSectionsTensorEquiv (A := A) f).toRingHom := by
  intro hRX hAP
  apply (CommRingCat.isPushout_tensorProduct R A Γ(X, ⊤)).hom_ext
  · rw [specPullbackSectionsTensorMap_left]
    apply CommRingCat.hom_ext
    ext a
    exact ((specPullbackSectionsTensorEquiv (A := A) f).commutes a).symm
  · rw [specPullbackSectionsTensorMap_right]
    apply CommRingCat.hom_ext
    ext x
    exact (specPullbackSectionsTensorEquiv_one_tmul (A := A) f x).symm

/-- The canonical map is bijective under the existing flat base-change hypotheses. -/
theorem specPullbackSectionsTensorMap_bijective :
    let : Algebra R Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    Function.Bijective (specPullbackSectionsTensorMap (A := A) f) := by
  intro hRX
  let : Algebra A Γ(pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap R A))), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop).hom.toAlgebra
  rw [specPullbackSectionsTensorMap_eq_equiv]
  exact (specPullbackSectionsTensorEquiv (A := A) f).bijective

end AlgebraicGeometry
