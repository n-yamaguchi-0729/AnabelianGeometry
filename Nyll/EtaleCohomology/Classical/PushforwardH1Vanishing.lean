/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.PushforwardGlobalSections
public import Nyll.EtaleCohomology.Classical.CohomologyPresheafBoundary
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Degree-one vanishing for direct images

Vanishing of the degree-one cohomology presheaf after direct image follows
from the actual injective presentation and the comparison of its cokernel.
-/

@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite
namespace EtaleCohomology

/-- The degree-one vanishing part of the low-degree direct-image
comparison. It follows from the actual injective presentation and the
monomorphism from its pushed-forward cokernel to the direct image of
the original cokernel. -/
theorem etalePushforward_cohomologyPresheaf_one_eq_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (h : ∀ a : Sheaf.H'.{u} F 1 ((etaleBaseChange f).obj V), a = 0)
    (a : Sheaf.H'.{u} ((etaleAbelianPushforward f).obj F) 1 V) : a = 0 := by
  let G := etaleAbelianPushforward f
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
  have : Mono S.f := hS.mono_f
  have hGS : (S.map G).Exact :=
    hS.exact.map_of_mono_of_preservesKernel G hS.mono_f inferInstance
  let T := ShortComplex.mk (G.map S.f) (cokernel.π (G.map S.f))
    (cokernel.condition (G.map S.f))
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel (G.map S.f) }
  have : Injective T.X₂ := G.injective_obj S.X₂
  let d : T.X₃ ⟶ G.obj S.X₃ :=
    cokernel.desc (G.map S.f) (G.map S.g) (S.map G).zero
  have : Mono d := hGS.mono_cokernelDesc
  obtain ⟨q, hq⟩ := cohomologyPresheafSectionBoundary_surjective Y T hT V a
  let W := (etaleBaseChange f).obj V
  let s : S.X₃.obj.obj (op W) := d.hom.app (op V) q
  obtain ⟨t, ht⟩ :=
    (cohomologyPresheafSectionBoundary_eq_zero_iff X S hS W s).mp
      (h (cohomologyPresheafSectionBoundary X S hS W s))
  have ht' : T.g.hom.app (op V) t = q := by
    apply (AddCommGrpCat.mono_iff_injective (d.hom.app (op V))).mp inferInstance
    change ((T.g ≫ d).hom.app (op V)) t = d.hom.app (op V) q
    have hd : T.g ≫ d = G.map S.g := cokernel.π_desc _ _ _
    rw [hd]
    exact ht
  rw [← hq]
  exact (cohomologyPresheafSectionBoundary_eq_zero_iff Y T hT V q).mpr ⟨t, ht'⟩

/-- The degree-two vanishing part of the low-degree direct-image
comparison. Degree-one source vanishing is required on every étale object;
degree two is only required at the base change of the object in question. -/
theorem etalePushforward_cohomologyPresheaf_two_eq_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (h1 : ∀ W : X.Etale, ∀ a : Sheaf.H'.{u} F 1 W, a = 0)
    (h2 : ∀ a : Sheaf.H'.{u} F 2 ((etaleBaseChange f).obj V), a = 0)
    (a : Sheaf.H'.{u} ((etaleAbelianPushforward f).obj F) 2 V) : a = 0 := by
  let G := etaleAbelianPushforward f
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
  have : Mono S.f := hS.mono_f
  have hepiApp (W : Y.Etaleᵒᵖ) : Epi ((G.map S.g).hom.app W) := by
    apply ConcreteCategory.epi_of_surjective
    intro q
    exact (cohomologyPresheafSectionBoundary_eq_zero_iff X S hS
      ((etaleBaseChange f).obj W.unop) q).mp
        (h1 _ (cohomologyPresheafSectionBoundary X S hS
          ((etaleBaseChange f).obj W.unop) q))
  have hPresheaf : Epi ((sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
      (G.map S.g)) := (NatTrans.epi_iff_epi_app _).mpr hepiApp
  have hEpiMapped : Epi (G.map S.g) :=
    (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).epi_of_epi_map
      hPresheaf
  have : PreservesLimitsOfSize.{0, 0} G :=
    (etaleAbelianPullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
  have hMonoMapped : Mono (G.map S.f) := preserves_mono_of_preservesLimit G S.f
  have hGS : (S.map G).ShortExact :=
    { exact := hS.exact.map_of_mono_of_preservesKernel G hS.mono_f inferInstance
      mono_f := hMonoMapped
      epi_g := hEpiMapped }
  have : Mono (S.map G).f := hGS.mono_f
  have : Epi (S.map G).g := hGS.epi_g
  have : Injective (S.map G).X₂ := G.injective_obj S.X₂
  let P := (freeAbelianSheafYoneda Y.smallEtaleTopology).obj V
  obtain ⟨b, hb⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₁ P hGS a
    (CategoryTheory.Abelian.Ext.eq_zero_of_injective _) (n₀ := 1) rfl
  have hQ (c : Sheaf.H'.{u} S.X₃ 1 ((etaleBaseChange f).obj V)) : c = 0 := by
    let Q := (freeAbelianSheafYoneda X.smallEtaleTopology).obj
      ((etaleBaseChange f).obj V)
    obtain ⟨d, hd⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₃ Q hS c rfl
      (h2 (c.comp hS.extClass rfl))
    rw [CategoryTheory.Abelian.Ext.eq_zero_of_injective d,
      CategoryTheory.Abelian.Ext.zero_comp] at hd
    exact hd.symm
  have hb0 := etalePushforward_cohomologyPresheaf_one_eq_zero f S.X₃ V hQ b
  rw [hb0] at hb
  change (0 : CategoryTheory.Abelian.Ext P (S.map G).X₃ 1).comp
    hGS.extClass (by norm_num) = a at hb
  rw [CategoryTheory.Abelian.Ext.zero_comp] at hb
  exact hb.symm

end EtaleCohomology
