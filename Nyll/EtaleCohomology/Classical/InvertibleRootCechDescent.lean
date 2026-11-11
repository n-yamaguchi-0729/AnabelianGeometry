/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.EtaleCohomology.Classical.CartierTensorRootVanishing
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupExtensionRepresentatives
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionCohomologyComparison
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectNaturality
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.InvertibleCycleClass
public import Nyll.EtaleCohomology.Classical.InvertibleFiniteEtalePullback
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.RootExtensionDescent
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Descent of the native class of a specified invertible root

An actual invertible module on an integral étale cover gives a native
H¹(Gm) class on that cover and hence a class in the original cohomology
presheaf. Its actual tensor-power isomorphism identifies its multiple
with the restriction of the original signed Cartier class.

Representing these same classes by short extensions supplies the
root-sensitive three-by-three construction. Its resulting class on
the covering kernel retains the original root through its coefficient
inclusion, and its transgression is the negative of the original signed
Cartier cycle class.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite Abelian

namespace EtaleCohomology

private theorem ext_comp_mk₀_nsmul_id
    {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]
    {A B : C} (β : Ext.{u} A B 1) (n : ℕ) :
    β.comp (Ext.mk₀ (n • 𝟙 B)) (add_zero 1) = n • β := by
  change ((Abelian.extFunctorObj A 1).map (n • 𝟙 B)) β = n • β
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

variable {X : Scheme.{u}} (V : X.Etale) [IsIntegral V.left]
  {L : V.left.Modules} (hL : Scheme.Modules.IsInvertible L)

/-- The class of the specified original invertible module, regarded
as a section of the original cohomology presheaf on the ambient site. -/
def invertibleModuleCohomologyPresheafH1 :
    Sheaf.H'.{u} (etaleMultiplicativeGroupSheaf X) 1 V :=
  (etaleCohomologyPresheafRestrictionEquiv V (etaleMultiplicativeGroupSheaf X) 1).symm
    (Sheaf.H.map (etaleRestrictionMultiplicativeGroupIso V.hom).inv 1
      (invertibleModuleMultiplicativeGroupH1 (X := V.left) hL))

/-- Restricting the original root class to an integral finite étale
object gives the native class of the actual pulled-back root module.
Both sides lie in the original ambient cohomology presheaf. -/
theorem invertibleModuleCohomologyPresheafH1_finiteEtale_restriction
    [IsNormalIntegral V.left] {W : X.Etale} (g : W ⟶ V)
    [IsFinite g.left] [IsIntegral W.left] :
    ((etaleMultiplicativeGroupSheaf X).cohomologyPresheaf 1).map g.op
        (invertibleModuleCohomologyPresheafH1 V hL) =
      invertibleModuleCohomologyPresheafH1 W (hL.pullback g.left) := by
  have : IsFiniteEtale g.left := IsFiniteEtale.mk
  let B : FiniteEtale V.left := FiniteEtale.mk g.left
  have : ConnectedSpace B.left := inferInstanceAs (ConnectedSpace W.left)
  have : CategoryTheory.PreGaloisCategory.IsConnected B :=
    FiniteEtale.isConnected_of_connectedSpace_left B
  have hn := invertibleModuleMultiplicativeGroupH1_finiteEtalePullback
    (X := V.left) B hL
  let F := etaleMultiplicativeGroupSheaf X
  let eV := etaleCohomologyPresheafRestrictionEquiv V F 1
  let eW := etaleCohomologyPresheafRestrictionEquiv W F 1
  let uV := etaleRestrictionMultiplicativeGroupIso V.hom
  let uW := etaleRestrictionMultiplicativeGroupIso W.hom
  apply eW.injective
  apply ((Sheaf.functorH W.left.smallEtaleTopology 1).mapIso uW).addCommGroupIsoToAddEquiv.injective
  change Sheaf.H.map uW.hom 1
      (eW ((F.cohomologyPresheaf 1).map g.op (invertibleModuleCohomologyPresheafH1 V hL))) =
    Sheaf.H.map uW.hom 1 (eW (invertibleModuleCohomologyPresheafH1 W (hL.pullback g.left)))
  rw [etaleCohomologyPresheafRestrictionEquiv_units_object_restriction]
  change etaleMultiplicativeGroupCohomologyPullback g.left 1
      (Sheaf.H.map uV.hom 1
        (eV (eV.symm (Sheaf.H.map uV.inv 1
          (invertibleModuleMultiplicativeGroupH1 (X := V.left) hL))))) =
    Sheaf.H.map uW.hom 1
      (eW (eW.symm (Sheaf.H.map uW.inv 1
        (invertibleModuleMultiplicativeGroupH1 (X := W.left) (hL.pullback g.left)))))
  rw [eV.apply_symm_apply, eW.apply_symm_apply,
    ← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply,
    ← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply]
  exact hn

variable [IsIntegral X] {T : X.Etale} (hT : IsTerminal T) (f : V ⟶ T)
  (n : ℕ) (D E : Scheme.EffectiveCartierDivisor X)
  (e : (Scheme.Modules.pullback V.hom).obj (D.1.invModule ⊗ E.1.module) ≅ L.tensorPow n)

include e in
/-- The actual tensor root supplies the root equation on the original
covering source in Ext. The comparison uses the original native
Cartier pullback and the original restriction equivalence. -/
theorem invertibleModuleCohomologyPresheafH1_nsmul_of_tensorPowIso :
    n • invertibleModuleCohomologyPresheafH1 V hL =
      (Ext.mk₀ (abelianCechUnitAugmentation X.smallEtaleTopology hT f)).comp
        (effectiveCartierMultiplicativeGroupH1 D -
          effectiveCartierMultiplicativeGroupH1 E) (zero_add 1) := by
  let F := etaleMultiplicativeGroupSheaf X
  let α := effectiveCartierMultiplicativeGroupH1 D -
    effectiveCartierMultiplicativeGroupH1 E
  let r := etaleCohomologyPresheafRestrictionEquiv V F 1
  let v := etaleRestrictionMultiplicativeGroupIso V.hom
  have hrestriction :
      r ((Ext.mk₀ (abelianCechUnitAugmentation X.smallEtaleTopology hT f)).comp
        α (zero_add 1)) = etaleAbelianRestrictionCohomologyPullback V.hom F 1 α := by
    rw [abelianCechUnitAugmentation, ← Ext.mk₀_comp_mk₀_assoc]
    exact etaleCohomologyPresheafRestrictionEquiv_terminal_restriction V hT f F 1 α
  apply r.injective
  apply ((Sheaf.functorH V.left.smallEtaleTopology 1).mapIso v).addCommGroupIsoToAddEquiv.injective
  change Sheaf.H.map v.hom 1 (r (n • invertibleModuleCohomologyPresheafH1 V hL)) =
    Sheaf.H.map v.hom 1
      (r ((Ext.mk₀ (abelianCechUnitAugmentation X.smallEtaleTopology hT f)).comp
        α (zero_add 1)))
  rw [map_nsmul, map_nsmul, invertibleModuleCohomologyPresheafH1,
    r.apply_symm_apply, ← Sheaf.H.map_comp_apply, Iso.inv_hom_id,
    Sheaf.H.map_id_apply, hrestriction]
  exact (signedCartierMultiplicativeGroupH1_pullback_eq_nsmul_of_tensorPowIso
    (X := X) (Y := V.left) V.hom n D E L hL e).symm.trans
      (etaleMultiplicativeGroupCohomologyPullback_restriction V.hom 1 α)

include e in
/-- A specified tensor root constructs a class on the original first
covering kernel. Its original coefficient image is the restriction of
that same root, and its original transgression recovers the signed
Cartier cycle class with the three-by-three sign. -/
theorem signedCartierRoot_exists_cech_descent
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    let A := abelianCechAugmentationSequence X.smallEtaleTopology hT f
    let hA := abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf
    ∃ a : Ext.{u} A.X₁ (etaleRootsOfUnitySheaf X n) 1,
      a.comp (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower X n))) (add_zero 1) =
        (Ext.mk₀ A.f).comp (invertibleModuleCohomologyPresheafH1 V hL) (zero_add 1) ∧
      hA.extClass.comp a (show 1 + 1 = 2 from rfl) +
        (effectiveCartierCycleClass D hn hnX - effectiveCartierCycleClass E hn hnX) = 0 := by
  intro A hA
  let S := etaleKummerComplex X n
  let hS := etaleKummerComplex_shortExact X hn hnX
  let α : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 :=
    effectiveCartierMultiplicativeGroupH1 D - effectiveCartierMultiplicativeGroupH1 E
  let β := invertibleModuleCohomologyPresheafH1 V hL
  have hpower : β.comp (Ext.mk₀ S.g) (add_zero 1) = n • β := by
    change β.comp (Ext.mk₀ (n • 𝟙 (etaleMultiplicativeGroupSheaf X)))
      (add_zero 1) = n • β
    exact ext_comp_mk₀_nsmul_id β n
  obtain ⟨Eβ, iβ, pβ, zβ, hβ, hβeq⟩ := ext_one_exists_shortExact β
  obtain ⟨Eα, iα, pα, zα, hα, hαeq⟩ := ext_one_exists_shortExact α
  have hroot : hβ.extClass.comp (Ext.mk₀ S.g) (add_zero 1) =
      (Ext.mk₀ A.g).comp hα.extClass (zero_add 1) := by
    rw [hβeq, hαeq, hpower]
    exact invertibleModuleCohomologyPresheafH1_nsmul_of_tensorPowIso V hL hT f n D E e
  obtain ⟨M, i, p, z, hM, j, m, _, _, _, _, _, hcoeff, htrans⟩ :=
    exists_rootExtension_descent S A hS hA iβ pβ zβ hβ iα pα zα hα hroot
  refine ⟨hM.extClass, ?_, ?_⟩
  · simpa only [hβeq] using hcoeff
  · rw [hαeq] at htrans
    change hA.extClass.comp hM.extClass (show 1 + 1 = 2 from rfl) +
      Sheaf.H.δ hS 1 2 rfl α = 0 at htrans
    simpa only [α, map_sub, effectiveCartierCycleClass] using htrans

end EtaleCohomology
