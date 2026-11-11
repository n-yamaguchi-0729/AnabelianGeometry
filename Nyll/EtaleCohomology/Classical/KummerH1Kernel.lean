/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.KummerPowerTransition
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Original degree-one Kummer maps and torsion

The original coefficient inclusion maps H¹ of the actual Kummer kernel
onto the n-torsion subgroup of the original H¹(Gm). If the original
global-unit power map is surjective, the preceding connecting map
vanishes and this actual inclusion is an isomorphism onto that subgroup.
The original exponent transition is multiplication on H¹(Gm).
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

/-- The original power morphism acts as integer multiplication on
the actual cohomology of the original multiplicative-group sheaf. -/
theorem etaleMultiplicativeGroupPower_cohomology_apply
    (X : Scheme.{u}) (n i : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) i) :
    Sheaf.H.map (etaleMultiplicativeGroupPower X n) i a = n • a := by
  change ((Sheaf.functorH X.smallEtaleTopology i).map
    (n • 𝟙 (etaleMultiplicativeGroupSheaf X))) a = n • a
  have hm : ((Sheaf.functorH X.smallEtaleTopology i).map
      (n • 𝟙 (etaleMultiplicativeGroupSheaf X))) a =
        (n • 𝟙 ((Sheaf.functorH X.smallEtaleTopology i).obj
          (etaleMultiplicativeGroupSheaf X))) a := by
    simp only [(Sheaf.functorH X.smallEtaleTopology i).map_nsmul,
      (Sheaf.functorH X.smallEtaleTopology i).map_id]
  have hv : (n • 𝟙 ((Sheaf.functorH X.smallEtaleTopology i).obj
      (etaleMultiplicativeGroupSheaf X))) a = n • a := rfl
  exact hm.trans hv

/-- The original Kummer-kernel inclusion on actual degree-one
cohomology, with its original multiplicative-group target. -/
def etaleRootsOfUnityH1ToMultiplicativeGroup (X : Scheme.{u}) (n : ℕ) :
    Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 1 →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 :=
  Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower X n)) 1

/-- Every original degree-one Kummer class maps to actual n-torsion. -/
theorem etaleRootsOfUnityH1ToMultiplicativeGroup_nsmul
    (X : Scheme.{u}) (n : ℕ)
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 1) :
    n • etaleRootsOfUnityH1ToMultiplicativeGroup X n a = 0 := by
  rw [← etaleMultiplicativeGroupPower_cohomology_apply X n 1]
  change Sheaf.H.map (etaleMultiplicativeGroupPower X n) 1
    (Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower X n)) 1 a) = 0
  rw [← Sheaf.H.map_comp_apply, kernel.condition, Sheaf.H.map_apply,
    Ext.mk₀_zero, Ext.comp_zero]

/-- The original Kummer inclusion, restricted to its actual torsion target. -/
def etaleKummerH1ToPowerKernel (X : Scheme.{u}) (n : ℕ) :
    Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 1 →+
      (nsmulAddMonoidHom n : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 →+
        Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1).ker :=
  (etaleRootsOfUnityH1ToMultiplicativeGroup X n).codRestrict _
    (etaleRootsOfUnityH1ToMultiplicativeGroup_nsmul X n)

/-- Exactness makes the actual coefficient inclusion surjective onto
the original n-torsion subgroup. -/
theorem etaleKummerH1ToPowerKernel_surjective
    (X : Scheme.{u}) {n : ℕ} (hn : 0 < n)
    (hnX : IsUnit (n : Γ(X, ⊤))) :
    Function.Surjective (etaleKummerH1ToPowerKernel X n) := by
  rintro ⟨b, hb⟩
  have hpower : Sheaf.H.map (etaleMultiplicativeGroupPower X n) 1 b = 0 :=
    (etaleMultiplicativeGroupPower_cohomology_apply X n 1 b).trans hb
  obtain ⟨a, ha⟩ := Sheaf.H.longSequence_exact₂
    (etaleKummerComplex_shortExact X hn hnX) b hpower
  exact ⟨a, Subtype.ext ha⟩

private theorem addCommGrpCat_comp_zero_apply
    {A B C : AddCommGrpCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : f ≫ g = 0) (a : A) : g (f a) = 0 := by
  have h := congrArg (fun k : A ⟶ C => k a) hfg
  change g (f a) = 0 at h
  exact h

/-- If actual global units admit nth roots, the preceding actual
connecting map vanishes and the original coefficient inclusion is injective. -/
theorem etaleRootsOfUnityH1ToMultiplicativeGroup_injective_of_power_surjective
    (X : Scheme.{u}) {n : ℕ} (hn : 0 < n)
    (hnX : IsUnit (n : Γ(X, ⊤)))
    (hpower : Function.Surjective
      (fun a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0 => n • a)) :
    Function.Injective (etaleRootsOfUnityH1ToMultiplicativeGroup X n) := by
  let S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    etaleKummerComplex X n
  have hS : S.ShortExact := etaleKummerComplex_shortExact X hn hnX
  let j : Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 1 →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 :=
    etaleRootsOfUnityH1ToMultiplicativeGroup X n
  have hzero : ∀ a : Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 1,
      j a = 0 → a = 0 := by
    intro a ha
    obtain ⟨b, hb⟩ := Sheaf.H.longSequence_exact₁ hS a ha (n₀ := 0) rfl
    obtain ⟨d, hd⟩ := hpower b
    have hmul : Sheaf.H.map S.g 0 d = b :=
      (etaleMultiplicativeGroupPower_cohomology_apply X n 0 d).trans hd
    have hz : AddCommGrpCat.ofHom (Sheaf.H.map S.g 0) ≫
        AddCommGrpCat.ofHom (Sheaf.H.δ hS 0 1 rfl) = 0 :=
      (Sheaf.H.longSequence_exact hS 0 1 rfl).zero 1
    have hd0 : Sheaf.H.δ hS 0 1 rfl (Sheaf.H.map S.g 0 d) = 0 :=
      addCommGrpCat_comp_zero_apply
        (AddCommGrpCat.ofHom (Sheaf.H.map S.g 0))
        (AddCommGrpCat.ofHom (Sheaf.H.δ hS 0 1 rfl)) hz d
    exact hb.symm.trans
      ((congrArg (Sheaf.H.δ hS 0 1 rfl) hmul.symm).trans hd0)
  intro a b hab
  change j a = j b at hab
  apply sub_eq_zero.mp
  have hsub : j (a - b) = 0 :=
    (j.map_sub a b).trans
      ((congrArg (fun z : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 => z - j b)
        hab).trans (sub_self (j b)))
  exact hzero (a - b) hsub

/-- The actual Kummer inclusion is the n-torsion comparison whenever
the original global power map is surjective. -/
def etaleKummerH1EquivPowerKernel
    (X : Scheme.{u}) {n : ℕ} (hn : 0 < n)
    (hnX : IsUnit (n : Γ(X, ⊤)))
    (hpower : Function.Surjective
      (fun a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0 => n • a)) :
    Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 1 ≃+
      (nsmulAddMonoidHom n : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 →+
        Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1).ker :=
  AddEquiv.ofBijective (etaleKummerH1ToPowerKernel X n)
    ⟨fun _ _ h =>
      etaleRootsOfUnityH1ToMultiplicativeGroup_injective_of_power_surjective
        X hn hnX hpower (congrArg Subtype.val h),
      etaleKummerH1ToPowerKernel_surjective X hn hnX⟩

/-- The comparison retains the literal original coefficient inclusion. -/
theorem etaleKummerH1EquivPowerKernel_apply
    (X : Scheme.{u}) {n : ℕ} (hn : 0 < n)
    (hnX : IsUnit (n : Γ(X, ⊤)))
    (hpower : Function.Surjective
      (fun a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0 => n • a))
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 1) :
    (etaleKummerH1EquivPowerKernel X hn hnX hpower a).val =
      Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower X n)) 1 a := rfl

/-- On original degree-one cohomology, exponent reduction induces
the original multiplication by the exponent ratio on H¹(Gm). -/
theorem etaleRootsOfUnityH1ToMultiplicativeGroup_power_transition
    (X : Scheme.{u}) (n m : ℕ)
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf X (n * m)) 1) :
    etaleRootsOfUnityH1ToMultiplicativeGroup X n
        (Sheaf.H.map (etaleKummerPowerTransition X n m) 1 a) =
      m • etaleRootsOfUnityH1ToMultiplicativeGroup X (n * m) a := by
  change Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower X n)) 1
      (Sheaf.H.map (etaleKummerPowerTransition X n m) 1 a) =
    m • Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower X (n * m))) 1 a
  rw [← Sheaf.H.map_comp_apply, etaleKummerPowerTransition_ι,
    Sheaf.H.map_comp_apply, etaleMultiplicativeGroupPower_cohomology_apply]

end EtaleCohomology
