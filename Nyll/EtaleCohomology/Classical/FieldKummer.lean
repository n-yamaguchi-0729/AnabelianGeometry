/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FieldHilbert90
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Kummer classes and finite effacement over fields

The actual derived étale H¹ with roots-of-unity coefficients is computed as
field units modulo nth powers. The map is the connecting homomorphism of the
constructed Kummer sequence, with H⁰ identified with the original field units.
Surjectivity uses the proved geometric Hilbert 90 theorem; the kernel is
computed using exactness and the actual power map on units.

This is the field case of the cohomology sequence in Stacks Project, Section
59.28 (https://stacks.math.columbia.edu/tag/03PK). The field-unit quotient
interface below retains its characteristic-zero convenience hypothesis. The
results supplied with an explicit invertible exponent, including the actual
degree-two injection, apply in every characteristic.
-/

/-!
# Kummer effacement and degree-two injectivity for invertible exponents

Geometric Hilbert 90 makes the actual Kummer boundary surjective in degree
one. Consequently every roots-of-unity H1 class has a finite etale effacing
cover of the prescribed degree. In degree two, the actual inclusion of
roots of unity into Gm induces an injection on derived sheaf cohomology.
No comparison with Galois cohomology is assumed.
-/

@[expose] public section

noncomputable section

universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits Opposite

namespace EtaleCohomology

/-- Every positive exponent is invertible on the spectrum of a characteristic-zero field. -/
theorem fieldKummerExponentUnit (K : Type u) [Field K] [CharZero K]
    {n : ℕ} (hn : 0 < n) : IsUnit (n : Γ(Spec (.of K), ⊤)) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  apply (MulEquiv.isUnit_map e).mp
  simpa only [map_natCast] using
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) : IsUnit (n : K))

/-- Degree-zero cohomology of the multiplicative group over a field is its group of units. -/
def fieldUnitsH0Equiv (K : Type u) [Field K] :
    Sheaf.H.{u} (etaleMultiplicativeGroupSheaf (Spec (.of K))) 0 ≃+ Additive Kˣ :=
  (Sheaf.H.equiv₀ (etaleMultiplicativeGroupSheaf (Spec (.of K)))
    (MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) (Spec (.of K)))).trans
      (etaleMultiplicativeGroupSpecSectionsEquiv (Spec (.of K)) (.of K) (𝟙 _))

private theorem fieldUnitsH0Equiv_power (K : Type u) [Field K] (n : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf (Spec (.of K))) 0) :
    fieldUnitsH0Equiv K (Sheaf.H.map (etaleMultiplicativeGroupPower (Spec (.of K)) n) 0 a) =
      n • fieldUnitsH0Equiv K a := by
  let X : Scheme.{u} := Spec (.of K)
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let e : (etaleMultiplicativeGroupSheaf X).obj.obj
      (op (Scheme.Etale.mk (𝟙 X))) ≃+ Additive Kˣ :=
    etaleMultiplicativeGroupSpecSectionsEquiv X (.of K) (𝟙 X)
  change e (Sheaf.H.equiv₀ (etaleMultiplicativeGroupSheaf X) hT
    (Sheaf.H.map (etaleMultiplicativeGroupPower X n) 0 a)) = _
  rw [← Sheaf.H.equiv₀_naturality hT (etaleMultiplicativeGroupPower X n)]
  change e (n • Sheaf.H.equiv₀ (etaleMultiplicativeGroupSheaf X) hT a) =
    n • e (Sheaf.H.equiv₀ (etaleMultiplicativeGroupSheaf X) hT a)
  exact map_nsmul e n _

/-- The connecting homomorphism on original field units, with multiplication
written additively, taking values in actual derived étale cohomology. -/
def etaleFieldKummerBoundary (K : Type u) [Field K] [CharZero K]
    {n : ℕ} (hn : 0 < n) :
    Additive Kˣ →+ Sheaf.H.{u} (etaleRootsOfUnitySheaf (Spec (.of K)) n) 1 :=
  (Sheaf.H.δ (etaleKummerComplex_shortExact (Spec (.of K)) hn
    (fieldKummerExponentUnit K hn)) 0 1 rfl).comp (fieldUnitsH0Equiv K).symm.toAddMonoidHom

/-- Every roots-of-unity H¹ class over the field is a Kummer class. -/
theorem etaleFieldKummerBoundary_surjective (K : Type u) [Field K] [CharZero K]
    {n : ℕ} (hn : 0 < n) : Function.Surjective (etaleFieldKummerBoundary K hn) := by
  intro a
  let hS := etaleKummerComplex_shortExact (Spec (.of K)) hn (fieldKummerExponentUnit K hn)
  obtain ⟨b, hb⟩ := Sheaf.H.longSequence_exact₁ hS a
    (etaleMultiplicativeGroup_H1_eq_zero_of_field K _) rfl
  refine ⟨fieldUnitsH0Equiv K b, ?_⟩
  change Sheaf.H.δ hS 0 1 rfl
    ((fieldUnitsH0Equiv K).symm (fieldUnitsH0Equiv K b)) = a
  rw [AddEquiv.symm_apply_apply]
  exact hb

/-- The kernel consists exactly of nth powers in the original field units. -/
theorem etaleFieldKummerBoundary_eq_zero_iff (K : Type u) [Field K] [CharZero K]
    {n : ℕ} (hn : 0 < n) (s : Additive Kˣ) :
    etaleFieldKummerBoundary K hn s = 0 ↔ ∃ t : Additive Kˣ, n • t = s := by
  let X : Scheme.{u} := Spec (.of K)
  let hS := etaleKummerComplex_shortExact X hn (fieldKummerExponentUnit K hn)
  let e : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0 ≃+ Additive Kˣ :=
    fieldUnitsH0Equiv K
  constructor
  · intro hs
    obtain ⟨b, hb⟩ := Sheaf.H.longSequence_exact₃ hS (e.symm s) rfl hs
    refine ⟨e b, ?_⟩
    exact (fieldUnitsH0Equiv_power K n b).symm.trans
      ((congrArg e hb).trans (e.apply_symm_apply s))
  · rintro ⟨t, rfl⟩
    have he : e.symm (n • t) =
        Sheaf.H.map (etaleMultiplicativeGroupPower X n) 0 (e.symm t) := by
      apply e.injective
      exact (e.apply_symm_apply (n • t)).trans
        ((congrArg (fun z : Additive Kˣ => n • z) (e.apply_symm_apply t)).symm.trans
          (fieldUnitsH0Equiv_power K n (e.symm t)).symm)
    change Sheaf.H.δ hS 0 1 rfl (e.symm (n • t)) = 0
    rw [he]
    change ((e.symm t).comp (Ext.mk₀ (etaleMultiplicativeGroupPower X n))
      (add_zero 0)).comp hS.extClass (zero_add 1) = 0
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- The field-unit quotient by nth powers is the actual étale H¹ of μₙ.
The source quotient uses additive notation for the multiplicative unit group. -/
def etaleFieldKummerEquiv (K : Type u) [Field K] [CharZero K]
    {n : ℕ} (hn : 0 < n) :
    (Additive Kˣ ⧸ (nsmulAddMonoidHom n : Additive Kˣ →+ Additive Kˣ).range) ≃+
      Sheaf.H.{u} (etaleRootsOfUnitySheaf (Spec (.of K)) n) 1 := by
  let δ := etaleFieldKummerBoundary K hn
  have hker : (nsmulAddMonoidHom n : Additive Kˣ →+ Additive Kˣ).range = δ.ker := by
    ext s
    exact (etaleFieldKummerBoundary_eq_zero_iff K hn s).symm
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective δ (etaleFieldKummerBoundary_surjective K hn))


/-- Hilbert 90 also vanishes at the terminal object in the actual cohomology
presheaf, through the proved terminal-object comparison. -/
theorem etaleMultiplicativeGroup_H1_terminal_eq_zero_of_field
    (K : Type u) [Field K]
    (a : Sheaf.H'.{u} (etaleMultiplicativeGroupSheaf (Spec (.of K))) 1
      (Scheme.Etale.mk (𝟙 (Spec (.of K))))) : a = 0 := by
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 (Spec (.of K)))) :=
    MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) (Spec (.of K))
  let e : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf (Spec (.of K))) 1 ≃+
      Sheaf.H'.{u} (etaleMultiplicativeGroupSheaf (Spec (.of K))) 1
        (Scheme.Etale.mk (𝟙 (Spec (.of K)))) :=
    sheafCohomologyTerminalEquiv _ hT _ 1
  obtain ⟨b, rfl⟩ := e.surjective a
  rw [etaleMultiplicativeGroup_H1_eq_zero_of_field K b, map_zero]

/-- Every actual roots-of-unity H1 class over a field is the Kummer class
of a unit section. -/
theorem etaleKummerBoundary_surjective_of_field
    (K : Type u) [Field K] {n : ℕ}
    (hn : 0 < n) (hnK : IsUnit (n : Γ(Spec (.of K), ⊤))) :
    Function.Surjective
      (etaleKummerBoundary (Spec (.of K)) hn hnK
        (Scheme.Etale.mk (𝟙 (Spec (.of K))))) := by
  intro a
  let X : Scheme.{u} := Spec (.of K)
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (freeAbelianSheafYoneda X.smallEtaleTopology).obj T
  have hS : (etaleKummerComplex X n).ShortExact :=
    etaleKummerComplex_shortExact X hn hnK
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ P hS a
    (etaleMultiplicativeGroup_H1_terminal_eq_zero_of_field K _) (n₀ := 0) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective P (etaleMultiplicativeGroupSheaf X)).surjective b
  refine ⟨freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology T
    (etaleMultiplicativeGroupSheaf X) f, ?_⟩
  change (Ext.mk₀ ((freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology T
    (etaleMultiplicativeGroupSheaf X)).symm
      (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology T
        (etaleMultiplicativeGroupSheaf X) f))).comp hS.extClass (zero_add 1) = a
  rw [Equiv.symm_apply_apply]
  exact hb

/-- Every actual roots-of-unity H1 class over a field, for an invertible exponent,
is killed by an actual finite etale cover of degree exactly n. -/
theorem exists_degree_n_cover_killing_rootsOfUnity_H1_of_field
    (K : Type u) [Field K] {n : ℕ}
    (hn : 0 < n) (hnK : IsUnit (n : Γ(Spec (.of K), ⊤)))
    (a : Sheaf.H'.{u} (etaleRootsOfUnitySheaf (Spec (.of K)) n) 1
      (Scheme.Etale.mk (𝟙 (Spec (.of K))))) :
    ∃ (W : (Spec (.of K)).Etale)
      (g : W ⟶ Scheme.Etale.mk (𝟙 (Spec (.of K)))),
      IsFiniteEtale g.left ∧ Function.Surjective g.left ∧
      (∀ x : (Scheme.Etale.mk (𝟙 (Spec (.of K)))).left, g.left.finrank x = n) ∧
      ((etaleRootsOfUnitySheaf (Spec (.of K)) n).cohomologyPresheaf 1).map g.op a = 0 := by
  obtain ⟨s, rfl⟩ := etaleKummerBoundary_surjective_of_field K hn hnK a
  exact exists_degree_n_cover_killing_etaleKummerBoundary (Spec (.of K)) hn hnK _ s

/-- The actual Kummer inclusion induces the coefficient map on derived H2. -/
def etaleRootsOfUnityH2ToMultiplicativeGroup (X : Scheme.{u}) (n : ℕ) :
    Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 2 →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 2 :=
  (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower X n))).postcomp
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (add_zero 2)

/-- Geometric Hilbert 90 proves injectivity on actual derived H2, without
assuming a field/Galois or Brauer comparison. -/
theorem etaleRootsOfUnityH2ToMultiplicativeGroup_injective_of_field
    (K : Type u) [Field K] {n : ℕ}
    (hn : 0 < n) (hnK : IsUnit (n : Γ(Spec (.of K), ⊤))) :
    Function.Injective (etaleRootsOfUnityH2ToMultiplicativeGroup (Spec (.of K)) n) := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  rw [AddSubgroup.eq_bot_iff_forall]
  intro a ha
  let X : Scheme.{u} := Spec (.of K)
  let Z : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))
  have hS : (etaleKummerComplex X n).ShortExact :=
    etaleKummerComplex_shortExact X hn hnK
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ Z hS a ha (n₀ := 1) rfl
  rw [etaleMultiplicativeGroup_H1_eq_zero_of_field K b, Ext.zero_comp] at hb
  exact hb.symm

end EtaleCohomology
