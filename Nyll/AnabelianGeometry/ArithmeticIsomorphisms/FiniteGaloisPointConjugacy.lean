/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.FiniteQuotientConjugacy
public import Nyll.EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient
public import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenNormalUniverse
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticSurjective
public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic

/-!
# Closed-subgroup and full-inner conjugacy from finite Galois-cover pointings

The finite-level input is an actual point intertwining the second action
with the deck action specified by the first. If each point lies in the orbit
of a specified closed subgroup, compactness gives one conjugator in that
subgroup. The geometric theorem specializes to the arithmetic kernel. The
full-inner theorem uses transitivity and has no orbit premise; it does not
imply geometric-inner conjugacy over a finite field.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.ArithmeticIsomorphisms

/-- Actual finite Galois-cover pointings in the orbits of a specified closed
subgroup supply one simultaneous conjugator in that subgroup. At each cover
one point must intertwine every source element; no compatibility between
covers is needed. No arithmetic or normality condition on the subgroup is
used in the compactness argument. -/
theorem exists_conjugator_in_closedSubgroup_of_galoisCover_pointings
    {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    {A : Type v} (α β : A → π₁ᵉᵗ(xi))
    (H : Subgroup π₁ᵉᵗ(xi)) (hH : IsClosed (H : Set π₁ᵉᵗ(xi)))
    (hpoint : ∀ (W : FiniteEtale X) (hW : IsGalois W)
      (x : (fiber xi).obj W),
      let _ : IsGalois W := hW
      ∃ y : (fiber xi).obj W,
        y ∈ MulAction.orbit H x ∧
        ∀ a : A, β a • y = (fiber xi).map
          ((galoisObjectQuotientMonoidHom (fiber xi) π₁ᵉᵗ(xi) W x
            (α a)).unop.asIso.hom) y) :
    ∃ c : π₁ᵉᵗ(xi), c ∈ H ∧ ∀ a : A, β a = c * α a * c⁻¹ := by
  refine exists_simultaneous_conjugator_of_finite_quotients α β H hH ?_
  intro U
  obtain ⟨W, hW, x, hx⟩ :=
    exists_galois_object_point_stabilizer_eq_any_universe (fiber xi) U
  let : IsGalois W := hW
  obtain ⟨y, hy, hact⟩ := hpoint W hW x
  obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.mp hy
  let c₀ : π₁ᵉᵗ(xi) := c
  have hcpoint : c₀ • x = y := hc
  refine ⟨c₀, c.property, fun a => ?_⟩
  let d : Aut W :=
    (galoisObjectQuotientMonoidHom (fiber xi) π₁ᵉᵗ(xi) W x (α a)).unop
  have hdeck : (fiber xi).map d.asIso.hom x = α a • x :=
    galoisObjectQuotientMonoidHom_evaluation (fiber xi) π₁ᵉᵗ(xi) W x (α a)
  have hcomm : β a • (c₀ • x) = c₀ • (α a • x) := by
    calc
      β a • (c₀ • x) = β a • y := congrArg (β a • ·) hcpoint
      _ = (fiber xi).map d.asIso.hom y := hact a
      _ = (fiber xi).map d.asIso.hom (c₀ • x) :=
        congrArg ((fiber xi).map d.asIso.hom) hcpoint.symm
      _ = c₀ • (fiber xi).map d.asIso.hom x :=
        (mulAction_naturality (fiber xi) c₀ d.asIso.hom x).symm
      _ = c₀ • (α a • x) := congrArg (c₀ • ·) hdeck
  have hmem : (c₀ * α a)⁻¹ * (β a * c₀) ∈ (U : Subgroup π₁ᵉᵗ(xi)) := by
    rw [← hx]
    change ((c₀ * α a)⁻¹ * (β a * c₀)) • x = x
    rw [mul_smul, mul_smul, hcomm, ← mul_smul c₀ (α a) x, inv_smul_smul]
  let q := ProCGroups.ProC.OpenNormalSubgroup.quotientProj U
  have hq : q (c₀ * α a) = q (β a * c₀) := QuotientGroup.eq.mpr hmem
  apply mul_right_cancel (b := q c₀)
  calc
    q (β a) * q c₀ = q (β a * c₀) := (map_mul q _ _).symm
    _ = q (c₀ * α a) := hq.symm
    _ = q ((c₀ * α a * c₀⁻¹) * c₀) := by
      rw [mul_assoc (c₀ * α a) c₀⁻¹ c₀, inv_mul_cancel, mul_one]
    _ = q (c₀ * α a * c₀⁻¹) * q c₀ := map_mul q _ _

/-- Pointings on the actual finite-etale Galois covers give one conjugator
in the original arithmetic kernel. Each pointing must intertwine all source
elements at its level, but no compatibility between different levels is
assumed. In particular this applies to continuous homomorphisms or
equivalences between the original fundamental groups. -/
theorem exists_geometric_conjugator_of_galoisCover_pointings
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    {A : Type v} (α β : A → π₁ᵉᵗ(xi))
    (hpoint : ∀ (W : FiniteEtale X) (hW : IsGalois W)
      (x : (fiber xi).obj W),
      let _ : IsGalois W := hW
      ∃ y : (fiber xi).obj W,
        y ∈ MulAction.orbit
          (arithmeticFundamentalGroupHom k K f xi).toMonoidHom.ker x ∧
        ∀ a : A, β a • y = (fiber xi).map
          ((galoisObjectQuotientMonoidHom (fiber xi) π₁ᵉᵗ(xi) W x
            (α a)).unop.asIso.hom) y) :
    ∃ c : π₁ᵉᵗ(xi), arithmeticFundamentalGroupHom k K f xi c = 1 ∧
      ∀ a : A, β a = c * α a * c⁻¹ := by
  exact exists_conjugator_in_closedSubgroup_of_galoisCover_pointings xi α β
    (arithmeticFundamentalGroupHom k K f xi).toMonoidHom.ker
    (ProCGroups.ContinuousMonoidHom.isClosed_ker (arithmeticFundamentalGroupHom k K f xi))
    hpoint

/-- Actual intertwining pointings on every finite Galois cover give a full
inner conjugator. The orbit premise disappears because the full fundamental
group acts transitively on each such fibre. This is the unpointed outer
conclusion: it does not assert that the conjugator lies in an arithmetic
kernel, even when the two original maps preserve an arithmetic marking. -/
theorem exists_conjugator_of_galoisCover_pointings
    {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    {A : Type v} (α β : A → π₁ᵉᵗ(xi))
    (hpoint : ∀ (W : FiniteEtale X) (hW : IsGalois W)
      (x : (fiber xi).obj W),
      let _ : IsGalois W := hW
      ∃ y : (fiber xi).obj W, ∀ a : A, β a • y = (fiber xi).map
        ((galoisObjectQuotientMonoidHom (fiber xi) π₁ᵉᵗ(xi) W x
          (α a)).unop.asIso.hom) y) :
    ∃ c : π₁ᵉᵗ(xi), ∀ a : A, β a = c * α a * c⁻¹ := by
  obtain ⟨c, _, hc⟩ := exists_conjugator_in_closedSubgroup_of_galoisCover_pointings
    xi α β ⊤ (show IsClosed ((⊤ : Subgroup π₁ᵉᵗ(xi)) : Set π₁ᵉᵗ(xi)) from isClosed_univ)
    (by
      intro W hW x
      let _ : IsGalois W := hW
      obtain ⟨y, hy⟩ := hpoint W hW x
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq π₁ᵉᵗ(xi) x y
      refine ⟨y, MulAction.mem_orbit_iff.mpr ?_, hy⟩
      exact ⟨⟨g, Subgroup.mem_top g⟩, hg⟩)
  exact ⟨c, hc⟩

end AnabelianGeometry.ArithmeticIsomorphisms
