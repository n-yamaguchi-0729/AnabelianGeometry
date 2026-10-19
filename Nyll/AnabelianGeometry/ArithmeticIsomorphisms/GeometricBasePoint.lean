/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticSurjective
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality
import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso
import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality
import Nyll.ProCGroups.Topologies.ArithmeticInnerCorrectionFiberTransport

/-! # Arithmetic-preserving changes of geometric base point

An arbitrary comparison of geometric fibres need not commute with the chosen
maps to the absolute Galois group. Its discrepancy is computed from the two
comparisons on constant covers. Geometric connectedness then supplies an
actual lift which corrects the fibre comparison itself.
-/

noncomputable section

universe u u₁ u₂ v₁ v₂ w

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.ArithmeticIsomorphisms

private theorem autHomOfCompIso_whiskerLeft_trans
    {C : Type u₁} [Category.{u₂} C]
    {D : Type v₁} [Category.{v₂} D]
    (H : C ⥤ D)
    {F : C ⥤ FintypeCat.{w}} {F' G' : D ⥤ FintypeCat.{w}}
    (t : F' ≅ G') (r : H ⋙ G' ≅ F) (g : Aut F') :
    autHomOfCompIso H (Functor.isoWhiskerLeft H t ≪≫ r) g =
      autHomOfCompIso H r (t.conjAut g) := by
  simp only [autHomOfCompIso_apply, Iso.trans_conjAut]
  exact congrArg r.conjAut
    (Functor.map_conjAut
      ((Functor.whiskeringLeft C D FintypeCat.{w}).obj H) t g).symm

private theorem arithmeticMap_toFiberAut
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsSepClosure k K] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (g : π₁ᵉᵗ(x)) :
    absoluteGaloisToFiberAutMulEquiv k K ‹IsSepClosed K›
        (arithmeticFundamentalGroupHom k K f x g) =
      autHomOfCompIso (pullback f)
        (pullbackFiberIso f x ≪≫ (nonempty_fiber_iso (x ≫ f) (ξ k K)).some) g := by
  let t : fiber (x ≫ f) ≅ fib k K :=
    (nonempty_fiber_iso (x ≫ f) (ξ k K)).some
  rw [autHomOfCompIso_apply, Iso.trans_conjAut]
  change (toAutHomeo (fib k K) (K ≃ₐ[k] K))
      ((toAutHomeo (fib k K) (K ≃ₐ[k] K)).symm
        ((continuousConjAut t) (fundamentalGroupHom f x g))) =
    t.conjAut (fundamentalGroupHom f x g)
  exact (toAutHomeo (fib k K) (K ≃ₐ[k] K)).apply_symm_apply _

/-- A comparison of actual geometric fibre functors has one uniform arithmetic
conjugator, computed from its restriction to the constant finite covers. -/
theorem arithmeticFundamentalGroupHom_fiberIso_conjugate
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X)
    (t : fiber x ≅ fiber y) :
    ∃ d : Gal(K/k), ∀ g : π₁ᵉᵗ(x),
      arithmeticFundamentalGroupHom k K f y (continuousConjAut t g) =
        d * arithmeticFundamentalGroupHom k K f x g * d⁻¹ := by
  let : IsSepClosed K := IsSepClosure.sep_closed k
  let e : Gal(K/k) ≃* Aut (fib k K) :=
    absoluteGaloisToFiberAutMulEquiv k K ‹IsSepClosed K›
  let tx : pullback f ⋙ fiber x ≅ fib k K :=
    pullbackFiberIso f x ≪≫ (nonempty_fiber_iso (x ≫ f) (ξ k K)).some
  let ty : pullback f ⋙ fiber y ≅ fib k K :=
    pullbackFiberIso f y ≪≫ (nonempty_fiber_iso (y ≫ f) (ξ k K)).some
  let txy : pullback f ⋙ fiber x ≅ fib k K :=
    Functor.isoWhiskerLeft (pullback f) t ≪≫ ty
  let a : Aut (fib k K) := tx.symm ≪≫ txy
  refine ⟨e.symm a, fun g => ?_⟩
  have hx : autHomOfCompIso (pullback f) tx g =
      e (arithmeticFundamentalGroupHom k K f x g) :=
    (arithmeticMap_toFiberAut k K f x g).symm
  have hy : autHomOfCompIso (pullback f) txy g =
      e (arithmeticFundamentalGroupHom k K f y (continuousConjAut t g)) := by
    exact (autHomOfCompIso_whiskerLeft_trans (pullback f) t ty g).trans
      (arithmeticMap_toFiberAut k K f y (continuousConjAut t g)).symm
  have h := autHomOfCompIso_eq_conj (pullback f) tx txy g
  rw [hx, hy] at h
  have hcore :
      e (arithmeticFundamentalGroupHom k K f y (continuousConjAut t g)) =
        a * e (arithmeticFundamentalGroupHom k K f x g) * a⁻¹ :=
    h.trans (MulAut.conj_apply a (e (arithmeticFundamentalGroupHom k K f x g)))
  have he := congrArg e.symm hcore
  simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using he

/-- On a geometrically connected scheme the comparison can be chosen to
preserve the original arithmetic maps strictly. The corrected comparison is
an isomorphism of the actual fibre functors, not just an abstract group map. -/
theorem exists_arithmetic_preserving_fiberIso
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [GeometricallyConnected f]
    {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X) :
    ∃ t : fiber x ≅ fiber y, ∀ g : π₁ᵉᵗ(x),
      arithmeticFundamentalGroupHom k K f y (continuousConjAut t g) =
        arithmeticFundamentalGroupHom k K f x g := by
  let : ConnectedSpace X :=
    GeometricallyConnected.connectedSpace_of_subsingleton f
  obtain ⟨t⟩ := nonempty_fiber_iso x y
  obtain ⟨d, hd⟩ := arithmeticFundamentalGroupHom_fiberIso_conjugate k K f x y t
  obtain ⟨c, _hc, hcorrected⟩ := ProCGroups.exists_innerCorrection_strict_quotient
    (continuousConjAut t)
    (arithmeticFundamentalGroupHom k K f x).toMonoidHom
    (arithmeticFundamentalGroupHom k K f y).toMonoidHom
    (arithmeticFundamentalGroupHom_surjective k K f y) d hd
  let cIso : fiber y ≅ fiber y := c
  refine ⟨t ≪≫ cIso, fun g => ?_⟩
  have htrans : continuousConjAut (t ≪≫ cIso) g =
      cIso.conjAut (t.conjAut g) := Iso.trans_conjAut t cIso g
  have hinner : cIso.conjAut (t.conjAut g) =
      c * continuousConjAut t g * c⁻¹ := by
    apply Aut.ext
    rfl
  exact (congrArg (arithmeticFundamentalGroupHom k K f y) htrans).trans
    ((congrArg (arithmeticFundamentalGroupHom k K f y) hinner).trans (hcorrected g))

end AnabelianGeometry.ArithmeticIsomorphisms
