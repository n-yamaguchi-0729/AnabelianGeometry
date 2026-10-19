/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.CoefficientProjection
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality
import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso

/-! # Exact coefficient quotients in a tower of fields

Extension of a geometric-point field commutes with pullback of constant
covers, by the actual formulas on field-valued points. Consequently the
quotient defined by a supplied coefficient embedding commutes strictly with
restriction of scalars. Only actual scheme and point equations are used.
-/

noncomputable section
open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u u₁ u₂ v₁ v₂ w

private theorem fiber_point_eqToIso
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (x y : Spec (.of Ω) ⟶ X) (h : x = y)
    (A : FiniteEtale X) (v : (fiber x).obj A) :
    (fiberObjEquivHom y A ((eqToIso (congrArg fiber h)).hom.app A v)).left =
      (fiberObjEquivHom x A v).left := by
  subst y
  rfl

private theorem fiberIso_ext_point
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] {Y : Scheme.{u}}
    (y : Spec (.of Ω) ⟶ Y) {F : FiniteEtale Y ⥤ FintypeCat.{u}}
    (r s : F ≅ fiber y)
    (h : ∀ (A : FiniteEtale Y) (v : F.obj A),
      (fiberObjEquivHom y A (r.hom.app A v)).left =
        (fiberObjEquivHom y A (s.hom.app A v)).left) : r = s := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply FintypeCat.hom_ext
  intro v
  apply (fiberObjEquivHom y A).injective
  apply Over.OverMorphism.ext
  exact h A v

private theorem pointedPullbackFiberIso_point
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (h : x ≫ f = y) (A : FiniteEtale Y)
    (v : (fiber x).obj ((pullback f).obj A)) :
    (fiberObjEquivHom y A
      ((pullbackFiberIso f x ≪≫ eqToIso (congrArg fiber h)).hom.app A v)).left =
      (fiberObjEquivHom x ((pullback f).obj A) v).left ≫
        Limits.pullback.fst A.hom f := by
  exact (fiber_point_eqToIso (x ≫ f) y h A
    ((pullbackFiberIso f x).hom.app A v)).trans
      (pullbackFiberIso_hom_fiberObjEquivHom_left f x A v)

private theorem eqToIso_conjAut_eq_transport
    {Ω : Type u} [Field Ω] {X : Scheme.{u}}
    (x y : Spec (.of Ω) ⟶ X) (h : x = y) (g : Aut (fiber x)) :
    (eqToIso (congrArg fiber h)).conjAut g = h ▸ g := by
  subst y
  apply Aut.ext
  simp only [eqToIso_refl, Iso.conjAut_hom, Iso.refl_conj]

private theorem autHom_trans_target
    {C : Type u₁} [Category.{u₂} C] {D : Type v₁} [Category.{v₂} D]
    (H : C ⥤ D) {F G : C ⥤ FintypeCat.{w}} {F' : D ⥤ FintypeCat.{w}}
    (t : H ⋙ F' ≅ F) (r : F ≅ G) (g : Aut F') :
    autHomOfCompIso H (t ≪≫ r) g = r.conjAut (autHomOfCompIso H t g) := by
  simp only [autHomOfCompIso_apply, Iso.trans_conjAut]

private theorem autHom_whisker_trans
    {C : Type u₁} [Category.{u₂} C] {D : Type v₁} [Category.{v₂} D]
    (H : C ⥤ D) {F : C ⥤ FintypeCat.{w}} {F' G' : D ⥤ FintypeCat.{w}}
    (t : F' ≅ G') (r : H ⋙ G' ≅ F) (g : Aut F') :
    autHomOfCompIso H (Functor.isoWhiskerLeft H t ≪≫ r) g =
      autHomOfCompIso H r (t.conjAut g) := by
  simp only [autHomOfCompIso_apply, Iso.trans_conjAut]
  exact congrArg r.conjAut
    (Functor.map_conjAut ((Functor.whiskeringLeft C D FintypeCat.{w}).obj H) t g).symm

private theorem pointedFundamentalGroupHom_eq_comparison
    {Ω : Type u} [Field Ω] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (h : x ≫ f = y) (g : π₁ᵉᵗ(x)) :
    pointedFundamentalGroupHom f x y h g =
      autHomOfCompIso (pullback f)
        (pullbackFiberIso f x ≪≫ eqToIso (congrArg fiber h)) g := by
  exact (pointedFundamentalGroupHom_apply f x y h g).trans
    ((eqToIso_conjAut_eq_transport (x ≫ f) y h
      (fundamentalGroupHom f x g)).symm.trans
        (autHom_trans_target (pullback f) (pullbackFiberIso f x)
          (eqToIso (congrArg fiber h)) g).symm)

private theorem pointedFundamentalGroupHom_congr_map
    {Ω : Type u} [Field Ω] {X Y : Scheme.{u}}
    (f₁ f₂ : X ⟶ Y) (hf : f₁ = f₂)
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (h₁ : x ≫ f₁ = y) (h₂ : x ≫ f₂ = y) :
    pointedFundamentalGroupHom f₁ x y h₁ =
      pointedFundamentalGroupHom f₂ x y h₂ := by
  subst f₂
  rfl

private theorem pointedFundamentalGroupHom_square_apply
    {Ω : Type u} [Field Ω] {X Y Z W : Scheme.{u}}
    (f : X ⟶ Z) (c : Y ⟶ W) (a : Y ⟶ X) (b : W ⟶ Z)
    (ha : a ≫ f = c ≫ b)
    (y : Spec (.of Ω) ⟶ Y) (x : Spec (.of Ω) ⟶ X)
    (z : Spec (.of Ω) ⟶ W) (w : Spec (.of Ω) ⟶ Z)
    (hpoint : y ≫ a = x) (hy : y ≫ c = z)
    (hx : x ≫ f = w) (hb : z ≫ b = w) (g : π₁ᵉᵗ(y)) :
    pointedFundamentalGroupHom f x w hx
        (pointedFundamentalGroupHom a y x hpoint g) =
      pointedFundamentalGroupHom b z w hb
        (pointedFundamentalGroupHom c y z hy g) := by
  have hsquare :
      (pointedFundamentalGroupHom f x w hx).comp
          (pointedFundamentalGroupHom a y x hpoint) =
        (pointedFundamentalGroupHom b z w hb).comp
          (pointedFundamentalGroupHom c y z hy) := by
    rw [pointedFundamentalGroupHom_comp, pointedFundamentalGroupHom_comp]
    exact pointedFundamentalGroupHom_congr_map (a ≫ f) (c ≫ b) ha y w _ _
  exact DFunLike.congr_fun hsquare g

private theorem iso_conjAut_symm_apply
    {C : Type u₁} [Category.{u₂} C] {P Q : C}
    (t : P ≅ Q) (a : Aut P) : t.symm.conjAut (t.conjAut a) = a := by
  apply Aut.ext
  simp only [Iso.conjAut_hom, Iso.symm_self_conj]

/-- A coherent comparison square transports automorphisms through the inverse fibers. -/
private theorem autHom_inverse_coherence
    {C : Type u₁} [Category.{u₂} C] {D : Type v₁} [Category.{v₂} D]
    (H : C ⥤ D) {F G : C ⥤ FintypeCat.{w}} {F' G' : D ⥤ FintypeCat.{w}}
    (t : F' ≅ G') (s : F ≅ G) (r : H ⋙ F' ≅ F) (q : H ⋙ G' ≅ G)
    (hcoherence : Functor.isoWhiskerLeft H t ≪≫ q = r ≪≫ s) (g : Aut G') :
    s.symm.conjAut (autHomOfCompIso H q g) =
      autHomOfCompIso H r (t.symm.conjAut g) := by
  have hforward : autHomOfCompIso H q (t.conjAut (t.symm.conjAut g)) =
      s.conjAut (autHomOfCompIso H r (t.symm.conjAut g)) := by
    rw [← autHom_whisker_trans, hcoherence, autHom_trans_target]
  have ht : t.conjAut (t.symm.conjAut g) = g :=
    iso_conjAut_symm_apply t.symm g
  exact (congrArg (fun a => s.symm.conjAut (autHomOfCompIso H q a)) ht).symm.trans
    ((congrArg s.symm.conjAut hforward).trans
      (iso_conjAut_symm_apply s (autHomOfCompIso H r (t.symm.conjAut g))))

section Pointed

variable (k κ Ω : Type u) [Field k] [Field κ] [Field Ω]
  [Algebra k κ] [IsSepClosure k κ] [IsSepClosed κ]
  [Algebra κ Ω] [Algebra k Ω] [IsScalarTower k κ Ω] [IsSepClosed Ω]

/-- The supplied coefficient quotient uses the actual pointed scheme map
followed by the inverse of the actual extension of coefficient fibers. -/
theorem coefficientProjection_eq_pointed
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : Spec (.of Ω) ⟶ X)
    (hx : x ≫ f = ξ k Ω) (g : π₁ᵉᵗ(x)) :
    coefficientProjection k κ Ω f x hx g =
      (suppliedGaloisEquivFundamentalGroup k κ).symm
        ((fieldFiberExtensionIso k κ Ω).symm.conjAut
          (pointedFundamentalGroupHom f x (ξ k Ω) hx g)) := by
  change (suppliedGaloisEquivFundamentalGroup k κ).symm
      ((eqToIso (congrArg fiber hx) ≪≫ (fieldFiberExtensionIso k κ Ω).symm).conjAut
        (fundamentalGroupHom f x g)) = _
  exact
    (congrArg (suppliedGaloisEquivFundamentalGroup k κ).symm
      (Iso.trans_conjAut (eqToIso (congrArg fiber hx))
        (fieldFiberExtensionIso k κ Ω).symm (fundamentalGroupHom f x g))).trans
      (congrArg
        (fun a : π₁ᵉᵗ(ξ k Ω) =>
          (suppliedGaloisEquivFundamentalGroup k κ).symm
            ((fieldFiberExtensionIso k κ Ω).symm.conjAut a))
        ((eqToIso_conjAut_eq_transport (x ≫ f) (ξ k Ω) hx
          (fundamentalGroupHom f x g)).trans
          (pointedFundamentalGroupHom_apply f x (ξ k Ω) hx g).symm))

end Pointed

section Tower

variable (k E κ Ω : Type u) [Field k] [Field E] [Field κ] [Field Ω]
  [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
  [Algebra κ Ω] [Algebra E Ω] [Algebra k Ω]
  [IsScalarTower E κ Ω] [IsScalarTower k κ Ω] [IsScalarTower k E Ω]
  [IsSepClosed κ] [IsSepClosed Ω]

/-- The two actual comparisons of an extended constant-cover fiber agree. -/
theorem fieldFiberExtensionIso_pullback :
    Functor.isoWhiskerLeft (pullback (ξ k E)) (fieldFiberExtensionIso E κ Ω) ≪≫
        fieldPullbackFiberIso k E Ω =
      fieldPullbackFiberIso k E κ ≪≫ fieldFiberExtensionIso k κ Ω := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply FintypeCat.hom_ext
  intro x
  apply (fiberObjEquivHom (ξ k Ω) A).injective
  apply Over.OverMorphism.ext
  change (fiberObjEquivHom (ξ k Ω) A
      (fieldFiberEquiv k E Ω A
        ((fieldFiberExtensionIso E κ Ω).hom.app ((pullback (ξ k E)).obj A) x))).left =
    (fiberObjEquivHom (ξ k Ω) A ((fieldFiberExtensionIso k κ Ω).hom.app A
      (fieldFiberEquiv k E κ A x))).left
  rw [fiberObjEquivHom_fieldFiberEquiv, fieldFiberExtensionIso_point]
  change (fiberObjEquivHom (ξ E Ω) ((pullback (ξ k E)).obj A)
      ((fieldFiberExtensionIso E κ Ω).hom.app ((pullback (ξ k E)).obj A) x)).left ≫
        Limits.pullback.fst A.hom (ξ k E) =
    ξ κ Ω ≫ (fiberObjEquivHom (ξ k κ) A (fieldFiberEquiv k E κ A x)).left
  rw [fieldFiberExtensionIso_point, fiberObjEquivHom_fieldFiberEquiv]
  exact Category.assoc _ _ _

omit [IsSepClosed Ω] in
private theorem fieldPullbackOverEquiv_left
    (A : FiniteEtale (Spec (.of k)))
    (x : Over.mk (ξ E Ω) ⟶ ((pullback (ξ k E)).obj A).toComma) :
    (fieldPullbackOverEquiv k E Ω A x).left =
      x.left ≫ Limits.pullback.fst A.hom (ξ k E) := by
  rfl

private theorem fieldPullbackFiberIso_point
    (A : FiniteEtale (Spec (.of k)))
    (x : (pullback (ξ k E) ⋙ fib E Ω).obj A) :
    (fiberObjEquivHom (ξ k Ω) A
      ((fieldPullbackFiberIso k E Ω).hom.app A x)).left =
      (fiberObjEquivHom (ξ E Ω) ((pullback (ξ k E)).obj A) x).left ≫
        Limits.pullback.fst A.hom (ξ k E) := by
  exact
    (congrArg (fun z : Over.mk (ξ k Ω) ⟶ A.toComma => z.left)
      (fiberObjEquivHom_fieldFiberEquiv k E Ω A x)).trans
      (fieldPullbackOverEquiv_left k E Ω A
        (fiberObjEquivHom (ξ E Ω) ((pullback (ξ k E)).obj A) x))

private theorem fieldPullbackFiberIso_eq_pointed :
    fieldPullbackFiberIso k E Ω =
      pullbackFiberIso (ξ k E) (ξ E Ω) ≪≫
        eqToIso (congrArg fiber (fieldGeometricPoint_comp k E Ω)) := by
  apply fiberIso_ext_point (ξ k Ω)
  intro A x
  exact (fieldPullbackFiberIso_point k E Ω A x).trans
    (pointedPullbackFiberIso_point (ξ k E) (ξ E Ω) (ξ k Ω)
      (fieldGeometricPoint_comp k E Ω) A x).symm

variable [IsSepClosure k κ] [IsSepClosure E κ]

/-- The extended field fibers retain restriction of scalars exactly. -/
theorem extendedFieldCoefficient_restrict
    (g : Aut (fib E Ω)) :
    (suppliedGaloisEquivFundamentalGroup k κ).symm
        ((fieldFiberExtensionIso k κ Ω).symm.conjAut
          (pointedFundamentalGroupHom (ξ k E) (ξ E Ω) (ξ k Ω)
            (fieldGeometricPoint_comp k E Ω) g)) =
      ((suppliedGaloisEquivFundamentalGroup E κ).symm
        ((fieldFiberExtensionIso E κ Ω).symm.conjAut g)).restrictScalars k := by
  let εE := suppliedGaloisEquivFundamentalGroup E κ
  let εk := suppliedGaloisEquivFundamentalGroup k κ
  let tE := fieldFiberExtensionIso E κ Ω
  let tk := fieldFiberExtensionIso k κ Ω
  let H := pullback (ξ k E)
  let rκ := fieldPullbackFiberIso k E κ
  let rΩ := fieldPullbackFiberIso k E Ω
  let σ := εE.symm (tE.symm.conjAut g)
  have hscalar : autHomOfCompIso H rκ (εE σ) = εk (σ.restrictScalars k) :=
    fieldFundamentalGroupHom_toAutMulEquiv k E κ σ
  have he : εE σ = tE.symm.conjAut g := εE.apply_symm_apply _
  have hp : pointedFundamentalGroupHom (ξ k E) (ξ E Ω) (ξ k Ω)
      (fieldGeometricPoint_comp k E Ω) g = autHomOfCompIso H rΩ g :=
    (pointedFundamentalGroupHom_eq_comparison (ξ k E) (ξ E Ω) (ξ k Ω)
      (fieldGeometricPoint_comp k E Ω) g).trans
      (congrArg
        (fun t : pullback (ξ k E) ⋙ fib E Ω ≅ fib k Ω =>
          autHomOfCompIso (pullback (ξ k E)) t g)
        (fieldPullbackFiberIso_eq_pointed k E Ω).symm)
  have hc := autHom_inverse_coherence H tE tk rκ rΩ
    (fieldFiberExtensionIso_pullback k E κ Ω) g
  change εk.symm (tk.symm.conjAut
      (pointedFundamentalGroupHom (ξ k E) (ξ E Ω) (ξ k Ω)
        (fieldGeometricPoint_comp k E Ω) g)) = σ.restrictScalars k
  exact (congrArg εk.symm
    ((congrArg tk.symm.conjAut hp).trans
      (hc.trans ((congrArg (fun a => autHomOfCompIso H rκ a) he).symm.trans
        hscalar)))).trans (εk.symm_apply_apply _)

/-- Strict tower compatibility for the quotient from actual coefficient
embeddings, for every group element and any actual compatible pointed map. -/
theorem coefficientProjection_tower
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (c : Y ⟶ Spec (.of E))
    (a : Y ⟶ X) (ha : a ≫ f = c ≫ ξ k E)
    (y : Spec (.of Ω) ⟶ Y) (x : Spec (.of Ω) ⟶ X)
    (hpoint : y ≫ a = x) (hy : y ≫ c = ξ E Ω) (hx : x ≫ f = ξ k Ω)
    (g : π₁ᵉᵗ(y)) :
    coefficientProjection k κ Ω f x hx
        (pointedFundamentalGroupHom a y x hpoint g) =
      (coefficientProjection E κ Ω c y hy g).restrictScalars k := by
  have hvalue := pointedFundamentalGroupHom_square_apply f c a (ξ k E) ha
    y x (ξ E Ω) (ξ k Ω) hpoint hy hx (fieldGeometricPoint_comp k E Ω) g
  exact
    (coefficientProjection_eq_pointed k κ Ω f x hx
      (pointedFundamentalGroupHom a y x hpoint g)).trans
      ((congrArg
        (fun v : π₁ᵉᵗ(ξ k Ω) =>
          (suppliedGaloisEquivFundamentalGroup k κ).symm
            ((fieldFiberExtensionIso k κ Ω).symm.conjAut v))
        hvalue).trans
          ((extendedFieldCoefficient_restrict k E κ Ω
            (pointedFundamentalGroupHom c y (ξ E Ω) hy g)).trans
              (congrArg
                (fun σ : κ ≃ₐ[E] κ => σ.restrictScalars k)
                (coefficientProjection_eq_pointed E κ Ω c y hy g).symm)))

end Tower
end AnabelianGeometry.ArithmeticIsomorphisms
