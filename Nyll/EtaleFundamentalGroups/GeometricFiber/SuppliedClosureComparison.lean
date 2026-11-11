/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSeparableComparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceBasePointComparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction

/-!
# The native generic point and the supplied separable closure

An actual equivalence of separable closures defines extension of geometric
points. Its literal point action intertwines the two original Galois actions.
The pullback-fiber comparison then identifies the native generic Galois map
with the original field-source map for the supplied closure. The comparison
is constructed from these maps, rather than supplied as an additional datum.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

universe u

section Fields

variable {K Ω₀ Ω : Type u} [Field K] [Field Ω₀] [Field Ω]
  [Algebra K Ω₀] [Algebra K Ω] [IsSepClosure K Ω₀] [IsSepClosure K Ω]
  [IsSepClosed Ω₀] [IsSepClosed Ω]

/-- The actual extension of field-valued points along a specified
equivalence of separable closures. -/
def suppliedClosureFieldFiberIso (e : Ω₀ ≃ₐ[K] Ω) : fib K Ω₀ ≅ fib K Ω := by
  let : Algebra Ω₀ Ω := e.toRingHom.toAlgebra
  have : IsScalarTower K Ω₀ Ω :=
    IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  exact fieldFiberExtensionIso K Ω₀ Ω

/-- Extension of the actual field-valued points carries an automorphism
to its literal conjugate by the specified closure equivalence. -/
theorem suppliedClosureFieldFiberIso_galois
    (e : Ω₀ ≃ₐ[K] Ω) (σ : Gal(Ω₀/K)) :
    (suppliedClosureFieldFiberIso e).conjAut
        (suppliedGaloisEquivFundamentalGroup K Ω₀ σ) =
      suppliedGaloisEquivFundamentalGroup K Ω (AlgEquiv.autCongr e σ) := by
  let : Algebra Ω₀ Ω := e.toRingHom.toAlgebra
  have : IsScalarTower K Ω₀ Ω :=
    IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  let τ := AlgEquiv.autCongr e σ
  have hτ : τ.toRingHom.comp (algebraMap Ω₀ Ω) =
      (algebraMap Ω₀ Ω).comp σ.toRingHom := by
    apply RingHom.ext
    intro a
    change e (σ (e.symm (e a))) = e (σ a)
    rw [e.symm_apply_apply]
  change absoluteGaloisToExtendedFiberAut K Ω₀ Ω σ =
    suppliedGaloisEquivFundamentalGroup K Ω τ
  apply Aut.ext
  ext Z z
  apply (fiberObjEquivHom (ξ K Ω) Z).injective
  ext1
  exact (absoluteGaloisToExtendedFiberAut_point K Ω₀ Ω σ τ.toRingHom hτ Z z).trans
    (suppliedGaloisEquivFundamentalGroup_point K Ω τ Z z).symm

end Fields

section Generic

variable (X : Scheme.{u}) [IsIntegral X]
  (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
  [IsSepClosure X.functionField Ω] [IsSepClosed Ω]

/-- The native algebraic-closure generic fiber is compared with the
original supplied-closure generic fiber by actual extension of points. -/
def nativeToSuppliedGenericFiberIso :
    fiber (X.genericExtensionMorphism (AlgebraicClosure X.functionField)) ≅
      fiber (X.genericExtensionMorphism Ω) :=
  (genericSeparableFiberIso X).symm ≪≫
    (pullbackFiberIso (X.fromSpecStalk (genericPoint X))
      (ξ X.functionField (SeparableClosure X.functionField))).symm ≪≫
    Functor.isoWhiskerLeft (pullback (X.fromSpecStalk (genericPoint X)))
      (suppliedClosureFieldFiberIso (K := X.functionField)
        (Ω₀ := SeparableClosure X.functionField) (Ω := Ω)
        (IsSepClosure.equiv X.functionField (SeparableClosure X.functionField) Ω)) ≪≫
    pullbackFiberIso (X.fromSpecStalk (genericPoint X)) (ξ X.functionField Ω)

/-- The induced isomorphism retains the original generic points. -/
def nativeToSuppliedGenericGroupEquiv :
    π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField)) ≃ₜ*
      π₁ᵉᵗ(X.genericExtensionMorphism Ω) :=
  continuousConjAut (nativeToSuppliedGenericFiberIso X Ω)

/-- The constructed comparison intertwines the actual native generic
Galois map and the actual original field-source map, on every automorphism. -/
theorem nativeToSuppliedGenericGroupEquiv_galois
    (σ : Gal(SeparableClosure X.functionField/X.functionField)) :
    nativeToSuppliedGenericGroupEquiv X Ω (genericAbsoluteGaloisHom X σ) =
      fieldSourceAbsoluteGaloisHom X.functionField Ω
        (X.fromSpecStalk (genericPoint X))
        (AlgEquiv.autCongr
          (IsSepClosure.equiv X.functionField (SeparableClosure X.functionField) Ω) σ) := by
  let K : Type u := X.functionField
  let j : Spec (.of K) ⟶ X := X.fromSpecStalk (genericPoint X)
  let e := IsSepClosure.equiv K (SeparableClosure K) Ω
  let t : fib K (SeparableClosure K) ≅ fib K Ω :=
    suppliedClosureFieldFiberIso (K := K) (Ω₀ := SeparableClosure K) (Ω := Ω) e
  let a := suppliedGaloisEquivFundamentalGroup K (SeparableClosure K) σ
  let b := fundamentalGroupHom j (ξ K (SeparableClosure K)) a
  let s : fiber (ξ K (SeparableClosure K) ≫ j) ≅
      fiber (X.genericExtensionMorphism (AlgebraicClosure X.functionField)) :=
    genericSeparableFiberIso X
  let r : fiber (ξ K (SeparableClosure K) ≫ j) ≅ fiber (ξ K Ω ≫ j) :=
    (pullbackFiberIso j (ξ K (SeparableClosure K))).symm ≪≫
      Functor.isoWhiskerLeft (pullback j) t ≪≫ pullbackFiberIso j (ξ K Ω)
  have ha : a = toAut (fib K (SeparableClosure K)) Gal(SeparableClosure K/K) σ :=
    toAutHomeo_apply (fib K (SeparableClosure K)) σ
  have hnative : genericAbsoluteGaloisHom X σ = s.conjAut b := by
    change genericAbsoluteGaloisHom X σ = (genericSeparableFiberIso X).conjAut
      (fundamentalGroupHom j (ξ K (SeparableClosure K)) a)
    rw [ha]
    exact genericAbsoluteGaloisHom_eq_separable X σ
  have hcancel : s.symm.conjAut (s.conjAut b) = b := s.conjAut.symm_apply_apply b
  have hn : s.symm.conjAut (genericAbsoluteGaloisHom X σ) = b :=
    (congrArg s.symm.conjAut hnative).trans hcancel
  have hconj : r.conjAut b = fundamentalGroupHom j (ξ K Ω) (t.conjAut a) :=
    fundamentalGroupHom_conjAut j (ξ K (SeparableClosure K)) (ξ K Ω) t a
  have hgalois : t.conjAut a = suppliedGaloisEquivFundamentalGroup K Ω
      (AlgEquiv.autCongr e σ) := suppliedClosureFieldFiberIso_galois e σ
  change (s.symm ≪≫ r).conjAut (genericAbsoluteGaloisHom X σ) = _
  exact (Iso.trans_conjAut s.symm r (genericAbsoluteGaloisHom X σ)).trans
    ((congrArg r.conjAut hn).trans
      (hconj.trans (congrArg (fundamentalGroupHom j (ξ K Ω)) hgalois)))

end Generic

end AlgebraicGeometry.FiniteEtale
