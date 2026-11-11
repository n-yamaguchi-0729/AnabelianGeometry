/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticNaturality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceBasePointComparison
public import Nyll.GaloisCohomology.Topology.FiniteFieldAbelian

/-!
# Arithmetic maps over an actual extension of the base field

The two arithmetic maps use independently chosen comparisons of fiber functors.
For a commuting scheme square over a tower of fields, their discrepancy is one
explicit, uniform inner conjugation. The actual scheme morphism and geometric
point are retained throughout.

-/

@[expose] public section

noncomputable section

universe u u₁ u₂ v₁ v₂ w

open CategoryTheory CategoryTheory.PreGaloisCategory

private theorem autHomOfCompIso_trans_target
    {C : Type u₁} [Category.{u₂} C]
    {D : Type v₁} [Category.{v₂} D]
    (H : C ⥤ D)
    {F G : C ⥤ FintypeCat.{w}} {F' : D ⥤ FintypeCat.{w}}
    (t : H ⋙ F' ≅ F) (r : F ≅ G) (σ : Aut F') :
    autHomOfCompIso H (t ≪≫ r) σ =
      r.conjAut (autHomOfCompIso H t σ) := by
  simp only [autHomOfCompIso_apply, Iso.trans_conjAut]

private theorem autHomOfCompIso_whiskerLeft_trans
    {C : Type u₁} [Category.{u₂} C]
    {D : Type v₁} [Category.{v₂} D]
    (H : C ⥤ D)
    {F : C ⥤ FintypeCat.{w}} {F' G' : D ⥤ FintypeCat.{w}}
    (t : F' ≅ G') (r : H ⋙ G' ≅ F) (σ : Aut F') :
    autHomOfCompIso H (Functor.isoWhiskerLeft H t ≪≫ r) σ =
      autHomOfCompIso H r (t.conjAut σ) := by
  simp only [autHomOfCompIso_apply, Iso.trans_conjAut]
  exact congrArg r.conjAut (congrArg Aut.of
    (Functor.map_conjAut
      ((Functor.whiskeringLeft C D FintypeCat.{w}).obj H) t σ).symm)

namespace AlgebraicGeometry.FiniteEtale

/-- Evaluate the arithmetic map in the canonical automorphism group. This
helper unfolds only the arithmetic map and its chosen field identification. -/
private theorem absoluteGaloisToFiberAut_arithmeticFundamentalGroupHom
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsSepClosure k K] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X) (γ : π₁ᵉᵗ(xi)) :
    absoluteGaloisToFiberAutMulEquiv k K ‹IsSepClosed K›
        (arithmeticFundamentalGroupHom k K f xi γ) =
      ((nonempty_fiber_iso (xi ≫ f) (ξ k K)).some).conjAut
        (fundamentalGroupHom f xi γ) := by
  let t : fiber (xi ≫ f) ≅ fib k K :=
    (nonempty_fiber_iso (xi ≫ f) (ξ k K)).some
  change (toAutHomeo (fib k K) (K ≃ₐ[k] K))
      ((toAutHomeo (fib k K) (K ≃ₐ[k] K)).symm
        ((continuousConjAut t) (fundamentalGroupHom f xi γ))) = _
  exact (toAutHomeo (fib k K) (K ≃ₐ[k] K)).apply_symm_apply _

/-- For an actual scheme square over `k → E`, restriction of the arithmetic
map over `E` agrees, up to one uniform inner conjugation, with the arithmetic
map over `k` composed with the actual pointed fundamental-group map.

The conjugator is obtained from the two fiber-functor comparisons; no
comparison equation or arithmetic-preservation hypothesis is supplied. -/
theorem arithmeticFundamentalGroupHom_fieldExtension_conjugate
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ]
    [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosure E κ]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (c : Y ⟶ Spec (.of E))
    (a : Y ⟶ X)
    (ha : a ≫ f = c ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xiY : Spec (.of Ω) ⟶ Y) :
    ∃ α : Gal(κ/k), ∀ γ : π₁ᵉᵗ(xiY),
      (arithmeticFundamentalGroupHom E κ c xiY γ).restrictScalars k =
        α * arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
          (fundamentalGroupHom a xiY γ) * α⁻¹ := by
  let : IsSepClosed κ := IsSepClosure.sep_closed k
  let b : Spec (.of E) ⟶ Spec (.of k) := ξ k E
  let z : Spec (.of Ω) ⟶ Spec (.of E) := xiY ≫ c
  let H := pullback b
  let eE : Gal(κ/E) ≃* Aut (fib E κ) :=
    absoluteGaloisToFiberAutMulEquiv E κ (IsSepClosure.sep_closed k)
  let eK : Gal(κ/k) ≃* Aut (fib k κ) :=
    absoluteGaloisToFiberAutMulEquiv k κ (IsSepClosure.sep_closed k)
  let tE : fiber z ≅ fib E κ :=
    (nonempty_fiber_iso z (ξ E κ)).some
  let tK : fiber (z ≫ b) ≅ fib k κ :=
    (nonempty_fiber_iso (z ≫ b) (ξ k κ)).some
  let r : H ⋙ fib E κ ≅ fib k κ := fieldPullbackFiberIso k E κ
  let T₁ : H ⋙ fiber z ≅ fib k κ := pullbackFiberIso b z ≪≫ tK
  let T₂ : H ⋙ fiber z ≅ fib k κ := Functor.isoWhiskerLeft H tE ≪≫ r
  let β : Aut (fib k κ) := Aut.of (T₁.symm ≪≫ T₂)
  let α : Gal(κ/k) := eK.symm β
  have hE (γ : π₁ᵉᵗ(xiY)) :
      eE (arithmeticFundamentalGroupHom E κ c xiY γ) =
        tE.conjAut (fundamentalGroupHom c xiY γ) :=
    absoluteGaloisToFiberAut_arithmeticFundamentalGroupHom E κ c xiY γ
  have hK (δ : π₁ᵉᵗ(z)) :
      eK (arithmeticFundamentalGroupHom k κ b z δ) =
        tK.conjAut (fundamentalGroupHom b z δ) :=
    absoluteGaloisToFiberAut_arithmeticFundamentalGroupHom k κ b z δ
  have hT₁ (δ : π₁ᵉᵗ(z)) :
      autHomOfCompIso H T₁ δ =
        eK (arithmeticFundamentalGroupHom k κ b z δ) := by
    exact (autHomOfCompIso_trans_target H (pullbackFiberIso b z) tK δ).trans
      (hK δ).symm
  have hcore (γ : π₁ᵉᵗ(xiY)) :
      eK ((arithmeticFundamentalGroupHom E κ c xiY γ).restrictScalars k) =
        MulAut.conj β
          (eK (arithmeticFundamentalGroupHom k κ b z
            (fundamentalGroupHom c xiY γ))) := by
    calc
      eK ((arithmeticFundamentalGroupHom E κ c xiY γ).restrictScalars k) =
          autHomOfCompIso H r
            (eE (arithmeticFundamentalGroupHom E κ c xiY γ)) :=
        (fieldFundamentalGroupHom_toAutMulEquiv k E κ
          (arithmeticFundamentalGroupHom E κ c xiY γ)).symm
      _ = autHomOfCompIso H T₂ (fundamentalGroupHom c xiY γ) := by
        rw [hE]
        exact (autHomOfCompIso_whiskerLeft_trans H tE r
          (fundamentalGroupHom c xiY γ)).symm
      _ = MulAut.conj β (autHomOfCompIso H T₁
          (fundamentalGroupHom c xiY γ)) :=
        autHomOfCompIso_eq_conj H T₁ T₂ (fundamentalGroupHom c xiY γ)
      _ = MulAut.conj β
          (eK (arithmeticFundamentalGroupHom k κ b z
            (fundamentalGroupHom c xiY γ))) := by rw [hT₁]
  have ha' : a ≫ f = c ≫ b := ha
  have harithmetic (γ : π₁ᵉᵗ(xiY)) :
      arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
          (fundamentalGroupHom a xiY γ) =
        arithmeticFundamentalGroupHom k κ b z
          (fundamentalGroupHom c xiY γ) := by
    calc
      arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
          (fundamentalGroupHom a xiY γ) =
          arithmeticFundamentalGroupHom k κ (a ≫ f) xiY γ :=
        arithmeticFundamentalGroupHom_comp k κ a f xiY γ
      _ = arithmeticFundamentalGroupHom k κ (c ≫ b) xiY γ := by rw [ha']
      _ = arithmeticFundamentalGroupHom k κ b z
          (fundamentalGroupHom c xiY γ) :=
        (arithmeticFundamentalGroupHom_comp k κ c b xiY γ).symm
  refine ⟨α, fun γ => ?_⟩
  rw [harithmetic]
  have h := congrArg eK.symm (hcore γ)
  simpa only [MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.symm_apply_apply, α] using h

/-- Over a finite field the original arithmetic extension square is strict:
the comparison conjugator disappears in its abelian absolute Galois group.
Thus a cover's full-constant marking restricts to the original base marking. -/
theorem arithmeticFundamentalGroupHom_fieldExtension_of_finite_base
    (k E κ : Type u) [Field k] [Finite k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosure E κ]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (c : Y ⟶ Spec (.of E))
    (a : Y ⟶ X)
    (ha : a ≫ f = c ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xiY : Spec (.of Ω) ⟶ Y) (γ : π₁ᵉᵗ(xiY)) :
    (arithmeticFundamentalGroupHom E κ c xiY γ).restrictScalars k =
      arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
        (fundamentalGroupHom a xiY γ) := by
  obtain ⟨α, hα⟩ :=
    arithmeticFundamentalGroupHom_fieldExtension_conjugate k E κ f c a ha xiY
  exact (hα γ).trans (GaloisCohomology.galois_conjugation_eq_of_finite_base k κ α _)

/-- Over finite constants, every actual fiber-functor comparison preserves
the arithmetic marking exactly. The two choices on the field fiber differ
by inner conjugation, which is trivial in the original finite-field Galois
group. This applies in particular when repointing a cover at its own native
function-field closure. -/
theorem arithmeticFundamentalGroupHom_fiberIso_of_finite_base
    (k κ : Type u) [Field k] [Finite k] [Field κ]
    [Algebra k κ] [IsSepClosure k κ]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X)
    (t : fiber x ≅ fiber y) (g : π₁ᵉᵗ(x)) :
    arithmeticFundamentalGroupHom k κ f y ((continuousConjAut t) g) =
      arithmeticFundamentalGroupHom k κ f x g := by
  have : IsSepClosed κ := IsSepClosure.sep_closed k
  let E := absoluteGaloisToFiberAutMulEquiv k κ (inferInstance : IsSepClosed κ)
  let tx : fiber (x ≫ f) ≅ fib k κ := (nonempty_fiber_iso (x ≫ f) (ξ k κ)).some
  let ty : fiber (y ≫ f) ≅ fib k κ := (nonempty_fiber_iso (y ≫ f) (ξ k κ)).some
  let u : fiber (x ≫ f) ≅ fiber (y ≫ f) :=
    (pullbackFiberIso f x).symm ≪≫ Functor.isoWhiskerLeft (pullback f) t ≪≫
      pullbackFiberIso f y
  have hn := fundamentalGroupHom_conjAut f x y t g
  have hc := fundamentalGroupIsoOfFiberIso_eq_conj
    (x ≫ f) (ξ k κ) tx (u ≪≫ ty) (fundamentalGroupHom f x g)
  have hcomm := congrArg E (GaloisCohomology.galois_conjugation_eq_of_finite_base k κ
    (E.symm (Aut.of (tx.symm ≪≫ (u ≪≫ ty))))
    (E.symm (tx.conjAut (fundamentalGroupHom f x g))))
  simp only [map_mul, map_inv, E.apply_symm_apply] at hcomm
  apply E.injective
  calc
    E (arithmeticFundamentalGroupHom k κ f y ((continuousConjAut t) g)) =
        ty.conjAut (fundamentalGroupHom f y (t.conjAut g)) :=
      absoluteGaloisToFiberAut_arithmeticFundamentalGroupHom k κ f y _
    _ = (u ≪≫ ty).conjAut (fundamentalGroupHom f x g) := by
      rw [Iso.trans_conjAut]
      exact congrArg ty.conjAut hn.symm
    _ = tx.conjAut (fundamentalGroupHom f x g) := hc.trans hcomm
    _ = E (arithmeticFundamentalGroupHom k κ f x g) :=
      (absoluteGaloisToFiberAut_arithmeticFundamentalGroupHom k κ f x g).symm

/-- The actual field-extension square preserves exactly the geometric kernel. -/
theorem arithmeticFundamentalGroupHom_fieldExtension_ker_comap
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ]
    [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosure E κ]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (c : Y ⟶ Spec (.of E))
    (a : Y ⟶ X)
    (ha : a ≫ f = c ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xiY : Spec (.of Ω) ⟶ Y) :
    (arithmeticFundamentalGroupHom k κ f (xiY ≫ a)).ker.comap
        (fundamentalGroupHom a xiY).toMonoidHom =
      (arithmeticFundamentalGroupHom E κ c xiY).ker := by
  obtain ⟨α, hα⟩ :=
    arithmeticFundamentalGroupHom_fieldExtension_conjugate k E κ f c a ha xiY
  ext γ
  change arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
      (fundamentalGroupHom a xiY γ) = 1 ↔
    arithmeticFundamentalGroupHom E κ c xiY γ = 1
  constructor
  · intro hγ
    have hr : (arithmeticFundamentalGroupHom E κ c xiY γ).restrictScalars k = 1 := by
      rw [hα γ, hγ]
      simpa only [mul_one] using mul_inv_cancel α
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun z : Gal(κ/k) => z x) hr
  · intro hγ
    have hc : α * arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
        (fundamentalGroupHom a xiY γ) * α⁻¹ = 1 := by
      rw [← hα γ, hγ]
      rfl
    have h := congrArg (fun z : Gal(κ/k) => α⁻¹ * z * α) hc
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one,
      mul_inv_cancel_left, one_mul] using h

/-- Once the actual full constant fields have been identified inside the
same closure, the original marked covering-group square preserves their
native arithmetic maps strictly. Injectivity of scalar restriction removes
any need to choose another arithmetic marking on the covering groups. -/
theorem arithmeticFundamentalGroupHom_fullConstant_cover_marked
    (k E κ : Type u) [Field k] [Finite k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosure E κ]
    {S T A B : Scheme.{u}}
    (fS : S ⟶ Spec (.of k)) (fT : T ⟶ Spec (.of k))
    (cA : A ⟶ Spec (.of E)) (cB : B ⟶ Spec (.of E))
    (a : A ⟶ S) (b : B ⟶ T)
    (ha : a ≫ fS = cA ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    (hb : b ≫ fT = cB ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    {ΩA ΩB : Type u} [Field ΩA] [IsSepClosed ΩA] [Field ΩB] [IsSepClosed ΩB]
    (x : Spec (.of ΩA) ⟶ A) (y : Spec (.of ΩB) ⟶ B)
    (e : π₁ᵉᵗ(x ≫ a) → π₁ᵉᵗ(y ≫ b))
    (he : ∀ z, arithmeticFundamentalGroupHom k κ fT (y ≫ b) (e z) =
      arithmeticFundamentalGroupHom k κ fS (x ≫ a) z)
    (r : π₁ᵉᵗ(x) → π₁ᵉᵗ(y))
    (hr : ∀ z, fundamentalGroupHom b y (r z) = e (fundamentalGroupHom a x z))
    (z : π₁ᵉᵗ(x)) :
    arithmeticFundamentalGroupHom E κ cB y (r z) =
      arithmeticFundamentalGroupHom E κ cA x z := by
  have h : (arithmeticFundamentalGroupHom E κ cB y (r z)).restrictScalars k =
      (arithmeticFundamentalGroupHom E κ cA x z).restrictScalars k := by
    rw [arithmeticFundamentalGroupHom_fieldExtension_of_finite_base k E κ fT cB b hb,
      hr, he, ← arithmeticFundamentalGroupHom_fieldExtension_of_finite_base k E κ fS cA a ha]
  apply AlgEquiv.ext
  intro w
  exact congrArg (fun σ : Gal(κ/k) => σ w) h

/-- Repointing the base of an actual full-constant cover preserves the same
geometric kernel. This identifies the native full-constant first quotient
with the quotient used by descent to a fixed original base point. -/
theorem arithmeticFundamentalGroupHom_fieldExtension_fiberIso_ker
    (k E κ : Type u) [Field k] [Finite k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosure E κ]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (c : Y ⟶ Spec (.of E)) (a : Y ⟶ X)
    (ha : a ≫ f = c ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    (y : Spec (.of Ω) ⟶ Y) (t : Spec (.of Ω') ⟶ X)
    (s : fiber (y ≫ a) ≅ fiber t) :
    ((arithmeticFundamentalGroupHom k κ f t).comp
      (autHomOfCompIso (pullback a) (pullbackFiberIso a y ≪≫ s))).toMonoidHom.ker =
      (arithmeticFundamentalGroupHom E κ c y).toMonoidHom.ker := by
  have hk := arithmeticFundamentalGroupHom_fieldExtension_ker_comap k E κ f c a ha y
  apply Subgroup.ext
  intro z
  have hm : arithmeticFundamentalGroupHom k κ f t
        (autHomOfCompIso (pullback a) (pullbackFiberIso a y ≪≫ s) z) =
      arithmeticFundamentalGroupHom k κ f (y ≫ a) (fundamentalGroupHom a y z) := by
    rw [autHomOfCompIso_apply, Iso.trans_conjAut]
    exact arithmeticFundamentalGroupHom_fiberIso_of_finite_base k κ f (y ≫ a) t s
      (fundamentalGroupHom a y z)
  change arithmeticFundamentalGroupHom k κ f t
      (autHomOfCompIso (pullback a) (pullbackFiberIso a y ≪≫ s) z) = 1 ↔
    arithmeticFundamentalGroupHom E κ c y z = 1
  rw [hm]
  exact SetLike.ext_iff.mp hk z

end AlgebraicGeometry.FiniteEtale
