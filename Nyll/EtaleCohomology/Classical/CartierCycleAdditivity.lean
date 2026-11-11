/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.EtaleCohomology.Classical.CartierGenericUnitLocalSections
public import Nyll.EtaleCohomology.Classical.CartierGenericUnitSections
public import Nyll.EtaleCohomology.Classical.ZariskiH0Ext
public import Nyll.SchemeTheory.Divisors.CartierProducts
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Additivity of the original Cartier cycle class

The product ideal of two effective Cartier divisors has the product of
their actual local equations. Its section in the original generic-unit
quotient is their sum. Applying the original connecting homomorphisms
therefore proves additivity in H¹(Gm) and H²(μₙ), in any dimension.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace EtaleCohomology

/-- Multiplication of actual nonzero regular equations is multiplication
of their original function-field units. -/
theorem openSectionRationalUnit_mul
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
    (f g : Γ(X, U)) (hf : f ≠ 0) (hg : g ≠ 0) :
    openSectionRationalUnit X U (f * g) (mul_ne_zero hf hg) =
      openSectionRationalUnit X U f hf * openSectionRationalUnit X U g hg := by
  apply Units.ext
  exact map_mul (X.germToFunctionField U).hom f g

/-- The original generic-unit quotient sends a product of local
equations to the sum of their actual classes. -/
theorem openSectionGenericUnitQuotient_mul
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
    (f g : Γ(X, U)) (hf : f ≠ 0) (hg : g ≠ 0) :
    openSectionGenericUnitQuotient X U (f * g) (mul_ne_zero hf hg) =
      openSectionGenericUnitQuotient X U f hf +
        openSectionGenericUnitQuotient X U g hg := by
  unfold openSectionGenericUnitQuotient
  rw [openSectionRationalUnit_mul X U f g hf hg]
  exact map_add (genericPointRationalUnitQuotientHom X ((zariskiToEtale X).obj U))
    (Additive.ofMul (openSectionRationalUnit X U f hf))
    (Additive.ofMul (openSectionRationalUnit X U g hg))

/-- The actual section attached to the product ideal is the sum of the
two original H⁰ classes. All local compatibility is proved from the
actual ideal-sheaf restriction maps. -/
theorem effectiveCartierGenericUnitH0_mul
    {X : Scheme.{u}} [IsIntegral X] (D E : Scheme.EffectiveCartierDivisor X) :
    effectiveCartierGenericUnitH0 ⟨D.1 * E.1, D.2.mul E.2⟩ =
      effectiveCartierGenericUnitH0 D + effectiveCartierGenericUnitH0 E := by
  apply etaleAbelianH0_ext_zariski X (etaleGenericUnitQuotient X)
  intro x
  obtain ⟨U, hxU, f, hf, hD⟩ := D.2 x
  obtain ⟨V, hxV, g, hg, hE⟩ := E.2 x
  obtain ⟨W, hW, hxW, hWUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := U.1 ⊓ V.1)
      (x := x) ⟨hxU, hxV⟩
  have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hf0 : f ≠ 0 := hf.ne_zero
  have hg0 : g ≠ 0 := hg.ne_zero
  let a : W ≤ U.1 := hWUV.trans inf_le_left
  let b : W ≤ V.1 := hWUV.trans inf_le_right
  let fW : Γ(X, W) := X.presheaf.map (homOfLE a).op f
  let gW : Γ(X, W) := X.presheaf.map (homOfLE b).op g
  have hfW : fW ≠ 0 := openSectionRestriction_ne_zero X a f hf0
  have hgW : gW ≠ 0 := openSectionRestriction_ne_zero X b g hg0
  have hDW : D.1.ideal ⟨W, hW⟩ = Ideal.span {fW} := by
    rw [← D.1.map_ideal (U := ⟨W, hW⟩) (V := U) a, hD,
      Ideal.map_span, Set.image_singleton]
    rfl
  have hEW : E.1.ideal ⟨W, hW⟩ = Ideal.span {gW} := by
    rw [← E.1.map_ideal (U := ⟨W, hW⟩) (V := V) b, hE,
      Ideal.map_span, Set.image_singleton]
    rfl
  have hDEW : (D.1 * E.1).ideal ⟨W, hW⟩ = Ideal.span {fW * gW} := by
    change D.1.ideal ⟨W, hW⟩ * E.1.ideal ⟨W, hW⟩ = _
    rw [hDW, hEW, Ideal.span_singleton_mul_span_singleton]
  refine ⟨W, hxW, ?_⟩
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let ev : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      (etaleGenericUnitQuotient X).obj.obj (op ((zariskiToEtale X).obj W)) :=
    ((etaleGenericUnitQuotient X).obj.map
      (hT.from ((zariskiToEtale X).obj W)).op).hom.comp
        (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X) hT).toAddMonoidHom
  change ev (effectiveCartierGenericUnitH0 ⟨D.1 * E.1, D.2.mul E.2⟩) =
    ev (effectiveCartierGenericUnitH0 D + effectiveCartierGenericUnitH0 E)
  have hprod : ev (effectiveCartierGenericUnitH0 ⟨D.1 * E.1, D.2.mul E.2⟩) =
      openSectionGenericUnitQuotient X W (fW * gW) (mul_ne_zero hfW hgW) :=
    effectiveCartierGenericUnitH0_section
      ⟨D.1 * E.1, D.2.mul E.2⟩ ⟨W, hW⟩ (fW * gW) (mul_ne_zero hfW hgW) hDEW
  have hsecD : ev (effectiveCartierGenericUnitH0 D) =
      openSectionGenericUnitQuotient X W fW hfW :=
    effectiveCartierGenericUnitH0_section D ⟨W, hW⟩ fW hfW hDW
  have hsecE : ev (effectiveCartierGenericUnitH0 E) =
      openSectionGenericUnitQuotient X W gW hgW :=
    effectiveCartierGenericUnitH0_section E ⟨W, hW⟩ gW hgW hEW
  exact hprod.trans
    ((openSectionGenericUnitQuotient_mul X W fW gW hfW hgW).trans
      ((congrArg₂
        (fun q r : (etaleGenericUnitQuotient X).obj.obj
          (op ((zariskiToEtale X).obj W)) => q + r) hsecD.symm hsecE.symm).trans
        (ev.map_add (effectiveCartierGenericUnitH0 D)
          (effectiveCartierGenericUnitH0 E)).symm))

/-- Additivity of the native generic-unit connecting class. -/
theorem effectiveCartierMultiplicativeGroupH1_mul
    {X : Scheme.{u}} [IsIntegral X] (D E : Scheme.EffectiveCartierDivisor X) :
    effectiveCartierMultiplicativeGroupH1 ⟨D.1 * E.1, D.2.mul E.2⟩ =
      effectiveCartierMultiplicativeGroupH1 D +
        effectiveCartierMultiplicativeGroupH1 E := by
  let δ : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 :=
    Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl
  exact (congrArg δ (effectiveCartierGenericUnitH0_mul D E)).trans
    (δ.map_add (effectiveCartierGenericUnitH0 D) (effectiveCartierGenericUnitH0 E))

/-- Additivity of the original roots-of-unity Cartier class. -/
theorem effectiveCartierCycleClass_mul
    {X : Scheme.{u}} [IsIntegral X] (D E : Scheme.EffectiveCartierDivisor X)
    {n : ℕ} (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    effectiveCartierCycleClass ⟨D.1 * E.1, D.2.mul E.2⟩ hn hnX =
      effectiveCartierCycleClass D hn hnX + effectiveCartierCycleClass E hn hnX := by
  let δ : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 →+
      Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 2 :=
    Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) 1 2 rfl
  exact (congrArg δ (effectiveCartierMultiplicativeGroupH1_mul D E)).trans
    (δ.map_add (effectiveCartierMultiplicativeGroupH1 D)
      (effectiveCartierMultiplicativeGroupH1 E))

end EtaleCohomology
