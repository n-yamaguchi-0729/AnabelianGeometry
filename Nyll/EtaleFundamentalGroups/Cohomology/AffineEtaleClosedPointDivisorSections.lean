/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Nyll.EtaleFundamentalGroups.Cohomology.AffineClosedPointDivisorComparison

/-!
# Closed-point divisor sections on affine étale objects

For an affine étale domain over a Dedekind base, sections of the actual
closed-point divisor sheaf are described by finitely supported coefficients
on the height-one points of the affine source.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open IsDedekindDomain
universe u
namespace EtaleCohomology

variable {R S : Type u} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]

/-- The closed base point and fiber point associated with a height-one point
of an affine étale Dedekind domain. -/
noncomputable def affineEtaleClosedPointFiberPointEquivHeightOne
    (hR : ¬ IsField R) :
    (Σ x : closedPoints (Spec (CommRingCat.of R)),
      closedPointResidueFiber (Spec (CommRingCat.of R)) x
        (affineEtaleSpecObject (R := R) (S := S))) ≃ HeightOneSpectrum S := by
  let eR := HeightOneSpectrum.equivClosedPoints hR
  let c := fun v : HeightOneSpectrum S =>
    eR (heightOneSpectrumContractionOfEtale (R := R) (S := S) v)
  let eF (x : closedPoints (Spec (CommRingCat.of R))) :=
    affineEtaleClosedPointResidueFiberEquivHeightOneFiber
      (R := R) (S := S) hR x
  let e₀ (x : closedPoints (Spec (CommRingCat.of R))) :
      closedPointResidueFiber (Spec (CommRingCat.of R)) x
        (affineEtaleSpecObject (R := R) (S := S)) ≃ {v : HeightOneSpectrum S // c v = x} := {
    toFun y := ⟨(eF x y).1, by
      change eR (heightOneSpectrumContractionOfEtale (R := R) (S := S)
        (eF x y).1) = x
      rw [(eF x y).2]
      exact eR.apply_symm_apply x⟩
    invFun v := eF x |>.symm ⟨v.1, by
      apply eR.injective
      change eR (heightOneSpectrumContractionOfEtale (R := R) (S := S) v.1) = x
      exact v.2⟩
    left_inv y := by simp [eF]
    right_inv v := by
      apply Subtype.ext
      change ((eF x) ((eF x).symm ⟨v.1, by
        apply eR.injective
        change eR (heightOneSpectrumContractionOfEtale (R := R) (S := S) v.1) = x
        exact v.2⟩)).1 = v.1
      exact congrArg Subtype.val ((eF x).apply_symm_apply ⟨v.1, by
        apply eR.injective
        change eR (heightOneSpectrumContractionOfEtale (R := R) (S := S) v.1) = x
        exact v.2⟩)
  }
  exact (Equiv.sigmaCongrRight e₀).trans (Equiv.sigmaFiberEquiv c)

/-- Return the base closed point and its fiber point corresponding to a
height-one point of the affine étale source. -/
noncomputable def affineEtaleHeightOneToClosedPointFiber
    (hR : ¬ IsField R) (v : HeightOneSpectrum S) :
    Σ x : closedPoints (Spec (CommRingCat.of R)),
      closedPointResidueFiber (Spec (CommRingCat.of R)) x
        (affineEtaleSpecObject (R := R) (S := S)) :=
  (affineEtaleClosedPointFiberPointEquivHeightOne (R := R) (S := S) hR).symm v

/-- Every point of a closed fiber is the point attached to its corresponding
height-one point. -/
theorem affineEtaleHeightOneToClosedPointFiber_of_fiberPoint
    (hR : ¬ IsField R) (x : closedPoints (Spec (CommRingCat.of R)))
    (y : closedPointResidueFiber (Spec (CommRingCat.of R)) x
      (affineEtaleSpecObject (R := R) (S := S))) :
    affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR
      (affineEtaleClosedPointResidueFiberEquivHeightOneFiber
        (R := R) (S := S) hR x y).1 = ⟨x, y⟩ := by
  exact Equiv.symm_apply_apply
    (affineEtaleClosedPointFiberPointEquivHeightOne (R := R) (S := S) hR)
    (⟨x, y⟩ : Σ x, closedPointResidueFiber (Spec (CommRingCat.of R)) x
      (affineEtaleSpecObject (R := R) (S := S)))

theorem affineEtaleClosedPointFiberEquivHeightOne_apply_heightOneToFiber
    (hR : ¬ IsField R) (v : HeightOneSpectrum S) :
    (affineEtaleClosedPointResidueFiberEquivHeightOneFiber
      (R := R) (S := S) hR
      (affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR v).1
      (affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR v).2).1 = v := by
  let eR := HeightOneSpectrum.equivClosedPoints hR
  let x := eR (heightOneSpectrumContractionOfEtale (R := R) (S := S) v)
  let eF := affineEtaleClosedPointResidueFiberEquivHeightOneFiber
    (R := R) (S := S) hR x
  have hc : heightOneSpectrumContractionOfEtale (R := R) (S := S) v = eR.symm x := by
    exact (eR.symm_apply_apply _).symm
  change (eF (eF.symm ⟨v, hc⟩)).1 = v
  exact congrArg Subtype.val (eF.apply_symm_apply ⟨v, hc⟩)

/-- A closed-point summand section with prescribed integer values on the
height-one points in that fiber. -/
noncomputable def affineEtaleClosedPointDivisorSummandSection
    (hR : ¬ IsField R) (x : closedPoints (Spec (CommRingCat.of R)))
    (D : HeightOneSpectrum S →₀ ℤ) :
    (closedPointDivisorSummand (Spec (CommRingCat.of R)) x).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S))) :=
  (closedPointDivisorSummandSectionsAddEquiv (Spec (CommRingCat.of R)) x
    (affineEtaleSpecObject (R := R) (S := S))).symm
    (fun y => ULift.up (D (affineEtaleClosedPointResidueFiberEquivHeightOneFiber
      (R := R) (S := S) hR x y).1))

/-- Reconstruct a section of the actual divisor sheaf from its finitely
supported height-one coefficients. -/
noncomputable def affineEtaleClosedPointDivisorSectionOfFinsupp
    (hR : ¬ IsField R) (D : HeightOneSpectrum S →₀ ℤ) :
    (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S))) := by
  classical
  let X := Spec (CommRingCat.of R)
  let U := affineEtaleSpecObject (R := R) (S := S)
  let T := D.support.image fun v =>
    (affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR v).1
  exact ∑ x ∈ T,
    ConcreteCategory.hom
      ((closedPointDivisorSheafInjection X x).hom.app (op U))
      (affineEtaleClosedPointDivisorSummandSection (R := R) (S := S) hR x D)

/-- Read the coefficient indexed by a height-one point from the corresponding
closed-point summand of the divisor sheaf on `Spec R`, evaluated on
`Spec S`. -/
noncomputable def affineEtaleClosedPointDivisorCoefficient
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (v : HeightOneSpectrum S)
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) : ℤ := by
  let X := Spec (CommRingCat.of R)
  let q := affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR v
  let p := @sheafCoproductComponentProjection (closedPoints X) X
    (closedPointDivisorSummand X) hShape q.1
  exact ((closedPointDivisorSummandSectionsAddEquiv X q.1
    (affineEtaleSpecObject (R := R) (S := S))
    (ConcreteCategory.hom (p.hom.app
      (op (affineEtaleSpecObject (R := R) (S := S)))) s) q.2).down)

/-- The reconstructed affine divisor-sheaf section has the prescribed
height-one coefficients. -/
theorem affineEtaleClosedPointDivisorSectionOfFinsupp_coefficient
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (D : HeightOneSpectrum S →₀ ℤ) (v : HeightOneSpectrum S) :
    affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR v
      (affineEtaleClosedPointDivisorSectionOfFinsupp (R := R) (S := S) hR D) = D v := by
  classical
  let X := Spec (CommRingCat.of R)
  let U := affineEtaleSpecObject (R := R) (S := S)
  let q := affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR v
  let e := affineEtaleClosedPointResidueFiberEquivHeightOneFiber
    (R := R) (S := S) hR q.1
  let p := closedPointDivisorSheafComponentProjection X q.1
  let T := D.support.image fun w =>
    (affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR w).1
  change ((closedPointDivisorSummandSectionsAddEquiv X q.1 U
    (ConcreteCategory.hom (p.hom.app (op U))
      (affineEtaleClosedPointDivisorSectionOfFinsupp (R := R) (S := S) hR D))
    q.2).down) = D v
  dsimp [affineEtaleClosedPointDivisorSectionOfFinsupp, T]
  rw [map_sum]
  rw [Finset.sum_eq_single q.1]
  · dsimp only [p]
    rw [closedPointDivisorSheafComponentProjection_app_injection]
    have hEval := congrArg (fun f => f q.2)
      (AddEquiv.apply_symm_apply
        (closedPointDivisorSummandSectionsAddEquiv X q.1 U)
        (fun y => ULift.up (D (e y).1)))
    have hval := affineEtaleClosedPointFiberEquivHeightOne_apply_heightOneToFiber
      (R := R) (S := S) hR v
    change (e q.2).1 = v at hval
    simpa only [affineEtaleClosedPointDivisorSummandSection, hval]
      using congrArg ULift.down hEval
  · intro x hx hxne
    exact closedPointDivisorSheafComponentProjection_app_injection_of_ne
      hxne U (affineEtaleClosedPointDivisorSummandSection (R := R) (S := S) hR x D)
  · intro hnot
    dsimp only [p]
    rw [closedPointDivisorSheafComponentProjection_app_injection]
    let E := closedPointDivisorSummandSectionsAddEquiv X q.1 U
    apply E.injective
    funext y
    let F := fun z => ULift.up (D (e z).1)
    have heval : E (affineEtaleClosedPointDivisorSummandSection
        (R := R) (S := S) hR q.1 D) y = F y := by
      change E (E.symm F) y = F y
      exact congrArg (fun g => g y) (E.apply_symm_apply F)
    change E (affineEtaleClosedPointDivisorSummandSection
      (R := R) (S := S) hR q.1 D) y = E 0 y
    rw [heval, E.map_zero]
    change ULift.up (D (e y).1) = 0
    apply ULift.ext
    let w := (e y).1
    have hx : (affineEtaleHeightOneToClosedPointFiber
        (R := R) (S := S) hR w).1 = q.1 := by
      change (HeightOneSpectrum.equivClosedPoints hR)
        (heightOneSpectrumContractionOfEtale (R := R) (S := S) w) = q.1
      rw [(e y).2]
      exact (HeightOneSpectrum.equivClosedPoints hR).apply_symm_apply q.1
    by_contra hne
    have hw : w ∈ D.support := Finsupp.mem_support_iff.mpr hne
    exact hnot (Finset.mem_image.mpr ⟨w, hw, hx⟩)

theorem affineEtaleClosedPointDivisorCoefficient_eq_summandValue
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (x : closedPoints (Spec (CommRingCat.of R)))
    (y : closedPointResidueFiber (Spec (CommRingCat.of R)) x
      (affineEtaleSpecObject (R := R) (S := S)))
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR
      (affineEtaleClosedPointResidueFiberEquivHeightOneFiber
        (R := R) (S := S) hR x y).1 s =
    ((closedPointDivisorSummandSectionsAddEquiv
      (Spec (CommRingCat.of R)) x (affineEtaleSpecObject (R := R) (S := S))
      (ConcreteCategory.hom
        ((sheafCoproductComponentProjection (Spec (CommRingCat.of R))
          (closedPointDivisorSummand (Spec (CommRingCat.of R))) x).hom.app
          (op (affineEtaleSpecObject (R := R) (S := S)))) s) y).down) := by
  let v := (affineEtaleClosedPointResidueFiberEquivHeightOneFiber
    (R := R) (S := S) hR x y).1
  let q := affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR v
  have hq := affineEtaleHeightOneToClosedPointFiber_of_fiberPoint
    (R := R) (S := S) hR x y
  let g := fun z : Σ x : closedPoints (Spec (CommRingCat.of R)),
      closedPointResidueFiber (Spec (CommRingCat.of R)) x
        (affineEtaleSpecObject (R := R) (S := S)) =>
      ((closedPointDivisorSummandSectionsAddEquiv
        (Spec (CommRingCat.of R)) z.1 (affineEtaleSpecObject (R := R) (S := S))
        (ConcreteCategory.hom
          ((sheafCoproductComponentProjection (Spec (CommRingCat.of R))
            (closedPointDivisorSummand (Spec (CommRingCat.of R))) z.1).hom.app
            (op (affineEtaleSpecObject (R := R) (S := S)))) s) z.2).down)
  change g q = g ⟨x, y⟩
  exact congrArg g hq

/-- Coefficients at a fixed height-one point are additive. -/
noncomputable def affineEtaleClosedPointDivisorCoefficientAddHom
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (v : HeightOneSpectrum S) :
    ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) →+ ℤ where
  toFun := affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR v
  map_zero' := by
    let X := Spec (CommRingCat.of R)
    let q := affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR v
    let p := @sheafCoproductComponentProjection (closedPoints X) X
      (closedPointDivisorSummand X) hShape q.1
    let E := closedPointDivisorSummandSectionsAddEquiv X q.1
      (affineEtaleSpecObject (R := R) (S := S))
    change (E (ConcreteCategory.hom (p.hom.app
      (op (affineEtaleSpecObject (R := R) (S := S)))) 0) q.2).down = 0
    rw [map_zero, E.map_zero]
    rfl
  map_add' s t := by
    let X := Spec (CommRingCat.of R)
    let q := affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR v
    let p := @sheafCoproductComponentProjection (closedPoints X) X
      (closedPointDivisorSummand X) hShape q.1
    let E := closedPointDivisorSummandSectionsAddEquiv X q.1
      (affineEtaleSpecObject (R := R) (S := S))
    change (E (ConcreteCategory.hom (p.hom.app
      (op (affineEtaleSpecObject (R := R) (S := S)))) (s + t)) q.2).down = _
    have hadd := map_add (ConcreteCategory.hom (p.hom.app
      (op (affineEtaleSpecObject (R := R) (S := S))))) s t
    have hadd' : ConcreteCategory.hom (p.hom.app
        (op (affineEtaleSpecObject (R := R) (S := S)))) (s + t) =
        ConcreteCategory.hom (p.hom.app
          (op (affineEtaleSpecObject (R := R) (S := S)))) s +
        ConcreteCategory.hom (p.hom.app
          (op (affineEtaleSpecObject (R := R) (S := S)))) t := by
      simpa only [closedPointDivisorSheaf] using hadd
    rw [hadd', E.map_add]
    rfl

/-- The coefficient map takes values in finitely supported divisors. Its
support is contained in the finite union of the fibers above the finitely
many closed points occurring in the coproduct decomposition. -/
noncomputable def affineEtaleClosedPointDivisorSectionFinsupp
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    HeightOneSpectrum S →₀ ℤ := by
  classical
  let X := Spec (CommRingCat.of R)
  let U := affineEtaleSpecObject (R := R) (S := S)
  have hQC : QuasiCompact (terminal.from U.left) := by
    change QuasiCompact (terminal.from (Spec (CommRingCat.of S)))
    exact (AlgebraicGeometry.compactSpace_iff_quasiCompact
      (Spec (CommRingCat.of S))).mp inferInstance
  have hLQF : LocallyQuasiFinite U.hom := by
    rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
    intro V W e
    have h : RingHom.Etale (U.hom.appLE V W e).hom :=
      HasRingHomProperty.appLE (P := @Etale) U.hom inferInstance V W e
    algebraize [(U.hom.appLE V W e).hom]
    change Algebra.QuasiFinite _ _
    infer_instance
  have hQS_X : QuasiSeparatedSpace ((Functor.fromPUnit X).obj U.right) := by
    change QuasiSeparatedSpace (Spec (CommRingCat.of R))
    exact quasiSeparatedSpace_of_isAffine (Spec (CommRingCat.of R))
  let hFiberFinite (x : closedPoints X) : Finite (closedPointResidueFiber X x U) :=
    @closedPointResidueFiber_finite X x U hLQF hQC hQS_X
  letI : QuasiSeparatedSpace U.left := by
    change QuasiSeparatedSpace (Spec (CommRingCat.of S))
    exact quasiSeparatedSpace_of_isAffine (Spec (CommRingCat.of S))
  letI : QuasiSeparatedSpace ((Functor.fromPUnit X).obj U.right) := by
    change QuasiSeparatedSpace (Spec (CommRingCat.of R))
    exact quasiSeparatedSpace_of_isAffine (Spec (CommRingCat.of R))
  letI : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) := hShape
  have hfin := closedPointDivisorSheaf_finiteSupport_of_quasiCompact X U s
  let T := Classical.choose hfin
  have hT := Classical.choose_spec hfin
  let f := fun v : HeightOneSpectrum S =>
    affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR v s
  let fiberHeights (x : closedPoints X) : Finset (HeightOneSpectrum S) := by
    letI : Finite (closedPointResidueFiber X x U) :=
      hFiberFinite x
    letI : Fintype (closedPointResidueFiber X x U) := Fintype.ofFinite _
    exact Finset.univ.image fun y =>
      (affineEtaleClosedPointResidueFiberEquivHeightOneFiber
        (R := R) (S := S) hR x y).1
  have hsub : Function.support f ⊆ T.biUnion fiberHeights := by
    intro v hv
    have hvnz : f v ≠ 0 := hv
    let q := affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR v
    let : Finite (closedPointResidueFiber X q.1 U) := hFiberFinite q.1
    let : Fintype (closedPointResidueFiber X q.1 U) := Fintype.ofFinite _
    have hx : q.1 ∈ T := by
      by_contra hnot
      let p := @sheafCoproductComponentProjection (closedPoints X) X
        (closedPointDivisorSummand X) hShape q.1
      have hp : ConcreteCategory.hom (p.hom.app (op U)) s = 0 := by
        rw [hT, map_sum]
        apply Finset.sum_eq_zero
        intro x hxT
        have hne : x ≠ q.1 := fun heq => hnot (heq ▸ hxT)
        exact closedPointDivisorSheafComponentProjection_app_injection_of_ne
          hne U (ConcreteCategory.hom
            ((@sheafCoproductComponentProjection (closedPoints X) X
              (closedPointDivisorSummand X) hShape x).hom.app (op U)) s)
      have hcoeff : f v = 0 := by
        dsimp [f, affineEtaleClosedPointDivisorCoefficient]
        rw [hp]
        simp only [map_zero, Pi.zero_apply]
        rfl
      exact hvnz hcoeff
    simp only [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨q.1, hx, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨q.2, ?_, ?_⟩
    · exact Finset.mem_univ _
    have hc : heightOneSpectrumContractionOfEtale (R := R) (S := S) v =
        (HeightOneSpectrum.equivClosedPoints hR).symm q.1 := by
      dsimp [q, affineEtaleHeightOneToClosedPointFiber]
      exact ((HeightOneSpectrum.equivClosedPoints hR).symm_apply_apply
        (heightOneSpectrumContractionOfEtale (R := R) (S := S) v)).symm
    change (affineEtaleClosedPointResidueFiberEquivHeightOneFiber
      (R := R) (S := S) hR q.1 q.2).1 = v
    dsimp [q, affineEtaleHeightOneToClosedPointFiber]
    exact congrArg Subtype.val (Equiv.apply_symm_apply
      (affineEtaleClosedPointResidueFiberEquivHeightOneFiber
        (R := R) (S := S) hR
        ((HeightOneSpectrum.equivClosedPoints hR)
          (heightOneSpectrumContractionOfEtale (R := R) (S := S) v)))
      ⟨v, hc⟩)
  exact Finsupp.ofSupportFinite f ((T.biUnion fiberHeights).finite_toSet.subset hsub)

/-- The finite coefficient encoding is an additive homomorphism. -/
noncomputable def affineEtaleClosedPointDivisorSectionFinsuppAddHom
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})] :
    ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) →+
      (HeightOneSpectrum S →₀ ℤ) where
  toFun := affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR
  map_zero' := by
    apply Finsupp.ext
    intro v
    exact (affineEtaleClosedPointDivisorCoefficientAddHom
      (R := R) (S := S) hR v).map_zero
  map_add' s t := by
    apply Finsupp.ext
    intro v
    exact (affineEtaleClosedPointDivisorCoefficientAddHom
      (R := R) (S := S) hR v).map_add s t

/-- Equality of all height-one coefficients determines an affine étale section. -/
theorem affineEtaleClosedPointDivisorSectionFinsupp_injective
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    {s t : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))}
    (h : affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR s =
      affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR t) : s = t := by
  classical
  let X := Spec (CommRingCat.of R)
  let U := affineEtaleSpecObject (R := R) (S := S)
  have hQC : QuasiCompact (terminal.from U.left) := by
    change QuasiCompact (terminal.from (Spec (CommRingCat.of S)))
    exact (AlgebraicGeometry.compactSpace_iff_quasiCompact
      (Spec (CommRingCat.of S))).mp inferInstance
  have hLQF : LocallyQuasiFinite U.hom := by
    rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
    intro V W e
    have h' : RingHom.Etale (U.hom.appLE V W e).hom :=
      HasRingHomProperty.appLE (P := @Etale) U.hom inferInstance V W e
    algebraize [(U.hom.appLE V W e).hom]
    change Algebra.QuasiFinite _ _
    infer_instance
  have hQS_X : QuasiSeparatedSpace ((Functor.fromPUnit X).obj U.right) := by
    change QuasiSeparatedSpace (Spec (CommRingCat.of R))
    exact quasiSeparatedSpace_of_isAffine (Spec (CommRingCat.of R))
  let hFiberFinite (x : closedPoints X) : Finite (closedPointResidueFiber X x U) :=
    @closedPointResidueFiber_finite X x U hLQF hQC hQS_X
  have hfinS := closedPointDivisorSheaf_finiteSupport_of_quasiCompact X U s
  have hfinT := closedPointDivisorSheaf_finiteSupport_of_quasiCompact X U t
  let Ts := Classical.choose hfinS
  let Tt := Classical.choose hfinT
  have hTs := Classical.choose_spec hfinS
  have hTt := Classical.choose_spec hfinT
  let T := Ts ∪ Tt
  let component (z : (closedPointDivisorSheaf X).obj.obj (op U)) (x : closedPoints X) :=
    ConcreteCategory.hom
      ((sheafCoproductComponentProjection X (closedPointDivisorSummand X) x).hom.app
        (op U)) z
  let term (z : (closedPointDivisorSheaf X).obj.obj (op U)) (x : closedPoints X) :=
    ConcreteCategory.hom
      ((colimit.ι (Discrete.functor (closedPointDivisorSummand X)) ⟨x⟩).hom.app (op U))
      (component z x)
  have hcomponent (x : closedPoints X) : component s x = component t x := by
    let E := closedPointDivisorSummandSectionsAddEquiv X x U
    apply E.injective
    funext y
    let v := (affineEtaleClosedPointResidueFiberEquivHeightOneFiber
      (R := R) (S := S) hR x y).1
    have hcoeff := congrArg (fun D : HeightOneSpectrum S →₀ ℤ => D v) h
    change affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR v s =
      affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR v t at hcoeff
    rw [affineEtaleClosedPointDivisorCoefficient_eq_summandValue
      (R := R) (S := S) hR x y s,
      affineEtaleClosedPointDivisorCoefficient_eq_summandValue
        (R := R) (S := S) hR x y t] at hcoeff
    exact ULift.ext hcoeff
  have hsum : (∑ x ∈ T, term s x) = ∑ x ∈ T, term t x := by
    apply Finset.sum_congr rfl
    intro x hx
    exact congrArg (ConcreteCategory.hom
      ((colimit.ι (Discrete.functor (closedPointDivisorSummand X)) ⟨x⟩).hom.app (op U)))
      (hcomponent x)
  have hsExtend : (∑ x ∈ T, term s x) = ∑ x ∈ Ts, term s x := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro x hx hxnot
    have hzero' : ConcreteCategory.hom
        ((sheafCoproductComponentProjection X (closedPointDivisorSummand X) x).hom.app
          (op U)) s = 0 := by
      rw [hTs, map_sum]
      apply Finset.sum_eq_zero
      intro x' hx'
      have hne : x' ≠ x := fun heq => hxnot (heq ▸ hx')
      exact closedPointDivisorSheafComponentProjection_app_injection_of_ne
        hne U (component s x')
    have hzero : component s x = 0 := hzero'
    simp [term, hzero]
  have htExtend : (∑ x ∈ T, term t x) = ∑ x ∈ Tt, term t x := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro x hx hxnot
    have hzero' : ConcreteCategory.hom
        ((sheafCoproductComponentProjection X (closedPointDivisorSummand X) x).hom.app
          (op U)) t = 0 := by
      rw [hTt, map_sum]
      apply Finset.sum_eq_zero
      intro x' hx'
      have hne : x' ≠ x := fun heq => hxnot (heq ▸ hx')
      exact closedPointDivisorSheafComponentProjection_app_injection_of_ne
        hne U (component t x')
    have hzero : component t x = 0 := hzero'
    simp [term, hzero]
  have hs : s = ∑ x ∈ T, term s x := hTs.trans hsExtend.symm
  have ht : t = ∑ x ∈ T, term t x := hTt.trans htExtend.symm
  exact hs.trans (hsum.trans ht.symm)

/-- The coefficient encoding is a left inverse to reconstruction. -/
theorem affineEtaleClosedPointDivisorSectionFinsupp_sectionOfFinsupp
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (D : HeightOneSpectrum S →₀ ℤ) :
    affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR
      (affineEtaleClosedPointDivisorSectionOfFinsupp (R := R) (S := S) hR D) = D := by
  apply Finsupp.ext
  intro v
  exact affineEtaleClosedPointDivisorSectionOfFinsupp_coefficient
    (R := R) (S := S) hR D v

/-- Sections of the closed-point divisor sheaf on an affine étale Dedekind
domain are additively equivalent to finitely supported height-one
coefficients. The construction also covers the field case for `S`, where
the closed fibers and height-one spectrum are both empty. -/
noncomputable def affineEtaleClosedPointDivisorSectionFinsuppAddEquiv
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})] :
    ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) ≃+
      (HeightOneSpectrum S →₀ ℤ) :=
  AddEquiv.ofBijective
    (affineEtaleClosedPointDivisorSectionFinsuppAddHom (R := R) (S := S) hR)
    ⟨fun _ _ h => affineEtaleClosedPointDivisorSectionFinsupp_injective
        (R := R) (S := S) hR h,
      fun D => ⟨affineEtaleClosedPointDivisorSectionOfFinsupp
          (R := R) (S := S) hR D,
        affineEtaleClosedPointDivisorSectionFinsupp_sectionOfFinsupp
          (R := R) (S := S) hR D⟩⟩

/-- Coefficient maps commute with restriction along a tower of affine étale
Dedekind domains. -/
theorem affineEtaleClosedPointDivisorCoefficient_map
    {T : Type u} [CommRing T] [IsDedekindDomain T]
    [Algebra S T] [Algebra.Etale S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.Etale R T]
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S))))
    (w : HeightOneSpectrum T) :
    affineEtaleClosedPointDivisorCoefficient (R := R) (S := T) hR w
      (ConcreteCategory.hom
        ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.map
          (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op) s) =
    affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR
      (heightOneSpectrumContractionOfEtale (R := S) (S := T) w) s := by
  let X := Spec (CommRingCat.of R)
  let U := affineEtaleSpecObject (R := R) (S := S)
  let V := affineEtaleSpecObject (R := R) (S := T)
  let m := affineEtaleSpecObjectMap (R := R) (S := S) (T := T)
  let q := affineEtaleHeightOneToClosedPointFiber (R := R) (S := T) hR w
  let x := q.1
  let y := q.2
  let eT := affineEtaleClosedPointResidueFiberEquivHeightOneFiber
    (R := R) (S := T) hR x
  let v := heightOneSpectrumContractionOfEtale (R := S) (S := T) w
  let eS := affineEtaleClosedPointResidueFiberEquivHeightOneFiber
    (R := R) (S := S) hR x
  let yS : closedPointResidueFiber X x U :=
    ⟨m.left y.1, by
      have hm := congrArg (fun f => f y.1) (MorphismProperty.Over.w m)
      exact hm.trans y.2⟩
  have hw : (eT y).1 = w :=
    affineEtaleClosedPointFiberEquivHeightOne_apply_heightOneToFiber
      (R := R) (S := T) hR w
  have hv : (eS yS).1 = v := by
    rw [affineEtaleClosedPointResidueFiberEquivHeightOneFiber_map
      (R := R) (S := S) (T := T) hR x y]
    exact congrArg (heightOneSpectrumContractionOfEtale (R := S) (S := T)) hw
  let pS := closedPointDivisorSheafComponentProjection X x
  let pT := closedPointDivisorSheafComponentProjection X x
  have hproj :
      ConcreteCategory.hom ((closedPointDivisorSummand X x).obj.map m.op)
        (ConcreteCategory.hom (pS.hom.app (op U)) s) =
      ConcreteCategory.hom (pT.hom.app (op V))
        (ConcreteCategory.hom
          ((closedPointDivisorSheaf X).obj.map m.op) s) := by
    have hn := pS.hom.naturality m.op
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    exact (ConcreteCategory.congr_hom hn s).symm
  have hleft := affineEtaleClosedPointDivisorCoefficient_eq_summandValue
    (R := R) (S := T) hR x y
    (ConcreteCategory.hom ((closedPointDivisorSheaf X).obj.map m.op) s)
  have hright := affineEtaleClosedPointDivisorCoefficient_eq_summandValue
    (R := R) (S := S) hR x yS s
  have hnat := closedPointDivisorSummandSectionsAddEquiv_naturality
    X x V U m (ConcreteCategory.hom (pS.hom.app (op U)) s) y
  have hcoeffS : affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR v s =
      ((closedPointDivisorSummandSectionsAddEquiv X x U
        (ConcreteCategory.hom (pS.hom.app (op U)) s) yS).down) := by
    rw [← hv]
    exact hright
  have hcoeffT : affineEtaleClosedPointDivisorCoefficient (R := R) (S := T) hR w
      (ConcreteCategory.hom ((closedPointDivisorSheaf X).obj.map m.op) s) =
      ((closedPointDivisorSummandSectionsAddEquiv X x V
        (ConcreteCategory.hom (pT.hom.app (op V))
          (ConcreteCategory.hom ((closedPointDivisorSheaf X).obj.map m.op) s)) y).down) := by
    rw [← hw]
    exact hleft
  have hnat' :
      closedPointDivisorSummandSectionsAddEquiv X x V
        (ConcreteCategory.hom (pT.hom.app (op V))
          (ConcreteCategory.hom ((closedPointDivisorSheaf X).obj.map m.op) s)) y =
      closedPointDivisorSummandSectionsAddEquiv X x U
        (ConcreteCategory.hom (pS.hom.app (op U)) s) yS := by
    rw [← hproj]
    exact hnat
  calc
    affineEtaleClosedPointDivisorCoefficient (R := R) (S := T) hR w
        (ConcreteCategory.hom ((closedPointDivisorSheaf X).obj.map m.op) s) =
        ((closedPointDivisorSummandSectionsAddEquiv X x V
          (ConcreteCategory.hom (pT.hom.app (op V))
            (ConcreteCategory.hom ((closedPointDivisorSheaf X).obj.map m.op) s)) y).down) := hcoeffT
    _ = ((closedPointDivisorSummandSectionsAddEquiv X x U
          (ConcreteCategory.hom (pS.hom.app (op U)) s) yS).down) := by
      exact congrArg ULift.down hnat'
    _ = affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR v s := hcoeffS.symm

/-- The affine section-to-divisor equivalences are natural under restriction
along a tower of étale Dedekind domains. -/
theorem affineEtaleClosedPointDivisorSectionFinsuppAddEquiv_naturality
    {T : Type u} [CommRing T] [IsDedekindDomain T]
    [Algebra S T] [Algebra.Etale S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.Etale R T]
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    affineEtaleClosedPointDivisorSectionFinsuppAddEquiv (R := R) (S := T) hR
      (ConcreteCategory.hom
        ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.map
          (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op) s) =
    affineEtaleDivisorPullback
      (affineEtaleClosedPointDivisorSectionFinsuppAddEquiv
        (R := R) (S := S) hR s) := by
  apply Finsupp.ext
  intro w
  change affineEtaleClosedPointDivisorCoefficient (R := R) (S := T) hR w
      (ConcreteCategory.hom
        ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.map
          (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op) s) =
    (affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR s)
      (heightOneSpectrumContractionOfEtale (R := S) (S := T) w)
  rw [affineEtaleClosedPointDivisorCoefficient_map
    (R := R) (S := S) (T := T) hR s w]
  rfl

end EtaleCohomology
