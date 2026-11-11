/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericUnitDivisorSections
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Nyll.SchemeTheory.Divisors.DedekindPrincipalDivisor
/-!
# Affine closed-point divisor sections

Coordinate descriptions of sections of the actual closed-point divisor sheaf
on an affine Dedekind scheme, and their comparison with generic-unit quotients.
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open IsDedekindDomain
universe u
namespace EtaleCohomology
variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- Read the coefficient at a height-one prime from the corresponding closed
point summand of the actual divisor sheaf. -/
noncomputable def affineClosedPointDivisorCoefficient
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (v : HeightOneSpectrum R)
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R)))) : ℤ := by
  let X := Spec (CommRingCat.of R)
  let U := affineEtaleSpecObject (R := R) (S := R)
  let x := IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR v
  let fiberEquiv := affineEtaleClosedPointResidueFiberEquivHeightOneFiber (R := R) (S := R) hR x
  have hmap : algebraMap R R = RingHom.id R := by
    ext r
    rfl
  have hId := heightOneSpectrumContractionOfEtale_id (R := R) hmap v
  have hfiber : heightOneSpectrumContractionOfEtale (R := R) (S := R) v =
      (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm x := by
    rw [hId]
    exact (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm_apply_apply v
  let y := fiberEquiv.symm ⟨v, hfiber⟩
  let p := @sheafCoproductComponentProjection (closedPoints X) X
    (closedPointDivisorSummand X) hShape x
  exact ((closedPointDivisorSummandSectionsAddEquiv X x U
      (ConcreteCategory.hom (p.hom.app (op (affineEtaleSpecObject (R := R) (S := R)))) s) y).down)





omit [IsDedekindDomain R] in
/-- An affine divisor-sheaf section is supported on finitely many closed points. -/
theorem affineClosedPointDivisorSheafSection_finiteSupport
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    [hQC : QuasiCompact (terminal.from
      (affineEtaleSpecObject (R := R) (S := R)).left)]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R)))) :
    ∃ T : Finset (closedPoints (Spec (CommRingCat.of R))),
      s = ∑ x ∈ T,
        ConcreteCategory.hom
          ((colimit.ι (Discrete.functor
            (closedPointDivisorSummand (Spec (CommRingCat.of R)))) ⟨x⟩).hom.app
              (op (affineEtaleSpecObject (R := R) (S := R))))
          (ConcreteCategory.hom
            ((sheafCoproductComponentProjection (Spec (CommRingCat.of R))
              (closedPointDivisorSummand (Spec (CommRingCat.of R))) x).hom.app
                (op (affineEtaleSpecObject (R := R) (S := R)))) s) := by
  exact @sheafCoproductSection_finiteSupport_of_quasiCompact
    (closedPoints (Spec (CommRingCat.of R))) (Spec (CommRingCat.of R))
    (closedPointDivisorSummand (Spec (CommRingCat.of R))) hShape
    (affineEtaleSpecObject (R := R) (S := R)) hQC s

theorem affineClosedPointDivisorCoefficient_zero_of_not_mem
    (hR : ¬ IsField R) (v : HeightOneSpectrum R)
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    [_hQC : QuasiCompact (terminal.from
      (affineEtaleSpecObject (R := R) (S := R)).left)]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R))))
    (T : Finset (closedPoints (Spec (CommRingCat.of R))))
    (hT : s = ∑ x ∈ T,
      ConcreteCategory.hom
          ((colimit.ι (Discrete.functor
            (closedPointDivisorSummand (Spec (CommRingCat.of R)))) ⟨x⟩).hom.app
              (op (affineEtaleSpecObject (R := R) (S := R))))
        (ConcreteCategory.hom
          ((sheafCoproductComponentProjection (Spec (CommRingCat.of R))
            (closedPointDivisorSummand (Spec (CommRingCat.of R))) x).hom.app
              (op (affineEtaleSpecObject (R := R) (S := R)))) s))
    (hnot : IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR v ∉ T) :
    affineClosedPointDivisorCoefficient R hR v s = 0 := by
  let X := Spec (CommRingCat.of R)
  let x := IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR v
  change x ∉ T at hnot
  let p := @sheafCoproductComponentProjection (closedPoints X) X
    (closedPointDivisorSummand X) hShape x
  have hp : ConcreteCategory.hom
      (p.hom.app (op (affineEtaleSpecObject (R := R) (S := R)))) s = 0 := by
    rw [hT]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro x' hx'
    have hne : x' ≠ x := by
      intro heq
      apply hnot
      rw [← heq]
      exact hx'
    exact closedPointDivisorSheafComponentProjection_app_injection_of_ne
      hne (affineEtaleSpecObject (R := R) (S := R))
      (ConcreteCategory.hom
        ((@sheafCoproductComponentProjection (closedPoints X) X
          (closedPointDivisorSummand X) hShape x').hom.app
            (op (affineEtaleSpecObject (R := R) (S := R)))) s)
  unfold affineClosedPointDivisorCoefficient
  dsimp only
  rw [hp]
  simp only [map_zero, Pi.zero_apply]
  rfl

/-- Encode an affine divisor-sheaf section as its finitely supported prime
coefficient function. -/
noncomputable def affineClosedPointDivisorSectionFinsupp
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R)))) :
    HeightOneSpectrum R →₀ ℤ := by
  classical
  let X := Spec (CommRingCat.of R)
  let U := affineEtaleSpecObject (R := R) (S := R)
  have hQC : QuasiCompact (terminal.from U.left) := by
    change QuasiCompact (terminal.from (Spec (CommRingCat.of R)))
    exact (AlgebraicGeometry.compactSpace_iff_quasiCompact
      (Spec (CommRingCat.of R))).mp inferInstance
  let hfin := @affineClosedPointDivisorSheafSection_finiteSupport
    R _ hShape hQC s
  let T := Classical.choose hfin
  have hT := Classical.choose_spec hfin
  let f := fun v : HeightOneSpectrum R =>
    @affineClosedPointDivisorCoefficient R _ _ hR hShape v s
  have hsub : Function.support f ⊆ T.image
      (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm := by
    intro v hv
    have hvnz : f v ≠ 0 := hv
    have hx : IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR v ∈ T := by
      by_contra hnot
      exact hvnz (@affineClosedPointDivisorCoefficient_zero_of_not_mem
        R _ _ hR v hShape hQC s T hT hnot)
    exact Finset.mem_image.mpr ⟨_, hx,
      (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm_apply_apply v⟩
  exact Finsupp.ofSupportFinite f ((T.image
    (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm).finite_toSet.subset hsub)


/-- The coefficient-at-a-prime map is additive. -/
noncomputable def affineClosedPointDivisorCoefficientAddHom
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (v : HeightOneSpectrum R) :
    ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R)))) →+ ℤ where
  toFun := @affineClosedPointDivisorCoefficient R _ _ hR hShape v
  map_zero' := by
    let X := Spec (CommRingCat.of R)
    let x := IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR v
    let hShape : HasColimitsOfShape (Discrete (closedPoints X))
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape X
    let p := @sheafCoproductComponentProjection (closedPoints X) X
      (closedPointDivisorSummand X) hShape x
    let E := closedPointDivisorSummandSectionsAddEquiv X x
      (affineEtaleSpecObject (R := R) (S := R))
    let y := (affineEtaleClosedPointResidueFiberEquivHeightOneFiber hR x).symm
      ⟨v, by
        have hm : algebraMap R R = RingHom.id R := by ext r; rfl
        rw [heightOneSpectrumContractionOfEtale_id hm]
        exact (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm_apply_apply v⟩
    change (E (ConcreteCategory.hom (p.hom.app
      (op (affineEtaleSpecObject (R := R) (S := R)))) 0) y).down = 0
    have hp0 := map_zero (ConcreteCategory.hom (p.hom.app
      (op (affineEtaleSpecObject (R := R) (S := R)))) )
    rw [hp0, E.map_zero]
    rfl
  map_add' s t := by
    let X := Spec (CommRingCat.of R)
    let x := IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR v
    let hShape : HasColimitsOfShape (Discrete (closedPoints X))
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape X
    let p := @sheafCoproductComponentProjection (closedPoints X) X
      (closedPointDivisorSummand X) hShape x
    let E := closedPointDivisorSummandSectionsAddEquiv X x
      (affineEtaleSpecObject (R := R) (S := R))
    let y := (affineEtaleClosedPointResidueFiberEquivHeightOneFiber hR x).symm
      ⟨v, by
        have hm : algebraMap R R = RingHom.id R := by ext r; rfl
        rw [heightOneSpectrumContractionOfEtale_id hm]
        exact (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm_apply_apply v⟩
    change (E (ConcreteCategory.hom (p.hom.app
      (op (affineEtaleSpecObject (R := R) (S := R)))) (s + t)) y).down = _
    have hpadd := map_add (ConcreteCategory.hom (p.hom.app
      (op (affineEtaleSpecObject (R := R) (S := R)))) ) s t
    have hpadd' : ConcreteCategory.hom (p.hom.app
        (op (affineEtaleSpecObject (R := R) (S := R)))) (s + t) =
        ConcreteCategory.hom (p.hom.app
          (op (affineEtaleSpecObject (R := R) (S := R)))) s +
        ConcreteCategory.hom (p.hom.app
          (op (affineEtaleSpecObject (R := R) (S := R)))) t := by
      simpa only [closedPointDivisorSheaf] using hpadd
    rw [hpadd', E.map_add]
    rfl

/-- The finite coefficient encoding is additive. -/
noncomputable def affineClosedPointDivisorSectionFinsuppAddHom
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})] :
    ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R)))) →+
      (HeightOneSpectrum R →₀ ℤ) where
  toFun := @affineClosedPointDivisorSectionFinsupp R _ _ hR hShape
  map_zero' := by
    apply Finsupp.ext
    intro v
    change affineClosedPointDivisorCoefficient R hR v 0 = 0
    exact (affineClosedPointDivisorCoefficientAddHom R hR v).map_zero
  map_add' s t := by
    apply Finsupp.ext
    intro v
    change affineClosedPointDivisorCoefficient R hR v (s + t) = _
    exact (affineClosedPointDivisorCoefficientAddHom R hR v).map_add s t

/-- The section of one closed-point summand with a prescribed constant
coefficient on the identity affine étale object. -/
noncomputable def affineClosedPointDivisorSummandSection
    (x : closedPoints (Spec (CommRingCat.of R))) (n : ℤ) :
    (closedPointDivisorSummand (Spec (CommRingCat.of R)) x).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R))) :=
  (closedPointDivisorSummandSectionsAddEquiv (Spec (CommRingCat.of R)) x
    (affineEtaleSpecObject (R := R) (S := R))).symm (fun _ => ULift.up n)

/-- Build an actual divisor-sheaf section from a finitely supported divisor by
inserting its single closed-point summand sections into the coproduct. -/
noncomputable def affineClosedPointDivisorSectionOfFinsupp
    (hR : ¬ IsField R) (D : HeightOneSpectrum R →₀ ℤ) :
    (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R))) := by
  classical
  let X := Spec (CommRingCat.of R)
  let U := affineEtaleSpecObject (R := R) (S := R)
  exact ∑ v ∈ D.support,
    ConcreteCategory.hom
      ((closedPointDivisorSheafInjection X
        (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR v)).hom.app (op U))
      (affineClosedPointDivisorSummandSection R
        (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR v) (D v))

/-- Coefficients of the reconstructed divisor-sheaf section are the original
finite divisor coefficients. -/
theorem affineClosedPointDivisorSectionOfFinsupp_coefficient
    (hR : ¬ IsField R) (D : HeightOneSpectrum R →₀ ℤ)
    (v : HeightOneSpectrum R) :
    let X := Spec (CommRingCat.of R)
    let : HasColimitsOfShape (Discrete (closedPoints X)) AddCommGrpCat.{u} := inferInstance
    let : HasColimitsOfShape (Discrete (closedPoints X))
      (X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) := inferInstance
    let : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
      CategoryTheory.Sheaf.instHasColimitsOfShape
    affineClosedPointDivisorCoefficient R hR v
      (affineClosedPointDivisorSectionOfFinsupp R hR D) = D v := by
  intro X
  classical
  let U := affineEtaleSpecObject (R := R) (S := R)
  let x := IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR v
  let fiberEquiv := affineEtaleClosedPointResidueFiberEquivHeightOneFiber
    (R := R) (S := R) hR x
  have hmap : algebraMap R R = RingHom.id R := by
    ext r
    rfl
  have hId := heightOneSpectrumContractionOfEtale_id (R := R) hmap v
  have hfiber : heightOneSpectrumContractionOfEtale (R := R) (S := R) v =
      (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm x := by
    rw [hId]
    exact (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm_apply_apply v
  let y := fiberEquiv.symm ⟨v, hfiber⟩
  let p := closedPointDivisorSheafComponentProjection X x
  change ((closedPointDivisorSummandSectionsAddEquiv X x U)
      (ConcreteCategory.hom (p.hom.app (op U))
        (affineClosedPointDivisorSectionOfFinsupp R hR D)) y).down = D v
  dsimp only [affineClosedPointDivisorSectionOfFinsupp]
  rw [map_sum]
  rw [Finset.sum_eq_single v]
  · dsimp only [p]
    rw [closedPointDivisorSheafComponentProjection_app_injection]
    simp only [affineClosedPointDivisorSummandSection]
    have hEval := congrArg (fun f => f y)
      (AddEquiv.apply_symm_apply (closedPointDivisorSummandSectionsAddEquiv X x U)
        (fun _ => ULift.up (D v)))
    exact congrArg ULift.down hEval
  · intro w hw hwv
    exact closedPointDivisorSheafComponentProjection_app_injection_of_ne
      (fun heq => hwv ((IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).injective heq))
      U (affineClosedPointDivisorSummandSection R
        (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR w) (D w))
  · intro hv
    have hzero : D v = 0 := by
      by_contra hne
      exact hv (Finsupp.mem_support_iff.mpr hne)
    rw [hzero]
    dsimp only [p]
    rw [closedPointDivisorSheafComponentProjection_app_injection]
    change (closedPointDivisorSummandSectionsAddEquiv X x U).symm 0 = 0
    exact (closedPointDivisorSummandSectionsAddEquiv X x U).symm.map_zero

/-- The finitely supported coefficient map is a left inverse to reconstruction
of a section from its divisor coefficients. -/
theorem affineClosedPointDivisorSectionFinsupp_sectionOfFinsupp
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (D : HeightOneSpectrum R →₀ ℤ) :
    affineClosedPointDivisorSectionFinsupp R hR
      (affineClosedPointDivisorSectionOfFinsupp R hR D) = D := by
  classical
  apply Finsupp.ext
  intro v
  change affineClosedPointDivisorCoefficient R hR v
      (affineClosedPointDivisorSectionOfFinsupp R hR D) = D v
  exact affineClosedPointDivisorSectionOfFinsupp_coefficient R hR D v

omit [IsDedekindDomain R] in
/-- The closed-point fiber of the identity affine étale object is a singleton. -/
private theorem affineEtaleIdentityClosedPointFiber_subsingleton
    (x : closedPoints (Spec (CommRingCat.of R))) :
    Subsingleton (closedPointResidueFiber (Spec (CommRingCat.of R)) x
      (affineEtaleSpecObject (R := R) (S := R))) := by
  constructor
  intro y z
  apply Subtype.ext
  have hy : y.1 = x.1 := by
    have hpoint := y.2
    change Spec.map (CommRingCat.ofHom (algebraMap R R)) y.1 = x.1 at hpoint
    have hmap : algebraMap R R = RingHom.id R := by
      ext r
      rfl
    rw [hmap] at hpoint
    have hId : CommRingCat.ofHom (RingHom.id R) = 𝟙 (CommRingCat.of R) := by
      ext r
      rfl
    rw [hId, Spec.map_id] at hpoint
    exact hpoint
  have hz : z.1 = x.1 := by
    have hpoint := z.2
    change Spec.map (CommRingCat.ofHom (algebraMap R R)) z.1 = x.1 at hpoint
    have hmap : algebraMap R R = RingHom.id R := by
      ext r
      rfl
    rw [hmap] at hpoint
    have hId : CommRingCat.ofHom (RingHom.id R) = 𝟙 (CommRingCat.of R) := by
      ext r
      rfl
    rw [hId, Spec.map_id] at hpoint
    exact hpoint
  exact hy.trans hz.symm

/-- On the identity affine object, the coefficient determines the entire
closed-point summand component. -/
private theorem affineClosedPointDivisorComponent_eq_of_coefficient_eq
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s t : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R))))
    (v : HeightOneSpectrum R)
    (hcoeff : affineClosedPointDivisorCoefficient R hR v s =
      affineClosedPointDivisorCoefficient R hR v t) :
    let X := Spec (CommRingCat.of R)
    ConcreteCategory.hom
      (((@sheafCoproductComponentProjection (closedPoints X) X
        (closedPointDivisorSummand X) hShape
        (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR v)).hom.app
          (op (affineEtaleSpecObject (R := R) (S := R))))) s =
    ConcreteCategory.hom
      (((@sheafCoproductComponentProjection (closedPoints X) X
        (closedPointDivisorSummand X) hShape
        (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR v)).hom.app
          (op (affineEtaleSpecObject (R := R) (S := R))))) t := by
  intro X
  let U := affineEtaleSpecObject (R := R) (S := R)
  let x := IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR v
  let p := @sheafCoproductComponentProjection (closedPoints X) X
    (closedPointDivisorSummand X) hShape x
  let E := closedPointDivisorSummandSectionsAddEquiv X x U
  let fiberEquiv := affineEtaleClosedPointResidueFiberEquivHeightOneFiber
    (R := R) (S := R) hR x
  have hm : algebraMap R R = RingHom.id R := by
    ext r
    rfl
  have hfiber : heightOneSpectrumContractionOfEtale (R := R) (S := R) v =
      (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm x := by
    rw [heightOneSpectrumContractionOfEtale_id hm]
    exact (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm_apply_apply v
  let y := fiberEquiv.symm ⟨v, hfiber⟩
  have hval : (E (ConcreteCategory.hom (p.hom.app (op U)) s)) y =
      (E (ConcreteCategory.hom (p.hom.app (op U)) t)) y := by
    apply ULift.ext
    change affineClosedPointDivisorCoefficient R hR v s =
      affineClosedPointDivisorCoefficient R hR v t
    exact hcoeff
  have hfun : E (ConcreteCategory.hom (p.hom.app (op U)) s) =
      E (ConcreteCategory.hom (p.hom.app (op U)) t) := by
    funext z
    have hsub := affineEtaleIdentityClosedPointFiber_subsingleton (R := R) x
    have hz : z = y := hsub.elim z y
    rw [hz]
    exact hval
  exact E.injective hfun

/-- The coefficient encoding is injective on sections over the identity
affine étale object. -/
theorem affineClosedPointDivisorSectionFinsupp_injective
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    {s t : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R)))}
    (h : affineClosedPointDivisorSectionFinsupp R hR s =
      affineClosedPointDivisorSectionFinsupp R hR t) : s = t := by
  classical
  let X := Spec (CommRingCat.of R)
  let U := affineEtaleSpecObject (R := R) (S := R)
  have hQC : QuasiCompact (terminal.from U.left) := by
    change QuasiCompact (terminal.from (Spec (CommRingCat.of R)))
    exact (AlgebraicGeometry.compactSpace_iff_quasiCompact
      (Spec (CommRingCat.of R))).mp inferInstance
  obtain ⟨Ts, hTs⟩ :=
    @affineClosedPointDivisorSheafSection_finiteSupport R _ hShape hQC s
  obtain ⟨Tt, hTt⟩ :=
    @affineClosedPointDivisorSheafSection_finiteSupport R _ hShape hQC t
  let T := Ts ∪ Tt
  let e := IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR
  let term (z : (closedPointDivisorSheaf X).obj.obj (op U))
      (x : closedPoints X) :=
    ConcreteCategory.hom
      ((colimit.ι (Discrete.functor (closedPointDivisorSummand X)) ⟨x⟩).hom.app (op U))
      (ConcreteCategory.hom
        ((@sheafCoproductComponentProjection (closedPoints X) X
          (closedPointDivisorSummand X) hShape x).hom.app (op U)) z)
  have hcomponent_zero (z : (closedPointDivisorSheaf X).obj.obj (op U))
      (Tz : Finset (closedPoints X))
      (hTz : z = ∑ x ∈ Tz, term z x)
      {x : closedPoints X} (hx : x ∉ Tz) :
      ConcreteCategory.hom
        ((@sheafCoproductComponentProjection (closedPoints X) X
          (closedPointDivisorSummand X) hShape x).hom.app (op U)) z = 0 := by
    let v := e.symm x
    have hvx : e v = x := by
      dsimp only [v]
      exact e.apply_symm_apply x
    have hmem : e v ∉ Tz := by rw [hvx]; exact hx
    have hz := @affineClosedPointDivisorCoefficient_zero_of_not_mem
      R _ _ hR v hShape hQC z Tz hTz hmem
    have hzero := (affineClosedPointDivisorCoefficientAddHom R hR v).map_zero
    have heq := affineClosedPointDivisorComponent_eq_of_coefficient_eq
      (R := R) hR z 0 v (hz.trans hzero.symm)
    rw [hvx] at heq
    have hp0 := map_zero (ConcreteCategory.hom
      (((@sheafCoproductComponentProjection (closedPoints X) X
        (closedPointDivisorSummand X) hShape x).hom.app (op U))))
    exact heq.trans hp0
  have hsumT : (∑ x ∈ T, term s x) = ∑ x ∈ T, term t x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hv := congrArg (fun D : HeightOneSpectrum R →₀ ℤ => D (e.symm x)) h
    have hcoeff : affineClosedPointDivisorCoefficient R hR (e.symm x) s =
        affineClosedPointDivisorCoefficient R hR (e.symm x) t := by
      change affineClosedPointDivisorCoefficient R hR (e.symm x) s =
        affineClosedPointDivisorCoefficient R hR (e.symm x) t at hv
      exact hv
    exact congrArg (fun z => ConcreteCategory.hom
      ((colimit.ι (Discrete.functor (closedPointDivisorSummand X)) ⟨x⟩).hom.app (op U)) z)
      (affineClosedPointDivisorComponent_eq_of_coefficient_eq
        (R := R) hR s t (e.symm x) hcoeff)
  have hsExtend : (∑ x ∈ T, term s x) = ∑ x ∈ Ts, term s x := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro x hx hxnot
    have hzero := hcomponent_zero s Ts hTs hxnot
    simp only [term, hzero, map_zero]
  have htExtend : (∑ x ∈ T, term t x) = ∑ x ∈ Tt, term t x := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro x hx hxnot
    have hzero := hcomponent_zero t Tt hTt hxnot
    simp only [term, hzero, map_zero]
  have hsEq : s = ∑ x ∈ T, term s x := hTs.trans hsExtend.symm
  have htEq : t = ∑ x ∈ T, term t x := hTt.trans htExtend.symm
  exact hsEq.trans (hsumT.trans htEq.symm)

/-- Actual sections of the affine closed-point divisor sheaf are additively
equivalent to finitely supported height-one coefficients. -/
noncomputable def affineClosedPointDivisorSectionFinsuppAddEquiv
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})] :
    ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R)))) ≃+
      (HeightOneSpectrum R →₀ ℤ) :=
  AddEquiv.ofBijective (affineClosedPointDivisorSectionFinsuppAddHom R hR)
    ⟨fun _ _ h => affineClosedPointDivisorSectionFinsupp_injective R hR h,
      fun D => ⟨affineClosedPointDivisorSectionOfFinsupp R hR D,
        affineClosedPointDivisorSectionFinsupp_sectionOfFinsupp R hR D⟩⟩

/-- The actual closed-point divisor-sheaf section module is equivalent to the
global generic-unit quotient through finite divisor coefficients. -/
noncomputable def affineClosedPointDivisorSheafToGenericUnitQuotientEquiv
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})] :
    ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R)))) ≃+
    (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale
          (Spec (CommRingCat.of R))).obj ⊤)) :=
  (affineClosedPointDivisorSectionFinsuppAddEquiv R hR).trans
    (EtaleFundamentalGroups.StrictHenselian.divisorGenericUnitQuotientGlobalSectionEquiv R)

/-- The comparison from the actual closed-point divisor-sheaf sections on the
affine identity object to the actual generic-unit quotient. It first reads the
finite divisor through the closed-point fiber equivalence, then applies the
actual global-section equivalence for generic-unit quotients. -/
noncomputable def affineClosedPointDivisorSheafToGenericUnitQuotient
    (hR : ¬ IsField R) :
    ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R)))) →+
    (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale
          (Spec (CommRingCat.of R))).obj ⊤)) :=
  let hShape : HasColimitsOfShape
      (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
  (@affineClosedPointDivisorSheafToGenericUnitQuotientEquiv R _ _ hR hShape).toAddMonoidHom

/-- Reconstruct the actual divisor-sheaf section from a global generic-unit
quotient by taking its finite divisor coefficients. -/
noncomputable def affineClosedPointDivisorGenericUnitQuotientToSheaf
    (hR : ¬ IsField R)
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale
          (Spec (CommRingCat.of R))).obj ⊤))) :
    (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R))) :=
  affineClosedPointDivisorSectionOfFinsupp R hR
    (EtaleFundamentalGroups.StrictHenselian.genericUnitQuotientSectionDivisor R q)

/-- The reconstructed divisor section maps back to its original global
generic-unit quotient section. -/
theorem affineClosedPointDivisorSheafToGenericUnitQuotient_rightInverse
    (hR : ¬ IsField R)
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale
          (Spec (CommRingCat.of R))).obj ⊤))) :
    affineClosedPointDivisorSheafToGenericUnitQuotient R hR
      (affineClosedPointDivisorGenericUnitQuotientToSheaf R hR q) = q := by
  let X := Spec (CommRingCat.of R)
  let hShape : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape X
  change EtaleFundamentalGroups.StrictHenselian.divisorGenericUnitQuotientGlobalSectionEquiv R
      (@affineClosedPointDivisorSectionFinsuppAddHom R _ _ hR hShape
        (affineClosedPointDivisorSectionOfFinsupp R hR
          (EtaleFundamentalGroups.StrictHenselian.genericUnitQuotientSectionDivisor R q))) = q
  change EtaleFundamentalGroups.StrictHenselian.divisorGenericUnitQuotientGlobalSectionEquiv R
      (affineClosedPointDivisorSectionFinsupp R hR
        (affineClosedPointDivisorSectionOfFinsupp R hR
          (EtaleFundamentalGroups.StrictHenselian.genericUnitQuotientSectionDivisor R q))) = q
  rw [affineClosedPointDivisorSectionFinsupp_sectionOfFinsupp]
  exact EtaleFundamentalGroups.StrictHenselian.divisorGenericUnitQuotientSection_sectionDivisor
    R q

/-- Reconstructing a section after mapping it to the global generic-unit
quotient returns the original section. -/
theorem affineClosedPointDivisorSheafToGenericUnitQuotient_leftInverse
    (hR : ¬ IsField R)
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R)))) :
    affineClosedPointDivisorGenericUnitQuotientToSheaf R hR
      (affineClosedPointDivisorSheafToGenericUnitQuotient R hR s) = s := by
  let X := Spec (CommRingCat.of R)
  let hShape : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape X
  apply (@affineClosedPointDivisorSheafToGenericUnitQuotientEquiv
    R _ _ hR hShape).injective
  exact affineClosedPointDivisorSheafToGenericUnitQuotient_rightInverse
    R hR (affineClosedPointDivisorSheafToGenericUnitQuotient R hR s)

theorem affineClosedPointDivisorSheafToGenericUnitQuotient_coefficient
    (hR : ¬ IsField R)
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := R))))
    (v : HeightOneSpectrum R) :
    EtaleFundamentalGroups.StrictHenselian.genericUnitQuotientSectionCoefficient R v
      (affineClosedPointDivisorSheafToGenericUnitQuotient R hR s) =
    affineClosedPointDivisorCoefficient R hR v s := by
  change EtaleFundamentalGroups.StrictHenselian.genericUnitQuotientSectionCoefficient R v
      ((EtaleFundamentalGroups.StrictHenselian.divisorGenericUnitQuotientGlobalSectionEquiv R)
        (affineClosedPointDivisorSectionFinsupp R hR s)) = _
  rw [EtaleFundamentalGroups.StrictHenselian.divisorGenericUnitQuotientGlobalSectionEquiv]
  change EtaleFundamentalGroups.StrictHenselian.genericUnitQuotientSectionCoefficient R v
      (EtaleFundamentalGroups.StrictHenselian.divisorGenericUnitQuotientSection R
        (affineClosedPointDivisorSectionFinsupp R hR s)) = _
  exact EtaleFundamentalGroups.StrictHenselian.genericUnitQuotientSectionCoefficient_divisor
    R v (affineClosedPointDivisorSectionFinsupp R hR s)

end EtaleCohomology
