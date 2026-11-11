/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.ConstantEtaleSections
public import Nyll.SchemeTheory.Etale.FiniteGeometricPoints
public import Nyll.SchemeTheory.CategoryTheory.PresheafDirectSum
public import Nyll.SchemeTheory.Divisors.DedekindPrincipalDivisor
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The closed-point divisor sheaf

The divisor sheaf on a scheme is defined here as the categorical coproduct,
over its actual closed points, of the direct images of the constant integer
sheaf on each residue-field spectrum. This is the target sheaf in the
Fundamental Exact Sequence, Stacks Project, Theorem 59.68.1 (Tag 03RI):
<https://stacks.math.columbia.edu/tag/03RI>.

This file defines the target object only; it does not assert the comparison
with the quotient of generic-point units.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace EtaleCohomology

/-- The actual residue-field point map associated to a closed point. -/
abbrev closedPointResidueFieldMap (X : Scheme.{u}) (x : closedPoints X) :
    Spec (X.residueField x.1) ⟶ X :=
  X.fromSpecResidueField x.1

/-- The residue-field map of an actual closed point is a closed immersion. -/
theorem closedPointResidueFieldMap_isClosedImmersion
    (X : Scheme.{u}) (x : closedPoints X) :
    IsClosedImmersion (closedPointResidueFieldMap X x) :=
  isClosed_singleton_iff_isClosedImmersion.mp x.2

/-- The summand of the divisor sheaf supported at a single actual closed
point, given by the actual direct image of its constant integer sheaf. -/
def closedPointDivisorSummand (X : Scheme.{u}) (x : closedPoints X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (etaleAbelianPushforward (closedPointResidueFieldMap X x)).obj
    ((constantSheaf (Spec (X.residueField x.1)).smallEtaleTopology
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))

/-- The canonical shape colimits used by the actual closed-point divisor
sheaf. -/
theorem closedPointDivisorSheafHasColimitsOfShape (X : Scheme.{u}) :
    HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) := by
  let hAdd : HasColimitsOfShape (Discrete (closedPoints X)) AddCommGrpCat.{u} := inferInstance
  exact @CategoryTheory.Sheaf.instHasColimitsOfShape
    X.Etale _ X.smallEtaleTopology AddCommGrpCat.{u} _
    (Discrete (closedPoints X)) _ inferInstance hAdd

/-- Points of an étale object lying over the closed point `x`. -/
abbrev closedPointResidueFiber (X : Scheme.{u}) (x : closedPoints X)
    (U : X.Etale) : Type u := {y : U.left // U.hom y = x.1}

/-- A quasi-compact locally quasi-finite étale object over a quasi-separated
scheme has only finitely many points over any fixed closed point. -/
theorem closedPointResidueFiber_finite (X : Scheme.{u}) (x : closedPoints X)
    (U : X.Etale) [LocallyQuasiFinite U.hom]
    [QuasiCompact (terminal.from U.left)]
    [QuasiSeparatedSpace ((Functor.fromPUnit X).obj U.right)] :
    Finite (closedPointResidueFiber X x U) := by
  have hCompact : CompactSpace U.left :=
    (AlgebraicGeometry.compactSpace_iff_quasiCompact U.left).2 inferInstance
  have hQuasiCompact : QuasiCompact U.hom :=
    @AlgebraicGeometry.quasiCompact_of_compactSpace _ _ U.hom hCompact inferInstance
  have hFiber : (U.hom ⁻¹' {x.1}).Finite :=
    @Scheme.Hom.finite_preimage_singleton _ _ U.hom inferInstance hQuasiCompact x.1
  change Finite (↑(U.hom ⁻¹' {x.1}))
  exact @Finite.of_fintype _ hFiber.fintype

/-- The affine-scheme object over `Spec R` associated to an étale algebra
`R → S`. Keep this canonical object transparent when it indexes bundled
section groups. -/
noncomputable abbrev affineEtaleSpecObject
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] : (Spec (CommRingCat.of R)).Etale := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  letI : Etale f :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  exact Scheme.Etale.mk f

/-- The actual closed-point residue fiber of an affine étale map of Dedekind
domains is the fiber of the existing height-one prime contraction map. The
base must be a non-field so its closed points correspond to height-one primes;
the source may be a field, in which case both fibers are empty. -/
noncomputable def affineEtaleClosedPointResidueFiberEquivHeightOneFiber
    {R S : Type u} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]
    (hR : ¬ IsField R) (x : closedPoints (Spec (CommRingCat.of R))) :
    closedPointResidueFiber (Spec (CommRingCat.of R)) x
      (affineEtaleSpecObject (R := R) (S := S)) ≃
    {w : IsDedekindDomain.HeightOneSpectrum S //
      heightOneSpectrumContractionOfEtale (R := R) (S := S) w =
        (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm x} where
  toFun y := by
    let v := (IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm x
    have hmap : Spec.map (CommRingCat.ofHom (algebraMap R S)) y.1 = x.1 := by
      exact y.2
    have hcontract : y.1.asIdeal.under R = v.asIdeal := by
      change (Spec.map (CommRingCat.ofHom (algebraMap R S)) y.1).asIdeal = x.1.asIdeal
      exact congrArg PrimeSpectrum.asIdeal hmap
    have hne : y.1.asIdeal ≠ ⊥ := by
      intro hbot
      have hbotContract : y.1.asIdeal.under R = ⊥ := by
        rw [hbot]
        exact Ideal.under_bot R S
      exact v.ne_bot ((hbotContract.symm.trans hcontract).symm)
    let w : IsDedekindDomain.HeightOneSpectrum S :=
      ⟨y.1.asIdeal, y.1.isPrime, hne⟩
    refine ⟨w, ?_⟩
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [heightOneSpectrumContractionOfEtale_asIdeal]
    exact hcontract
  invFun w := by
    let q : PrimeSpectrum S := ⟨w.1.asIdeal, w.1.isPrime⟩
    have hcontract : w.1.asIdeal.under R =
        ((IsDedekindDomain.HeightOneSpectrum.equivClosedPoints hR).symm x).asIdeal := by
      have h := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal w.2
      simpa only [heightOneSpectrumContractionOfEtale_asIdeal] using h
    refine ⟨q, ?_⟩
    apply PrimeSpectrum.ext
    change q.asIdeal.under R = x.1.asIdeal
    exact hcontract
  left_inv := by
    intro y
    apply Subtype.ext
    apply PrimeSpectrum.ext
    rfl
  right_inv := by
    intro w
    apply Subtype.ext
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rfl

/-- The prime ideal of the height-one point attached to a point of the
residue fiber is the prime ideal of that point. -/
@[simp] theorem affineEtaleClosedPointResidueFiberEquivHeightOneFiber_asIdeal
    {R S : Type u} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]
    (hR : ¬ IsField R) (x : closedPoints (Spec (CommRingCat.of R)))
    (y : closedPointResidueFiber (Spec (CommRingCat.of R)) x
      (affineEtaleSpecObject (R := R) (S := S))) :
    ((affineEtaleClosedPointResidueFiberEquivHeightOneFiber hR x y).1).asIdeal =
      y.1.asIdeal := rfl

/-- The actual morphism of affine étale objects induced by a tower of étale
algebras `R → S → T`. -/
noncomputable def affineEtaleSpecObjectMap
    {R S T : Type u} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]
    [CommRing T] [IsDedekindDomain T] [Algebra S T] [Algebra.Etale S T]
    [Algebra R T] [IsScalarTower R S T] [Algebra.Etale R T] :
    affineEtaleSpecObject (R := R) (S := T) ⟶
      affineEtaleSpecObject (R := R) (S := S) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap S T))
  letI : Etale f :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  refine MorphismProperty.Over.homMk f ?_ trivial
  change Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
    Spec.map (CommRingCat.ofHom (algebraMap R T))
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (IsScalarTower.algebraMap_apply R S T r).symm

/-- Contraction of the height-one point agrees with the map on actual
closed-point residue fibers induced by `Spec T → Spec S`. -/
theorem affineEtaleClosedPointResidueFiberEquivHeightOneFiber_map
    {R S T : Type u} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]
    [CommRing T] [IsDedekindDomain T] [Algebra S T] [Algebra.Etale S T]
    [Algebra R T] [IsScalarTower R S T] [Algebra.Etale R T]
    (hR : ¬ IsField R) (x : closedPoints (Spec (CommRingCat.of R)))
    (y : closedPointResidueFiber (Spec (CommRingCat.of R)) x
      (affineEtaleSpecObject (R := R) (S := T))) :
    affineEtaleClosedPointResidueFiberEquivHeightOneFiber hR x
      ⟨(affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).left y.1, by
        have hm := congrArg (fun f => f y.1)
          (MorphismProperty.Over.w
            (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)))
        exact hm.trans y.2⟩ =
      heightOneSpectrumContractionOfEtale (R := S) (S := T)
        (affineEtaleClosedPointResidueFiberEquivHeightOneFiber hR x y).1 := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [affineEtaleClosedPointResidueFiberEquivHeightOneFiber_asIdeal,
    heightOneSpectrumContractionOfEtale_asIdeal,
    affineEtaleClosedPointResidueFiberEquivHeightOneFiber_asIdeal]
  change Ideal.comap (algebraMap S T) y.1.asIdeal =
    y.1.asIdeal.under S
  rfl

/-- The actual projection from the scheme-theoretic residue-field fiber gives
the set of points of `U` over `x`. Its injectivity uses that the residue-field
map is a closed immersion; surjectivity uses the pullback carrier theorem. -/
noncomputable def closedPointResidueFiberPointEquiv
    (X : Scheme.{u}) (x : closedPoints X) (U : X.Etale) :
    ((etaleBaseChange (closedPointResidueFieldMap X x)).obj U).left ≃
      closedPointResidueFiber X x U := by
  let i := closedPointResidueFieldMap X x
  letI : IsClosedImmersion i := closedPointResidueFieldMap_isClosedImmersion X x
  let p := pullback.fst U.hom i
  have hp : IsClosedImmersion p := by infer_instance
  have hpInjective : Function.Injective p := p.isClosedEmbedding.injective
  have hi : i (IsLocalRing.closedPoint (X.residueField x.1)) = x.1 := by
    change X.fromSpecResidueField x.1
      (IsLocalRing.closedPoint (X.residueField x.1)) = x.1
    exact Scheme.fromSpecResidueField_apply x.1 _
  refine Equiv.ofBijective (fun z => (⟨p z, ?_⟩ : closedPointResidueFiber X x U)) ?_
  · have h := congrArg (fun k : pullback U.hom i ⟶ X => k z) pullback.condition
    change U.hom (p z) = i (pullback.snd U.hom i z) at h
    calc
      U.hom (p z) = i (pullback.snd U.hom i z) := h
      _ = i (IsLocalRing.closedPoint (X.residueField x.1)) := by
        congr 1
        exact Subsingleton.elim _ _
      _ = x.1 := hi
  · constructor
    · intro z z' h
      apply hpInjective
      exact congrArg Subtype.val h
    · intro y
      obtain ⟨z, hfst, hsnd⟩ :=
        Scheme.Pullback.exists_preimage_pullback (f := U.hom) (g := i) y.1
          (IsLocalRing.closedPoint (X.residueField x.1)) (y.2.trans hi.symm)
      exact ⟨z, Subtype.ext hfst⟩

/-- The geometric fiber-point equivalence commutes with base-changed
morphisms of étale objects. -/
theorem closedPointResidueFiberPointEquiv_map
    (X : Scheme.{u}) (x : closedPoints X) (U W : X.Etale) (m : U ⟶ W)
    (z : ((etaleBaseChange (closedPointResidueFieldMap X x)).obj U).left) :
    closedPointResidueFiberPointEquiv X x W
        (((etaleBaseChange (closedPointResidueFieldMap X x)).map m).left z) =
      ⟨m.left (closedPointResidueFiberPointEquiv X x U z).1,
        by
          have hm := congrArg (fun k => k (closedPointResidueFiberPointEquiv X x U z).1)
            (MorphismProperty.Over.w m)
          exact hm.trans (closedPointResidueFiberPointEquiv X x U z).2⟩ := by
  let i := closedPointResidueFieldMap X x
  have hproj :
      ((etaleBaseChange i).map m).left ≫ pullback.fst W.hom i =
        pullback.fst U.hom i ≫ m.left := by
    have hw : (pullback.fst U.hom i ≫ m.left) ≫ W.hom =
        pullback.snd U.hom i ≫ i := by
      rw [Category.assoc, MorphismProperty.Over.w
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) m]
      exact pullback.condition
    have hm : ((etaleBaseChange i).map m).left =
        pullback.lift (pullback.fst U.hom i ≫ m.left) (pullback.snd U.hom i) hw := by
      dsimp only [etaleBaseChange]
      exact MorphismProperty.Over.pullback_map_left
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) (f := i) m
    calc
      _ = pullback.lift (pullback.fst U.hom i ≫ m.left) (pullback.snd U.hom i) hw ≫
          pullback.fst W.hom i := congrArg (fun k => k ≫ pullback.fst W.hom i) hm
      _ = pullback.fst U.hom i ≫ m.left := pullback.lift_fst _ _ _
  apply Subtype.ext
  change pullback.fst W.hom i (((etaleBaseChange i).map m).left z) = _
  exact congrArg (fun k => k z) hproj

/-- Inverse-coordinate form of the geometric fiber-point compatibility. -/
theorem closedPointResidueFiberPointEquiv_symm_map
    (X : Scheme.{u}) (x : closedPoints X) (U W : X.Etale) (m : U ⟶ W)
    (y : closedPointResidueFiber X x U) :
    closedPointResidueFiberPointEquiv X x W
        (((etaleBaseChange (closedPointResidueFieldMap X x)).map m).left
          ((closedPointResidueFiberPointEquiv X x U).symm y)) =
      ⟨m.left y.1, by
        have hm := congrArg (fun k => k y.1)
          (MorphismProperty.Over.w
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) m)
        exact hm.trans y.2⟩ := by
  let pU := closedPointResidueFiberPointEquiv X x U
  have h := closedPointResidueFiberPointEquiv_map X x U W m (pU.symm y)
  calc
    closedPointResidueFiberPointEquiv X x W
        (((etaleBaseChange (closedPointResidueFieldMap X x)).map m).left
          (pU.symm y)) =
      ⟨m.left (pU (pU.symm y)).1, by
        have hm := congrArg (fun k => k (pU (pU.symm y)).1)
          (MorphismProperty.Over.w
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) m)
        exact hm.trans (pU (pU.symm y)).2⟩ := h
    _ = ⟨m.left y.1, by
        have hm := congrArg (fun k => k y.1)
          (MorphismProperty.Over.w
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) m)
        exact hm.trans y.2⟩ := by
          apply Subtype.ext
          exact congrArg m.left (congrArg Subtype.val (pU.apply_symm_apply y))

/-- On geometric fibers, the closed-point/height-one equivalence commutes
with the actual base change of `affineEtaleSpecObjectMap`. -/
theorem affineEtaleClosedPointResidueFiberEquivHeightOneFiber_geometric_map
    {R S T : Type u} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]
    [CommRing T] [IsDedekindDomain T] [Algebra S T] [Algebra.Etale S T]
    [Algebra R T] [IsScalarTower R S T] [Algebra.Etale R T]
    (hR : ¬ IsField R) (x : closedPoints (Spec (CommRingCat.of R)))
    (z : ((etaleBaseChange (closedPointResidueFieldMap
      (Spec (CommRingCat.of R)) x)).obj
        (affineEtaleSpecObject (R := R) (S := T))).left) :
    affineEtaleClosedPointResidueFiberEquivHeightOneFiber hR x
      (closedPointResidueFiberPointEquiv (Spec (CommRingCat.of R)) x
        (affineEtaleSpecObject (R := R) (S := S))
        (((etaleBaseChange (closedPointResidueFieldMap
          (Spec (CommRingCat.of R)) x)).map
            (affineEtaleSpecObjectMap (R := R) (S := S) (T := T))).left z)) =
      heightOneSpectrumContractionOfEtale (R := S) (S := T)
        (affineEtaleClosedPointResidueFiberEquivHeightOneFiber hR x
          (closedPointResidueFiberPointEquiv (Spec (CommRingCat.of R)) x
            (affineEtaleSpecObject (R := R) (S := T)) z)).1 := by
  rw [closedPointResidueFiberPointEquiv_map]
  exact affineEtaleClosedPointResidueFiberEquivHeightOneFiber_map
    hR x (closedPointResidueFiberPointEquiv
      (Spec (CommRingCat.of R)) x (affineEtaleSpecObject (R := R) (S := T)) z)

/-- Sections of a single closed-point divisor summand are functions on the
actual points of the residue-field fiber. The comparison is the arbitrary
étale-field section equivalence followed by the geometric fiber projection. -/
noncomputable def closedPointDivisorSummandSectionsAddEquiv
    (X : Scheme.{u}) (x : closedPoints X) (U : X.Etale) :
    ((closedPointDivisorSummand X x).obj.obj (op U)) ≃+
      (closedPointResidueFiber X x U → ULift.{u} ℤ) := by
  let V := (etaleBaseChange (closedPointResidueFieldMap X x)).obj U
  let e := fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec
    (X.residueField x.1) V (AddCommGrpCat.of (ULift.{u} ℤ))
  let points := closedPointResidueFiberPointEquiv X x U
  let r : (V.left → AddCommGrpCat.of (ULift.{u} ℤ)) →+
      (closedPointResidueFiber X x U → AddCommGrpCat.of (ULift.{u} ℤ)) :=
    { toFun := fun f y => f (points.symm y)
      map_zero' := by
        ext y
        rfl
      map_add' := by
        intro f g
        ext y
        rfl }
  have hr : Function.Bijective r :=
    (Equiv.arrowCongr points (Equiv.refl _)).bijective
  change (((constantSheaf (Spec (X.residueField x.1)).smallEtaleTopology
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))).obj.obj (op V)) ≃+
      (closedPointResidueFiber X x U → AddCommGrpCat.of (ULift.{u} ℤ))
  exact e.trans (AddEquiv.ofBijective r hr)

/-- The function description of a closed-point summand is natural under
morphisms of étale objects. -/
theorem closedPointDivisorSummandSectionsAddEquiv_naturality
    (X : Scheme.{u}) (x : closedPoints X) (U W : X.Etale) (m : U ⟶ W)
    (s : (closedPointDivisorSummand X x).obj.obj (op W))
    (y : closedPointResidueFiber X x U) :
    closedPointDivisorSummandSectionsAddEquiv X x U
      (((closedPointDivisorSummand X x).obj.map m.op).hom s) y =
    closedPointDivisorSummandSectionsAddEquiv X x W s
      ⟨m.left y.1, by
        have hm := congrArg (fun k => k y.1)
          (MorphismProperty.Over.w
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) m)
        exact hm.trans y.2⟩ := by
  let i := closedPointResidueFieldMap X x
  let B := etaleBaseChange i
  let V := B.obj U
  let T := B.obj W
  let n := B.map m
  let c := (constantSheaf (Spec (X.residueField x.1)).smallEtaleTopology
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  let pU := closedPointResidueFiberPointEquiv X x U
  let pW := closedPointResidueFiberPointEquiv X x W
  let yW : closedPointResidueFiber X x W := ⟨m.left y.1, by
    have hm := congrArg (fun k => k y.1)
      (MorphismProperty.Over.w
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) m)
    exact hm.trans y.2⟩
  have hmap : ((closedPointDivisorSummand X x).obj.map m.op).hom s =
      (c.obj.map n.op).hom s := by
    change (c.obj.map (B.map m).op).hom s = (c.obj.map n.op).hom s
    rfl
  have hfield := fieldEtaleConstantAbelianSectionsAddEquiv_morphism_naturality
    (X.residueField x.1) V T n (AddCommGrpCat.of (ULift.{u} ℤ)) s (pU.symm y)
  have hcoord : n.left (pU.symm y) = pW.symm yW := by
    apply pW.injective
    calc
      pW (n.left (pU.symm y)) = yW :=
        closedPointResidueFiberPointEquiv_symm_map X x U W m y
      _ = pW (pW.symm yW) := (pW.apply_symm_apply yW).symm
  rw [hmap]
  change (fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec
      (X.residueField x.1) V (AddCommGrpCat.of (ULift.{u} ℤ))
      ((c.obj.map n.op).hom s)) (pU.symm y) =
    (fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec
      (X.residueField x.1) T (AddCommGrpCat.of (ULift.{u} ℤ)) s) (pW.symm yW)
  exact hfield.trans (congrArg
    (fun q => (fieldEtaleConstantAbelianSectionsAddEquiv_of_exists_iso_sigmaSpec
      (X.residueField x.1) T (AddCommGrpCat.of (ULift.{u} ℤ)) s) q) hcoord)

/-- The actual closed-point divisor sheaf: the categorical coproduct of the
closed-point direct images of the constant integer sheaf. -/
noncomputable def closedPointDivisorSheaf (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := by
  let : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape X
  exact colimit (Discrete.functor (fun x : closedPoints X =>
    closedPointDivisorSummand X x))

/-- The canonical inclusion of one closed-point summand into the actual
divisor sheaf. -/
noncomputable def closedPointDivisorSheafInjection (X : Scheme.{u})
    (x : closedPoints X) :
    closedPointDivisorSummand X x ⟶ closedPointDivisorSheaf X := by
  let : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape X
  exact colimit.ι (Discrete.functor (closedPointDivisorSummand X)) ⟨x⟩

/-- After forgetting the additive-group structure, the sheafification map of an
abelian presheaf on the small étale site is locally surjective. -/
theorem etaleAbelianToSheafify_locallySurjective (X : Scheme.{u})
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (Functor.whiskerRight (toSheafify X.smallEtaleTopology P)
        (forget AddCommGrpCat.{u})) := by
  let hPres : X.smallEtaleTopology.PreservesSheafification
      (forget AddCommGrpCat.{u}) :=
    GrothendieckTopology.PreservesSheafification.transport
      X.smallEtaleTopology (Scheme.AffineEtale.topology X) (Scheme.AffineEtale.Spec X)
      (Type u) (forget AddCommGrpCat.{u})
  have hW : X.smallEtaleTopology.W
      (Functor.whiskerRight (toSheafify X.smallEtaleTopology P)
        (forget AddCommGrpCat.{u})) :=
    @GrothendieckTopology.W_of_preservesSheafification X.Etale _
      X.smallEtaleTopology AddCommGrpCat.{u} (Type u) _ _
      (forget AddCommGrpCat.{u}) hPres P
      (sheafify X.smallEtaleTopology P)
      (toSheafify X.smallEtaleTopology P)
      (X.smallEtaleTopology.W_toSheafify P)
  exact (X.smallEtaleTopology.W_iff_isLocallyBijective
    (A := Type u) (Functor.whiskerRight (toSheafify X.smallEtaleTopology P)
      (forget AddCommGrpCat.{u}))).mp hW |>.2

/-- A section of a sheafification of a discrete coproduct of étale
presheaves has a local preimage which is a finite sum of summand terms. -/
theorem etalePresheafCoproductSheafification_locally_finite_sum
    (X : Scheme.{u}) {ι : Type u} [DecidableEq ι]
    (F : ι → X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) (U : X.Etale)
    (s : (sheafify X.smallEtaleTopology
      (colimit (Discrete.functor F))).obj (op U)) :
    let f := toSheafify X.smallEtaleTopology (colimit (Discrete.functor F))
    Presheaf.imageSieve f s ∈ X.smallEtaleTopology U ∧
      ∀ V (g : V ⟶ U) (hg : (Presheaf.imageSieve f s).arrows g),
        ∃ T : Finset (Discrete ι),
          Presheaf.localPreimage f s g hg =
            ∑ i ∈ T,
              (Presheaf.discreteCoproductObjIsoDirectSum F (op V)).inv.hom
                (DirectSum.of
                  (fun j => (((Discrete.functor F).obj j).obj (op V) : Type u)) i
                  ((Presheaf.discreteCoproductObjIsoDirectSum F (op V)).hom.hom
                    (Presheaf.localPreimage f s g hg) i)) := by
  intro f
  have hloc := etaleAbelianToSheafify_locallySurjective X
    (colimit (Discrete.functor F))
  constructor
  · change Presheaf.imageSieve
      (Functor.whiskerRight f (forget AddCommGrpCat.{u})) s ∈ X.smallEtaleTopology U
    exact hloc.imageSieve_mem (U := U) s
  · intro V g hg
    exact Presheaf.discreteCoproductObj_eq_finite_sum F (op V)
      (Presheaf.localPreimage f s g hg)

variable {ι : Type u}
variable (X : Scheme.{u})
variable (F : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
variable [HasColimitsOfShape (Discrete ι)
  (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/-- The coproduct of sheaves is the sheafification of the coproduct of their
underlying presheaves. -/
noncomputable def sheafCoproductSheafificationIso :
    colimit (Discrete.functor F) ≅
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (colimit (Discrete.functor (fun i => (F i).obj))) := by
  let J := X.smallEtaleTopology
  let G := Discrete.functor F
  let E := colimit.cocone (G ⋙ sheafToPresheaf J AddCommGrpCat.{u})
  let hE := colimit.isColimit (G ⋙ sheafToPresheaf J AddCommGrpCat.{u})
  let c := Sheaf.sheafifyCocone E
  let hc := Sheaf.isColimitSheafifyCocone E hE
  let e1 : colimit G ≅
      (presheafToSheaf J AddCommGrpCat.{u}).obj E.pt :=
    colimit.isoColimitCocone ⟨c, hc⟩
  let n := Discrete.compNatIsoDiscrete F (sheafToPresheaf J AddCommGrpCat.{u})
  let e2 := HasColimit.isoOfNatIso n
  exact e1 ≪≫ (presheafToSheaf J AddCommGrpCat.{u}).mapIso e2

/-- Each sheaf coproduct injection agrees with the presheaf injection after
sheafification. -/
theorem sheafCoproductSheafificationIso_injection
    (i : Discrete ι) (V : X.Etale) :
    (colimit.ι (Discrete.functor F) i).hom.app (op V) ≫
        (sheafCoproductSheafificationIso X F).hom.hom.app (op V) =
      (colimit.ι (Discrete.functor (fun j => (F j).obj)) i).app (op V) ≫
        (toSheafify X.smallEtaleTopology
          (colimit (Discrete.functor (fun j => (F j).obj)))).app (op V) := by
  let J := X.smallEtaleTopology
  let G := Discrete.functor F
  let E := colimit.cocone (G ⋙ sheafToPresheaf J AddCommGrpCat.{u})
  let hE := colimit.isColimit (G ⋙ sheafToPresheaf J AddCommGrpCat.{u})
  let c := Sheaf.sheafifyCocone E
  let n := Discrete.compNatIsoDiscrete F (sheafToPresheaf J AddCommGrpCat.{u})
  let e2 := HasColimit.isoOfNatIso n
  let e := sheafCoproductSheafificationIso X F
  let e1 : colimit G ≅
      (presheafToSheaf J AddCommGrpCat.{u}).obj E.pt :=
    colimit.isoColimitCocone ⟨c, Sheaf.isColimitSheafifyCocone E hE⟩
  have hi : colimit.ι G i ≫ e1.hom = c.ι.app i := by
    exact colimit.isoColimitCocone_ι_hom ⟨c,
      Sheaf.isColimitSheafifyCocone E hE⟩ i
  have hcomp : E.ι.app i ≫ e2.hom =
      colimit.ι (Discrete.functor (fun j => (F j).obj)) i := by
    change colimit.ι (G ⋙ sheafToPresheaf J AddCommGrpCat.{u}) i ≫ e2.hom = _
    rw [HasColimit.ι_isoOfNatIso_hom]
    rw [Discrete.compNatIsoDiscrete_hom_app]
    exact Category.id_comp _
  have hnat' : e2.hom ≫
      toSheafify J (colimit (Discrete.functor (fun j => (F j).obj))) =
      toSheafify J E.pt ≫ sheafifyMap J e2.hom := by
    change e2.hom ≫
      toSheafify J (colimit (Discrete.functor
        ((sheafToPresheaf J AddCommGrpCat.{u}).obj ∘ F))) =
      toSheafify J (colimit (G ⋙ sheafToPresheaf J AddCommGrpCat.{u})) ≫
        sheafifyMap J e2.hom
    exact toSheafify_naturality (J := J) e2.hom
  have hcat : colimit.ι G i ≫ e.hom =
      c.ι.app i ≫ (presheafToSheaf J AddCommGrpCat.{u}).map e2.hom := by
    change colimit.ι G i ≫
      (e1.hom ≫ ((presheafToSheaf J AddCommGrpCat.{u}).mapIso e2).hom) = _
    rw [← Category.assoc, hi]
    rfl
  have hp : (c.ι.app i).hom ≫
      ((presheafToSheaf J AddCommGrpCat.{u}).map e2.hom).hom =
      (colimit.ι (Discrete.functor (fun j => (F j).obj)) i) ≫
        toSheafify J (colimit (Discrete.functor (fun j => (F j).obj))) := by
    rw [Sheaf.sheafifyCocone_ι_app_val E i]
    change (E.ι.app i ≫ toSheafify J E.pt) ≫ sheafifyMap J e2.hom = _
    rw [Category.assoc, ← hnat', ← Category.assoc, hcomp]
  calc
    _ = (colimit.ι G i ≫ e.hom).hom.app (op V) := rfl
    _ = (c.ι.app i ≫ (presheafToSheaf J AddCommGrpCat.{u}).map e2.hom).hom.app
        (op V) := congrArg (fun k => k.hom.app (op V)) hcat
    _ = _ := congrArg (fun k => k.app (op V)) hp

/-- A section of a coproduct of sheaves is locally a finite sum of sections
from its summands. -/
theorem sheaf_coproduct_locally_finite_sum (U : X.Etale)
    (s : (colimit (Discrete.functor F)).obj.obj (op U)) :
    ∃ R : Sieve U, R ∈ X.smallEtaleTopology U ∧
      ∀ V (g : V ⟶ U), R.arrows g →
        ∃ T : Finset ι, ∃ a : ∀ i, (F i).obj.obj (op V),
          ConcreteCategory.hom
              ((colimit (Discrete.functor F)).obj.map g.op) s =
            ∑ i ∈ T, ConcreteCategory.hom
              ((colimit.ι (Discrete.functor F) ⟨i⟩).hom.app (op V)) (a i) := by
  classical
  let J := X.smallEtaleTopology
  let Fp := fun i => (F i).obj
  let P := colimit (Discrete.functor Fp)
  let f := toSheafify J P
  let e := sheafCoproductSheafificationIso X F
  let s' := ConcreteCategory.hom (e.hom.hom.app (op U)) s
  have hLocal := etalePresheafCoproductSheafification_locally_finite_sum X Fp U s'
  let R := Presheaf.imageSieve f s'
  change R ∈ J U ∧ _ at hLocal
  rcases hLocal with ⟨hR, hFiber⟩
  refine ⟨R, hR, ?_⟩
  intro V g hg
  obtain ⟨Td, hTd⟩ := hFiber V g hg
  let t := Presheaf.localPreimage f s' g hg
  let d := Presheaf.discreteCoproductObjIsoDirectSum Fp (op V)
  let a : ∀ i : ι, (F i).obj.obj (op V) := fun i => d.hom.hom t ⟨i⟩
  let T : Finset ι := Td.image (fun j : Discrete ι => j.as)
  have hInjective : Set.InjOn (fun j : Discrete ι => j.as) (↑Td : Set (Discrete ι)) := by
    intro j hj k hk h
    exact Discrete.ext h
  have hPres : t = ∑ j ∈ Td, ConcreteCategory.hom
      ((colimit.ι (Discrete.functor Fp) j).app (op V)) (a j.as) := by
    calc
      t = ∑ j ∈ Td, d.inv.hom
          (DirectSum.of (fun k : Discrete ι =>
            (((Discrete.functor Fp).obj k).obj (op V) : Type u)) j
              (d.hom.hom t j)) := hTd
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        exact Presheaf.discreteCoproductObjIsoDirectSum_inv_of
          Fp (op V) j (d.hom.hom t j)
  have hF : ConcreteCategory.hom (f.app (op V)) t =
      ∑ j ∈ Td, ConcreteCategory.hom (f.app (op V))
        (ConcreteCategory.hom ((colimit.ι (Discrete.functor Fp) j).app (op V))
          (a j.as)) := by
    rw [hPres]
    simp only [map_sum]
  have hRes : ConcreteCategory.hom (e.hom.hom.app (op V))
      (ConcreteCategory.hom ((colimit (Discrete.functor F)).obj.map g.op) s) =
      ConcreteCategory.hom (f.app (op V)) t := by
    rw [Presheaf.app_localPreimage f s' g hg]
    exact NatTrans.naturality_apply e.hom.hom g.op s
  have hCompat (j : Discrete ι) :
      ConcreteCategory.hom (e.hom.hom.app (op V))
          (ConcreteCategory.hom ((colimit.ι (Discrete.functor F) j).hom.app (op V))
            (a j.as)) =
        ConcreteCategory.hom (f.app (op V))
          (ConcreteCategory.hom ((colimit.ι (Discrete.functor Fp) j).app (op V))
            (a j.as)) := by
    have h := ConcreteCategory.congr_hom
      (sheafCoproductSheafificationIso_injection X F j V) (a j.as)
    simpa only [ConcreteCategory.comp_apply] using h
  have hImage : ConcreteCategory.hom (e.hom.hom.app (op V))
      (ConcreteCategory.hom ((colimit (Discrete.functor F)).obj.map g.op) s) =
      ConcreteCategory.hom (e.hom.hom.app (op V))
        (∑ i ∈ T, ConcreteCategory.hom
          ((colimit.ι (Discrete.functor F) ⟨i⟩).hom.app (op V)) (a i)) := by
    rw [hRes]
    calc
      ConcreteCategory.hom (f.app (op V)) t =
          ∑ j ∈ Td, ConcreteCategory.hom (f.app (op V))
            (ConcreteCategory.hom ((colimit.ι (Discrete.functor Fp) j).app (op V))
              (a j.as)) := hF
      _ = ∑ j ∈ Td, ConcreteCategory.hom (e.hom.hom.app (op V))
            (ConcreteCategory.hom ((colimit.ι (Discrete.functor F) j).hom.app (op V))
              (a j.as)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (hCompat j).symm
      _ = ConcreteCategory.hom (e.hom.hom.app (op V))
            (∑ i ∈ T, ConcreteCategory.hom
              ((colimit.ι (Discrete.functor F) ⟨i⟩).hom.app (op V)) (a i)) := by
        simp only [map_sum]
        rw [Finset.sum_image hInjective]
  have hinj : Function.Injective
      (ConcreteCategory.hom (e.hom.hom.app (op V))) := by
    have hIso : IsIso (e.hom.hom) := by
      change IsIso ((sheafToPresheaf J AddCommGrpCat.{u}).map e.hom)
      infer_instance
    have hIsoV : IsIso (e.hom.hom.app (op V)) :=
      (NatTrans.isIso_iff_isIso_app e.hom.hom).mp hIso (op V)
    exact (ConcreteCategory.isIso_iff_bijective _).mp hIsoV |>.1
  exact ⟨T, a, hinj hImage⟩

/-- The canonical projection from a sheaf coproduct to one summand. -/
noncomputable def sheafCoproductComponentProjection (i : ι) :
    colimit (Discrete.functor F) ⟶ F i := by
  classical
  let c : Cocone (Discrete.functor F) := {
    pt := F i
    ι := {
      app := fun j => if h : j.as = i then eqToHom (congrArg F h) else 0
      naturality := by
        intro j k f
        have h : j = k := Discrete.ext f.eq
        subst k
        rw [Subsingleton.elim f (𝟙 j)]
        rfl
    }
  }
  exact colimit.desc (Discrete.functor F) c

/-- The canonical component projection from the actual closed-point divisor
sheaf to one summand. -/
noncomputable def closedPointDivisorSheafComponentProjection (X : Scheme.{u})
    (x : closedPoints X) :
    closedPointDivisorSheaf X ⟶ closedPointDivisorSummand X x := by
  let : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape X
  exact sheafCoproductComponentProjection X (closedPointDivisorSummand X) x

/-- A coproduct injection followed by the corresponding component projection
is the identity. -/
@[simp] theorem sheafCoproductInjection_comp_componentProjection
    (i : ι) :
    colimit.ι (Discrete.functor F) ⟨i⟩ ≫
      sheafCoproductComponentProjection X F i = 𝟙 (F i) := by
  classical
  dsimp only [sheafCoproductComponentProjection]
  rw [colimit.ι_desc]
  simp only [Discrete.functor_obj, dite_eq_left, eqToHom_refl]

/-- A coproduct injection followed by a different component projection is
zero. -/
theorem sheafCoproductInjection_comp_componentProjection_of_ne
    {i j : ι} (hij : i ≠ j) :
    colimit.ι (Discrete.functor F) ⟨i⟩ ≫
      sheafCoproductComponentProjection X F j = 0 := by
  classical
  dsimp only [sheafCoproductComponentProjection]
  rw [colimit.ι_desc]
  simp only [Discrete.functor_obj, dite_eq_right hij]

/-- Evaluating a component projection after its matching injection returns
the original section. -/
theorem sheafCoproductComponentProjection_app_injection
    (i : ι) (V : X.Etale) (z : (F i).obj.obj (op V)) :
    ConcreteCategory.hom
        ((sheafCoproductComponentProjection X F i).hom.app (op V))
        (ConcreteCategory.hom
          ((colimit.ι (Discrete.functor F) ⟨i⟩).hom.app (op V)) z) = z := by
  have h := sheafCoproductInjection_comp_componentProjection X F i
  have hV := congrArg (fun f => f.hom.app (op V)) h
  exact ConcreteCategory.congr_hom hV z

/-- Evaluating a component projection after a different injection gives
zero. -/
theorem sheafCoproductComponentProjection_app_injection_of_ne
    {i j : ι} (hij : i ≠ j) (V : X.Etale) (z : (F i).obj.obj (op V)) :
    ConcreteCategory.hom
        ((sheafCoproductComponentProjection X F j).hom.app (op V))
        (ConcreteCategory.hom
          ((colimit.ι (Discrete.functor F) ⟨i⟩).hom.app (op V)) z) = 0 := by
  have h := sheafCoproductInjection_comp_componentProjection_of_ne X F hij
  have hV := congrArg (fun f => f.hom.app (op V)) h
  exact ConcreteCategory.congr_hom hV z

/-- The component projection recovers a section after its matching
closed-point summand is included. -/
theorem closedPointDivisorSheafComponentProjection_app_injection
    (X : Scheme.{u}) (x : closedPoints X) (V : X.Etale)
    (z : (closedPointDivisorSummand X x).obj.obj (op V)) :
    ConcreteCategory.hom
        ((closedPointDivisorSheafComponentProjection X x).hom.app (op V))
        (ConcreteCategory.hom
          ((closedPointDivisorSheafInjection X x).hom.app (op V)) z) = z := by
  convert (@sheafCoproductComponentProjection_app_injection
    (closedPoints X) X (closedPointDivisorSummand X)
    (closedPointDivisorSheafHasColimitsOfShape X) x V z) using 1
  all_goals rfl

/-- The component projection annihilates every other closed-point summand
inclusion. -/
theorem closedPointDivisorSheafComponentProjection_app_injection_of_ne
    {X : Scheme.{u}} {x y : closedPoints X} (hxy : x ≠ y) (V : X.Etale)
    (z : (closedPointDivisorSummand X x).obj.obj (op V)) :
    ConcreteCategory.hom
        ((closedPointDivisorSheafComponentProjection X y).hom.app (op V))
        (ConcreteCategory.hom
          ((closedPointDivisorSheafInjection X x).hom.app (op V)) z) = 0 := by
  convert (@sheafCoproductComponentProjection_app_injection_of_ne
    (closedPoints X) X (closedPointDivisorSummand X)
    (closedPointDivisorSheafHasColimitsOfShape X) x y hxy V z) using 1
  all_goals rfl

/-- Over a quasi-compact étale object, a section of a sheaf coproduct is a
finite sum of the images of its component projections. -/
theorem sheafCoproductSection_finiteSupport_of_quasiCompact
    (U : X.Etale) [QuasiCompact (terminal.from U.left)]
    (s : (colimit (Discrete.functor F)).obj.obj (op U)) :
    ∃ T : Finset ι,
      s = ∑ i ∈ T,
        ConcreteCategory.hom ((colimit.ι (Discrete.functor F) ⟨i⟩).hom.app (op U))
          (ConcreteCategory.hom
            ((sheafCoproductComponentProjection X F i).hom.app (op U)) s) := by
  classical
  let H := colimit (Discrete.functor F)
  have : CompactSpace U.left :=
    (AlgebraicGeometry.compactSpace_iff_quasiCompact U.left).2 inferInstance
  have hUcompact : IsCompact (Set.univ : Set U.left) := isCompact_univ
  obtain ⟨R, hR, hFiber⟩ := sheaf_coproduct_locally_finite_sum X F U s
  let I := Σ V : X.Etale, {g : V ⟶ U // R.arrows g}
  let arrow (i : I) : i.1 ⟶ U := i.2.val
  have hSieve : Sieve.ofArrows (fun i : I => i.1) arrow = R := by
    ext V g
    rw [Sieve.mem_ofArrows_iff]
    constructor
    · rintro ⟨i, k, rfl⟩
      exact R.downward_closed i.2.property k
    · intro hg
      exact ⟨⟨V, ⟨g, hg⟩⟩, 𝟙 V, Category.id_comp g⟩
  have hCoverR : Sieve.ofArrows (fun i : I => i.1) arrow ∈ X.smallEtaleTopology U := by
    rw [hSieve]
    exact hR
  have hRanges := (Scheme.ofArrows_mem_smallEtaleTopology_iff arrow).mp hCoverR
  obtain ⟨K, hK⟩ := hUcompact.elim_finite_subcover
    (fun i : I => Set.range (arrow i).left)
    (fun i => (arrow i).left.isOpenMap.isOpen_range)
    (by
      intro x hx
      have hx' : x ∈ ⋃ i : I, Set.range (arrow i).left := by
        rw [hRanges]
        exact Set.mem_univ x
      exact hx')
  let K' := {i : I // i ∈ K}
  have hRangesK : ⋃ i : K', Set.range (arrow i.1).left = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hK (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  have hCoverK :
      Sieve.ofArrows (fun i : K' => i.1.1) (fun i => arrow i.1) ∈
        X.smallEtaleTopology U :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun i : K' => arrow i.1)).mpr hRangesK
  have hChoice (i : I) : ∃ T : Finset ι, ∃ a : ∀ j, (F j).obj.obj (op i.1),
      ConcreteCategory.hom (H.obj.map (arrow i).op) s =
        ∑ j ∈ T, ConcreteCategory.hom
          ((colimit.ι (Discrete.functor F) ⟨j⟩).hom.app (op i.1)) (a j) :=
    hFiber i.1 (arrow i) i.2.property
  choose support coeff hLocal using hChoice
  let S : Finset ι := K.biUnion support
  have hSupport (i : I) (hi : i ∈ K) : support i ⊆ S := by
    intro j hj
    exact Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
  let component (j : ι) : (F j).obj.obj (op U) :=
    ConcreteCategory.hom ((sheafCoproductComponentProjection X F j).hom.app (op U)) s
  let d : H.obj.obj (op U) := ∑ j ∈ S,
    ConcreteCategory.hom ((colimit.ι (Discrete.functor F) ⟨j⟩).hom.app (op U))
      (component j)
  have hProjectedLocal (i : I) (j : ι) :
      ConcreteCategory.hom ((F j).obj.map (arrow i).op) (component j) =
        if j ∈ support i then coeff i j else 0 := by
    let p := sheafCoproductComponentProjection X F j
    have h := congrArg (ConcreteCategory.hom (p.hom.app (op i.1))) (hLocal i)
    have hNat : ConcreteCategory.hom (p.hom.app (op i.1))
        (ConcreteCategory.hom (H.obj.map (arrow i).op) s) =
        ConcreteCategory.hom ((F j).obj.map (arrow i).op) (component j) :=
      NatTrans.naturality_apply p.hom (arrow i).op s
    rw [hNat] at h
    rw [map_sum] at h
    by_cases hj : j ∈ support i
    · have hsingle :
          ∑ k ∈ support i, ConcreteCategory.hom (p.hom.app (op i.1))
            (ConcreteCategory.hom
              ((colimit.ι (Discrete.functor F) ⟨k⟩).hom.app (op i.1)) (coeff i k)) =
            coeff i j := by
        rw [Finset.sum_eq_single j]
        · exact sheafCoproductComponentProjection_app_injection X F j i.1 (coeff i j)
        · intro k hk hkj
          exact sheafCoproductComponentProjection_app_injection_of_ne
            (X := X) (F := F) (i := k) (j := j) hkj i.1 (coeff i k)
        · intro hnot
          exact (hnot hj).elim
      rw [hsingle] at h
      rw [ite_eq_left hj]
      exact h
    · have hzero :
          ∑ k ∈ support i, ConcreteCategory.hom (p.hom.app (op i.1))
            (ConcreteCategory.hom
              ((colimit.ι (Discrete.functor F) ⟨k⟩).hom.app (op i.1)) (coeff i k)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hne : k ≠ j := by
          intro hkj
          exact hj (hkj ▸ hk)
        exact sheafCoproductComponentProjection_app_injection_of_ne
          (X := X) (F := F) (i := k) (j := j) hne i.1 (coeff i k)
      rw [hzero] at h
      rw [ite_eq_right hj]
      exact h
  have hOnArrow (i : I) (hi : i ∈ K) :
      ConcreteCategory.hom (H.obj.map (arrow i).op) s =
        ConcreteCategory.hom (H.obj.map (arrow i).op) d := by
    have hsum : ConcreteCategory.hom (H.obj.map (arrow i).op) d =
        ∑ j ∈ S, ConcreteCategory.hom
          ((colimit.ι (Discrete.functor F) ⟨j⟩).hom.app (op i.1))
            (ConcreteCategory.hom ((F j).obj.map (arrow i).op) (component j)) := by
      dsimp [d]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hInjNat := NatTrans.naturality_apply
        (colimit.ι (Discrete.functor F) ⟨j⟩).hom (arrow i).op (component j)
      exact hInjNat.symm
    have hsum' : ConcreteCategory.hom (H.obj.map (arrow i).op) d =
        ∑ j ∈ S, (if j ∈ support i then
          ConcreteCategory.hom
            ((colimit.ι (Discrete.functor F) ⟨j⟩).hom.app (op i.1)) (coeff i j)
          else 0) := by
      rw [hsum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hProjectedLocal i j]
      split_ifs with hmem
      · rfl
      · rw [map_zero]
    have hsumSupport :
        ∑ j ∈ S, (if j ∈ support i then
          ConcreteCategory.hom
            ((colimit.ι (Discrete.functor F) ⟨j⟩).hom.app (op i.1)) (coeff i j)
          else 0) =
        ∑ j ∈ support i, ConcreteCategory.hom
          ((colimit.ι (Discrete.functor F) ⟨j⟩).hom.app (op i.1)) (coeff i j) := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hSupport i hi)]
    rw [hLocal i, hsum', hsumSupport]
  let sieve : Sieve U := Sieve.ofArrows (fun i : K' => i.1.1) (fun i => arrow i.1)
  have hSeparated := H.isSeparated U sieve hCoverK
  refine ⟨S, ?_⟩
  apply hSeparated s d
  intro V g hg
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  rw [op_comp, H.obj.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact congrArg (ConcreteCategory.hom (H.obj.map k.op)) (hOnArrow i.1 i.2)

/-- Over a quasi-compact étale object, a section of the closed-point divisor
sheaf has finite support among the closed-point summands. -/
theorem closedPointDivisorSheaf_finiteSupport_of_quasiCompact
    (X : Scheme.{u}) (U : X.Etale)
    [QuasiCompact (terminal.from U.left)]
    (s : (closedPointDivisorSheaf X).obj.obj (op U)) :
    let _ : HasColimitsOfShape (Discrete (closedPoints X))
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape X
    ∃ T : Finset (closedPoints X),
      s = ∑ x ∈ T,
        ConcreteCategory.hom
          ((colimit.ι (Discrete.functor (closedPointDivisorSummand X)) ⟨x⟩).hom.app (op U))
          (ConcreteCategory.hom
            ((sheafCoproductComponentProjection X
              (closedPointDivisorSummand X) x).hom.app (op U)) s) := by
  classical
  intro hColimits
  exact sheafCoproductSection_finiteSupport_of_quasiCompact
    X (closedPointDivisorSummand X) U s

/-- A section of the actual closed-point divisor sheaf is locally a finite
sum of sections from its closed-point summands. -/
theorem closedPointDivisorSheaf_locally_finite_sum
    (X : Scheme.{u}) (U : X.Etale)
    (s : (closedPointDivisorSheaf X).obj.obj (op U)) :
    let _ : HasColimitsOfShape (Discrete (closedPoints X))
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape X
    ∃ R : Sieve U, R ∈ X.smallEtaleTopology U ∧
      ∀ V (g : V ⟶ U), R.arrows g →
        ∃ T : Finset (closedPoints X),
          ∃ a : ∀ x, (closedPointDivisorSummand X x).obj.obj (op V),
            ConcreteCategory.hom
                ((closedPointDivisorSheaf X).obj.map g.op) s =
              ∑ x ∈ T, ConcreteCategory.hom
                ((colimit.ι (Discrete.functor
                  (closedPointDivisorSummand X)) ⟨x⟩).hom.app (op V)) (a x) := by
  classical
  intro hColimits
  exact sheaf_coproduct_locally_finite_sum X (closedPointDivisorSummand X) U s

end EtaleCohomology
