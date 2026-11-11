/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Nyll.EtaleFundamentalGroups.Cohomology.DVRGenericUnitQuotient
public import Nyll.EtaleCohomology.Sites.ZariskiGeometricStalks
public import Nyll.EtaleCohomology.Classical.AffineGenericUnitQuotient
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.SchemeTheory.RingTheory.Etale.UnramifiedDedekind
public import Nyll.SchemeTheory.Divisors.DedekindPrincipalDivisor
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Nyll.SchemeTheory.Divisors.DVRUnitQuotient
public import Nyll.SchemeTheory.Sheaves.UnitStalks

/-! # Rational divisor classes on actual open subschemes

This file supplies affine divisor and geometric-stalk comparison components
related to [Stacks Project, Theorem 59.68.1 (Tag 03RI)](https://stacks.math.columbia.edu/tag/03RI);
it does not prove the completed global sheaf exact sequence.
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsDedekindDomain
namespace EtaleFundamentalGroups.StrictHenselian
universe u
variable (R : Type u) [CommRing R] [IsDedekindDomain R]

omit [IsDedekindDomain R] in
private theorem specMap_point_asIdeal_eq_ker
    {Ω : Type u} [Field Ω] (φ : R →+* Ω) (ξ : Spec (CommRingCat.of Ω)) :
    (Spec.map (CommRingCat.ofHom φ) ξ).asIdeal = RingHom.ker φ := by
  have hξ : ξ = default := Subsingleton.elim _ _
  rw [hξ]
  change (PrimeSpectrum.comap φ (⊥ : PrimeSpectrum Ω)).asIdeal = RingHom.ker φ
  rw [PrimeSpectrum.comap_asIdeal]
  exact (RingHom.ker_eq_comap_bot φ).symm

/-- The actual quotient-sheaf representative of a rational unit on any
small-etale object over the affine base. -/
def genericRationalUnitQuotientRepresentative
    (W : (Spec (CommRingCat.of R)).Etale) (a : Additive (FractionRing R)ˣ) :
    (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op W) :=
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  (cokernel.π (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)).hom.app (op W)
    (Additive.ofMul (Units.map
      (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
        (pullback.snd W.hom j).appTop).hom.toMonoidHom) a.toMul))

/-- The actual quotient-sheaf section induced by a rational unit on an open subscheme. -/
def genericRationalUnitQuotientSection
    (U : (Spec (CommRingCat.of R)).Opens) (a : Additive (FractionRing R)ˣ) :
    (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj U)) :=
  genericRationalUnitQuotientRepresentative R
    ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj U) a

/-- Zero order at every non-generic geometric point of an open makes the
actual rational divisor class zero on that open. Generic-point vanishing
is supplied by the proved zero-stalk theorem. -/
theorem genericRationalUnitQuotientSection_eq_zero
    (U : (Spec (CommRingCat.of R)).Opens) (a : Additive (FractionRing R)ˣ)
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
      (ξ : Spec (CommRingCat.of Ω)),
      (Spec.map (CommRingCat.ofHom φ)) ξ ∈ U →
      ∀ v : HeightOneSpectrum R, v.asIdeal = RingHom.ker φ →
        FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = 0) :
    genericRationalUnitQuotientSection R U a = 0 := by
  let X := Spec (CommRingCat.of R)
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let g := EtaleCohomology.etaleMultiplicativeGroupToPushforward j
  let Q := cokernel g
  let W := (EtaleCohomology.zariskiToEtale X).obj U
  apply EtaleCohomology.etaleZariskiAbelianSection_eq_of_geometric_germs_eq
    Q U (genericRationalUnitQuotientSection R U a) 0
  intro Ω _ _ s ξ hU
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  let Φ := Scheme.pointSmallEtale (Spec.map φ)
  let t := EtaleCohomology.zariskiGeometricLift (Spec.map φ) ξ U hU
  rw [map_zero]
  by_cases hφ : RingHom.ker φ.hom = ⊥
  · have hz := geometricGenericUnitQuotientStalk_isZero_of_injective R φ.hom
      ((RingHom.injective_iff_ker_eq_bot φ.hom).mpr hφ)
    exact (AddCommGrpCat.subsingleton_of_isZero hz).elim _ _
  · let v : HeightOneSpectrum R := ⟨RingHom.ker φ.hom, RingHom.ker_isPrime φ.hom, hφ⟩
    have hv : v.asIdeal = RingHom.ker φ.hom := rfl
    let P := etaleBaseChangedSections j
    let z : (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P).obj
        (Opposite.op W) := Additive.ofMul (Units.map
      (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
        (pullback.snd W.hom j).appTop).hom.toMonoidHom) a.toMul)
    have hn := ConcreteCategory.congr_hom
      (Φ.toPresheafFiber_naturality (cokernel.π g).hom W t) z
    change (Φ.presheafFiber (A := AddCommGrpCat.{u})).map (cokernel.π g).hom
        (Φ.toPresheafFiber W t
          (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P) z) =
      Φ.toPresheafFiber W t Q.obj ((cokernel.π g).hom.app (op W) z) at hn
    change Φ.toPresheafFiber W t Q.obj
      ((cokernel.π g).hom.app (op W) z) = 0
    rw [← hn]
    exact geometricGenericUnitQuotient_rational_germ_eq_zero
      (R := R) (φ := φ.hom) (v := v) (hv := hv)
      W t a (h Ω φ.hom ξ hU v hv)

/-- A zero actual rational quotient section has order zero at every closed
geometric point of its domain. -/
theorem principalDivisor_eq_zero_of_genericRationalUnitQuotientSection_eq_zero
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
    (ξ : Spec (CommRingCat.of Ω))
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (Spec.map (CommRingCat.ofHom φ)) ξ ∈ U)
    (v : HeightOneSpectrum R) (hv : v.asIdeal = RingHom.ker φ)
    (a : Additive (FractionRing R)ˣ)
    (ha : genericRationalUnitQuotientSection R U a = 0) :
    FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = 0 := by
  let X := Spec (CommRingCat.of R)
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let g := EtaleCohomology.etaleMultiplicativeGroupToPushforward j
  let Q := cokernel g
  let W := (EtaleCohomology.zariskiToEtale X).obj U
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let t := EtaleCohomology.zariskiGeometricLift
    (Spec.map (CommRingCat.ofHom φ)) ξ U hU
  let P := etaleBaseChangedSections j
  let z : (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P).obj
      (Opposite.op W) := Additive.ofMul (Units.map
    (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
      (pullback.snd W.hom j).appTop).hom.toMonoidHom) a.toMul)
  have hn := ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_naturality (cokernel.π g).hom W t) z
  change (Φ.presheafFiber (A := AddCommGrpCat.{u})).map (cokernel.π g).hom
      (Φ.toPresheafFiber W t
        (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P) z) =
    Φ.toPresheafFiber W t Q.obj ((cokernel.π g).hom.app (op W) z) at hn
  apply principalDivisor_eq_zero_of_geometricGenericUnitQuotient_rational_germ_eq_zero
    (R := R) (φ := φ) (v := v) (hv := hv) W t a
  change (Φ.presheafFiber (A := AddCommGrpCat.{u})).map (cokernel.π g).hom
    (Φ.toPresheafFiber W t
      (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P) z) = 0
  rw [hn]
  change Φ.toPresheafFiber W t Q.obj (genericRationalUnitQuotientSection R U a) = 0
  rw [ha, map_zero]

/-- Ordinary basic-open order vanishing suffices for zero in the actual quotient sheaf. -/
theorem genericRationalUnitQuotientSection_basicOpen_eq_zero
    (s : R) (a : Additive (FractionRing R)ˣ)
    (h : ∀ v : HeightOneSpectrum R, s ∉ v.asIdeal →
      FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = 0) :
    genericRationalUnitQuotientSection R
      ((Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s)) a = 0 := by
  apply genericRationalUnitQuotientSection_eq_zero
  intro Ω _ _ φ ξ hU v hv
  apply h v
  have hpoint := specMap_point_asIdeal_eq_ker R φ ξ
  have hU' : (Spec.map (CommRingCat.ofHom φ) ξ) ∈ PrimeSpectrum.basicOpen s := by
    rw [← basicOpen_eq_of_affine (R := CommRingCat.of R) s]
    exact hU
  have hs := (PrimeSpectrum.mem_basicOpen s _).mp hU'
  rwa [hpoint, ← hv] at hs

omit [IsDedekindDomain R] in
/-- The actual quotient class is additive in the rational function written additively. -/
theorem genericRationalUnitQuotientSection_sub
    (U : (Spec (CommRingCat.of R)).Opens) (a b : Additive (FractionRing R)ˣ) :
    genericRationalUnitQuotientSection R U (a - b) =
      genericRationalUnitQuotientSection R U a -
        genericRationalUnitQuotientSection R U b := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let W := (EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj U
  let f := (Units.map
    (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
      (pullback.snd W.hom j).appTop).hom.toMonoidHom)).toAdditive
  let q := (cokernel.π
    (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)).hom.app (op W)
  change (ConcreteCategory.hom q) (f (a - b)) =
    (ConcreteCategory.hom q) (f a) - (ConcreteCategory.hom q) (f b)
  rw [map_sub]
  exact (ConcreteCategory.hom q).map_sub _ _

/-- Local rational representatives with equal divisor coefficients define
the same actual quotient-sheaf section on the basic open. -/
theorem genericRationalUnitQuotientSection_basicOpen_eq
    (s : R) (a b : Additive (FractionRing R)ˣ)
    (h : ∀ v : HeightOneSpectrum R, s ∉ v.asIdeal →
      FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v =
        FractionalIdeal.principalDivisorAddHom R (FractionRing R) b v) :
    genericRationalUnitQuotientSection R
      ((Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s)) a =
      genericRationalUnitQuotientSection R
        ((Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s)) b := by
  apply sub_eq_zero.mp
  rw [← genericRationalUnitQuotientSection_sub
    (R := R) ((Spec (CommRingCat.of R)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s)) a b]
  apply genericRationalUnitQuotientSection_basicOpen_eq_zero
  intro v hv
  rw [map_sub, Finsupp.sub_apply, h v hv, sub_self]

omit [IsDedekindDomain R] in
/-- Rational quotient classes restrict along the actual inclusions of open subschemes. -/
theorem genericRationalUnitQuotientSection_restrict
    {U V : (Spec (CommRingCat.of R)).Opens} (hUV : U ≤ V)
    (a : Additive (FractionRing R)ˣ) :
    (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.map
        ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).map
          (homOfLE hUV)).op
        (genericRationalUnitQuotientSection R V a) =
      genericRationalUnitQuotientSection R U a := by
  let X := Spec (CommRingCat.of R)
  let K := FractionRing R
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let Z := EtaleCohomology.zariskiToEtale X
  let WU := Z.obj U
  let WV := Z.obj V
  let g := Z.map (homOfLE hUV)
  let gUnit := EtaleCohomology.etaleMultiplicativeGroupToPushforward j
  let q := cokernel.π gUnit
  let zV := Additive.ofMul (Units.map
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (pullback.snd WV.hom j).appTop).hom.toMonoidHom) a.toMul)
  let zU := Additive.ofMul (Units.map
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (pullback.snd WU.hom j).appTop).hom.toMonoidHom) a.toMul)
  have hz :
      ((EtaleCohomology.etaleAbelianPushforward j).obj
        (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of K)))).obj.map
          g.op zV = zU := by
    change ((EtaleCohomology.etaleAbelianPushforward j).obj
      (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of K)))).obj.map
        g.op (Additive.ofMul (Units.map
          (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
            (pullback.snd WV.hom j).appTop).hom.toMonoidHom) a.toMul)) =
      Additive.ofMul (Units.map
        (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
          (pullback.snd WU.hom j).appTop).hom.toMonoidHom) a.toMul)
    exact EtaleCohomology.rationalUnitDirectImage_naturality
      (R := R) (K := K) WV WU g a
  have hq := ConcreteCategory.congr_hom (q.hom.naturality g.op) zV
  change (cokernel gUnit).obj.map g.op (q.hom.app (op WV) zV) =
    q.hom.app (op WU) zU
  exact hq.symm.trans (congrArg (q.hom.app (op WU)) hz)

omit [IsDedekindDomain R] in
/-- Rational-unit quotient sections respect addition. -/
theorem genericRationalUnitQuotientSection_add
    (U : (Spec (CommRingCat.of R)).Opens) (a b : Additive (FractionRing R)ˣ) :
    genericRationalUnitQuotientSection R U (a + b) =
      genericRationalUnitQuotientSection R U a +
        genericRationalUnitQuotientSection R U b := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let W := (EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj U
  let f := (Units.map
    (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
      (pullback.snd W.hom j).appTop).hom.toMonoidHom)).toAdditive
  let q := (cokernel.π
    (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)).hom.app (op W)
  change (ConcreteCategory.hom q) (f (a + b)) =
    (ConcreteCategory.hom q) (f a) + (ConcreteCategory.hom q) (f b)
  rw [map_add]
  exact (ConcreteCategory.hom q).map_add _ _

/-- Local rational representatives characterize a divisor section in the actual quotient sheaf. -/
def IsGenericUnitDivisorSection
    (D : HeightOneSpectrum R →₀ ℤ)
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤))) : Prop :=
  let X := Spec (CommRingCat.of R)
  let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  let Z := EtaleCohomology.zariskiToEtale X
  ∀ p : PrimeSpectrum R, ∃ (s : R) (a : Additive (FractionRing R)ˣ),
    s ∉ p.asIdeal ∧
    (∀ v : HeightOneSpectrum R, s ∉ v.asIdeal →
      FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = D v) ∧
    Q.obj.map (Z.map (homOfLE (show
      X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s) ≤ ⊤ from le_top))).op q =
      genericRationalUnitQuotientSection R
        (X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s)) a

/-- A finite divisor on a Dedekind affine scheme is represented by an actual
global section of the quotient of generic units by regular units.
The local rational representatives and their covering are constructed. -/
theorem exists_genericUnitQuotientSection_of_divisor
    (D : HeightOneSpectrum R →₀ ℤ) :
    let X := Spec (CommRingCat.of R)
    let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
    let Z := EtaleCohomology.zariskiToEtale X
    ∃ q : Q.obj.obj (op (Z.obj ⊤)), IsGenericUnitDivisorSection R D q := by
  intro X j Q Z
  classical
  have hlocal := FractionalIdeal.exists_principalDivisor_eq_on_basicOpen_at_prime
    R (FractionRing R) D
  choose s a hmem hdiv using hlocal
  let U : PrimeSpectrum R → X.Opens :=
    fun p => X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (s p))
  let H : TopCat.Sheaf AddCommGrpCat.{u} X :=
    ⟨Z.op ⋙ Q.obj, ((EtaleCohomology.etaleZariskiRestriction X AddCommGrpCat.{u}).obj Q).property⟩
  let sf := fun p => genericRationalUnitQuotientSection R (U p) (a p)
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro p _
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨p, ?_⟩
    change p ∈ X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (s p))
    rw [basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen (s p) p).mpr (hmem p)
  have hcompatible : TopCat.Presheaf.IsCompatible H.obj U sf := by
    intro p q
    change Q.obj.map (Z.map (homOfLE inf_le_left)).op (sf p) =
      Q.obj.map (Z.map (homOfLE inf_le_right)).op (sf q)
    rw [genericRationalUnitQuotientSection_restrict,
      genericRationalUnitQuotientSection_restrict]
    apply sub_eq_zero.mp
    rw [← genericRationalUnitQuotientSection_sub]
    apply genericRationalUnitQuotientSection_eq_zero
    intro Ω _ _ φ ξ hU v hv
    have hnot (i : PrimeSpectrum R)
        (hi : (Spec.map (CommRingCat.ofHom φ)) ξ ∈ U i) : s i ∉ v.asIdeal := by
      change (Spec.map (CommRingCat.ofHom φ)) ξ ∈
        X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (s i)) at hi
      rw [basicOpen_eq_of_affine] at hi
      have ht := (PrimeSpectrum.mem_basicOpen (s i) _).mp hi
      rwa [specMap_point_asIdeal_eq_ker R φ ξ, ← hv] at ht
    rw [map_sub, Finsupp.sub_apply, hdiv p v (hnot p hU.1),
      hdiv q v (hnot q hU.2), sub_self]
  obtain ⟨q, hq, _⟩ := H.existsUnique_gluing' U ⊤
    (fun p => homOfLE (show U p ≤ ⊤ from le_top)) hcover sf hcompatible
  refine ⟨q, ?_⟩
  change ∀ p : PrimeSpectrum R, ∃ (s : R) (a : Additive (FractionRing R)ˣ),
    s ∉ p.asIdeal ∧
    (∀ v : HeightOneSpectrum R, s ∉ v.asIdeal →
      FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = D v) ∧
    Q.obj.map (Z.map (homOfLE (show
      X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s) ≤ ⊤ from le_top))).op q =
      genericRationalUnitQuotientSection R
        (X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s)) a
  intro p
  exact ⟨s p, a p, hmem p, hdiv p, hq p⟩

/-- Two global quotient-sheaf sections representing the same divisor agree. -/
theorem IsGenericUnitDivisorSection.unique
    (D : HeightOneSpectrum R →₀ ℤ)
    {q q' : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤))}
    (hq : IsGenericUnitDivisorSection R D q)
    (hq' : IsGenericUnitDivisorSection R D q') : q = q' := by
  let X := Spec (CommRingCat.of R)
  let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  let Z := EtaleCohomology.zariskiToEtale X
  let H : TopCat.Sheaf AddCommGrpCat.{u} X :=
    ⟨Z.op ⋙ Q.obj, ((EtaleCohomology.etaleZariskiRestriction X AddCommGrpCat.{u}).obj Q).property⟩
  apply TopCat.Presheaf.section_ext H ⊤ q q'
  intro p hp
  obtain ⟨s, a, hs, ha, hqa⟩ := hq p
  obtain ⟨t, b, ht, hb, hqb⟩ := hq' p
  let U := X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s)
  let V := X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t)
  have hpU : p ∈ U := by
    change p ∈ X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s)
    rw [basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen s p).mpr hs
  have hpV : p ∈ V := by
    change p ∈ X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t)
    rw [basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen t p).mpr ht
  have hpW : p ∈ U ⊓ V := ⟨hpU, hpV⟩
  have heq : genericRationalUnitQuotientSection R (U ⊓ V) a =
      genericRationalUnitQuotientSection R (U ⊓ V) b := by
    apply sub_eq_zero.mp
    rw [← genericRationalUnitQuotientSection_sub]
    apply genericRationalUnitQuotientSection_eq_zero
    intro Ω _ _ φ ξ hW v hv
    have hs' : s ∉ v.asIdeal := by
      have hm := hW.1
      change (Spec.map (CommRingCat.ofHom φ)) ξ ∈ U at hm
      change (Spec.map (CommRingCat.ofHom φ)) ξ ∈
        X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s) at hm
      rw [basicOpen_eq_of_affine] at hm
      have hm' := (PrimeSpectrum.mem_basicOpen s _).mp hm
      rwa [specMap_point_asIdeal_eq_ker R φ ξ, ← hv] at hm'
    have ht' : t ∉ v.asIdeal := by
      have hm := hW.2
      change (Spec.map (CommRingCat.ofHom φ)) ξ ∈
        X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t) at hm
      rw [basicOpen_eq_of_affine] at hm
      have hm' := (PrimeSpectrum.mem_basicOpen t _).mp hm
      rwa [specMap_point_asIdeal_eq_ker R φ ξ, ← hv] at hm'
    rw [map_sub, Finsupp.sub_apply, ha v hs', hb v ht', sub_self]
  have liftGerm (B : X.Opens) (hB : p ∈ B) (hWB : U ⊓ V ≤ B)
      (r : H.obj.obj (op ⊤)) (c : Additive (FractionRing R)ˣ)
      (hr : H.obj.map (homOfLE (show B ≤ ⊤ from le_top)).op r =
        genericRationalUnitQuotientSection R B c) :
      H.presheaf.germ ⊤ p hp r =
        H.presheaf.germ (U ⊓ V) p hpW
          (genericRationalUnitQuotientSection R (U ⊓ V) c) := by
    calc
      H.presheaf.germ ⊤ p hp r =
          H.presheaf.germ B p hB (genericRationalUnitQuotientSection R B c) :=
        (H.presheaf.germ_res_apply (homOfLE (show B ≤ ⊤ from le_top)) p hB r).symm.trans
          (congrArg (H.presheaf.germ B p hB) hr)
      _ = H.presheaf.germ (U ⊓ V) p hpW
          (H.obj.map (homOfLE hWB).op (genericRationalUnitQuotientSection R B c)) :=
        (H.presheaf.germ_res_apply (homOfLE hWB) p hpW
          (genericRationalUnitQuotientSection R B c)).symm
      _ = _ := congrArg (H.presheaf.germ (U ⊓ V) p hpW)
        (genericRationalUnitQuotientSection_restrict R hWB c)
  exact (liftGerm U hpU inf_le_left q a hqa).trans
    ((congrArg (H.presheaf.germ (U ⊓ V) p hpW) heq).trans
      (liftGerm V hpV inf_le_right q' b hqb).symm)

/-- Addition of actual divisor sections represents addition of divisors. -/
theorem IsGenericUnitDivisorSection.add
    {D E : HeightOneSpectrum R →₀ ℤ}
    {q r : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤))}
    (hq : IsGenericUnitDivisorSection R D q)
    (hr : IsGenericUnitDivisorSection R E r) :
    IsGenericUnitDivisorSection R (D + E) (q + r) := by
  let X := Spec (CommRingCat.of R)
  let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  let Z := EtaleCohomology.zariskiToEtale X
  let P := Z.op ⋙ Q.obj
  intro p
  obtain ⟨s, a, hs, ha, hqa⟩ := hq p
  obtain ⟨t, b, ht, hb, hrb⟩ := hr p
  let U := X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s)
  let V := X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t)
  let W := X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (s * t))
  have hWU : W ≤ U := by
    change X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (s * t)) ≤ U
    rw [map_mul, Scheme.basicOpen_mul]
    exact inf_le_left
  have hWV : W ≤ V := by
    change X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (s * t)) ≤ V
    rw [map_mul, Scheme.basicOpen_mul]
    exact inf_le_right
  have hrestrict (B : X.Opens) (hWB : W ≤ B)
      (z : P.obj (op ⊤)) (c : Additive (FractionRing R)ˣ)
      (hz : P.map (homOfLE (show B ≤ ⊤ from le_top)).op z =
        genericRationalUnitQuotientSection R B c) :
      P.map (homOfLE (show W ≤ ⊤ from le_top)).op z =
        genericRationalUnitQuotientSection R W c := by
    calc
      P.map (homOfLE (show W ≤ ⊤ from le_top)).op z =
          P.map (homOfLE hWB).op
            (P.map (homOfLE (show B ≤ ⊤ from le_top)).op z) := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
          homOfLE_comp]
      _ = P.map (homOfLE hWB).op (genericRationalUnitQuotientSection R B c) :=
        congrArg (P.map (homOfLE hWB).op) hz
      _ = _ := genericRationalUnitQuotientSection_restrict R hWB c
  refine ⟨s * t, a + b, ?_, ?_, ?_⟩
  · intro hst
    exact ((p.isPrime.mul_mem_iff_mem_or_mem).mp hst).elim hs ht
  · intro v hv
    have hs' : s ∉ v.asIdeal := by
      intro h
      exact hv (v.asIdeal.mul_mem_right t h)
    have ht' : t ∉ v.asIdeal := by
      intro h
      exact hv (v.asIdeal.mul_mem_left s h)
    rw [map_add, Finsupp.add_apply, ha v hs', hb v ht', Finsupp.add_apply]
  · change P.map (homOfLE (show W ≤ ⊤ from le_top)).op (q + r) =
      genericRationalUnitQuotientSection R W (a + b)
    rw [map_add, hrestrict U hWU q a hqa, hrestrict V hWV r b hrb,
      genericRationalUnitQuotientSection_add]

/-- The uniquely characterized actual global quotient section of a finite divisor. -/
def divisorGenericUnitQuotientSection (D : HeightOneSpectrum R →₀ ℤ) :
    (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤)) :=
  Classical.choose (exists_genericUnitQuotientSection_of_divisor R D)

/-- The canonical divisor section has the constructed local rational representatives. -/
theorem divisorGenericUnitQuotientSection_spec (D : HeightOneSpectrum R →₀ ℤ) :
    IsGenericUnitDivisorSection R D (divisorGenericUnitQuotientSection R D) :=
  Classical.choose_spec (exists_genericUnitQuotientSection_of_divisor R D)

/-- A principal divisor is represented by the original actual rational-unit section. -/
theorem isGenericUnitDivisorSection_principal (a : Additive (FractionRing R)ˣ) :
    IsGenericUnitDivisorSection R
      (FractionalIdeal.principalDivisorAddHom R (FractionRing R) a)
      (genericRationalUnitQuotientSection R ⊤ a) := by
  intro p
  refine ⟨1, a, ?_, ?_, ?_⟩
  · exact (Ideal.ne_top_iff_one _).mp p.isPrime.ne_top
  · intro v _
    rfl
  · exact genericRationalUnitQuotientSection_restrict R le_top a

/-- The canonical construction agrees with the genuine rational-function map
on principal divisors. -/
theorem divisorGenericUnitQuotientSection_principal (a : Additive (FractionRing R)ˣ) :
    divisorGenericUnitQuotientSection R
      (FractionalIdeal.principalDivisorAddHom R (FractionRing R) a) =
      genericRationalUnitQuotientSection R ⊤ a :=
  IsGenericUnitDivisorSection.unique R _
    (divisorGenericUnitQuotientSection_spec R _)
    (isGenericUnitDivisorSection_principal R a)

/-- The geometric germ of an actual rational quotient section retains its
fraction-unit class under the existing stalk comparison. -/
theorem genericRationalUnitQuotientSection_geometric_germ_image
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
    (ξ : Spec (CommRingCat.of Ω))
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (Spec.map (CommRingCat.ofHom φ)) ξ ∈ U)
    (a : Additive (FractionRing R)ˣ) :
    let s := Spec.map (CommRingCat.ofHom φ)
    let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
    let W := (EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj U
    let Φ := Scheme.pointSmallEtale s
    let t := EtaleCohomology.zariskiGeometricLift s ξ U hU
    (geometricGenericUnitQuotientStalkIso R φ).hom
      (Φ.toPresheafFiber W t Q.obj (genericRationalUnitQuotientSection R U a)) =
      cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion
        (geometricStalk s) (FractionRing (geometricStalk s)))
        (Additive.ofMul (Units.map (geometricStalkFractionFieldMap φ).toMonoidHom a.toMul)) := by
  let X := Spec (CommRingCat.of R)
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let g := EtaleCohomology.etaleMultiplicativeGroupToPushforward j
  let Q := cokernel g
  let W := (EtaleCohomology.zariskiToEtale X).obj U
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let t := EtaleCohomology.zariskiGeometricLift
    (Spec.map (CommRingCat.ofHom φ)) ξ U hU
  let P := etaleBaseChangedSections j
  let z : (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P).obj
      (Opposite.op W) := Additive.ofMul (Units.map
    (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
      (pullback.snd W.hom j).appTop).hom.toMonoidHom) a.toMul)
  have hn := ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_naturality (cokernel.π g).hom W t) z
  change (Φ.presheafFiber (A := AddCommGrpCat.{u})).map (cokernel.π g).hom
      (Φ.toPresheafFiber W t
        (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P) z) =
    Φ.toPresheafFiber W t Q.obj ((cokernel.π g).hom.app (op W) z) at hn
  change (geometricGenericUnitQuotientStalkIso R φ).hom
    (Φ.toPresheafFiber W t Q.obj ((cokernel.π g).hom.app (op W) z)) = _
  rw [← hn]
  exact geometricGenericUnitQuotient_rational_germ_image R φ W t a

/-- Every closed geometric quotient germ is represented by a rational section
on any open neighborhood of the point. -/
theorem genericRationalUnitQuotientSection_geometric_germ_surjective
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
    (ξ : Spec (CommRingCat.of Ω))
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (Spec.map (CommRingCat.ofHom φ)) ξ ∈ U)
    (v : HeightOneSpectrum R) (hv : v.asIdeal = RingHom.ker φ) :
    let s := Spec.map (CommRingCat.ofHom φ)
    let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
    let W := (EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj U
    let Φ := Scheme.pointSmallEtale s
    let t := EtaleCohomology.zariskiGeometricLift s ξ U hU
    Function.Surjective (fun a : Additive (FractionRing R)ˣ =>
      Φ.toPresheafFiber W t Q.obj (genericRationalUnitQuotientSection R U a)) := by
  intro s j Q W Φ t q
  let e := (geometricGenericUnitQuotientStalkIso R φ).addCommGroupIsoToAddEquiv
  obtain ⟨a, ha⟩ := geometricFractionUnitCokernel_rational_surjective
    (R := R) (φ := φ) (v := v) (hv := hv) (e q)
  refine ⟨a, e.injective ?_⟩
  exact (genericRationalUnitQuotientSection_geometric_germ_image R φ ξ U hU a).trans ha

/-- Global finite divisors generate every closed geometric quotient stalk. -/
theorem divisorGenericUnitQuotientSection_geometric_germ_surjective
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
    (ξ : Spec (CommRingCat.of Ω))
    (v : HeightOneSpectrum R) (hv : v.asIdeal = RingHom.ker φ) :
    let s := Spec.map (CommRingCat.ofHom φ)
    let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
    let W := (EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤
    let Φ := Scheme.pointSmallEtale s
    let t := EtaleCohomology.zariskiGeometricLift s ξ ⊤ (by trivial)
    Function.Surjective (fun D : HeightOneSpectrum R →₀ ℤ =>
      Φ.toPresheafFiber W t Q.obj (divisorGenericUnitQuotientSection R D)) := by
  intro s j Q W Φ t q
  obtain ⟨a, ha⟩ :=
    genericRationalUnitQuotientSection_geometric_germ_surjective R φ ξ ⊤
      (by trivial) v hv q
  refine ⟨FractionalIdeal.principalDivisorAddHom R (FractionRing R) a, ?_⟩
  change Φ.toPresheafFiber W t Q.obj
    (divisorGenericUnitQuotientSection R
      (FractionalIdeal.principalDivisorAddHom R (FractionRing R) a)) = q
  rw [divisorGenericUnitQuotientSection_principal]
  exact ha

/-- Every actual quotient section is Zariski locally represented by a rational unit.
The proof includes the generic point and arbitrary closed residue fields. -/
theorem genericUnitQuotientSection_exists_local_rational
    (U : (Spec (CommRingCat.of R)).Opens)
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj U)))
    (p : PrimeSpectrum R) (hp : p ∈ U) :
    ∃ (V : (Spec (CommRingCat.of R)).Opens) (hVU : V ≤ U),
      p ∈ V ∧ ∃ a : Additive (FractionRing R)ˣ,
        (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.map
          ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).map
            (homOfLE hVU)).op q = genericRationalUnitQuotientSection R V a := by
  let X := Spec (CommRingCat.of R)
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
  let Z := EtaleCohomology.zariskiToEtale X
  let Ω := SeparableClosure (p.asIdeal.ResidueField)
  let φ : R →+* Ω :=
    (algebraMap (p.asIdeal.ResidueField) Ω).comp
      (algebraMap R (p.asIdeal.ResidueField))
  have hker : RingHom.ker φ = p.asIdeal := by
    rw [RingHom.ker_comp_of_injective
        (algebraMap R (p.asIdeal.ResidueField))
        (algebraMap (p.asIdeal.ResidueField) Ω).injective,
      Ideal.ker_algebraMap_residueField]
  let s := Spec.map (CommRingCat.ofHom φ)
  let ξ : Spec (CommRingCat.of Ω) := default
  have hpoint : s ξ = p := by
    apply PrimeSpectrum.ext
    exact (specMap_point_asIdeal_eq_ker R φ ξ).trans hker
  have hU : s ξ ∈ U := hpoint.symm ▸ hp
  let Φ := Scheme.pointSmallEtale s
  let t := EtaleCohomology.zariskiGeometricLift s ξ U hU
  obtain ⟨a, ha⟩ : ∃ a : Additive (FractionRing R)ˣ,
      Φ.toPresheafFiber (Z.obj U) t Q.obj q =
      Φ.toPresheafFiber (Z.obj U) t Q.obj
        (genericRationalUnitQuotientSection R U a) := by
    by_cases hk : RingHom.ker φ = ⊥
    · have hz := geometricGenericUnitQuotientStalk_isZero_of_injective R φ
        ((RingHom.injective_iff_ker_eq_bot φ).mpr hk)
      have hs := AddCommGrpCat.subsingleton_of_isZero hz
      let e := (Φ.sheafToPresheafCompPresheafFiberIso
        (A := AddCommGrpCat.{u})).app Q
      have hpref : Subsingleton ((Φ.presheafFiber (A := AddCommGrpCat.{u})).obj Q.obj) :=
        ⟨fun x y => (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance
          (hs.elim (e.hom x) (e.hom y))⟩
      exact ⟨0, hpref.elim _ _⟩
    · let v : HeightOneSpectrum R :=
        ⟨RingHom.ker φ, RingHom.ker_isPrime φ, hk⟩
      obtain ⟨a, ha⟩ :=
        genericRationalUnitQuotientSection_geometric_germ_surjective
          R φ ξ U hU v rfl (Φ.toPresheafFiber (Z.obj U) t Q.obj q)
      exact ⟨a, ha.symm⟩
  obtain ⟨V, hVU, hV, hq⟩ :=
    EtaleCohomology.exists_zariski_neighborhood_abelianSections_eq_of_geometric_germs_eq
      s ξ Q U hU q (genericRationalUnitQuotientSection R U a) ha
  refine ⟨V, hVU, ?_, a, ?_⟩
  · exact hpoint ▸ hV
  · exact hq.trans (genericRationalUnitQuotientSection_restrict R hVU a)

/-- At a closed geometric point the germ of a divisor section vanishes exactly
when its coefficient at the underlying point vanishes. -/
theorem divisorGenericUnitQuotientSection_geometric_germ_eq_zero_iff
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
    (ξ : Spec (CommRingCat.of Ω))
    (v : HeightOneSpectrum R) (hv : v.asIdeal = RingHom.ker φ)
    (D : HeightOneSpectrum R →₀ ℤ) :
    let s := Spec.map (CommRingCat.ofHom φ)
    let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
    let W := (EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤
    let Φ := Scheme.pointSmallEtale s
    let t := EtaleCohomology.zariskiGeometricLift s ξ ⊤ (by trivial)
    Φ.toPresheafFiber W t Q.obj (divisorGenericUnitQuotientSection R D) = 0 ↔ D v = 0 := by
  let X := Spec (CommRingCat.of R)
  let s := Spec.map (CommRingCat.ofHom φ)
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
  let Z := EtaleCohomology.zariskiToEtale X
  let Φ := Scheme.pointSmallEtale s
  let p : PrimeSpectrum R := s ξ
  obtain ⟨f, a, hf, ha, hqa⟩ := divisorGenericUnitQuotientSection_spec R D p
  let U := X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)
  have hU : s ξ ∈ U := by
    change s ξ ∈ X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)
    rw [basicOpen_eq_of_affine]
    exact hf
  have hfv : f ∉ v.asIdeal := by
    have hp : p.asIdeal = v.asIdeal :=
      (specMap_point_asIdeal_eq_ker R φ ξ).trans hv.symm
    rw [← hp]
    exact hf
  let tU := EtaleCohomology.zariskiGeometricLift s ξ U hU
  let tTop := EtaleCohomology.zariskiGeometricLift s ξ ⊤ (by trivial)
  have hrep :
      Φ.toPresheafFiber (Z.obj ⊤) tTop Q.obj
        (divisorGenericUnitQuotientSection R D) =
      Φ.toPresheafFiber (Z.obj U) tU Q.obj
        (genericRationalUnitQuotientSection R U a) := by
    have hr := EtaleCohomology.zariskiGeometricAbelianGerm_restrict
      s ξ Q (show U ≤ ⊤ from le_top) hU (by trivial)
      (divisorGenericUnitQuotientSection R D)
    exact hr.symm.trans (congrArg (Φ.toPresheafFiber (Z.obj U) tU Q.obj) hqa)
  change Φ.toPresheafFiber (Z.obj ⊤) tTop Q.obj
    (divisorGenericUnitQuotientSection R D) = 0 ↔ D v = 0
  rw [hrep]
  have him := genericRationalUnitQuotientSection_geometric_germ_image R φ ξ U hU a
  constructor
  · intro hz
    have hc : cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion
        (geometricStalk s) (FractionRing (geometricStalk s)))
        (Additive.ofMul
          (Units.map (geometricStalkFractionFieldMap φ).toMonoidHom a.toMul)) = 0 := by
      calc
        _ = (geometricGenericUnitQuotientStalkIso R φ).hom
            (Φ.toPresheafFiber (Z.obj U) tU Q.obj
              (genericRationalUnitQuotientSection R U a)) := him.symm
        _ = (geometricGenericUnitQuotientStalkIso R φ).hom 0 := congrArg
          (geometricGenericUnitQuotientStalkIso R φ).hom hz
        _ = 0 := map_zero _
    have ho := principalDivisor_eq_zero_of_geometricFractionUnitCokernel_eq_zero
      (R := R) (φ := φ) (v := v) (hv := hv) a hc
    exact (ha v hfv).symm.trans ho
  · intro hz
    have hc := geometricFractionUnitCokernel_eq_zero_of_principalDivisor_eq_zero
      (R := R) (φ := φ) (v := v) (hv := hv) a ((ha v hfv).trans hz)
    have hzero : (geometricGenericUnitQuotientStalkIso R φ).hom
        (Φ.toPresheafFiber (Z.obj U) tU Q.obj
          (genericRationalUnitQuotientSection R U a)) =
        (geometricGenericUnitQuotientStalkIso R φ).hom 0 :=
      (him.trans hc).trans (map_zero _).symm
    exact (AddCommGrpCat.mono_iff_injective
      (geometricGenericUnitQuotientStalkIso R φ).hom).mp inferInstance hzero

/-- The canonical divisor section construction is additive. -/
theorem divisorGenericUnitQuotientSection_add
    (D E : HeightOneSpectrum R →₀ ℤ) :
    divisorGenericUnitQuotientSection R (D + E) =
      divisorGenericUnitQuotientSection R D + divisorGenericUnitQuotientSection R E :=
  IsGenericUnitDivisorSection.unique R (D + E)
    (divisorGenericUnitQuotientSection_spec R (D + E))
    (IsGenericUnitDivisorSection.add R (D := D) (E := E)
      (divisorGenericUnitQuotientSection_spec R D)
      (divisorGenericUnitQuotientSection_spec R E))

/-- The canonical divisor section sends the zero divisor to zero. -/
theorem divisorGenericUnitQuotientSection_zero :
    divisorGenericUnitQuotientSection R 0 = 0 := by
  have h := divisorGenericUnitQuotientSection_add R 0 0
  rw [zero_add] at h
  exact (add_left_cancel (show
    divisorGenericUnitQuotientSection R 0 + divisorGenericUnitQuotientSection R 0 =
      divisorGenericUnitQuotientSection R 0 + 0 by
        rw [add_zero]
        exact h.symm))

/-- Finite divisors map additively to sections of the actual generic-unit quotient. -/
def divisorGenericUnitQuotientSectionAddHom :
    (HeightOneSpectrum R →₀ ℤ) →+
      (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
          (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤)) where
  toFun := divisorGenericUnitQuotientSection R
  map_zero' := divisorGenericUnitQuotientSection_zero R
  map_add' := divisorGenericUnitQuotientSection_add R

/-- The actual quotient section detects the zero divisor. -/
theorem divisorGenericUnitQuotientSection_eq_zero_iff
    (D : HeightOneSpectrum R →₀ ℤ) :
    divisorGenericUnitQuotientSection R D = 0 ↔ D = 0 := by
  constructor
  · intro hD
    ext v
    let p : PrimeSpectrum R := ⟨v.asIdeal, inferInstance⟩
    obtain ⟨s, a, hs, ha, hqa⟩ :=
      divisorGenericUnitQuotientSection_spec R D p
    let Ω := SeparableClosure (v.asIdeal.ResidueField)
    let φ : R →+* Ω :=
      (algebraMap (v.asIdeal.ResidueField) Ω).comp
        (algebraMap R (v.asIdeal.ResidueField))
    have hker : RingHom.ker φ = v.asIdeal := by
      rw [RingHom.ker_comp_of_injective
          (algebraMap R (v.asIdeal.ResidueField))
          (algebraMap (v.asIdeal.ResidueField) Ω).injective,
        Ideal.ker_algebraMap_residueField]
    let ξ : Spec (CommRingCat.of Ω) := default
    let U := (Spec (CommRingCat.of R)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s)
    have hU : (Spec.map (CommRingCat.ofHom φ)) ξ ∈ U := by
      change (Spec.map (CommRingCat.ofHom φ)) ξ ∈
        (Spec (CommRingCat.of R)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s)
      rw [basicOpen_eq_of_affine]
      change s ∉ ((Spec.map (CommRingCat.ofHom φ)) ξ).asIdeal
      rw [specMap_point_asIdeal_eq_ker R φ ξ, hker]
      exact hs
    have hz : genericRationalUnitQuotientSection R U a = 0 := by
      rw [← hqa, hD, map_zero]
    have hv := principalDivisor_eq_zero_of_genericRationalUnitQuotientSection_eq_zero
      R φ ξ U hU v hker.symm a hz
    exact (ha v hs).symm.trans hv
  · intro hD
    rw [hD, divisorGenericUnitQuotientSection_zero]

/-- Finite divisors embed in sections of the actual generic-unit quotient. -/
theorem divisorGenericUnitQuotientSection_injective :
    Function.Injective (divisorGenericUnitQuotientSection R) := by
  intro D E h
  apply sub_eq_zero.mp
  apply (divisorGenericUnitQuotientSection_eq_zero_iff R (D - E)).mp
  change divisorGenericUnitQuotientSectionAddHom R (D - E) = 0
  rw [map_sub]
  change divisorGenericUnitQuotientSection R D -
    divisorGenericUnitQuotientSection R E = 0
  rw [h, sub_self]

section CanonicalDivisorStalk

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
  (ξ : Spec (CommRingCat.of Ω))

/-- The actual geometric germ map on finite divisor sections. -/
def divisorGenericUnitQuotientGeometricGerm :
    (HeightOneSpectrum R →₀ ℤ) →+
      ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
        (A := AddCommGrpCat.{u})).obj
        (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))) := by
  let s := Spec.map (CommRingCat.ofHom φ)
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
  let W := (EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤
  let t := EtaleCohomology.zariskiGeometricLift s ξ ⊤ (by trivial)
  exact (ConcreteCategory.hom ((Scheme.pointSmallEtale s).toPresheafFiber W t Q.obj)).comp
    (divisorGenericUnitQuotientSectionAddHom R)

/-- At a fixed closed point, the actual divisor germ depends only on its coefficient. -/
theorem divisorGenericUnitQuotientGeometricGerm_eq_single
    (v : HeightOneSpectrum R) (hv : v.asIdeal = RingHom.ker φ)
    (D : HeightOneSpectrum R →₀ ℤ) :
    divisorGenericUnitQuotientGeometricGerm R φ ξ D =
      divisorGenericUnitQuotientGeometricGerm R φ ξ (Finsupp.single v (D v)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (divisorGenericUnitQuotientSection_geometric_germ_eq_zero_iff
    R φ ξ v hv (D - Finsupp.single v (D v))).mpr
  simp only [Finsupp.sub_apply, Finsupp.single_eq_same, sub_self]

/-- A canonical integer generator for the actual quotient stalk, normalized by
the coefficient of the base divisor rather than a chosen stalk uniformizer. -/
def divisorGenericUnitQuotientGeometricStalkEquiv
    (v : HeightOneSpectrum R) (hv : v.asIdeal = RingHom.ker φ) :
    ℤ ≃+ ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
      (A := AddCommGrpCat.{u})).obj
      (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))) := by
  classical
  let S : ℤ →+ (HeightOneSpectrum R →₀ ℤ) :=
    { toFun := fun n => Finsupp.single v n
      map_zero' := Finsupp.single_zero v
      map_add' := fun m n => Finsupp.single_add v m n }
  let F := divisorGenericUnitQuotientGeometricGerm R φ ξ
  refine AddEquiv.ofBijective (F.comp S) ⟨?_, ?_⟩
  · intro m n h
    apply sub_eq_zero.mp
    have hz : F (S (m - n)) = 0 := by
      change (F.comp S) (m - n) = 0
      rw [map_sub, h, sub_self]
    have hc := (divisorGenericUnitQuotientSection_geometric_germ_eq_zero_iff
      R φ ξ v hv (Finsupp.single v (m - n))).mp hz
    simpa only [Finsupp.single_eq_same] using hc
  · intro q
    obtain ⟨D, hD⟩ := divisorGenericUnitQuotientSection_geometric_germ_surjective
      R φ ξ v hv q
    refine ⟨D v, ?_⟩
    exact (divisorGenericUnitQuotientGeometricGerm_eq_single R φ ξ v hv D).symm.trans hD

/-- The normalized actual stalk comparison recovers the coefficient of every divisor. -/
theorem divisorGenericUnitQuotientGeometricStalkEquiv_symm_germ
    (v : HeightOneSpectrum R) (hv : v.asIdeal = RingHom.ker φ)
    (D : HeightOneSpectrum R →₀ ℤ) :
    (divisorGenericUnitQuotientGeometricStalkEquiv R φ ξ v hv).symm
      (divisorGenericUnitQuotientGeometricGerm R φ ξ D) = D v := by
  apply (divisorGenericUnitQuotientGeometricStalkEquiv R φ ξ v hv).injective
  rw [AddEquiv.apply_symm_apply]
  exact divisorGenericUnitQuotientGeometricGerm_eq_single R φ ξ v hv D

end CanonicalDivisorStalk

/-- The coefficient of an actual global quotient section at a height-one point,
defined using the normalized actual geometric stalk. -/
def genericUnitQuotientSectionCoefficient (v : HeightOneSpectrum R) :
    (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤)) →+ ℤ := by
  let Ω := SeparableClosure (v.asIdeal.ResidueField)
  let φ : R →+* Ω :=
    (algebraMap (v.asIdeal.ResidueField) Ω).comp
      (algebraMap R (v.asIdeal.ResidueField))
  have hker : RingHom.ker φ = v.asIdeal := by
    rw [RingHom.ker_comp_of_injective
        (algebraMap R (v.asIdeal.ResidueField))
        (algebraMap (v.asIdeal.ResidueField) Ω).injective,
      Ideal.ker_algebraMap_residueField]
  let ξ : Spec (CommRingCat.of Ω) := default
  let s := Spec.map (CommRingCat.ofHom φ)
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
  let W := (EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤
  let t := EtaleCohomology.zariskiGeometricLift s ξ ⊤ (by trivial)
  let e := divisorGenericUnitQuotientGeometricStalkEquiv R φ ξ v hker.symm
  exact e.symm.toAddMonoidHom.comp
    (ConcreteCategory.hom ((Scheme.pointSmallEtale s).toPresheafFiber W t Q.obj))

/-- The coefficient map recovers the original finite divisor. -/
theorem genericUnitQuotientSectionCoefficient_divisor
    (v : HeightOneSpectrum R) (D : HeightOneSpectrum R →₀ ℤ) :
    genericUnitQuotientSectionCoefficient R v
      (divisorGenericUnitQuotientSection R D) = D v := by
  let Ω := SeparableClosure (v.asIdeal.ResidueField)
  let φ : R →+* Ω :=
    (algebraMap (v.asIdeal.ResidueField) Ω).comp
      (algebraMap R (v.asIdeal.ResidueField))
  have hker : RingHom.ker φ = v.asIdeal := by
    rw [RingHom.ker_comp_of_injective
        (algebraMap R (v.asIdeal.ResidueField))
        (algebraMap (v.asIdeal.ResidueField) Ω).injective,
      Ideal.ker_algebraMap_residueField]
  let ξ : Spec (CommRingCat.of Ω) := default
  change (divisorGenericUnitQuotientGeometricStalkEquiv R φ ξ v hker.symm).symm
    (divisorGenericUnitQuotientGeometricGerm R φ ξ D) = D v
  exact divisorGenericUnitQuotientGeometricStalkEquiv_symm_germ R φ ξ v hker.symm D

/-- A local rational representative computes the actual global geometric germ. -/
theorem genericUnitQuotientSection_germ_of_local_rational
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
    (ξ : Spec (CommRingCat.of Ω))
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (Spec.map (CommRingCat.ofHom φ)) ξ ∈ U)
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤)))
    (a : Additive (FractionRing R)ˣ)
    (hq : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.map
        ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).map
          (homOfLE (show U ≤ ⊤ from le_top))).op q =
        genericRationalUnitQuotientSection R U a) :
    let s := Spec.map (CommRingCat.ofHom φ)
    let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
    let Z := EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))
    let t := EtaleCohomology.zariskiGeometricLift s ξ ⊤ (by trivial)
    (Scheme.pointSmallEtale s).toPresheafFiber (Z.obj ⊤) t Q.obj q =
      divisorGenericUnitQuotientGeometricGerm R φ ξ
        (FractionalIdeal.principalDivisorAddHom R (FractionRing R) a) := by
  intro s j Q Z
  let Φ := Scheme.pointSmallEtale s
  let tU := EtaleCohomology.zariskiGeometricLift s ξ U hU
  let tTop := EtaleCohomology.zariskiGeometricLift s ξ ⊤ (by trivial)
  have hr := EtaleCohomology.zariskiGeometricAbelianGerm_restrict
    s ξ Q (show U ≤ ⊤ from le_top) hU (by trivial) q
  have ha := EtaleCohomology.zariskiGeometricAbelianGerm_restrict
    s ξ Q (show U ≤ ⊤ from le_top) hU (by trivial)
    (genericRationalUnitQuotientSection R ⊤ a)
  rw [genericRationalUnitQuotientSection_restrict] at ha
  change Φ.toPresheafFiber (Z.obj ⊤) tTop Q.obj q =
    Φ.toPresheafFiber (Z.obj ⊤) tTop Q.obj
      (divisorGenericUnitQuotientSection R
        (FractionalIdeal.principalDivisorAddHom R (FractionRing R) a))
  rw [divisorGenericUnitQuotientSection_principal]
  exact hr.symm.trans
    ((congrArg (Φ.toPresheafFiber (Z.obj U) tU Q.obj) hq).trans ha)

/-- On any open where an actual section is represented by a rational unit,
its coefficient is the principal-divisor order of that unit. -/
theorem genericUnitQuotientSectionCoefficient_of_local_rational
    (v : HeightOneSpectrum R)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hvU : (⟨v.asIdeal, inferInstance⟩ : PrimeSpectrum R) ∈ U)
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤)))
    (a : Additive (FractionRing R)ˣ)
    (hq : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.map
        ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).map
          (homOfLE (show U ≤ ⊤ from le_top))).op q =
        genericRationalUnitQuotientSection R U a) :
    genericUnitQuotientSectionCoefficient R v q =
      FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v := by
  let Ω := SeparableClosure (v.asIdeal.ResidueField)
  let φ : R →+* Ω :=
    (algebraMap (v.asIdeal.ResidueField) Ω).comp
      (algebraMap R (v.asIdeal.ResidueField))
  have hker : RingHom.ker φ = v.asIdeal := by
    rw [RingHom.ker_comp_of_injective
        (algebraMap R (v.asIdeal.ResidueField))
        (algebraMap (v.asIdeal.ResidueField) Ω).injective,
      Ideal.ker_algebraMap_residueField]
  let ξ : Spec (CommRingCat.of Ω) := default
  let s := Spec.map (CommRingCat.ofHom φ)
  have hpoint : s ξ = (⟨v.asIdeal, inferInstance⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    exact (specMap_point_asIdeal_eq_ker R φ ξ).trans hker
  have hU : s ξ ∈ U := hpoint.symm ▸ hvU
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
  let Z := EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))
  let Φ := Scheme.pointSmallEtale s
  let tU := EtaleCohomology.zariskiGeometricLift s ξ U hU
  let tTop := EtaleCohomology.zariskiGeometricLift s ξ ⊤ (by trivial)
  let D := FractionalIdeal.principalDivisorAddHom R (FractionRing R) a
  have hg :
      Φ.toPresheafFiber (Z.obj ⊤) tTop Q.obj q =
      divisorGenericUnitQuotientGeometricGerm R φ ξ D := by
    exact genericUnitQuotientSection_germ_of_local_rational R φ ξ U hU q a hq
  change (divisorGenericUnitQuotientGeometricStalkEquiv R φ ξ v hker.symm).symm
    (Φ.toPresheafFiber (Z.obj ⊤) tTop Q.obj q) = D v
  rw [hg]
  exact divisorGenericUnitQuotientGeometricStalkEquiv_symm_germ R φ ξ v hker.symm D

/-- An actual global quotient section has only finitely many nonzero divisor coefficients. -/
theorem genericUnitQuotientSectionCoefficient_finite_support
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤))) :
    (Function.support (fun v => genericUnitQuotientSectionCoefficient R v q)).Finite := by
  classical
  choose V hVle hV a ha using
    (fun p : PrimeSpectrum R =>
      genericUnitQuotientSection_exists_local_rational R ⊤ q p (by trivial))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p => (V p : Set (Spec (CommRingCat.of R))))
    (fun p => (V p).is_open')
    (fun p _ => Set.mem_iUnion.mpr ⟨p, hV p⟩)
  let S : Finset (HeightOneSpectrum R) :=
    t.biUnion (fun p =>
      (FractionalIdeal.principalDivisorAddHom R (FractionRing R) (a p)).support)
  apply S.finite_toSet.subset
  intro v hv
  let p : PrimeSpectrum R := ⟨v.asIdeal, inferInstance⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (show p ∈ Set.univ from Set.mem_univ p))
  obtain ⟨hit, hpV⟩ := Set.mem_iUnion.mp hi
  have hc := genericUnitQuotientSectionCoefficient_of_local_rational
    R v (V i) hpV q (a i) (ha i)
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hit, Finsupp.mem_support_iff.mpr ?_⟩
  intro hz
  exact hv (hc.trans hz)

/-- The actual finite divisor extracted from a global generic-unit quotient section. -/
def genericUnitQuotientSectionDivisor
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤))) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => genericUnitQuotientSectionCoefficient R v q)
    (genericUnitQuotientSectionCoefficient_finite_support R q)

/-- Evaluation of the extracted divisor is the actual geometric-stalk coefficient. -/
theorem genericUnitQuotientSectionDivisor_apply
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤)))
    (v : HeightOneSpectrum R) :
    genericUnitQuotientSectionDivisor R q v = genericUnitQuotientSectionCoefficient R v q :=
  rfl

/-- Extraction recovers every original finite divisor. -/
theorem genericUnitQuotientSectionDivisor_divisor
    (D : HeightOneSpectrum R →₀ ℤ) :
    genericUnitQuotientSectionDivisor R
      (divisorGenericUnitQuotientSection R D) = D := by
  ext v
  exact genericUnitQuotientSectionCoefficient_divisor R v D

/-- The coefficient is independent of the chosen separably closed geometric point. -/
theorem genericUnitQuotientSectionCoefficient_eq_geometric_germ
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
    (ξ : Spec (CommRingCat.of Ω))
    (v : HeightOneSpectrum R) (hv : v.asIdeal = RingHom.ker φ)
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤))) :
    let s := Spec.map (CommRingCat.ofHom φ)
    let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
    let Z := EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))
    let t := EtaleCohomology.zariskiGeometricLift s ξ ⊤ (by trivial)
    (divisorGenericUnitQuotientGeometricStalkEquiv R φ ξ v hv).symm
      ((Scheme.pointSmallEtale s).toPresheafFiber (Z.obj ⊤) t Q.obj q) =
        genericUnitQuotientSectionCoefficient R v q := by
  intro s
  obtain ⟨U, hUle, hU, a, hq⟩ :=
    genericUnitQuotientSection_exists_local_rational R ⊤ q (s ξ) (by trivial)
  have hp : s ξ = (⟨v.asIdeal, inferInstance⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    exact (specMap_point_asIdeal_eq_ker R φ ξ).trans hv.symm
  have hvU : (⟨v.asIdeal, inferInstance⟩ : PrimeSpectrum R) ∈ U := hp ▸ hU
  have hg := genericUnitQuotientSection_germ_of_local_rational R φ ξ U hU q a hq
  let E := divisorGenericUnitQuotientGeometricStalkEquiv R φ ξ v hv
  have htransport : E.symm
      ((Scheme.pointSmallEtale s).toPresheafFiber
        ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤)
        (EtaleCohomology.zariskiGeometricLift s ξ ⊤ (by trivial))
        (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj q) =
      E.symm (divisorGenericUnitQuotientGeometricGerm R φ ξ
        (FractionalIdeal.principalDivisorAddHom R (FractionRing R) a)) := by
    exact congrArg E.symm hg
  have hdiv := divisorGenericUnitQuotientGeometricStalkEquiv_symm_germ
    R φ ξ v hv (FractionalIdeal.principalDivisorAddHom R (FractionRing R) a)
  have hcoeff := genericUnitQuotientSectionCoefficient_of_local_rational
    R v U hvU q a hq
  change E.symm
      ((Scheme.pointSmallEtale s).toPresheafFiber
        ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤)
        (EtaleCohomology.zariskiGeometricLift s ξ ⊤ (by trivial))
        (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj q) =
    genericUnitQuotientSectionCoefficient R v q
  exact htransport.trans (hdiv.trans hcoeff.symm)

/-- The actual global quotient section is determined by all of its divisor coefficients. -/
theorem genericUnitQuotientSectionCoefficient_jointly_injective
    (q r : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤)))
    (h : ∀ v, genericUnitQuotientSectionCoefficient R v q =
      genericUnitQuotientSectionCoefficient R v r) : q = r := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)
  apply EtaleCohomology.etaleZariskiAbelianSection_eq_of_geometric_germs_eq Q ⊤ q r
  intro Ω _ _ s ξ htop
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  by_cases hk : RingHom.ker φ.hom = ⊥
  · have hz := geometricGenericUnitQuotientStalk_isZero_of_injective R φ.hom
      ((RingHom.injective_iff_ker_eq_bot φ.hom).mpr hk)
    exact (AddCommGrpCat.subsingleton_of_isZero hz).elim _ _
  · let v : HeightOneSpectrum R :=
      ⟨RingHom.ker φ.hom, RingHom.ker_isPrime φ.hom, hk⟩
    let E := divisorGenericUnitQuotientGeometricStalkEquiv R φ.hom ξ v rfl
    have hqg := genericUnitQuotientSectionCoefficient_eq_geometric_germ
      R φ.hom ξ v rfl q
    have hrg := genericUnitQuotientSectionCoefficient_eq_geometric_germ
      R φ.hom ξ v rfl r
    apply E.symm.injective
    calc
      E.symm ((Scheme.pointSmallEtale (Spec.map φ)).toPresheafFiber
          ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤)
          (EtaleCohomology.zariskiGeometricLift (Spec.map φ) ξ ⊤ htop) Q.obj q) =
        genericUnitQuotientSectionCoefficient R v q := hqg
      _ = genericUnitQuotientSectionCoefficient R v r := h v
      _ = E.symm ((Scheme.pointSmallEtale (Spec.map φ)).toPresheafFiber
          ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤)
          (EtaleCohomology.zariskiGeometricLift (Spec.map φ) ξ ⊤ htop) Q.obj r) := hrg.symm

/-- Extracting and reconstructing an actual global quotient section returns that section. -/
theorem divisorGenericUnitQuotientSection_sectionDivisor
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤))) :
    divisorGenericUnitQuotientSection R (genericUnitQuotientSectionDivisor R q) = q := by
  apply genericUnitQuotientSectionCoefficient_jointly_injective R
  intro v
  rw [genericUnitQuotientSectionCoefficient_divisor, genericUnitQuotientSectionDivisor_apply]

/-- Finite divisors identify with actual global generic-unit quotient sections
on the spectrum of a Dedekind domain. -/
def divisorGenericUnitQuotientGlobalSectionEquiv :
    (HeightOneSpectrum R →₀ ℤ) ≃+ (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤)) :=
  AddEquiv.ofBijective (divisorGenericUnitQuotientSectionAddHom R)
    ⟨divisorGenericUnitQuotientSection_injective R,
      fun q => ⟨genericUnitQuotientSectionDivisor R q,
        divisorGenericUnitQuotientSection_sectionDivisor R q⟩⟩

section AffineEtaleDivisorSections

variable (S : Type u) [CommRing S] [IsDomain S] [algRS : Algebra R S]
  [Algebra.Etale R S]

/-- Restricting the actual rational-unit quotient representative along any
etale morphism over the affine base, then applying the fraction-field
comparison, gives the representative of the mapped fraction-field unit. -/
theorem genericRationalUnitQuotientRepresentative_naturality
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      algRS.toSMul (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (V : (Spec (CommRingCat.of S)).Etale)
    (W : (Spec (CommRingCat.of R)).Etale)
    (m : (EtaleCohomology.etalePostcompose
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj V ⟶ W)
    (a : Additive (FractionRing R)ˣ) :
    let Q_R := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
    let e := EtaleCohomology.affineEtaleFractionRingUnitQuotientIso R S
    let eP := (sheafToPresheaf (Spec (CommRingCat.of S)).smallEtaleTopology
      AddCommGrpCat.{u}).mapIso e
    ConcreteCategory.hom (eP.hom.app (op V))
      (ConcreteCategory.hom (Q_R.obj.map m.op)
        (genericRationalUnitQuotientRepresentative R W a)) =
      genericRationalUnitQuotientRepresentative S V
        ((Units.map (algebraMap (FractionRing R) (FractionRing S)).toMonoidHom).toAdditive a) := by
  let X := Spec (CommRingCat.of R)
  let Y := Spec (CommRingCat.of S)
  let K := FractionRing R
  let E := FractionRing S
  let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let f := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let p := Spec.map (CommRingCat.ofHom (algebraMap S E))
  let g := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let V' := (EtaleCohomology.etalePostcompose i).obj V
  let Q_R := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward f)
  let Q_S := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward p)
  let e := EtaleCohomology.etaleRestrictionFractionFieldUnitQuotientIso R S K E
  let eP := (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).mapIso e
  let pushIso := EtaleCohomology.etaleRestrictionFractionFieldUnitPushforwardIso R S K E
  let pushIsoP := (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).mapIso pushIso
  let πR := cokernel.π (EtaleCohomology.etaleMultiplicativeGroupToPushforward f)
  let πS := cokernel.π (EtaleCohomology.etaleMultiplicativeGroupToPushforward p)
  let zW := Additive.ofMul (Units.map
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (pullback.snd W.hom f).appTop).hom.toMonoidHom) a.toMul)
  let zV' := Additive.ofMul (Units.map
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (pullback.snd V'.hom f).appTop).hom.toMonoidHom) a.toMul)
  let zV := Additive.ofMul (Units.map
    (((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
      (pullback.snd V.hom p).appTop).hom.toMonoidHom)
    ((Units.map (algebraMap K E).toMonoidHom).toAdditive a).toMul)
  let sRestricted : ((sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat).obj
      ((EtaleCohomology.etaleRestriction i AddCommGrpCat).obj Q_R)).obj (op V) :=
    (Q_R.obj.map m.op) (genericRationalUnitQuotientRepresentative R W a)
  have hunit := EtaleCohomology.rationalUnitDirectImage_naturality
    (R := R) (K := K) W V' m a
  change ((EtaleCohomology.etaleAbelianPushforward f).obj
    (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of K)))).obj.map
      m.op zW = zV' at hunit
  have hq := ConcreteCategory.congr_hom (πR.hom.naturality m.op) zW
  change πR.hom.app (op V') (((EtaleCohomology.etaleAbelianPushforward f).obj
      (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of K)))).obj.map
        m.op zW) = (Q_R.obj.map m.op) (πR.hom.app (op W) zW) at hq
  have hres : (Q_R.obj.map m.op) (πR.hom.app (op W) zW) =
      πR.hom.app (op V') zV' := by
    calc
      _ = πR.hom.app (op V') (((EtaleCohomology.etaleAbelianPushforward f).obj
          (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of K)))).obj.map
            m.op zW) := hq.symm
      _ = πR.hom.app (op V') zV' := congrArg (πR.hom.app (op V')) hunit
  have hleft := congrArg (ConcreteCategory.hom (eP.hom.app (op V))) hres
  have hπ := EtaleCohomology.etaleRestrictionFractionFieldUnitQuotientIso_π
    R S K E
  have hπV := congrArg (fun α => α.hom.app (op V)) hπ
  have hπpoint := ConcreteCategory.congr_hom hπV zV'
  change ConcreteCategory.hom (eP.hom.app (op V))
      (πR.hom.app (op V') zV') =
    ConcreteCategory.hom (πS.hom.app (op V))
      (ConcreteCategory.hom (pushIsoP.hom.app (op V)) zV') at hπpoint
  have hpush := EtaleCohomology.etaleRestrictionFractionFieldUnitPushforwardIso_rationalUnit
    R S K E V a
  change ConcreteCategory.hom (eP.hom.app (op V)) sRestricted =
    πS.hom.app (op V) zV
  change ConcreteCategory.hom (pushIsoP.hom.app (op V)) zV' = zV at hpush
  calc
    _ = ConcreteCategory.hom (eP.hom.app (op V))
        (πR.hom.app (op V') zV') := hleft
    _ = ConcreteCategory.hom (πS.hom.app (op V))
        (ConcreteCategory.hom (pushIsoP.hom.app (op V)) zV') := hπpoint
    _ = πS.hom.app (op V) zV := by
      rw [hpush]

/-- The actual top-section map from the generic-unit quotient over `R` to
the quotient over `S`: restrict along the induced top etale object, then apply
the fraction-field quotient comparison. -/
def affineEtaleGenericUnitQuotientTopSectionMap
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      algRS.toSMul (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul] :
    (EtaleCohomology.affineEtaleFractionRingUnitQuotient R).obj.obj
        (op ((EtaleCohomology.zariskiToEtale
          (Spec (CommRingCat.of R))).obj ⊤)) →+
    (EtaleCohomology.affineEtaleFractionRingUnitQuotient S).obj.obj
        (op ((EtaleCohomology.zariskiToEtale
          (Spec (CommRingCat.of S))).obj ⊤)) := by
  let X := Spec (CommRingCat.of R)
  let Y := Spec (CommRingCat.of S)
  let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let Q_R := EtaleCohomology.affineEtaleFractionRingUnitQuotient R
  let Q_S := EtaleCohomology.affineEtaleFractionRingUnitQuotient S
  let e := EtaleCohomology.affineEtaleFractionRingUnitQuotientIso R S
  let eP := (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).mapIso e
  let W_R := (EtaleCohomology.zariskiToEtale X).obj ⊤
  let W_S := (EtaleCohomology.zariskiToEtale Y).obj ⊤
  let VTop := (EtaleCohomology.etalePostcompose i).obj W_S
  let t : VTop ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk VTop.hom (Category.comp_id _)
  let mTop := t ≫ (EtaleCohomology.zariskiToEtaleTopIso X).inv
  exact AddCommGrpCat.Hom.hom (Q_R.obj.map mTop.op ≫ eP.hom.app (op W_S))



/-- The coefficient of an actual quotient section is preserved by the
fraction-field comparison along an affine etale base change. The comparison
on sections is the actual restriction followed by the quotient isomorphism. -/
theorem genericUnitQuotientSectionCoefficient_map
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      algRS.toSMul (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S)
    (hwv : w.asIdeal.under R = v.asIdeal)
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤))) :
    let hS : IsDedekindDomain S :=
      IsDedekindDomain.of_essFiniteType_formallyUnramified R S
    @genericUnitQuotientSectionCoefficient S (inferInstance : CommRing S) hS w
      (affineEtaleGenericUnitQuotientTopSectionMap R S q) =
      genericUnitQuotientSectionCoefficient R v q := by
  let X := Spec (CommRingCat.of R)
  let Y := Spec (CommRingCat.of S)
  let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let ZR := EtaleCohomology.zariskiToEtale X
  let ZS := EtaleCohomology.zariskiToEtale Y
  let KR := FractionRing R
  let KS := FractionRing S
  let Q_R := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
    (Spec.map (CommRingCat.ofHom (algebraMap R KR))))
  let Q_S := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
    (Spec.map (CommRingCat.ofHom (algebraMap S KS))))
  let e := EtaleCohomology.etaleRestrictionFractionFieldUnitQuotientIso R S KR KS
  let eP := (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).mapIso e
  let W_R := ZR.obj ⊤
  let W_S := ZS.obj ⊤
  let topIsoR := EtaleCohomology.zariskiToEtaleTopIso X
  let VTop := (EtaleCohomology.etalePostcompose i).obj W_S
  let tTop : VTop ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk VTop.hom (Category.comp_id _)
  let mTop : VTop ⟶ W_R := tTop ≫ topIsoR.inv
  let qS : Q_S.obj.obj (op W_S) :=
    affineEtaleGenericUnitQuotientTopSectionMap R S q
  let hS : IsDedekindDomain S :=
    IsDedekindDomain.of_essFiniteType_formallyUnramified R S
  let p : PrimeSpectrum R := ⟨v.asIdeal, inferInstance⟩
  obtain ⟨U, hUtop, hvU, a, ha⟩ :=
    genericUnitQuotientSection_exists_local_rational R ⊤ q p (by trivial)
  let U' := i ⁻¹ᵁ U
  have hwU : (⟨w.asIdeal, inferInstance⟩ : PrimeSpectrum S) ∈ U' := by
    change (i.base ⟨w.asIdeal, inferInstance⟩) ∈ U
    have hpoint : i.base (⟨w.asIdeal, inferInstance⟩ : PrimeSpectrum S) = p := by
      change PrimeSpectrum.comap (algebraMap R S) ⟨w.asIdeal, inferInstance⟩ = p
      apply PrimeSpectrum.ext
      rw [PrimeSpectrum.comap_asIdeal]
      exact hwv
    rw [hpoint]
    exact hvU
  let WU := ZR.obj U
  let VS := ZS.obj U'
  let V := (EtaleCohomology.etalePostcompose i).obj VS
  let m : V ⟶ WU := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme from @Etale) (Q := ⊤)
    (A := V) (B := WU) (i ∣_ U) (isPullback_morphismRestrict i U).w trivial
  let jU : WU ⟶ W_R := ZR.map (homOfLE hUtop)
  let nS : VS ⟶ W_S := ZS.map (homOfLE (show U' ≤ ⊤ from le_top))
  let VTop := (EtaleCohomology.etalePostcompose i).obj W_S
  let n : V ⟶ VTop := (EtaleCohomology.etalePostcompose i).map nS
  have hcomp : n ≫ mTop = m ≫ jU := by
    apply (cancel_mono topIsoR.hom).1
    apply MorphismProperty.Over.Hom.ext
    have hleft : (n ≫ mTop ≫ topIsoR.hom).left = V.hom := by
      have hw := (n ≫ mTop ≫ topIsoR.hom).w
      change (n ≫ mTop ≫ topIsoR.hom).left ≫ 𝟙 X = V.hom at hw
      exact (Category.comp_id _).symm.trans hw
    have hright : (m ≫ jU ≫ topIsoR.hom).left = V.hom := by
      have hw := (m ≫ jU ≫ topIsoR.hom).w
      change (m ≫ jU ≫ topIsoR.hom).left ≫ 𝟙 X = V.hom at hw
      exact (Category.comp_id _).symm.trans hw
    exact hleft.trans hright.symm
  have hlocalR := ha
  have hlocalMap := congrArg (Q_R.obj.map m.op) hlocalR
  have hnatRep := genericRationalUnitQuotientRepresentative_naturality
    (R := R) (S := S) VS WU m a
  let aS := ((Units.map (algebraMap KR KS).toMonoidHom).toAdditive a)
  have hpaths : Q_R.obj.map mTop.op ≫ Q_R.obj.map n.op =
      Q_R.obj.map jU.op ≫ Q_R.obj.map m.op := by
    have hcompOp : mTop.op ≫ n.op = jU.op ≫ m.op := by
      rw [← op_comp (f := n) (g := mTop), ← op_comp (f := m) (g := jU)]
      exact congrArg (fun f => f.op) hcomp
    calc
      Q_R.obj.map mTop.op ≫ Q_R.obj.map n.op =
          Q_R.obj.map (mTop.op ≫ n.op) := (Functor.map_comp _ _ _).symm
      _ = Q_R.obj.map (jU.op ≫ m.op) := by
        exact congrArg (fun f => Q_R.obj.map f) hcompOp
      _ = Q_R.obj.map jU.op ≫ Q_R.obj.map m.op := Functor.map_comp _ _ _
  have hcompEta := ConcreteCategory.congr_hom
    (eP.hom.naturality nS.op) (ConcreteCategory.hom (Q_R.obj.map mTop.op) q)
  change ConcreteCategory.hom (eP.hom.app (op VS))
      (ConcreteCategory.hom (Q_R.obj.map n.op)
        (ConcreteCategory.hom (Q_R.obj.map mTop.op) q)) =
    ConcreteCategory.hom (Q_S.obj.map nS.op)
      (ConcreteCategory.hom (eP.hom.app (op W_S))
        (ConcreteCategory.hom (Q_R.obj.map mTop.op) q)) at hcompEta
  have hsource : Q_R.obj.map n.op (Q_R.obj.map mTop.op q) =
      Q_R.obj.map m.op (genericRationalUnitQuotientSection R U a) := by
    have hpath : Q_R.obj.map n.op (Q_R.obj.map mTop.op q) =
        Q_R.obj.map m.op (Q_R.obj.map jU.op q) := by
      simpa only [AddCommGrpCat.comp_apply] using
        congrArg (fun f => (AddCommGrpCat.Hom.hom f) q) hpaths
    rw [hpath]
    exact hlocalMap
  have hqS_local : Q_S.obj.map nS.op qS =
      genericRationalUnitQuotientSection S U' aS := by
    calc
      Q_S.obj.map nS.op qS =
          ConcreteCategory.hom (eP.hom.app (op VS))
            (Q_R.obj.map n.op (Q_R.obj.map mTop.op q)) := by
        change Q_S.obj.map nS.op
            (ConcreteCategory.hom (eP.hom.app (op W_S))
              (ConcreteCategory.hom (Q_R.obj.map mTop.op) q)) = _
        exact hcompEta.symm
      _ = ConcreteCategory.hom (eP.hom.app (op VS))
          (Q_R.obj.map m.op (genericRationalUnitQuotientSection R U a)) :=
        congrArg (ConcreteCategory.hom (eP.hom.app (op VS))) hsource
      _ = genericRationalUnitQuotientSection S U' aS := by
        change ConcreteCategory.hom (eP.hom.app (op VS))
            (Q_R.obj.map m.op (genericRationalUnitQuotientRepresentative R WU a)) =
          genericRationalUnitQuotientRepresentative S VS aS
        dsimp [aS]
        exact hnatRep
  have hcoeffR := genericUnitQuotientSectionCoefficient_of_local_rational
    (R := R) v U hvU q a ha
  have hcoeffS := @genericUnitQuotientSectionCoefficient_of_local_rational S
    (inferInstance : CommRing S) hS w U' hwU qS aS hqS_local
  have hgAlg : (algebraMap KR KS).comp (algebraMap R KR) =
      (algebraMap S KS).comp (algebraMap R S) := by
    ext r
    change algebraMap KR KS (algebraMap R KR r) =
      algebraMap S KS (algebraMap R S r)
    calc
      algebraMap KR KS (algebraMap R KR r) = algebraMap R KS r :=
        (IsScalarTower.algebraMap_apply R KR KS r).symm
      _ = algebraMap S KS (algebraMap R S r) :=
        IsScalarTower.algebraMap_apply R S KS r
  calc
    @genericUnitQuotientSectionCoefficient S (inferInstance : CommRing S) hS w qS =
        FractionalIdeal.principalDivisorAddHom S KS aS w := hcoeffS
    _ = FractionalIdeal.principalDivisorAddHom R KR a v :=
      @FractionalIdeal.principalDivisorAddHom_map_eq_of_base_unramified R S
        KR KS (inferInstance : CommRing R) (inferInstance : IsDedekindDomain R)
        (inferInstance : CommRing S) hS (inferInstance : Algebra R S)
        (inferInstance : Algebra.EssFiniteType R S)
        (inferInstance : Algebra.FormallyUnramified R S)
        (inferInstance : Field KR) (inferInstance : Algebra R KR)
        (inferInstance : IsFractionRing R KR) (inferInstance : Field KS)
        (inferInstance : Algebra S KS) (inferInstance : IsFractionRing S KS)
        (algebraMap KR KS) hgAlg v w hwv a
    _ = genericUnitQuotientSectionCoefficient R v q := hcoeffR.symm

/-- Finite divisors on an affine étale domain identify with the actual
sections of the restricted generic-unit quotient of the base. -/
def affineEtaleDivisorGenericUnitQuotientSectionEquiv
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      algRS.toSMul (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul] :
    (HeightOneSpectrum S →₀ ℤ) ≃+
      ((EtaleCohomology.etaleRestriction
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) AddCommGrpCat.{u}).obj
        (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) := by
  have : IsDedekindDomain S :=
    IsDedekindDomain.of_essFiniteType_formallyUnramified R S
  let e := @EtaleCohomology.affineEtaleFractionRingUnitQuotientIso R S
    _ _ _ _ algRS _ algRE hRS algKE hKS
  let eP := (sheafToPresheaf (Spec (CommRingCat.of S)).smallEtaleTopology
    AddCommGrpCat.{u}).mapIso e
  let V := op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)
  simpa only [CategoryTheory.sheafToPresheaf, CategoryTheory.ObjectProperty.ι_obj] using
    (divisorGenericUnitQuotientGlobalSectionEquiv S).trans
      (eP.app V).symm.addCommGroupIsoToAddEquiv

/-- The forward divisor-section comparison is the inverse component of the
actual fraction-field quotient comparison applied to the divisor section. -/
theorem affineEtaleDivisorGenericUnitQuotientSectionEquiv_apply
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      algRS.toSMul (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (D : HeightOneSpectrum S →₀ ℤ) :
    let : IsDedekindDomain S :=
      IsDedekindDomain.of_essFiniteType_formallyUnramified R S
    let Q_R : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u} :=
      cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
    let Q_S : Sheaf (Spec (CommRingCat.of S)).smallEtaleTopology AddCommGrpCat.{u} :=
      cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S)))))
    let e : (EtaleCohomology.etaleRestriction
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) AddCommGrpCat.{u}).obj Q_R ≅ Q_S :=
      EtaleCohomology.affineEtaleFractionRingUnitQuotientIso R S
    let eP : ((EtaleCohomology.etaleRestriction
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) AddCommGrpCat.{u}).obj Q_R).obj ≅
        Q_S.obj :=
      (sheafToPresheaf (Spec (CommRingCat.of S)).smallEtaleTopology
        AddCommGrpCat.{u}).mapIso e
    affineEtaleDivisorGenericUnitQuotientSectionEquiv R S
        (algRS := algRS) (algRE := algRE) (hRS := hRS) (algKE := algKE) (hKS := hKS) D =
      ConcreteCategory.hom (eP.inv.app
        (op ((EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)))
        (divisorGenericUnitQuotientSection S D) := by
  intro hS Q_R Q_S e eP
  change ((divisorGenericUnitQuotientGlobalSectionEquiv S).trans
    (eP.app (op ((EtaleCohomology.zariskiToEtale
      (Spec (CommRingCat.of S))).obj ⊤))).symm.addCommGroupIsoToAddEquiv) D = _
  rw [AddEquiv.trans_apply, Iso.addCommGroupIsoToAddEquiv_apply,
    Iso.symm_hom, Iso.app_inv]
  rfl

/-- The actual top-section map commutes with geometric pullback of finite
height-one divisors under an affine etale map. -/
theorem affineEtaleDivisorPullback_commutes_with_topSectionMap
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      algRS.toSMul (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (D : HeightOneSpectrum R →₀ ℤ) :
    let e := EtaleCohomology.affineEtaleFractionRingUnitQuotientIso R S
    let eP := (sheafToPresheaf (Spec (CommRingCat.of S)).smallEtaleTopology
      AddCommGrpCat.{u}).mapIso e
    let W_S := (EtaleCohomology.zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤
    ConcreteCategory.hom (eP.hom.app (op W_S))
      (affineEtaleDivisorGenericUnitQuotientSectionEquiv R S
        (affineEtaleDivisorPullback D)) =
      affineEtaleGenericUnitQuotientTopSectionMap R S
        (divisorGenericUnitQuotientGlobalSectionEquiv R D) := by
  let X := Spec (CommRingCat.of R)
  let Y := Spec (CommRingCat.of S)
  let KR := FractionRing R
  let KS := FractionRing S
  let Q_R := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
    (Spec.map (CommRingCat.ofHom (algebraMap R KR))))
  let Q_S := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
    (Spec.map (CommRingCat.ofHom (algebraMap S KS))))
  let e := EtaleCohomology.etaleRestrictionFractionFieldUnitQuotientIso R S KR KS
  let eP := (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).mapIso e
  let W_S := (EtaleCohomology.zariskiToEtale Y).obj ⊤
  have : IsDedekindDomain S :=
    IsDedekindDomain.of_essFiniteType_formallyUnramified R S
  let qR := divisorGenericUnitQuotientGlobalSectionEquiv R D
  have hsection (E : HeightOneSpectrum S →₀ ℤ) :
      ConcreteCategory.hom (eP.hom.app (op W_S))
        (affineEtaleDivisorGenericUnitQuotientSectionEquiv R S E) =
      divisorGenericUnitQuotientSection S E := by
    change ConcreteCategory.hom (eP.hom.app (op W_S))
        (ConcreteCategory.hom (eP.inv.app (op W_S))
          (divisorGenericUnitQuotientSection S E)) = _
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app,
      ConcreteCategory.id_apply]
  apply genericUnitQuotientSectionCoefficient_jointly_injective S
  intro w
  let v := heightOneSpectrumContractionOfEtale (R := R) (S := S) w
  have hvw : w.asIdeal.under R = v.asIdeal := rfl
  have hmap := genericUnitQuotientSectionCoefficient_map
    (R := R) (S := S) v w hvw qR
  calc
    genericUnitQuotientSectionCoefficient S w
        (ConcreteCategory.hom (eP.hom.app (op W_S))
          (affineEtaleDivisorGenericUnitQuotientSectionEquiv R S
            (affineEtaleDivisorPullback D))) =
        affineEtaleDivisorPullback D w := by
          rw [hsection, genericUnitQuotientSectionCoefficient_divisor]
    _ = D v := by
      rw [affineEtaleDivisorPullback_apply]
    _ = genericUnitQuotientSectionCoefficient R v qR := by
          change D v = genericUnitQuotientSectionCoefficient R v
            (divisorGenericUnitQuotientSection R D)
          exact (genericUnitQuotientSectionCoefficient_divisor R v D).symm
    _ = genericUnitQuotientSectionCoefficient S w
        (affineEtaleGenericUnitQuotientTopSectionMap R S qR) := hmap.symm

/-- On sections corresponding to finite divisors, the comparison map is
exactly the divisor pullback under the global divisor-section equivalences. -/
theorem affineEtaleTopSectionMap_on_divisor
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      algRS.toSMul (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (D : HeightOneSpectrum R →₀ ℤ) :
    let _hS : IsDedekindDomain S :=
      IsDedekindDomain.of_essFiniteType_formallyUnramified R S
    affineEtaleGenericUnitQuotientTopSectionMap R S
      (divisorGenericUnitQuotientGlobalSectionEquiv R D) =
    divisorGenericUnitQuotientGlobalSectionEquiv S
      (affineEtaleDivisorPullback D) := by
  dsimp only
  have hS : IsDedekindDomain S :=
    IsDedekindDomain.of_essFiniteType_formallyUnramified R S
  let e := EtaleCohomology.affineEtaleFractionRingUnitQuotientIso R S
  let eP := (sheafToPresheaf (Spec (CommRingCat.of S)).smallEtaleTopology
    AddCommGrpCat.{u}).mapIso e
  let W_S := (EtaleCohomology.zariskiToEtale
    (Spec (CommRingCat.of S))).obj ⊤
  have hsection (E : HeightOneSpectrum S →₀ ℤ) :
      ConcreteCategory.hom (eP.hom.app (op W_S))
        (affineEtaleDivisorGenericUnitQuotientSectionEquiv R S E) =
      divisorGenericUnitQuotientSection S E := by
    change ConcreteCategory.hom (eP.hom.app (op W_S))
        (ConcreteCategory.hom (eP.inv.app (op W_S))
          (divisorGenericUnitQuotientSection S E)) = _
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app,
      ConcreteCategory.id_apply]
  have hcomm := affineEtaleDivisorPullback_commutes_with_topSectionMap
    (R := R) (S := S) D
  calc
    affineEtaleGenericUnitQuotientTopSectionMap R S
        (divisorGenericUnitQuotientGlobalSectionEquiv R D) =
        ConcreteCategory.hom (eP.hom.app (op W_S))
          (affineEtaleDivisorGenericUnitQuotientSectionEquiv R S
            (affineEtaleDivisorPullback D)) := hcomm.symm
    _ = divisorGenericUnitQuotientSection S (affineEtaleDivisorPullback D) :=
      hsection _
    _ = divisorGenericUnitQuotientGlobalSectionEquiv S
        (affineEtaleDivisorPullback D) := rfl

end AffineEtaleDivisorSections

/-- The top-section comparison associated with the identity algebra map is the
identity, as follows from its action on all divisor sections. -/
theorem affineEtaleTopSectionMap_id
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale
          (Spec (CommRingCat.of R))).obj ⊤))) :
    affineEtaleGenericUnitQuotientTopSectionMap R R q = q := by
  let eR := divisorGenericUnitQuotientGlobalSectionEquiv R
  obtain ⟨D, hq⟩ := eR.surjective q
  rw [← hq, affineEtaleTopSectionMap_on_divisor (R := R) (S := R) D]
  rw [affineEtaleDivisorPullback_id (R := R) rfl]

section AffineEtaleSectionComposition

variable (S T : Type u)
variable [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Etale R S]
variable [CommRing T] [IsDomain T] [Algebra S T] [Algebra.Etale S T]
variable [Algebra R T] [IsScalarTower R S T] [Algebra.Etale R T]

/-- The actual quotient-section comparison is contravariantly functorial under
composition of affine etale maps. This follows from the divisor comparison
equivalence and the coefficientwise composition law. -/
theorem affineEtaleTopSectionMap_comp
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    [algST : Algebra S (FractionRing T)]
    [hST : @IsScalarTower S T (FractionRing T)
      (inferInstance : Algebra S T).toSMul
      (inferInstance : Algebra T (FractionRing T)).toSMul algST.toSMul]
    [algKT : Algebra (FractionRing S) (FractionRing T)]
    [hKT : @IsScalarTower S (FractionRing S) (FractionRing T)
      (inferInstance : Algebra S (FractionRing S)).toSMul
      algKT.toSMul algST.toSMul]
    [algRT : Algebra R (FractionRing T)]
    [hRT : @IsScalarTower R T (FractionRing T)
      (inferInstance : Algebra R T).toSMul
      (inferInstance : Algebra T (FractionRing T)).toSMul algRT.toSMul]
    [algKT' : Algebra (FractionRing R) (FractionRing T)]
    [hKT' : @IsScalarTower R (FractionRing R) (FractionRing T)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKT'.toSMul algRT.toSMul]
    (q : (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (FractionRing R)))))).obj.obj
        (op ((EtaleCohomology.zariskiToEtale
          (Spec (CommRingCat.of R))).obj ⊤))) :
    let _hS : IsDedekindDomain S :=
      IsDedekindDomain.of_essFiniteType_formallyUnramified R S
    let _hT : IsDedekindDomain T :=
      IsDedekindDomain.of_essFiniteType_formallyUnramified R T
    affineEtaleGenericUnitQuotientTopSectionMap R T q =
      affineEtaleGenericUnitQuotientTopSectionMap S T
        (affineEtaleGenericUnitQuotientTopSectionMap R S q) := by
  dsimp only
  have hS : IsDedekindDomain S :=
    IsDedekindDomain.of_essFiniteType_formallyUnramified R S
  have hT : IsDedekindDomain T :=
    IsDedekindDomain.of_essFiniteType_formallyUnramified R T
  let eR := divisorGenericUnitQuotientGlobalSectionEquiv R
  obtain ⟨D, hq⟩ := eR.surjective q
  rw [← hq,
    affineEtaleTopSectionMap_on_divisor (R := R) (S := T) D,
    affineEtaleTopSectionMap_on_divisor (R := R) (S := S) D,
    affineEtaleTopSectionMap_on_divisor (R := S) (S := T)
      (affineEtaleDivisorPullback D)]
  rw [affineEtaleDivisorPullback_comp]

end AffineEtaleSectionComposition

end EtaleFundamentalGroups.StrictHenselian
