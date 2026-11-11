/- 
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.AffineGenericUnitQuotient
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineGenericPointStalkComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorData
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorTransport
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorCompatibility

/-!
# Naturality of the affine divisor comparison

Combine the independently proved source transport and divisor compatibility.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open IsDedekindDomain
open EtaleFundamentalGroups.StrictHenselian
universe u
namespace EtaleCohomology

variable (R S T : Type u)
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S]
  [CommRing T] [IsDedekindDomain T]
  [Algebra R S] [Algebra.Etale R S]
  [Algebra S T] [Algebra.Etale S T]
  [Algebra R T] [IsScalarTower R S T] [Algebra.Etale R T]
  [algRS : Algebra R (FractionRing S)]
  [hRS : @IsScalarTower R S (FractionRing S)
    (inferInstance : Algebra R S).toSMul
    (inferInstance : Algebra S (FractionRing S)).toSMul algRS.toSMul]
  [algKS : Algebra (FractionRing R) (FractionRing S)]
  [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
    (inferInstance : Algebra R (FractionRing R)).toSMul algKS.toSMul algRS.toSMul]
  [algST : Algebra S (FractionRing T)]
  [hST : @IsScalarTower S T (FractionRing T)
    (inferInstance : Algebra S T).toSMul
    (inferInstance : Algebra T (FractionRing T)).toSMul algST.toSMul]
  [algKT : Algebra (FractionRing S) (FractionRing T)]
  [hKT : @IsScalarTower S (FractionRing S) (FractionRing T)
    (inferInstance : Algebra S (FractionRing S)).toSMul algKT.toSMul algST.toSMul]
  [algRT : Algebra R (FractionRing T)]
  [hRT : @IsScalarTower R T (FractionRing T)
    (inferInstance : Algebra R T).toSMul
    (inferInstance : Algebra T (FractionRing T)).toSMul algRT.toSMul]
  [algRKT : Algebra (FractionRing R) (FractionRing T)]
  [hRKT : @IsScalarTower R (FractionRing R) (FractionRing T)
    (inferInstance : Algebra R (FractionRing R)).toSMul algRKT.toSMul algRT.toSMul]


/-- The actual divisor and generic-unit quotient comparisons are natural
along arrows between affine étale spectra. -/
theorem affineEtaleClosedPointDivisorGenericUnitObject_naturality
    (hR : ¬ IsField R)
    [HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (s : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv
      (R := R) (S := T) hR
      (ConcreteCategory.hom
        ((closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.map
          (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op) s) =
    ConcreteCategory.hom ((affineGenericPointUnitQuotient R).obj.map
      (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op)
        (affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv
          (R := R) (S := S) hR s) := by
  apply (affineEtaleGenericUnitObjectToSourceAddEquiv (R := R) (S := T)).injective
  rw [affineEtaleClosedPointDivisorGenericUnitObject_compat,
    affineEtaleGenericUnitObjectToSource_naturality,
    affineEtaleClosedPointDivisorGenericUnitObject_compat]
  exact affineEtaleClosedPointDivisorToGenericUnitQuotient_naturality
    (R := R) (S := S) (T := T) hR s

end EtaleCohomology
