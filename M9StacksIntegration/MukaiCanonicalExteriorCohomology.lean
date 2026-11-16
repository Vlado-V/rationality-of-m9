module

public import M9StacksIntegration.MukaiCanonicalExteriorNumerics
public import M9StacksIntegration.SchemeWedgeDuality

/-!
# The actual canonical rank-three exterior cohomology identity

Native perfect wedge duality and the actual canonical determinant identify
H⁰(⋀²E) with the actual Serre dual of H¹(E). Native determinant degree and
canonical degree give deg(E)=2g−2. Riemann--Roch then proves
h⁰(⋀²E)=h⁰(E)+8 in genus nine, hence fourteen when h⁰(E)=6.
No wedge-duality isomorphism, h¹ value, exterior section dimension or
canonical degree is supplied as a premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace M9Native.MukaiCanonicalExteriorCohomology

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : Scheme.{u}}

section ActualWedgeDuality

variable (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

/-- Perfectness of the literal native wedge map in degrees two and one
identifies the second exterior power with the actual determinant-valued Hom. -/
def rankThreeWedgeIso :
    exteriorSquare E ≅ RingedSite.internalHomSheaf (ringedSite X) E (exteriorCube E) := by
  let A := _root_.SheafOfModules.algebras (Osharp := X.sheaf)
    (Opens.grothendieckTopology X) E
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (2 + 1) :=
    inferInstanceAs (SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3)
  let : IsIso (M9Native.SchemeWedgeDuality.wedgeHom A.exterior 2 1) :=
    M9Native.SchemeWedgeDuality.isIso_wedgeHom A.exterior A.exterior_isExteriorAlgebra 2 1
  exact asIso (M9Native.SchemeWedgeDuality.wedgeHom A.exterior 2 1) ≪≫
    precomposeSheafHomIso A.exteriorGeneratorIso (exteriorCube E)

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]

/-- A canonical top exterior isomorphism yields the genuine wedge-induced
Serre-dual sheaf, with no supplied duality isomorphism. -/
def canonicalWedgeIso
    (d : exteriorCube E ≅ Stacks.Duality.dualizingSheafOverField f) :
    exteriorSquare E ≅ canonicalHom f E :=
  rankThreeWedgeIso E ≪≫ postcomposeSheafHomIso d E

end ActualWedgeDuality

section CanonicalCohomology

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (d : exteriorCube E ≅ Stacks.Duality.dualizingSheafOverField f)

include hdim d

/-- The actual second-exterior H⁰ is the actual Serre dual of H¹(E),
via the proved native perfect wedge map and the given canonical determinant. -/
def canonicalWedgeH0SerreEquiv :
    cohomologyOverField k f (exteriorSquare E) 0 ≃ₗ[k]
      (cohomologyOverField k f E 1 →ₗ[k] k) :=
  (cohomologyOverFieldIso k f (canonicalWedgeIso E f d) 0).toLinearEquiv.trans
    (h0CanonicalHomSerreEquiv k f hdim E)

/-- Serre duality computes the second-exterior section count from E's
first cohomology; this dimension equality is proved rather than assumed. -/
theorem h0_exteriorSquare_eq_h1 :
    Module.finrank k (cohomologyOverField k f (exteriorSquare E) 0) =
      Module.finrank k (cohomologyOverField k f E 1) := by
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f E 3
  let : Module.Finite k (cohomologyOverField k f E 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k f E 1
  exact (canonicalWedgeH0SerreEquiv k f hdim E d).finrank_eq.trans Subspace.dual_finrank_eq

variable [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

/-- Actual wedge duality and Riemann--Roch give the intrinsic section
identity for a rank-three bundle with canonical determinant. -/
theorem canonical_exterior_h0_identity :
    (Module.finrank k (cohomologyOverField k f (exteriorSquare E) 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f E 0) : ℤ) = (genus f : ℤ) - 1 := by
  rw [h0_exteriorSquare_eq_h1 k f hdim E d]
  exact canonical_h1_sub_h0_identity k f hdim E d

/-- On the actual genus-nine curve, the second-exterior section count
is h⁰(E)+8. No h¹ or second-exterior dimension is a premise. -/
theorem canonical_exterior_h0_genus_nine (hg : genus f = 9) :
    Module.finrank k (cohomologyOverField k f (exteriorSquare E) 0) =
      Module.finrank k (cohomologyOverField k f E 0) + 8 := by
  rw [h0_exteriorSquare_eq_h1 k f hdim E d]
  exact canonical_h1_genus_nine k f hdim E d hg

theorem canonical_exterior_h0_fourteen (hg : genus f = 9)
    (hE : Module.finrank k (cohomologyOverField k f E 0) = 6) :
    Module.finrank k (cohomologyOverField k f (exteriorSquare E) 0) = 14 := by
  have h := canonical_exterior_h0_genus_nine k f hdim E d hg
  omega

end CanonicalCohomology

section ActualCurve

variable (k : Type u) [Field k] [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (d : exteriorCube E ≅ Stacks.Duality.dualizingSheafOverField f)

include d

/-- The actual proper integral curve supplies its dimension and its
constant global functions, so the geometric interface has no such premises. -/
theorem curve_canonical_exterior_h0_genus_nine (hg : genus f = 9) :
    Module.finrank k (cohomologyOverField k f (exteriorSquare E) 0) =
      Module.finrank k (cohomologyOverField k f E 0) + 8 := by
  let := isIso_globalSections_of_isAlgClosed k f
  exact canonical_exterior_h0_genus_nine k f
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le E d hg

/-- The genuine h⁰(⋀²E)=14 input for the Mukai Lagrangian map. -/
theorem curve_canonical_exterior_h0_fourteen (hg : genus f = 9)
    (hE : Module.finrank k (cohomologyOverField k f E 0) = 6) :
    Module.finrank k (cohomologyOverField k f (exteriorSquare E) 0) = 14 := by
  have h := curve_canonical_exterior_h0_genus_nine k f E d hg
  omega

end ActualCurve

end M9Native.MukaiCanonicalExteriorCohomology
