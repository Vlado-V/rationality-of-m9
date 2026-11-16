module

public import M9StacksIntegration.MukaiBundleTensor
public import M9StacksIntegration.MukaiBundleUniqueness
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.FirstVariable
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne
public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-!
# Canonical rank-three bundles and their second exterior cohomology

The cohomological core uses the actual native Serre equivalence and
Riemann--Roch for a finite locally free sheaf. The exterior and canonical
degree identifications are constructed from the native wedge and degree
providers, rather than supplied as dimension hypotheses.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Opposite

universe u

namespace M9Native.MukaiCanonicalExteriorCohomology

variable {X : Scheme.{u}}

/-- The literal second exterior power on the native scheme. -/
abbrev exteriorSquare (E : X.Modules) : X.Modules := Scheme.Modules.exteriorPower E (2 : ℤ)

/-- The literal top exterior power of a rank-three native bundle. -/
abbrev exteriorCube (E : X.Modules) : X.Modules := Scheme.Modules.exteriorPower E (3 : ℤ)

/-- The native scheme regarded as its actual ringed site. -/
abbrev ringedSite (X : Scheme.{u}) : RingedSite.{u,u,u} :=
  ⟨X.Opens, Opens.grothendieckTopology X, X.sheaf⟩

/-- Precomposition on native sheaf-Hom is transported by the genuine
contravariant internal-Hom functor. -/
def precomposeSheafHomIso {F G : X.Modules} (e : F ≅ G) (W : X.Modules) :
    RingedSite.internalHomSheaf (ringedSite X) G W ≅
      RingedSite.internalHomSheaf (ringedSite X) F W :=
  ((Stacks.SheafOfModules.InternalHom.internalHomFirstFunctor (ringedSite X) W).mapIso e).unop

/-- Postcomposition on native sheaf-Hom is transported by its genuine
covariant second-variable functor. -/
def postcomposeSheafHomIso {F G : X.Modules} (e : F ≅ G) (V : X.Modules) :
    RingedSite.internalHomSheaf (ringedSite X) V F ≅
      RingedSite.internalHomSheaf (ringedSite X) V G :=
  (Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor
    (Opens.grothendieckTopology X) X.sheaf V).mapIso e

/-- The actual native sheaf of morphisms into the actual canonical sheaf. -/
abbrev canonicalHom {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    [IsProper f] (E : X.Modules) : X.Modules :=
  RingedSite.internalHomSheaf (ringedSite X) E (Stacks.Duality.dualizingSheafOverField f)

/-- A genuine canonical top-exterior identification proves invertibility
of the native dualizing sheaf; this is not an extra hypothesis. -/
theorem canonical_isInvertible_of_topExteriorIso {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (d : exteriorCube E ≅ Stacks.Duality.dualizingSheafOverField f) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (exteriorCube E) 1 :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 3
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Stacks.Duality.dualizingSheafOverField f) 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso d inferInstance
  exact Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _

section CohomologyCore

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

/-- The actual global-section comparison is used with its checked
linearity in precisely the original native base-field scalar structure. -/
def h0CanonicalHomLinearEquiv :
    letI := modulesLinearOverField k f
    cohomologyOverField k f (canonicalHom f E) 0 ≃ₗ[k]
      (E ⟶ Stacks.Duality.dualizingSheafOverField f) := by
  letI := modulesLinearOverField k f
  exact (MukaiBundleUniqueness.homH0SheafHomLinearEquiv k f E
    (Stacks.Duality.dualizingSheafOverField f)).symm

include hdim in
/-- Global sections of the native canonical sheaf-Hom are the actual
Serre dual of H¹, without a supplied cohomological dimension. -/
def h0CanonicalHomSerreEquiv :
    cohomologyOverField k f (canonicalHom f E) 0 ≃ₗ[k]
      (cohomologyOverField k f E 1 →ₗ[k] k) := by
  letI := modulesLinearOverField k f
  letI : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f E 3
  exact (h0CanonicalHomLinearEquiv k f E).trans
    (Stacks.Duality.homDualizingSheafLinearEquiv f hdim E (isQuasicoherent_of_isCoherent E))

include hdim in
/-- The actual canonical sheaf-Hom has H⁰ of dimension h¹(E), from the
native linear global-section comparison and native linear Serre duality. -/
theorem finrank_h0CanonicalHom_eq_h1 :
    Module.finrank k (cohomologyOverField k f (canonicalHom f E) 0) =
      Module.finrank k (cohomologyOverField k f E 1) := by
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f E 3
  let : Module.Finite k (cohomologyOverField k f E 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k f E 1
  exact (h0CanonicalHomSerreEquiv k f hdim E).finrank_eq.trans Subspace.dual_finrank_eq

include hdim in
/-- The actual Serre duality equivalence computes morphisms into the
native dualizing sheaf in the original base-field scalar structure. -/
theorem finrank_homCanonical_eq_h1 :
    letI := modulesLinearOverField k f
    Module.finrank k (E ⟶ Stacks.Duality.dualizingSheafOverField f) =
      Module.finrank k (cohomologyOverField k f E 1) := by
  let := modulesLinearOverField k f
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f E 3
  let : Module.Finite k (cohomologyOverField k f E 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k f E 1
  exact (Stacks.Duality.homDualizingSheafLinearEquiv f hdim E
    (isQuasicoherent_of_isCoherent E)).finrank_eq.trans Subspace.dual_finrank_eq

/-- Riemann--Roch is specialized to the actual rank-three cohomology,
using the native vanishing above degree one. -/
theorem rankThree_riemannRoch
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    (Module.finrank k (cohomologyOverField k f E 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f E 1) : ℤ) =
      curveDegree k f hdim E 3 + 3 * (1 - (genus f : ℤ)) := by
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f E 3
  exact (finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f E
    (isZero_cohomologyOverField_two_le k f hdim E)).symm.trans
      (eulerCharacteristic_eq_curveDegree_add_genus k f hdim E 3)

/-- Combining actual Serre duality and actual Riemann--Roch leaves only
the intrinsic degree and genus; neither cohomological dimension is assumed. -/
theorem rankThree_homCanonicalEuler
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    letI := modulesLinearOverField k f
    (Module.finrank k (E ⟶ Stacks.Duality.dualizingSheafOverField f) : ℤ) -
        (Module.finrank k (cohomologyOverField k f E 0) : ℤ) =
      -(curveDegree k f hdim E 3 + 3 * (1 - (genus f : ℤ))) := by
  let := modulesLinearOverField k f
  rw [finrank_homCanonical_eq_h1 k f hdim E]
  have h := rankThree_riemannRoch k f hdim E
  linarith

end CohomologyCore

end M9Native.MukaiCanonicalExteriorCohomology
