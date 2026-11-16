module

public import M9StacksIntegration.CanonicalLineCohomology
public import M9StacksIntegration.MukaiFilteredVanishing
public import StacksFrontier.AlgebraicGeometry.AmpleCurve.Basic
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional

/-!
# The actual genus-nine canonical Hilbert function

Strict degree comparison makes the actual H¹ of every canonical power
of exponent at least two vanish by native Serre duality. Native tensor
degree and Riemann--Roch then give the actual H⁰ value 16t−8.
The smooth-curve construction separately supplies invertibility of the
actual dualizing sheaf; no desired Hilbert value is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

universe u

namespace M9Native.CanonicalHilbertFunction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Duality (dualizingSheafOverField)

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f]
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
  (dualizingSheafOverField f)]

/-- The literal native tensor power of the actual canonical module. -/
abbrev canonicalPower (t : ℕ) : X.Modules :=
  Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.property
    (dualizingSheafOverField f) (t : ℤ)

instance canonicalPower_isInvertible (t : ℕ) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (canonicalPower f t) :=
  Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf X.ringCatSheaf.property
    (dualizingSheafOverField f) (t : ℤ)

variable (hdim : topologicalKrullDim X ≤ 1)

include hdim

/-- The original first cohomology is a zero module once its line has
degree strictly greater than the actual canonical line. -/
theorem h1_isZero_of_canonical_degree_lt [IsCurve k f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hdeg : invertibleCurveDegree k f hdim (dualizingSheafOverField f) <
      invertibleCurveDegree k f hdim L) :
    IsZero (cohomologyOverField k f L 1) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : L.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  by_contra hn
  obtain ⟨φ, hφ⟩ := Stacks.Duality.exists_ne_zero_hom_dualizingSheaf f hdim L
    (isQuasicoherent_of_isCoherent _) hn
  exact hφ (MukaiFilteredVanishing.hom_eq_zero_of_degree_lt f hdim L
    (dualizingSheafOverField f) hdeg φ)

/-- Actual native cohomology has the genus-nine canonical Hilbert
value 16t−8 for every exponent t≥2. -/
theorem canonical_power_h0 [IsCurve k f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hg : genus f = 9) (t : ℕ) (ht : 2 ≤ t) :
    (Module.finrank k (cohomologyOverField k f (canonicalPower f t) 0) : ℤ) =
      16 * (t : ℤ) - 8 := by
  have hK : invertibleCurveDegree k f hdim (dualizingSheafOverField f) = 16 := by
    calc
      _ = 2 * (genus f : ℤ) - 2 := CanonicalLineCohomology.canonical_degree f hdim
      _ = 16 := by rw [hg]; norm_num
  have hP : invertibleCurveDegree k f hdim (canonicalPower f t) = (t : ℤ) * 16 := by
    have h := invertibleCurveDegree_tensorPower_eq_mul k f hdim (dualizingSheafOverField f)
      (@invertibleCurveDegree_tensorSheaf_eq_add k _ X f _ hdim) (t : ℤ)
    change invertibleCurveDegree k f hdim (canonicalPower f t) =
      (t : ℤ) * invertibleCurveDegree k f hdim (dualizingSheafOverField f) at h
    rwa [hK] at h
  have hlt : invertibleCurveDegree k f hdim (dualizingSheafOverField f) <
      invertibleCurveDegree k f hdim (canonicalPower f t) := by
    rw [hK, hP]
    have ht' : (2 : ℤ) ≤ t := by exact_mod_cast ht
    omega
  have hz := h1_isZero_of_canonical_degree_lt f hdim (canonicalPower f t) hlt
  have h1 : Module.finrank k (cohomologyOverField k f (canonicalPower f t) 1) = 0 := by
    let : Subsingleton (cohomologyOverField k f (canonicalPower f t) 1) :=
      ModuleCat.subsingleton_of_isZero hz
    exact Module.finrank_zero_of_subsingleton
  have hRR := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdim (canonicalPower f t)
  rw [h1, hP, hg] at hRR
  push_cast at hRR
  linarith

end M9Native.CanonicalHilbertFunction
