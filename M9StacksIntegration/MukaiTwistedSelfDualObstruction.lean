module

public import M9StacksIntegration.MukaiDualDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.EpiResidueFields
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.EpiIso

/-!
# The degree obstruction to a twisted self-dual Mukai bundle

An actual map ξ ⊗ E∨ → E that is an isomorphism on every actual field
fiber is globally an isomorphism: residue-field Nakayama gives epimorphy,
and the proved equal-rank criterion gives isomorphy. Actual tensor and
dual degrees then imply rank(E) · deg(ξ) = 2 · deg(E). For rank three and
degree sixteen this is impossible in the integers.

This is the obstruction used in Theorem C, Step 2. No failure of
transversality, conormal nondegeneracy, or projective geometric conclusion
is claimed here. The all-field isomorphism condition is an explicit input
to the contradiction, and is not asserted for an arbitrary conormal map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundleDeterminant

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.MukaiTwistedSelfDualObstruction

variable {X : Scheme.{u}}

/-- The actual twisted dual, with the literal native tensor and dual. -/
abbrev twistedDual (ξ E : X.Modules) : X.Modules := tensor ξ (dualSheaf E)

theorem twistedDual_rank (ξ E : X.Modules) (r : ℕ)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (twistedDual ξ E) r := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf E) r :=
    isFiniteLocallyFreeOfRank_dualSheaf E r hE
  have h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (twistedDual ξ E) (1*r) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X ξ (dualSheaf E) 1 r
  simpa only [Nat.one_mul] using h

/-- Invertibility of the actual sheaf map after every actual field pullback. -/
def FieldFiberIsomorphisms {M N : X.Modules} (a : M ⟶ N) : Prop :=
  ∀ (K : Type u) [Field K] (p : Spec (.of K) ⟶ X),
    IsIso ((Scheme.Modules.pullback p).map a)

/-- Equal-rank vector-bundle maps which are isomorphisms at every field
fiber are actual global isomorphisms. -/
theorem isIso_of_fieldFiberIsomorphisms {M N : X.Modules} (a : M ⟶ N) (r : ℕ)
    (hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} M r)
    (hN : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} N r)
    (ha : FieldFiberIsomorphisms a) : IsIso a := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} M r := hM
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} N r := hN
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} N := hN.isFiniteLocallyFree
  have hep : Epi a := by
    apply Scheme.Modules.epi_of_forall_epi_pullback_fromSpecResidueField a
      (Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree N)
    intro x
    let p := X.fromSpecResidueField x
    let e : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj N :=
      @asIso _ _ _ _ ((Scheme.Modules.pullback p).map a) (ha (X.residueField x) p)
    exact (show Epi e.hom from inferInstance)
  let : Epi a := hep
  exact SheafOfModules.isIso_of_epi_of_isFiniteLocallyFreeOfRank a r

theorem twistedDual_isIso_of_fieldFibers (ξ E : X.Modules) (r : ℕ)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r)
    (a : twistedDual ξ E ⟶ E) (ha : FieldFiberIsomorphisms a) : IsIso a :=
  isIso_of_fieldFiberIsomorphisms a r (twistedDual_rank ξ E r hE) hE ha

section Curve

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)

/-- The genuine global isomorphism forces the actual integral degree
relation. The dual degree is proved by actual sheaf constructions. -/
theorem degree_relation_of_iso (hreg : IsRegular X) (ξ E : X.Modules) (n : ℕ)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]
    (e : twistedDual ξ E ≅ E) :
    ((n+1 : ℕ) : ℤ) * invertibleCurveDegree k f hdim ξ =
      2 * curveDegree k f hdim E (n+1) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf E) (n+1) :=
    isFiniteLocallyFreeOfRank_dualSheaf E (n+1) hE
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (twistedDual ξ E) (n+1) :=
    twistedDual_rank ξ E (n+1) hE
  have hd := MukaiDualDegree.curveDegree_dual_positive k f hdim hreg n E hE
  have hi := curveDegree_eq_of_iso k f hdim (n+1) e
  have ht : curveDegree k f hdim (twistedDual ξ E) (n+1) =
      ((n+1 : ℕ) : ℤ) * curveDegree k f hdim ξ 1 +
        curveDegree k f hdim (dualSheaf E) (n+1) := by
    simpa only [Nat.one_mul, Nat.cast_one, one_mul] using
      (MukaiDualDegree.curveDegree_tensor k f hdim ξ (dualSheaf E) 1 (n+1))
  have hp := congrArg (fun z : ℤ => ((n+1 : ℕ) : ℤ) * z)
    (invertibleCurveDegree_eq_curveDegree_one k f hdim ξ)
  linarith

/-- Rank three and degree sixteen contradict the integral degree relation. -/
theorem no_iso_rankThree_degreeSixteen (hreg : IsRegular X) (ξ E : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (hdegree : curveDegree k f hdim E 3 = 16) (e : twistedDual ξ E ≅ E) : False := by
  have h := degree_relation_of_iso k f hdim hreg ξ E 2 e
  change (3 : ℤ) * invertibleCurveDegree k f hdim ξ =
    2 * curveDegree k f hdim E 3 at h
  rw [hdegree] at h
  omega

/-- The actual all-field-fiber invertibility assumption is impossible;
no global isomorphism is an input. -/
theorem not_fieldFiberIsomorphisms_rankThree_degreeSixteen
    (hreg : IsRegular X) (ξ E : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (hdegree : curveDegree k f hdim E 3 = 16) (a : twistedDual ξ E ⟶ E) :
    ¬ FieldFiberIsomorphisms a := by
  intro ha
  exact no_iso_rankThree_degreeSixteen k f hdim hreg ξ E hdegree
    (@asIso _ _ _ _ a (twistedDual_isIso_of_fieldFibers ξ E 3 hE a ha))

/-- The original smooth proper curve supplies regularity itself. -/
theorem not_fieldFiberIsomorphisms_on_smooth_curve [Smooth f]
    (ξ E : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (hdegree : curveDegree k f hdim E 3 = 16) (a : twistedDual ξ E ⟶ E) :
    ¬ FieldFiberIsomorphisms a :=
  not_fieldFiberIsomorphisms_rankThree_degreeSixteen k f hdim
    (isRegular_of_smooth_over_field f) ξ E hdegree a

end Curve

end M9Native.MukaiTwistedSelfDualObstruction
