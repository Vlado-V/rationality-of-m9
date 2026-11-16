module

public import M9StacksIntegration.RationalPointDivisor
public import M9StacksIntegration.CanonicalDivisorEvaluation
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization

/-!
# The actual restriction kernel on a reduced rational-point divisor

Restriction to the reduced closed subscheme of a finite tuple vanishes
exactly when the original section vanishes after pullback to every
canonical rational point of the tuple. This is derived from the actual
vanishing ideal and the genuine section zero scheme, without choosing
line bases or a vector-space structure on a tuple of point fibres.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace M9Native.RationalPointDivisorRestriction

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- The existing zero-scheme universal property gives the exact ideal
kernel criterion for a pulled invertible section. -/
theorem pullback_eq_zero_iff_zeroIdeal_le_ker {Y : Scheme.{u}}
    (g : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    pullbackGlobalSections g L s = 0 ↔ Stacks.Divisors.zeroScheme X L s ≤ g.ker := by
  rw [Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme]
  constructor
  · rintro ⟨b, hb⟩
    have hker := Scheme.Hom.le_ker_comp b (Stacks.Divisors.zeroScheme X L s).subschemeι
    rwa [ker_subschemeι, hb] at hker
  · intro h
    have hk : (Stacks.Divisors.zeroScheme X L s).subschemeι.ker ≤ g.ker := by
      simpa only [ker_subschemeι] using h
    exact ⟨IsClosedImmersion.lift (Stacks.Divisors.zeroScheme X L s).subschemeι g hk,
      IsClosedImmersion.lift_fac (Stacks.Divisors.zeroScheme X L s).subschemeι g hk⟩

/-- The actual canonical rational point maps every point of its field
spectrum to the original closed point. -/
theorem canonicalPoint_apply (c : closedPoints X) (z : Spec (.of K)) :
    ((pointEquivClosedPoint f).symm c).val z = c.val := by
  change pointOfClosedPoint f c.val c.property z = c.val
  exact pointOfClosedPoint_apply f c.val c.property z

/-- Containment in the kernel of an actual canonical rational point is
equivalent to membership of the original closed point in the support.
The reverse direction uses reducedness of the actual field spectrum. -/
theorem ideal_le_canonicalPoint_ker_iff (I : X.IdealSheafData)
    (c : closedPoints X) :
    I ≤ (((pointEquivClosedPoint f).symm c).val).ker ↔ c.val ∈ I.support := by
  let p := ((pointEquivClosedPoint f).symm c).val
  constructor
  · intro h
    apply support_antitone h
    exact p.range_subset_ker_support
      ⟨IsLocalRing.closedPoint K, canonicalPoint_apply f c _⟩
  · intro h
    have hrange : Set.range p ⊆ (I.support : Set X) := by
      rintro _ ⟨z, rfl⟩
      rw [show p z = c.val from canonicalPoint_apply f c z]
      exact h
    obtain ⟨g, hg⟩ :=
      (exists_lift_subschemeι_iff_range_subset_support I p).mpr hrange
    have hker : I ≤ (g ≫ I.subschemeι).ker := by
      simpa only [ker_subschemeι] using Scheme.Hom.le_ker_comp g I.subschemeι
    rwa [hg] at hker

/-- The actual vanishing ideal of the tuple is detected by the kernels
of its canonical rational points. No distinctness premise is needed. -/
theorem ideal_le_divisor_iff {n : ℕ} (c : Fin n → closedPoints X)
    (I : X.IdealSheafData) :
    I ≤ RationalPointDivisor.divisor c ↔
      ∀ i, I ≤ (((pointEquivClosedPoint f).symm (c i)).val).ker := by
  change I ≤ vanishingIdeal (RationalPointDivisor.pointSet c) ↔ _
  rw [← le_support_iff_le_vanishingIdeal]
  change (Set.range (fun i => (c i).val) ⊆ (I.support : Set X)) ↔ _
  rw [Set.range_subset_iff]
  exact forall_congr' fun i => (ideal_le_canonicalPoint_ker_iff f I (c i)).symm

/-- The original pulled section vanishes on the actual reduced tuple
divisor if and only if it vanishes at each actual canonical point. -/
theorem pullback_divisor_eq_zero_iff_points {n : ℕ}
    (c : Fin n → closedPoints X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    pullbackGlobalSections (RationalPointDivisor.divisor c).subschemeι L s = 0 ↔
      ∀ i, pullbackGlobalSections (((pointEquivClosedPoint f).symm (c i)).val) L s = 0 := by
  calc
    _ ↔ Stacks.Divisors.zeroScheme X L s ≤ RationalPointDivisor.divisor c := by
      rw [pullback_eq_zero_iff_zeroIdeal_le_ker, ker_subschemeι]
    _ ↔ ∀ i, Stacks.Divisors.zeroScheme X L s ≤
        (((pointEquivClosedPoint f).symm (c i)).val).ker :=
      ideal_le_divisor_iff f c _
    _ ↔ _ := forall_congr' fun i =>
      (pullback_eq_zero_iff_zeroIdeal_le_ker
        (((pointEquivClosedPoint f).symm (c i)).val) L s).symm

omit [IsAlgClosed K] [LocallyOfFiniteType f] in
/-- The actual H0/section isomorphism detects the restriction kernel and
reads it as the genuine pulled section. -/
theorem restriction_eq_zero_iff_pullback (D : X.IdealSheafData) (L : X.Modules)
    (x : cohomologyOverField K f L 0) :
    (cohomologyOverFieldMap K f (CurveDivisorSections.restrictionπ D L) 0).hom x = 0 ↔
      pullbackGlobalSections D.subschemeι L
        ((cohomologyOverFieldZeroLinearIso K f L).hom x) = 0 := by
  rw [← CanonicalDivisorEvaluation.evaluation_apply f D L x]
  change (cohomologyOverFieldMap K f (CurveDivisorSections.restrictionπ D L) 0).hom x = 0 ↔
    (cohomologyOverFieldZeroLinearIso K f _).hom
      ((cohomologyOverFieldMap K f (CurveDivisorSections.restrictionπ D L) 0).hom x) = 0
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso K f _).hom).injective).symm

/-- The kernel of native cohomology restriction to the actual reduced
point divisor is exactly pointwise vanishing of the original section.
Proper smooth curves and distinct tuples specialize to this statement. -/
theorem restriction_eq_zero_iff_points {n : ℕ}
    (c : Fin n → closedPoints X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (x : cohomologyOverField K f L 0) :
    (cohomologyOverFieldMap K f
      (CurveDivisorSections.restrictionπ (RationalPointDivisor.divisor c) L) 0).hom x = 0 ↔
      ∀ i, pullbackGlobalSections (((pointEquivClosedPoint f).symm (c i)).val) L
        ((cohomologyOverFieldZeroLinearIso K f L).hom x) = 0 :=
  (restriction_eq_zero_iff_pullback f (RationalPointDivisor.divisor c) L x).trans
    (pullback_divisor_eq_zero_iff_points f c L _)

end M9Native.RationalPointDivisorRestriction
