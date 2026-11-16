module

public import M9StacksIntegration.LagrangianQuotientConstantTransport
public import M9StacksIntegration.Sp6VectorTransitivity

/-!
# The genuine common-kernel obstruction to original section injectivity

An actual relation among the original six quotient sections is normalized
by a constructed native constant symplectic matrix. The actual full
exterior-evaluation image is preserved under that true source equivalence.
The original primitive section image therefore has dimension at most five.

The final injection corollary records its independent primitive-span input
explicitly. The actual span-nine theorem for a transverse linear section
is a separate geometric producer; it is not assumed as a classifier field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite

universe u

namespace M9Native.LagrangianUniversalSectionInjection

open LagrangianField LagrangianGrassmannian LagrangianMatrixChart
open LagrangianPluckerQuotient LagrangianIsotropicRestriction
open LagrangianQuotientExteriorEvaluation LagrangianQuotientConstantTransport
open LagrangianKernelPrimitiveSections

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable {X : Scheme.{u}} (k : Type u) [Field k] [CharZero k]
  (f : X ⟶ Spec (.of k)) {Q : X.Modules} (q : freeOn X 6 ⟶ Q)

/-- The dimension-five obstruction is derived from an actual relation;
no symplectic normalizer, rank bound, or section-completeness premise is supplied. -/
theorem primitive_span_le_five_of_noninjective (hq : AnnihilatesSigma X q)
    (hbad : ¬ Function.Injective (originalSectionMap k f q)) :
    finrank k (Submodule.span k (Set.range (primitiveH0 k f q))) ≤ 5 := by
  have hker : (originalSectionMap k f q).ker ≠ ⊥ :=
    fun h => hbad (LinearMap.ker_eq_bot.mp h)
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  change originalSectionMap k f q v = 0 at hv
  obtain ⟨g, hg⟩ := Sp6VectorTransitivity.exists_matrixSix_send_e0 k v hvne
  have hg' : LagrangianTransitivity.symplecticEquiv k g (basisVector k 0) = v := hg
  have hzero := transformed_first_section_zero k f q g v hg' hv
  have hdim := finrank_range_lambda_le_five k f (transformedQuotient k f q g)
    (transformedQuotient_annihilates k f q g hq) hzero
  rw [range_lambda_transformed] at hdim
  rw [← range_primitiveEvaluation k f q hq, range_primitiveEvaluation_eq_span] at hdim
  exact hdim

/-- A genuine independently proved primitive image of dimension greater
than five forces injectivity of the actual original six sections. -/
theorem originalSectionMap_injective_of_primitive_span (hq : AnnihilatesSigma X q)
    (hspan : 5 < finrank k (Submodule.span k (Set.range (primitiveH0 k f q)))) :
    Function.Injective (originalSectionMap k f q) := by
  by_contra hbad
  exact Nat.not_lt_of_ge (primitive_span_le_five_of_noninjective k f q hq hbad) hspan

variable (l : X ⟶ LagrangianGrassmannian.space k)

omit [CharZero k] in
/-- The original universal quotient relation holds after actual pullback. -/
theorem universal_quotient_annihilates :
    AnnihilatesSigma X (LagrangianUniversalSections.quotientMap k l) := by
  change AnnihilatesSigma X (pulledQuotient l (quotientOnLG k).map)
  exact pulledQuotient_annihilates l (quotientOnLG k).map
    (LagrangianSymplecticAction.lagrangianUniversal_annihilates k)

omit [CharZero k] in
theorem originalSectionMap_eq_universal :
    originalSectionMap k f (LagrangianUniversalSections.quotientMap k l) =
      LagrangianUniversalSections.sectionMap k f l := rfl

/-- The original restricted universal six-section map is injective as
soon as its actual original primitive image exceeds the common-kernel bound. -/
theorem universal_sectionMap_injective_of_primitive_span
    (hspan : 5 < finrank k (Submodule.span k (Set.range
      (primitiveH0 k f (LagrangianUniversalSections.quotientMap k l))))) :
    Function.Injective (LagrangianUniversalSections.sectionMap k f l) := by
  rw [← originalSectionMap_eq_universal k f l]
  exact originalSectionMap_injective_of_primitive_span k f _
    (universal_quotient_annihilates k l) hspan

end M9Native.LagrangianUniversalSectionInjection
