module

public import M9StacksIntegration.MukaiRankTwoSubobjectBound
public import M9StacksIntegration.MukaiGeneratedQuotient
public import M9StacksIntegration.MukaiResidualLineBounds
public import M9StacksIntegration.MukaiRankTwoExteriorDegree
public import M9StacksIntegration.CurveDivisorSections

/-!
# Native genus-nine rank-two subobject bounds

The quotient-section and determinant-section bounds in the elementary
rank-two subobject argument are derived here. The original quotient is
generated and cannot be trivial; its degree is therefore at least six.
Actual degree additivity bounds the original rank-two determinant by
ten, and the proved native genus-nine line-bundle bound supplies its
four-section upper bound. No determinant section bound is assumed.

The canonical residual relation is the actual isomorphism from the
tensor product of the two degree-eight lines to the native dualizing
sheaf. Its invertibility and degree are derived by the residual-line
provider; no additional canonical formula is a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiGenusNineSubobjects

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

private theorem hom_eq_zero_of_outer_homs (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (T : X.Modules) (h1 : ∀ a : S.X₁ ⟶ T, a = 0) (h3 : ∀ a : S.X₃ ⟶ T, a = 0)
    (a : S.X₂ ⟶ T) : a = 0 := by
  let : Epi S.g := hS.epi_g
  have ha : S.f ≫ a = 0 := h1 _
  let b := hS.exact.desc a ha
  have hb : b = 0 := h3 b
  exact (hS.exact.g_desc a ha).symm.trans (by change S.g ≫ b = 0; rw [hb,comp_zero])

variable [IsAlgClosed k] [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)
variable (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
variable (S : ShortComplex X.Modules) (hS : S.ShortExact)
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₁]
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₃]
variable [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
variable (hgen : MukaiSemiIrreducible.GloballyGenerated S.X₂)
variable (hA : invertibleCurveDegree k f hdim S.X₁ = 2)
variable (hB : invertibleCurveDegree k f hdim S.X₃ = 6)
variable (E α : X.Modules)
variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
variable (i : S.X₂ ⟶ E) (p : E ⟶ α) (w : i ≫ p = 0)
variable (hT : (ShortComplex.mk i p w).ShortExact)
variable (hnonsplit : ∀ t : α ⟶ E, t ≫ p ≠ 𝟙 _)
variable (hα : invertibleCurveDegree k f hdim α = 8)
variable (hn : ¬ Nonempty (LinearSeries k f hdim 7 2))

include hS hA hB hT hα

omit [IsAlgClosed k] [Smooth f]
  [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3] in
/-- Vanishing of maps from the original extension to the structure
sheaf is derived from its two actual positive-degree filtrations. -/
theorem hom_structure_eq_zero (a : E ⟶ MukaiBundle.structureModule X) : a = 0 := by
  have hQ : ∀ b : S.X₂ ⟶ MukaiBundle.structureModule X, b = 0 :=
    hom_eq_zero_of_outer_homs S hS _
      (MukaiDualSpanSections.hom_structure_eq_zero_of_positive_degree f hdim S.X₁
        (by rw [hA]; decide))
      (MukaiDualSpanSections.hom_structure_eq_zero_of_positive_degree f hdim S.X₃
        (by rw [hB]; decide))
  exact hom_eq_zero_of_outer_homs (ShortComplex.mk i p w) hT _ hQ
    (MukaiDualSpanSections.hom_structure_eq_zero_of_positive_degree f hdim α
      (by rw [hα]; decide)) a

variable (hEgen : MukaiSemiIrreducible.GloballyGenerated E)
variable (β : X.Modules)
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
variable (hβ : invertibleCurveDegree k f hdim β = 8)
variable (e : MukaiBundleDeterminant.tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
variable (hg : genus f = 9)

include hnp hgen hnonsplit hn hEgen hβ e hg

/-- Every original rank-two subbundle has at most three sections.
Its quotient and determinant section bounds are proved internally. -/
theorem h0_le_three_of_subobject
    (hreg : IsRegular X) (hdegree : curveDegree k f hdim E 3 = 16)
    (F ξ : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (u : F ⟶ E) (v : E ⟶ ξ) (wv : u ≫ v = 0)
    (hU : (ShortComplex.mk u v wv).ShortExact) :
    Module.finrank k (cohomologyOverField k f F 0) ≤ 3 := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_isAlgClosed k f
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 2
  let : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X F
  let : FiniteDimensional k (cohomologyOverField k f F 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f F 0
  let : FiniteDimensional k (cohomologyOverField k f ξ 0) :=
    CurveDivisorSections.invertible_cohomology_zero_finite f ξ
  let : Epi v := hU.epi_g
  have hξ := MukaiGeneratedQuotient.two_le_h0_of_generated_no_unit_hom f E ξ hEgen v
    (hom_structure_eq_zero k f hdim S hS hA hB E α i p w hT hα)
  have hξdegree := MukaiPencilDegreeBounds.six_le_degree_of_two_sections f hdim hnp ξ hξ
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} ξ 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X ξ
  have hdeg := curveDegree_add_of_shortExact_of_isProper k f hdim
    (ShortComplex.mk u v wv) hU 2 3 1
  rw [← invertibleCurveDegree_eq_curveDegree k f hdim ξ] at hdeg
  change curveDegree k f hdim E 3 = curveDegree k f hdim F 2 +
    invertibleCurveDegree k f hdim ξ at hdeg
  rw [hdegree] at hdeg
  have hFdegree : curveDegree k f hdim F 2 ≤ 10 := by omega
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Modules.exteriorPower F 2) := MukaiTwistBounds.exterior_two_isInvertible F
  let : FiniteDimensional k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0) :=
    CurveDivisorSections.invertible_cohomology_zero_finite f _
  have hdetdegree := MukaiTwistBounds.degree_exterior_two f F
  change invertibleCurveDegree k f hdim (Scheme.Modules.exteriorPower F 2) =
    curveDegree k f hdim F 2 at hdetdegree
  have hdet := MukaiResidualLineBounds.h0_le_four_of_degree_le_ten
    f hdim hg hnp α β e hα hβ (Scheme.Modules.exteriorPower F 2)
    (by rw [hdetdegree]; exact hFdegree)
  exact MukaiRankTwoSubobjectBound.h0_le_three_of_subobject
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn
    hreg hdegree F ξ u v wv hU hξ hdet

end M9Native.MukaiGenusNineSubobjects
