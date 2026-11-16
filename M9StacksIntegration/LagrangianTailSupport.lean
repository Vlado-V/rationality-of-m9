module

public import M9StacksIntegration.LagrangianTailLinearForms
public import M9StacksIntegration.LineSectionRangeSupport
public import M9StacksIntegration.LagrangianPrimitivePointVanishing
public import M9StacksIntegration.LagrangianHyperplaneRows

/-!
# The actual prefix meets its remaining linear space only in the final cut

Membership in the native projective tail locus puts each literal original
tail row in the projective point kernel. The proved original-point/support
dictionary gives the genuine determinant zero supports, and the actual cut
range theorem supplies the original final scheme's image. No intersection
or component-containment conclusion is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Module
open AlgebraicGeometry.ProjectiveSpaceOfModule
universe u
namespace M9Native.LagrangianTailSupport
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianProjectiveIntersection
  LagrangianProjectiveLinearForms LagrangianTailLinearSpace LagrangianTailLinearForms

variable (K : Type u) [Field K] [CharZero K]

local instance determinantLine_invertible :
    SheafOfModules.IsInvertible (space K).sheaf.obj (space K).ringCatSheaf.property (determinantLine K) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (LagrangianPluckerQuotient.determinantLine_invertible K)

def sectionList (M : Matrix (Fin 5) (Fin 14) K) : List Γ(determinantLine K, ⊤) :=
  List.ofFn (fun j => LagrangianHyperplaneCoordinates.determinantSection K (M j))

theorem remaining_sections_support (M : Matrix (Fin 5) (Fin 14) K)
    (i : ℕ) (hi : i ≤ 5) (x : space K)
    (hx : LagrangianPlucker.primitivePlucker K x ∈ locus K M i hi) :
    ∀ s ∈ (sectionList K M).drop i,
      x ∈ (Stacks.Divisors.zeroScheme (space K) (determinantLine K) s).support := by
  rw [sectionList, drop_ofFn_tail _ i hi]
  intro s hs
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
  have hp : LagrangianSymmetricPlucker.canonicalPlucker K x ∈
      linearSubspace K (Forms K) (constraints K M i hi) := by
    rw [LagrangianSymmetricPlucker.canonicalPlucker_eq, Scheme.Hom.comp_apply]
    exact hx
  rw [mem_linearSubspace_iff] at hp
  have hm := hp (row_mem_constraints K M i hi j)
  have hz := (LagrangianPrimitivePointVanishing.mem_pointSubmodule_iff_mem_support_zeroScheme
    K x (rowForms K M.mulVecLin (tailEmbedding i hi j))).mp hm
  rw [LagrangianHyperplaneRows.determinantSection_row]
  exact hz

theorem image_inter_subset_full (M : Matrix (Fin 5) (Fin 14) K) (i : ℕ) (hi : i ≤ 5) :
    Set.range ((IteratedLineSectionCuts.simultaneousCut (determinantLine K)
      ((sectionList K M).take i)).hom ≫ LagrangianPlucker.primitivePlucker K) ∩ locus K M i hi ⊆
    Set.range ((IteratedLineSectionCuts.simultaneousCut (determinantLine K)
      (sectionList K M)).hom ≫ LagrangianPlucker.primitivePlucker K) :=
  LineSectionRangeSupport.image_inter_of_tail_support (determinantLine K) (sectionList K M) i
    (LagrangianPlucker.primitivePlucker K) (locus K M i hi)
    (remaining_sections_support K M i hi)

end M9Native.LagrangianTailSupport
