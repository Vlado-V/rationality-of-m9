module

public import M9StacksIntegration.DirectC9Bundles
public import M9StacksIntegration.DirectC9OriginalPoint
public import M9StacksIntegration.DirectC9NormalizationClass

/-! The actual fixed degree-seventeen line on the original curve,
obtained from a constructed original-field point of C9. Its rank-nine
ordinary direct image follows from actual fibre cohomology and base change. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.CurvePower
open CartesianMonoidalCategory AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u
namespace M9Native.DirectC9InitialFixedFibre

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

variable (c₀ : power C 0 ⟶ C)

def repeatedPoint : Spec (.of k) ⟶ (power C 9).left :=
  (Stacks.CurvePower.lift 9 (fun _ => c₀)).left

theorem repeatedPoint_over : repeatedPoint k C c₀ ≫ (power C 9).hom = 𝟙 _ :=
  Over.w (Stacks.CurvePower.lift 9 (fun _ => c₀))

abbrev graph : C.left ⟶ familySpace C :=
  DirectC9OriginalPoint.pointGraph k C (repeatedPoint k C c₀) (repeatedPoint_over k C c₀)

theorem graph_isPullback :
    IsPullback (graph k C c₀) C.hom (familyProjection C) (repeatedPoint k C c₀) :=
  DirectC9OriginalPoint.pointGraph_isPullback k C (repeatedPoint k C c₀)
    (repeatedPoint_over k C c₀)

theorem graph_fst : graph k C c₀ ≫ (fst C (power C 9)).left = 𝟙 _ :=
  BaseFieldGraph.graph_fst C.hom (power C 9).hom (repeatedPoint k C c₀)
    (repeatedPoint_over k C c₀)

abbrev fixedFibreLine : C.left.Modules :=
  (Scheme.Modules.pullback (graph k C c₀)).obj (fixedLine C c₀ 16)

instance fixedFibreLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible C.left.presheaf C.left.ringCatSheaf.2
      (fixedFibreLine k C c₀) :=
  Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj (graph k C c₀)
    (fixedLine C c₀ 16)

theorem fixedLine_fibreCohomology (hg : genus C.hom = 9) (t : (power C 9).left) (i : ℕ) :
    Module.finrank ((power C 9).left.residueField t)
      (cohomologyOverField ((power C 9).left.residueField t)
        ((familyProjection C).fiberToSpecResidueField t)
        ((Scheme.Modules.pullback ((familyProjection C).fiberι t)).obj (fixedLine C c₀ 16)) i) =
      if i=0 then 9 else 0 := by
  apply DirectC9Cohomology.largeDegree_fibreFinrank k C (fixedLine C c₀ 16) hg 9 (by omega)
  intro y
  have hd := DirectC9FamilyDegree.constantFamily_degree C c₀
    (DirectC9FibreGeometry.fibre_dimension_le_one k C) 16 y
  have he : @PoincareChern.lineClass (familySpace C) (fixedLine C c₀ 16)
      (fixedLine_isInvertible C c₀ 16) =
      DirectC9FamilyDegree.familyClass C (constantFamily C c₀ 16) := rfl
  rw [he]
  exact hd.trans (by norm_num)

theorem fixedFibreLine_hasDerivedRank (hg : genus C.hom = 9) :
    HasDerivedPushforwardRank C.hom (fixedFibreLine k C c₀) 0 9 :=
  DirectC9Bundles.line_hasDerivedRank_of_fibreFinrank_baseChange (familyProjection C)
    (DirectC9FibreGeometry.projection_finitePresentation k C) (fixedLine C c₀ 16) 9
    (fixedLine_fibreCohomology k C c₀ hg) (repeatedPoint k C c₀) C.hom (graph k C c₀)
    (graph_isPullback k C c₀)

theorem fixedFibreLine_ordinary_rank (hg : genus C.hom = 9) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pushforward C.hom).obj (fixedFibreLine k C c₀)) 9 :=
  PoincareChern.OrdinaryDegreeZero.ordinaryPushforward_rank_of_derivedRank
    C.hom (fixedFibreLine k C c₀) 9 (fixedFibreLine_hasDerivedRank k C c₀ hg)

end M9Native.DirectC9InitialFixedFibre
