module

public import M9StacksIntegration.BoundedCoverAtlasPointImage

/-! Finite actual bounded-cover families miss a dense open of each
actual integral smooth-classifier atlas piece. Native comparison points
are excluded via the constructed representing scheme and its real arrow. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace M9Native.FiniteBoundedCoverAtlasAvoidance

open BoundedCoverAtlasPullback

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (hK : B.Contains (Spec (.of K)))
  {V : BigFppfOver B (Spec (.of K)) hK}
  (b : Stack.schemeStack.{u,u+1} B (Spec (.of K)) hK V ⟶
    CoverFamilyStackPullback.sourceStack B hZ K hK)
  [QuasiCompact (B.inclusion.map V.hom)] [LocallyOfFiniteType (B.inclusion.map V.hom)]

/-- Every actual comparison point of finitely many genuine bounded
covers avoids one common dense original open. The finite-type pullback
schemes, their raw cover families and family arrows are constructed. -/
theorem exists_dense_open_avoiding_comparisonPoints
    [IsIntegral (B.inclusion.obj (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b).base.left)]
    [LocallyOfFiniteType (NativeCoverFamilyAtlasArrow.targetStructure B hZ K hK V b)]
    (hR : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK
        (curvesFiberedCategory_isAlgebraicStack.{u,u+1} B hZ)
        (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b)
        (NativeCoverFamilyAtlasArrow.targetStructure B hZ K hK V b)))
    {ι : Type v} [Finite ι] (D : ι → BoundedCoverFamily B K) :
    ∃ U : (B.inclusion.obj (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b).base.left).Opens,
      Dense (U : Set (B.inclusion.obj
        (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b).base.left)) ∧
      (U : Set (B.inclusion.obj
        (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b).base.left)).Nonempty ∧
      ∀ (i : ι) (T : BigFppfOver B (Spec (.of K)) hK)
        (F : CoverFamilyStackPullback.PointData B hZ K hK (sourceBase B K hK (D i)) V
          (classifier B hZ K hK (D i)) b (P := T)) (t : B.inclusion.obj T.left),
        BoundedCoverAtlasPointImage.targetPoint B hZ K hK (D i) b F t ∉ U := by
  classical
  let E : ∀ i, BoundedCoverAtlasPullback.Data B hZ K hK (D i) b :=
    fun i => Classical.choice (BoundedCoverAtlasPullback.exists_data B hZ K hK (D i) b)
  obtain ⟨U,hd,hn,hdisj⟩ :=
    BoundedCoverFamily.exists_dense_open_avoiding_finite_parameterImages B hZ K hK
      (curvesFiberedCategory_isAlgebraicStack.{u,u+1} B hZ)
      (fun i => (E i).boundedFamily)
      (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b)
      (NativeCoverFamilyAtlasArrow.targetStructure B hZ K hK V b)
      (fun i => (E i).familyArrow) (fun i => (E i).familyArrow_ground) hR
  refine ⟨U,hd,hn,?_⟩
  intro i T F t ht
  exact Set.disjoint_left.mp (hdisj i)
    (BoundedCoverAtlasPointImage.targetPoint_mem_range B hZ K hK (D i) b F (E i) t) ht

end M9Native.FiniteBoundedCoverAtlasAvoidance
end
