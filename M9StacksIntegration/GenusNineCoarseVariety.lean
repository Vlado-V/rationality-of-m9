module

public import M9StacksIntegration.GenusNineStackSmooth
public import M9StacksIntegration.GenusNineStackQuasiCompact
public import M9StacksIntegration.CoarseReducedTarget
public import M9StacksIntegration.CoarseSeparatedTarget
public import M9StacksIntegration.CoarseFiniteTypeTarget
public import M9StacksIntegration.CoarseDecentTarget
public import M9StacksIntegration.AllTestNativeOriginalVarietyGeometry

@[expose] public section

/-! Properties of the actual coarse algebraic space, on all original test
schemes. Structural smoothness and boundedness of the genuine source are
proved inputs; reducedness, separation and finite type of this target are
conclusions. No replacement by a reduced or pointwise moduli space is made.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9Native.GenusNineCoarseVariety

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

open M9StacksIntegration.GenusNineCoarseOverField

/-- Reducedness of the original native coarse space, derived by the genuine
categorical universal property and source smoothness. -/
theorem reduced (g : ℕ) (hg : 2 ≤ g) :
    Space.HasEtaleLocalProperty B (Spec (.of K)) hK
      (coarseSpace B hZ K hK g hg).obj (fun T : Scheme.{u} => IsReduced T) :=
  CoarseReducedTarget.reduced_of_categorical B (Spec (.of K)) hK
    (smoothStack B hZ K hK g hg) (coarseSpace B hZ K hK g hg)
    (coarseMap B hZ K hK g hg)
    (Stack.isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace
      B (Spec (.of K)) hK (coarseMap_uniform B hZ K hK g hg))
    (GenusNineStackSmooth.reduced B hZ K hK g hg)

/-- Genuine relative separatedness of the actual coarse target. -/
theorem separated (g : ℕ) (hg : 2 ≤ g) :
    Space.IsSeparatedOver B (Spec (.of K)) hK (coarseSpace B hZ K hK g hg).obj :=
  CoarseSeparatedTarget.separated_of_coarse_universalHomeomorphism B (Spec (.of K)) hK
    (smoothStack B hZ K hK g hg) (coarseSpace B hZ K hK g hg)
    (coarseMap B hZ K hK g hg) (coarseMap_universalHomeomorphism B hZ K hK g hg)
    (smoothStack_separated B hZ K hK g hg)

/-- Decency is derived from actual target separatedness, so integrality
assembly needs no independent decency premise. -/
theorem decent (g : ℕ) (hg : 2 ≤ g) :
    Space.IsDecentSpace B (Spec (.of K)) hK (coarseSpace B hZ K hK g hg).obj :=
  CoarseDecentTarget.decent_of_separated B (Spec (.of K)) hK
    (coarseSpace B hZ K hK g hg) (separated B hZ K hK g hg)

/-- Actual local finite type of the same original structural morphism. -/
theorem locallyFiniteType (g : ℕ) (hg : 2 ≤ g) :
    Space.IsLocallyOfFiniteType B (Spec (.of K)) hK
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).from
        (coarseSpace B hZ K hK g hg).obj) :=
  CoarseFiniteTypeTarget.locallyFiniteType_of_categorical B K hK
    (smoothStack B hZ K hK g hg) (coarseSpace B hZ K hK g hg)
    (coarseMap B hZ K hK g hg)
    (Stack.isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace
      B (Spec (.of K)) hK (coarseMap_uniform B hZ K hK g hg))
    (smoothStack_finite_inertia B hZ K hK g hg)
    (GenusNineStackSmooth.locallyFiniteType B hZ K hK g hg)

/-- Surjectivity follows from the original constructor's actual universal
homeomorphism, rather than an assumed field-point classification. -/
theorem coarseMap_surjective (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsSurjective B (Spec (.of K)) hK (coarseMap B hZ K hK g hg) := by
  let f := coarseMap B hZ K hK g hg
  let Y := coarseSpace B hZ K hK g hg
  let C := Stack.twoFibreProductSquareAlgebraicStacks B (Spec (.of K)) hK (𝟙 _) f
  have hs : Function.Surjective
      (Stack.AlgebraicStacks.pointsMap B (Spec (.of K)) hK C.fst) := by
    letI := Stack.pointTopology B (Spec (.of K)) hK C.pt.val
    letI := Stack.pointTopology B (Spec (.of K)) hK
      (Stack.algebraicSpaceStack.{u,u+1} B (Spec (.of K)) hK Y.obj Y.property).val
    exact ((coarseMap_universalHomeomorphism B hZ K hK g hg) _ (𝟙 _) C
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks
        B (Spec (.of K)) hK (𝟙 _) f)).surjective
  have hc := Stack.AlgebraicStacks.pointsMap_eq_of_hom₂ B (Spec (.of K)) hK C.iso.hom
  rw [Category.comp_id, Stack.AlgebraicStacks.pointsMap_comp] at hc
  rw [hc] at hs
  exact hs.of_comp

/-- Actual boundedness of smooth genus-g families gives quasi-compactness of
this exact coarse target. -/
theorem quasiCompact (g : ℕ) (hg : 2 ≤ g) :
    Space.IsQuasiCompactSpace B (Spec (.of K)) hK (coarseSpace B hZ K hK g hg).obj :=
  CoarseFiniteTypeTarget.quasiCompact_of_surjective B K hK
    (smoothStack B hZ K hK g hg) (coarseSpace B hZ K hK g hg)
    (coarseMap B hZ K hK g hg) (coarseMap_surjective B hZ K hK g hg)
    (GenusNineStackQuasiCompact.quasiCompact B hZ K hK g hg)

/-- The genuine actual coarse space is a variety on all original test
schemes, without a supplied variety/reducedness/normality/finite-type premise. -/
theorem variety (g : ℕ) (hg : 2 ≤ g) :
    M9StandaloneDraft.VarietySpace K
      (M9StacksIntegration.AllTestNativeOriginalSpace.originalSpaceOfNative K B hK
        (coarseSpace B hZ K hK g hg).obj (coarseSpace B hZ K hK g hg).property) :=
  M9StacksIntegration.AllTestNativeOriginalVarietyGeometry.variety_of_native_locallyFiniteType
    K B hK (coarseSpace B hZ K hK g hg).obj (coarseSpace B hZ K hK g hg).property
    (separated B hZ K hK g hg) (reduced B hZ K hK g hg)
    (locallyFiniteType B hZ K hK g hg) (quasiCompact B hZ K hK g hg)

/-- The genus-nine instance for the actual coarse target in the main goal. -/
theorem genusNine_variety :
    M9StandaloneDraft.VarietySpace K
      (M9StacksIntegration.AllTestNativeOriginalSpace.originalSpaceOfNative K B hK
        (genusNineCoarseSpace B hZ K hK).obj (genusNineCoarseSpace B hZ K hK).property) :=
  variety B hZ K hK 9 (by decide)

end M9Native.GenusNineCoarseVariety
