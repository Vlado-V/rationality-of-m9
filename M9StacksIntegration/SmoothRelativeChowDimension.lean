module

public import M9StacksIntegration.FiniteZeroRegularity
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.ChowSteps
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base

/-!
# Actual smooth relative dimension bounds field-Chow delta dimension

Native constant local fibre dimensions give equidimensional nonempty
fibres and their actual dimensions, hence the native relative-dimension
predicate. The native flat relative-dimension bound over the actual
field base then bounds delta dimension. Empty sources and fibres are
included; no integrality, nonemptiness or supplied purity is required.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow
universe u
namespace M9Native.SmoothRelativeChowDimension

/-- Actual constant smooth relative dimension gives the native
equidimensional-fibre predicate, on an arbitrary actual base scheme. -/
theorem relativeDimension_of_smooth_relative_dimension {X S : Scheme.{u}}
    (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f] :
    letI := SmoothOfRelativeDimension.smooth d f
    AlgebraicGeometry.RelativeDimension f d := by
  let := SmoothOfRelativeDimension.smooth d f
  intro s hs
  let : Nonempty (f.fiber s) := hs
  let : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  have hd (z : f.fiber s) : topologicalKrullDimAt (f.fiber s) z = (d : WithBot ℕ∞) := by
    rw [topologicalKrullDimAt_eq_localKrullDim]
    exact localKrullDim_fiber_eq_of_smoothOfRelativeDimension d f s z
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq (S.residueField s)
    (f.fiber s) (f.fiberToSpecResidueField s) hd, ?_⟩
  rw [topologicalKrullDim_eq_iSup_localKrullDim,
    iSup_congr fun z => localKrullDim_fiber_eq_of_smoothOfRelativeDimension d f s z,
    iSup_const]

/-- Over the original field the actual smooth relative dimension
bounds native delta dimension, with no integral or nonempty premise. -/
theorem schemeDeltaDimension_le_of_smooth_relative_dimension (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    letI := SmoothOfRelativeDimension.smooth d f
    schemeDeltaDimension (fieldChowSituation K) f ≤ (((d : ℕ) : ℤ) : EInt) := by
  let := SmoothOfRelativeDimension.smooth d f
  have hbase : schemeDeltaDimension (fieldChowSituation K)
      (𝟙 (fieldChowSituation K).S) ≤ (0 : EInt) := by
    rw [schemeDeltaDimension_eq_iSup]
    refine iSup_le fun Z => ?_
    simp only [deltaDimension, relativeDimension_id]
    exact le_rfl
  have h := SectionZeroScheme.schemeDeltaDimension_le_of_flat (fieldChowSituation K)
    (𝟙 (fieldChowSituation K).S) f d
    (relativeDimension_of_smooth_relative_dimension f d) hbase
  simpa only [Category.comp_id, Int.zero_add] using h

end M9Native.SmoothRelativeChowDimension
