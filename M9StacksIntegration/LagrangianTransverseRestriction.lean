module

public import M9StacksIntegration.LagrangianIntegralPrefixes
public import M9StacksIntegration.LagrangianIntegralPrefixData
public import M9StacksIntegration.LagrangianIntegralPrefixRestriction
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension

/-! Mukai II, Lemma 4.2 on the literal original transverse five-row
section. Prefix geometry is a theorem of the original actual section;
neither a prefix condition nor a kernel/span claim is an input. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Module

universe u

namespace M9Native.LagrangianTransverseRestriction

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianPrimitiveSystem

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

abbrev curve (M : Matrix (Fin 5) (Fin 14) K) : Scheme.{u} := (sectionCut K M).left
abbrev inclusion (M : Matrix (Fin 5) (Fin 14) K) : curve K M ⟶ space K := (sectionCut K M).hom
abbrev curveProjection (M : Matrix (Fin 5) (Fin 14) K) : curve K M ⟶ Spec (.of K) :=
  inclusion K M ≫ projection K

omit [IsAlgClosed K] in
instance curve_proper (M : Matrix (Fin 5) (Fin 14) K) : IsProper (curveProjection K M) :=
  LagrangianIntegralPrefixRestriction.sectionCut_proper K M

variable (M : Matrix (Fin 5) (Fin 14) K)
  [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]

/-- The exact recursive geometric predicate is derived from the
actual transverse original section, including every next nonzero row. -/
theorem derivedIntegralPrefixes (hM : Function.Surjective M.mulVec) : IntegralPrefixes K M := by
  let : IsIntegral
      (IteratedLineSectionCuts.simultaneousCut (determinantLine K)
        (LagrangianPrefixIntegralStep.sections K M)).left := by
    change IsIntegral (curve K M)
    infer_instance
  let : SmoothOfRelativeDimension 1
      ((IteratedLineSectionCuts.simultaneousCut (determinantLine K)
        (LagrangianPrefixIntegralStep.sections K M)).hom ≫ projection K) := by
    change SmoothOfRelativeDimension 1 (curveProjection K M)
    infer_instance
  have hMLin : Function.Surjective M.mulVecLin := hM
  apply LagrangianIntegralPrefixData.integralPrefixes_of_data K M
  · intro i hi
    exact LagrangianIntegralPrefixes.integral_prefixes K M hMLin i hi
  · intro i hi
    exact LagrangianIntegralPrefixes.prefix_section_ne_zero K M hMLin i hi

/-- The actual primitive restriction has precisely the five original
defining rows as kernel. No linear-normality hypothesis is supplied. -/
theorem primitiveRestriction_kernel (hM : Function.Surjective M.mulVec) :
    LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
      (curveProjection K M) (inclusion K M)) = Submodule.span K (Set.range M) :=
  LagrangianIntegralPrefixRestriction.primitiveRestriction_kernel K M (derivedIntegralPrefixes K M hM)

theorem primitiveRestriction_kernel_finrank (hM : Function.Surjective M.mulVec) :
    finrank K (LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
      (curveProjection K M) (inclusion K M))) = 5 :=
  LagrangianIntegralPrefixRestriction.primitiveRestriction_kernel_finrank K M hM
    (derivedIntegralPrefixes K M hM)

theorem primitiveRestriction_range_finrank (hM : Function.Surjective M.mulVec) :
    finrank K (LinearMap.range (LagrangianPrimitiveRestriction.primitiveRestriction K
      (curveProjection K M) (inclusion K M))) = 9 :=
  LagrangianIntegralPrefixRestriction.primitiveRestriction_range_finrank K M hM
    (derivedIntegralPrefixes K M hM)

theorem primitiveH0_span_finrank (hM : Function.Surjective M.mulVec) :
    finrank K (Submodule.span K (Set.range
      (LagrangianPrimitiveRestriction.sectionH0 K (curveProjection K M) (inclusion K M)))) = 9 :=
  LagrangianIntegralPrefixRestriction.primitiveH0_span_finrank K M hM
    (derivedIntegralPrefixes K M hM)

/-- Every actual vanishing primitive coefficient vector is an actual
linear combination of the original five rows. -/
theorem exists_vecMul_of_restriction_eq_zero (hM : Function.Surjective M.mulVec)
    (v : Fin 14 → K)
    (hv : LagrangianPrimitiveRestriction.primitiveRestriction K
      (curveProjection K M) (inclusion K M) v = 0) :
    ∃ a : Fin 5 → K, v = Matrix.vecMul a M := by
  have hmem : v ∈ Submodule.span K (Set.range M) := by
    rw [← primitiveRestriction_kernel K M hM]
    exact hv
  rw [← Fintype.range_linearCombination K M] at hmem
  obtain ⟨a,ha⟩ := hmem
  refine ⟨a,ha.symm.trans ?_⟩
  funext j
  simp [Fintype.linearCombination_apply,Matrix.vecMul,dotProduct,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

theorem exists_nonzero_vecMul_of_restriction_eq_zero (hM : Function.Surjective M.mulVec)
    (v : Fin 14 → K)
    (hv : LagrangianPrimitiveRestriction.primitiveRestriction K
      (curveProjection K M) (inclusion K M) v = 0) (hv0 : v ≠ 0) :
    ∃ a : Fin 5 → K, a ≠ 0 ∧ v = Matrix.vecMul a M := by
  obtain ⟨a,ha⟩ := exists_vecMul_of_restriction_eq_zero K M hM v hv
  refine ⟨a,?_,ha⟩
  intro hz
  rw [hz,Matrix.zero_vecMul] at ha
  exact hv0 ha

instance curve_isCurve : IsCurve K (curveProjection K M) := by
  let : Smooth (curveProjection K M) := SmoothOfRelativeDimension.smooth 1 _
  exact (isCurve_iff K (curveProjection K M)).mpr
    ⟨⟨⟩,topologicalKrullDim_eq_of_smoothOfRelativeDimension (curveProjection K M) 1⟩

/-- An actual canonical-line identification transports the proved
original kernel; existence of that identification is adjunction. -/
theorem canonicalRestriction_kernel (hM : Function.Surjective M.mulVec)
    (c : LagrangianPrimitiveRestriction.restrictedLine K (inclusion K M) ≅
      Stacks.Duality.dualizingSheafOverField (curveProjection K M)) :
    LinearMap.ker (LagrangianPrimitiveRestriction.canonicalRestriction K
      (curveProjection K M) (inclusion K M) c) = Submodule.span K (Set.range M) :=
  LagrangianIntegralPrefixRestriction.canonicalRestriction_kernel K M
    (derivedIntegralPrefixes K M hM) c

/-- Actual genus nine and actual adjunction give the surjective
restriction to native canonical H0, with the same five original rows. -/
theorem canonicalRestriction_surjective (hM : Function.Surjective M.mulVec)
    (c : LagrangianPrimitiveRestriction.restrictedLine K (inclusion K M) ≅
      Stacks.Duality.dualizingSheafOverField (curveProjection K M))
    (hg : genus (curveProjection K M) = 9) :
    Function.Surjective (LagrangianPrimitiveRestriction.canonicalRestriction K
      (curveProjection K M) (inclusion K M) c) :=
  LagrangianIntegralPrefixRestriction.canonicalRestriction_surjective K M hM
    (derivedIntegralPrefixes K M hM) c hg

end M9Native.LagrangianTransverseRestriction
end
