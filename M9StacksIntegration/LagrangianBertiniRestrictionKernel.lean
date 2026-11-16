module

public import M9StacksIntegration.LagrangianPrimitiveIndependence
public import M9StacksIntegration.LagrangianPrimitiveRestriction
public import M9StacksIntegration.IntegralRestrictionLadder
public import M9StacksIntegration.SmoothIntegralHyperplaneCuts
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom

/-! The genuine constructed five-cut curve has exactly the five
original coefficient relations. All integral prefixes are supplied
internally by the frozen actual Bertini construction. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open Stacks.Bertini

universe u

namespace M9Native.LagrangianBertiniRestrictionKernel

open SmoothIntegralHyperplaneCuts IntegralRestrictionLadder

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

omit [IsAlgClosed K] in
theorem initialSystem_kernel : LinearMap.ker (initialSystem K).ψ = ⊥ := by
  apply le_antisymm
  · intro v hv
    change v = 0
    apply LagrangianPrimitiveIndependence.coefficients_eq_zero_of_determinantSection K v
    have h : LagrangianHyperplaneCoordinates.linearSection K v = 0 := by
      rw [← initialSystem_section K v]
      exact hv
    have hi := congrArg ((LagrangianHyperplaneCoordinates.lineIso K).hom.app ⊤) h
    rw [LagrangianHyperplaneCoordinates.lineIso_linearSection,map_zero] at hi
    exact hi
  · exact bot_le

omit [IsAlgClosed K] [CharZero K] in
private theorem span_snoc {V : Type u} [AddCommGroup V] [Module K V]
    {r : ℕ} (v : Fin r → V) (w : V) :
    Submodule.span K (Set.range (Fin.snoc v w)) =
      Submodule.span K (Set.range v) ⊔ Submodule.span K {w} := by
  have hs : Set.range (Fin.snoc v w) = Set.range v ∪ {w} := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact Or.inr (by simp)
      · exact Or.inl ⟨j,by simp⟩
    · rintro (⟨j,rfl⟩ | hx)
      · exact ⟨j.castSucc,by simp⟩
      · exact ⟨Fin.last r,by simpa using (Set.mem_singleton_iff.mp hx).symm⟩
  rw [hs,Submodule.span_union]

private theorem next_kernel {d r : ℕ} (S : CutState (initialSystem K) (d+2) r) :
    LinearMap.ker (restrictionMap (initialSystem K)
      (nextState (initialSystem K) (initialSystem_generates K) (initialSystem_immersive K) S).toRoot) =
      LinearMap.ker (restrictionMap (initialSystem K) S.toRoot) ⊔
        Submodule.span K (Set.singleton (nextCoefficients (initialSystem K)
          (initialSystem_generates K) (initialSystem_immersive K) S)) := by
  let : IsIntegral (Over.mk S.toRoot).left := by
    change IsIntegral S.X
    exact S.integral
  let : IsClosedImmersion (Over.mk S.toRoot).hom := by
    change IsClosedImmersion S.toRoot
    exact S.closed
  let : IsAlgClosed (initialSystem K).k := (inferInstance : IsAlgClosed K)
  exact ker_cut (initialSystem K) (Over.mk S.toRoot)
    (nextCoefficients (initialSystem K) (initialSystem_generates K) (initialSystem_immersive K) S)
    (nextDivisor_section_ne_zero (initialSystem K)
      (initialSystem_generates K) (initialSystem_immersive K) S)

private theorem next_kernel_span {d r : ℕ} (S : CutState (initialSystem K) (d+2) r)
    (h : LinearMap.ker (restrictionMap (initialSystem K) S.toRoot) =
      Submodule.span K (Set.range S.coefficients)) :
    LinearMap.ker (restrictionMap (initialSystem K)
      (nextState (initialSystem K) (initialSystem_generates K) (initialSystem_immersive K) S).toRoot) =
      Submodule.span K (Set.range
        (nextState (initialSystem K) (initialSystem_generates K) (initialSystem_immersive K) S).coefficients) := by
  rw [next_kernel K S,h]
  exact (span_snoc K (V := Fin 14 → K) S.coefficients
    (nextCoefficients (initialSystem K) (initialSystem_generates K) (initialSystem_immersive K) S)).symm

/-- Exact kernel for the actual constructed final curve, with no
prefix-integrality or kernel hypothesis remaining. -/
theorem fiveCut_kernel :
    LinearMap.ker (restrictionMap (initialSystem K) (fiveCutToLG K)) =
      Submodule.span K (Set.range (fifthState K).coefficients) := by
  have h0 : LinearMap.ker (restrictionMap (initialSystem K) (initialState K).toRoot) =
      Submodule.span K (Set.range (initialState K).coefficients) := by
    change LinearMap.ker (restrictionMap (initialSystem K) (𝟙 (initialSystem K).X)) = _
    rw [ker_pullback_identity,initialSystem_kernel]
    have he : Set.range (initialState K).coefficients = (∅ : Set (Fin 14 → K)) := by
      ext v
      constructor
      · rintro ⟨i,_⟩
        exact Fin.elim0 i
      · intro hv
        exact False.elim hv
    rw [he,Submodule.span_empty]
  have h1 := next_kernel_span K (initialState K) h0
  have h2 := next_kernel_span K (firstState K) h1
  have h3 := next_kernel_span K (secondState K) h2
  have h4 := next_kernel_span K (thirdState K) h3
  exact next_kernel_span K (fourthState K) h4

theorem fiveCut_primitiveRestriction_kernel :
    LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
      (fiveCutToLG K ≫ LagrangianGrassmannian.projection K) (fiveCutToLG K)) =
        Submodule.span K (Set.range (fifthState K).coefficients) := by
  rw [← fiveCut_kernel K]
  ext v
  rw [LinearMap.mem_ker,LagrangianPrimitiveRestriction.primitiveRestriction_ker_iff K _ _ rfl]
  change pullbackGlobalSections (fiveCutToLG K) (LagrangianPluckerQuotient.determinantLine K)
    (LagrangianHyperplaneCoordinates.determinantSection K v) = 0 ↔
      pullbackGlobalSections (fiveCutToLG K) (initialSystem K).L
        ((initialSystem K).sectionOf v) = 0
  rw [initialSystem_section]
  exact (LagrangianHyperplaneCoordinates.pullback_linearSection_zero_iff K
    (fiveCutToLG K) v).symm

theorem fiveCut_primitiveRestriction_kernel_finrank :
    finrank K (LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
      (fiveCutToLG K ≫ LagrangianGrassmannian.projection K) (fiveCutToLG K))) = 5 := by
  rw [fiveCut_primitiveRestriction_kernel]
  exact finrank_span_eq_card (fifthState K).independent

/-- The actual original primitive section image has dimension nine,
proved before any genus or canonical-completeness assertion. -/
theorem fiveCut_primitiveRestriction_range_finrank :
    finrank K (LinearMap.range (LagrangianPrimitiveRestriction.primitiveRestriction K
      (fiveCutToLG K ≫ LagrangianGrassmannian.projection K) (fiveCutToLG K))) = 9 := by
  have hd := (LagrangianPrimitiveRestriction.primitiveRestriction K
    (fiveCutToLG K ≫ LagrangianGrassmannian.projection K) (fiveCutToLG K)).finrank_range_add_finrank_ker
  rw [fiveCut_primitiveRestriction_kernel_finrank] at hd
  have h14 : finrank K (Fin 14 → K) = 14 := by simp
  rw [h14] at hd
  omega

theorem fiveCut_primitiveH0_span_finrank :
    finrank K (Submodule.span K (Set.range
      (LagrangianPrimitiveRestriction.sectionH0 K
        (fiveCutToLG K ≫ LagrangianGrassmannian.projection K) (fiveCutToLG K)))) = 9 := by
  rw [← LagrangianPrimitiveRestriction.primitiveRestriction_range]
  exact fiveCut_primitiveRestriction_range_finrank K

abbrev structuralMap : fiveCutCurve K ⟶ Spec (.of K) :=
  fiveCutToLG K ≫ LagrangianGrassmannian.projection K

instance fiveCut_closed : IsClosedImmersion (fiveCutToLG K) := (fifthState K).closed

instance fiveCut_proper : IsProper (structuralMap K) := by
  let : IsProper (LagrangianGrassmannian.projection K) := by
    rw [← initialSystem_toBase K]
    infer_instance
  change IsProper (fiveCutToLG K ≫ LagrangianGrassmannian.projection K)
  infer_instance

instance fiveCut_isCurve : IsCurve K (structuralMap K) := by
  let : IsIntegral (fiveCutCurve K) := fiveCutCurve_integral K
  exact (isCurve_iff K (structuralMap K)).mpr ⟨⟨⟩,fiveCutCurve_dimension K⟩

/-- The genuine canonical H0 dimension turns the proved nine-dimensional
original image into surjectivity.  Genus is an actual curve invariant. -/
theorem fiveCut_canonicalRestriction_surjective
    (c : LagrangianPrimitiveRestriction.restrictedLine K (fiveCutToLG K) ≅
      Stacks.Duality.dualizingSheafOverField (structuralMap K))
    (hg : genus (structuralMap K) = 9) :
    Function.Surjective (LagrangianPrimitiveRestriction.canonicalRestriction K
      (structuralMap K) (fiveCutToLG K) c) := by
  let F := LagrangianPrimitiveRestriction.canonicalRestriction K
    (structuralMap K) (fiveCutToLG K) c
  let : IsIntegral (fiveCutCurve K) := fiveCutCurve_integral K
  let : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (structuralMap K).appTop) :=
    isIso_globalSections_of_isAlgClosed K (structuralMap K)
  have hk : finrank K (LinearMap.ker F) = 5 := by
    rw [LagrangianPrimitiveRestriction.canonicalRestriction_kernel]
    exact fiveCut_primitiveRestriction_kernel_finrank K
  have h9 : finrank K (cohomologyOverField K (structuralMap K)
      (Stacks.Duality.dualizingSheafOverField (structuralMap K)) 0) = 9 :=
    (Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField
      (structuralMap K) (fiveCutCurve_dimension K).le).trans hg
  let : FiniteDimensional K (cohomologyOverField K (structuralMap K)
      (Stacks.Duality.dualizingSheafOverField (structuralMap K)) 0) :=
    Module.finite_of_finrank_pos (by rw [h9]; decide)
  have hd := F.finrank_range_add_finrank_ker
  rw [hk] at hd
  have h14 : finrank K (Fin 14 → K) = 14 := by simp
  rw [h14] at hd
  have hr : finrank K (LinearMap.range F) = 9 := by omega
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (hr.trans h9.symm))

end M9Native.LagrangianBertiniRestrictionKernel
end
