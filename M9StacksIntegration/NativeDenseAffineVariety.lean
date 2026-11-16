module

public import M9StacksIntegration.NativeIntegralDenseScheme
public import M9StacksIntegration.AllTestNativeOriginalVarietyAtlas

/-!
# An actual dense affine integral variety over the original field

A nonempty affine open of the actual integral schematic locus stays dense.
Affineness supplies separatedness and quasi-compactness of the actual original
structural map. Its local finite type is extracted from the genuine native
structural morphism by the checked same-chart comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9StacksIntegration.NativeDenseAffineVariety
open AllTestBoundedCharts AllTestNativeOriginalFunctor AllTestNativeOriginalPullbacks
attribute [local instance] Space.pointTopology

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- An integral native algebraic space has a dense open represented by an
actual affine integral scheme in the same bounded site. -/
theorem exists_native_affine_integral_dense_scheme
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (hI : Space.IsIntegralSpace B (Spec (.of K)) hK X.obj) :
    ∃ (V : BigFppfOver B (Spec (.of K)) hK) (b : yoneda.obj V ⟶ X.obj),
      IsAffine ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj V) ∧
      IsIntegral ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj V) ∧
      Space.IsOpenImmersion B (Spec (.of K)) hK b ∧
      DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj V) b) := by
  obtain ⟨U, a, ha, hd, hU⟩ :=
    NativeIntegralDenseScheme.exists_native_integral_dense_scheme K B hK X hI
  haveI : IsIntegral ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U) := hU
  let x : (BigFppfOver.toScheme B (Spec (.of K)) hK).obj U := Classical.choice inferInstance
  obtain ⟨W, hWaff, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := x) (U := ⊤) (show x ∈ (⊤ : ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U).Opens)
      from trivial)
  let V := Space.opensObject B (Spec (.of K)) hK U W
  let i : V ⟶ U := Space.opensObjectι B (Spec (.of K)) hK U W
  have hVAff : IsAffine ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj V) := hWaff
  haveI : Nonempty ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj V) := ⟨⟨x, hxW⟩⟩
  have hi : IsOpenImmersion ((BigFppfOver.toScheme B (Spec (.of K)) hK).map i) :=
    inferInstanceAs (IsOpenImmersion W.ι)
  haveI := hi
  have hiDense : DenseRange ((BigFppfOver.toScheme B (Spec (.of K)) hK).map i) :=
    IsOpenMap.denseRange_of_isPreirreducibleSpace _
      ((BigFppfOver.toScheme B (Spec (.of K)) hK).map i).isOpenMap
  have hiNative : Space.IsOpenImmersion B (Spec (.of K)) hK (yoneda.map i) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of K)) hK
      (@IsOpenImmersion.{u}) i).mpr hi
  let b : yoneda.obj V ⟶ X.obj := yoneda.map i ≫ a
  have hb : Space.IsOpenImmersion B (Spec (.of K)) hK b :=
    Space.isOpenImmersion_comp B (Spec (.of K)) hK _ _ hiNative ha
  have hiDenseNative : DenseRange (Space.pointsMap B (Spec (.of K)) hK
      (yoneda.obj V) (yoneda.map i)) := by
    change Dense (Set.range (Space.pointsMap B (Spec (.of K)) hK
      (yoneda.obj V) (yoneda.map i)))
    rw [Space.range_pointsMap_yoneda_eq_preimage]
    exact hiDense.preimage (Space.schemePointsHomeomorph B (Spec (.of K)) hK U).isOpenMap
  have hbDense : DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj V) b) := by
    change DenseRange (Space.pointsMap B (Spec (.of K)) hK
      (yoneda.obj V) (yoneda.map i ≫ a))
    rw [Space.pointsMap_comp]
    exact hd.comp hiDenseNative (Space.continuous_pointsMap B (Spec (.of K)) hK a)
  exact ⟨V, b, hVAff,
    NativeIntegralDenseScheme.scheme_isIntegral_of_dense_open K B hK X hI.1 hI.2.2 V b hb hbDense,
    hb, hbDense⟩

/-- Genuine native integral and local-finite-type geometry constructs an
actual affine integral separated finite-type original scheme dense open,
retaining its actual native arrow and its literal original map. -/
theorem exists_original_dense_affine_chart
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (hI : Space.IsIntegralSpace B (Spec (.of K)) hK X.obj)
    (hf : Space.IsLocallyOfFiniteType B (Spec (.of K)) hK
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).from X.obj)) :
    ∃ (V : BigFppfOver B (Spec (.of K)) hK) (b : yoneda.obj V ⟶ X.obj),
      IsAffine ((boundedInclusion B K hK).obj V).left ∧
      IsIntegral ((boundedInclusion B K hK).obj V).left ∧
      IsSeparated ((boundedInclusion B K hK).obj V).hom ∧
      LocallyOfFiniteType ((boundedInclusion B K hK).obj V).hom ∧
      QuasiCompact ((boundedInclusion B K hK).obj V).hom ∧
      Space.IsOpenImmersion B (Spec (.of K)) hK b ∧
      DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj V) b) ∧
      M9StandaloneDraft.DenseOpen K (originalChart K B hK X V b) := by
  obtain ⟨V, b, hVA, hVI, hb, hd⟩ := exists_native_affine_integral_dense_scheme K B hK X hI
  haveI : IsAffine ((boundedInclusion B K hK).obj V).left := hVA
  have hL := AllTestNativeOriginalVarietyAtlas.native_chart_locallyOfFiniteType
    K B hK X.obj hf V b (NativeIntegralDenseScheme.etale_of_open K B hK V b hb)
  exact ⟨V, b, hVA, hVI, inferInstance, hL, inferInstance, hb, hd,
    NativeDenseSchematicOriginal.originalChart_denseOpen K B hK X V b hb hd⟩

/-- The conclusion is a concrete original scheme over the SAME field,
with all variety hypotheses proved and a literal original dense-open map. -/
theorem exists_original_dense_affine_variety
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (hI : Space.IsIntegralSpace B (Spec (.of K)) hK X.obj)
    (hf : Space.IsLocallyOfFiniteType B (Spec (.of K)) hK
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).from X.obj)) :
    ∃ (V : M9StandaloneDraft.Schemes K)
      (j : yoneda.obj V ⟶ (originalPresheafFunctor K B hK).obj X),
      IsAffine V.left ∧ IsIntegral V.left ∧ IsSeparated V.hom ∧
      LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ M9StandaloneDraft.DenseOpen K j := by
  obtain ⟨V, b, hVA, hVI, hVS, hVL, hVQ, _, _, hd⟩ :=
    exists_original_dense_affine_chart K B hK X hI hf
  exact ⟨(boundedInclusion B K hK).obj V, originalChart K B hK X V b,
    hVA, hVI, hVS, hVL, hVQ, hd⟩

end M9StacksIntegration.NativeDenseAffineVariety
