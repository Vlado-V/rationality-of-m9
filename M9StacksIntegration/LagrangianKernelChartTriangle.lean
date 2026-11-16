module

public import M9StacksIntegration.LagrangianKernelProjectiveComparison
public import M9StacksIntegration.LagrangianKernelFivePullback

/-!
# The genuine five-space projective triangle on the original zero scheme

The original affine Grassmannian charts supply actual determinant-line
frames. Literal section expansion forces unit-ideal generation of the
five functions. The resulting native projective triangle is descended
through the actual pulled-back cover, and gives a closed immersion of
the original section-zero scheme into projective four-space.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianKernelChartTriangle

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianPullback
open LagrangianPluckerGeneration LagrangianPluckerTrivialization
open LagrangianKernelFiveSections LagrangianKernelFivePullback
open LagrangianKernelProjectiveComparison LagrangianKernelLinearEmbedding
open LagrangianCommonKernelSpan LagrangianCommonKernelZero
open Stacks.ProjectiveSpaceChartRatio
open AlgebraicGeometry.Grassmannian

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

/-- Actual unit-ideal generation follows from literal function expansion. -/
theorem span_eq_top_of_expansion {R : Type u} [CommRing R]
    {m n : ℕ} (s : Fin m → R) (t : Fin n → R) (c : Fin m → Fin n → R)
    (hs : Ideal.span (Set.range s) = ⊤)
    (h : ∀ j, s j = ∑ a, c j a * t a) : Ideal.span (Set.range t) = ⊤ := by
  apply top_unique
  rw [← hs]
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  rw [h j]
  apply Submodule.sum_mem
  intro a _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, rfl⟩)

private theorem moduleIso_app_injective {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) : Function.Injective (e.hom.app ⊤) := by
  intro x y h
  have hi (s : Γ(M, ⊤)) : e.inv.app ⊤ (e.hom.app ⊤ s) = s := by
    change (e.hom ≫ e.inv).app ⊤ s = s
    rw [Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  exact (hi x).symm.trans ((congrArg (fun s => e.inv.app ⊤ s) h).trans (hi y))

variable (k : Type u) [Field k] {X : Scheme.{u}}
  (l : X ⟶ space k)

/-- Literal expansion in the actual pulled-back universal determinant line. -/
theorem pulledPrimitive_expansion
    (hq : (LagrangianUniversalSections.quotientMap k l).app ⊤
      (freeBasisSection X 6 0) = 0) (j : Fin 14) :
    pullbackGlobalSections l (determinantLine k) (primitiveSections k j) =
      ∑ a : Fin 5, baseRingHom (l ≫ projection k)
        (embeddingFourteen k (Pi.single a 1) j) • pulledFiveSections k l a := by
  apply moduleIso_app_injective (exteriorPullbackIso l (quotientOnLG k).target 3)
  simp only [map_sum, Scheme.Modules.Hom.app_smul,
    pulledFiveSections_transport k (l ≫ projection k) l]
  rw [LagrangianPrimitiveSectionsPullback.primitiveSections_pullback,
    LagrangianUniversalSections.coefficients k (l ≫ projection k) l rfl]
  have hb : baseRingHom (l ≫ projection k) = ExteriorEvaluation.baseRingMap k (l ≫ projection k) :=
    LagrangianQuotientConstantTransport.scalarMap_eq_baseRingMap k (l ≫ projection k)
  rw [hb]
  exact primitiveSection_expansion k (l ≫ projection k)
    (LagrangianUniversalSections.quotientMap k l) hq j

variable [CharZero k]

/-- The actual projective triangle on every genuine affine matrix-chart test scheme. -/
theorem chart_projectiveMap_triangle [IsAffine X]
    (ι : Fin 3 ↪ Fin 6)
    (g : X ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k := 3) (n := 6) ι) (ULift.{u} ℤ))))
    (hfg : (l ≫ inclusion k) ≫ pullback.snd _ _ = g ≫ AlgebraicGeometry.Grassmannian.chart 3 6 ι)
    (hq : (LagrangianUniversalSections.quotientMap k l).app ⊤
      (freeBasisSection X 6 0) = 0) :
    projectiveMap k (l ≫ projection k) l rfl hq ≫ fixedLinearEmbedding k =
      l ≫ LagrangianPlucker.primitivePlucker k := by
  let s := fun j => pullbackGlobalSections l (determinantLine k) (primitiveSections k j)
  let t := pulledFiveSections k l
  let e := chartLineIso k l ι g hfg
  have hs := pulledPrimitiveSections_generatesStalks k l
  have ht := pulledFiveSections_generatesStalks k (l ≫ projection k) l rfl hq
  have hspanS : Ideal.span (Set.range (fun j => (show Γ(X, ⊤) from e.hom.app ⊤ (s j)))) = ⊤ := by
    have he : (fun j => (show Γ(X, ⊤) from e.hom.app ⊤ (s j))) =
        LagrangianPlucker.chartCoordinates k l ι g :=
      funext (chartLineIso_primitive k l ι g hfg)
    rw [he]
    exact LagrangianPlucker.chartCoordinates_span k l ι g hfg
  have hrel : ∀ j : Fin 14, s j = ∑ a : Fin 5,
      baseRingHom (l ≫ projection k) (embeddingFourteen k (Pi.single a 1) j) • t a :=
    pulledPrimitive_expansion k l hq
  have hspanT : Ideal.span (Set.range (fun a => (show Γ(X, ⊤) from e.hom.app ⊤ (t a)))) = ⊤ := by
    apply span_eq_top_of_expansion _ _
      (fun j a => baseRingHom (l ≫ projection k) (embeddingFourteen k (Pi.single a 1) j)) hspanS
    intro j
    have he := congrArg (fun s => e.hom.app ⊤ s) (hrel j)
    simpa only [map_sum, Scheme.Modules.Hom.app_smul, smul_eq_mul] using he
  have hP : l ≫ LagrangianPlucker.primitivePlucker k =
      Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs (l ≫ projection k) := by
    rw [primitivePlucker_eq_toProjectiveSpaceOver k]
    exact comp_toProjectiveSpaceOver_sameBase (primitiveSections k)
      (LagrangianPluckerEpimorphism.primitiveSections_generatesStalks k) l (projection k) hs
  rw [projectiveMap_eq_pulled k (l ≫ projection k) l rfl hq]
  exact (framed_triangle k (l ≫ projection k) s hs t ht e hspanS hspanT hrel).trans hP.symm

omit [CharZero k] in
/-- Every actual map to the native zero scheme gives the literal first-section relation. -/
theorem quotient_first_section_zero_comp {T : Scheme.{u}} (t : T ⟶ zeroSpace k) :
    (LagrangianUniversalSections.quotientMap k (t ≫ zeroInclusion k)).app ⊤
      (freeBasisSection T 6 0) = 0 := by
  change (LagrangianIsotropicRestriction.pulledQuotient (t ≫ zeroInclusion k)
    (quotientOnLG k).map).app ⊤ (LagrangianGrassmannian.freeVector T 0) = 0
  rw [LagrangianIsotropicRestriction.pulledQuotient_basis]
  exact (factorsThrough_iff k (t ≫ zeroInclusion k)).mpr ⟨t, rfl⟩

/-- The original zero scheme has the actual original P4/P13 triangle.
The proof uses a genuine scheme cover, not only field-valued points. -/
theorem zeroProjectiveMap_triangle :
    zeroProjectiveMap k ≫ fixedLinearEmbedding k =
      zeroInclusion k ≫ LagrangianPlucker.primitivePlucker k := by
  let C := (LagrangianPlucker.matrixCover k).pullback₁ (zeroInclusion k)
  apply C.hom_ext
  intro ι
  change Fin 3 ↪ Fin 6 at ι
  let T := C.X ι
  let t : T ⟶ zeroSpace k := C.f ι
  let h : T ⟶ (LagrangianPlucker.matrixCover k).X ι :=
    (LagrangianPlucker.matrixCover k).pullbackHom (zeroInclusion k) ι
  let l : T ⟶ space k := t ≫ zeroInclusion k
  let g := h ≫ LagrangianPlucker.matrixChartIntegral k ι
  letI := LagrangianPluckerEpimorphism.matrixCover_chart_isAffine k ι
  haveI : IsAffine T := by
    change IsAffine (pullback (zeroInclusion k) ((LagrangianPlucker.matrixCover k).f ι))
    infer_instance
  have hlt : h ≫ (LagrangianPlucker.matrixCover k).f ι = l :=
    (LagrangianPlucker.matrixCover k).pullbackHom_map (zeroInclusion k) ι
  have hfg : (l ≫ inclusion k) ≫ pullback.snd _ _ = g ≫ AlgebraicGeometry.Grassmannian.chart 3 6 ι := by
    calc
      _ = h ≫ (((LagrangianPlucker.matrixCover k).f ι ≫ inclusion k) ≫ pullback.snd _ _) := by
        rw [← hlt]
        simp only [Category.assoc]
      _ = h ≫ (LagrangianPlucker.matrixChartIntegral k ι ≫ AlgebraicGeometry.Grassmannian.chart 3 6 ι) :=
        congrArg (fun m => h ≫ m) (LagrangianPlucker.matrixChartIntegral_diagram k ι)
      _ = _ := (Category.assoc _ _ _).symm
  have hq := quotient_first_section_zero_comp k t
  have hnat : t ≫ zeroProjectiveMap k =
      projectiveMap k (l ≫ projection k) l rfl hq := by
    simpa only [zeroProjectiveMap, zeroProjection, ← Category.assoc] using
      (projectiveMap_comp k (zeroProjection k) (zeroInclusion k) rfl
        (quotient_first_section_zero k) t hq)
  change t ≫ (zeroProjectiveMap k ≫ fixedLinearEmbedding k) =
    t ≫ (zeroInclusion k ≫ LagrangianPlucker.primitivePlucker k)
  calc
    _ = (t ≫ zeroProjectiveMap k) ≫ fixedLinearEmbedding k := (Category.assoc _ _ _).symm
    _ = projectiveMap k (l ≫ projection k) l rfl hq ≫ fixedLinearEmbedding k :=
      congrArg (fun m => m ≫ fixedLinearEmbedding k) hnat
    _ = l ≫ LagrangianPlucker.primitivePlucker k := chart_projectiveMap_triangle k l ι g hfg hq
    _ = _ := Category.assoc _ _ _

/-- The actual native section-zero scheme is a closed subscheme of the
actual P4, derived from its original closed embedding in P13. -/
theorem zeroProjectiveMap_isClosedImmersion : IsClosedImmersion (zeroProjectiveMap k) := by
  letI := fixedLinearEmbedding_isClosedImmersion k
  haveI : IsClosedImmersion (zeroProjectiveMap k ≫ fixedLinearEmbedding k) := by
    rw [zeroProjectiveMap_triangle k]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (zeroProjectiveMap k) (fixedLinearEmbedding k)

end M9Native.LagrangianKernelChartTriangle
