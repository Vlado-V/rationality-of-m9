module

public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.ChartMatrix
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Algebra.MvPolynomial.Equiv
public import M9StacksIntegration.GrassmannianMatrix
public import M9StacksIntegration.GrassmannianFunctionField
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Genuine matrix charts and function fields of the native free Grassmannian

The target is the pinned Stacks representing scheme.  Its coordinate charts
are actual open immersions obtained from the quotient-functor universal
property, rather than a chosen rational function field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.GrassmannianCharts

open AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K] (r n : ℕ)

/-- The pinned Stacks representing scheme, base changed to the actual field. -/
abbrev space : Scheme.{u} := schemeOverRing r n (.of K)

abbrev projection : space K r n ⟶ Spec (.of K) := pullback.fst _ _
abbrev toIntegral : space K r n ⟶ scheme.{u} r n := pullback.snd _ _

/-- The genuine matrix-chart domain obtained by base change from the integral chart. -/
abbrev chartSpace (ι : Fin (n-r) ↪ Fin n) : Scheme.{u} :=
  AffineSpace (ChartIndex.{u} ι) (Spec (.of K))

/-- Base change of the universal quotient chart into the native Grassmannian. -/
def chartOver (ι : Fin (n-r) ↪ Fin n) : chartSpace K r n ι ⟶ space K r n :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ chart r n ι) (terminal.hom_ext _ _)

@[reassoc (attr := simp)] theorem chartOver_projection (ι : Fin (n-r) ↪ Fin n) :
    chartOver K r n ι ≫ projection K r n = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem chartOver_toIntegral (ι : Fin (n-r) ↪ Fin n) :
    chartOver K r n ι ≫ toIntegral K r n = pullback.snd _ _ ≫ chart r n ι :=
  pullback.lift_snd _ _ _

/-- The chart is the actual base-change square of the native integral chart. -/
theorem chartOver_isPullback (ι : Fin (n-r) ↪ Fin n) :
    IsPullback (chartOver K r n ι) (pullback.snd _ _) (toIntegral K r n) (chart r n ι) := by
  apply IsPullback.of_right
    (h₁₂ := projection K r n) (h₂₂ := terminal.from (scheme.{u} r n))
  · simpa only [chartOver_projection,terminal.comp_from] using
      (IsPullback.of_hasPullback (terminal.from (Spec (.of K)))
        (terminal.from (Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))))))
  · exact chartOver_toIntegral K r n ι
  · exact IsPullback.of_hasPullback _ _

instance chartOver_isOpenImmersion (ι : Fin (n-r) ↪ Fin n) :
    IsOpenImmersion (chartOver K r n ι) :=
  MorphismProperty.of_isPullback (chartOver_isPullback K r n ι).flip inferInstance

/-- The actual quotient on the base-changed chart has the normalized matrix
with identity pivot columns and independent remaining coordinates. -/
theorem chartQuotient_matrix (ι : Fin (n-r) ↪ Fin n) :
    Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap r n ι
      (AffineSpace.toSpecMvPoly (ChartIndex.{u} ι) (Spec (.of K)))) =
      chartMatrix ι (AffineSpace.coord (Spec (.of K))) :=
  toMatrix_chartQuotientMap ι _

/-- All points of the native Grassmannian are in genuine matrix charts. -/
theorem charts_cover (x : space K r n) :
    ∃ ι : Fin (n-r) ↪ Fin n, x ∈ Set.range (chartOver K r n ι) := by
  obtain ⟨ι,hι⟩ := exists_mem_range_chart r n (toIntegral K r n x)
  have heq := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (chartOver_isPullback K r n ι).flip (⊤ : (Spec (.of
      (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ)))).Opens)
  refine ⟨ι,?_⟩
  have hh : x ∈ (toIntegral K r n) ⁻¹ᵁ (chart r n ι) ''ᵁ ⊤ := by
    change (toIntegral K r n) x ∈ (chart r n ι) ''ᵁ ⊤
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact Scheme.Hom.mem_opensRange.mpr hι
  rw [← heq] at hh
  rw [Scheme.Hom.preimage_top,Scheme.Hom.image_top_eq_opensRange] at hh
  exact Scheme.Hom.mem_opensRange.mp hh

/-- The chart's index set has the expected size, proved from the actual complement. -/
def chartIndexEquiv (ι : Fin (n-r) ↪ Fin n) : ChartIndex.{u} ι ≃ Fin (r*(n-r)) := by
  classical
  apply Fintype.equivFinOfCardEq
  change Fintype.card (ULift.{u} ({j : Fin n // j ∉ Set.range ι} × Fin (n-r))) = _
  rw [Fintype.card_ulift,Fintype.card_prod,Fintype.card_subtype_compl,
    Fintype.card_fin,Set.card_range_of_injective ι.injective,Fintype.card_fin]
  rcases le_total r n with h | h
  · rw [Nat.sub_sub_self h]
  · rw [Nat.sub_eq_zero_of_le h,Nat.mul_zero,Nat.mul_zero]

/-- The actual chart coordinate ring, rather than a definition of the Grassmannian's field. -/
abbrev chartPolynomial (ι : Fin (n-r) ↪ Fin n) := MvPolynomial (ChartIndex.{u} ι) K

def chartSpecMap (ι : Fin (n-r) ↪ Fin n) :
    Spec (.of (chartPolynomial K r n ι)) ⟶ space K r n :=
  (AffineSpace.SpecIso (ChartIndex.{u} ι) (.of K)).inv ≫ chartOver K r n ι

instance chartSpecMap_isOpenImmersion (ι : Fin (n-r) ↪ Fin n) :
    IsOpenImmersion (chartSpecMap K r n ι) := inferInstanceAs
      (IsOpenImmersion ((AffineSpace.SpecIso (ChartIndex.{u} ι) (.of K)).inv ≫ chartOver K r n ι))

@[reassoc (attr := simp)] theorem chartSpecMap_projection (ι : Fin (n-r) ↪ Fin n) :
    chartSpecMap K r n ι ≫ projection K r n =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ChartIndex.{u} ι) (R := K))) := by
  rw [chartSpecMap,Category.assoc,chartOver_projection]
  exact AffineSpace.SpecIso_inv_over (.of K)

/-- Coordinates of a normalized matrix are literal global sections on `Spec K`. -/
def matrixPoint (κ : Fin (n-r) ↪ Fin n) (E : Matrix (Fin (n-r)) (Fin n) K) :
    Spec (.of K) ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} κ) (ULift.{u} ℤ))) :=
  (AffineSpace.toSpecMvPolyIntEquiv (ChartIndex.{u} κ)).symm
    (fun a => (Scheme.ΓSpecIso (.of K)).inv (E a.down.2 a.down.1.val))

theorem matrixPoint_chartMatrix (κ : Fin (n-r) ↪ Fin n)
    (E : Matrix (Fin (n-r)) (Fin n) K) (hE : E.submatrix id κ = 1) :
    chartMatrix κ (AffineSpace.toSpecMvPolyIntEquiv _ (matrixPoint K r n κ E)) =
      E.map (Scheme.ΓSpecIso (.of K)).inv.hom := by
  classical
  ext i j
  by_cases hj : j ∈ Set.range κ
  · obtain ⟨j',rfl⟩ := hj
    rw [chartMatrix_apply_self]
    have hh := congrFun (congrFun hE i) j'
    change E i (κ j') = (1 : Matrix (Fin (n-r)) (Fin (n-r)) K) i j' at hh
    simp only [Matrix.map_apply,hh,Matrix.one_apply]
    split_ifs <;> simp
  · rw [chartMatrix_apply_of_notMem κ _ i hj]
    simp only [matrixPoint,Equiv.apply_symm_apply,Matrix.map_apply]

/-- The same actual field-valued quotient lies in every native integral chart. -/
theorem exists_common_integral_chart_point [Infinite K] (κ : Fin (n-r) ↪ Fin n) :
    ∃ p : Spec (.of K) ⟶ scheme.{u} r n,
      ∀ ι : Fin (n-r) ↪ Fin n,
        ∃ g : Spec (.of K) ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))),
          g ≫ chart r n ι = p := by
  let E := normalizedMatrix K r n κ
  let h := matrixPoint K r n κ E
  refine ⟨h ≫ chart r n κ,fun ι => ?_⟩
  apply exists_comp_chart_eq_of_isUnit_det h
  rw [matrixPoint_chartMatrix K r n κ E (normalizedMatrix_pivots K r n κ)]
  have hunit : IsUnit (Matrix.det (E.submatrix id ι)) :=
    isUnit_iff_ne_zero.mpr (normalizedMatrix_det_ne_zero K r n κ ι)
  have hh := hunit.map (Scheme.ΓSpecIso (.of K)).inv.hom
  simpa only [RingHom.map_det,RingHom.mapMatrix_apply,← Matrix.submatrix_map] using hh

/-- A pivot embedding exists for every free Grassmannian in the subspace convention. -/
def standardEmbedding : Fin (n-r) ↪ Fin n := Fin.castLEEmb (Nat.sub_le n r)

/-- A point over an auxiliary rational-function field lies in every chart.
This works over finite as well as infinite base fields. -/
theorem exists_common_chart_point :
    ∃ x : space K r n, ∀ ι : Fin (n-r) ↪ Fin n, x ∈ Set.range (chartOver K r n ι) := by
  let L := FractionRing (Polynomial K)
  let _ : Infinite L := Infinite.of_injective (algebraMap (Polynomial K) L)
    (IsFractionRing.injective (Polynomial K) L)
  obtain ⟨p,hp⟩ := exists_common_integral_chart_point L r n (standardEmbedding r n)
  let b : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom ((algebraMap (Polynomial K) L).comp Polynomial.C))
  let pK : Spec (.of L) ⟶ space K r n :=
    pullback.lift b p (terminal.hom_ext _ _)
  let η := genericPoint (Spec (.of L))
  refine ⟨pK η,fun ι => ?_⟩
  obtain ⟨g,hg⟩ := hp ι
  let gK : Spec (.of L) ⟶ chartSpace K r n ι :=
    pullback.lift b g (terminal.hom_ext _ _)
  have hfac : gK ≫ chartOver K r n ι = pK := by
    apply pullback.hom_ext
    · rw [Category.assoc,chartOver_projection]
      simp only [gK,pK,pullback.lift_fst]
    · rw [Category.assoc,chartOver_toIntegral]
      simp only [gK,pK,pullback.lift_snd_assoc,pullback.lift_snd,hg]
  exact ⟨gK η,congrArg (fun f : Spec (.of L) ⟶ space K r n => f η) hfac⟩

/-- The integral representing scheme's open-cover property survives actual base change. -/
def matrixCover : (space K r n).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (n-r) ↪ Fin n)
    (fun ι => chartSpace K r n ι) (chartOver K r n)
    (fun x => by obtain ⟨ι,y,hy⟩ := charts_cover K r n x; exact ⟨ι,y,hy⟩)

instance space_isReduced : IsReduced (space K r n) := by
  let _ : ∀ i : (matrixCover K r n).I₀, IsReduced ((matrixCover K r n).X i) := fun i => by
    change IsReduced (chartSpace K r n i)
    infer_instance
  exact IsReduced.of_openCover (space K r n) (matrixCover K r n)

/-- Irreducibility is proved from the actual affine cover and a common matrix point. -/
instance space_irreducible : IrreducibleSpace (space K r n) := by
  obtain ⟨x,hx⟩ := exists_common_chart_point K r n
  have hopen (ι : Fin (n-r) ↪ Fin n) : IsOpen (Set.range (chartOver K r n ι)) :=
    (chartOver K r n ι).isOpenEmbedding.isOpen_range
  have hirr (ι : Fin (n-r) ↪ Fin n) : IsIrreducible (Set.range (chartOver K r n ι)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (chartSpace K r n ι)).image
        (chartOver K r n ι) (chartOver K r n ι).continuous.continuousOn
  have hpre : PreirreducibleSpace (space K r n) :=
    PreirreducibleSpace.of_forall_nonempty_inter (fun {U V} hU hV hUne hVne => by
      obtain ⟨u,hu⟩ := hUne
      obtain ⟨v,hv⟩ := hVne
      obtain ⟨ι,huι⟩ := charts_cover K r n u
      obtain ⟨κ,hvκ⟩ := charts_cover K r n v
      obtain ⟨z,_,hzU,hzκ⟩ := (hirr ι).2 U (Set.range (chartOver K r n κ)) hU (hopen κ)
        ⟨u,huι,hu⟩ ⟨x,hx ι,hx κ⟩
      obtain ⟨w,_,hwU,hwV⟩ := (hirr κ).2 U V hU hV ⟨z,hzκ,hzU⟩ ⟨v,hvκ,hv⟩
      exact ⟨w,hwU,hwV⟩)
  exact { toPreirreducibleSpace := hpre, toNonempty := ⟨x⟩ }

instance space_isIntegral : IsIntegral (space K r n) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- Each actual matrix chart is dense in the native Grassmannian. -/
theorem chartOver_dense (ι : Fin (n-r) ↪ Fin n) :
    DenseRange (chartOver K r n ι) :=
  (chartOver K r n ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

theorem chartSpecMap_dense (ι : Fin (n-r) ↪ Fin n) :
    DenseRange (chartSpecMap K r n ι) :=
  (chartSpecMap K r n ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

instance functionField_algebra : Algebra K (space K r n).functionField :=
  (structureScalarMap K (projection K r n)).toAlgebra

/-- The function field of the native representing Grassmannian is the field
of rational functions in exactly `r(n-r)` independent variables over `K`. -/
def rationalFunctionFieldEquiv :
    (space K r n).functionField ≃ₐ[K] FractionRing (MvPolynomial (Fin (r*(n-r))) K) := by
  let ι := standardEmbedding r n
  let e₁ := (openImmersionFunctionFieldIso (chartSpecMap K r n ι)).commRingCatIsoToRingEquiv
  let e₂ := (FractionRing.algEquiv (chartPolynomial K r n ι)
    (Spec (.of (chartPolynomial K r n ι))).functionField).symm
  let e₃ : FractionRing (chartPolynomial K r n ι) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin (r*(n-r))) K) :=
    IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K (chartIndexEquiv r n ι))
  refine { __ := e₁.trans (e₂.toRingEquiv.trans e₃.toRingEquiv), commutes' := fun c => ?_ }
  have h₁ : e₁ (algebraMap K (space K r n).functionField c) =
      algebraMap (chartPolynomial K r n ι) (Spec (.of (chartPolynomial K r n ι))).functionField
        (MvPolynomial.C c) := by
    have h := openImmersionFunctionFieldIso_scalar K (chartSpecMap K r n ι) (projection K r n)
    rw [chartSpecMap_projection] at h
    have hs := affine_structureScalarMap K (chartPolynomial K r n ι)
    change structureScalarMap K (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C (σ := ChartIndex.{u} ι) (R := K)))) =
        (algebraMap (chartPolynomial K r n ι) (Spec (.of (chartPolynomial K r n ι))).functionField).comp
          MvPolynomial.C at hs
    rw [hs] at h
    exact DFunLike.congr_fun h c
  change e₃ (e₂ (e₁ (algebraMap K (space K r n).functionField c))) = _
  rw [h₁,e₂.commutes]
  exact e₃.commutes c

def grNineFourteenFunctionFieldEquiv :
    (space K 9 14).functionField ≃ₐ[K] FractionRing (MvPolynomial (Fin 45) K) :=
  rationalFunctionFieldEquiv K 9 14

def grFourTwelveFunctionFieldEquiv :
    (space K 4 12).functionField ≃ₐ[K] FractionRing (MvPolynomial (Fin 32) K) :=
  rationalFunctionFieldEquiv K 4 12

def grFourSixFunctionFieldEquiv :
    (space K 4 6).functionField ≃ₐ[K] FractionRing (MvPolynomial (Fin 8) K) :=
  rationalFunctionFieldEquiv K 4 6

end M9Native.GrassmannianCharts
