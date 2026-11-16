module

public import M9.Basic
public import M9.Private.ProjectiveCharts
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The actual function field of complex projective matrix space

The scheme is the native `Proj` of the standard polynomial grading. Its
function field is the actual stalk at its generic point. Standard affine
coordinate charts identify this field, over its actual complex structure
map, with a fraction field of independent affine coordinates.

The chart and generic-stalk arguments adapt the minimal OAI algebraic
projective constructions recorded with source SHA256 provenance in
`audits/projective-function-field/provenance.json`. The original source
project is distributed under the Apache 2.0 license; the selected source
files contain no separate per-file copyright headers.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace M9.ProjectiveFunctionField

open CategoryTheory AlgebraicGeometry TopologicalSpace
open M9.ProjectiveGeometry

/-- Native complex projective `n`-space, with its genuine structure sheaf. -/
abbrev space (n : ℕ) : Scheme := ProjectiveSpace.projectiveSpace n

/-- The actual projective structure morphism to `Spec ℂ`. -/
abbrev projection (n : ℕ) : space n ⟶ Spec (.of ℂ) :=
  ProjectiveSpace.projectiveSpaceToBase n

/-- The zero homogeneous prime is the actual generic projective point. -/
def projectiveGenericPoint (n : ℕ) : space n where
  asHomogeneousIdeal := ⊥
  isPrime := by
    simpa only [HomogeneousIdeal.toIdeal_bot] using
      (inferInstance : (⊥ : Ideal (ProjectiveSpace.homogeneousCoordinateRing n)).IsPrime)
  not_irrelevant_le h := by
    have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem
      (ProjectiveSpace.projectiveGrading n) (by decide : 0 < 1)
      (MvPolynomial.isHomogeneous_X ℂ (Fin.last n)))
    exact MvPolynomial.X_ne_zero (Fin.last n) (Ideal.mem_bot.mp hx)

theorem projectiveGenericPoint_dense (n : ℕ) :
    closure ({projectiveGenericPoint n} : Set (space n)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (ProjectiveSpectrum.le_iff_mem_closure (ProjectiveSpace.projectiveGrading n)
    (projectiveGenericPoint n) x).mp
      (show (⊥ : HomogeneousIdeal (ProjectiveSpace.projectiveGrading n)) ≤
        x.asHomogeneousIdeal from bot_le)

instance space_irreducible (n : ℕ) : IrreducibleSpace (space n) := by
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (space n))
  rw [← projectiveGenericPoint_dense n]
  exact (isIrreducible_singleton (x := projectiveGenericPoint n)).closure

/-- Every standard coordinate open is nonempty at the actual generic point. -/
instance coordinateOpen_nonempty (n : ℕ) (i : Fin (n+1)) :
    Nonempty (ProjectiveCoordinateCover.projectiveCoordinateOpen n i) := by
  refine ⟨⟨projectiveGenericPoint n, ?_⟩⟩
  change MvPolynomial.X i ∉ (⊥ : Ideal (ProjectiveSpace.homogeneousCoordinateRing n))
  exact fun h => MvPolynomial.X_ne_zero i (Ideal.mem_bot.mp h)

/-- The actual coordinate opens are dense, rather than a separately declared
affine model of projective space. -/
theorem coordinateOpen_dense (n : ℕ) (i : Fin (n+1)) :
    Dense (ProjectiveCoordinateCover.projectiveCoordinateOpen n i : Set (space n)) := by
  intro x
  have hx : x ∈ closure ({projectiveGenericPoint n} : Set (space n)) := by
    rw [projectiveGenericPoint_dense]
    trivial
  have hp : projectiveGenericPoint n ∈ ProjectiveCoordinateCover.projectiveCoordinateOpen n i := by
    change MvPolynomial.X i ∉ (⊥ : Ideal (ProjectiveSpace.homogeneousCoordinateRing n))
    exact fun h => MvPolynomial.X_ne_zero i (Ideal.mem_bot.mp h)
  exact closure_mono (Set.singleton_subset_iff.mpr hp) hx

instance space_reduced (n : ℕ) : IsReduced (space n) := by
  let U : (space n).OpenCover := (space n).openCoverOfIsOpenCover
    (ProjectiveCoordinateCover.projectiveCoordinateOpen n)
    (by simpa only [TopologicalSpace.IsOpenCover] using
      ProjectiveCoordinateCover.iSup_projectiveCoordinateOpen n)
  have h (i : Fin (n+1)) :
      IsReduced (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).toScheme :=
    isReduced_of_isOpenImmersion (ProjectiveChart.projectiveCoordinateIsoSpec n i).hom
  let : ∀ i, IsReduced (U.X i) := h
  exact IsReduced.of_openCover _ U

instance space_integral (n : ℕ) : IsIntegral (space n) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The function field is literally the native generic stalk of `Proj`. -/
abbrev functionField (n : ℕ) := (space n).functionField

/-- Canonical scalars use pullback by the actual structure morphism followed
by the actual germ at the generic point. -/
def structureScalarMap {X : Scheme} [IrreducibleSpace X]
    (f : X ⟶ Spec (.of ℂ)) : ℂ →+* X.functionField :=
  (X.presheaf.germ ⊤ (genericPoint X) (by trivial)).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom)

instance functionField_complexAlgebra (n : ℕ) : Algebra ℂ (functionField n) :=
  (structureScalarMap (projection n)).toAlgebra

/-- Generic-stalk restriction along an actual open immersion. -/
def openImmersionFunctionFieldIso {Y X : Scheme} [IrreducibleSpace Y]
    [IrreducibleSpace X] (i : Y ⟶ X) [IsOpenImmersion i] :
    X.functionField ≅ Y.functionField :=
  X.presheaf.stalkCongr
      (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion i).symm) ≪≫
    asIso (i.stalkMap (genericPoint Y))

set_option backward.isDefEq.respectTransparency.types false in
/-- Generic-stalk restriction is the original sheaf pullback on global
functions; this is the compatibility needed for later scheme actions. -/
theorem openImmersionFunctionFieldIso_germ {Y X : Scheme} [IrreducibleSpace Y]
    [IrreducibleSpace X] (i : Y ⟶ X) [IsOpenImmersion i] :
    X.presheaf.germ ⊤ (genericPoint X) (by trivial) ≫
      (openImmersionFunctionFieldIso i).hom =
      i.appTop ≫ Y.presheaf.germ ⊤ (genericPoint Y) (by trivial) := by
  simp only [openImmersionFunctionFieldIso, Iso.trans_hom,
    TopCat.Presheaf.stalkCongr_hom, asIso_hom, ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact i.germ_stalkMap ⊤ (genericPoint Y) (by trivial)

/-- The original structure morphism's constants commute with generic-stalk
restriction, by sheaf functoriality. -/
theorem openImmersionFunctionFieldIso_scalar {Y X : Scheme} [IrreducibleSpace Y]
    [IrreducibleSpace X] (i : Y ⟶ X) [IsOpenImmersion i] (f : X ⟶ Spec (.of ℂ)) :
    (openImmersionFunctionFieldIso i).hom.hom.comp (structureScalarMap f) =
      structureScalarMap (i ≫ f) := by
  have h : f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) (by trivial) ≫
        (openImmersionFunctionFieldIso i).hom =
      (i ≫ f).appTop ≫ Y.presheaf.germ ⊤ (genericPoint Y) (by trivial) := by
    rw [openImmersionFunctionFieldIso_germ]
    simp only [Scheme.Hom.comp_appTop, Category.assoc]
  exact congrArg (fun g => g.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom) h

/-- The native affine coefficient algebra, written with an unbundled ring
argument so inference can also use it on polynomial chart rings. -/
instance affineFunctionField_ringAlgebra (R : Type) [CommRing R] [IsDomain R] :
    Algebra R (Spec (.of R)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)

instance affineFunctionField_isFractionRing (R : Type) [CommRing R] [IsDomain R] :
    IsFractionRing R (Spec (.of R)).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine (.of R)

/-- Constants on an affine scheme enter its actual generic stalk through
the native coefficient-ring algebra map. -/
theorem affine_structureScalarMap (R : Type) [CommRing R] [IsDomain R] [Algebra ℂ R] :
    structureScalarMap (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) =
      (algebraMap R (Spec (.of R)).functionField).comp (algebraMap ℂ R) := by
  change (((Scheme.ΓSpecIso (.of ℂ)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))).appTop) ≫
        (Spec (.of R)).presheaf.germ ⊤ (genericPoint (Spec (.of R))) (by trivial)).hom = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Polynomial coordinates on the genuine `i`-th projective chart. -/
abbrev chartPolynomial (n : ℕ) (i : Fin (n+1)) :=
  ProjectiveChartToPolynomial.projectiveChartPolynomial n i

abbrev chartScheme (n : ℕ) (i : Fin (n+1)) := Spec (.of (chartPolynomial n i))

/-- The actual dense affine chart immersion. -/
abbrev chartMap (n : ℕ) (i : Fin (n+1)) : chartScheme n i ⟶ space n :=
  ProjectiveChart.projectiveAffineChartMap n i

abbrev chartProjection (n : ℕ) (i : Fin (n+1)) : chartScheme n i ⟶ Spec (.of ℂ) :=
  ProjectiveChart.projectiveChartPolynomialToBase n i

instance chartFunctionField_complexAlgebra (n : ℕ) (i : Fin (n+1)) :
    Algebra ℂ (chartScheme n i).functionField :=
  (structureScalarMap (chartProjection n i)).toAlgebra

instance chartFunctionField_isScalarTower (n : ℕ) (i : Fin (n+1)) :
    IsScalarTower ℂ (chartPolynomial n i) (chartScheme n i).functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  exact affine_structureScalarMap (chartPolynomial n i)

/-- Restriction to the actual affine chart preserves the original complex
structure map on the projective generic stalk. -/
def chartFunctionFieldEquiv (n : ℕ) (i : Fin (n+1)) :
    functionField n ≃ₐ[ℂ] (chartScheme n i).functionField where
  __ := (openImmersionFunctionFieldIso (chartMap n i)).commRingCatIsoToRingEquiv
  commutes' c := by
    have h := openImmersionFunctionFieldIso_scalar (chartMap n i) (projection n)
    rw [ProjectiveChart.projectiveAffineChartMap_over] at h
    exact DFunLike.congr_fun h c

/-- The native generic stalk of the affine chart is its actual fraction ring. -/
def chartFractionEquiv (n : ℕ) (i : Fin (n+1)) :
    (chartScheme n i).functionField ≃ₐ[ℂ] FractionRing (chartPolynomial n i) :=
  (FractionRing.algEquiv (chartPolynomial n i) (chartScheme n i).functionField).symm.restrictScalars ℂ

/-- Canonical numbering of the affine ratios, omitting the normalized
homogeneous coordinate. -/
def chartCoordinatesEquiv (n : ℕ) (i : Fin (n+1)) :
    chartPolynomial n i ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  MvPolynomial.renameEquiv ℂ (finSuccAboveEquiv i).symm

def chartFractionCoordinatesEquiv (n : ℕ) (i : Fin (n+1)) :
    FractionRing (chartPolynomial n i) ≃ₐ[ℂ] FractionRing (MvPolynomial (Fin n) ℂ) :=
  IsFractionRing.algEquivOfAlgEquiv (chartCoordinatesEquiv n i)

/-- The actual native projective function field is rational of dimension `n`
over the actual structure-map scalars. The equivalence is induced by the
genuine coordinate chart and its generic-stalk restriction. -/
def functionFieldEquiv (n : ℕ) (i : Fin (n+1)) :
    functionField n ≃ₐ[ℂ] RationalField ℂ n :=
  (chartFunctionFieldEquiv n i).trans
    ((chartFractionEquiv n i).trans (chartFractionCoordinatesEquiv n i))

/-- Affine chart polynomials viewed in the actual projective generic stalk. -/
def chartPolynomialToFunctionField (n : ℕ) (i : Fin (n+1)) :
    chartPolynomial n i →+* functionField n :=
  (chartFunctionFieldEquiv n i).symm.toRingHom.comp
    (algebraMap (chartPolynomial n i) (chartScheme n i).functionField)

/-- The chart-induced field equivalence has the actual expected value on
every chart polynomial, not just on an independently declared field model. -/
theorem functionFieldEquiv_chartPolynomial (n : ℕ) (i : Fin (n+1))
    (p : chartPolynomial n i) :
    functionFieldEquiv n i (chartPolynomialToFunctionField n i p) =
      algebraMap (MvPolynomial (Fin n) ℂ) (RationalField ℂ n) (chartCoordinatesEquiv n i p) := by
  change chartFractionCoordinatesEquiv n i
    (chartFractionEquiv n i
      (chartFunctionFieldEquiv n i ((chartFunctionFieldEquiv n i).symm
        (algebraMap (chartPolynomial n i) (chartScheme n i).functionField p)))) = _
  rw [AlgEquiv.apply_symm_apply]
  have h := (FractionRing.algEquiv (chartPolynomial n i) (chartScheme n i).functionField).symm.commutes p
  change chartFractionCoordinatesEquiv n i
    ((FractionRing.algEquiv (chartPolynomial n i) (chartScheme n i).functionField).symm
      (algebraMap (chartPolynomial n i) (chartScheme n i).functionField p)) = _
  rw [h]
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap (chartCoordinatesEquiv n i) p

/-- A normalized projective coordinate ratio inside the actual generic stalk. -/
def coordinateRatio (n : ℕ) (i : Fin (n+1)) (a : Fin n) : functionField n :=
  chartPolynomialToFunctionField n i (MvPolynomial.X (finSuccAboveEquiv i a))

@[simp] theorem functionFieldEquiv_coordinateRatio (n : ℕ) (i : Fin (n+1)) (a : Fin n) :
    functionFieldEquiv n i (coordinateRatio n i a) =
      algebraMap (MvPolynomial (Fin n) ℂ) (RationalField ℂ n) (MvPolynomial.X a) := by
  rw [coordinateRatio, functionFieldEquiv_chartPolynomial]
  simp [chartCoordinatesEquiv]

/-- Scheme automorphisms over the actual complex base induce actual
generic-stalk automorphisms, ready for later projectivized matrix actions. -/
def automorphismFunctionField (n : ℕ) (f : space n ≅ space n)
    (hf : f.hom ≫ projection n = projection n) : functionField n ≃ₐ[ℂ] functionField n where
  __ := (openImmersionFunctionFieldIso f.hom).commRingCatIsoToRingEquiv
  commutes' c := by
    have h := openImmersionFunctionFieldIso_scalar f.hom (projection n)
    rw [hf] at h
    exact DFunLike.congr_fun h c

/-- Numerical indexing of the nine actual matrix positions. -/
def matrixIndexEquiv : (Fin 3 × Fin 3) ≃ Fin 9 := finProdFinEquiv

/-- The nine homogeneous coordinates are the actual matrix entries. -/
def matrixCoordinates : Matrix (Fin 3) (Fin 3) ℂ ≃ₗ[ℂ] (Fin 9 → ℂ) where
  toFun M a := M (matrixIndexEquiv.symm a).1 (matrixIndexEquiv.symm a).2
  invFun x i j := x (matrixIndexEquiv (i,j))
  left_inv M := by funext i j; simp
  right_inv x := by funext a; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `ℙ(Mat₃)` in its actual nine matrix-entry homogeneous coordinates. -/
abbrev matrixSpace : Scheme := space 8

/-- The actual generic-stalk function field of `ℙ(Mat₃)`. -/
abbrev matrixFunctionField := functionField 8

/-- The chart normalizing the last matrix entry gives eight independent
affine ratios in the genuine projective function field. -/
def matrixFunctionFieldEquiv : matrixFunctionField ≃ₐ[ℂ] RationalField ℂ 8 :=
  functionFieldEquiv 8 (Fin.last 8)

theorem matrixFunctionField_rational : RationalOfDimension ℂ matrixFunctionField 8 :=
  ⟨matrixFunctionFieldEquiv⟩

end M9.ProjectiveFunctionField
