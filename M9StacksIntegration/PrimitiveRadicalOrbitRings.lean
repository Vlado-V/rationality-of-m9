module

public import M9StacksIntegration.PrimitiveRadicalOrbitFamily
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.RingTheory.OreLocalization.Ring
import all Mathlib.Basic.Complex.Basic
import all Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# The actual integral tensor source of the radical orbit family

The three localization steps retain the original Gauss13, graph32, and
nondegenerate Gram determinant coordinates. Their tensor source is a domain
by localization of the actual polynomial tensor product.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory
open scoped Classical TensorProduct
open TensorProduct

namespace M9Native.PrimitiveRadicalOrbitRings
open M9.GraphBundleDescent
open PrimitiveRadicalOrbitFamily

abbrev gaussPolynomial := PrimitiveGaussCoordinates.polynomial ℂ
abbrev graphPolynomial := ChartRing ℂ
abbrev polynomialPair := gaussPolynomial ⊗[ℂ] graphPolynomial
abbrev graphLocalized := gaussPolynomial ⊗[ℂ] IsomChartRing ℂ
abbrev gaussGraphLocalized := gaussRing ⊗[ℂ] IsomChartRing ℂ

def polynomialEquiv : polynomialPair ≃ₐ[ℂ]
    MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ :=
  MvPolynomial.tensorEquivSum ℂ (Fin 13) ParameterIndex ℂ

instance polynomialPair_isDomain : IsDomain polynomialPair :=
  polynomialEquiv.toRingEquiv.isDomain_iff.mpr inferInstance

def graphLocalization : graphPolynomial →ₐ[ℂ] IsomChartRing ℂ :=
  IsScalarTower.toAlgHom ℂ graphPolynomial (IsomChartRing ℂ)

def gaussLocalization : gaussPolynomial →ₐ[ℂ] gaussRing :=
  IsScalarTower.toAlgHom ℂ gaussPolynomial gaussRing

def firstMap : polynomialPair →ₐ[ℂ] graphLocalized :=
  Algebra.TensorProduct.map (AlgHom.id ℂ gaussPolynomial) graphLocalization

def secondMap : graphLocalized →ₐ[ℂ] gaussGraphLocalized :=
  Algebra.TensorProduct.map gaussLocalization (AlgHom.id ℂ (IsomChartRing ℂ))

def thirdMap : gaussGraphLocalized →ₐ[ℂ] coordinateRing :=
  Algebra.TensorProduct.map (AlgHom.id ℂ gaussRing) PrimitiveRhoFiberNondegenerate.localizationMap

instance firstAlgebra : Algebra polynomialPair graphLocalized := RingHom.toAlgebra (R := polynomialPair) (S := graphLocalized) firstMap.toRingHom
instance secondAlgebra : Algebra graphLocalized gaussGraphLocalized := RingHom.toAlgebra (R := graphLocalized) (S := gaussGraphLocalized) secondMap.toRingHom
instance thirdAlgebra : Algebra gaussGraphLocalized coordinateRing := RingHom.toAlgebra (R := gaussGraphLocalized) (S := coordinateRing) thirdMap.toRingHom

instance secondSMul : SMul graphLocalized gaussGraphLocalized := secondAlgebra.toSMul
instance thirdSMul : SMul gaussGraphLocalized coordinateRing := thirdAlgebra.toSMul

instance firstTower : IsScalarTower gaussPolynomial polynomialPair graphLocalized :=
  IsScalarTower.of_algHom (R := gaussPolynomial) (A := polynomialPair) (B := graphLocalized) (Algebra.TensorProduct.map
    (AlgHom.id gaussPolynomial gaussPolynomial) graphLocalization)

instance secondTower : IsScalarTower gaussPolynomial graphLocalized gaussGraphLocalized := by
  apply IsScalarTower.of_algebraMap_eq' (R := gaussPolynomial) (S := graphLocalized) (A := gaussGraphLocalized)
  apply RingHom.ext
  intro p
  change gaussLocalization p ⊗ₜ[ℂ] (1 : IsomChartRing ℂ) =
    secondMap (p ⊗ₜ[ℂ] (1 : IsomChartRing ℂ))
  simp only [secondMap,Algebra.TensorProduct.map_tmul,map_one]

instance thirdTower : IsScalarTower gaussRing gaussGraphLocalized coordinateRing := by
  apply IsScalarTower.of_algebraMap_eq' (R := gaussRing) (S := gaussGraphLocalized) (A := coordinateRing)
  apply RingHom.ext
  intro p
  change p ⊗ₜ[ℂ] (1 : fiberRing) = thirdMap (p ⊗ₜ[ℂ] (1 : IsomChartRing ℂ))
  simp only [thirdMap,Algebra.TensorProduct.map_tmul,map_one,AlgHom.id_apply]

instance firstLocalization : IsLocalization.Away
    ((1 : gaussPolynomial) ⊗ₜ[ℂ] universalDeterminant ℂ) graphLocalized := by
  have h := IsLocalization.tensorProduct_tensorProduct_right ℂ gaussPolynomial
    (Submonoid.powers (universalDeterminant ℂ)) (IsomChartRing ℂ) (by
      apply RingHom.ext
      intro p
      change firstMap ((1 : gaussPolynomial) ⊗ₜ[ℂ] p) = 1 ⊗ₜ[ℂ] graphLocalization p
      simp only [firstMap,Algebra.TensorProduct.map_tmul,map_one])
  simpa only [Submonoid.map_powers,Algebra.TensorProduct.includeRight_apply] using h

theorem firstLocalizer_ne_zero :
    (1 : gaussPolynomial) ⊗ₜ[ℂ] universalDeterminant ℂ ≠ 0 := by
  have hi := Algebra.TensorProduct.includeRight_injective
    (A := gaussPolynomial) (B := graphPolynomial) (algebraMap ℂ gaussPolynomial).injective
  simpa only [map_zero,Algebra.TensorProduct.includeRight_apply] using
    hi.ne (universalDeterminant_ne_zero (K := ℂ))

instance graphLocalized_isDomain : IsDomain graphLocalized :=
  IsLocalization.Away.isDomain graphLocalized firstLocalizer_ne_zero

instance secondLocalization : IsLocalization.Away
    ((PrimitiveGaussCoordinates.localizer ℂ) ⊗ₜ[ℂ] (1 : IsomChartRing ℂ)) gaussGraphLocalized := by
  have h := IsLocalization.tensorProduct_tensorProduct ℂ (IsomChartRing ℂ)
    (Submonoid.powers (PrimitiveGaussCoordinates.localizer ℂ)) gaussRing (by
      apply RingHom.ext
      intro p
      change secondMap ((1 : gaussPolynomial) ⊗ₜ[ℂ] p) = 1 ⊗ₜ[ℂ] p
      simp only [secondMap,Algebra.TensorProduct.map_tmul,map_one,AlgHom.id_apply])
  simpa only [Algebra.algebraMapSubmonoid_powers,Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self,RingHom.id_apply] using h

theorem secondLocalizer_ne_zero :
    (PrimitiveGaussCoordinates.localizer ℂ) ⊗ₜ[ℂ] (1 : IsomChartRing ℂ) ≠ 0 := by
  have hi := Algebra.TensorProduct.includeLeft_injective
    (A := gaussPolynomial) (B := IsomChartRing ℂ) (S := ℂ)
    (algebraMap ℂ (IsomChartRing ℂ)).injective
  simpa only [map_zero,Algebra.TensorProduct.includeLeft_apply] using
    hi.ne (PrimitiveGaussCoordinates.localizer_ne_zero ℂ)

instance gaussGraphLocalized_isDomain : IsDomain gaussGraphLocalized :=
  IsLocalization.Away.isDomain gaussGraphLocalized secondLocalizer_ne_zero

instance thirdLocalization : IsLocalization.Away
    ((1 : gaussRing) ⊗ₜ[ℂ] PrimitiveRhoFiberNondegenerate.nondegenerateDeterminant) coordinateRing := by
  have h := IsLocalization.tensorProduct_tensorProduct_right ℂ gaussRing
    (Submonoid.powers PrimitiveRhoFiberNondegenerate.nondegenerateDeterminant) fiberRing (by
      apply RingHom.ext
      intro p
      change thirdMap ((1 : gaussRing) ⊗ₜ[ℂ] p) =
        1 ⊗ₜ[ℂ] PrimitiveRhoFiberNondegenerate.localizationMap p
      simp only [thirdMap,Algebra.TensorProduct.map_tmul,map_one])
  simpa only [Submonoid.map_powers,Algebra.TensorProduct.includeRight_apply] using h

theorem thirdLocalizer_ne_zero :
    (1 : gaussRing) ⊗ₜ[ℂ] PrimitiveRhoFiberNondegenerate.nondegenerateDeterminant ≠ 0 := by
  have hi := Algebra.TensorProduct.includeRight_injective
    (A := gaussRing) (B := IsomChartRing ℂ) (algebraMap ℂ gaussRing).injective
  simpa only [map_zero,Algebra.TensorProduct.includeRight_apply] using
    hi.ne PrimitiveRhoFiberNondegenerate.nondegenerateDeterminant_ne_zero

/-- Integrality is derived from the original independent coordinate blocks and all three
actual localization maps, rather than posited for the orbit-family source. -/
instance coordinateRing_isDomain : IsDomain coordinateRing :=
  IsLocalization.Away.isDomain coordinateRing thirdLocalizer_ne_zero

instance source_isIntegral : IsIntegral source := inferInstanceAs (IsIntegral (Spec (.of coordinateRing)))

abbrev coefficientMap := @algebraMap ℂ coordinateRing
  (inferInstance : CommSemiring ℂ) (inferInstance : Semiring coordinateRing)
  (inferInstance : Algebra ℂ coordinateRing)
abbrev coordinateFunctionFieldMap := @algebraMap coordinateRing source.functionField
  (inferInstance : CommSemiring coordinateRing) (inferInstance : Semiring source.functionField)
  (inferInstance : Algebra coordinateRing source.functionField)
abbrev coordinateFractionMap := @algebraMap coordinateRing (FractionRing coordinateRing)
  (inferInstance : CommSemiring coordinateRing) (inferInstance : Semiring (FractionRing coordinateRing))
  (inferInstance : Algebra coordinateRing (FractionRing coordinateRing))
abbrev coefficientFractionMap := algebraMap ℂ (FractionRing coordinateRing)

/-- The scalar inclusion in the native generic stalk is its actual structure morphism. -/
instance functionFieldComplexAlgebra : Algebra ℂ source.functionField :=
  RingHom.toAlgebra (R := ℂ) (S := source.functionField)
    (GrassmannianCharts.structureScalarMap ℂ projection)

def nativeFractionEquiv := (FractionRing.algEquiv coordinateRing source.functionField).symm

/-- The actual generic-stalk fraction equivalence with its actual structure-morphism scalars. -/
def sourceFractionEquiv : source.functionField ≃ₐ[ℂ] FractionRing coordinateRing := by
  let e := nativeFractionEquiv
  refine { __ := e.toRingEquiv, commutes' := fun c => ?_ }
  have hc : algebraMap ℂ source.functionField c =
      coordinateFunctionFieldMap (coefficientMap c) := by
    change GrassmannianCharts.structureScalarMap ℂ projection c = _
    unfold projection
    exact DFunLike.congr_fun (GrassmannianCharts.affine_structureScalarMap ℂ coordinateRing) c
  change e (algebraMap ℂ source.functionField c) = _
  rw [hc]
  calc
    e (coordinateFunctionFieldMap (coefficientMap c)) = coordinateFractionMap (coefficientMap c) :=
      e.commutes (coefficientMap c)
    _ = algebraMap ℂ (FractionRing coordinateRing) c :=
      (IsScalarTower.algebraMap_apply ℂ coordinateRing (FractionRing coordinateRing) c).symm

theorem sourceFractionEquiv_coordinate (r : coordinateRing) :
    sourceFractionEquiv (coordinateFunctionFieldMap r) = coordinateFractionMap r := by
  change nativeFractionEquiv (coordinateFunctionFieldMap r) = coordinateFractionMap r
  exact nativeFractionEquiv.commutes r

section FractionLocalization

variable {K R B : Type*} [Field K] [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [Algebra K R] [Algebra K B] [Algebra R B] [IsScalarTower K R B]
  (q : R) [IsLocalization.Away q B] (hq : q ≠ 0)

/-- The native fraction equivalence induced by an actual localization,
together with its actual original-coordinate formula. -/
def awayFractionComparison :
    {e : FractionRing B ≃ₐ[K] FractionRing R // ∀ r : R,
      e (algebraMap B (FractionRing B) (algebraMap R B r)) =
        algebraMap R (FractionRing R) r} := by
  have hu : IsUnit (algebraMap R (FractionRing R) q) := by
    apply isUnit_iff_ne_zero.mpr
    simpa only [map_zero] using (IsFractionRing.injective R (FractionRing R)).ne hq
  let f : B →ₐ[K] FractionRing R := IsLocalization.Away.liftAlgHom q
    (f := IsScalarTower.toAlgHom K R (FractionRing R)) hu
  letI : Algebra B (FractionRing R) :=
    RingHom.toAlgebra (R := B) (S := FractionRing R) f.toRingHom
  letI : IsScalarTower K B (FractionRing R) :=
    IsScalarTower.of_algHom (R := K) (A := B) (B := FractionRing R) f
  letI : IsScalarTower R B (FractionRing R) := by
    apply IsScalarTower.of_algebraMap_eq' (R := R) (S := B) (A := FractionRing R)
    apply RingHom.ext
    intro r
    change algebraMap R (FractionRing R) r = f (algebraMap R B r)
    exact (IsLocalization.Away.lift_eq (S := B) (g := algebraMap R (FractionRing R)) q hu r).symm
  letI : IsFractionRing B (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers q) B (FractionRing R)
  refine ⟨(FractionRing.algEquiv B (FractionRing R)).restrictScalars K,fun r => ?_⟩
  change (FractionRing.algEquiv B (FractionRing R))
    (algebraMap B (FractionRing B) (algebraMap R B r)) = _
  rw [(FractionRing.algEquiv B (FractionRing R)).commutes]
  exact IsLocalization.Away.lift_eq (S := B) (g := algebraMap R (FractionRing R)) q hu r

end FractionLocalization

instance firstScalarTower : IsScalarTower ℂ polynomialPair graphLocalized :=
  IsScalarTower.of_algHom (R := ℂ) (A := polynomialPair) (B := graphLocalized) firstMap
instance secondScalarTower : IsScalarTower ℂ graphLocalized gaussGraphLocalized :=
  IsScalarTower.of_algHom (R := ℂ) (A := graphLocalized) (B := gaussGraphLocalized) secondMap
instance thirdScalarTower : IsScalarTower ℂ gaussGraphLocalized coordinateRing :=
  IsScalarTower.of_algHom (R := ℂ) (A := gaussGraphLocalized) (B := coordinateRing) thirdMap

def firstFractionComparison := awayFractionComparison (K := ℂ) (B := graphLocalized)
  ((1 : gaussPolynomial) ⊗ₜ[ℂ] universalDeterminant ℂ) firstLocalizer_ne_zero

def secondFractionComparison := awayFractionComparison (K := ℂ) (B := gaussGraphLocalized)
  ((PrimitiveGaussCoordinates.localizer ℂ) ⊗ₜ[ℂ] (1 : IsomChartRing ℂ)) secondLocalizer_ne_zero

def thirdFractionComparison := awayFractionComparison (K := ℂ) (B := coordinateRing)
  ((1 : gaussRing) ⊗ₜ[ℂ] PrimitiveRhoFiberNondegenerate.nondegenerateDeterminant)
  thirdLocalizer_ne_zero

/-- The actual three localization-induced fraction maps, preserving the two original blocks. -/
def coordinateFractionEquiv : FractionRing coordinateRing ≃ₐ[ℂ] FractionRing polynomialPair :=
  (thirdFractionComparison.val.trans secondFractionComparison.val).trans firstFractionComparison.val

/-- The source is rational in the original thirteen-plus-thirty-two independent variables. -/
def sourceRationalEquiv : FractionRing coordinateRing ≃ₐ[ℂ]
    FractionRing (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ) :=
  coordinateFractionEquiv.trans (IsFractionRing.algEquivOfAlgEquiv polynomialEquiv)

def polynomialToCoordinateMap : polynomialPair →ₐ[ℂ] coordinateRing :=
  thirdMap.comp (secondMap.comp firstMap)

theorem coordinateFractionEquiv_coordinate (p : polynomialPair) :
    coordinateFractionEquiv
      (coordinateFractionMap (polynomialToCoordinateMap p)) =
      algebraMap polynomialPair (FractionRing polynomialPair) p := by
  have h3 := thirdFractionComparison.property (secondMap (firstMap p))
  have h2 := secondFractionComparison.property (firstMap p)
  have h1 := firstFractionComparison.property p
  change thirdFractionComparison.val
    (coordinateFractionMap (thirdMap (secondMap (firstMap p)))) = _ at h3
  change secondFractionComparison.val
    (algebraMap gaussGraphLocalized (FractionRing gaussGraphLocalized) (secondMap (firstMap p))) = _ at h2
  change firstFractionComparison.val
    (algebraMap graphLocalized (FractionRing graphLocalized) (firstMap p)) = _ at h1
  change firstFractionComparison.val (secondFractionComparison.val (thirdFractionComparison.val
    (coordinateFractionMap (thirdMap (secondMap (firstMap p)))))) = _
  rw [h3,h2,h1]

theorem sourceRationalEquiv_coordinate (p : polynomialPair) :
    sourceRationalEquiv
      (coordinateFractionMap (polynomialToCoordinateMap p)) =
      algebraMap (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ)
        (FractionRing (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ)) (polynomialEquiv p) := by
  change IsFractionRing.algEquivOfAlgEquiv polynomialEquiv
    (coordinateFractionEquiv _) = _
  rw [coordinateFractionEquiv_coordinate,IsFractionRing.algEquivOfAlgEquiv_algebraMap]


def gaussInclusion : gaussRing →ₐ[ℂ] coordinateRing := Algebra.TensorProduct.includeLeft

def graphInclusion : graphPolynomial →ₐ[ℂ] coordinateRing :=
  (Algebra.TensorProduct.includeRight : fiberRing →ₐ[ℂ] coordinateRing).comp
    (PrimitiveRhoFiberNondegenerate.localizationMap.comp graphLocalization)

theorem gaussInclusion_injective : Function.Injective gaussInclusion :=
  Algebra.TensorProduct.includeLeft_injective (A := gaussRing) (B := fiberRing) (S := ℂ)
    (algebraMap ℂ fiberRing).injective

theorem polynomialToCoordinateMap_gauss (p : gaussPolynomial) :
    polynomialToCoordinateMap (p ⊗ₜ[ℂ] (1 : graphPolynomial)) =
      gaussInclusion (gaussLocalization p) := by
  simp only [polynomialToCoordinateMap,AlgHom.comp_apply,firstMap,secondMap,thirdMap,
    Algebra.TensorProduct.map_tmul,map_one,AlgHom.id_apply,gaussInclusion,
    Algebra.TensorProduct.includeLeft_apply]

theorem polynomialToCoordinateMap_graph (p : graphPolynomial) :
    polynomialToCoordinateMap ((1 : gaussPolynomial) ⊗ₜ[ℂ] p) = graphInclusion p := by
  simp only [polynomialToCoordinateMap,AlgHom.comp_apply,firstMap,secondMap,thirdMap,
    Algebra.TensorProduct.map_tmul,map_one,AlgHom.id_apply,graphInclusion,
    Algebra.TensorProduct.includeRight_apply]

/-- The original Gauss variables are the left thirteen polynomial variables. -/
theorem sourceRationalEquiv_gauss_X (i : Fin 13) :
    sourceRationalEquiv (coordinateFractionMap (gaussInclusion (gaussLocalization (MvPolynomial.X i)))) =
      algebraMap (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ)
        (FractionRing (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ)) (MvPolynomial.X (Sum.inl i)) := by
  have h := sourceRationalEquiv_coordinate
    ((MvPolynomial.X i : gaussPolynomial) ⊗ₜ[ℂ] (1 : graphPolynomial))
  rw [polynomialToCoordinateMap_gauss] at h
  simpa only [polynomialEquiv,MvPolynomial.tensorEquivSum_X_tmul_one] using h

/-- The original graph variables are the right thirty-two polynomial variables. -/
theorem sourceRationalEquiv_graph_X (i : ParameterIndex) :
    sourceRationalEquiv (coordinateFractionMap (graphInclusion (MvPolynomial.X i))) =
      algebraMap (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ)
        (FractionRing (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ)) (MvPolynomial.X (Sum.inr i)) := by
  have h := sourceRationalEquiv_coordinate
    ((1 : gaussPolynomial) ⊗ₜ[ℂ] (MvPolynomial.X i : graphPolynomial))
  rw [polynomialToCoordinateMap_graph] at h
  simpa only [polynomialEquiv,MvPolynomial.tensorEquivSum_one_tmul_X] using h

def gaussToFraction : gaussRing →ₐ[ℂ] FractionRing coordinateRing :=
  (IsScalarTower.toAlgHom ℂ coordinateRing (FractionRing coordinateRing)).comp gaussInclusion

theorem gaussToFraction_injective : Function.Injective gaussToFraction :=
  (IsFractionRing.injective coordinateRing (FractionRing coordinateRing)).comp gaussInclusion_injective

/-- The actual Gauss-ring inclusion induces the actual fraction-field embedding. -/
def gaussFieldEmbedding : FractionRing gaussRing →ₐ[ℂ] FractionRing coordinateRing :=
  IsFractionRing.liftAlgHom (g := gaussToFraction) gaussToFraction_injective

@[simp] theorem gaussFieldEmbedding_coordinate (a : gaussRing) :
    gaussFieldEmbedding (algebraMap gaussRing (FractionRing gaussRing) a) =
      coordinateFractionMap (gaussInclusion a) :=
  IsFractionRing.lift_algebraMap (g := gaussToFraction.toRingHom) gaussToFraction_injective a

/-- The actual source generic stalk, with its actual structure scalars, is rational in these coordinates. -/
def sourceFieldRationalEquiv : source.functionField ≃ₐ[ℂ]
    FractionRing (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ) :=
  sourceFractionEquiv.trans sourceRationalEquiv

theorem sourceFieldRationalEquiv_coordinate (p : polynomialPair) :
    sourceFieldRationalEquiv (coordinateFunctionFieldMap (polynomialToCoordinateMap p)) =
      algebraMap (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ)
        (FractionRing (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ)) (polynomialEquiv p) := by
  simp only [sourceFieldRationalEquiv,AlgEquiv.trans_apply,
    sourceFractionEquiv_coordinate,sourceRationalEquiv_coordinate]

theorem rationalVariableCount : Fintype.card (Fin 13 ⊕ ParameterIndex) = 45 := by decide

def rationalVariableEquiv : (Fin 13 ⊕ ParameterIndex) ≃ Fin 45 :=
  (Fintype.equivFin _).trans (finCongr rationalVariableCount)

/-- An optional Fin45 presentation; the Sum-indexed equivalence above retains the original blocks. -/
def sourceRationalFin45Equiv : FractionRing coordinateRing ≃ₐ[ℂ] M9.RationalField ℂ 45 :=
  sourceRationalEquiv.trans
    (IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv ℂ rationalVariableEquiv))


def gaussFractionComparison := awayFractionComparison (K := ℂ) (B := gaussRing)
  (PrimitiveGaussCoordinates.localizer ℂ) (PrimitiveGaussCoordinates.localizer_ne_zero ℂ)

/-- The canonical thirteen-variable parameter field enters through the original Gauss block. -/
def parameterFieldEmbedding : PrimitiveGaussCoordinates.rationalField ℂ →ₐ[ℂ]
    FractionRing coordinateRing :=
  gaussFieldEmbedding.comp gaussFractionComparison.val.symm.toAlgHom

theorem parameterFieldEmbedding_coordinate (p : gaussPolynomial) :
    parameterFieldEmbedding
      (algebraMap gaussPolynomial (PrimitiveGaussCoordinates.rationalField ℂ) p) =
      coordinateFractionMap (gaussInclusion (gaussLocalization p)) := by
  have h := gaussFractionComparison.property p
  have hi : gaussFractionComparison.val.symm
      (algebraMap gaussPolynomial (PrimitiveGaussCoordinates.rationalField ℂ) p) =
      algebraMap gaussRing (FractionRing gaussRing) (gaussLocalization p) := by
    apply gaussFractionComparison.val.injective
    rw [gaussFractionComparison.val.apply_symm_apply]
    exact h.symm
  change gaussFieldEmbedding (gaussFractionComparison.val.symm
    (algebraMap gaussPolynomial (PrimitiveGaussCoordinates.rationalField ℂ) p)) = _
  rw [hi,gaussFieldEmbedding_coordinate]

theorem parameterFieldEmbedding_X (i : Fin 13) :
    sourceRationalEquiv (parameterFieldEmbedding
      (algebraMap gaussPolynomial (PrimitiveGaussCoordinates.rationalField ℂ) (MvPolynomial.X i))) =
      algebraMap (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ)
        (FractionRing (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ)) (MvPolynomial.X (Sum.inl i)) := by
  rw [parameterFieldEmbedding_coordinate,sourceRationalEquiv_gauss_X]

def sourceFieldRationalFin45Equiv : source.functionField ≃ₐ[ℂ] M9.RationalField ℂ 45 :=
  sourceFractionEquiv.trans sourceRationalFin45Equiv

end M9Native.PrimitiveRadicalOrbitRings
