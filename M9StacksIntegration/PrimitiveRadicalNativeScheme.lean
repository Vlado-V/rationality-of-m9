module

public import M9StacksIntegration.RadicalGrassmannianChart
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.Gluing
import all StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme

/-!
# The native radical chart's actual universal primitive plane

The native chart quotient is classified explicitly, and its actual kernel
is identified over every complex coefficient ring with the original
scalar-extended primitive exterior space, using the original coordinate basis.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical TensorProduct Matrix

namespace M9Native.PrimitiveRadicalNativeScheme
open Module AlgebraicGeometry.Grassmannian MvPolynomial
open M9.RadicalMap M9.PrimitiveRadicalScheme
open RadicalGrassmannianChart

local instance primitiveGroup : AddCommGroup (M9.ExteriorPrimitive.Primitive ℂ) :=
  { (M9.ExteriorPrimitive.Primitive ℂ).addCommGroup with
    toAddCommMonoid := (M9.ExteriorPrimitive.Primitive ℂ).addCommMonoid }

abbrev domain := Spec (.of parameterRing)

def integralChartPoint : domain ⟶
    Spec (.of (MvPolynomial NativeIndex (ULift ℤ))) :=
  Spec.map (CommRingCat.ofHom coordinateRingEquiv.toRingHom) ≫
    (AffineSpace.SpecIso NativeIndex (.of ℂ)).inv ≫ AffineSpace.toSpecMvPoly _ (Spec (.of ℂ))

theorem integralChartPoint_coordinates (a : NativeIndex) :
    AffineSpace.toSpecMvPolyIntEquiv _ integralChartPoint a =
      (Scheme.ΓSpecIso (.of parameterRing)).inv (coordinateRingEquiv (X a)) := by
  rw [integralChartPoint,AffineSpace.toSpecMvPolyIntEquiv_comp,
    AffineSpace.toSpecMvPolyIntEquiv_comp,← AffineSpace.coord,AffineSpace.SpecIso_inv_appTop_coord]
  rw [← CommRingCat.comp_apply,← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem chart_toIntegral : RadicalGrassmannianChart.chart ≫ GrassmannianCharts.toIntegral ℂ 9 14 =
    integralChartPoint ≫ Grassmannian.chart 9 14 pivot := by
  simp only [RadicalGrassmannianChart.chart,GrassmannianCharts.chartSpecMap,Category.assoc,
    GrassmannianCharts.chartOver_toIntegral,integralChartPoint,AffineSpace.toSpecMvPoly]

def quotient : Stacks.FreeSheafMatrix.F domain 14 ⟶ Stacks.FreeSheafMatrix.F domain 5 :=
  chartQuotientMap 9 14 pivot integralChartPoint

def sectionMap : Stacks.FreeSheafMatrix.F domain 5 ⟶ Stacks.FreeSheafMatrix.F domain 14 :=
  SheafOfModules.freeMap (fun i : ULift (Fin 5) => ULift.up (pivot i.down))

theorem sectionMap_quotient : sectionMap ≫ quotient = 𝟙 _ := by
  apply (SheafOfModules.freeHomEquiv (Stacks.FreeSheafMatrix.F domain 5)).injective
  funext i
  apply (Stacks.FreeSheafMatrix.F domain 5).unitHomEquiv.symm.injective
  rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
    SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  simpa only [sectionMap,quotient,Category.assoc,SheafOfModules.ιFree_freeMap_assoc,
    Category.comp_id] using ιFree_comp_chartQuotientMap 9 14 pivot integralChartPoint i.down

theorem quotient_epi : Epi quotient := by
  have : Epi (sectionMap ≫ quotient) := by rw [sectionMap_quotient]; infer_instance
  exact epi_of_epi sectionMap quotient

def presentation : QuotientPresentation domain 9 14 where
  target := SheafOfModules.free (R := domain.ringCatSheaf) (ULift (Fin (14-9)))
  map := chartQuotientMap 9 14 pivot integralChartPoint
  map_epi := quotient_epi
  finiteLocallyFree := free_isFiniteLocallyFreeOfRank domain (14-9)

theorem chart_class : (functorData 9 14).objEquiv domain
    ((schemeRepresentableBy 9 14).homEquiv
      (RadicalGrassmannianChart.chart ≫ GrassmannianCharts.toIntegral ℂ 9 14)) = ⟦presentation⟧ := by
  rw [chart_toIntegral]
  exact private_decl% (by
    have h := objEquiv_homEquiv_comp_chartMap 9 14 pivot integralChartPoint
    refine h.trans (Quotient.sound (.rel _ _ ⟨Iso.refl _,?_⟩))
    dsimp only [normalizedQuotientPresentation,presentation,quotient]
    simp only [chartQuotientMap,Iso.refl_hom,Category.comp_id])

theorem presentation_map : presentation.map = quotient := rfl

def parameterMatrix : Matrix (Fin 5) (Fin 9) parameterRing := fun i j => X (i,j)

instance globalComplexAlgebra : Algebra ℂ Γ(domain,⊤) :=
  ((Scheme.ΓSpecIso (.of parameterRing)).inv.hom.comp (algebraMap ℂ parameterRing)).toAlgebra

def globalMatrix : Matrix (Fin 5) (Fin 9) Γ(domain,⊤) :=
  parameterMatrix.map (Scheme.ΓSpecIso (.of parameterRing)).inv.hom

/-- The classified quotient matrix has the original cofactor chart's exact
negative X block and its literal identity pivot columns. -/
theorem quotient_matrix : Stacks.FreeSheafMatrix.toMatrix quotient = quotientMatrix globalMatrix := by
  rw [quotient,toMatrix_chartQuotientMap,quotientMatrix_eq_chartMatrix]
  congr 1
  funext a
  rw [integralChartPoint_coordinates,coordinateRingEquiv_X,map_neg]
  rfl

section CoefficientExtension
variable (R : Type*) [CommRing R] [Algebra ℂ R]

/-- Literal coefficient extension of the original primitive coordinates. -/
def scalarExtendedCoordinates :
    (R ⊗[ℂ] M9.ExteriorPrimitive.Primitive ℂ) ≃ₗ[R] (Fin 14 → R) :=
  (primitiveCoordinates.baseChange ℂ R (M9.ExteriorPrimitive.Primitive ℂ) (Fin 14 → ℂ)).trans
    (TensorProduct.piScalarRight ℂ R R (Fin 14))

theorem scalarExtendedCoordinates_tmul (a : R) (v : M9.ExteriorPrimitive.Primitive ℂ) (i : Fin 14) :
    scalarExtendedCoordinates R (a ⊗ₜ[ℂ] v) i = algebraMap ℂ R (primitiveCoordinates v i) * a := by
  simp only [scalarExtendedCoordinates,LinearEquiv.trans_apply,LinearEquiv.baseChange_tmul,
    TensorProduct.piScalarRight_apply,TensorProduct.piScalarRightHom_tmul]
  rw [Algebra.smul_def]

/-- The actual primitive-plane embedding over every coefficient ring,
including nonreduced ones, with the original [I9;X] coordinate frame. -/
def primitiveFrame (D : Matrix (Fin 5) (Fin 9) R) :
    (Fin 9 → R) →ₗ[R] (R ⊗[ℂ] M9.ExteriorPrimitive.Primitive ℂ) :=
  (scalarExtendedCoordinates R).symm.toLinearMap.comp (Matrix.toLin' (frameMatrix D))

theorem kernel_scalarExtended_primitiveFrame (D : Matrix (Fin 5) (Fin 9) R) :
    (Matrix.toLin' (quotientMatrix D)).ker.map (scalarExtendedCoordinates R).symm.toLinearMap =
      (primitiveFrame R D).range := by
  rw [quotientMatrix_ker,primitiveFrame,LinearMap.range_comp]

end CoefficientExtension

theorem universal_kernel_primitiveFrame :
    (Matrix.toLin' (Stacks.FreeSheafMatrix.toMatrix quotient)).ker.map
        (scalarExtendedCoordinates Γ(domain,⊤)).symm.toLinearMap =
      (primitiveFrame Γ(domain,⊤) globalMatrix).range := by
  rw [quotient_matrix]
  exact kernel_scalarExtended_primitiveFrame _ _

end M9Native.PrimitiveRadicalNativeScheme
