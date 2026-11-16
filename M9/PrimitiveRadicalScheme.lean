module

public import M9.RadicalMapScheme
public import M9.PrimitiveRadicalFiber

/-! # Actual primitive radical charts as scheme morphisms

The basis is a proved basis of the actual primitive exterior kernel. The
forty-five parameters specify the standard graph frame in that basis, and
the native projective morphisms have the evaluated actual radical vectors
as their coordinate ratios.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.PrimitiveRadicalScheme

open Module ExteriorPrimitive PrimitiveStabilizer RadicalMap
open CategoryTheory AlgebraicGeometry
open M9.ProjectiveGeometry

local instance primitiveAddCommGroup : AddCommGroup (Primitive ℂ) :=
  { (Primitive ℂ).addCommGroup with toAddCommMonoid := (Primitive ℂ).addCommMonoid }

/-- A fixed fourteen-element basis of the genuine primitive kernel. -/
def primitiveChartBasis : Basis AmbientIndex ℂ (Primitive ℂ) :=
  (primitiveBasis ℂ).reindex (Fintype.equivOfCardEq (by simp [AmbientIndex]))

def ambientFinEquiv : AmbientIndex ≃ Fin 14 := finSumFinEquiv

/-- The explicit coordinate equivalence used to identify the native target P13. -/
def primitiveCoordinates : Primitive ℂ ≃ₗ[ℂ] (Fin 14 → ℂ) :=
  primitiveChartBasis.equivFun.trans (LinearEquiv.funCongrLeft ℂ ℂ ambientFinEquiv.symm)

/-- Literal graph frames in the actual primitive exterior space. -/
def actualFrame (x : ChartIndex → ℂ) : Fin 9 → Primitive ℂ :=
  chartFrame ℂ primitiveChartBasis x

theorem actualFrame_independent (x : ChartIndex → ℂ) : LinearIndependent ℂ (actualFrame x) :=
  chartFrame_independent ℂ primitiveChartBasis x

def actualBasisGram : Matrix AmbientIndex AmbientIndex ℂ :=
  fun a b => primitivePairing ℂ (primitiveChartBasis a) (primitiveChartBasis b)

/-- The polynomial vector used by the native scheme morphisms, with its genuine basis indices. -/
def radicalCoordinates (j : Fin 9) : Fin 14 → ChartRing ℂ :=
  fun k => polynomialRadical ℂ actualBasisGram j (ambientFinEquiv.symm k)

/-- Literal polynomial evaluation is the coordinate vector of the actual radical. -/
theorem radicalCoordinates_evaluation (x : ChartIndex → ℂ) (j : Fin 9) (k : Fin 14) :
    MvPolynomial.eval x (radicalCoordinates j k) =
      primitiveCoordinates (radicalVector (primitivePairing ℂ) (actualFrame x) j) k :=
  eval_polynomialRadical ℂ (primitivePairing ℂ) primitiveChartBasis x j (ambientFinEquiv.symm k)

/-- The nonzero component charts cover precisely the actual rank-eight domain. -/
theorem rank_eight_iff_component (x : ChartIndex → ℂ) :
    (gram (primitivePairing ℂ) (actualFrame x)).rank = 8 ↔
      ∃ j k, MvPolynomial.eval x (radicalCoordinates j k) ≠ 0 := by
  unfold actualFrame radicalCoordinates actualBasisGram
  rw [rank_eight_iff_polynomialRadical ℂ (primitivePairing ℂ) (primitivePairing_isAlt ℂ)
    primitiveChartBasis x]
  constructor
  · rintro ⟨j,a,ha⟩
    refine ⟨j,ambientFinEquiv a,?_⟩
    simpa only [ambientFinEquiv.symm_apply_apply] using ha
  · rintro ⟨j,k,hk⟩
    exact ⟨j,ambientFinEquiv.symm k,hk⟩

/-- Each local radical map is an actual morphism to the native projective scheme. -/
def radicalChartMorphism (j : Fin 9) (k : Fin 14) :
    Spec (.of (ComponentRing (radicalCoordinates j) k)) ⟶ ProjectiveSpace.projectiveSpace 13 :=
  componentSchemeMorphism (radicalCoordinates j) k

theorem radicalChartMorphism_over (j : Fin 9) (k : Fin 14) :
    radicalChartMorphism j k ≫ ProjectiveSpace.projectiveSpaceToBase 13 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (ComponentRing (radicalCoordinates j) k))) :=
  componentSchemeMorphism_over _ _

/-- Its affine projective coordinate functions have exactly the actual radical ratios. -/
theorem radicalChart_ratio_evaluation (x : ChartIndex → ℂ) (j : Fin 9) (k : Fin 14)
    (hx : MvPolynomial.eval x (radicalCoordinates j k) ≠ 0)
    (a : {a : Fin 14 // a ≠ k}) :
    componentEvaluation (radicalCoordinates j) k x hx
        (componentRatioHom (radicalCoordinates j) k (MvPolynomial.X a)) =
      primitiveCoordinates (radicalVector (primitivePairing ℂ) (actualFrame x) j) a.val /
        primitiveCoordinates (radicalVector (primitivePairing ℂ) (actualFrame x) j) k := by
  rw [componentRatio_evaluation,radicalCoordinates_evaluation,radicalCoordinates_evaluation]

/-- The actual rank-eight locus is represented by a native union of principal opens. -/
def rankEightOpen : TopologicalSpace.Opens (PrimeSpectrum (ChartRing ℂ)) :=
  ⨆ j : Fin 9, ⨆ k : Fin 14, PrimeSpectrum.basicOpen (radicalCoordinates j k)

/-- Actual affine chart points, formed from their literal polynomial evaluations. -/
def chartPoint (x : ChartIndex → ℂ) : PrimeSpectrum (ChartRing ℂ) :=
  PrimeSpectrum.comap (MvPolynomial.eval x) ⟨⊥,inferInstance⟩

theorem chartPoint_mem_rankEightOpen (x : ChartIndex → ℂ) :
    chartPoint x ∈ rankEightOpen ↔ (gram (primitivePairing ℂ) (actualFrame x)).rank = 8 := by
  rw [rank_eight_iff_component]
  simp only [rankEightOpen,TopologicalSpace.Opens.mem_iSup]
  rfl

end M9.PrimitiveRadicalScheme
