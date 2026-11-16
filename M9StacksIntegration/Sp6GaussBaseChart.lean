module

public import M9StacksIntegration.Sp6GaussPrincipalOpen
public import M9StacksIntegration.Sp6AffineBaseChange

/-!
# The actual Gauss open chart after base change

The source is the genuine tensor base change of the checked Gauss
parameter ring. Pullback pasting gives the actual affine isomorphism
to the base-changed principal open in the original symplectic group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.Sp6GaussBaseChart

open Sp6AffineBaseChange (IntegerRing specAlgebraMap tensorObject tensorObjectLeftAlgebra)

variable (K : Type u) [CommRing K]

local instance targetIntegerAlgebra : Algebra IntegerRing.{u} K :=
  Sp6AffineBaseChange.integerAlgebra K

abbrev CoordinateRing : Type u :=
  tensorObject IntegerRing.{u} K Sp6GaussCellCoordinates.CoordinateRing.{u}

instance coordinateCommRing : CommRing (CoordinateRing K) := by infer_instance
instance coordinateAlgebra : Algebra K (CoordinateRing K) :=
  tensorObjectLeftAlgebra IntegerRing K Sp6GaussCellCoordinates.CoordinateRing

abbrev source : Scheme.{u} := Spec (.of (CoordinateRing K))
abbrev group : Scheme.{u} := (Sp6GroupScheme.obj (Spec (.of K))).left

def projection : source K ⟶ Spec (.of K) := specAlgebraMap K (CoordinateRing K)

def groupFst : group K ⟶ Sp6GroupScheme.integralScheme.{u} :=
  pullback.fst Sp6GroupScheme.integralProjection (specULiftZIsTerminal.from (Spec (.of K)))

def integralSourceProjection : Sp6GaussPrincipalOpen.parameterScheme.{u} ⟶
    Sp6GroupScheme.integralBase.{u} :=
  Sp6GaussPrincipalOpen.chart ≫ Sp6GroupScheme.integralProjection

abbrev pullbackSource : Scheme.{u} :=
  pullback Sp6GaussPrincipalOpen.chart (groupFst K)

def canonicalPullbackIso :
    pullback integralSourceProjection.{u} (specULiftZIsTerminal.from (Spec (.of K))) ≅
      pullback
        (specAlgebraMap IntegerRing Sp6GaussCellCoordinates.CoordinateRing)
        (specAlgebraMap IntegerRing K) :=
  pullback.congrHom (specULiftZIsTerminal.hom_ext _ _) (specULiftZIsTerminal.hom_ext _ _)

theorem canonicalPullbackIso_inv_snd :
    (canonicalPullbackIso K).inv ≫
      pullback.snd integralSourceProjection (specULiftZIsTerminal.from (Spec (.of K))) =
        pullback.snd
          (specAlgebraMap IntegerRing Sp6GaussCellCoordinates.CoordinateRing)
          (specAlgebraMap IntegerRing K) := by
  simp only [canonicalPullbackIso,pullback.congrHom_inv,pullback.map,
    pullback.lift_snd,Category.comp_id]

def affineIso : source K ≅ pullbackSource K :=
  (pullbackSpecIso IntegerRing K Sp6GaussCellCoordinates.CoordinateRing).symm ≪≫
    (pullbackSymmetry
      (specAlgebraMap IntegerRing Sp6GaussCellCoordinates.CoordinateRing)
      (specAlgebraMap IntegerRing K)).symm ≪≫
    (canonicalPullbackIso K).symm ≪≫
    (pullbackRightPullbackFstIso Sp6GroupScheme.integralProjection
      (specULiftZIsTerminal.from (Spec (.of K))) Sp6GaussPrincipalOpen.chart).symm

def chart : source K ⟶ group K :=
  (affineIso K).hom ≫ pullback.snd Sp6GaussPrincipalOpen.chart (groupFst K)

instance chart_isOpenImmersion : IsOpenImmersion (chart K) := by
  dsimp [chart]
  infer_instance

@[reassoc]
theorem chart_projection :
    chart K ≫ (Sp6GroupScheme.obj (Spec (.of K))).hom = projection K := by
  simp only [chart,affineIso,Iso.trans_hom,Iso.symm_hom,Category.assoc]
  rw [show (Sp6GroupScheme.obj (Spec (.of K))).hom =
    pullback.snd Sp6GroupScheme.integralProjection
      (specULiftZIsTerminal.from (Spec (.of K))) from rfl]
  have hp :
      (pullbackRightPullbackFstIso Sp6GroupScheme.integralProjection
        (specULiftZIsTerminal.from (Spec (.of K))) Sp6GaussPrincipalOpen.chart).inv ≫
        pullback.snd Sp6GaussPrincipalOpen.chart (groupFst K) ≫
        pullback.snd Sp6GroupScheme.integralProjection
          (specULiftZIsTerminal.from (Spec (.of K))) =
      pullback.snd integralSourceProjection (specULiftZIsTerminal.from (Spec (.of K))) :=
    pullbackRightPullbackFstIso_inv_snd_snd _ _ _
  rw [hp]
  simp only [canonicalPullbackIso_inv_snd, pullbackSymmetry_inv_comp_snd]
  dsimp [projection,specAlgebraMap]
  exact pullbackSpecIso_inv_fst' IntegerRing K Sp6GaussCellCoordinates.CoordinateRing

def overChart : Over.mk (projection K) ⟶ Sp6GroupScheme.obj (Spec (.of K)) :=
  Over.homMk (chart K) (chart_projection K)

/-- Factorization is for every actual test scheme, rather than only
for points valued in the structural field. -/
theorem exists_chart_factor {T : Scheme.{u}} (p : T ⟶ group K)
    (hp : IsUnit
      (Sp6GroupScheme.schemePointsEquiv T (p ≫ groupFst K)).val.toBlocks₁₁.det) :
    ∃ z : T ⟶ source K, z ≫ chart K = p := by
  obtain ⟨z,hz⟩ := Sp6GaussPrincipalOpen.exists_chart_factor (p ≫ groupFst K) hp
  let l : T ⟶ pullbackSource K := pullback.lift z p hz
  refine ⟨l ≫ (affineIso K).inv,?_⟩
  rw [chart,Category.assoc,Iso.inv_hom_id_assoc]
  exact pullback.lift_snd _ _ _

theorem exists_overChart_factor {T : Over (Spec (.of K))}
    (p : T ⟶ Sp6GroupScheme.obj (Spec (.of K)))
    (hp : IsUnit (Sp6GroupScheme.pointsMulEquiv (Spec (.of K)) T p).val.toBlocks₁₁.det) :
    ∃ z : T ⟶ Over.mk (projection K), z ≫ overChart K = p := by
  change IsUnit
    (Sp6GroupScheme.schemePointsEquiv T.left (p.left ≫ groupFst K)).val.toBlocks₁₁.det at hp
  obtain ⟨z,hz⟩ := exists_chart_factor K p.left hp
  have hb : z ≫ projection K = T.hom := by
    rw [← chart_projection,← Category.assoc,hz]
    exact p.w
  refine ⟨Over.homMk z hb,?_⟩
  exact Over.OverMorphism.ext hz

end M9Native.Sp6GaussBaseChart

