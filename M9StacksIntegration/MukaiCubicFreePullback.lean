module

public import M9StacksIntegration.MukaiTensorPullbackNaturality
public import M9StacksIntegration.MukaiFreePullbackCoordinates
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis

/-! The actual global cubic on the free fourteen-coordinate bundle
agrees with its original ground-field cubic at every actual same-base
field point. The comparison is proved on all genuine affine sections
through the native tensor and free-basis pullback comparisons. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiCubicFreePullback

open MukaiBundleDeterminant MukaiTensorPullbackNaturality MukaiCubicFreeSheaf
open MukaiFreePullbackCoordinates LagrangianMatrixChart LinearIncidenceTensorCoordinates
open AlgebraicGeometry.Grassmannian SectionZeroIdealFactorization

variable {X Y : Scheme.{u}}

def freeCubePullbackIso (p : Y ⟶ X) :
    (Scheme.Modules.pullback p).obj (cubeObj (freeOn X 14)) ≅ cubeObj (freeOn Y 14) :=
  cubePullbackIso p (freeOn X 14) ≪≫
    tensorIso (tensorIso (pullbackFreeIso p 14) (pullbackFreeIso p 14))
      (pullbackFreeIso p 14)

theorem freeCubePullbackIso_tensorTop (p : Y ⟶ X)
    (s t u : Γ(freeOn X 14, ⊤)) :
    (freeCubePullbackIso p).hom.app ⊤
      (pullbackGlobalSections p (cubeObj (freeOn X 14))
        (tensorTop X (tensor (freeOn X 14) (freeOn X 14)) (freeOn X 14)
          (tensorTop X (freeOn X 14) (freeOn X 14) s t) u)) =
      tensorTop Y (tensor (freeOn Y 14) (freeOn Y 14)) (freeOn Y 14)
        (tensorTop Y (freeOn Y 14) (freeOn Y 14)
          ((pullbackFreeIso p 14).hom.app ⊤ (pullbackGlobalSections p (freeOn X 14) s))
          ((pullbackFreeIso p 14).hom.app ⊤ (pullbackGlobalSections p (freeOn X 14) t)))
        ((pullbackFreeIso p 14).hom.app ⊤ (pullbackGlobalSections p (freeOn X 14) u)) := by
  change (tensorIso (tensorIso (pullbackFreeIso p 14) (pullbackFreeIso p 14))
      (pullbackFreeIso p 14)).hom.app ⊤
      ((cubePullbackIso p (freeOn X 14)).hom.app ⊤ _) = _
  rw [cubePullbackIso_tensorTop, MukaiCubicConstantSheaf.tensorIso_tensorTop,
    MukaiCubicConstantSheaf.tensorIso_tensorTop]

variable (K : Type u) [Field K] [CharZero K] (f : X ⟶ Spec (.of K))

def pulledCubicMap (p : Y ⟶ X) : cubeObj (freeOn Y 14) ⟶ freeOn Y 14 :=
  (freeCubePullbackIso p).inv ≫ (Scheme.Modules.pullback p).map (cubicFreeMap K f) ≫
    (pullbackFreeIso p 14).hom

theorem freeCubePullbackIso_formSection (p : Y ⟶ X)
    (a b c : MukaiPrimitiveQuartic.Forms K) :
    (freeCubePullbackIso p).hom.app ⊤
      (pullbackGlobalSections p (cubeObj (freeOn X 14)) (tripleFormSection K f a b c)) =
      tripleFormSection K (p ≫ f) a b c := by
  unfold tripleFormSection
  rw [freeCubePullbackIso_tensorTop, formSection_pullback, formSection_pullback,
    formSection_pullback]

theorem freeCubePullbackIso_inv_formSection (p : Y ⟶ X)
    (a b c : MukaiPrimitiveQuartic.Forms K) :
    (freeCubePullbackIso p).inv.app ⊤ (tripleFormSection K (p ≫ f) a b c) =
      pullbackGlobalSections p (cubeObj (freeOn X 14)) (tripleFormSection K f a b c) := by
  have h := congrArg ((freeCubePullbackIso p).inv.app ⊤)
    (freeCubePullbackIso_formSection K f p a b c)
  have hc := congrArg (fun m => m.app ⊤
    (pullbackGlobalSections p (cubeObj (freeOn X 14)) (tripleFormSection K f a b c)))
      (freeCubePullbackIso p).hom_inv_id
  exact h.symm.trans hc

/-- Literal equality of the pulled global cubic with the original
coefficient cubic at a ground-field point. No condition on the conormal
image or on the evaluation kernel is used. -/
theorem pulledCubicMap_fieldPoint (p : Spec (.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) :
    pulledCubicMap K f p = cubicFreeMap K (𝟙 (Spec (.of K))) := by
  let A := freeOn (Spec (.of K)) 14
  let hA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A 14 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_free (R := (Spec (.of K)).ringCatSheaf) 14
  let hAA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor A A) (14*14) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (Spec (.of K)) A A 14 14
  let hAAA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cubeObj A) ((14*14)*14) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (Spec (.of K)) (tensor A A) A (14*14) 14
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} A := hA.isFiniteLocallyFree
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (tensor A A) := hAA.isFiniteLocallyFree
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (cubeObj A) := hAAA.isFiniteLocallyFree
  let : A.IsQuasicoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree A
  let : (tensor A A).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree (tensor A A)
  let : (cubeObj A).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree (cubeObj A)
  apply affine_cube_hom_ext
  intro s t u
  obtain ⟨a, rfl⟩ := formSection_surjective K s
  obtain ⟨b, rfl⟩ := formSection_surjective K t
  obtain ⟨c, rfl⟩ := formSection_surjective K u
  change (pullbackFreeIso p 14).hom.app ⊤
    (((Scheme.Modules.pullback p).map (cubicFreeMap K f)).app ⊤
      ((freeCubePullbackIso p).inv.app ⊤ (tripleFormSection K (𝟙 _) a b c))) = _
  have hi := freeCubePullbackIso_inv_formSection K f p a b c
  rw [hp] at hi
  rw [hi, pullback_map_app_pullbackGlobalSections]
  change (pullbackFreeIso p 14).hom.app ⊤
    (pullbackGlobalSections p (freeOn X 14)
      ((cubicFreeMap K f).app ⊤ (tripleFormSection K f a b c))) =
      (cubicFreeMap K (𝟙 (Spec (.of K)))).app ⊤ (tripleFormSection K (𝟙 _) a b c)
  unfold tripleFormSection
  rw [cubicFreeMap_section, cubicFreeMap_section, dualFormSection_pullback, hp]

end M9Native.MukaiCubicFreePullback
