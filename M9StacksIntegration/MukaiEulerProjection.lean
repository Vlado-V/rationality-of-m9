module

public import M9StacksIntegration.MukaiEulerFieldPoint
public import M9StacksIntegration.MukaiConormalFieldCoordinates
public import StacksFrontier.AlgebraicGeometry.Recovery27.Representable.ChartSubfunctors

/-! Literal projection coherence for the ORIGINAL native fourteen-fold
Euler cancellation and the actual field-point free coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf
  M9Native.NativeTensorLineTrivialization.tensorRight

namespace M9Native.MukaiEulerProjection

open LagrangianGrassmannian LagrangianMatrixChart MukaiBundleDeterminant
open MukaiConormalEuler MukaiConormalEulerPairing MukaiConormalEulerTwist MukaiConormalRank
open MukaiConormalFieldCoordinates
open AlgebraicGeometry.Grassmannian

theorem freeBiproductIso_inv_projection (X : Scheme.{u}) (r : ℕ) (k : Fin r) :
    (Stacks.SheafOfModules.freeULiftFinIsoBiproduct X.sheaf r).inv ≫
        Stacks.SheafOfModules.freeProj (S := X.ringCatSheaf) (ULift.up k) =
      biproduct.π (fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf) k := by
  apply biproduct.hom_ext'
  intro j
  simp only [Stacks.SheafOfModules.freeULiftFinIsoBiproduct,Iso.trans_inv,Iso.symm_inv,
    biproduct.isoCoproduct_hom,Category.assoc,biproduct.ι_desc_assoc,
    Sigma.ι_reindex_hom_assoc]
  change SheafOfModules.ιFree (ULift.up j) ≫
      Stacks.SheafOfModules.freeProj (S := X.ringCatSheaf) (ULift.up k) =
    biproduct.ι (fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf) j ≫
      biproduct.π (fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf) k
  have hl := Stacks.SheafOfModules.ιFree_comp_freeProj (S := X.ringCatSheaf)
    (ULift.up k : ULift.{u} (Fin r)) (ULift.up j)
  have hr := biproduct.ι_π (f := fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf) j k
  have hl' : SheafOfModules.ιFree (ULift.up j) ≫
      Stacks.SheafOfModules.freeProj (S := X.ringCatSheaf) (ULift.up k) =
      if j=k then 𝟙 _ else 0 := by
    simpa only [ULift.up_inj] using hl
  have hr' : biproduct.ι (fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf) j ≫
      biproduct.π (fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf) k =
      if j=k then 𝟙 _ else 0 := by
    by_cases hjk : j=k
    · simpa only [dif_pos hjk,if_pos hjk,eqToHom_refl] using hr
    · simpa only [dif_neg hjk,if_neg hjk] using hr
  exact hl'.trans hr'.symm

variable (K : Type u) [Field K] [CharZero K]

/-- The original free coordinate is exactly the original paired
biproduct component. No alternative middle-space identification is used. -/
theorem twistedMiddleIso_projection (k : Fin 14) :
    (twistedMiddleIso K).hom ≫
        Stacks.SheafOfModules.freeProj (S := (space K).ringCatSheaf) (ULift.up k) =
      (determinantTensorRight K).map
        ((Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)).map
          (ProjectiveEulerFieldPointLine.component (ULift.{u} ℤ) 13 k)) ≫
        (negativeDeterminantPairingIso K).hom := by
  let P := Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)
  let T := determinantTensorRight K
  let v : Fin 14 → (projectiveSpaceAtUniverse.{u} 13).Modules :=
    Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneFamily (ULift.{u} ℤ) 13
  letI : T.IsEquivalence := determinantTensorRight_isEquivalence K
  letI : PreservesBiproduct (P.obj ∘ v) T := preservesBiproduct_of_preservesProduct T
  have hP : (P.mapBiproduct v).hom ≫ biproduct.π (P.obj ∘ v) k =
      P.map (biproduct.π v k) := by
    exact biproduct.lift_π _ k
  have hT : (T.mapBiproduct (P.obj ∘ v)).hom ≫
      biproduct.π (T.obj ∘ P.obj ∘ v) k = T.map (biproduct.π (P.obj ∘ v) k) := by
    exact biproduct.lift_π _ k
  have hpair : (biproduct.mapIso (fun _ : Fin 14 => negativeDeterminantPairingIso K)).hom ≫
      biproduct.π (fun _ : Fin 14 => SheafOfModules.unit (space K).ringCatSheaf) k =
    biproduct.π (T.obj ∘ P.obj ∘ v) k ≫ (negativeDeterminantPairingIso K).hom := by
    exact biproduct.map_π (fun _ : Fin 14 => (negativeDeterminantPairingIso K).hom) k
  simp only [twistedMiddleIso,Iso.trans_hom,Iso.symm_hom,Category.assoc]
  rw [freeBiproductIso_inv_projection]
  change T.map (P.mapBiproduct v).hom ≫
    (T.mapBiproduct (P.obj ∘ v)).hom ≫
      (biproduct.mapIso (fun _ : Fin 14 => negativeDeterminantPairingIso K)).hom ≫
        biproduct.π (fun _ : Fin 14 => SheafOfModules.unit (space K).ringCatSheaf) k = _
  rw [hpair,← Category.assoc (T.mapBiproduct (P.obj ∘ v)).hom,hT,
    ← CategoryTheory.Functor.map_comp_assoc,hP]
  rfl

theorem twistedEuler_projection (k : Fin 14) :
    (twistedEulerSequence K).f ≫ (twistedMiddleIso K).hom ≫
        Stacks.SheafOfModules.freeProj (S := (space K).ringCatSheaf) (ULift.up k) =
      (determinantTensorRight K).map
        ((Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)).map
          (integralEulerFirst ≫ ProjectiveEulerFieldPointLine.component (ULift.{u} ℤ) 13 k)) ≫
        (negativeDeterminantPairingIso K).hom := by
  rw [twistedMiddleIso_projection]
  simp only [twistedEulerSequence,ShortComplex.map_f,integralSequence,← Category.assoc,
    ← CategoryTheory.Functor.map_comp]

variable (p : Spec (.of K) ⟶ space K)

theorem pulledEuler_projection (k : Fin 14) :
    (Scheme.Modules.pullback p).map (twistedEulerSequence K).f ≫
      (Scheme.Modules.pullback p).map (twistedMiddleIso K).hom ≫
      (pullbackFreeIso p 14).hom ≫
        SheafOfModules.freeProjection (R := (Spec (.of K)).ringCatSheaf) (ULift.up k) =
    (Scheme.Modules.pullback p).map
      ((determinantTensorRight K).map
        ((Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)).map
          (integralEulerFirst ≫ ProjectiveEulerFieldPointLine.component (ULift.{u} ℤ) 13 k)) ≫
        (negativeDeterminantPairingIso K).hom) ≫
      (Scheme.Modules.pullbackUnitIso p).hom := by
  rw [← freeProjection_pullback]
  simp only [← CategoryTheory.Functor.map_comp_assoc,← CategoryTheory.Functor.map_comp]
  rw [← freeProj_eq_freeProjection,twistedEuler_projection]

def freeCoefficient (x : MukaiEulerFieldPoint.Source K p) : Fin 14 → K :=
  freeCoordinates K 14
    ((moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (twistedEulerSequence K).f ≫
      (Scheme.Modules.pullback p).map (twistedMiddleIso K).hom ≫
        (pullbackFreeIso p 14).hom)).hom x)

theorem freeCoefficient_eq (x : MukaiEulerFieldPoint.Source K p) (k : Fin 14) :
    freeCoefficient K p x k = MukaiEulerFieldPoint.coefficient K p k x := by
  have h := congrArg (fun t => (moduleSpecΓFunctor.map t).hom x)
    (pulledEuler_projection K p k)
  change (scalarEquiv K).symm
      (freeSectionCoordinates (Spec (.of K)) 14
        ((moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (twistedEulerSequence K).f ≫
          (Scheme.Modules.pullback p).map (twistedMiddleIso K).hom ≫
            (pullbackFreeIso p 14).hom)).hom x) k) = _
  rw [freeSectionCoordinates_apply,freeProj_eq_freeProjection]
  change (ProjectiveEulerFieldPointLine.unitCoordinates K)
      ((moduleSpecΓFunctor.map
        (SheafOfModules.freeProjection (R := (Spec (.of K)).ringCatSheaf) (ULift.up k))).hom
        ((moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (twistedEulerSequence K).f ≫
          (Scheme.Modules.pullback p).map (twistedMiddleIso K).hom ≫
            (pullbackFreeIso p 14).hom)).hom x)) = _
  apply congrArg (ProjectiveEulerFieldPointLine.unitCoordinates K)
  simp only [CategoryTheory.Functor.map_comp,ModuleCat.hom_comp,LinearMap.comp_apply] at h
  simp only [SpecFieldStalkSections.space,ProjectiveEulerCompositeLine.pairedEulerComponent,
    NativeTensorLineTrivialization.tensorRight,determinantTensorRight,
    ProjectiveEulerFieldPoint.eulerFirst,integralEulerFirst,
    CategoryTheory.Functor.map_comp,ModuleCat.hom_comp,LinearMap.comp_apply] at h ⊢
  exact h

variable [IsAlgClosed K]

/-- The frozen original coefficientMap is identified with the actual
paired Euler coordinate on the actual conormal input. -/
theorem coefficientMap_eq (y : Source K p) (k : Fin 14) :
    coefficientMap K p y k =
      MukaiEulerFieldPoint.coefficient K p k (MukaiEulerFieldPoint.conormalInput K p y) := by
  rw [← freeCoefficient_eq]
  have h : (twistedConormalMap K) =
      (determinantTensorRight K).map
        (MukaiConormalCotangentTransport.conormalToIntegralCotangent K) ≫
          (twistedEulerSequence K).f ≫ (twistedMiddleIso K).hom := by
    simp only [twistedConormalMap,conormalEulerMap,CategoryTheory.Functor.map_comp]
    rfl
  simp only [coefficientMap,freeCoefficient,MukaiEulerFieldPoint.conormalInput,
    LinearMap.comp_apply,h,CategoryTheory.Functor.map_comp,ModuleCat.hom_comp,
    LinearMap.comp_apply]
  rfl

end M9Native.MukaiEulerProjection
