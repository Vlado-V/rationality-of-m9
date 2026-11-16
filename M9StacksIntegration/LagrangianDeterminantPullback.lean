module

public import M9StacksIntegration.LagrangianDeterminantSections

/-! Actual base change of the quotient determinant sections. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
universe u
namespace M9Native.LagrangianDeterminantPullback
open M9Native.LagrangianGrassmannian M9Native.LagrangianMatrixChart
open M9Native.LagrangianPullback M9Native.LagrangianDeterminantSections
open M9Native.SectionZeroIdealFactorization AlgebraicGeometry.Grassmannian

/-- The two native application spellings have the same actual value. -/
theorem app_apply_val {X : Scheme.{u}} {E F : X.Modules} (φ : E ⟶ F) (U : X.Opens)
    (v : Γ(E,U)) : φ.app U v=φ.val.app (op U) v := rfl

/-- The actual exterior comparison in the scheme-module application spelling. -/
theorem comparison_eq_homogeneousProd {X : Scheme.{u}} (F : X.Modules) (n : ℕ)
    (s : Fin n → Γ(F,⊤)) :
    M9Native.ExteriorEvaluation.sectionComparison F n ⊤ (exteriorPower.ιMulti Γ(X,⊤) n s)=
      (Scheme.Modules.exteriorAlgebra F).toPresheafGradedAlgebra.homogeneousProd (op ⊤) n
        (fun i => (Scheme.Modules.exteriorGenerator F).app ⊤ (s i)) := by
  refine (M9Native.ExteriorEvaluation.sectionComparison_ιMulti F n ⊤ s).trans ?_
  exact congrArg ((Scheme.Modules.exteriorAlgebra F).toPresheafGradedAlgebra.homogeneousProd (op ⊤) n)
    (funext fun i => (app_apply_val (Scheme.Modules.exteriorGenerator F) ⊤ (s i)).symm)

/-- The canonical free/exterior comparison transports the actual standard third wedge. -/
theorem standardWedge_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (c : Fin 3 ↪ Fin 6) :
    (exteriorPowerMap Y (pullbackFreeIso f 6).hom 3).app ⊤
      ((exteriorPullbackIso f (freeOn X 6) 3).hom.app ⊤
        (pullbackGlobalSections f (Scheme.Modules.exteriorPower (freeOn X 6) 3) (standardWedge X c)))=
      standardWedge Y c := by
  have h : (exteriorPullbackIso f (freeOn X 6) 3).hom.app ⊤
        (pullbackGlobalSections f (Scheme.Modules.exteriorPower (freeOn X 6) 3) (standardWedge X c))=
      M9Native.ExteriorEvaluation.sectionComparison ((Scheme.Modules.pullback f).obj (freeOn X 6)) 3 ⊤
        (exteriorPower.ιMulti Γ(Y,⊤) 3 (fun i =>
          pullbackGlobalSections f (freeOn X 6) (freeBasisSection X 6 (c i)))) := by
    rw [standardWedge,comparison_eq_homogeneousProd,comparison_eq_homogeneousProd]
    exact exteriorPullback_homogeneousProd f (freeOn X 6) 3 (fun i => freeBasisSection X 6 (c i))
  rw [h,exteriorPowerMap_eq_native]
  have hn := M9Native.ExteriorEvaluation.sectionComparison_map_ιMulti (pullbackFreeIso f 6).hom 3 ⊤
    (fun i => pullbackGlobalSections f (freeOn X 6) (freeBasisSection X 6 (c i)))
  refine hn.trans ?_
  change M9Native.ExteriorEvaluation.sectionComparison (freeOn Y 6) 3 ⊤
    (exteriorPower.ιMulti Γ(Y,⊤) 3 (fun i =>
      (pullbackFreeIso f 6).hom.app ⊤
        (pullbackGlobalSections f (freeOn X 6) (freeBasisSection X 6 (c i)))))=_
  exact congrArg (fun v => M9Native.ExteriorEvaluation.sectionComparison (freeOn Y 6) 3 ⊤
    (exteriorPower.ιMulti Γ(Y,⊤) 3 v))
    (funext fun i => freeVector_pullback f (c i))

/-- A genuine pulled-back quotient has exactly the pulled-back determinant sections. -/
theorem minorSection_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) {k : ℕ}
    (q : QuotientPresentation X k 6) (c : Fin 3 ↪ Fin 6) :
    (exteriorPullbackIso f q.target 3).hom.app ⊤
      (pullbackGlobalSections f (Scheme.Modules.exteriorPower q.target 3) (minorSection X q.map c))=
      minorSection Y (pullbackPresentation f q).map c := by
  let s := pullbackGlobalSections f (Scheme.Modules.exteriorPower (freeOn X 6) 3) (standardWedge X c)
  let t := (exteriorPullbackIso f (freeOn X 6) 3).hom.app ⊤ s
  have hn : (Scheme.Modules.pullback f).map (exteriorPowerMap X q.map 3) ≫
      (exteriorPullbackIso f q.target 3).hom=
    (exteriorPullbackIso f (freeOn X 6) 3).hom ≫
      exteriorPowerMap Y ((Scheme.Modules.pullback f).map q.map) 3 := by
    simpa only [exteriorPowerMap_eq_native] using exteriorPullbackIso_natural f q.map 3
  have hq : exteriorPowerMap Y (pullbackFreeIso f 6).hom 3 ≫
      exteriorPowerMap Y (pullbackPresentation f q).map 3=
      exteriorPowerMap Y ((Scheme.Modules.pullback f).map q.map) 3 := by
    simp only [exteriorPowerMap_eq_native,← Scheme.Modules.exteriorPowerMap_comp]
    congr 1
    change (pullbackFreeIso f 6).hom ≫
      ((pullbackFreeIso f 6).inv ≫ (Scheme.Modules.pullback f).map q.map)=_
    exact Iso.hom_inv_id_assoc _ _
  calc
    _ = (exteriorPullbackIso f q.target 3).hom.app ⊤
        (((Scheme.Modules.pullback f).map (exteriorPowerMap X q.map 3)).app ⊤ s) :=
      congrArg ((exteriorPullbackIso f q.target 3).hom.app ⊤)
        (pullback_map_app_pullbackGlobalSections f (exteriorPowerMap X q.map 3) (standardWedge X c)).symm
    _ = (exteriorPowerMap Y ((Scheme.Modules.pullback f).map q.map) 3).app ⊤ t :=
      congrArg (fun φ => φ.app ⊤ s) hn
    _ = _ := by
      rw [minorSection,← standardWedge_pullback f c]
      exact (congrArg (fun φ => φ.app ⊤ t) hq).symm

end M9Native.LagrangianDeterminantPullback
