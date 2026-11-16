module

public import M9StacksIntegration.LagrangianVariableSymplecticAction
public import M9StacksIntegration.LagrangianPluckerTrivialization
public import M9StacksIntegration.LagrangianCommonKernelZero
public import M9StacksIntegration.LagrangianArbitraryPlaneIncidence
public import M9StacksIntegration.SymplecticPlaneLineNormalizer

/-! Actual quotient and section transport for variable symplectic
matrices. All statements retain the original universal quotient map,
its native pullback and the literal first section. The arbitrary-plane
normalizer then identifies that section with the original line equation,
over every test scheme and its genuine ring of global functions. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix Module Opposite
open scoped BigOperators
universe u

namespace M9Native.LagrangianVariableQuotientSections

open AlgebraicGeometry.Grassmannian
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianMatrixChart
open LagrangianTransitivity LagrangianIsotropicRestriction LagrangianFreeMatrixPullback
open LagrangianVariableSymplecticAction SymplecticPlaneLineNormalizer

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable (K : Type u) [Field K]

abbrev actualQuotient {T : Scheme.{u}} (p : T ⟶ space K) : QuotientPresentation T 3 6 :=
  pullbackPresentation p (quotientOnLG K)

/-- Actual iterated pullback, with its original quotient map. -/
theorem actualQuotient_isomorphic_pointQuotient {T : Scheme.{u}} (p : T ⟶ space K) :
    (actualQuotient K p).Isomorphic (pointQuotient K p) :=
  LagrangianPluckerTrivialization.pullbackPresentation_comp_isomorphic
    (inclusion K) p (universalQuotient K)

/-- The variable action's target isomorphism is transported to the
literal pullback of the original quotient on LG. -/
theorem actualQuotient_actPoint_isomorphic {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    (actualQuotient K (actPoint K p g)).Isomorphic (transform g (actualQuotient K p)) := by
  obtain ⟨eA,hA⟩ := actualQuotient_isomorphic_pointQuotient K (actPoint K p g)
  obtain ⟨e,hV⟩ := pullback_actPoint_isomorphic K p g
  obtain ⟨eP,hP⟩ := actualQuotient_isomorphic_pointQuotient K p
  have hPr : (pointQuotient K p).map ≫ eP.inv = (actualQuotient K p).map := by
    rw [← hP,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  refine ⟨eA ≪≫ e ≪≫ eP.symm,?_⟩
  change (actualQuotient K (actPoint K p g)).map ≫
      (eA.hom ≫ e.hom ≫ eP.inv) = (freeSymplecticIso T g).hom ≫ (actualQuotient K p).map
  calc
    _ = ((actualQuotient K (actPoint K p g)).map ≫ eA.hom) ≫ e.hom ≫ eP.inv := by
      simp only [Category.assoc]
    _ = ((freeSymplecticIso T g).hom ≫ (pointQuotient K p).map) ≫ eP.inv := by
      rw [hA,← Category.assoc,hV]
      rfl
    _ = _ := by rw [Category.assoc,hPr]

def targetIso {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    (Scheme.Modules.pullback (actPoint K p g)).obj (quotientOnLG K).target ≅
      (Scheme.Modules.pullback p).obj (quotientOnLG K).target :=
  Classical.choose (actualQuotient_actPoint_isomorphic K p g)

theorem targetIso_triangle {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    (actualQuotient K (actPoint K p g)).map ≫ (targetIso K p g).hom =
      (freeSymplecticIso T g).hom ≫ (actualQuotient K p).map :=
  Classical.choose_spec (actualQuotient_actPoint_isomorphic K p g)

/-- The original universal quotient section corresponding to a basis vector. -/
def basisSection (j : Fin 6) : Γ((quotientOnLG K).target,⊤) :=
  Scheme.Modules.Hom.app (quotientOnLG K).map ⊤ (freeVector (space K) j)

/-- The true first section after the variable action is the original
quotient applied to the literal first matrix column. -/
theorem targetIso_standardSection {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    (targetIso K p g).hom.app ⊤
      (pullbackGlobalSections (actPoint K p g) (quotientOnLG K).target
        (LagrangianCommonKernelZero.standardSection K)) =
      ∑ j : Fin 6, matrixSix Γ(T,⊤) g j 0 •
        pullbackGlobalSections p (quotientOnLG K).target (basisSection K j) := by
  change (targetIso K p g).hom.app ⊤
      (pullbackGlobalSections (actPoint K p g) (quotientOnLG K).target
        (Scheme.Modules.Hom.app (quotientOnLG K).map ⊤ (freeVector (space K) 0))) = _
  rw [← pulledQuotient_basis]
  change Scheme.Modules.Hom.app
    ((actualQuotient K (actPoint K p g)).map ≫ (targetIso K p g).hom) ⊤ (freeVector T 0) = _
  rw [targetIso_triangle]
  change Scheme.Modules.Hom.app (actualQuotient K p).map ⊤
    ((freeSymplecticIso T g).hom.app ⊤ (freeVector T 0)) = _
  rw [end_column_eq_sum,freeSymplecticIso_matrix]
  simp only [map_sum,Scheme.Modules.Hom.app_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact pulledQuotient_basis p (quotientOnLG K).map j

/-- Actual pullback of each original plane section uses the original
structure-map coefficient homomorphism. -/
theorem originalSection_pullback {T : Scheme.{u}} (p : T ⟶ space K)
    (w : LagrangianArbitraryPlaneIncidence.PlaneFrame K) (i : Fin 2) :
    pullbackGlobalSections p (quotientOnLG K).target
      (LagrangianArbitraryPlaneIncidence.originalSection K w i) =
      ∑ j : Fin 6, LagrangianSymplecticAction.scalarMap K (p ≫ projection K) (w i j) •
        pullbackGlobalSections p (quotientOnLG K).target (basisSection K j) := by
  rw [LagrangianArbitraryPlaneIncidence.originalSection_eq_sum]
  simp only [map_sum,AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul]
  rfl

/-- The actual coefficient-ring normalizer on an arbitrary test scheme. -/
def planeMatrix {T : Scheme.{u}} (p : T ⟶ space K)
    (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) (t : Γ(T,⊤)) :
    Matrix.symplecticGroup (Fin 3) Γ(T,⊤) :=
  normalizer K w hw (LagrangianSymplecticAction.scalarMap K (p ≫ projection K)) t

def planePoint {T : Scheme.{u}} (p : T ⟶ space K)
    (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) (t : Γ(T,⊤)) :
    T ⟶ space K := actPoint K p (planeMatrix K p w hw t)

def planeTargetIso {T : Scheme.{u}} (p : T ⟶ space K)
    (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) (t : Γ(T,⊤)) :
    (Scheme.Modules.pullback (planePoint K p w hw t)).obj (quotientOnLG K).target ≅
      (Scheme.Modules.pullback p).obj (quotientOnLG K).target :=
  targetIso K p (planeMatrix K p w hw t)

/-- No plane normal-form or zero-transport premise is supplied: the
proved original first-column equation computes the actual pulled section. -/
theorem planeTargetIso_standardSection {T : Scheme.{u}} (p : T ⟶ space K)
    (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) (t : Γ(T,⊤)) :
    (planeTargetIso K p w hw t).hom.app ⊤
      (pullbackGlobalSections (planePoint K p w hw t) (quotientOnLG K).target
        (LagrangianCommonKernelZero.standardSection K)) =
      pullbackGlobalSections p (quotientOnLG K).target
        (LagrangianArbitraryPlaneIncidence.originalSection K w 0) +
      t • pullbackGlobalSections p (quotientOnLG K).target
        (LagrangianArbitraryPlaneIncidence.originalSection K w 1) := by
  change (targetIso K p (planeMatrix K p w hw t)).hom.app ⊤
      (pullbackGlobalSections (actPoint K p (planeMatrix K p w hw t))
        (quotientOnLG K).target (LagrangianCommonKernelZero.standardSection K)) = _
  rw [targetIso_standardSection]
  have hcol (j : Fin 6) : matrixSix Γ(T,⊤) (planeMatrix K p w hw t) j 0 =
      LagrangianSymplecticAction.scalarMap K (p ≫ projection K) (w 0 j) +
      t * LagrangianSymplecticAction.scalarMap K (p ≫ projection K) (w 1 j) := by
    have h := congrFun (normalizer_sends_first K w hw
      (LagrangianSymplecticAction.scalarMap K (p ≫ projection K)) t) j
    simpa only [planeMatrix,Matrix.mulVec_single_one,Matrix.col_apply,Pi.add_apply,Pi.smul_apply,
      smul_eq_mul,constantVector,Function.comp_apply] using h
  simp_rw [hcol,add_smul,mul_smul]
  rw [Finset.sum_add_distrib,← Finset.smul_sum,
    ← originalSection_pullback,← originalSection_pullback]

@[reassoc] theorem planePoint_projection {T : Scheme.{u}} (p : T ⟶ space K)
    (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) (t : Γ(T,⊤)) :
    planePoint K p w hw t ≫ projection K = p ≫ projection K :=
  actPoint_projection K p (planeMatrix K p w hw t)

end M9Native.LagrangianVariableQuotientSections
