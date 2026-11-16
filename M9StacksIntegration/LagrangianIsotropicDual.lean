module

public import M9StacksIntegration.LagrangianDualCoefficients
public import M9StacksIntegration.LagrangianSigmaInvariance

/-! Actual dual coefficient isotropy for the original exterior-isotropic quotient. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators

universe u

namespace M9Native.LagrangianIsotropicDual

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- An actual global section of the dual is an actual sheaf morphism.
The construction is on all opens and retains the original evaluations. -/
def topFunctional (Q : X.Modules) (α : Γ(dualSheaf Q,⊤)) :
    Q ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ⟨{ app := fun U => α.app (op (Over.mk (homOfLE (show U.unop≤⊤ from le_top))))
     naturality := by
       intro U V f
       let g : Over.mk (homOfLE (show V.unop≤⊤ from le_top)) ⟶
           Over.mk (homOfLE (show U.unop≤⊤ from le_top)) :=
         Over.homMk f.unop (Subsingleton.elim _ _)
       exact α.naturality g.op }⟩

theorem topFunctional_top (Q : X.Modules) (α : Γ(dualSheaf Q,⊤)) (s : Γ(Q,⊤)) :
    (topFunctional Q α).app ⊤ s=evalAt Q α s := by
  change (α.app (op (Over.mk (homOfLE (show (⊤ : X.Opens)≤⊤ from le_top))))).hom s=
    (α.app (op (Over.mk (𝟙 (⊤ : X.Opens))))).hom s
  congr 3

/-- Actual exterior annihilation is preserved by any original target map. -/
theorem annihilatesSigma_postcomp {Q P : X.Modules} (q : freeOn X 6 ⟶ Q) (g : Q ⟶ P)
    (hq : AnnihilatesSigma X q) : AnnihilatesSigma X (q ≫ g) := by
  change (Scheme.Modules.exteriorPowerMap (q ≫ g) 2).app ⊤ (sigmaSection X)=0
  rw [Scheme.Modules.exteriorPowerMap_comp]
  change (Scheme.Modules.exteriorPowerMap g 2).app ⊤
    ((Scheme.Modules.exteriorPowerMap q 2).app ⊤ (sigmaSection X))=0
  rw [show (Scheme.Modules.exteriorPowerMap q 2).app ⊤ (sigmaSection X)=0 from hq,map_zero]

/-- Two actual sheaf functionals combined into the actual free rank-two target. -/
def twoFunctionals (Q : X.Modules) (α β : Γ(dualSheaf Q,⊤)) : Q ⟶ freeOn X 2 :=
  topFunctional Q α ≫ SheafOfModules.ιFree (ULift.up (0 : Fin 2))+
    topFunctional Q β ≫ SheafOfModules.ιFree (ULift.up (1 : Fin 2))

theorem twoFunctionals_projection_zero (Q : X.Modules) (α β : Γ(dualSheaf Q,⊤)) :
    twoFunctionals Q α β ≫ SheafOfModules.freeProjection (ULift.up (0 : Fin 2))=
      topFunctional Q α := by
  simp only [twoFunctionals,Preadditive.add_comp,Category.assoc]
  rw [SheafOfModules.ιFree_comp_freeProjection_self,
    SheafOfModules.ιFree_comp_freeProjection_of_ne (by decide)]
  simp

theorem twoFunctionals_projection_one (Q : X.Modules) (α β : Γ(dualSheaf Q,⊤)) :
    twoFunctionals Q α β ≫ SheafOfModules.freeProjection (ULift.up (1 : Fin 2))=
      topFunctional Q β := by
  simp only [twoFunctionals,Preadditive.add_comp,Category.assoc]
  rw [SheafOfModules.ιFree_comp_freeProjection_of_ne (by decide),
    SheafOfModules.ιFree_comp_freeProjection_self]
  simp

theorem twoFunctionals_matrix_zero {Q : X.Modules} (q : freeOn X 6 ⟶ Q)
    (α β : Γ(dualSheaf Q,⊤)) (j : Fin 6) :
    Stacks.FreeSheafMatrix.toMatrix (q ≫ twoFunctionals Q α β) 0 j=
      coefficientMap q ⊤ α j := by
  change Stacks.FreeSheafMatrix.unitEndValue
    (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up.{u} j) ≫ (q ≫ twoFunctionals Q α β) ≫
      SheafOfModules.freeProjection (R := X.ringCatSheaf) (ULift.up.{u} (0 : Fin 2)))= _
  have h := congrArg (fun g : Q ⟶ SheafOfModules.unit X.ringCatSheaf =>
    Stacks.FreeSheafMatrix.unitEndValue
      (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up.{u} j) ≫ q ≫ g))
      (twoFunctionals_projection_zero Q α β)
  simp only [Category.assoc] at h ⊢
  rw [h]
  change (topFunctional Q α).app ⊤ (q.app ⊤ (freeVector X j))=
    evalAt Q α (quotientVector q ⊤ j)
  rw [topFunctional_top]
  congr 1
  simp [quotientVector]

theorem twoFunctionals_matrix_one {Q : X.Modules} (q : freeOn X 6 ⟶ Q)
    (α β : Γ(dualSheaf Q,⊤)) (j : Fin 6) :
    Stacks.FreeSheafMatrix.toMatrix (q ≫ twoFunctionals Q α β) 1 j=
      coefficientMap q ⊤ β j := by
  change Stacks.FreeSheafMatrix.unitEndValue
    (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up.{u} j) ≫ (q ≫ twoFunctionals Q α β) ≫
      SheafOfModules.freeProjection (R := X.ringCatSheaf) (ULift.up.{u} (1 : Fin 2)))= _
  have h := congrArg (fun g : Q ⟶ SheafOfModules.unit X.ringCatSheaf =>
    Stacks.FreeSheafMatrix.unitEndValue
      (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up.{u} j) ≫ q ≫ g))
      (twoFunctionals_projection_one Q α β)
  simp only [Category.assoc] at h ⊢
  rw [h]
  change (topFunctional Q β).app ⊤ (q.app ⊤ (freeVector X j))=
    evalAt Q β (quotientVector q ⊤ j)
  rw [topFunctional_top]
  congr 1
  simp [quotientVector]

def area (R : Type u) [CommRing R] : (⋀[R]^2 (Fin 2 → R)) →ₗ[R] R :=
  exteriorPower.pairingDual R (Fin 2 → R) 2
    (exteriorPower.ιMulti R 2 ![LinearMap.proj 0,LinearMap.proj 1])

@[simp] theorem area_wedge (R : Type u) [CommRing R] (v w : Fin 2 → R) :
    area R (exteriorPower.ιMulti R 2 ![v,w])=v 0*w 1-v 1*w 0 := by
  simp [area,Matrix.det_fin_two]

/-- Actual exterior annihilation of a free rank-two target implies
actual isotropy of its two coefficient rows. -/
theorem freeTwo_rows_isotropic (q : freeOn X 6 ⟶ freeOn X 2)
    (hq : AnnihilatesSigma X q) :
    LagrangianCotangentFormula.symplecticPair
      (Stacks.FreeSheafMatrix.toMatrix q 0) (Stacks.FreeSheafMatrix.toMatrix q 1)=0 := by
  let M := Stacks.FreeSheafMatrix.toMatrix q
  have hmod : (∑ i : Fin 3,exteriorPower.ιMulti Γ(X,⊤) 2
      ![fun r => M r (i.castAdd 3),fun r => M r (Fin.natAdd 3 i)])=0 := by
    apply (freeExteriorSectionsEquiv X 2 2).injective
    rw [map_sum,map_zero]
    have hcol (j : Fin 6) :
        (freeSectionCoordinates X 2).symm (fun r => M r j)=q.app ⊤ (freeVector X j) := by
      apply (freeSectionCoordinates X 2).injective
      funext r
      rw [LinearEquiv.apply_symm_apply]
      exact (freeCoordinates_map_basis q r j).symm
    calc
      _ = ∑ i : Fin 3,ExteriorEvaluation.sectionComparison (freeOn X 2) 2 ⊤
          (exteriorPower.ιMulti Γ(X,⊤) 2
            ![q.app ⊤ (freeVector X (i.castAdd 3)),q.app ⊤ (freeVector X (Fin.natAdd 3 i))]) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [freeExteriorSectionsEquiv_ιMulti]
        congr 2
        funext j
        fin_cases j <;> exact hcol _
      _ = (exteriorPowerMap X q 2).app ⊤ (sigmaSection X) := by
        simp only [sigmaSection,map_sum,exteriorPowerMap_wedgeSection,
          ExteriorEvaluation.sectionComparison_ιMulti]
        rfl
      _ = 0 := hq
  have h := congrArg (area Γ(X,⊤)) hmod
  simpa only [map_sum,map_zero,area_wedge,LagrangianCotangentFormula.symplecticPair,M,mul_comm] using h

/-- The original dual coefficients of an actual exterior-isotropic
quotient are isotropic. No freeness or rank of the quotient is assumed. -/
theorem coefficientMap_top_isotropic {Q : X.Modules} (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) (α β : Γ(dualSheaf Q,⊤)) :
    LagrangianCotangentFormula.symplecticPair (coefficientMap q ⊤ α) (coefficientMap q ⊤ β)=0 := by
  have h := freeTwo_rows_isotropic (q ≫ twoFunctionals Q α β)
    (annihilatesSigma_postcomp q (twoFunctionals Q α β) hq)
  have h0 : Stacks.FreeSheafMatrix.toMatrix (q ≫ twoFunctionals Q α β) 0=coefficientMap q ⊤ α :=
    funext (twoFunctionals_matrix_zero q α β)
  have h1 : Stacks.FreeSheafMatrix.toMatrix (q ≫ twoFunctionals Q α β) 1=coefficientMap q ⊤ β :=
    funext (twoFunctionals_matrix_one q α β)
  rwa [h0,h1] at h

end M9Native.LagrangianIsotropicDual
