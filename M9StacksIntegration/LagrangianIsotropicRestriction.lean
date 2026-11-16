module

public import M9StacksIntegration.LagrangianIsotropicDual
public import M9StacksIntegration.LagrangianFreeMatrixPullback
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictOpenSections
import all StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization

/-! Actual exterior-isotropic quotients under pullback and open restriction. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators

universe u

namespace M9Native.LagrangianIsotropicRestriction

open LagrangianGrassmannian LagrangianMatrixChart LagrangianIsotropicDual
open LagrangianFreeMatrixPullback AlgebraicGeometry.Grassmannian LagrangianPullback
open M9Native.SectionZeroIdealFactorization

variable {X Y : Scheme.{u}} {Q : X.Modules}

/-- Pullback of the original quotient, using the canonical free-bundle comparison. -/
def pulledQuotient (f : Y ⟶ X) (q : freeOn X 6 ⟶ Q) :
    freeOn Y 6 ⟶ (Scheme.Modules.pullback f).obj Q :=
  (pullbackFreeIso f 6).inv ≫ (Scheme.Modules.pullback f).map q

theorem pulledQuotient_basis (f : Y ⟶ X) (q : freeOn X 6 ⟶ Q) (j : Fin 6) :
    (pulledQuotient f q).app ⊤ (freeVector Y j)=
      pullbackGlobalSections f Q (q.app ⊤ (freeVector X j)) := by
  change ((Scheme.Modules.pullback f).map q).app ⊤
    ((pullbackFreeIso f 6).inv.app ⊤ (freeVector Y j))=_
  rw [inverse_freeVector_pullback,pullback_map_app_pullbackGlobalSections]

/-- The actual defining bivector image, after canonical pullback. -/
theorem pulledQuotient_sigma (f : Y ⟶ X) (q : freeOn X 6 ⟶ Q) :
    (exteriorPullbackIso f Q 2).hom.app ⊤
      (pullbackGlobalSections f (Scheme.Modules.exteriorPower Q 2)
        ((exteriorPowerMap X q 2).app ⊤ (sigmaSection X)))=
      (exteriorPowerMap Y (pulledQuotient f q) 2).app ⊤ (sigmaSection Y) := by
  let s := pullbackGlobalSections f (Scheme.Modules.exteriorPower (freeOn X 6) 2)
    (sigmaSection X)
  let t := (exteriorPullbackIso f (freeOn X 6) 2).hom.app ⊤ s
  have hn : (Scheme.Modules.pullback f).map (exteriorPowerMap X q 2) ≫
        (exteriorPullbackIso f Q 2).hom=
      (exteriorPullbackIso f (freeOn X 6) 2).hom ≫
        exteriorPowerMap Y ((Scheme.Modules.pullback f).map q) 2 := by
    simpa only [exteriorPowerMap_eq_native] using exteriorPullbackIso_natural f q 2
  have hc : exteriorPowerMap Y (pullbackFreeIso f 6).hom 2 ≫
      exteriorPowerMap Y (pulledQuotient f q) 2=
      exteriorPowerMap Y ((Scheme.Modules.pullback f).map q) 2 := by
    simp only [exteriorPowerMap_eq_native,← Scheme.Modules.exteriorPowerMap_comp]
    congr 1
    exact Iso.hom_inv_id_assoc _ _
  calc
    _ = (exteriorPullbackIso f Q 2).hom.app ⊤
        (((Scheme.Modules.pullback f).map (exteriorPowerMap X q 2)).app ⊤ s) :=
      congrArg ((exteriorPullbackIso f Q 2).hom.app ⊤)
        (pullback_map_app_pullbackGlobalSections f (exteriorPowerMap X q 2) (sigmaSection X)).symm
    _ = (exteriorPowerMap Y ((Scheme.Modules.pullback f).map q) 2).app ⊤ t :=
      congrArg (fun φ => φ.app ⊤ s) hn
    _ = _ := by
      rw [← sigmaSection_pullback f]
      exact (congrArg (fun φ => φ.app ⊤ t) hc).symm

/-- Exterior-isotropy is preserved by actual scheme pullback. -/
theorem pulledQuotient_annihilates (f : Y ⟶ X) (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) : AnnihilatesSigma Y (pulledQuotient f q) := by
  rw [AnnihilatesSigma,← pulledQuotient_sigma]
  rw [show (exteriorPowerMap X q 2).app ⊤ (sigmaSection X)=0 from hq,map_zero,map_zero]

/-- The original quotient restricted to the literal open subscheme. -/
def restrictedQuotient (q : freeOn X 6 ⟶ Q) (U : X.Opens) :
    freeOn (U : Scheme.{u}) 6 ⟶ Q.restrict U.ι :=
  pulledQuotient U.ι q ≫ ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app Q).inv

theorem restrictedQuotient_annihilates (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) (U : X.Opens) :
    AnnihilatesSigma (U : Scheme.{u}) (restrictedQuotient q U) :=
  annihilatesSigma_postcomp _ _ (pulledQuotient_annihilates U.ι q hq)

/-- The literal restricted quotient has the original restricted basis images. -/
theorem restrictedQuotient_basis (q : freeOn X 6 ⟶ Q) (U : X.Opens) (j : Fin 6) :
    (openSectionsIso Q U).hom
      ((restrictedQuotient q U).app ⊤ (freeVector (U : Scheme.{u}) j))=
      LagrangianDualCoefficients.quotientVector q U j := by
  change (openSectionsIso Q U).hom
    ((((Scheme.Modules.restrictFunctorIsoPullback U.ι).app Q).inv).app ⊤
      ((pulledQuotient U.ι q).app ⊤ (freeVector (U : Scheme.{u}) j)))=_
  rw [pulledQuotient_basis,← Stacks.Divisors.pullbackGlobalSections_open]
  change (openSectionsIso Q U).hom
    ((((Scheme.Modules.restrictFunctorIsoPullback U.ι).app Q).hom ≫
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app Q).inv).app ⊤
        (Q.presheaf.map (homOfLE le_top).op (q.app ⊤ (freeVector X j))))=_
  rw [Iso.hom_inv_id]
  change Q.presheaf.map (eqToHom U.ι_image_top.symm).op
    (Q.presheaf.map (homOfLE le_top).op (q.app ⊤ (freeVector X j)))=_
  rw [← ConcreteCategory.comp_apply,← Q.presheaf.map_comp]
  rfl

end M9Native.LagrangianIsotropicRestriction
