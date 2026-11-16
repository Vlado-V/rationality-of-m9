module

public import M9StacksIntegration.FreeTwoSelectedPairIso
public import M9StacksIntegration.FreeTwoPairIncidenceBaseChange
public import M9StacksIntegration.RankTwoSelectedPairUnitCover
public import M9StacksIntegration.FreeTwoWedgeDeterminant
public import M9StacksIntegration.FiniteLocallyFreeAffineFrameCover

/-! A selected pair of the original epimorphism O3 to a rank-two
bundle has incidence isomorphic to its base whenever its full actual
wedge vanishes. Unit pivots are produced on the original entry opens;
all comparisons and gluing retain the original scheme structure. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf
namespace M9Native.RankTwoSelectedPairIncidenceIso
open LagrangianMatrixChart FreeTwoProjectiveCharts

variable {X : Scheme.{u}} {F : X.Modules}
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
  (phi : freeOn X 3 ⟶ F) [Epi phi] (e : Fin 2 ↪ Fin 3)

def selectedSections : Fin 2 → Γ(F,⊤) := fun k => phi.app ⊤ (freeBasisSection X 3 (e k))

variable (eF : F ≅ freeOn X 2)

variable {Y : Scheme.{u}} (g : Y ⟶ X)

def localTargetIso : freeOn Y 2 ≅ (Scheme.Modules.pullback g).obj F :=
  (AlgebraicGeometry.Grassmannian.pullbackFreeIso g 2).symm ≪≫
    (Scheme.Modules.pullback g).mapIso eF.symm

theorem localSections_eq_column (k : Fin 2) :
    FreeTwoPairIncidenceBaseChange.sections g F (freeOn Y 2) (localTargetIso eF g)
      (selectedSections phi e) k =
    (GrassmannianFixedLineSheaf.pulledMap g (phi ≫ eF.hom)).app ⊤
      (freeBasisSection Y 3 (e k)) := by
  change (AlgebraicGeometry.Grassmannian.pullbackFreeIso g 2).hom.app ⊤
    (((Scheme.Modules.pullback g).map eF.hom).app ⊤
      (pullbackGlobalSections g F (phi.app ⊤ (freeBasisSection X 3 (e k))))) = _
  rw [SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections]
  symm
  change (AlgebraicGeometry.Grassmannian.pullbackFreeIso g 2).hom.app ⊤
    (((Scheme.Modules.pullback g).map (phi ≫ eF.hom)).app ⊤
      ((AlgebraicGeometry.Grassmannian.pullbackFreeIso g 3).inv.app ⊤
        (freeBasisSection Y 3 (e k)))) = _
  rw [FiniteFreeBasisPullback.inverse_freeBasisSection_pullback,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections]
  rfl

theorem localMatrix_eq :
    RankTwoUnitPivotColumns.sectionMatrix Y (Iso.refl (freeOn Y 2))
      (FreeTwoPairIncidenceBaseChange.sections g F (freeOn Y 2) (localTargetIso eF g)
        (selectedSections phi e)) =
    (((Stacks.FreeSheafMatrix.toMatrix (phi ≫ eF.hom)).submatrix id e).map g.appTop.hom) := by
  ext i j
  change freeSectionCoordinates Y 2
    (FreeTwoPairIncidenceBaseChange.sections g F (freeOn Y 2) (localTargetIso eF g)
      (selectedSections phi e) j) i =
    g.appTop (Stacks.FreeSheafMatrix.toMatrix (phi ≫ eF.hom) i (e j))
  rw [localSections_eq_column]
  have hc : freeSectionCoordinates Y 2
      ((GrassmannianFixedLineSheaf.pulledMap g (phi ≫ eF.hom)).app ⊤
        (freeBasisSection Y 3 (e j))) i =
      Stacks.FreeSheafMatrix.toMatrix (GrassmannianFixedLineSheaf.pulledMap g (phi ≫ eF.hom)) i (e j) :=
    freeCoordinates_map_basis (GrassmannianFixedLineSheaf.pulledMap g (phi ≫ eF.hom)) i (e j)
  exact hc.trans (congrFun (congrFun (GrassmannianFixedLineSheaf.pulledMap_matrix g (phi ≫ eF.hom)) i) (e j))

include eF in
/-- The affine framed case uses the actual four selected-entry opens.
The determinant is derived from the actual original wedge equation. -/
theorem projection_isIso_affine [IsAffine X]
    (hw : LagrangianGrassmannian.wedgeSection X F
      (selectedSections phi e 0) (selectedSections phi e 1) = 0) :
    IsIso (FreeTwoPairIncidence.toBase X F (selectedSections phi e)) := by
  let U := X.openCoverOfIsOpenCover (RankTwoSelectedPairUnitCover.entryOpen X phi eF e)
    (RankTwoSelectedPairUnitCover.entryOpens_cover X phi eF e)
  apply IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme) U
  intro ij
  let g := U.f ij
  let B := FreeTwoPairIncidenceBaseChange.sections g F (freeOn (U.X ij) 2)
    (localTargetIso eF g) (selectedSections phi e)
  have hmatrix := localMatrix_eq phi e eF g
  have hdet : (RankTwoUnitPivotColumns.sectionMatrix (U.X ij)
      (Iso.refl (freeOn (U.X ij) 2)) B).det = 0 := by
    rw [hmatrix]
    have hh := congrArg g.appTop.hom
      (FreeTwoWedgeDeterminant.selectedMatrix_det_eq_zero X phi eF e hw)
    simpa only [RingHom.map_det,RingHom.mapMatrix_apply,map_zero] using hh
  have hunit : IsUnit (g.appTop (RankTwoSelectedPairUnitCover.entry X phi eF e ij)) :=
    RankTwoSelectedPairUnitCover.entry_isUnit X phi eF e ij
  obtain ⟨a,ha⟩ := hunit
  have hpivot : RankTwoUnitPivotColumns.sectionMatrix (U.X ij)
      (Iso.refl (freeOn (U.X ij) 2)) B ij.1 ij.2 = (a : Γ(U.X ij,⊤)) := by
    have hm := congrFun (congrFun hmatrix ij.1) ij.2
    exact hm.trans ha.symm
  letI := FreeTwoSelectedPairIso.projection_isIso (U.X ij) (Iso.refl (freeOn (U.X ij) 2))
    B ij.1 ij.2 a hdet hpivot
  let d := FreeTwoPairIncidenceBaseChange.baseChangeIso g F (freeOn (U.X ij) 2)
    (localTargetIso eF g) 2 (selectedSections phi e)
  letI : IsIso (d.hom ≫ pullback.fst g (FreeTwoPairIncidence.toBase X F (selectedSections phi e))) := by
    rw [FreeTwoPairIncidenceBaseChange.baseChangeIso_hom_fst]
    infer_instance
  letI : IsIso (pullback.fst g (FreeTwoPairIncidence.toBase X F (selectedSections phi e))) :=
    IsIso.of_isIso_comp_left d.hom _
  have hcov : IsPullback (U.pullbackHom (FreeTwoPairIncidence.toBase X F (selectedSections phi e)) ij)
      ((U.pullback₁ (FreeTwoPairIncidence.toBase X F (selectedSections phi e))).f ij)
      (U.f ij) (FreeTwoPairIncidence.toBase X F (selectedSections phi e)) :=
    (IsPullback.of_hasPullback (FreeTwoPairIncidence.toBase X F (selectedSections phi e)) (U.f ij)).flip
  rw [← hcov.isoPullback_hom_fst]
  infer_instance

def pulledEvaluation : freeOn Y 3 ⟶ (Scheme.Modules.pullback g).obj F :=
  (AlgebraicGeometry.Grassmannian.pullbackFreeIso g 3).inv ≫ (Scheme.Modules.pullback g).map phi

instance pulledEvaluation_epi : Epi (pulledEvaluation phi g) := by
  dsimp [pulledEvaluation]
  infer_instance

theorem pulledEvaluation_basis (k : Fin 3) :
    (pulledEvaluation phi g).app ⊤ (freeBasisSection Y 3 k) =
      pullbackGlobalSections g F (phi.app ⊤ (freeBasisSection X 3 k)) := by
  change ((Scheme.Modules.pullback g).map phi).app ⊤
    ((AlgebraicGeometry.Grassmannian.pullbackFreeIso g 3).inv.app ⊤
      (freeBasisSection Y 3 k)) = _
  rw [FiniteFreeBasisPullback.inverse_freeBasisSection_pullback,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections]

/-- On an arbitrary scheme the genuine affine frame cover, and then
the genuine four entry opens, glue the actual local isomorphisms. -/
theorem projection_isIso
    (hw : LagrangianGrassmannian.wedgeSection X F
      (selectedSections phi e 0) (selectedSections phi e 1) = 0) :
    IsIso (FreeTwoPairIncidence.toBase X F (selectedSections phi e)) := by
  let U := FiniteLocallyFreeAffineFrameCover.frameCover F
  apply IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme) U
  intro i
  let g := U.f i
  let Fg := (Scheme.Modules.pullback g).obj F
  letI := isFiniteLocallyFreeOfRank_pullback g F 2
  have hwpull : LagrangianGrassmannian.wedgeSection (U.X i) Fg
      (selectedSections (pulledEvaluation phi g) e 0)
      (selectedSections (pulledEvaluation phi g) e 1) = 0 := by
    change LagrangianGrassmannian.wedgeSection (U.X i) Fg
      ((pulledEvaluation phi g).app ⊤ (freeBasisSection (U.X i) 3 (e 0)))
      ((pulledEvaluation phi g).app ⊤ (freeBasisSection (U.X i) 3 (e 1))) = 0
    have hw' : LagrangianGrassmannian.wedgeSection X F
        (phi.app ⊤ (freeBasisSection X 3 (e 0)))
        (phi.app ⊤ (freeBasisSection X 3 (e 1))) = 0 := hw
    rw [pulledEvaluation_basis,pulledEvaluation_basis,
      ← LagrangianGrassmannian.exteriorPullback_wedgeSection,hw',map_zero,map_zero]
  have hloc := projection_isIso_affine (pulledEvaluation phi g) e
    (FiniteLocallyFreeAffineFrameCover.frame F i) hwpull
  have hs : FreeTwoPairIncidenceBaseChange.sections g F Fg (Iso.refl Fg)
      (selectedSections phi e) = selectedSections (pulledEvaluation phi g) e := by
    funext k
    exact (pulledEvaluation_basis phi g (e k)).symm
  letI : IsIso (FreeTwoPairIncidence.toBase (U.X i) Fg
      (FreeTwoPairIncidenceBaseChange.sections g F Fg (Iso.refl Fg) (selectedSections phi e))) := by
    rw [hs]
    exact hloc
  let d := FreeTwoPairIncidenceBaseChange.baseChangeIso g F Fg (Iso.refl Fg) 2 (selectedSections phi e)
  letI : IsIso (d.hom ≫ pullback.fst g (FreeTwoPairIncidence.toBase X F (selectedSections phi e))) := by
    rw [FreeTwoPairIncidenceBaseChange.baseChangeIso_hom_fst]
    infer_instance
  letI : IsIso (pullback.fst g (FreeTwoPairIncidence.toBase X F (selectedSections phi e))) :=
    IsIso.of_isIso_comp_left d.hom _
  have hcov : IsPullback (U.pullbackHom (FreeTwoPairIncidence.toBase X F (selectedSections phi e)) i)
      ((U.pullback₁ (FreeTwoPairIncidence.toBase X F (selectedSections phi e))).f i)
      (U.f i) (FreeTwoPairIncidence.toBase X F (selectedSections phi e)) :=
    (IsPullback.of_hasPullback (FreeTwoPairIncidence.toBase X F (selectedSections phi e)) (U.f i)).flip
  rw [← hcov.isoPullback_hom_fst]
  infer_instance

def zeroIsoBase
    (hw : LagrangianGrassmannian.wedgeSection X F
      (selectedSections phi e 0) (selectedSections phi e 1) = 0) :
    FreeTwoPairIncidence.space X F (selectedSections phi e) ≅ X := by
  letI := projection_isIso phi e hw
  exact asIso (FreeTwoPairIncidence.toBase X F (selectedSections phi e))

theorem zeroIsoBase_hom
    (hw : LagrangianGrassmannian.wedgeSection X F
      (selectedSections phi e 0) (selectedSections phi e 1) = 0) :
    (zeroIsoBase phi e hw).hom = FreeTwoPairIncidence.toBase X F (selectedSections phi e) := rfl

end M9Native.RankTwoSelectedPairIncidenceIso
