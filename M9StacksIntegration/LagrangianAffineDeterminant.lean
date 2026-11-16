module

public import M9StacksIntegration.LagrangianPluckerQuotient
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis

/-! Thin affine determinant-line trivialization. The affine-isomorphism
criterion is the exact proof of the pinned native AffineIsoCriterion:82–104;
its two actual green imports suffice, without the projective-bundle header. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
namespace M9Native.LagrangianAffineDeterminant
open M9Native.LagrangianMatrixChart M9Native.LagrangianDeterminantSections
open Stacks.AlgebraicGeometry.AffineBaseChange Stacks.AlgebraicGeometry

/-- The actual affine quasi-coherent isomorphism criterion, with the
literal native proof and no extra projective-bundle prerequisites. -/
theorem isIso_of_isIso_app_top {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (h : IsIso (φ.app ⊤)) : IsIso φ := by
  have hψ : IsIso (φ.app ((isAffineOpen_top X).fromSpec ''ᵁ
      (⊤ : (Spec Γ(X, ⊤)).Opens))) := by
    rw [ModuleLimits.image_top_fromSpec]; exact h
  have hbij : Function.Bijective (ConcreteCategory.hom
      (((Scheme.Modules.restrictFunctor (isAffineOpen_top X).fromSpec).map φ).app ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hψ
  have hΓ : IsIso ((moduleSpecΓFunctor (R := Γ(X, ⊤))).map
      ((Scheme.Modules.restrictFunctor (isAffineOpen_top X).fromSpec).map φ)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hres : IsIso ((Scheme.Modules.restrictFunctor (isAffineOpen_top X).fromSpec).map φ) :=
    isIso_of_isIso_moduleSpecΓ _ hΓ
  exact @isIso_of_reflects_iso _ _ _ _ _ _ φ
    (Scheme.Modules.restrictFunctor (isAffineOpen_top X).fromSpec) hres
    (reflectsIsomorphisms_of_full_and_faithful _)

theorem presheaf_map_top_apply {X : Scheme.{u}} (M : X.Modules)
    (a : op (⊤ : X.Opens) ⟶ op (⊤ : X.Opens)) (t : Γ(M,⊤)) :
    M.presheaf.map a t=t := by
  rw [Subsingleton.elim a (𝟙 _),M.presheaf.map_id,ConcreteCategory.id_apply]

/-- The actual morphism attached to a section sends the unit to that section.
This is the pointwise argument in native UnitSplitting:444–450. -/
theorem unitHom_top_one {X : Scheme.{u}} (M : X.Modules) (a : Γ(M,⊤)) :
    (Scheme.Modules.unitHomEquivTop M a).app ⊤ (1 : Γ(X,⊤))=a := by
  have h2 : (Scheme.Modules.unitHomEquivTop M a).app ⊤ (1 : Γ(X,⊤))=
      (SheafOfModules.unitHomEquiv M (Scheme.Modules.unitHomEquivTop M a)).val (op ⊤) := rfl
  rw [h2,Scheme.Modules.unitHomEquiv_unitHomEquivTop,Scheme.Modules.sectionsTopEquiv_val]
  exact presheaf_map_top_apply M _ _

theorem unitHom_top_smul {X : Scheme.{u}} (M : X.Modules) (a : Γ(M,⊤)) (r : Γ(X,⊤)) :
    (Scheme.Modules.unitHomEquivTop M a).app ⊤ r=r • a := by
  have h : r=r • (1 : Γ(X,⊤)) := by simp
  calc
    _ = (Scheme.Modules.unitHomEquivTop M a).app ⊤ (r • (1 : Γ(X,⊤))) :=
      congrArg ((Scheme.Modules.unitHomEquivTop M a).app ⊤) h
    _ = r • a := by rw [Scheme.Modules.Hom.app_smul,unitHom_top_one]

variable (X : Scheme.{u})

def determinantVolume : Γ(Scheme.Modules.exteriorPower (freeOn X 3) 3,⊤) :=
  freeExteriorSectionsEquiv X 3 3 (volume Γ(X,⊤))

@[simp] theorem determinantVolume_coordinate :
    freeDeterminantCoordinates X (determinantVolume X)=1 := by
  change topEquiv Γ(X,⊤) ((freeExteriorSectionsEquiv X 3 3).symm
    (freeExteriorSectionsEquiv X 3 3 (volume Γ(X,⊤))))=1
  rw [LinearEquiv.symm_apply_apply,topEquiv_apply,topCoordinate_volume]

def determinantUnitMap : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
    Scheme.Modules.exteriorPower (freeOn X 3) 3 :=
  Scheme.Modules.unitHomEquivTop _ (determinantVolume X)

@[simp] theorem determinantUnitMap_coordinate (r : Γ(X,⊤)) :
    freeDeterminantCoordinates X (Scheme.Modules.Hom.app (determinantUnitMap X) ⊤ r)=r := by
  calc
    _ = freeDeterminantCoordinates X (r • determinantVolume X) :=
      congrArg (freeDeterminantCoordinates X)
        (unitHom_top_smul (Scheme.Modules.exteriorPower (freeOn X 3) 3) (determinantVolume X) r)
    _ = r := by rw [map_smul,determinantVolume_coordinate,smul_eq_mul,mul_one]

theorem determinantUnitMap_top_bijective : Function.Bijective (Scheme.Modules.Hom.app (determinantUnitMap X) ⊤) := by
  constructor
  · intro r s h
    simpa only [determinantUnitMap_coordinate] using congrArg (freeDeterminantCoordinates X) h
  · intro w
    refine ⟨freeDeterminantCoordinates X w,?_⟩
    apply (freeDeterminantCoordinates X).injective
    rw [determinantUnitMap_coordinate]

instance determinantUnitMap_isIso [IsAffine X] : IsIso (determinantUnitMap X) := by
  have : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent := by infer_instance
  have hFree : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeOn X 3) 3 :=
    AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free (R:=X.ringCatSheaf) 3
  let := hFree
  have hTop : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower (freeOn X 3) 3) 1 := by
    simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower (freeOn X 3) 3 3
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Modules.exteriorPower (freeOn X 3) 3) := hTop.isFiniteLocallyFree
  have : (Scheme.Modules.exteriorPower (freeOn X 3) 3).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _
  exact isIso_of_isIso_app_top _ ((ConcreteCategory.isIso_iff_bijective _).mpr
    (determinantUnitMap_top_bijective X))

/-- The actual affine determinant-line isomorphism, not only a global-section equivalence. -/
def affineDeterminantIso [IsAffine X] : Scheme.Modules.exteriorPower (freeOn X 3) 3 ≅
    SheafOfModules.unit X.ringCatSheaf := (asIso (determinantUnitMap X)).symm


/-- The actual affine determinant-line isomorphism has the checked literal
canonical determinant coordinates on all global sections. -/
theorem affineDeterminantIso_coordinate [IsAffine X]
    (w : Γ(Scheme.Modules.exteriorPower (freeOn X 3) 3,⊤)) :
    Scheme.Modules.Hom.app (affineDeterminantIso X).hom ⊤ w=freeDeterminantCoordinates X w := by
  have h : Scheme.Modules.Hom.app (determinantUnitMap X) ⊤
      (Scheme.Modules.Hom.app (affineDeterminantIso X).hom ⊤ w)=w :=
    congrArg (fun φ : (Scheme.Modules.exteriorPower (freeOn X 3) 3) ⟶
      (Scheme.Modules.exteriorPower (freeOn X 3) 3) => Scheme.Modules.Hom.app φ ⊤ w)
      (asIso (determinantUnitMap X)).inv_hom_id
  simpa only [determinantUnitMap_coordinate] using congrArg (freeDeterminantCoordinates X) h

end M9Native.LagrangianAffineDeterminant
