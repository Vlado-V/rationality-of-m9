module

public import M9StacksIntegration.ConstantMapPullback
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Restrict

/-! An actual affine open cover with rank-two frames is constructed from
genuine finite local freeness. The cover, its affine sources and all
pullback frames are produced; no local frame or cover is an input. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.FiniteLocallyFreeAffineFrameCover

theorem exists_affine_frames {X : Scheme.{u}} (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2] :
    ∃ U : Scheme.AffineOpenCover.{u} X,
      ∀ i : U.I₀, Nonempty ((Scheme.Modules.pullback (U.f i)).obj F ≅
        SheafOfModules.free (R := (Spec (U.X i)).ringCatSheaf) (ULift.{u} (Fin 2))) := by
  classical
  have hlocal := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff F 2).mpr inferInstance
  choose V hV e using hlocal
  have hcover : IsOpenCover V :=
    eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hV x⟩
  let C : Scheme.OpenCover.{u} X := X.openCoverOfIsOpenCover V hcover
  have hframe (i : C.I₀) : (Scheme.Modules.pullback (C.f i)).obj F ≅
      SheafOfModules.free (R := (C.X i).ringCatSheaf) (ULift.{u} (Fin 2)) :=
    ((Scheme.Modules.restrictFunctorIsoPullback (V i).ι).app F).symm ≪≫ (e i).some
  let A : Scheme.AffineOpenCover.{u} X := C.affineRefinement
  let R : A.openCover ⟶ C := C.fromAffineRefinement
  refine ⟨A, fun i => ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackCongr (R.w₀ i)).symm.app F ≪≫
    (Scheme.Modules.pullbackComp (R.h₀ i) (C.f (R.s₀ i))).symm.app F ≪≫
    (Scheme.Modules.pullback (R.h₀ i)).mapIso (hframe (R.s₀ i)) ≪≫
    AlgebraicGeometry.Grassmannian.pullbackFreeIso (R.h₀ i) 2

/-- The actual chosen native open cover, constructed from rank two. -/
def frameCover {X : Scheme.{u}} (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2] : Scheme.OpenCover.{u} X :=
  (exists_affine_frames F).choose.openCover

/-- Every actual source of the produced native cover is affine. -/
instance frameCover_isAffine {X : Scheme.{u}} (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    (i : (frameCover F).I₀) : IsAffine ((frameCover F).X i) := by
  change IsAffine (Spec ((exists_affine_frames F).choose.X i))
  infer_instance

/-- An actual pullback frame on every produced affine cover member. -/
def frame {X : Scheme.{u}} (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    (i : (frameCover F).I₀) :
    (Scheme.Modules.pullback ((frameCover F).f i)).obj F ≅
      SheafOfModules.free (R := ((frameCover F).X i).ringCatSheaf) (ULift.{u} (Fin 2)) :=
  ((exists_affine_frames F).choose_spec i).some

end M9Native.FiniteLocallyFreeAffineFrameCover
