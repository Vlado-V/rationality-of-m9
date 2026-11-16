module

public import M9StacksIntegration.LagrangianFixedEquationRows

/-!
# Actual framed pullback of a finite linear combination

The unit-sheaf scalar action is normalized on abstract schemes before
specialization to an actual LG chart and determinant line. All maps are
the original global-section pullback and the actual supplied frame.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

universe u v
namespace M9Native.MukaiFramedSectionSum

/-- Read the original pulled section in an actual unit-sheaf frame. -/
def framedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    (e : (Scheme.Modules.pullback f).obj L ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (s : Γ(L,⊤)) : Γ(X,⊤) :=
  e.hom.app ⊤ (pullbackGlobalSections f L s)

/-- The actual frame of the actual pulled linear combination, with
the scalar action converted to structure-ring multiplication while
the ambient schemes and sheaf remain abstract. -/
theorem framedPullback_sum_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    (e : (Scheme.Modules.pullback f).obj L ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (c : ι → Γ(Y,⊤)) (s : ι → Γ(L,⊤)) :
    framedPullback f L e (∑ j : ι, c j • s j) =
      ∑ j : ι, f.appTop (c j) * framedPullback f L e (s j) := by
  unfold framedPullback
  simp only [map_sum, SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul]
  rfl

/-- The original base scalar retains its actual composite structure
map under the actual global-section pullback. -/
theorem scalarMap_pullback (K : Type u) [Field K] {X Y : Scheme.{u}}
    (b : Y ⟶ Spec (.of K)) (f : X ⟶ Y) (q : X ⟶ Spec (.of K))
    (hf : f ≫ b = q) (c : K) :
    f.appTop (LagrangianSymplecticAction.scalarMap K b c) =
      LagrangianSymplecticAction.scalarMap K q c :=
  (RingHom.congr_fun (LagrangianSymplecticAction.scalarMap_comp K b f) c).symm.trans
    (congrArg (fun t : X ⟶ Spec (.of K) => LagrangianSymplecticAction.scalarMap K t c) hf)

end M9Native.MukaiFramedSectionSum
