module

public import M9StacksIntegration.NativeTensorLineTrivialization
public import M9StacksIntegration.SpecFieldStalkSections
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula

/-! The genuine native pullback-tensor coordinate isomorphism for a
trivialized point line, and its actual differential-map compatibility. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.pullback AlgebraicGeometry.moduleSpecΓFunctor
  Stacks.SheafOfModules.Tensor.ringSheaf
  M9Native.NativeTensorLineTrivialization.tensorRight

namespace M9Native.NativePullbackTensorLine

open MukaiBundleDeterminant (tensor)
open NativeTensorLineTrivialization (tensorRight untwistIso)

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

def pullbackTensorIso (A L : X.Modules) :
    (Scheme.Modules.pullback p).obj (tensor A L) ≅
      tensor ((Scheme.Modules.pullback p).obj A) ((Scheme.Modules.pullback p).obj L) :=
  Stacks.RingedSpace.pullbackTensorIsoApp p.toLRSHom.toShHom A L

theorem pullbackTensorIso_naturality {A B : X.Modules} (f : A ⟶ B) (L : X.Modules) :
    (Scheme.Modules.pullback p).map ((tensorRight L).map f) ≫
        (pullbackTensorIso p B L).hom =
      (pullbackTensorIso p A L).hom ≫
        (tensorRight ((Scheme.Modules.pullback p).obj L)).map
          ((Scheme.Modules.pullback p).map f) := by
  have h := (Stacks.RingedSpace.comparisonNatTrans p.toLRSHom.toShHom).naturality
    ((f, 𝟙 L) : ((A,L) : X.Modules × X.Modules) ⟶ (B,L))
  simp only [pullbackTensorIso,Stacks.RingedSpace.pullbackTensorIsoApp_hom,
    Stacks.RingedSpace.comparisonNatTrans_app,
    CategoryTheory.Functor.comp_map,CategoryTheory.Functor.uncurry_obj_map,
    CategoryTheory.Functor.prod_map,CategoryTheory.Functor.prod_obj,
    CategoryTheory.Functor.map_id,Category.comp_id] at h
  exact h

/-- The actual coordinate map is pullback of tensor followed by the
actual positive-line frame and the actual native right unit. -/
def sourceIso (A L : X.Modules)
    (τ : (Scheme.Modules.pullback p).obj L ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback p).obj (tensor A L) ≅ (Scheme.Modules.pullback p).obj A :=
  pullbackTensorIso p A L ≪≫
    untwistIso ((Scheme.Modules.pullback p).obj A) ((Scheme.Modules.pullback p).obj L) τ

theorem sourceIso_naturality {A B : X.Modules} (f : A ⟶ B) (L : X.Modules)
    (τ : (Scheme.Modules.pullback p).obj L ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback p).map ((tensorRight L).map f) ≫ (sourceIso p B L τ).hom =
      (sourceIso p A L τ).hom ≫ (Scheme.Modules.pullback p).map f := by
  simp only [sourceIso,Iso.trans_hom]
  rw [← Category.assoc,pullbackTensorIso_naturality,Category.assoc,
    NativeTensorLineTrivialization.untwistIso_naturality,Category.assoc]

section FieldPoint

variable (K : Type u) [Field K] {X : Scheme.{u}}
variable (p : SpecFieldStalkSections.space K ⟶ X)

/-- The same original cotangent input is read by the genuine source
coordinate isomorphism; no zero-image or differential comparison is assumed. -/
theorem map_zero_of_tensor_map_zero {A B : X.Modules} (f : A ⟶ B) (L : X.Modules)
    (τ : (Scheme.Modules.pullback p).obj L ≅
      SheafOfModules.unit (SpecFieldStalkSections.space K).ringCatSheaf)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (tensor A L)))
    (hx : (moduleSpecΓFunctor.map
      ((Scheme.Modules.pullback p).map ((tensorRight L).map f))).hom x = 0) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map f)).hom
      ((moduleSpecΓFunctor.map (sourceIso p A L τ).hom).hom x) = 0 := by
  have h := congrArg (fun t : (Scheme.Modules.pullback p).obj (tensor A L) ⟶
      (Scheme.Modules.pullback p).obj B => (moduleSpecΓFunctor.map t).hom x)
    (sourceIso_naturality p f L τ)
  have hh : (moduleSpecΓFunctor.map (sourceIso p B L τ).hom).hom
      ((moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback p).map ((tensorRight L).map f))).hom x) =
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map f)).hom
      ((moduleSpecΓFunctor.map (sourceIso p A L τ).hom).hom x) := by
    simp only [CategoryTheory.Functor.map_comp,ModuleCat.hom_comp,LinearMap.comp_apply] at h
    exact h
  exact hh.symm.trans ((congrArg
    (moduleSpecΓFunctor.map (sourceIso p B L τ).hom).hom hx).trans (map_zero _))

end FieldPoint

end M9Native.NativePullbackTensorLine
