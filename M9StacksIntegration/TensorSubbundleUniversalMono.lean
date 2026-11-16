module

public import M9StacksIntegration.VectorBundleKZeroPullbackAdd
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge

/-! A genuine subbundle stays monomorphic after right tensoring by an
actual invertible line and after every scheme pullback. Exactness is
derived from the original short exact sequence and its locally free
quotient, rather than supplied as universal injectivity. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf

namespace M9Native.TensorSubbundleUniversalMono
variable {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
  (hQ : SheafOfModules.IsFiniteLocallyFree.{u,u,u} S.X₃) (L : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

def tensorRight : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj L

instance tensorRight_isEquivalence : (tensorRight L).IsEquivalence :=
  Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    X.presheaf X.ringCatSheaf.2 L

include hS in
theorem tensor_shortExact : (S.map (tensorRight L)).ShortExact :=
  hS.map_of_exact (tensorRight L)

include hQ in
theorem tensor_quotient_finiteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} ((S.map (tensorRight L)).X₃) := by
  have hQs := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry S.X₃).mpr hQ
  have hLs := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L).mpr
    (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1)
  exact (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).mp
    (@AlgebraicGeometry.isFiniteLocallyFree_tensorObj X S.X₃ L hQs hLs)

include hS hQ in
/-- The SAME original tensor map remains monic on every test scheme,
including schemes with nilpotents. -/
theorem mono_pullback_tensor {T : Scheme.{u}} (f : T ⟶ X) :
    Mono ((Scheme.Modules.pullback f).map ((tensorRight L).map S.f)) :=
  (VectorBundleKZeroPullbackAdd.shortExact_pullback f (S.map (tensorRight L))
    (tensor_shortExact S hS L) (tensor_quotient_finiteLocallyFree S hQ L)).mono_f

end M9Native.TensorSubbundleUniversalMono
