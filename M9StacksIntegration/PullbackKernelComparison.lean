module

public import M9StacksIntegration.SheafFieldKernelObstruction

/-!
# Actual kernels under the native iterated-pullback comparison

The actual kernel on sections of `p*(π*v)` is canonically isomorphic to
the kernel on sections of `(p ≫ π)*v`. This uses naturality of the
genuine scheme-module pullback composition isomorphism. It lets the
Picard fiber calculation, stated for a single composite point, feed the
actual incidence calculation, stated for two successive pullbacks.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.PullbackKernelComparison

/-- A genuine commuting square with isomorphisms gives an actual
linear equivalence of the two actual linear kernels. -/
def kernelEquivOfIsoSquare (K : Type u) [Field K]
    {A B A' B' : ModuleCat.{u} K} (v : A ⟶ B) (w : A' ⟶ B')
    (eA : A ≅ A') (eB : B ≅ B') (h : v ≫ eB.hom = eA.hom ≫ w) :
    LinearMap.ker v.hom ≃ₗ[K] LinearMap.ker w.hom := by
  let a := eA.toLinearEquiv
  let b := eB.toLinearEquiv
  have hc (x : A) : b (v.hom x) = w.hom (a x) :=
    congrArg (fun f => f.hom x) h
  exact
    { toFun := fun x => ⟨a x, by
        change w.hom (a x.1) = 0
        rw [← hc, x.2, map_zero]⟩
      invFun := fun y => ⟨a.symm y, by
        change v.hom (a.symm y.1) = 0
        apply b.injective
        rw [map_zero, hc, a.apply_symm_apply, y.2]⟩
      left_inv := fun x => Subtype.ext (a.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (a.apply_symm_apply y.1)
      map_add' := fun x y => Subtype.ext (a.map_add x.1 y.1)
      map_smul' := fun c x => Subtype.ext (a.map_smul c x.1) }

/-- The actual native scheme-module composition comparison induces
an actual linear equivalence on field-valued section kernels. -/
def iteratedPullbackKernelEquiv (K : Type u) [Field K]
    {X Y : Scheme.{u}} (p : Spec (.of K) ⟶ Y) (π : Y ⟶ X)
    {E F : X.Modules} (v : E ⟶ F) :
    LinearMap.ker (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      ((Scheme.Modules.pullback π).map v))).hom ≃ₗ[K]
      LinearMap.ker (moduleSpecΓFunctor.map ((Scheme.Modules.pullback (p ≫ π)).map v)).hom :=
  kernelEquivOfIsoSquare K _ _
    (moduleSpecΓFunctor.mapIso ((Scheme.Modules.pullbackComp p π).app E))
    (moduleSpecΓFunctor.mapIso ((Scheme.Modules.pullbackComp p π).app F))
    (by
      change moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
          ((Scheme.Modules.pullback π).map v)) ≫
          moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp p π).hom.app F) =
        moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp p π).hom.app E) ≫
          moduleSpecΓFunctor.map ((Scheme.Modules.pullback (p ≫ π)).map v)
      have h := congrArg (fun f => moduleSpecΓFunctor.map f)
        ((Scheme.Modules.pullbackComp p π).hom.naturality v)
      simpa only [Functor.map_comp, Functor.comp_map] using h)

/-- Iterated and composite pullback give the same actual kernel
dimension, without a finiteness or rank assumption. -/
theorem finrank_iteratedPullbackKernel (K : Type u) [Field K]
    {X Y : Scheme.{u}} (p : Spec (.of K) ⟶ Y) (π : Y ⟶ X)
    {E F : X.Modules} (v : E ⟶ F) :
    Module.finrank K (LinearMap.ker (moduleSpecΓFunctor.map
      ((Scheme.Modules.pullback p).map ((Scheme.Modules.pullback π).map v))).hom) =
      Module.finrank K (LinearMap.ker
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullback (p ≫ π)).map v)).hom) :=
  (iteratedPullbackKernelEquiv K p π v).finrank_eq

end M9Native.PullbackKernelComparison
