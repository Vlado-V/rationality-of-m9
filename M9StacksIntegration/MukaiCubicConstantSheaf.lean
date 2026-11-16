module

public import M9StacksIntegration.MukaiPrimitiveQuartic
public import M9StacksIntegration.MukaiBundleTensor
public import M9StacksIntegration.LinearIncidenceTensorCoordinates
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorComparison

/-!
# The actual constant-sheaf cubic from the exterior quartic

The trilinear cubic is first linearized on the genuine tensor product over
the ground field. Its associated-sheaf map is then pulled back along the
actual structural morphism. The comparisons below are the canonical
tilde/tensor and pullback/tensor isomorphisms; their formulas on original
decomposable sections retain the cubic's literal normalization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped TensorProduct

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.MukaiCubicConstantSheaf

open MukaiBundleDeterminant MukaiPrimitiveQuartic
open LinearIncidenceTensorCoordinates SectionZeroIdealFactorization

variable (R : CommRingCat.{u}) {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- The genuine constant vector bundle attached to a ground-field module. -/
abbrev constantObj (M : ModuleCat.{u} R) : X.Modules :=
  (Scheme.Modules.pullback f).obj (tilde M)

def constantMap {M N : ModuleCat.{u} R} (a : M ⟶ N) :
    constantObj R f M ⟶ constantObj R f N :=
  (Scheme.Modules.pullback f).map (tilde.map a)

def constantSection (M : ModuleCat.{u} R) (m : M) : Γ(constantObj R f M, ⊤) :=
  pullbackGlobalSections f (tilde M) ((tilde.toOpen M ⊤).hom m)

theorem constantMap_section {M N : ModuleCat.{u} R} (a : M ⟶ N) (m : M) :
    (constantMap R f a).app ⊤ (constantSection R f M m) =
      constantSection R f N (a.hom m) := by
  unfold constantMap constantSection
  rw [pullback_map_app_pullbackGlobalSections]
  exact congrArg (fun z => pullbackGlobalSections f (tilde N) z)
    (TildeTensor.toOpen_map_app_apply a ⊤ m)

/-- Canonical tensor comparison, in the direction needed for the cubic. -/
def constantTensorIso (M N : ModuleCat.{u} R) :
    tensor (constantObj R f M) (constantObj R f N) ≅
      constantObj R f (ModuleCat.of R (M ⊗[R] N)) :=
  by
    let e₁ : (Scheme.Modules.pullback f).obj (tensor (tilde M) (tilde N)) ≅
        tensor (constantObj R f M) (constantObj R f N) :=
      Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f (tilde M) (tilde N)
    let e₂ : tensor (tilde M) (tilde N) ≅ tilde (ModuleCat.of R (M ⊗[R] N)) :=
      (TildeTensor.tildeTensorIso M N).symm
    exact e₁.symm ≪≫ (Scheme.Modules.pullback f).mapIso e₂

theorem constantTensorIso_inv_section (M N : ModuleCat.{u} R) (m : M) (n : N) :
    (constantTensorIso R f M N).inv.app ⊤
      (constantSection R f (ModuleCat.of R (M ⊗[R] N)) (m ⊗ₜ[R] n)) =
      tensorTop X (constantObj R f M) (constantObj R f N)
        (constantSection R f M m) (constantSection R f N n) := by
  change (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f (tilde M) (tilde N)).hom.app ⊤
    (((Scheme.Modules.pullback f).map (TildeTensor.tildeTensorIso M N).hom).app ⊤
      (pullbackGlobalSections f (tilde (ModuleCat.of R (M ⊗[R] N)))
        ((tilde.toOpen (ModuleCat.of R (M ⊗[R] N)) ⊤).hom (m ⊗ₜ[R] n)))) = _
  rw [pullback_map_app_pullbackGlobalSections]
  have hbase : (TildeTensor.tildeTensorIso M N).hom.app ⊤
      ((tilde.toOpen (ModuleCat.of R (M ⊗[R] N)) ⊤).hom (m ⊗ₜ[R] n)) =
      tensorTop (Spec R) (tilde M) (tilde N)
        ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n) :=
    TildeTensor.tildeTensorComparison_app_top M N (m ⊗ₜ[R] n)
  rw [hbase]
  exact Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt f
    (tilde M) (tilde N) _ _

theorem constantTensorIso_section (M N : ModuleCat.{u} R) (m : M) (n : N) :
    (constantTensorIso R f M N).hom.app ⊤
      (tensorTop X (constantObj R f M) (constantObj R f N)
        (constantSection R f M m) (constantSection R f N n)) =
      constantSection R f (ModuleCat.of R (M ⊗[R] N)) (m ⊗ₜ[R] n) := by
  have h := congrArg (fun z => (constantTensorIso R f M N).hom.app ⊤ z)
    (constantTensorIso_inv_section R f M N m n)
  have hcancel (z : Γ(constantObj R f (ModuleCat.of R (M ⊗[R] N)), ⊤)) :
      (constantTensorIso R f M N).hom.app ⊤
        ((constantTensorIso R f M N).inv.app ⊤ z) = z :=
    congrArg (fun a => a.app ⊤ z) (constantTensorIso R f M N).inv_hom_id
  exact h.symm.trans (hcancel _)

variable (K : Type u) [Field K] [CharZero K]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- Linearization of the actual three cubic arguments, with the displayed
left-associated tensor product. -/
def cubicTensorMap :
    ((Forms K ⊗[K] Forms K) ⊗[K] Forms K) →ₗ[K] Module.Dual K (Forms K) :=
  TensorProduct.lift (TensorProduct.lift (primitiveCubic K))

theorem cubicTensorMap_tmul (a b c : Forms K) :
    cubicTensorMap K ((a ⊗ₜ[K] b) ⊗ₜ[K] c) = primitiveCubic K a b c := rfl

abbrev formModule : ModuleCat.{u} K := ModuleCat.of K (Forms K)
abbrev dualFormModule : ModuleCat.{u} K := ModuleCat.of K (Module.Dual K (Forms K))

local instance formTensorAddCommGroup : AddCommGroup (Forms K ⊗[K] Forms K) :=
  TensorProduct.addCommGroup

local instance formCubeAddCommGroup :
    AddCommGroup ((Forms K ⊗[K] Forms K) ⊗[K] Forms K) :=
  TensorProduct.addCommGroup

def cubicModuleMap :
    ModuleCat.of K ((Forms K ⊗[K] Forms K) ⊗[K] Forms K) ⟶ dualFormModule K :=
  ModuleCat.ofHom (cubicTensorMap K)

/-- The actual global cubic on the constant bundle, defined without a
choice of a free basis or a local frame. -/
def cubicMap :
    tensor (tensor (constantObj (.of K) f (formModule K)) (constantObj (.of K) f (formModule K)))
      (constantObj (.of K) f (formModule K)) ⟶ constantObj (.of K) f (dualFormModule K) :=
  (tensorIso (constantTensorIso (.of K) f (formModule K) (formModule K))
    (Iso.refl (constantObj (.of K) f (formModule K)))).hom ≫
  (constantTensorIso (.of K) f (ModuleCat.of K (Forms K ⊗[K] Forms K)) (formModule K)).hom ≫
  constantMap (.of K) f (cubicModuleMap K)

theorem tensorIso_tensorTop {Y : Scheme.{u}} {A A' B B' : Y.Modules}
    (e : A ≅ A') (e' : B ≅ B') (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    (tensorIso e e').hom.app ⊤ (tensorTop Y A B a b) =
      tensorTop Y A' B' (e.hom.app ⊤ a) (e'.hom.app ⊤ b) := by
  change ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).map
    ((e.hom, e'.hom) : (A,B) ⟶ (A',B'))).val.app (op ⊤) (tensorTop Y A B a b) = _
  rw [Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map]
  unfold tensorTop Stacks.SheafOfModules.tensorSectionsAt
  refine (Stacks.SheafOfModules.toSheafify_app_map_obj
    (O := Y.sheaf.obj) (hO := Y.ringCatSheaf.property)
    (f := PresheafOfModules.tensorHom (O := Y.sheaf.obj) e.hom.val e'.hom.val)
    (op ⊤) (a ⊗ₜ b)).trans ?_
  exact congrArg (fun z =>
    (Stacks.SheafOfModules.TensorSheafification.toSheafify Y.sheaf.obj
      Y.ringCatSheaf.property (PresheafOfModules.tensorObj A'.val B'.val)).app (op ⊤) z)
    (PresheafOfModules.tensorHom_tmul (O := Y.sheaf.obj) e.hom.val e'.hom.val (op ⊤) a b)

theorem cubicMap_section (a b c : Forms K) :
    (cubicMap K f).app ⊤
      (tensorTop X
        (tensor (constantObj (.of K) f (formModule K)) (constantObj (.of K) f (formModule K)))
        (constantObj (.of K) f (formModule K))
        (tensorTop X (constantObj (.of K) f (formModule K))
          (constantObj (.of K) f (formModule K))
          (constantSection (.of K) f (formModule K) a)
          (constantSection (.of K) f (formModule K) b))
        (constantSection (.of K) f (formModule K) c)) =
      constantSection (.of K) f (dualFormModule K) (primitiveCubic K a b c) := by
  change (constantMap (.of K) f (cubicModuleMap K)).app ⊤
    ((constantTensorIso (.of K) f (ModuleCat.of K (Forms K ⊗[K] Forms K))
      (formModule K)).hom.app ⊤
      ((tensorIso (constantTensorIso (.of K) f (formModule K) (formModule K))
        (Iso.refl (constantObj (.of K) f (formModule K)))).hom.app ⊤ _)) = _
  rw [tensorIso_tensorTop]
  change (constantMap (.of K) f (cubicModuleMap K)).app ⊤
    ((constantTensorIso (.of K) f (ModuleCat.of K (Forms K ⊗[K] Forms K))
      (formModule K)).hom.app ⊤
      (tensorTop X (constantObj (.of K) f (ModuleCat.of K (Forms K ⊗[K] Forms K)))
        (constantObj (.of K) f (formModule K))
        ((constantTensorIso (.of K) f (formModule K) (formModule K)).hom.app ⊤
          (tensorTop X (constantObj (.of K) f (formModule K))
            (constantObj (.of K) f (formModule K))
            (constantSection (.of K) f (formModule K) a)
            (constantSection (.of K) f (formModule K) b)))
        (constantSection (.of K) f (formModule K) c))) = _
  rw [constantTensorIso_section, constantTensorIso_section, constantMap_section]
  rfl

end M9Native.MukaiCubicConstantSheaf
