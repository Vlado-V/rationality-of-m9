module

public import M9StacksIntegration.MukaiCubicConstantSheaf
public import M9StacksIntegration.SectionCokernelField
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections

/-! Naturality of the actual sheaf tensor pullback, including its
left-associated third tensor power and the original decomposable
sections. The underlying comparison is the native canonical natural
transformation, not a chosen isomorphism of modules with equal rank. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.MukaiTensorPullbackNaturality

open MukaiBundleDeterminant LinearIncidenceTensorCoordinates

variable {X Y : Scheme.{u}}

def tensorMap {A A' B B' : X.Modules} (a : A ⟶ A') (b : B ⟶ B') :
    tensor A B ⟶ tensor A' B' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map a).app B ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A').map b

theorem tensorMap_comp {A A' A'' B B' B'' : X.Modules}
    (a : A ⟶ A') (a' : A' ⟶ A'') (b : B ⟶ B') (b' : B' ⟶ B'') :
    tensorMap (a ≫ a') (b ≫ b') = tensorMap a b ≫ tensorMap a' b' := by
  simp only [tensorMap, CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map a').naturality_assoc b]

theorem tensorMap_tensorTop {A A' B B' : X.Modules} (a : A ⟶ A') (b : B ⟶ B')
    (s : Γ(A, ⊤)) (t : Γ(B, ⊤)) :
    (tensorMap a b).app ⊤ (tensorTop X A B s t) =
      tensorTop X A' B' (a.app ⊤ s) (b.app ⊤ t) := by
  have hmap := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.sheaf a b
  change tensorMap a b = _ at hmap
  rw [hmap]
  unfold tensorTop Stacks.SheafOfModules.tensorSectionsAt
  refine (Stacks.SheafOfModules.toSheafify_app_map_obj
    (O := X.sheaf.obj) (hO := X.ringCatSheaf.property)
    (f := PresheafOfModules.tensorHom (O := X.sheaf.obj) a.val b.val)
    (op ⊤) (s ⊗ₜ t)).trans ?_
  exact congrArg (fun z =>
    (Stacks.SheafOfModules.TensorSheafification.toSheafify X.sheaf.obj
      X.ringCatSheaf.property (PresheafOfModules.tensorObj A'.val B'.val)).app (op ⊤) z)
    (PresheafOfModules.tensorHom_tmul (O := X.sheaf.obj) a.val b.val (op ⊤) s t)

theorem pullbackTensorIso_naturality (p : Y ⟶ X) {A A' B B' : X.Modules}
    (a : A ⟶ A') (b : B ⟶ B') :
    (Scheme.Modules.pullback p).map (tensorMap a b) ≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A' B').hom =
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A B).hom ≫
        tensorMap ((Scheme.Modules.pullback p).map a) ((Scheme.Modules.pullback p).map b) :=
  (Stacks.RingedSpace.comparisonNatTrans p.toLRSHom.toShHom).naturality
    ((a,b) : (A,B) ⟶ (A',B'))

abbrev cubeObj (A : X.Modules) : X.Modules := tensor (tensor A A) A

def cubeMap {A B : X.Modules} (a : A ⟶ B) : cubeObj A ⟶ cubeObj B :=
  tensorMap (tensorMap a a) a

def cubePullbackIso (p : Y ⟶ X) (A : X.Modules) :
    (Scheme.Modules.pullback p).obj (cubeObj A) ≅
      cubeObj ((Scheme.Modules.pullback p).obj A) :=
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p (tensor A A) A ≪≫
    tensorIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A A) (Iso.refl _)

theorem cubePullbackIso_naturality (p : Y ⟶ X) {A B : X.Modules}
    (a : A ⟶ B) :
    (Scheme.Modules.pullback p).map (cubeMap a) ≫ (cubePullbackIso p B).hom =
      (cubePullbackIso p A).hom ≫ cubeMap ((Scheme.Modules.pullback p).map a) := by
  change (Scheme.Modules.pullback p).map (tensorMap (tensorMap a a) a) ≫
      ((Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p (tensor B B) B).hom ≫
        tensorMap (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p B B).hom (𝟙 _)) =
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p (tensor A A) A).hom ≫
      (tensorMap (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A A).hom (𝟙 _) ≫
        tensorMap (tensorMap ((Scheme.Modules.pullback p).map a)
          ((Scheme.Modules.pullback p).map a)) ((Scheme.Modules.pullback p).map a))
  rw [← Category.assoc, pullbackTensorIso_naturality]
  rw [Category.assoc]
  congr 1
  rw [← tensorMap_comp, ← tensorMap_comp, Category.comp_id, Category.id_comp,
    pullbackTensorIso_naturality]

theorem cubeMap_tensorTop {A B : X.Modules} (a : A ⟶ B)
    (s t u : Γ(A, ⊤)) :
    (cubeMap a).app ⊤ (tensorTop X (tensor A A) A (tensorTop X A A s t) u) =
      tensorTop X (tensor B B) B (tensorTop X B B (a.app ⊤ s) (a.app ⊤ t)) (a.app ⊤ u) := by
  rw [cubeMap, tensorMap_tensorTop, tensorMap_tensorTop]

theorem cubePullbackIso_tensorTop (p : Y ⟶ X) (A : X.Modules) (s t u : Γ(A, ⊤)) :
    (cubePullbackIso p A).hom.app ⊤
      (pullbackGlobalSections p (cubeObj A)
        (tensorTop X (tensor A A) A (tensorTop X A A s t) u)) =
      tensorTop Y
        (tensor ((Scheme.Modules.pullback p).obj A) ((Scheme.Modules.pullback p).obj A))
        ((Scheme.Modules.pullback p).obj A)
        (tensorTop Y ((Scheme.Modules.pullback p).obj A) ((Scheme.Modules.pullback p).obj A)
          (pullbackGlobalSections p A s) (pullbackGlobalSections p A t))
        (pullbackGlobalSections p A u) := by
  change (tensorMap
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A A).hom
    (𝟙 ((Scheme.Modules.pullback p).obj A))).app ⊤
      ((Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p (tensor A A) A).hom.app ⊤
        (pullbackGlobalSections p (cubeObj A)
          (tensorTop X (tensor A A) A (tensorTop X A A s t) u))) = _
  have houter :
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p (tensor A A) A).hom.app ⊤
        (pullbackGlobalSections p (cubeObj A)
          (tensorTop X (tensor A A) A (tensorTop X A A s t) u)) =
        tensorTop Y ((Scheme.Modules.pullback p).obj (tensor A A))
          ((Scheme.Modules.pullback p).obj A)
          (pullbackGlobalSections p (tensor A A) (tensorTop X A A s t))
          (pullbackGlobalSections p A u) :=
    Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt p
      (tensor A A) A (tensorTop X A A s t) u
  rw [houter]
  have hmiddle :
      (tensorMap (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A A).hom
        (𝟙 ((Scheme.Modules.pullback p).obj A))).app ⊤
        (tensorTop Y ((Scheme.Modules.pullback p).obj (tensor A A))
          ((Scheme.Modules.pullback p).obj A)
          (pullbackGlobalSections p (tensor A A) (tensorTop X A A s t))
          (pullbackGlobalSections p A u)) =
        tensorTop Y
          (tensor ((Scheme.Modules.pullback p).obj A) ((Scheme.Modules.pullback p).obj A))
          ((Scheme.Modules.pullback p).obj A)
          ((Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A A).hom.app ⊤
            (pullbackGlobalSections p (tensor A A) (tensorTop X A A s t)))
          (pullbackGlobalSections p A u) :=
    tensorMap_tensorTop (X := Y)
      (A := (Scheme.Modules.pullback p).obj (tensor A A))
      (A' := tensor ((Scheme.Modules.pullback p).obj A) ((Scheme.Modules.pullback p).obj A))
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A A).hom
      (𝟙 ((Scheme.Modules.pullback p).obj A))
      (pullbackGlobalSections p (tensor A A) (tensorTop X A A s t))
      (pullbackGlobalSections p A u)
  rw [hmiddle]
  have hinner :
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A A).hom.app ⊤
        (pullbackGlobalSections p (tensor A A) (tensorTop X A A s t)) =
        tensorTop Y ((Scheme.Modules.pullback p).obj A) ((Scheme.Modules.pullback p).obj A)
          (pullbackGlobalSections p A s) (pullbackGlobalSections p A t) :=
    Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt p A A s t
  rw [hinner]

/-- Actual global sections detect affine sheaf maps with quasi-coherent
source. This invokes the checked native affine counit, not pointwise
agreement on an unspecified family. -/
theorem affine_hom_ext {R : CommRingCat.{u}} {A B : (Spec R).Modules}
    [A.IsQuasicoherent] (a b : A ⟶ B)
    (h : ∀ s : Γ(A, ⊤), a.app ⊤ s = b.app ⊤ s) : a = b := by
  by_contra hne
  apply SectionCokernelLocallyFree.gamma_map_ne_zero (a-b) (sub_ne_zero.mpr hne)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change a.app ⊤ s - b.app ⊤ s = 0
  exact sub_eq_zero.mpr (h s)

def cubeSectionsEquiv (R : CommRingCat.{u}) (A : (Spec R).Modules)
    [A.IsQuasicoherent] [(tensor A A).IsQuasicoherent] :
    ((Γ(A, ⊤) ⊗[R] Γ(A, ⊤)) ⊗[R] Γ(A, ⊤)) ≃ₗ[R] Γ(cubeObj A, ⊤) := by
  let e₁ : (Γ(A, ⊤) ⊗[R] Γ(A, ⊤)) ≃ₗ[R] Γ(tensor A A, ⊤) :=
    TildeTensor.gammaTensorEquiv A A
  let e₂ : (Γ(tensor A A, ⊤) ⊗[R] Γ(A, ⊤)) ≃ₗ[R] Γ(cubeObj A, ⊤) :=
    TildeTensor.gammaTensorEquiv (tensor A A) A
  exact (TensorProduct.congr e₁ (LinearEquiv.refl R Γ(A, ⊤))).trans e₂

theorem cubeSectionsEquiv_tmul (R : CommRingCat.{u}) (A : (Spec R).Modules)
    [A.IsQuasicoherent] [(tensor A A).IsQuasicoherent] (s t u : Γ(A, ⊤)) :
    cubeSectionsEquiv R A ((s ⊗ₜ[R] t) ⊗ₜ[R] u) =
      tensorTop (Spec R) (tensor A A) A (tensorTop (Spec R) A A s t) u := by
  simp only [cubeSectionsEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply]
  rfl

/-- Equality on actual decomposable global sections determines a map
out of the actual affine cube; the assertion follows from the two native
tensor comparisons and affine quasi-coherence. -/
theorem affine_cube_hom_ext {R : CommRingCat.{u}} {A B : (Spec R).Modules}
    [A.IsQuasicoherent] [(tensor A A).IsQuasicoherent] [(cubeObj A).IsQuasicoherent]
    (a b : cubeObj A ⟶ B)
    (h : ∀ s t u : Γ(A, ⊤),
      a.app ⊤ (tensorTop (Spec R) (tensor A A) A (tensorTop (Spec R) A A s t) u) =
      b.app ⊤ (tensorTop (Spec R) (tensor A A) A (tensorTop (Spec R) A A s t) u)) :
    a = b := by
  let e := cubeSectionsEquiv R A
  have he : ((moduleSpecΓFunctor.map a).hom.comp e.toLinearMap) =
      ((moduleSpecΓFunctor.map b).hom.comp e.toLinearMap) := by
    apply LinearMap.ext
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul st u =>
      induction st using TensorProduct.inductionOn with
      | tmul s t =>
        change a.app ⊤ (cubeSectionsEquiv R A ((s ⊗ₜ[R] t) ⊗ₜ[R] u)) =
          b.app ⊤ (cubeSectionsEquiv R A ((s ⊗ₜ[R] t) ⊗ₜ[R] u))
        rw [cubeSectionsEquiv_tmul]
        exact h s t u
      | add x y hx hy =>
        simpa only [TensorProduct.add_tmul, LinearMap.comp_apply, map_add] using
          congrArg₂ (fun x y => x+y) hx hy
    | add x y hx hy =>
      simpa only [LinearMap.comp_apply, map_add] using
        congrArg₂ (fun x y => x+y) hx hy
  apply affine_hom_ext a b
  intro s
  obtain ⟨w, rfl⟩ := e.surjective s
  exact LinearMap.congr_fun he w

end M9Native.MukaiTensorPullbackNaturality
