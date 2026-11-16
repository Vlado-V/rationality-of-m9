module

public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightScalar
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyLinear
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linear cancellation of an invertible tensor factor

All Hom spaces use the native `modulesLinearOverField k f` structure. Tensoring
is proved linear for that exact structure by its effect on multiplication by
a base scalar. Fully faithful tensoring and the actual unit, symmetry, and
evaluation isomorphisms then identify Hom(W ⊗ I,W) with H⁰(I∨).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9StacksIntegration.InvertibleHomCancellation

open CategoryTheory AlgebraicGeometry Opposite

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k))

theorem sectionsIsMulCommutative :
    ∀ U : X.Opensᵒᵖ, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  let : CommRing (X.ringCatSheaf.obj.obj U) :=
    inferInstanceAs (CommRing (X.presheaf.obj U))
  exact ⟨⟨mul_comm⟩⟩

/-- The actual compatible family of local functions induced by a base scalar. -/
def baseSection (c : k) : (X.ringCatSheaf.obj ⋙ forget RingCat).sections :=
  ⟨fun U => baseRingToSections k (Over.mk f) U c, by
    intro U V i
    exact (congrArg (fun g => RingCat.Hom.hom g
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (Over.mk f).hom.appTop).hom c))
        (X.ringCatSheaf.obj.map_comp U.unop.leTop.op i)).symm⟩

/-- The scalar action on native Hom spaces is multiplication by those local functions. -/
theorem smul_id_eq_globalSection (c : k) (M : X.Modules) :
    letI := sectionsIsMulCommutative (X := X)
    letI := modulesLinearOverField k f
    c • (𝟙 M) =
      (Stacks.SheafOfModules.globalSectionToEnd X.ringCatSheaf (baseSection f c)).asHom.app M := by
  let := sectionsIsMulCommutative (X := X)
  let := modulesLinearOverField k f
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  change baseRingToSections k (Over.mk f) U c • x = (baseSection f c).val U • x
  rfl

/-- The original sheaf tensor bifunctor with its right factor fixed. -/
abbrev tensorRight (W : X.Modules) : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf).flip.obj W

theorem tensorRight_additive (W : X.Modules) : (tensorRight W).Additive where
  map_add := NatTrans.congr_app
    (Functor.map_add (Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf)) W

theorem tensorRight_linear (W : X.Modules) :
    letI := modulesLinearOverField k f
    Functor.Linear k (tensorRight W) := by
  let := sectionsIsMulCommutative (X := X)
  let := modulesLinearOverField k f
  apply (Functor.linear_iff k (tensorRight W)).mpr
  intro M c
  calc
    _ = (tensorRight W).map
        ((Stacks.SheafOfModules.globalSectionToEnd X.ringCatSheaf
          (baseSection f c)).asHom.app M) :=
      congrArg (tensorRight W).map (smul_id_eq_globalSection f c M)
    _ = (Stacks.SheafOfModules.globalSectionToEnd X.ringCatSheaf
        (baseSection f c)).asHom.app ((tensorRight W).obj M) :=
      Stacks.sheafTensorRight_map_globalSmul (O := X.sheaf) W (baseSection f c) M
    _ = _ := (smul_id_eq_globalSection f c ((tensorRight W).obj M)).symm

/-- Fully faithful tensoring, as a genuine linear equivalence on Hom spaces. -/
def tensorRightHomLinearEquiv (W : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W]
    (A B : X.Modules) :
    letI := modulesLinearOverField k f
    (A ⟶ B) ≃ₗ[k] ((tensorRight W).obj A ⟶ (tensorRight W).obj B) := by
  letI := modulesLinearOverField k f
  letI := tensorRight_additive W
  letI := tensorRight_linear f W
  letI : (tensorRight W).IsEquivalence :=
    Scheme.Modules.isEquivalence_invertibleTensorRightFunctor W
  letI : (tensorRight W).Faithful := Functor.IsEquivalence.faithful
  letI : (tensorRight W).Full := Functor.IsEquivalence.full
  exact LinearEquiv.ofBijective ((tensorRight W).mapLinearMap k)
    ⟨(tensorRight W).map_injective, (tensorRight W).map_surjective⟩

/-- Cancel W from the actual Hom(W ⊗ I,W), including its native scalar action. -/
def homCancelLinearEquiv (W : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W]
    (I : X.Modules) :
    letI := modulesLinearOverField k f
    (Scheme.Modules.tensorObj W I ⟶ W) ≃ₗ[k] (I ⟶ structureSheafModule X) := by
  letI := modulesLinearOverField k f
  let c : Scheme.Modules.tensorObj W I ≅ (tensorRight W).obj I :=
    Stacks.SheafOfModules.Invertible.tensorProductBraiding X.sheaf.obj
      X.ringCatSheaf.property W I
  let e : (tensorRight W).obj (structureSheafModule X) ≅ W :=
    Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.sheaf.obj
      X.ringCatSheaf.property W
  let eHom : (Scheme.Modules.tensorObj W I ⟶ W) ≃ₗ[k]
      ((tensorRight W).obj I ⟶ (tensorRight W).obj (structureSheafModule X)) :=
    Linear.homCongr k c e.symm
  exact eHom.trans (tensorRightHomLinearEquiv f W I (structureSheafModule X)).symm

/-- The actual dual sheaf of an O_X-module, at the native scheme spelling. -/
abbrev dual (I : X.Modules) : X.Modules :=
  Stacks.SheafOfModules.dualSheaf X.presheaf (structureSheafRing X.toRingedSpace).property I

/-- The actual evaluation pairing gives Hom(O,I∨) ≃ Hom(I,O), linearly over k. -/
def unitDualHomLinearEquiv (I : X.Modules)
    [hI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property I] :
    letI := modulesLinearOverField k f
    (structureSheafModule X ⟶ dual I) ≃ₗ[k] (I ⟶ structureSheafModule X) := by
  letI := modulesLinearOverField k f
  letI : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property I :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ I hI
  let eI : (tensorRight I).obj (structureSheafModule X) ≅ I :=
    Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.sheaf.obj
      X.ringCatSheaf.property I
  let eDual : (tensorRight I).obj (dual I) ≅ structureSheafModule X :=
    Stacks.SheafOfModules.Scheme.evaluationIso X I
  exact (tensorRightHomLinearEquiv f I (structureSheafModule X) (dual I)).trans
    (Linear.homCongr k eI eDual)

def homDualLinearEquivCohomologyZero (I : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property I] :
    letI := modulesLinearOverField k f
    (I ⟶ structureSheafModule X) ≃ₗ[k] cohomologyOverField k f (dual I) 0 := by
  letI := modulesLinearOverField k f
  exact (unitDualHomLinearEquiv f I).symm.trans
    (unitHomLinearEquivCohomologyZero k f (dual I))

/-- The actual linear Hom-cancellation equivalence used in canonical restriction. -/
def invertibleHomLinearEquivCohomologyZero (W I : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property I] :
    letI := modulesLinearOverField k f
    (Scheme.Modules.tensorObj W I ⟶ W) ≃ₗ[k] cohomologyOverField k f (dual I) 0 := by
  letI := modulesLinearOverField k f
  exact (homCancelLinearEquiv f W I).trans (homDualLinearEquivCohomologyZero f I)

theorem finrank_hom_twist (W I : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property I] :
    letI := modulesLinearOverField k f
    Module.finrank k (Scheme.Modules.tensorObj W I ⟶ W) =
      Module.finrank k (cohomologyOverField k f (dual I) 0) := by
  let := modulesLinearOverField k f
  exact (invertibleHomLinearEquivCohomologyZero f W I).finrank_eq

/-- The exact divisor-ideal specialization; the right side is the native O_X(D). -/
theorem finrank_hom_divisor_twist (W : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W]
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    letI := modulesLinearOverField k f
    Module.finrank k (Scheme.Modules.tensorObj W (Stacks.Divisors.negativeTwist' D) ⟶ W) =
      Module.finrank k (cohomologyOverField k f (Stacks.Divisors.invertibleSheaf' D) 0) := by
  let := modulesLinearOverField k f
  let : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Divisors.negativeTwist' D) := Stacks.Divisors.isInvertible_negativeTwist D
  exact finrank_hom_twist f W (Stacks.Divisors.negativeTwist' D)

end M9StacksIntegration.InvertibleHomCancellation
