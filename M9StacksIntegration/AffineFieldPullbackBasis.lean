module

public import M9StacksIntegration.SpecFieldPullbackSections
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackStalkBasis
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.GlobalSections

/-! An actual affine section basis gives an actual field-point pullback
basis. Its coefficients are the original scheme's scalar pullbacks. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

universe u v

namespace M9Native.AffineFieldPullbackBasis

open SpecFieldStalkSections SpecFieldPullbackSections

variable (K : Type u) [Field K] {X : Scheme.{u}} [IsAffine X]
variable (p : Spec (.of K) ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
variable {ι : Type v} [Fintype ι] (b : Module.Basis ι Γ(X,⊤) Γ(E,⊤))

abbrev Source := moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj E)

local instance originalStalkModule : Module (X.presheaf.stalk (p.base (point K)))
    (E.presheaf.stalk (p.base (point K))) :=
  Stacks.ModuleStalkSpecialization.stalkModule E (p.base (point K))

local instance imageAlgebra : Algebra (X.presheaf.stalk (p.base (point K))) (localRing K) :=
  (p.stalkMap (point K)).hom.toAlgebra

local instance sourceStalkModule : Module (localRing K)
    (((Scheme.Modules.pullback p).obj E).presheaf.stalk (point K)) :=
  Stacks.ModuleStalkSpecialization.stalkModule ((Scheme.Modules.pullback p).obj E) (point K)

local instance sourceStalkKModule : Module K
    (((Scheme.Modules.pullback p).obj E).presheaf.stalk (point K)) :=
  moduleStalk K ((Scheme.Modules.pullback p).obj E)

local instance sourceStalkTower : IsScalarTower K (localRing K)
    (((Scheme.Modules.pullback p).obj E).presheaf.stalk (point K)) :=
  stalkScalarTower K ((Scheme.Modules.pullback p).obj E)

def fieldStalkBasis : Module.Basis ι (localRing K)
    (((Scheme.Modules.pullback p).obj E).presheaf.stalk (point K)) :=
  Stacks.ModuleStalkSpecialization.pullbackStalkBasis E (isAffineOpen_top X) b p (by trivial)

omit [Fintype ι] in
theorem fieldStalkBasis_apply (i : ι) :
    fieldStalkBasis K p E b i =
      (Stacks.Divisors.pullbackStalkBaseChange p E (point K)).symm
        ((1 : localRing K) ⊗ₜ[X.presheaf.stalk (p.base (point K))]
          E.presheaf.germ ⊤ (p.base (point K)) trivial (b i)) := by
  change (Stacks.Divisors.pullbackStalkBaseChange p E (point K)).symm
    (Algebra.TensorProduct.basis (localRing K)
      (Stacks.ModuleStalkSpecialization.stalkBasisOfAffine E (isAffineOpen_top X) b
        (show p.base (point K) ∈ (⊤ : X.Opens) from trivial)) i) = _
  rw [Algebra.TensorProduct.basis_apply, Stacks.ModuleStalkSpecialization.stalkBasisOfAffine_apply]

def coordinates : Source K p E ≃ₗ[K] (ι → K) :=
  (sectionsStalkEquiv K ((Scheme.Modules.pullback p).obj E)).trans
    (((fieldStalkBasis K p E b).equivFun.restrictScalars K).trans
      (LinearEquiv.piCongrRight fun _ => (scalarLinearEquiv K).symm))

theorem coordinates_pulled_basis [DecidableEq ι] (i : ι) :
    coordinates K p E b (pulledSection K p E ⊤ (by trivial) (b i)) = Pi.single i 1 := by
  have hg : sectionsStalkEquiv K ((Scheme.Modules.pullback p).obj E)
      (pulledSection K p E ⊤ (by trivial) (b i)) = fieldStalkBasis K p E b i := by
    apply (Stacks.Divisors.pullbackStalkBaseChange p E (point K)).injective
    rw [baseChange_pulledSection, fieldStalkBasis_apply, LinearEquiv.apply_symm_apply]
  change (fun k => (scalarLinearEquiv K).symm
    ((fieldStalkBasis K p E b).equivFun
      (sectionsStalkEquiv K ((Scheme.Modules.pullback p).obj E)
        (pulledSection K p E ⊤ (by trivial) (b i))) k)) = _
  rw [hg]
  funext k
  rw [Module.Basis.equivFun_self]
  have h1 : (scalarLinearEquiv K).symm 1 = 1 := (scalarStalkEquiv K).symm.map_one
  by_cases hk : k = i
  · subst k
    simp [h1]
  · have hik : i ≠ k := Ne.symm hk
    simp [hk, hik]

def basis : Module.Basis ι K (Source K p E) := Module.Basis.ofEquivFun (coordinates K p E b)

theorem basis_apply [DecidableEq ι] (i : ι) :
    basis K p E b i = pulledSection K p E ⊤ (by trivial) (b i) := by
  apply (coordinates K p E b).injective
  rw [coordinates_pulled_basis]
  have h := congrFun (Module.Basis.coe_ofEquivFun (coordinates K p E b)) i
  exact (congrArg (coordinates K p E b) h).trans
    ((coordinates K p E b).apply_symm_apply _)

omit [IsAffine X] [E.IsQuasicoherent] in
theorem pulled_top_eq_global (s : Γ(E,⊤)) :
    pulledSection K p E ⊤ (by trivial) s = pullbackGlobalSections p E s := by
  rw [pullbackGlobalSections_eq_unit]
  simp [pulledSection, Scheme.Modules.pullbackSection]
  rfl

def scalarEvaluation : Γ(X,⊤) →+* K :=
  (Scheme.ΓSpecIso (.of K)).hom.hom.comp p.appTop.hom

theorem coordinates_global_smul (c : Γ(X,⊤)) (s : Γ(E,⊤)) :
    coordinates K p E b (pullbackGlobalSections p E (c • s)) =
      scalarEvaluation K p c • coordinates K p E b (pullbackGlobalSections p E s) := by
  have hc : p.appTop c = (Scheme.ΓSpecIso (.of K)).inv (scalarEvaluation K p c) :=
    ((Scheme.ΓSpecIso (.of K)).hom_inv_id_apply (p.appTop c)).symm
  have hs : (p.appTop c • pullbackGlobalSections p E s :
      Γ((Scheme.Modules.pullback p).obj E,⊤)) =
        ((scalarEvaluation K p c) • (show Source K p E from pullbackGlobalSections p E s)) := by
    change p.appTop c • (show Γ((Scheme.Modules.pullback p).obj E,⊤) from
        pullbackGlobalSections p E s) =
      (Scheme.ΓSpecIso (.of K)).inv (scalarEvaluation K p c) •
        (show Γ((Scheme.Modules.pullback p).obj E,⊤) from pullbackGlobalSections p E s)
    rw [hc]
  calc
    _ = coordinates K p E b (p.appTop c • pullbackGlobalSections p E s) :=
      congrArg (coordinates K p E b) (SectionsEqualizer.pullbackGlobalSections_smul p E c s)
    _ = coordinates K p E b ((scalarEvaluation K p c) •
        (show Source K p E from pullbackGlobalSections p E s)) :=
      congrArg (coordinates K p E b) hs
    _ = _ := (coordinates K p E b).map_smul _ _

theorem coordinates_global_basis [DecidableEq ι] (i : ι) :
    coordinates K p E b (pullbackGlobalSections p E (b i)) = Pi.single i 1 := by
  rw [← pulled_top_eq_global]
  exact coordinates_pulled_basis K p E b i

theorem coordinates_global [DecidableEq ι] (s : Γ(E,⊤)) :
    coordinates K p E b (pullbackGlobalSections p E s) =
      fun i => scalarEvaluation K p (b.equivFun s i) := by
  have h := congrArg (fun t : Γ(E,⊤) =>
    coordinates K p E b (pullbackGlobalSections p E t)) (b.sum_repr s)
  simp only [map_sum, coordinates_global_smul, coordinates_global_basis] at h
  calc
    _ = ∑ i : ι, scalarEvaluation K p (b.equivFun s i) • Pi.single i 1 := by
      simpa only [Module.Basis.equivFun_apply] using h.symm
    _ = _ := by
      ext i
      simp [Pi.single_apply]

end M9Native.AffineFieldPullbackBasis
