module

public import M9StacksIntegration.TensorFreeRowProjection
public import M9StacksIntegration.LagrangianTransverseConormalFiber
public import M9StacksIntegration.SectionZeroDifferentialEvaluation

/-!
# Actual nonzero defining rows and their actual differentials

A literal nonzero original row gives a genuine split inclusion of the
dual determinant line into the actual equation-dual source. Its actual
conormal differential is injective on every residue fibre by actual
smooth-section geometry. Its normalization on every local dual-line
section is the actual universal differential of the original row value.
No fibre injectivity, desired transversality map, or differential
comparison is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianRowDifferential

open TupleEvaluationFiber

section Fiber

variable {X : Scheme.{u}}

/-- The original actual fibre-map construction preserves the original identity map. -/
theorem inducedFiberMap_id (E : X.Modules) (x : X) :
    inducedFiberMap (𝟙 E) x = LinearMap.id := by
  letI := residueAlgebra x
  change (MukaiSaturationRank.stalkMap (𝟙 E) x).baseChange (X.residueField x) = _
  have hid : MukaiSaturationRank.stalkMap (𝟙 E) x = LinearMap.id := by
    ext s
    change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (𝟙 E.val)))) s = s
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  rw [hid]
  simp

/-- Actual splitting, rather than an unjustified left-exact pullback, gives fibre injectivity. -/
theorem fiberMap_injective_of_leftInverse {E F : X.Modules}
    (a : E ⟶ F) (r : F ⟶ E) (hr : a ≫ r = 𝟙 E) (x : X) :
    Function.Injective (inducedFiberMap a x) := by
  have h : (inducedFiberMap r x).comp (inducedFiberMap a x) = LinearMap.id :=
    (MukaiShortExactFiberRank.fiberMap_comp a r x).symm.trans
      ((congrArg (fun q => inducedFiberMap q x) hr).trans (inducedFiberMap_id E x))
  exact (show Function.LeftInverse (inducedFiberMap r x) (inducedFiberMap a x) from
    fun v => LinearMap.congr_fun h v).injective

end Fiber

open LagrangianFiveSectionModel

variable (K : Type u) [Field K]

/-- The actual original line projection of the original equation bundle. -/
def rowProjection (a : Fin 5 → K) : equationBundle K ⟶ LagrangianPluckerQuotient.determinantLine K :=
  TensorFreeRowProjection.row K (LagrangianGrassmannian.projection K)
    (LagrangianPluckerQuotient.determinantLine K) 5 a

variable (s : Γ(equationBundle K,⊤))
  [SmoothOfRelativeDimension 1 (structureMap K s)]

/-- The actual row-dual to ambient differential morphism on the original zero scheme. -/
def rowDifferential (a : Fin 5 → K) :
    (Scheme.Modules.pullback (inclusion K s)).obj
      (dualSheaf (LagrangianPluckerQuotient.determinantLine K)) ⟶
    (conormalSequence K s).X₂ :=
  (Scheme.Modules.pullback (inclusion K s)).map (dualMap (rowProjection K a)) ≫
    (conormalSequence K s).f

/-- Every genuine nonzero original row has a nonzero differential on every actual residue fibre. -/
theorem rowDifferential_fiber_injective (a : Fin 5 → K) (ha : a ≠ 0) (x : curve K s) :
    Function.Injective (inducedFiberMap (rowDifferential K s a) x) := by
  obtain ⟨r, hr⟩ := TensorFreeRowProjection.dual_exists_leftInverse K
    (LagrangianGrassmannian.projection K) (LagrangianPluckerQuotient.determinantLine K) 5 a ha
  have hsplit : (Scheme.Modules.pullback (inclusion K s)).map (dualMap (rowProjection K a)) ≫
      (Scheme.Modules.pullback (inclusion K s)).map r = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, rowProjection, hr, CategoryTheory.Functor.map_id]
  rw [rowDifferential, MukaiShortExactFiberRank.fiberMap_comp]
  exact (LagrangianTransverseConormalFiber.equationMap_fiber_injective K s x).comp
    (fiberMap_injective_of_leftInverse _ _ hsplit x)

/-- The row map retains the actual local differential of the actual original row-valued section. -/
theorem rowDifferential_adjunction_apply (a : Fin 5 → K)
    (U : (LagrangianGrassmannian.space K).Opens)
    (tau : Γ(dualSheaf (LagrangianPluckerQuotient.determinantLine K), U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction (inclusion K s)).homEquiv _ _
      (rowDifferential K s a)).val.app (op U)) tau =
      (((Scheme.Modules.pullbackPushforwardAdjunction (inclusion K s)).unit.app
          (Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K))).val.app
        (op U)).hom
        ((Scheme.Hom.universalRelativeDerivation (LagrangianGrassmannian.projection K)).d
          (evalAt (LagrangianPluckerQuotient.determinantLine K) tau
            ((LagrangianPluckerQuotient.determinantLine K).presheaf.map
              (homOfLE le_top).op ((rowProjection K a).app ⊤ s)))) := by
  rw [rowDifferential, Adjunction.homEquiv_naturality_left]
  have he : evalAt (equationBundle K) ((dualMap (rowProjection K a)).app U tau)
      ((equationBundle K).presheaf.map (homOfLE le_top).op s) =
      evalAt (LagrangianPluckerQuotient.determinantLine K) tau
        ((LagrangianPluckerQuotient.determinantLine K).presheaf.map
          (homOfLE le_top).op ((rowProjection K a).app ⊤ s)) :=
    (dualPairing_dualMap (rowProjection K a) tau (Over.mk (𝟙 U)) _).trans
      (congrArg (evalAt (LagrangianPluckerQuotient.determinantLine K) tau)
        (PresheafOfModules.naturality_apply (rowProjection K a).val (homOfLE le_top).op s))
  exact (SectionZeroDifferentialEvaluation.equationSequence_f_adjunction_apply K
    (equationBundle K) s U ((dualMap (rowProjection K a)).app U tau)).trans
      (congrArg (fun z =>
        (((Scheme.Modules.pullbackPushforwardAdjunction (inclusion K s)).unit.app
            (Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K))).val.app
          (op U)).hom
          ((Scheme.Hom.universalRelativeDerivation (LagrangianGrassmannian.projection K)).d z)) he)

end M9Native.LagrangianRowDifferential
