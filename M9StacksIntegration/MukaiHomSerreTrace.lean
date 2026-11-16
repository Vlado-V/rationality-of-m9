module

public import M9StacksIntegration.UnitExtCohomologyAllDegrees
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom

/-!
# Actual Hom--Serre contraction of original unit Ext

Native curve Hom duality is already linear for `modulesLinearOverField`.
Its proved source naturality and the proved all-degree unit-Ext coefficient
naturality identify contraction with the actual coefficient postcomposition.
No canonical-versus-chosen boundary equality or trace normalization is needed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace M9Native.MukaiHomSerreTrace

open M9Native.UnitExtCohomologyAllDegrees

attribute [local instance 100000] ModuleCat.hasDerivedCategory
attribute [local instance 100000] Scheme.Modules.hasDerivedCategory

variable {X : Scheme.{u}}

local instance nativeHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- The actual relative dualizing module at the native locally small model. -/
abbrev curveDualizingModule (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] : X.Modules :=
  Stacks.Duality.relativeDualizingModule f
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (.of k)))

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]

/-- On an actual one-dimensional scheme the native relative module is
the native curve dualizing sheaf, by the proved cohomological identification. -/
def curveDualizingModuleIso (hdim : topologicalKrullDim X = 1) :
    curveDualizingModule k f ≅ Stacks.Duality.dualizingSheafOverField f :=
  eqToIso (Stacks.Duality.dualizingSheafOverField_eq_relativeDualizingModule f hdim).symm

/-- The actual linear form on H1 of the genuine dualizing sheaf,
obtained by applying native Hom duality to its identity morphism. -/
def traceLinearMap (hdim : topologicalKrullDim X ≤ 1) :
    cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 1 →ₗ[k] k := by
  letI := modulesLinearOverField k f
  exact Stacks.Duality.homDualizingSheafLinearEquiv f hdim
    (Stacks.Duality.dualizingSheafOverField f)
    (Stacks.Duality.isQuasicoherent_dualizingSheafOverField f) (𝟙 _)

/-- Native Hom duality contracts by the actual cohomology map of the
original coefficient morphism, followed by the actual identity trace. -/
theorem homSerre_apply_eq_trace (hdim : topologicalKrullDim X ≤ 1)
    (A : X.Modules) (hA : A.IsQuasicoherent)
    (q : A ⟶ Stacks.Duality.dualizingSheafOverField f)
    (y : cohomologyOverField k f A 1) :
    letI := modulesLinearOverField k f
    Stacks.Duality.homDualizingSheafLinearEquiv f hdim A hA q y =
      traceLinearMap k f hdim (cohomologyOverFieldMap k f q 1 y) := by
  let := modulesLinearOverField k f
  change (Stacks.Duality.homDualizingSheafAddEquiv f hdim A hA q).hom y =
    (Stacks.Duality.homDualizingSheafAddEquiv f hdim
      (Stacks.Duality.dualizingSheafOverField f)
      (Stacks.Duality.isQuasicoherent_dualizingSheafOverField f) (𝟙 _)).hom
        ((cohomologyOverFieldMap k f q 1).hom y)
  have h := congrArg (fun g => g.hom y)
    (Stacks.Duality.homDualizingSheafAddEquiv_naturality f hdim hA
      (Stacks.Duality.isQuasicoherent_dualizingSheafOverField f) q (𝟙 _))
  simpa only [Category.comp_id, ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- For the original small unit Ext, actual coefficient naturality
turns the same contraction into literal Yoneda postcomposition. -/
theorem homSerre_unitExt_eq_trace (hdim : topologicalKrullDim X ≤ 1)
    (A : X.Modules) (hA : A.IsQuasicoherent)
    (q : A ⟶ Stacks.Duality.dualizingSheafOverField f)
    (e : Ext.{u} (_root_.SheafOfModules.unit X.ringCatSheaf) A 1) :
    letI := modulesLinearOverField k f
    Stacks.Duality.homDualizingSheafLinearEquiv f hdim A hA q
      (unitExtCohomologyLinearEquivAll k f A 1 e) =
        traceLinearMap k f hdim
          (unitExtCohomologyLinearEquivAll k f
            (Stacks.Duality.dualizingSheafOverField f) 1
            (e.comp (Ext.mk₀ q) (add_zero 1))) := by
  let := modulesLinearOverField k f
  rw [homSerre_apply_eq_trace]
  exact congrArg (traceLinearMap k f hdim)
    (unitExtCohomologyAddEquiv_naturality k f q 1 e).symm

/-- An actual zero Yoneda postcomposition has zero native Hom--Serre
contraction. The later geometric instantiation proves this zero by wedge square-zero. -/
theorem homSerre_unitExt_eq_zero_of_postcomp_zero
    (hdim : topologicalKrullDim X ≤ 1) (A : X.Modules) (hA : A.IsQuasicoherent)
    (q : A ⟶ Stacks.Duality.dualizingSheafOverField f)
    (e : Ext.{u} (_root_.SheafOfModules.unit X.ringCatSheaf) A 1)
    (he : e.comp (Ext.mk₀ q) (add_zero 1) = 0) :
    letI := modulesLinearOverField k f
    Stacks.Duality.homDualizingSheafLinearEquiv f hdim A hA q
      (unitExtCohomologyLinearEquivAll k f A 1 e) = 0 := by
  let := modulesLinearOverField k f
  rw [homSerre_unitExt_eq_trace, he, map_zero, map_zero]

end M9Native.MukaiHomSerreTrace
