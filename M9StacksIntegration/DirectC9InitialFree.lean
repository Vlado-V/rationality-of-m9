module

public import M9StacksIntegration.DirectC9InitialFixedDescent
public import M9StacksIntegration.FieldLineBaseChangeFree
public import M9StacksIntegration.PoincareProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators

/-! The actual initial ordinary direct image is free rank nine tensored
with the actual inverse-normalization line. Both descent and the
trivialization are constructed; no Chern or K-zero equality is used. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.CurvePower
open MonoidalCategory

universe u
namespace M9Native.DirectC9InitialFree

attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal
  AlgebraicGeometry.schemeModulesSymmetric

open DirectC9PoincareFamily DirectC9InitialFixedFibre DirectC9InitialFixedDescent
open DirectC9FamilyDegree (familySpace familyProjection)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

variable (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)

def fixedPushforwardFreeIso :
    (Scheme.Modules.pushforward (familyProjection C)).obj
        (fixedLine C c₀ 16 : (familySpace C).Modules) ≅
      SheafOfModules.free (R := (power C 9).left.ringCatSheaf) (ULift.{u} (Fin 9)) := by
  let A : (familySpace C).Modules := fixedLine C c₀ 16
  let A₀ : C.left.Modules := fixedFibreLine k C c₀
  let eA : A ≅ (Scheme.Modules.pullback (firstProjection k C)).obj A₀ :=
    Classical.choice (nonempty_fixedLine_pullbackIso k C c₀)
  have hsq : IsPullback (firstProjection k C) (familyProjection C) C.hom (power C 9).hom :=
    IsPullback.of_hasPullback C.hom (power C 9).hom
  exact FieldLineBaseChangeFree.ordinaryPushforwardFreeNineIso k C.hom A₀
    (power C 9).hom (familyProjection C) (firstProjection k C) hsq A eA
    (fixedFibreLine_hasDerivedRank k C c₀ hg)

def initialIso :
    DirectC9Bundles.movingPushforward k C c₀ 0 (by omega) ≅
      Scheme.Modules.tensorObj
        (SheafOfModules.free (R := (power C 9).left.ringCatSheaf) (ULift.{u} (Fin 9)))
        (inverseNormalizationLine C c₀) := by
  let π := familyProjection C
  let A : (familySpace C).Modules := fixedLine C c₀ 16
  let N : (power C 9).left.Modules := inverseNormalizationLine C c₀
  let ecomm : Scheme.Modules.tensorObj ((Scheme.Modules.pullback π).obj N) A ≅
      Scheme.Modules.tensorObj A ((Scheme.Modules.pullback π).obj N) := β_ _ _
  exact (Scheme.Modules.pushforward π).mapIso ecomm ≪≫
    (PoincareChern.invertibleOrdinaryProjectionFormulaIso π A N).symm ≪≫
    (tensorRight N).mapIso (fixedPushforwardFreeIso k C c₀ hg)

end M9Native.DirectC9InitialFree
