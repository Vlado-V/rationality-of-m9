module

public import M9StacksIntegration.DirectC9FibreKernel
public import M9StacksIntegration.NoNetKernelBound
public import M9StacksIntegration.FlagThreeKernelExistence

/-!
# Original degree-eight nets from the actual C9 differential

Choose the single global differential whose actual field-point kernels
compute H0 of the proved degree-eight lines on the ORIGINAL curve.
A kernel of dimension at least three therefore produces an actual
native degree-eight net. The original flag-incidence cap version uses
the proved base-field point-existence theorem. Cap nonvanishing remains
an explicit input; no cohomology isomorphism or net is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.CurvePower
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.DirectC9KernelNet

open DirectC9Bundles (E10 F10)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
    [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]
    (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)

/-- The actual single global differential supplied by the genuine Cartier triangle. -/
def differential : E10 k C c₀ ⟶ F10 k C c₀ :=
  (DirectC9FibreKernel.exists_global_originalFieldKernel k C c₀ hg).choose

/-- Its actual kernel sections compute the original line's actual H0. -/
def pointKernelIso (p : Spec (.of k) ⟶ (power C 9).left)
    (hp : p ≫ (power C 9).hom = 𝟙 _) :
    cohomologyOverField k C.hom (DirectC9OriginalPoint.pointLine k C c₀ p hp) 0 ≅
      moduleSpecΓFunctor.obj (kernel ((Scheme.Modules.pullback p).map
        (differential k C c₀ hg))) :=
  ((DirectC9FibreKernel.exists_global_originalFieldKernel k C c₀ hg).choose_spec.2.2 p hp).some

theorem pointKernel_finrank (p : Spec (.of k) ⟶ (power C 9).left)
    (hp : p ≫ (power C 9).hom = 𝟙 _) :
    Module.finrank k (LinearMap.ker (moduleSpecΓFunctor.map
      ((Scheme.Modules.pullback p).map (differential k C c₀ hg))).hom) =
      Module.finrank k
        (cohomologyOverField k C.hom (DirectC9OriginalPoint.pointLine k C c₀ p hp) 0) :=
  FieldSectionsKernel.finrank_linearKernel_eq_of_iso k
    ((Scheme.Modules.pullback p).map (differential k C c₀ hg)) _
    (pointKernelIso k C c₀ hg p hp)

/-- The section bound is for the actual degree-eight module on the original curve. -/
theorem pointH0_ge_three_of_kernel_ge_three
    (p : Spec (.of k) ⟶ (power C 9).left) (hp : p ≫ (power C 9).hom = 𝟙 _)
    (hker : 3 ≤ Module.finrank k (LinearMap.ker (moduleSpecΓFunctor.map
      ((Scheme.Modules.pullback p).map (differential k C c₀ hg))).hom)) :
    3 ≤ Module.finrank k
      (cohomologyOverField k C.hom (DirectC9OriginalPoint.pointLine k C c₀ p hp) 0) := by
  rw [pointKernel_finrank k C c₀ hg p hp] at hker
  exact hker

/-- A genuine original-field kernel point produces a native original-curve net. -/
theorem nonempty_degree_eight_net_of_point_kernel_ge_three
    (p : Spec (.of k) ⟶ (power C 9).left) (hp : p ≫ (power C 9).hom = 𝟙 _)
    (hker : 3 ≤ Module.finrank k (LinearMap.ker (moduleSpecΓFunctor.map
      ((Scheme.Modules.pullback p).map (differential k C c₀ hg))).hom)) :
    Nonempty (LinearSeries k C.hom
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := C.hom)).le 8 2) := by
  let L := DirectC9OriginalPoint.pointLine k C c₀ p hp
  haveI : SheafOfModules.IsInvertible C.left.presheaf C.left.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (DirectC9OriginalPoint.pointLine_isInvertible k C c₀ p hp)
  exact LinearSeriesFromCohomology.nonempty_linearSeries_of_finrank_H0
    k C.hom (IsCurve.topologicalKrullDim_eq_one (k := k) (f := C.hom)).le L 8 2
    (DirectC9OriginalPoint.pointLine_degree k C c₀ p hp)
    (pointH0_ge_three_of_kernel_ge_three k C c₀ hg p hp hker)

/-- Failure of the native net statement bounds all actual base-field kernels
of the SAME single global differential. -/
theorem point_kernel_le_two_of_no_net
    (hno : ¬ Nonempty (LinearSeries k C.hom
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := C.hom)).le 8 2))
    (p : Spec (.of k) ⟶ (power C 9).left) (hp : p ≫ (power C 9).hom = 𝟙 _) :
    Module.finrank k (LinearMap.ker (moduleSpecΓFunctor.map
      ((Scheme.Modules.pullback p).map (differential k C c₀ hg))).hom) ≤ 2 := by
  let L := DirectC9OriginalPoint.pointLine k C c₀ p hp
  haveI : SheafOfModules.IsInvertible C.left.presheaf C.left.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (DirectC9OriginalPoint.pointLine_isInvertible k C c₀ p hp)
  exact NoNetKernelBound.linearKernel_finrank_le_two_of_no_degree_eight_net
    k C.hom (IsCurve.topologicalKrullDim_eq_one (k := k) (f := C.hom)).le hno L
    (DirectC9OriginalPoint.pointLine_degree k C c₀ p hp)
    ((Scheme.Modules.pullback p).map (differential k C c₀ hg))
    (pointKernelIso k C c₀ hg p hp)

include hg

/-- A nonzero actual incidence cap yields an actual native degree-eight net.
The global differential and every cohomology comparison are derived. -/
theorem nonempty_degree_eight_net_of_topCap_ne_zero
    (n : ℤ) :
    letI hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (E10 k C c₀) 10 :=
      DirectC9Bundles.E10_rank k C c₀ hg
    letI hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (F10 k C c₀) 10 :=
      DirectC9Bundles.F10_rank k C c₀
    letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (E10 k C c₀) := hE.isFiniteLocallyFree
    letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (dualSheaf (E10 k C c₀)) :=
      isFiniteLocallyFree_dualSheaf (E10 k C c₀) inferInstance
    letI : IsProper (FlagThreeIncidence.projection (E10 k C c₀)) :=
      FlagTowerProper.isProper_tower 3 (dualSheaf (E10 k C c₀))
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
        (FlagThreeIncidence.incidenceBundle (E10 k C c₀) (F10 k C c₀)) 30 :=
      FlagThreeIncidence.incidenceBundle_rank_thirty (E10 k C c₀) (F10 k C c₀) hF
    ∀ (α : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k)
      (FlagThreeIncidence.projection (E10 k C c₀) ≫ (power C 9).hom) n)
    (_hne : Stacks.Chow.GenuineChern.chernCap (Stacks.Chow.fieldChowSituation k) 30
      (FlagThreeIncidence.projection (E10 k C c₀) ≫ (power C 9).hom)
      (FlagThreeIncidence.incidenceBundle (E10 k C c₀) (F10 k C c₀)) n (Fin.last 30) α ≠ 0),
    Nonempty (LinearSeries k C.hom
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := C.hom)).le 8 2) := by
  haveI hE := DirectC9Bundles.E10_rank k C c₀ hg
  haveI hF := DirectC9Bundles.F10_rank k C c₀
  haveI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (E10 k C c₀) := hE.isFiniteLocallyFree
  haveI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (dualSheaf (E10 k C c₀)) :=
    isFiniteLocallyFree_dualSheaf (E10 k C c₀) inferInstance
  haveI : IsProper (FlagThreeIncidence.projection (E10 k C c₀)) :=
    FlagTowerProper.isProper_tower 3 (dualSheaf (E10 k C c₀))
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (FlagThreeIncidence.incidenceBundle (E10 k C c₀) (F10 k C c₀)) 30 :=
    FlagThreeIncidence.incidenceBundle_rank_thirty (E10 k C c₀) (F10 k C c₀) hF
  dsimp only
  intro α hne
  obtain ⟨p,hp,hker⟩ :=
    FlagThreeKernelExistence.exists_base_field_point_kernel_ge_three_of_topCap_ne_zero
      k (power C 9).hom (E10 k C c₀) (F10 k C c₀) (differential k C c₀ hg) n α hne
  exact nonempty_degree_eight_net_of_point_kernel_ge_three k C c₀ hg p hp hker

/-- The actual no-net statement annihilates every class under the original
incidence top cap, with no extension-field nonexistence premise. -/
theorem topCap_eq_zero_of_no_net
    (hno : ¬ Nonempty (LinearSeries k C.hom
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := C.hom)).le 8 2))
    (n : ℤ) :
    letI hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (E10 k C c₀) 10 :=
      DirectC9Bundles.E10_rank k C c₀ hg
    letI hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (F10 k C c₀) 10 :=
      DirectC9Bundles.F10_rank k C c₀
    letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (E10 k C c₀) := hE.isFiniteLocallyFree
    letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (dualSheaf (E10 k C c₀)) :=
      isFiniteLocallyFree_dualSheaf (E10 k C c₀) inferInstance
    letI : IsProper (FlagThreeIncidence.projection (E10 k C c₀)) :=
      FlagTowerProper.isProper_tower 3 (dualSheaf (E10 k C c₀))
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
        (FlagThreeIncidence.incidenceBundle (E10 k C c₀) (F10 k C c₀)) 30 :=
      FlagThreeIncidence.incidenceBundle_rank_thirty (E10 k C c₀) (F10 k C c₀) hF
    ∀ (α : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k)
      (FlagThreeIncidence.projection (E10 k C c₀) ≫ (power C 9).hom) n),
    Stacks.Chow.GenuineChern.chernCap (Stacks.Chow.fieldChowSituation k) 30
      (FlagThreeIncidence.projection (E10 k C c₀) ≫ (power C 9).hom)
      (FlagThreeIncidence.incidenceBundle (E10 k C c₀) (F10 k C c₀)) n (Fin.last 30) α = 0 := by
  haveI hE := DirectC9Bundles.E10_rank k C c₀ hg
  haveI hF := DirectC9Bundles.F10_rank k C c₀
  haveI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (E10 k C c₀) := hE.isFiniteLocallyFree
  haveI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (dualSheaf (E10 k C c₀)) :=
    isFiniteLocallyFree_dualSheaf (E10 k C c₀) inferInstance
  haveI : IsProper (FlagThreeIncidence.projection (E10 k C c₀)) :=
    FlagTowerProper.isProper_tower 3 (dualSheaf (E10 k C c₀))
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (FlagThreeIncidence.incidenceBundle (E10 k C c₀) (F10 k C c₀)) 30 :=
    FlagThreeIncidence.incidenceBundle_rank_thirty (E10 k C c₀) (F10 k C c₀) hF
  dsimp only
  intro α
  exact FlagThreeIncidenceChow.topCap_eq_zero_of_base_field_kernel_le_two
    k (power C 9).hom (E10 k C c₀) (F10 k C c₀) (differential k C c₀ hg)
    (point_kernel_le_two_of_no_net k C c₀ hg hno) n α

end M9Native.DirectC9KernelNet
