module

public import M9StacksIntegration.GenusNineTricanonicalCohomology
public import M9StacksIntegration.PencilDegreePullback
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-! The genuine external graph polarization of a smooth genus-nine curve.
For any fixed degree-one invertible line on the target curve, its restriction
to the actual graph is the original tricanonical line tensor the actual
pullback target line. Native function-field degree and Riemann--Roch give
the polynomial (48+d)m-8 for every integer m. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RelativeVeryAmple
universe u
namespace M9Native.GenusNineGraphPolarization
open GenusNineTricanonicalCohomology
variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
variable [IsProper pX] [IsCurve k pX] [Smooth pX]
variable (g : X ⟶ Y) (hg : g ≫ pY = pX) (M : Y.Modules)

def graphMap : X ⟶ pullback pX pY :=
  pullback.lift (𝟙 X) g (by simpa using hg.symm)

@[simp] theorem graphMap_fst : graphMap pX pY g hg ≫ pullback.fst pX pY = 𝟙 X :=
  pullback.lift_fst _ _ _

@[simp] theorem graphMap_snd : graphMap pX pY g hg ≫ pullback.snd pX pY = g :=
  pullback.lift_snd _ _ _

instance graphMap_isClosedImmersion [IsSeparated pY] :
    IsClosedImmersion (graphMap pX pY g hg) := by
  have : IsClosedImmersion (graphMap pX pY g hg ≫ pullback.fst pX pY) := by
    rw [graphMap_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst pX pY)

def graphLine : X.Modules :=
  tensorModules X (tricanonical pX) ((Scheme.Modules.pullback g).obj M)

def externalPolarization : (pullback pX pY).Modules :=
  tensorModules (pullback pX pY)
    ((Scheme.Modules.pullback (pullback.fst pX pY)).obj (tricanonical pX))
    ((Scheme.Modules.pullback (pullback.snd pX pY)).obj M)

def graphLineIso :
    (Scheme.Modules.pullback (graphMap pX pY g hg)).obj (externalPolarization pX pY M) ≅
      graphLine pX g M :=
  pullbackTensorModulesIso _ _ _ ≪≫ tensorModulesMapIso X
    ((Scheme.Modules.pullbackComp _ _).app (tricanonical pX) ≪≫
      (Scheme.Modules.pullbackCongr (graphMap_fst pX pY g hg)).app (tricanonical pX) ≪≫
      (Scheme.Modules.pullbackId X).app (tricanonical pX))
    ((Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (graphMap_snd pX pY g hg)).app M)

variable [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property M]

instance graphLine_isInvertible :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (graphLine pX g M) := by
  let := Stacks.InvertiblePullback.isInvertibleModule_pullback g M
  dsimp only [graphLine]
  infer_instance

instance externalPolarization_isInvertible :
    SheafOfModules.IsInvertible (pullback pX pY).presheaf
      (pullback pX pY).ringCatSheaf.property (externalPolarization pX pY M) := by
  let := Stacks.InvertiblePullback.isInvertibleModule_pullback
    (pullback.fst pX pY) (tricanonical pX)
  let := Stacks.InvertiblePullback.isInvertibleModule_pullback (pullback.snd pX pY) M
  dsimp only [externalPolarization]
  infer_instance

def graphTensorPower (m : ℤ) : X.Modules :=
  Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.property
    (graphLine pX g M) m

instance graphTensorPower_isInvertible (m : ℤ) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (graphTensorPower pX g M m) :=
  Stacks.SheafOfModules.Invertible.tensorPower_isInvertible _ _ _ m

variable [IsProper pY] [IsCurve k pY]
variable [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop)]

theorem graphLine_degree (hdimX : topologicalKrullDim X ≤ 1)
    (hdimY : topologicalKrullDim Y ≤ 1) (hgen : genus pX = 9)
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y)
    (hM : invertibleCurveDegree k pY hdimY M = 1) :
    invertibleCurveDegree k pX hdimX (graphLine pX g M) =
      48 + (PencilDegreePullback.curveMapDegree pX pY g hg hnc : ℤ) := by
  let := Stacks.InvertiblePullback.isInvertibleModule_pullback g M
  exact (invertibleCurveDegree_tensorSheaf_eq_add k pX hdimX
    (tricanonical pX) ((Scheme.Modules.pullback g).obj M)).trans
      (congrArg₂ (· + ·) (tricanonical_degree pX hdimX hgen)
        (PencilDegreePullback.pullback_degree_eq_curveMapDegree pX pY hdimX hdimY
          g hg hnc M hM))

theorem graphTensorPower_euler (hdimX : topologicalKrullDim X ≤ 1)
    (hdimY : topologicalKrullDim Y ≤ 1) (hgen : genus pX = 9)
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y)
    (hM : invertibleCurveDegree k pY hdimY M = 1) (m : ℤ) :
    (∑ᶠ i : ℕ, (-1 : ℤ)^i *
      (Module.finrank k (cohomologyOverField k pX (graphTensorPower pX g M m) i) : ℤ)) =
      (48 + (PencilDegreePullback.curveMapDegree pX pY g hg hnc : ℤ)) * m - 8 := by
  have hp := invertibleCurveDegree_tensorPower_eq_mul k pX hdimX (graphLine pX g M)
    (@invertibleCurveDegree_tensorSheaf_eq_add k _ X pX _ hdimX) m
  change invertibleCurveDegree k pX hdimX (graphTensorPower pX g M m) =
    m * invertibleCurveDegree k pX hdimX (graphLine pX g M) at hp
  rw [graphLine_degree pX pY g hg M hdimX hdimY hgen hnc hM] at hp
  have hO := eulerCharacteristic_unit_eq_one_sub_genus k pX hdimX
  change (∑ᶠ i : ℕ, (-1 : ℤ)^i *
    (Module.finrank k (cohomologyOverField k pX (SheafOfModules.unit X.ringCatSheaf) i) : ℤ)) =
      1 - (genus pX : ℤ) at hO
  rw [hgen] at hO
  change (∑ᶠ i : ℕ, (-1 : ℤ)^i *
    (Module.finrank k (cohomologyOverField k pX (graphTensorPower pX g M m) i) : ℤ)) -
      (∑ᶠ i : ℕ, (-1 : ℤ)^i *
    (Module.finrank k (cohomologyOverField k pX (SheafOfModules.unit X.ringCatSheaf) i) : ℤ)) =
      m * (48 + (PencilDegreePullback.curveMapDegree pX pY g hg hnc : ℤ)) at hp
  rw [hO] at hp
  have hr : (1 : ℤ) - (9 : ℕ) = -8 := by norm_num
  rw [hr] at hp
  nlinarith only [hp]

end M9Native.GenusNineGraphPolarization
end
