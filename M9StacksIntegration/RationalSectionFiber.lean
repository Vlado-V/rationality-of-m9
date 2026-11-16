/-
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Thin adaptation of pinned AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
DerivedVarieties/NoDeformations/RationalPointFibre.lean, rational-point
residue-field and fibre-square proofs.  The broad ConstantFamily typedefs
are replaced by the literal Mathlib pullback; only Mathlib.Fiber is needed.
The source snapshot and hash are retained in the owned audit directory.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.Topology.Dimension.Krull

/-! The actual pullback at a rational section is the actual residue-field
fibre, with both projections retained.  The residue-field identification
is proved from the section triangle, rather than assumed. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.RationalSectionFiber

variable (K : Type u) [Field K]

/-- The canonical residue-field homomorphism of the actual field point. -/
def residueHom {Y : Scheme.{u}} (p : Spec (.of K) ⟶ Y) :
    Y.residueField (p (IsLocalRing.closedPoint K)) ⟶ CommRingCat.of K :=
  Y.descResidueField (Scheme.stalkClosedPointTo p)

/-- The actual section triangle forces its residue-field homomorphism
to be an isomorphism. -/
theorem residueHom_isIso {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of K))
    (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _) : IsIso (residueHom K p) := by
  set ψ := residueHom K p
  have hfac : Spec.map ψ ≫ Y.fromSpecResidueField (p (IsLocalRing.closedPoint K)) = p :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y p
  set τ := Spec.preimage (Y.fromSpecResidueField (p (IsLocalRing.closedPoint K)) ≫ pY)
  have hτψ : τ ≫ ψ = 𝟙 (CommRingCat.of K) :=
    Spec.map_inj.mp (by
      rw [Spec.map_comp, Spec.map_id, Spec.map_preimage, ← Category.assoc, hfac, hp])
  exact (ConcreteCategory.isIso_iff_bijective ψ).mpr
    ⟨RingHom.injective _, fun z => ⟨τ.hom z,
      congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of K => h.hom z) hτψ⟩⟩

/-- The actual residue-field spectrum isomorphism of a rational section. -/
def residueSpecIso {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of K))
    (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _) :
    Spec (.of K) ≅ Spec (Y.residueField (p (IsLocalRing.closedPoint K))) := by
  let := residueHom_isIso K pY p hp
  exact asIso (Spec.map (residueHom K p))

theorem residueSpecIso_factor {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of K))
    (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _) :
    (residueSpecIso K pY p hp).hom ≫
      Y.fromSpecResidueField (p (IsLocalRing.closedPoint K)) = p :=
  Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y p

/-- The original rational-point pullback square, with its base edge
identified with the original canonical residue-field morphism. -/
theorem isPullback_fiber {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of K)) (f : X ⟶ Y)
    (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _) :
    IsPullback (pullback.fst f p) (pullback.snd f p ≫ (residueSpecIso K pY p hp).hom)
      f (Y.fromSpecResidueField (p (IsLocalRing.closedPoint K))) := by
  have hbot : IsPullback p (residueSpecIso K pY p hp).hom (𝟙 Y)
      (Y.fromSpecResidueField (p (IsLocalRing.closedPoint K))) :=
    IsPullback.of_vert_isIso ⟨by
      rw [Category.comp_id, residueSpecIso_factor K pY p hp]⟩
  have h := (IsPullback.of_hasPullback f p).paste_vert hbot
  rwa [Category.comp_id] at h

/-- The actual scheme isomorphism, retaining the original fibre. -/
def fiberIso {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of K)) (f : X ⟶ Y)
    (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _) :
    pullback f p ≅ f.fiber (p (IsLocalRing.closedPoint K)) :=
  (isPullback_fiber K pY f p hp).isoPullback

@[reassoc (attr := simp)] theorem fiberIso_hom_fiberι {X Y : Scheme.{u}}
    (pY : Y ⟶ Spec (.of K)) (f : X ⟶ Y) (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _) :
    (fiberIso K pY f p hp).hom ≫ f.fiberι (p (IsLocalRing.closedPoint K)) = pullback.fst f p :=
  (isPullback_fiber K pY f p hp).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem fiberIso_hom_fiberToSpec {X Y : Scheme.{u}}
    (pY : Y ⟶ Spec (.of K)) (f : X ⟶ Y) (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _) :
    (fiberIso K pY f p hp).hom ≫ f.fiberToSpecResidueField (p (IsLocalRing.closedPoint K)) =
      pullback.snd f p ≫ (residueSpecIso K pY p hp).hom :=
  (isPullback_fiber K pY f p hp).isoPullback_hom_snd

/-- Smoothness of the original rational-point curve transfers to the
original residue-field fibre through the proved actual isomorphisms. -/
theorem fiber_smooth {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of K)) (f : X ⟶ Y)
    (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _)
    [Smooth (pullback.snd f p)] : Smooth (f.fiberToSpecResidueField (p (IsLocalRing.closedPoint K))) := by
  let e := fiberIso K pY f p hp
  have he : f.fiberToSpecResidueField (p (IsLocalRing.closedPoint K)) =
      e.inv ≫ pullback.snd f p ≫ (residueSpecIso K pY p hp).hom := by
    calc
      _ = e.inv ≫ e.hom ≫ f.fiberToSpecResidueField (p (IsLocalRing.closedPoint K)) := by simp
      _ = _ := congrArg (fun h => e.inv ≫ h) (fiberIso_hom_fiberToSpec K pY f p hp)
  rw [he]
  infer_instance

/-- Irreducibility transfers on the original underlying schemes. -/
theorem fiber_irreducible {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of K)) (f : X ⟶ Y)
    (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _) [IrreducibleSpace (pullback (C := Scheme.{u}) f p)] :
    IrreducibleSpace (f.fiber (p (IsLocalRing.closedPoint K))) :=
  (Scheme.homeoOfIso (fiberIso K pY f p hp)).irreducibleSpace_iff.mp inferInstance

/-- Dimension is retained by the actual fibre comparison. -/
theorem fiber_dimension {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of K)) (f : X ⟶ Y)
    (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _) {r : ℕ}
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) f p) = (r : WithBot ℕ∞)) :
    topologicalKrullDim (f.fiber (p (IsLocalRing.closedPoint K))) = (r : WithBot ℕ∞) := by
  let e := Scheme.homeoOfIso (fiberIso K pY f p hp)
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm.trans hdim

end M9Native.RationalSectionFiber
