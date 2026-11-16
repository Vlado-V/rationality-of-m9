module

public import StacksFrontier.AlgebraicGeometry.Stacks.PredeformationBaseChange

/-!
# The original change-of-base predeformation functor is an equivalence

The native functor retains the original algebra and arrow of each deformation.
Its original lifting lemmas prove fullness and essential surjectivity; the
literal arrow fields prove faithfulness. This upgrades the actual native
base-change comparison, rather than supplying a formal-deformation equivalence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Deformation Deformation.Artin

universe u u₁ v₁ u₂ v₂

namespace M9Native.PredeformationChangeBaseEquivalence

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {S S' : Scheme.{u}} (iS : Spec (.of Λ) ⟶ S) (g : S ⟶ S')
variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
variable (qX : X ⥤ Over S) (qY : Y ⥤ Over S') (Φ : X ⥤ Y)
  (hΦ : Φ ⋙ qY = qX ⋙ Over.map g) [Φ.Faithful]
  (x₀ : X)
  (hx₀ : qX.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iS))
  (hy₀ : qY.obj (Φ.obj x₀) =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ (iS ≫ g)))

/-- Faithfulness is inherited from the actual projected deformation arrow. -/
theorem faithful :
    letI := (predeformationCategory iS qX x₀ hx₀).category
    letI := (predeformationCategory (iS ≫ g) qY (Φ.obj x₀) hy₀).category
    (predeformationFunctorOfCompEqCompMap iS g qX qY Φ hΦ x₀ hx₀ hy₀).toFunctor.Faithful := by
  letI := (predeformationCategory iS qX x₀ hx₀).category
  letI := (predeformationCategory (iS ≫ g) qY (Φ.obj x₀) hy₀).category
  let Ψ := predeformationFunctorOfCompEqCompMap iS g qX qY Φ hΦ x₀ hx₀ hy₀
  refine ⟨fun {a b} f₁ f₂ h => ?_⟩
  apply DeformationMorphism.ext_of_components
  · exact congrArg (fun m : Ψ.obj a ⟶ Ψ.obj b => m.ringHom) h
  · apply Φ.map_injective
    exact congrArg (fun m : Ψ.obj a ⟶ Ψ.obj b => m.arrow) h

/-- Actual native compatible lifting gives the actual functor equivalence. -/
theorem isEquivalence
    (hfull : LiftsCompEqCompMap g qX qY Φ hΦ)
    (hobj : ∀ (y : Y) (T : Over S), qY.obj y = (Over.map g).obj T →
      ∃ x : X, Φ.obj x = y ∧ qX.obj x = T) :
    letI := (predeformationCategory iS qX x₀ hx₀).category
    letI := (predeformationCategory (iS ≫ g) qY (Φ.obj x₀) hy₀).category
    (predeformationFunctorOfCompEqCompMap iS g qX qY Φ hΦ x₀ hx₀ hy₀).toFunctor.IsEquivalence := by
  letI := (predeformationCategory iS qX x₀ hx₀).category
  letI := (predeformationCategory (iS ≫ g) qY (Φ.obj x₀) hy₀).category
  let Ψ := predeformationFunctorOfCompEqCompMap iS g qX qY Φ hΦ x₀ hx₀ hy₀
  letI : Ψ.toFunctor.Faithful := faithful iS g qX qY Φ hΦ x₀ hx₀ hy₀
  letI : Ψ.toFunctor.Full :=
    predeformationFunctorOfCompEqCompMap_full iS x₀ hx₀ hy₀ (hΦ := hΦ) hfull
  letI : Ψ.toFunctor.EssSurj := ⟨fun y => by
    obtain ⟨d, hd⟩ := exists_deformationObjectOfCompEqCompMap_eq iS x₀ hx₀ hy₀
      (hΦ := hΦ) hfull hobj y
    exact ⟨d, ⟨eqToIso hd⟩⟩⟩
  exact Functor.IsEquivalence.mk

end M9Native.PredeformationChangeBaseEquivalence
