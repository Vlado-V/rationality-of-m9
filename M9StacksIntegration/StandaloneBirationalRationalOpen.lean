module

public import M9StacksIntegration.StandaloneDenseOpen
public import Mathlib.AlgebraicGeometry.Birational.Birational

/-! An actual birational common open yields the literal standalone rational
open, with its all-test etale density and original coefficient base. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9Native.StandaloneBirationalRationalOpen

variable (K : Type u) [Field K]

def affineProjection (n : ℕ) :
    AffineSpace (ULift.{u} (Fin n)) (M9StandaloneDraft.Base K) ⟶ M9StandaloneDraft.Base K :=
  pullback.fst _ _

/-- No field identification is substituted for the required genuine common
open: this theorem constructs that open and retains both base maps. -/
theorem rationalOpen_of_birationalOver (n : ℕ) (X : M9StandaloneDraft.Schemes K)
    [Nonempty X.left]
    (h : Scheme.BirationalOver X.hom (affineProjection K n)) :
    M9StandaloneDraft.RationalOpen K n (yoneda.obj X) := by
  obtain ⟨f,hf⟩ := h
  let U : M9StandaloneDraft.Schemes K := Over.mk (f.source.ι ≫ X.hom)
  let j : U ⟶ X := Over.homMk f.source.ι rfl
  haveI : IsOpenImmersion j.left := by
    change IsOpenImmersion f.source.ι
    infer_instance
  have hj : DenseRange j.left := by
    change Dense (Set.range f.source.ι)
    rw [Scheme.Opens.range_ι]
    exact f.dense_source
  have hU : Nonempty U.left := by
    obtain ⟨x,hx⟩ := f.dense_source.nonempty
    exact ⟨⟨x,hx⟩⟩
  refine ⟨U,yoneda.map j,hU,StandaloneDenseOpen.denseOpen_yoneda K j hj,?_,?_,?_,?_⟩
  · exact f.iso.hom ≫ f.target.ι
  · infer_instance
  · change Dense (Set.range (f.target.ι ∘ f.iso.hom))
    rw [f.iso.hom.surjective.range_comp,Scheme.Opens.range_ι]
    exact f.dense_target
  · change (f.iso.hom ≫ f.target.ι) ≫ affineProjection K n = f.source.ι ≫ X.hom
    change f.iso.hom ≫ f.target.ι ≫ affineProjection K n = f.source.ι ≫ X.hom at hf
    simpa only [Category.assoc] using hf

end M9Native.StandaloneBirationalRationalOpen
