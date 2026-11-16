module
public import Mathlib.AlgebraicGeometry.Cover.Open

@[expose] public noncomputable section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u v
namespace M9Native.CoverIsoRefinement

/-- A genuine cover retains coverage when its charts are transported
through actual isomorphisms with their actual map triangles. -/
theorem covers {X : Scheme.{u}} (U : X.OpenCover) {ι : Type v}
    (Y : ι → Scheme.{u}) (f : (i : ι) → Y i ⟶ X) (j : U.I₀ → ι)
    (e : (i : U.I₀) → U.X i ≅ Y (j i))
    (he : ∀ i : U.I₀, (e i).hom ≫ f (j i) = U.f i) (x : X) :
    ∃ i : ι, x ∈ Set.range (f i) := by
  obtain ⟨i,z,hz⟩ := Scheme.Cover.exists_eq U x
  refine ⟨j i,(e i).hom z,?_⟩
  exact (Scheme.Hom.comp_apply (e i).hom (f (j i)) z).symm.trans
    ((congrArg (fun a : U.X i ⟶ X => a z) (he i)).trans hz)

end M9Native.CoverIsoRefinement
