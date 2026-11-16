module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Functor

/-!
# The actual cokernel map induced by a cotangent chain map

The map is constructed by the original cokernel universal property from
the actual chain-map identity. Thus its projection square is derived,
never supplied as a hypothesis. This applies to the original cotangent
pushforward square even when the right adjoint is not exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u' v'

namespace M9Native.CotangentCokernelMap

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (G : C ⥤ D) [G.Additive]
  (K₀ : CochainComplex D ℤ) (K : CochainComplex C ℤ)
  (a : K₀ ⟶ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

/-- The actual chain-map identity makes the projected degree-zero map kill boundaries. -/
theorem differential_comp_projected_map_zero :
    K₀.d (-1) 0 ≫ (a.f 0 ≫ G.map (cokernel.π (K.d (-1) 0))) = 0 := by
  calc
    _ = (a.f (-1) ≫ G.map (K.d (-1) 0)) ≫ G.map (cokernel.π (K.d (-1) 0)) := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun b => b ≫ G.map (cokernel.π (K.d (-1) 0)))
          (a.comm (-1) 0).symm)
    _ = a.f (-1) ≫ G.map (K.d (-1) 0 ≫ cokernel.π (K.d (-1) 0)) := by
      rw [Category.assoc, ← G.map_comp]
    _ = 0 := by rw [cokernel.condition, G.map_zero, comp_zero]

/-- The actual induced cokernel morphism, with no compatibility premise. -/
def cokernelMap : cokernel (K₀.d (-1) 0) ⟶ G.obj (cokernel (K.d (-1) 0)) :=
  cokernel.desc _ (a.f 0 ≫ G.map (cokernel.π (K.d (-1) 0)))
    (differential_comp_projected_map_zero G K₀ K a)

/-- Its defining projection square follows from the genuine universal property. -/
theorem π_comp_cokernelMap :
    cokernel.π (K₀.d (-1) 0) ≫ cokernelMap G K₀ K a =
      a.f 0 ≫ G.map (cokernel.π (K.d (-1) 0)) :=
  cokernel.π_desc _ _ _

/-- No vanishing condition is lost when passing from the degree-zero
projected chain map to the actual cokernel map. -/
theorem cokernelMap_eq_zero_iff :
    cokernelMap G K₀ K a = 0 ↔ a.f 0 ≫ G.map (cokernel.π (K.d (-1) 0)) = 0 := by
  constructor
  · intro h
    rw [← π_comp_cokernelMap G K₀ K a, h, comp_zero]
  · intro h
    apply (cancel_epi (cokernel.π (K₀.d (-1) 0))).mp
    rw [π_comp_cokernelMap, h, comp_zero]

end M9Native.CotangentCokernelMap
