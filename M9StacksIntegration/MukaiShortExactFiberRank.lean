module

public import M9StacksIntegration.MukaiEvaluationImage
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Fibre rank of an epimorphism followed by a short-exact inclusion

All maps are the original sheaf maps and all fibres are the residue-field
tensors used by `MukaiSemiIrreducible.mapRankAt`. Right exactness of tensor
product transfers the actual stalk exact pair to the actual fibres. Thus
an epimorphism followed by the inclusion in a rank-three extension of a
line bundle has rank two everywhere. No left exactness of general pullback
is used or assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace M9Native.MukaiShortExactFiberRank

open MukaiSaturationRank TupleEvaluationFiber

variable {X : Scheme.{u}}

/-- An actual sheaf epimorphism is surjective on the original residue fibres. -/
theorem fiberMap_surjective {A B : X.Modules} (δ : A ⟶ B) [Epi δ] (x : X) :
    Function.Surjective (inducedFiberMap δ x) := by
  let := residueAlgebra x
  change Function.Surjective ((stalkMap δ x).baseChange (X.residueField x))
  exact LinearMap.baseChange_surjective (X.residueField x)
    (MukaiEvaluationImage.stalkMap_surjective δ x)

/-- The actual residue-fibre maps respect composition of the original sheaf maps. -/
theorem fiberMap_comp {A B C : X.Modules} (δ : A ⟶ B) (i : B ⟶ C) (x : X) :
    inducedFiberMap (δ ≫ i) x = (inducedFiberMap i x).comp (inducedFiberMap δ x) := by
  let := residueAlgebra x
  change (stalkMap (δ ≫ i) x).baseChange (X.residueField x) =
    ((stalkMap i x).baseChange (X.residueField x)).comp
      ((stalkMap δ x).baseChange (X.residueField x))
  rw [← LinearMap.baseChange_comp]
  congr 1
  ext s
  exact stalkMap_comp δ i x s

/-- Right exactness preserves the original exact stalk pair on the actual fibres. -/
theorem fiberMap_exact (S : ShortComplex X.Modules) (hS : S.Exact) [Epi S.g] (x : X) :
    Function.Exact (inducedFiberMap S.f x) (inducedFiberMap S.g x) := by
  let := residueAlgebra x
  change Function.Exact ((stalkMap S.f x).baseChange (X.residueField x))
    ((stalkMap S.g x).baseChange (X.residueField x))
  simpa only [LinearMap.baseChange_eq_lTensor] using
    (lTensor_exact (X.residueField x) (stalkMap_exact S hS x)
      (MukaiEvaluationImage.stalkMap_surjective S.g x))

/-- An epimorphic choice of generators has the full fibre image of the inclusion. -/
theorem range_fiberMap_comp {A B C : X.Modules} (δ : A ⟶ B) [Epi δ]
    (i : B ⟶ C) (x : X) :
    LinearMap.range (inducedFiberMap (δ ≫ i) x) =
      LinearMap.range (inducedFiberMap i x) := by
  rw [fiberMap_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (fiberMap_surjective δ x), Submodule.map_top]

/-- The rank of the original composite plus the quotient rank is the middle rank. -/
theorem mapRankAt_comp_add_quotient_rank (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (b c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₂ b]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ c]
    {A : X.Modules} (δ : A ⟶ S.X₁) [Epi δ] (x : X) :
    MukaiSemiIrreducible.mapRankAt (δ ≫ S.f) x + c = b := by
  let := residueAlgebra x
  let : Epi S.g := hS.epi_g
  let : Module.Finite (X.residueField x) (Fiber S.X₂ x) := fiberFinite S.X₂ b x
  have he := fiberMap_exact S hS.exact x
  have hs := fiberMap_surjective S.g x
  have hd := (inducedFiberMap S.g x).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, he.linearMap_ker_eq,
    finrank_fiber S.X₃ c x, finrank_fiber S.X₂ b x] at hd
  change Module.finrank (X.residueField x)
    (LinearMap.range (inducedFiberMap (δ ≫ S.f) x)) + c = b
  rw [range_fiberMap_comp]
  exact (Nat.add_comm _ _).trans hd

/-- The fibre rank is the difference of the actual middle and quotient ranks. -/
theorem everywhereRank_comp (S : ShortComplex X.Modules) (hS : S.ShortExact) (b c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₂ b]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ c]
    {A : X.Modules} (δ : A ⟶ S.X₁) [Epi δ] :
    MukaiSemiIrreducible.EverywhereRank (δ ≫ S.f) (b - c) := by
  intro x
  have h := mapRankAt_comp_add_quotient_rank S hS b c δ x
  omega

/-- In an original rank-three extension by an invertible quotient, any epimorphic
three-generator map onto the subbundle has the literal everywhere rank two. -/
theorem everywhereRank_freeThree_comp_inclusion (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₂ 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property S.X₃]
    (δ : _root_.SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 3)) ⟶ S.X₁)
    [Epi δ] : MukaiSemiIrreducible.EverywhereRank (δ ≫ S.f) 2 := by
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X S.X₃
  exact everywhereRank_comp S hS 3 1 δ

end M9Native.MukaiShortExactFiberRank
