module

public import M9StacksIntegration.AllTestLargeSiteAtlas

/-!
# Actual kernel pairs and diagonal charts

These universal-property proofs work in the actual category of presheaves
used for original all-test families, as well as in any category with the
displayed products. They turn a PROVED kernel-pair square into the actual
pullback square of the diagonal; no assumed presentation equivalence occurs.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace M9StacksIntegration.AllTestKernelPairDiagonal
universe v u
variable {C : Type u} [Category.{v} C]

/-- The relation map of an actual kernel pair is monomorphic. -/
theorem mono_relation_of_kernelPair {R U F : C} [HasBinaryProduct U U]
    {s t : R ⟶ U} {a : U ⟶ F} (h : IsPullback s t a a) :
    Mono (prod.lift s t) := by
  constructor
  intro W f g he
  apply h.hom_ext
  · simpa only [Category.assoc, prod.lift_fst] using
      congrArg (fun m => m ≫ prod.fst) he
  · simpa only [Category.assoc, prod.lift_snd] using
      congrArg (fun m => m ≫ prod.snd) he

/-- The actual kernel pair is the actual represented chart of the diagonal. -/
theorem isPullback_diagonal_of_kernelPair {R U F : C}
    [HasBinaryProduct U U] [HasBinaryProduct F F]
    {s t : R ⟶ U} {a : U ⟶ F} (h : IsPullback s t a a) :
    IsPullback (s ≫ a) (prod.lift s t) (diag F) (prod.map a a) where
  w := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, Category.comp_id,
        prod.map_fst, prod.lift_fst_assoc]
    · simpa only [Category.assoc, prod.lift_snd, Category.comp_id,
        prod.map_snd, prod.lift_snd_assoc] using h.w
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun c => by
    have hu : (c.snd ≫ prod.fst) ≫ a = c.fst := by
      simpa only [Category.assoc, prod.lift_fst, Category.comp_id,
        prod.map_fst, prod.lift_fst_assoc] using
          (congrArg (fun m => m ≫ prod.fst) c.condition).symm
    have hv : (c.snd ≫ prod.snd) ≫ a = c.fst := by
      simpa only [Category.assoc, prod.lift_snd, Category.comp_id,
        prod.map_snd, prod.lift_snd_assoc] using
          (congrArg (fun m => m ≫ prod.snd) c.condition).symm
    refine ⟨h.lift (c.snd ≫ prod.fst) (c.snd ≫ prod.snd) (hu.trans hv.symm), ?_, ?_, ?_⟩
    · change (h.lift _ _ _) ≫ (s ≫ a) = c.fst
      rw [← Category.assoc, h.lift_fst]
      exact hu
    · change (h.lift _ _ _) ≫ prod.lift s t = c.snd
      apply prod.hom_ext
      · simp only [Category.assoc, prod.lift_fst, h.lift_fst]
      · simp only [Category.assoc, prod.lift_snd, h.lift_snd]
    · intro m _hm₁ hm₂
      change m ≫ prod.lift s t = c.snd at hm₂
      apply h.hom_ext
      · rw [h.lift_fst]
        simpa only [Category.assoc, prod.lift_fst] using
          congrArg (fun k => k ≫ prod.fst) hm₂
      · rw [h.lift_snd]
        simpa only [Category.assoc, prod.lift_snd] using
          congrArg (fun k => k ≫ prod.snd) hm₂)⟩

end M9StacksIntegration.AllTestKernelPairDiagonal
