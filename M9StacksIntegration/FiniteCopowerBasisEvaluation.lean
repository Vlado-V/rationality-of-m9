module

public import M9StacksIntegration.FiniteCopowerBasisChange

/-! Actual evaluation triangles under a finite free change of basis. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v w z x

namespace M9Native.FiniteCopowerBasisChange

variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
  [Preadditive C] [Linear k C] (O B : C)
  {I J : Type z} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [HasCoproduct (fun _ : I => O)] [HasCoproduct (fun _ : J => O)]

/-- A literal coefficient identity gives the actual coproduct evaluation triangle. -/
theorem evaluation_triangle (e : (I → k) ≃ₗ[k] (J → k))
    (tI : I → (O ⟶ B)) (tJ : J → (O ⟶ B))
    (h : ∀ i, tI i = ∑ j, e (Pi.single i 1) j • tJ j) :
    (linearEquivIso O e).hom ≫ Sigma.desc tJ = Sigma.desc tI := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, linearEquivIso_generator, Preadditive.sum_comp]
  simpa only [Linear.smul_comp, Sigma.ι_comp_desc] using (h i).symm

/-- The coefficient identity for two actual bases is derived by expansion,
rather than assumed as an extra evaluation compatibility. -/
theorem basis_evaluation_triangle {V : Type x} [AddCommGroup V] [Module k V]
    (bI : Module.Basis I k V) (bJ : Module.Basis J k V)
    (L : V →ₗ[k] (O ⟶ B)) :
    (linearEquivIso O (bI.equivFun.symm.trans bJ.equivFun)).hom ≫
      Sigma.desc (fun j => L (bJ j)) = Sigma.desc (fun i => L (bI i)) := by
  apply evaluation_triangle O B
  intro i
  have hsingle : bI.equivFun.symm (Pi.single i 1) = bI i := by
    apply bI.equivFun.injective
    simp only [LinearEquiv.apply_symm_apply]
    ext j
    simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  change L (bI i) = ∑ j, bJ.equivFun (bI.equivFun.symm (Pi.single i 1)) j • L (bJ j)
  rw [hsingle]
  simpa only [map_sum, map_smul] using congrArg L (bJ.sum_equivFun (bI i)).symm

/-- The triangle can be stated using the actual evaluation maps, without
requiring their definitions to be coproduct descents. -/
theorem evaluation_triangle_of_generators (e : (I → k) ≃ₗ[k] (J → k))
    (p : (∐ fun _ : I => O) ⟶ B) (q : (∐ fun _ : J => O) ⟶ B)
    (h : ∀ i, Sigma.ι (fun _ : I => O) i ≫ p =
      ∑ j, e (Pi.single i 1) j • (Sigma.ι (fun _ : J => O) j ≫ q)) :
    (linearEquivIso O e).hom ≫ q = p := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, linearEquivIso_generator, Preadditive.sum_comp]
  simpa only [Linear.smul_comp] using (h i).symm

/-- The original two evaluation maps are intertwined by their actual
basis change as soon as their genuine generators are the given sections. -/
theorem basis_evaluation_triangle_of_generators
    {V : Type x} [AddCommGroup V] [Module k V]
    (bI : Module.Basis I k V) (bJ : Module.Basis J k V)
    (L : V →ₗ[k] (O ⟶ B))
    (p : (∐ fun _ : I => O) ⟶ B) (q : (∐ fun _ : J => O) ⟶ B)
    (hp : ∀ i, Sigma.ι (fun _ : I => O) i ≫ p = L (bI i))
    (hq : ∀ j, Sigma.ι (fun _ : J => O) j ≫ q = L (bJ j)) :
    (linearEquivIso O (bI.equivFun.symm.trans bJ.equivFun)).hom ≫ q = p := by
  have ep : p = Sigma.desc (fun i => L (bI i)) := by
    apply Sigma.hom_ext
    intro i
    simpa only [Sigma.ι_comp_desc] using hp i
  have eq : q = Sigma.desc (fun j => L (bJ j)) := by
    apply Sigma.hom_ext
    intro j
    simpa only [Sigma.ι_comp_desc] using hq j
  rw [ep, eq]
  exact basis_evaluation_triangle O B bI bJ L

end M9Native.FiniteCopowerBasisChange
