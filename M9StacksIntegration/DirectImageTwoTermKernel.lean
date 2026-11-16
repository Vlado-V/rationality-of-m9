module

public import M9StacksIntegration.DirectImageTwoTerm
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Actual degree-zero homology is the kernel of the actual differential

This proves the kernel comparison from the homology exact sequence of
the actual distinguished triangle. It does not posit a module/kernel
comparison or replace it by an equality of dimensions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace M9Native.DirectImageTwoTermKernel

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- A distinguished triangle with its last two terms in degree zero
identifies the actual degree-zero homology with the actual kernel. -/
theorem nonempty_homologyZeroIsoKernel
    {K : DerivedCategory A} {E F : A}
    (a : K ⟶ (DerivedCategory.singleFunctor A 0).obj E) (d : E ⟶ F)
    (b : (DerivedCategory.singleFunctor A 0).obj F ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a ((DerivedCategory.singleFunctor A 0).map d) b ∈
      distTriang (DerivedCategory A)) :
    Nonempty ((DerivedCategory.homologyFunctor A 0).obj K ≅ kernel d) := by
  let T := Triangle.mk a ((DerivedCategory.singleFunctor A 0).map d) b
  have hTT : T ∈ distTriang (DerivedCategory A) := hT
  let H := DerivedCategory.homologyFunctor A 0
  let eE := (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app E
  let eF := (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app F
  have hm : IsZero ((DerivedCategory.homologyFunctor A (-1)).obj T.obj₃) := by
    exact AlgebraicGeometry.Scheme.Modules.isZero_homologyFunctor_singleFunctor_obj F (by norm_num)
  haveI : Mono (H.map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T hTT (-1) 0 (by norm_num)).2 (hm.eq_of_src _ _)
  let C₀ := ShortComplex.mk (H.map T.mor₁) (H.map T.mor₂)
    (by simp only [← Functor.map_comp,comp_distTriang_mor_zero₁₂ _ hTT,Functor.map_zero])
  have hC₀ : C₀.Exact := DerivedCategory.HomologySequence.exact₂ T hTT 0
  have hn : H.map ((DerivedCategory.singleFunctor A 0).map d) ≫ eF.hom = eE.hom ≫ d :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).hom.naturality d
  let f := H.map a ≫ eE.hom
  have w : f ≫ d = 0 := by
    dsimp only [f]
    rw [Category.assoc,← hn,← Category.assoc,← Functor.map_comp]
    have hz : a ≫ (DerivedCategory.singleFunctor A 0).map d = 0 :=
      comp_distTriang_mor_zero₁₂ _ hT
    rw [hz,Functor.map_zero,zero_comp]
  let C₁ := ShortComplex.mk f d w
  let e : C₀ ≅ C₁ := ShortComplex.isoMk (Iso.refl _) eE eF
    (by simp [C₀,C₁,f,T]) (by simpa [C₀,C₁,T] using hn.symm)
  have hC₁ : C₁.Exact := ShortComplex.exact_of_iso e hC₀
  haveI : Mono (H.map a) := by change Mono (H.map T.mor₁); infer_instance
  haveI : Mono C₁.f := by dsimp only [C₁,f]; infer_instance
  let eK := hC₁.fIsKernel.conePointUniqueUpToIso (kernelIsKernel d)
  exact ⟨eK⟩

end M9Native.DirectImageTwoTermKernel
