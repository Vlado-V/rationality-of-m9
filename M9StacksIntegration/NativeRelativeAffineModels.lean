module

public import StacksFrontier.AlgebraicGeometry.Limits.AdjoinFinsetSystem
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Actual relative affine finite-type models in EVERY base-containing site

For any K-algebra A, the spectra of the finitely generated K-subalgebras
K[s] belong to every native site containing Spec K. Their original relative
maps and their actual cofiltered limit are retained, with NO assumption that
A, or Spec A, belongs to that site. In an enlarged site containing Spec A,
the same actual relative diagram and its actual cone are native affine
objects and the underlying original cone is genuinely limiting.

This uses relative finite type over K, never absolute finite type over Z.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.NativeRelativeAffineModels
universe u
variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]
  (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))

include hK in
/-- Every relative finite-type affine stage is genuinely in the site,
independently of the size of the full original K-algebra A. -/
theorem contains_stage (s : Finset A) :
    B.Contains ((AdjoinFinset.specDiagram K A).obj (op s)) := by
  let : Algebra.FiniteType K (Algebra.adjoin K (s : Set A)) :=
    Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit K (Algebra.adjoin K (s : Set A)) hK

/-- Each actual stage map is locally of finite type over the ORIGINAL K. -/
theorem stage_locallyOfFiniteType (s : Finset A) :
    LocallyOfFiniteType ((AdjoinFinset.specToBase K A).app (op s)) := by
  let : Algebra.FiniteType K (Algebra.adjoin K (s : Set A)) :=
    Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- The SAME relative finite-type affine stages, as actual native objects. -/
def diagram : (Finset A)ᵒᵖ ⥤ BigAffineFppf B (Spec (.of K)) hK where
  obj i := ⟨siteObject B (Spec (.of K)) hK (contains_stage K A B hK i.unop)
    ((AdjoinFinset.specToBase K A).app i), by
      change IsAffine (Spec (.of (Algebra.adjoin K (i.unop : Set A))))
      infer_instance⟩
  map f := ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk ((AdjoinFinset.specDiagram K A).map f))
    (ObjectProperty.hom_ext _ (by
      change (AdjoinFinset.specDiagram K A).map f ≫
        (AdjoinFinset.specToBase K A).app _ = (AdjoinFinset.specToBase K A).app _
      exact ((AdjoinFinset.specToBase K A).naturality f).trans (Category.comp_id _))))
  map_id i := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (AdjoinFinset.specDiagram K A).map_id i
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (AdjoinFinset.specDiagram K A).map_comp f g

/-- The original underlying diagram is literally the K-subalgebra diagram. -/
theorem diagram_toScheme :
    diagram K A B hK ⋙ BigAffineFppf.toScheme B (Spec (.of K)) hK =
      AdjoinFinset.specDiagram K A := rfl

/-- In any enlarged site containing Spec A, the actual original affine
limit cone is a cone of actual native relative affine objects. -/
def cone (hA : B.Contains (Spec (.of A))) : Cone (diagram K A B hK) where
  pt := ⟨siteObject B (Spec (.of K)) hK hA
    (Spec.map (CommRingCat.ofHom (algebraMap K A))), by
      change IsAffine (Spec (.of A))
      infer_instance⟩
  π :=
    { app := fun i => ObjectProperty.homMk (Over.homMk
        (ObjectProperty.homMk ((AdjoinFinset.specCone K A).π.app i))
        (ObjectProperty.hom_ext _ (AdjoinFinset.specCone_π_comp K A i)))
      naturality := by
        intro i j f
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        change (𝟙 (Spec (.of A))) ≫ (AdjoinFinset.specCone K A).π.app j =
          (AdjoinFinset.specCone K A).π.app i ≫ (AdjoinFinset.specDiagram K A).map f
        exact (Category.id_comp _).trans ((AdjoinFinset.specCone K A).w f).symm }

/-- The actual cone remains a true limit on the underlying ORIGINAL schemes. -/
def isLimit_toScheme_cone (hA : B.Contains (Spec (.of A))) :
    IsLimit ((BigAffineFppf.toScheme B (Spec (.of K)) hK).mapCone
      (cone K A B hK hA)) :=
  AdjoinFinset.isLimitSpecCone K A

end M9StacksIntegration.NativeRelativeAffineModels
