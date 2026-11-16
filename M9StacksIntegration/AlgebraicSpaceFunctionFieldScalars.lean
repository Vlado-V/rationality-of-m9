module

public import StacksFrontier.AlgebraicGeometry.Spaces.FunctionField

/-!
Structural scalars on the native function field of an actual integral algebraic
space over a field. The coefficient map comes from the actual generic point's
morphism to the original field spectrum. The native rational-function ring and
native generic residue field are retained. Integrality is a genuine hypothesis
on that algebraic space; no moduli-space integrality or rationality is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace M9Native.AlgebraicSpaceFunctionFieldScalars

universe u

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))
variable {X : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B (Spec (.of K)) hK X)
  (hInt : Space.IsIntegralSpace B (Spec (.of K)) hK X)

/-- The actual native residue field at the actual native generic point. -/
abbrev genericResidueField :=
  Space.residueField B (Spec (.of K)) hK X hInt.2.1
    (Space.genericPoint B (Spec (.of K)) hK hX hInt)

/-- Its actual original structural morphism to the given field base. -/
abbrev genericStructureMap :
    Spec (.of (genericResidueField K B hK hX hInt)) ⟶ Spec (.of K) :=
  (Space.genericRep B (Spec (.of K)) hK hX hInt).toBase

/-- Read the actual generic structural morphism through the fully faithful Spec. -/
def genericResidueFieldBaseMap : K →+* genericResidueField K B hK hX hInt :=
  ((Spec.fullyFaithful.preimage (genericStructureMap K B hK hX hInt)).unop).hom

@[simp]
theorem spec_map_genericResidueFieldBaseMap :
    Spec.map (CommRingCat.ofHom (genericResidueFieldBaseMap K B hK hX hInt)) =
      genericStructureMap K B hK hX hInt :=
  Spec.map_preimage_unop _

/-- The coefficient structure on the native generic residue field. -/
@[instance_reducible]
def genericResidueFieldBaseAlgebra :
    Algebra K (genericResidueField K B hK hX hInt) :=
  (genericResidueFieldBaseMap K B hK hX hInt).toAlgebra

/-- The coefficient map on the existing native rational-function ring. -/
def rationalFunctionsBaseMap : K →+* Space.rationalFunctions B (Spec (.of K)) hK hX :=
  (Space.rationalFunctionsRingEquiv B (Spec (.of K)) hK hX hInt).symm.toRingHom.comp
    (genericResidueFieldBaseMap K B hK hX hInt)

/-- This is the algebra structure from the original generic structural morphism. -/
@[instance_reducible]
def rationalFunctionsBaseAlgebra :
    Algebra K (Space.rationalFunctions B (Spec (.of K)) hK hX) :=
  (rationalFunctionsBaseMap K B hK hX hInt).toAlgebra

@[simp]
theorem rationalFunctionsRingEquiv_baseMap (c : K) :
    Space.rationalFunctionsRingEquiv B (Spec (.of K)) hK hX hInt
        (rationalFunctionsBaseMap K B hK hX hInt c) =
      genericResidueFieldBaseMap K B hK hX hInt c := by
  simp [rationalFunctionsBaseMap]

/-- The original native generic comparison respects the actual structural scalars. -/
def rationalFunctionsGenericAlgEquiv :
    letI := rationalFunctionsBaseAlgebra K B hK hX hInt
    letI := genericResidueFieldBaseAlgebra K B hK hX hInt
    Space.rationalFunctions B (Spec (.of K)) hK hX ≃ₐ[K]
      genericResidueField K B hK hX hInt := by
  letI := rationalFunctionsBaseAlgebra K B hK hX hInt
  letI := genericResidueFieldBaseAlgebra K B hK hX hInt
  exact { __ := Space.rationalFunctionsRingEquiv B (Spec (.of K)) hK hX hInt
          commutes' := rationalFunctionsRingEquiv_baseMap K B hK hX hInt }

@[simp]
theorem rationalFunctionsGenericAlgEquiv_toRingEquiv :
    letI := rationalFunctionsBaseAlgebra K B hK hX hInt
    letI := genericResidueFieldBaseAlgebra K B hK hX hInt
    (rationalFunctionsGenericAlgEquiv K B hK hX hInt).toRingEquiv =
      Space.rationalFunctionsRingEquiv B (Spec (.of K)) hK hX hInt := rfl

/-- Adding the actual field structure does not change the rational-function ring. -/
theorem functionField_toCommRing :
    (Space.functionField B (Spec (.of K)) hK hX hInt).toCommRing =
      (inferInstance : CommRing (Space.rationalFunctions B (Spec (.of K)) hK hX)) :=
  Space.functionField_toCommRing B (Spec (.of K)) hK hX hInt

/-- The original field of coefficients embeds in the actual function field. -/
theorem rationalFunctionsBaseMap_injective :
    Function.Injective (rationalFunctionsBaseMap K B hK hX hInt) := by
  let _ := Space.functionField B (Spec (.of K)) hK hX hInt
  exact (rationalFunctionsBaseMap K B hK hX hInt).injective

/-- Native dense-open lifting at the actual generic point, for every
representative. This existence is derived, not an extra denominator premise. -/
def genericRepresentativeLift
    (f : Space.PartialMap B (Spec (.of K)) hK hX
      (Space.affineLineFunctor B (Spec (.of K)) hK)) :
    {j : yoneda.obj ((Space.genericRep B (Spec (.of K)) hK hX hInt).siteObject
        B (Spec (.of K)) hK X) ⟶ f.domain.toFunctor //
      j ≫ f.domain.ι = Space.fieldMorphism B (Spec (.of K)) hK X
        (Space.genericRep B (Spec (.of K)) hK hX hInt)} :=
  Space.genericLiftData B (Spec (.of K)) hK hX hInt
    (Space.genericRep B (Spec (.of K)) hK hX hInt)
    (Space.genericRep_class B (Spec (.of K)) hK hX hInt) f.dense_open_domain

section FieldMorphism

variable (F : Type u) [Field F] [Algebra K F]
  (q : Spec (.of F) ⟶ Spec (.of (genericResidueField K B hK hX hInt)))
  (hq : q ≫ genericStructureMap K B hK hX hInt = Spec.algebraMap K F)

include hq

/-- An actual morphism of these field spectra over the original base preserves
its structural coefficients; no scalar-equality hypothesis is supplied. -/
theorem genericMorphism_baseMap (c : K) :
    (Spec.preimage q).hom (genericResidueFieldBaseMap K B hK hX hInt c) =
      algebraMap K F c := by
  have h : CommRingCat.ofHom (genericResidueFieldBaseMap K B hK hX hInt) ≫
      Spec.preimage q = CommRingCat.ofHom (algebraMap K F) :=
    Spec.map_injective (by
      rw [Spec.map_comp, Spec.map_preimage, spec_map_genericResidueFieldBaseMap]
      exact hq)
  exact congrArg (fun a : CommRingCat.of K ⟶ CommRingCat.of F => a.hom c) h

/-- Native evaluation via the actual generic field morphism is K-algebraic. -/
def genericEvaluationAlgHom :
    letI := rationalFunctionsBaseAlgebra K B hK hX hInt
    Space.rationalFunctions B (Spec (.of K)) hK hX →ₐ[K] F := by
  letI := rationalFunctionsBaseAlgebra K B hK hX hInt
  refine
    { __ := (Spec.preimage q).hom.comp
        (Space.rationalFunctionsRingEquiv B (Spec (.of K)) hK hX hInt).toRingHom
      commutes' := ?_ }
  intro c
  change (Spec.preimage q).hom
    (Space.rationalFunctionsRingEquiv B (Spec (.of K)) hK hX hInt
      (rationalFunctionsBaseMap K B hK hX hInt c)) = algebraMap K F c
  rw [rationalFunctionsRingEquiv_baseMap]
  exact genericMorphism_baseMap K B hK hX hInt F q hq c

@[simp]
theorem genericEvaluationAlgHom_apply (f : Space.rationalFunctions B (Spec (.of K)) hK hX) :
    letI := rationalFunctionsBaseAlgebra K B hK hX hInt
    genericEvaluationAlgHom K B hK hX hInt F q hq f =
      (Spec.preimage q).hom
        (Space.rationalFunctionsRingEquiv B (Spec (.of K)) hK hX hInt f) := rfl

/-- The algebraic evaluation is computed on an actual dense-open representative
by the original native coordinate formula. -/
theorem genericEvaluationAlgHom_toRationalMap
    (f : Space.PartialMap B (Spec (.of K)) hK hX
      (Space.affineLineFunctor B (Spec (.of K)) hK))
    (j : yoneda.obj ((Space.genericRep B (Spec (.of K)) hK hX hInt).siteObject
        B (Spec (.of K)) hK X) ⟶ f.domain.toFunctor)
    (hj : j ≫ f.domain.ι = Space.fieldMorphism B (Spec (.of K)) hK X
      (Space.genericRep B (Spec (.of K)) hK hX hInt)) :
    letI := rationalFunctionsBaseAlgebra K B hK hX hInt
    genericEvaluationAlgHom K B hK hX hInt F q hq (f.toRationalMap B (Spec (.of K)) hK) =
      (Spec.preimage q).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (genericResidueField K B hK hX hInt))).hom.hom
          (Space.affineLineCoordinate B (Spec (.of K)) hK
            (Opposite.op ((Space.genericRep B (Spec (.of K)) hK hX hInt).siteObject
              B (Spec (.of K)) hK X)) (yonedaEquiv (j ≫ f.hom)))) := by
  let _ := rationalFunctionsBaseAlgebra K B hK hX hInt
  rw [genericEvaluationAlgHom_apply,
    Space.rationalFunctionsRingEquiv_toRationalMap B (Spec (.of K)) hK hX hInt f j hj]

/-- Evaluation on every original dense-open representative with its actual
native generic lift. No lift or denominator-nonvanishing input is required. -/
theorem genericEvaluationAlgHom_chosenRepresentative
    (f : Space.PartialMap B (Spec (.of K)) hK hX
      (Space.affineLineFunctor B (Spec (.of K)) hK)) :
    letI := rationalFunctionsBaseAlgebra K B hK hX hInt
    genericEvaluationAlgHom K B hK hX hInt F q hq (f.toRationalMap B (Spec (.of K)) hK) =
      (Spec.preimage q).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (genericResidueField K B hK hX hInt))).hom.hom
          (Space.affineLineCoordinate B (Spec (.of K)) hK
            (Opposite.op ((Space.genericRep B (Spec (.of K)) hK hX hInt).siteObject
              B (Spec (.of K)) hK X))
            (yonedaEquiv ((genericRepresentativeLift K B hK hX hInt f).val ≫ f.hom)))) :=
  genericEvaluationAlgHom_toRationalMap K B hK hX hInt F q hq f
    (genericRepresentativeLift K B hK hX hInt f).val
    (genericRepresentativeLift K B hK hX hInt f).property

end FieldMorphism

end M9Native.AlgebraicSpaceFunctionFieldScalars
