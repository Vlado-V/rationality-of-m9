module

public import M9StacksIntegration.FrameHomRawFiniteOddDescent

/-! Rationality of the literal full fixed field of the original raw Hom field.
The field is the intersection of the actual finite-frame invariants and
the actual odd-involution fixed subfield. Genuine finite descent and its
proved odd intertwining identify it with the original descended isomorphism
fixed field. This endpoint does not identify that field with M9. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
namespace M9Native.FrameHomRawInvariantRationality
open M9.FrameBundleDescent (Ambient Even ConnectedField)
open M9.FrameBundleDescent.Standard (representation IsomField IsomFixedField)
open M9.FrameHomFieldDescent
open FrameHomRawOddCoordinates FrameHomRawFiniteOddDescent

def fullFixedField : IntermediateField ℂ RawField where
  __ := RawFixedField ⊓ M9.SemilinearInvolution.fixedField rawInversion
  algebraMap_mem' c := by
    refine ⟨?_, rawInversion_complex_constant c⟩
    have hc : ((algebraMap ℂ RawFixedField c : RawFixedField) : RawField) =
        algebraMap ℂ RawField c :=
      (rawFixedComplexAlgebra_coe c).trans
        (IsScalarTower.algebraMap_apply ℂ Ambient RawField c).symm
    rw [← hc]
    exact (algebraMap ℂ RawFixedField c).property

theorem mem_fullFixedField (z : RawField) :
    z ∈ fullFixedField ↔
      (∀ g : Even, rawFieldAction.smul g z = z) ∧ rawInversion z = z := Iff.rfl

def evenInclusion : fullFixedField →ₐ[ℂ] RawFixedField where
  toFun z := ⟨z.val, z.property.1⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  commutes' c := by
    apply Subtype.ext
    exact (IsScalarTower.algebraMap_apply ℂ Ambient RawField c).trans
      (rawFixedComplexAlgebra_coe c).symm

theorem evenInclusion_coe (z : fullFixedField) :
    ((evenInclusion z : RawFixedField) : RawField) = (z : RawField) := rfl

theorem evenInclusion_fixedInversion (z : fullFixedField) :
    fixedInversion (evenInclusion z) = evenInclusion z := by
  apply Subtype.ext
  exact (inclusion_intertwines (evenInclusion z)).symm.trans z.property.2

def toIsomField : fullFixedField →ₐ[ℂ] IsomField :=
  fixedFieldComplexEquiv.toAlgHom.comp evenInclusion

def isomFixedEquiv : fullFixedField ≃ₐ[ℂ] IsomFixedField where
  toFun z := ⟨toIsomField z, by
    change M9.FrameBundleDescent.isomInversion representation
      (fixedFieldEquiv (evenInclusion z)) = fixedFieldEquiv (evenInclusion z)
    exact (fixedFieldEquiv_fixedInversion (evenInclusion z)).symm.trans
      (congrArg fixedFieldEquiv (evenInclusion_fixedInversion z))⟩
  invFun y :=
    let z : RawFixedField := fixedFieldComplexEquiv.symm y.val
    ⟨z.val, z.property, by
      have hz : fixedInversion z = z := by
        apply fixedFieldEquiv.injective
        rw [fixedFieldEquiv_fixedInversion]
        change M9.FrameBundleDescent.isomInversion representation
          (fixedFieldComplexEquiv (fixedFieldComplexEquiv.symm y.val)) =
            fixedFieldComplexEquiv (fixedFieldComplexEquiv.symm y.val)
        rw [AlgEquiv.apply_symm_apply]
        exact y.property
      exact (inclusion_intertwines z).trans (congrArg Subtype.val hz)⟩
  left_inv z := by
    apply Subtype.ext
    change ((fixedFieldComplexEquiv.symm (fixedFieldComplexEquiv (evenInclusion z)) :
      RawFixedField) : RawField) = (z : RawField)
    exact congrArg (fun x : RawFixedField => (x : RawField))
      (fixedFieldComplexEquiv.symm_apply_apply (evenInclusion z))
  right_inv y := Subtype.ext (fixedFieldComplexEquiv.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (toIsomField.map_add' x y)
  map_mul' x y := Subtype.ext (toIsomField.map_mul' x y)
  commutes' c := by
    apply Subtype.ext
    exact toIsomField.commutes c

theorem isomFixedEquiv_coe (z : fullFixedField) :
    ((isomFixedEquiv z : IsomFixedField) : IsomField) =
      fixedFieldComplexEquiv (evenInclusion z) := rfl

theorem isomFixedEquiv_coefficient (c : ℂ) :
    isomFixedEquiv (algebraMap ℂ fullFixedField c) =
      algebraMap ℂ IsomFixedField c :=
  isomFixedEquiv.commutes c

def rationalEquiv : fullFixedField ≃ₐ[ℂ] M9.RationalField ℂ 24 :=
  isomFixedEquiv.trans M9.FrameBundleDescent.Standard.isomFixedFieldRationalEquiv

theorem rationalEquiv_coefficient (c : ℂ) :
    rationalEquiv (algebraMap ℂ fullFixedField c) =
      algebraMap ℂ (M9.RationalField ℂ 24) c :=
  rationalEquiv.commutes c

theorem fullFixedField_rational :
    Nonempty (fullFixedField ≃ₐ[ℂ] M9.RationalField ℂ 24) := ⟨rationalEquiv⟩

end M9Native.FrameHomRawInvariantRationality
end
