module

public import M9StacksIntegration.PrimitiveGeometricQuotientField
public import Mathlib.Algebra.Field.ULift

@[expose] public section

/-! Canonical coefficient relabeling of the actual structural generic
stalk. The complex specialization stays in Type 0 and retains the same
scheme, original structure map and quotient map. It does not enlarge the
universe of test schemes or prove the universe-polymorphic standalone goal. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite

namespace M9Native.FunctionFieldCoefficientRelabeling

universe u

variable {K L : Type u} [Field K] [Field L]

/-- The genuine spectrum isomorphism induced by the given coefficient
ring isomorphism, within one fixed scheme universe. -/
def baseIso (e : K ≃+* L) : Spec (.of L) ≅ Spec (.of K) :=
  Scheme.Spec.mapIso e.toCommRingCatIso.op

/-- Structural coefficients commute with the actual change of ground
field. This is derived from the structure map and its generic germ. -/
theorem structureScalarMap_comp (e : K ≃+* L)
    {Y : Scheme.{u}} [IrreducibleSpace Y] (p : Y ⟶ Spec (.of L)) :
    GrassmannianCharts.structureScalarMap K (p ≫ (baseIso e).hom) =
      (GrassmannianCharts.structureScalarMap L p).comp e.toRingHom := by
  have hc : (Scheme.ΓSpecIso (.of K)).inv ≫ (p ≫ (baseIso e).hom).appTop =
      e.toCommRingCatIso.hom ≫ (Scheme.ΓSpecIso (.of L)).inv ≫ p.appTop := by
    change (Scheme.ΓSpecIso (.of K)).inv ≫
      (p ≫ Spec.map e.toCommRingCatIso.hom).appTop = _
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
    rw [Category.assoc]
  change (((Scheme.ΓSpecIso (.of K)).inv ≫ (p ≫ (baseIso e).hom).appTop) ≫
    Y.presheaf.germ ⊤ (genericPoint Y) (by trivial)).hom = _
  rw [hc]
  rfl

/-- Canonical coefficient relabeling of rational functions, constructed
from the polynomial coefficient map and localization. -/
def rationalRingEquiv (e : K ≃+* L) (n : ℕ) :
    M9.RationalField K n ≃+* M9.RationalField L n :=
  IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.mapEquiv (Fin n) e)

theorem rationalRingEquiv_scalar (e : K ≃+* L) (n : ℕ) (c : K) :
    rationalRingEquiv e n (algebraMap K (M9.RationalField K n) c) =
      algebraMap L (M9.RationalField L n) (e c) := by
  change rationalRingEquiv e n
      (algebraMap (MvPolynomial (Fin n) K) (M9.RationalField K n) (MvPolynomial.C c)) =
    algebraMap (MvPolynomial (Fin n) L) (M9.RationalField L n) (MvPolynomial.C (e c))
  rw [rationalRingEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp

/-- Relabel an equivalence of the same genuine generic-stalk carrier,
using its actual structural scalar map over the relabeled base. The
complex client below obtains the input from the proved geometry criterion. -/
def relabel (e : K ≃+* L) (n : ℕ)
    {Y : Scheme.{u}} [IsIntegral Y] (p : Y ⟶ Spec (.of L))
    (eK : letI := (GrassmannianCharts.structureScalarMap K (p ≫ (baseIso e).hom)).toAlgebra
      Y.functionField ≃ₐ[K] M9.RationalField K n) :
    letI := (GrassmannianCharts.structureScalarMap L p).toAlgebra
    Y.functionField ≃ₐ[L] M9.RationalField L n := by
  letI := (GrassmannianCharts.structureScalarMap K (p ≫ (baseIso e).hom)).toAlgebra
  let er : Y.functionField ≃+* M9.RationalField L n :=
    eK.toRingEquiv.trans (rationalRingEquiv e n)
  letI := (GrassmannianCharts.structureScalarMap L p).toAlgebra
  refine { __ := er, commutes' := fun c => ?_ }
  have hc : GrassmannianCharts.structureScalarMap L p c =
      GrassmannianCharts.structureScalarMap K (p ≫ (baseIso e).hom) (e.symm c) := by
    rw [structureScalarMap_comp]
    simp
  change rationalRingEquiv e n (eK (GrassmannianCharts.structureScalarMap L p c)) = _
  rw [hc]
  change rationalRingEquiv e n (eK (algebraMap K Y.functionField (e.symm c))) = _
  rw [eK.commutes, rationalRingEquiv_scalar, e.apply_symm_apply]

/-- Rebase an already constructed structural equivalence along the inverse
base isomorphism. Equality transport is performed while the equivalence
is an abstract argument, so its mathematical construction stays opaque to
this instance-transport step without any compiler-budget increase. -/
def relabelOriginal (e : K ≃+* L) (n : ℕ)
    {Y : Scheme.{u}} [IsIntegral Y] (p : Y ⟶ Spec (.of K))
    (eK : letI := (GrassmannianCharts.structureScalarMap K p).toAlgebra
      Y.functionField ≃ₐ[K] M9.RationalField K n) :
    letI := (GrassmannianCharts.structureScalarMap L (p ≫ (baseIso e).inv)).toAlgebra
    Y.functionField ≃ₐ[L] M9.RationalField L n := by
  have hp : (p ≫ (baseIso e).inv) ≫ (baseIso e).hom = p := by
    simp [Category.assoc]
  exact relabel e n (p ≫ (baseIso e).inv)
    (Eq.mpr (congrArg (fun r : Y ⟶ Spec (.of K) =>
      letI := (GrassmannianCharts.structureScalarMap K r).toAlgebra
      Y.functionField ≃ₐ[K] M9.RationalField K n) hp) eK)

end M9Native.FunctionFieldCoefficientRelabeling

namespace M9Native.ComplexULiftFunctionField

/-- Only a Type-0 coefficient relabeling is asserted by this adapter. -/
abbrev Coeff : Type := ULift.{0} ℂ

def canonicalSpecIso : Spec (.of Coeff) ≅ Spec (.of ℂ) :=
  FunctionFieldCoefficientRelabeling.baseIso (ULift.ringEquiv.symm : ℂ ≃+* Coeff)

/-- The same underlying scheme gets its canonical lifted coefficient map
from the original complex structure map. -/
def liftedStructure {Y : Scheme} (p : Y ⟶ Spec (.of ℂ)) : Y ⟶ Spec (.of Coeff) :=
  p ≫ canonicalSpecIso.inv

theorem liftedStructure_comp {Y : Scheme} (p : Y ⟶ Spec (.of ℂ)) :
    liftedStructure p ≫ canonicalSpecIso.hom = p := by
  simp [liftedStructure, Category.assoc]

/-- The frozen original-complex geometry criterion supplies rationality of
the actual generic stalk with its canonically lifted structural algebra.
No field equivalence or rationality premise is supplied, and the scheme
and actual quotient map are unchanged. -/
def rationalEquiv
    (U : PrimitiveGrassmannianAction.space.Opens) [Nonempty U]
    {Y : Scheme} [IsIntegral Y] (p : Y ⟶ PrimitiveFamilyFreeAction.base)
    (q : U.toScheme ⟶ Y) [IsDominant q]
    (h : PrimitiveGeometricQuotientField.Geometry U p q) :
    letI := (GrassmannianCharts.structureScalarMap Coeff (liftedStructure p)).toAlgebra
    Y.functionField ≃ₐ[Coeff] M9.RationalField Coeff 24 :=
  FunctionFieldCoefficientRelabeling.relabelOriginal (K := ℂ) (L := Coeff)
    (ULift.ringEquiv.symm : ℂ ≃+* Coeff) 24 p
    (PrimitiveGeometricQuotientField.rationalEquiv U p q h)

end M9Native.ComplexULiftFunctionField
