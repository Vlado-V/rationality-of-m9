module

public import M9StacksIntegration.LagrangianPluckerGeneration
public import M9StacksIntegration.LagrangianProjectiveSections
public import M9StacksIntegration.NativeProjectiveVector

/-! The original primitive Plucker morphism in the native polynomial
projective model, with its actual determinant-frame coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

universe u

namespace M9Native.LagrangianPolynomialPluckerFrame

open Stacks.AlgebraicGeometry.ProjBaseChange Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.ProjectiveSpaceChartRatio

/-- The native function-tuple morphism and the original section morphism
agree through the proved coefficient-base-change comparison. -/
theorem sectionPolynomialMap {K : Type u} [CommRing K] {T : Scheme.{u}} {n : ℕ}
    (f : T ⟶ Spec (.of K)) (v : Fin (n+1) → Γ(T,⊤))
    (hv : Ideal.span (Set.range v) = ⊤) :
    Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver v hv f ≫
        (polynomialComparison K n).iso.hom =
      NativeProjectiveVector.onScheme T (baseRingHom f) v hv := by
  have h : NativeProjectiveVector.onScheme T (baseRingHom f) v hv ≫
      (polynomialComparison K n).iso.inv =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver v hv f :=
    LagrangianProjectiveSections.fromEvaluation_comp_comparison_inv f v hv
  calc
    _ = (NativeProjectiveVector.onScheme T (baseRingHom f) v hv ≫
        (polynomialComparison K n).iso.inv) ≫ (polynomialComparison K n).iso.hom :=
      congrArg (fun a => a ≫ (polynomialComparison K n).iso.hom) h.symm
    _ = _ := by rw [Category.assoc,Iso.inv_hom_id,Category.comp_id]

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianDeterminantSections
open LagrangianPluckerGeneration LagrangianSectionGeneration LagrangianPluckerEpimorphism
open ProjectiveSectionFunctions Stacks.ProjectiveFromSections

variable (K : Type u) [Field K] [CharZero K]

/-- The actual original LG embedding, transported to polynomial P13. -/
def polynomialPlucker : space K ⟶ Proj (polyGrading K 13) :=
  LagrangianPlucker.primitivePlucker K ≫ (polynomialComparison K 13).iso.hom

omit [CharZero K] in
/-- The field coefficients are exactly the original structure-morphism
coefficients, including on nonreduced test schemes. -/
theorem coefficientMap_eq_baseRingHom {T : Scheme.{u}} (f : T ⟶ space K) :
    LagrangianPlucker.coefficientMap K f = baseRingHom (f ≫ projection K) := rfl

/-- Generation in a genuine determinant frame is derived from the actual
universal generating tuple and the actual line isomorphism. -/
theorem frameTuple_generates {T : Scheme.{u}} (f : T ⟶ space K)
    (e : (Scheme.Modules.pullback f).obj (determinantLine K) ≅ UnitLine T)
    (v : Fin 14 → Γ(T,⊤))
    (he : ∀ j, e.hom.app ⊤
      (pullbackGlobalSections f (determinantLine K) (primitiveSections K j)) = v j) :
    GeneratesStalks (show Fin 14 → Γ(UnitLine T,⊤) from v) := by
  let sf := fun j => pullbackGlobalSections f (determinantLine K) (primitiveSections K j)
  let := sectionMap_epi_of_generatesStalks sf (pulledPrimitiveSections_generatesStalks K f)
  have hep : Epi (sectionMap T ((Scheme.Modules.pullback f).obj (determinantLine K)) sf ≫
      e.hom) := inferInstance
  have hmap : sectionMap T ((Scheme.Modules.pullback f).obj (determinantLine K)) sf ≫
      e.hom = sectionMap T (UnitLine T) (show Fin 14 → Γ(UnitLine T,⊤) from v) :=
    (sectionMap_postcomp T sf e.hom).trans
      (congrArg (sectionMap T (UnitLine T)) (funext he))
  exact generatesStalks_of_sectionMap_epi T _ _ (hmap ▸ hep)

/-- Every actual determinant frame computes the original polynomial
Plucker map by the original fourteen section values. No projective-map
identity is supplied as a premise. -/
theorem comp_polynomialPlucker_in_frame {T : Scheme.{u}} (f : T ⟶ space K)
    (e : (Scheme.Modules.pullback f).obj (determinantLine K) ≅ UnitLine T)
    (v : Fin 14 → Γ(T,⊤)) (hv : Ideal.span (Set.range v) = ⊤)
    (he : ∀ j, e.hom.app ⊤
      (pullbackGlobalSections f (determinantLine K) (primitiveSections K j)) = v j) :
    f ≫ polynomialPlucker K =
      NativeProjectiveVector.onScheme T (baseRingHom (f ≫ projection K)) v hv := by
  let : Stacks.Ample.IsInvertibleModule T (UnitLine T) := Stacks.Ample.isInvertibleModule_unit T
  let sf := fun j => pullbackGlobalSections f (determinantLine K) (primitiveSections K j)
  have hsf := pulledPrimitiveSections_generatesStalks K f
  have hvgen := frameTuple_generates K f e v he
  calc
    _ = (f ≫ LagrangianPlucker.primitivePlucker K) ≫
        (polynomialComparison K 13).iso.hom := (Category.assoc _ _ _).symm
    _ = toProjectiveSpaceOver sf hsf (f ≫ projection K) ≫
        (polynomialComparison K 13).iso.hom := by
      rw [primitivePlucker_eq_toProjectiveSpaceOver,
        comp_toProjectiveSpaceOver_sameBase (primitiveSections K)
          (primitiveSections_generatesStalks K) f (projection K) hsf]
    _ = toProjectiveSpaceOver (show Fin 14 → Γ(UnitLine T,⊤) from v) hvgen
        (f ≫ projection K) ≫ (polynomialComparison K 13).iso.hom :=
      congrArg (fun a => a ≫ (polynomialComparison K 13).iso.hom)
        (ProjectiveSectionIso.toProjectiveSpaceOver_iso sf
          (show Fin 14 → Γ(UnitLine T,⊤) from v) hsf hvgen e he (f ≫ projection K))
    _ = Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver v hv (f ≫ projection K) ≫
        (polynomialComparison K 13).iso.hom := by
      rw [ProjectiveSectionFunctions.toProjectiveSpaceOver_unit v hvgen hv]
    _ = _ := sectionPolynomialMap (f ≫ projection K) v hv

end M9Native.LagrangianPolynomialPluckerFrame
