module

public import M9StacksIntegration.SchematicGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilies

/-!
# Genuine reflection of native constant functions to the ORIGINAL scheme

The actual identity-chart ring equivalences and proved naturality identify
native global-functions pullback with the SAME scheme's actual appTop.
Bijectivity therefore reflects. Native universal-H0 then proves the actual
original field-constants isomorphism whenever its actual total is represented.
No H0, rank-H0, field-identification or scheme-constants premise is supplied.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Space

namespace M9StacksIntegration.AllTestSchematicGlobalFunctionsReflection
universe u
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Actual native global-function bijectivity reflects to the SAME
original scheme morphism, through the proved original chart naturality. -/
theorem bijective_appTop_of_native {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : Function.Bijective (globalFunctionsMap B S hS (schemeSpaceMap g))) :
    Function.Bijective ((BigFppfOver.toScheme B S hS).map g).appTop.hom := by
  let eU := globalFunctionsYonedaRingEquiv B S hS U
  let eV := globalFunctionsYonedaRingEquiv B S hS V
  let f := ((BigFppfOver.toScheme B S hS).map g).appTop.hom
  constructor
  · intro a b hab
    apply eV.symm.injective
    apply hg.1
    apply eU.injective
    have ha : eU (globalFunctionsMap B S hS (schemeSpaceMap g) (eV.symm a)) = f a :=
      (M9Native.SchematicGlobalFunctions.yoneda_naturality B S hS g (eV.symm a)).trans
        (congrArg f (eV.apply_symm_apply a))
    have hb : eU (globalFunctionsMap B S hS (schemeSpaceMap g) (eV.symm b)) = f b :=
      (M9Native.SchematicGlobalFunctions.yoneda_naturality B S hS g (eV.symm b)).trans
        (congrArg f (eV.apply_symm_apply b))
    exact ha.trans (hab.trans hb.symm)
  · intro a
    obtain ⟨b, hb⟩ := hg.2 (eU.symm a)
    refine ⟨eV b, ?_⟩
    calc
      f (eV b) = eU (globalFunctionsMap B S hS (schemeSpaceMap g) b) :=
        (M9Native.SchematicGlobalFunctions.yoneda_naturality B S hS g b).symm
      _ = eU (eU.symm a) := congrArg eU hb
      _ = a := eU.apply_symm_apply a

/-- Literal equivalence for the actual native and original pullback maps. -/
theorem bijective_appTop_iff_native {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    Function.Bijective ((BigFppfOver.toScheme B S hS).map g).appTop.hom ↔
      Function.Bijective (globalFunctionsMap B S hS (schemeSpaceMap g)) :=
  ⟨M9Native.SchematicGlobalFunctions.bijective_of_bijective_appTop B S hS g,
    bijective_appTop_of_native B S hS g⟩

/-- Native bijectivity gives the actual ORIGINAL field-constants map,
with the exact supplied original scheme map and coefficient field. -/
theorem isIso_constants_of_native_bijective {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (K : Type u) [Field K] (hV : (BigFppfOver.toScheme B S hS).obj V = Spec (.of K))
    (hg : Function.Bijective (globalFunctionsMap B S hS (schemeSpaceMap g))) :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
      ((BigFppfOver.toScheme B S hS).map g ≫ eqToHom hV).appTop) := by
  let : IsIso ((BigFppfOver.toScheme B S hS).map g).appTop := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_appTop_of_native B S hS g hg
  let : IsIso (eqToHom hV).appTop :=
    inferInstanceAs (IsIso (Scheme.Γ.map (eqToHom hV).op))
  rw [Scheme.Hom.comp_appTop]
  infer_instance

/-- Actual global-function pullback along an actual space isomorphism
is bijective. Literal six-line native CurvesSemistable proof, renamed. -/
theorem nativeGlobalFunctions_bijective_of_iso
    {S₀ : Scheme.{u}} {hS₀ : B.Contains S₀}
    {U V : AlgebraicSpaces B S₀ hS₀} (e : V ≅ U) :
    Function.Bijective (Space.globalFunctionsMap B S₀ hS₀ e.hom) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨Space.globalFunctionsMap B S₀ hS₀ e.inv, fun s => ?_, fun s => ?_⟩ <;>
  rw [← RingHom.comp_apply, ← Space.globalFunctionsMap_comp] <;>
  simp only [Iso.inv_hom_id, Iso.hom_inv_id, Space.globalFunctionsMap_id, RingHom.id_apply]

/-- Universal native H0 gives actual native global-function bijectivity.
The proof is extracted verbatim from pinned CurvesH01, with a new name and
only its already-ready genuine definition/geometry dependencies. -/
theorem nativeH0_bijective_globalFunctionsMap
    (hZ : B.Contains integerBase) {X : CurveFamily B hZ}
    (hX : HasUniversallyBijectiveGlobalFunctions B hZ X) :
    Function.Bijective (Space.globalFunctionsMap B integerBase hZ X.toBase) := by
  have hfib := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
    (𝟙 (schemeSpace X.base))
  let e := hfib.isoIsPullback _ _ (IsPullback.id_horiz X.toBase)
  have hsnd := (hfib.isoIsPullback_hom_snd _ _ (IsPullback.id_horiz X.toBase)).symm
  have h := hX (schemeSpace X.base) (𝟙 _)
  rw [hsnd, Space.globalFunctionsMap_comp, RingHom.coe_comp] at h
  exact (Function.Bijective.of_comp_iff' (nativeGlobalFunctions_bijective_of_iso B e) _).mp h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An ACTUAL native universal-H0 family with its actual represented total
proves the ORIGINAL field-constants isomorphism. No original H0 assumption. -/
theorem isIso_constants_of_native_H0_represented
    (hZ : B.Contains integerBase) (F : CurveFamily B hZ)
    (hF : HasUniversallyBijectiveGlobalFunctions B hZ F)
    (U : BigFppfOver B integerBase hZ) (e : F.total ≅ schemeSpace U)
    (g : U ⟶ F.base) (he : e.hom ≫ schemeSpaceMap g = F.toBase)
    (K : Type u) [Field K]
    (hbase : (BigFppfOver.toScheme B integerBase hZ).obj F.base = Spec (.of K)) :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
      ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hbase).appTop) := by
  have hb := nativeH0_bijective_globalFunctionsMap B hZ hF
  rw [← he, globalFunctionsMap_comp, RingHom.coe_comp] at hb
  have hg : Function.Bijective (globalFunctionsMap B integerBase hZ (schemeSpaceMap g)) :=
    (Function.Bijective.of_comp_iff' (nativeGlobalFunctions_bijective_of_iso B e) _).mp hb
  exact isIso_constants_of_native_bijective B integerBase hZ g K hbase hg

end M9StacksIntegration.AllTestSchematicGlobalFunctionsReflection
