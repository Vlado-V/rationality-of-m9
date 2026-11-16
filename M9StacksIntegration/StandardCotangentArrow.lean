module

public import M9StacksIntegration.StandardCurveCotangentExt

/-!
# Actual standard cotangent arrows and their ordinary Ext maps

Full faithfulness of the original single-sheaf functor extracts the unique
actual sheaf map from an actual derived arrow between smooth cotangent
objects. This records the original arrow, its scalar-compatible class
map, and its evaluation-natural dual H1 map. Identifying a particular
native cotangent arrow with the literal differential is a separate
calculation; no such equality is assumed here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.RingedSpaceThickening RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.AlgebraicGeometry.ReflexiveModules

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.StandardCotangentArrow

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
  [Smooth pX] [Smooth pY] (g : X ⟶ Y)

local instance nativeHasExt : HasExt.{u} X.Modules := hasExt_of_enoughInjectives X.Modules

/-- The sheaf morphism uniquely determined by the actual normalized
derived arrow; no equality to a prescribed differential is supplied. -/
def normalizedMap
    (q : (derivedPullback g.toLRSHom.toShHom).obj
      (StandardSmoothCotangent.nativeObject pY) ⟶
        StandardSmoothCotangent.nativeObject pX) :
    (Scheme.Modules.pullback g).obj (Scheme.Hom.relativeDifferentials pY) ⟶
      Scheme.Hom.relativeDifferentials pX :=
  (DerivedCategory.singleFunctor X.Modules 0).preimage
    ((StandardSmoothCotangent.pulledDifferentialsIso pY g).inv ≫ q ≫
      (StandardSmoothCotangent.differentialsIso pX).hom)

/-- The original derived arrow is retained under the actual sheaf map. -/
theorem single_map_normalizedMap
    (q : (derivedPullback g.toLRSHom.toShHom).obj
      (StandardSmoothCotangent.nativeObject pY) ⟶
        StandardSmoothCotangent.nativeObject pX) :
    (DerivedCategory.singleFunctor X.Modules 0).map (normalizedMap pX pY g q) =
      (StandardSmoothCotangent.pulledDifferentialsIso pY g).inv ≫ q ≫
        (StandardSmoothCotangent.differentialsIso pX).hom :=
  (DerivedCategory.singleFunctor X.Modules 0).map_preimage _

/-- The genuine normalization square commutes for every actual arrow. -/
theorem normalizedMap_commutes
    (q : (derivedPullback g.toLRSHom.toShHom).obj
      (StandardSmoothCotangent.nativeObject pY) ⟶
        StandardSmoothCotangent.nativeObject pX) :
    q ≫ (StandardSmoothCotangent.differentialsIso pX).hom =
      (StandardSmoothCotangent.pulledDifferentialsIso pY g).hom ≫
        (DerivedCategory.singleFunctor X.Modules 0).map (normalizedMap pX pY g q) := by
  rw [single_map_normalizedMap]
  simp only [Iso.hom_inv_id_assoc]

/-- The actual standard pulled-cotangent class group has the original
ordinary Yoneda Ext interpretation, with original field scalars. -/
@[instance_reducible]
def pulledExtModule (G : X.Modules) :
    Module k ((derivedPullback g.toLRSHom.toShHom).obj
      (StandardSmoothCotangent.nativeObject pY) ⟶
        ((DerivedCategory.singleFunctor X.Modules 0).obj G)⟦(1 : ℤ)⟧) := by
  let := modulesLinearOverField k pX
  exact inferInstanceAs (Module k
    ((show DerivedCategory X.Modules from
      (derivedPullback g.toLRSHom.toShHom).obj
        (StandardSmoothCotangent.nativeObject pY)) ⟶
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)⟦(1 : ℤ)⟧))

/-- The actual standard pulled-cotangent class group has the original
ordinary Yoneda Ext interpretation, with original field scalars. -/
def pulledOrdinaryExtOneLinearEquiv (G : X.Modules) :
    letI := modulesLinearOverField k pX
    letI := pulledExtModule pX pY g G
    ( (derivedPullback g.toLRSHom.toShHom).obj
        (StandardSmoothCotangent.nativeObject pY) ⟶
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)⟦(1 : ℤ)⟧ ) ≃ₗ[k]
        Ext.{u} ((Scheme.Modules.pullback g).obj
          (Scheme.Hom.relativeDifferentials pY)) G 1 := by
  let := modulesLinearOverField k pX
  let := pulledExtModule pX pY g G
  exact (Linear.homCongr k (C := DerivedCategory X.Modules)
    (StandardSmoothCotangent.pulledDifferentialsIso pY g)
    (Iso.refl _)).trans (Ext.homLinearEquiv (R := k)).symm

omit [Smooth pX] in
/-- The pulled class comparison acts by literal precomposition. -/
theorem pulledOrdinaryExtOneLinearEquiv_hom (G : X.Modules)
    (ξ : (derivedPullback g.toLRSHom.toShHom).obj
      (StandardSmoothCotangent.nativeObject pY) ⟶
        ((DerivedCategory.singleFunctor X.Modules 0).obj G)⟦(1 : ℤ)⟧) :
    letI := modulesLinearOverField k pX
    letI := pulledExtModule pX pY g G
    (pulledOrdinaryExtOneLinearEquiv pX pY g G ξ).hom =
      (StandardSmoothCotangent.pulledDifferentialsIso pY g).inv ≫ ξ := by
  let := modulesLinearOverField k pX
  let := pulledExtModule pX pY g G
  change (Ext.homLinearEquiv (R := k)
      (X := (Scheme.Modules.pullback g).obj (Scheme.Hom.relativeDifferentials pY))
      (Y := G) (n := 1))
    ((Ext.homLinearEquiv (R := k)
      (X := (Scheme.Modules.pullback g).obj (Scheme.Hom.relativeDifferentials pY))
      (Y := G) (n := 1)).symm
      (((StandardSmoothCotangent.pulledDifferentialsIso pY g).inv ≫ ξ) ≫ 𝟙 _)) =
        (StandardSmoothCotangent.pulledDifferentialsIso pY g).inv ≫ ξ
  rw [LinearEquiv.apply_symm_apply]
  exact Category.comp_id _

/-- Original derived restriction becomes Yoneda precomposition by the
actual uniquely extracted sheaf map. -/
theorem restriction_ordinaryExt
    (q : (derivedPullback g.toLRSHom.toShHom).obj
      (StandardSmoothCotangent.nativeObject pY) ⟶
        StandardSmoothCotangent.nativeObject pX)
    (G : X.Modules) (ξ : extOneNaiveCotangent pX.toLRSHom.toShHom G) :
    letI := modulesLinearOverField k pX
    letI := StandardCurveCotangentExt.nativeExtModule pX G
    letI := pulledExtModule pX pY g G
    pulledOrdinaryExtOneLinearEquiv pX pY g G (q ≫ ξ) =
      (Ext.mk₀ (normalizedMap pX pY g q)).comp
        (StandardCurveCotangentExt.ordinaryExtOneLinearEquiv pX G ξ) (zero_add 1) := by
  let := modulesLinearOverField k pX
  let := StandardCurveCotangentExt.nativeExtModule pX G
  let := pulledExtModule pX pY g G
  apply Ext.ext
  rw [pulledOrdinaryExtOneLinearEquiv_hom, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, StandardCurveCotangentExt.ordinaryExtOneLinearEquiv_hom,
    single_map_normalizedMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- On actual smooth curves the pulled class group is actual H1 of the
dual of the actual pulled cotangent line. -/
def pulledTangentOneLinearEquiv [IsCurve k pY] :
    letI := modulesLinearOverField k pX
    letI := pulledExtModule pX pY g (InvertibleExtCancellation.unit X)
    ((derivedPullback g.toLRSHom.toShHom).obj
        (StandardSmoothCotangent.nativeObject pY) ⟶
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (InvertibleExtCancellation.unit X))⟦(1 : ℤ)⟧) ≃ₗ[k]
      cohomologyOverField k pX (CurveTangentLineGeometry.pulledTangentLine pY g) 1 := by
  let := modulesLinearOverField k pX
  let := pulledExtModule pX pY g (InvertibleExtCancellation.unit X)
  let := CurveTangentLineGeometry.differentials_rank_one pY
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj (Scheme.Hom.relativeDifferentials pY)) :=
    (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
      X _).mpr (isFiniteLocallyFreeOfRank_pullback g (Scheme.Hom.relativeDifferentials pY) 1)
  exact (pulledOrdinaryExtOneLinearEquiv pX pY g (InvertibleExtCancellation.unit X)).trans
    (DualExtNaturality.dualExtOneCohomologyLinearEquiv pX _)

/-- The H1 map of the actual normalized arrow is exactly its original
derived restriction map, with the evaluation-natural dual convention. -/
theorem restriction_tangentOne [IsCurve k pX] [IsCurve k pY]
    (q : (derivedPullback g.toLRSHom.toShHom).obj
      (StandardSmoothCotangent.nativeObject pY) ⟶
        StandardSmoothCotangent.nativeObject pX)
    (ξ : extOneNaiveCotangent pX.toLRSHom.toShHom (InvertibleExtCancellation.unit X)) :
    letI := modulesLinearOverField k pX
    letI := StandardCurveCotangentExt.nativeExtModule pX (InvertibleExtCancellation.unit X)
    letI := pulledExtModule pX pY g (InvertibleExtCancellation.unit X)
    pulledTangentOneLinearEquiv pX pY g (q ≫ ξ) =
      cohomologyOverFieldMap k pX (dualMap (normalizedMap pX pY g q)) 1
        (StandardCurveCotangentExt.tangentOneLinearEquiv pX ξ) := by
  let := modulesLinearOverField k pX
  let := StandardCurveCotangentExt.nativeExtModule pX (InvertibleExtCancellation.unit X)
  let := pulledExtModule pX pY g (InvertibleExtCancellation.unit X)
  let := CurveTangentLineGeometry.differentials_isInvertible pX
  let := CurveTangentLineGeometry.differentials_rank_one pY
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj (Scheme.Hom.relativeDifferentials pY)) :=
    (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
      X _).mpr (isFiniteLocallyFreeOfRank_pullback g (Scheme.Hom.relativeDifferentials pY) 1)
  change DualExtNaturality.dualExtOneCohomologyLinearEquiv pX _
    (pulledOrdinaryExtOneLinearEquiv pX pY g (InvertibleExtCancellation.unit X) (q ≫ ξ)) = _
  rw [restriction_ordinaryExt]
  exact DualExtNaturality.dualExtOneCohomologyLinearEquiv_naturality pX
    (normalizedMap pX pY g q)
    (StandardCurveCotangentExt.ordinaryExtOneLinearEquiv pX (InvertibleExtCancellation.unit X) ξ)

/-- Vanishing of the original restricted class is equivalent to the
literal H1 vanishing for the actual extracted dual map. -/
theorem restriction_eq_zero_iff [IsCurve k pX] [IsCurve k pY]
    (q : (derivedPullback g.toLRSHom.toShHom).obj
      (StandardSmoothCotangent.nativeObject pY) ⟶
        StandardSmoothCotangent.nativeObject pX)
    (ξ : extOneNaiveCotangent pX.toLRSHom.toShHom (InvertibleExtCancellation.unit X)) :
    letI := modulesLinearOverField k pX
    letI := StandardCurveCotangentExt.nativeExtModule pX (InvertibleExtCancellation.unit X)
    q ≫ ξ = 0 ↔
      cohomologyOverFieldMap k pX (dualMap (normalizedMap pX pY g q)) 1
        (StandardCurveCotangentExt.tangentOneLinearEquiv pX ξ) = 0 := by
  let := modulesLinearOverField k pX
  let := StandardCurveCotangentExt.nativeExtModule pX (InvertibleExtCancellation.unit X)
  let := pulledExtModule pX pY g (InvertibleExtCancellation.unit X)
  rw [← restriction_tangentOne pX pY g q ξ]
  exact (pulledTangentOneLinearEquiv pX pY g).map_eq_zero_iff.symm

end M9Native.StandardCotangentArrow
