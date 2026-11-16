module

public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroAlgebraExtension
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionHomIdealMap
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# The actual ideal map along a morphism of ringed spaces

A map of square-zero extension sheaves over the structure comorphism of
g induces an actual map F -> g_*G. Linearity is derived by lifting local
structure sections to the first extension and gluing. No compatibility
of the independent extension bases is needed.

The local-lift argument adapts the pinned Stacks
RingedSpaceThickening.ExtensionHomIdealMap proof to different spaces.
The pinned native sources are preserved.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.Sites.Conormal (kernelIdeal presentationScalar)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace M9Native.ExtensionIdealMapAlong

/-- The literal structure comorphism, as a map of commutative-ring sheaves. -/
abbrev structureMap {X Y : RingedSpace.{u,u}} (g : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj X.sheaf :=
  ObjectProperty.homMk g.hom.c

variable {X Y S T : RingedSpace.{u,u}} {fY : Y ⟶ S} {fX : X ⟶ T}
    {F : ModuleSheaves Y} {G : ModuleSheaves X}
    (P : SquareZeroAlgebraExtension fY F) (Q : SquareZeroAlgebraExtension fX G)
    (g : X ⟶ Y)
    (β : P.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj Q.sheaf)
    (hβ : β ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map Q.reduction =
      P.reduction ≫ structureMap g)

include hβ

/-- The given ring map sends the original included ideal to the target ideal. -/
theorem map_incl_mem (U : (Opens Y.carrier)ᵒᵖ) (n : F.val.obj U) :
    (β.hom.app U).hom (P.incl U n) ∈
      kernelIdeal Q.reduction.hom ((Opens.map g.hom.base).op.obj U) := by
  have h := congrArg (fun t : P.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj X.sheaf =>
      (t.hom.app U).hom (P.incl U n)) hβ
  change (Q.reduction.hom.app _).hom ((β.hom.app U).hom (P.incl U n)) = 0
  refine h.trans ?_
  change (g.hom.c.app U).hom ((P.reduction.hom.app U).hom (P.incl U n)) = 0
  exact (congrArg (g.hom.c.app U).hom (P.reduction_incl U n)).trans (map_zero _)

/-- The sectionwise coefficient map is obtained from the actual target ideal identification. -/
def coefficientApp (U : (Opens Y.carrier)ᵒᵖ) (n : F.val.obj U) :
    ((modulePushforward g).obj G).val.obj U :=
  Q.ideal.app ((Opens.map g.hom.base).op.obj U)
    ⟨(β.hom.app U).hom (P.incl U n), map_incl_mem P Q g β hβ U n⟩

/-- Inclusion of the constructed coefficient is exactly the given ring map on inclusion. -/
theorem incl_comm_app (U : (Opens Y.carrier)ᵒᵖ) (n : F.val.obj U) :
    (β.hom.app U).hom (P.incl U n) =
      Q.incl ((Opens.map g.hom.base).op.obj U) (coefficientApp P Q g β hβ U n) :=
  (Q.incl_ideal _ ⟨_, map_incl_mem P Q g β hβ U n⟩).symm

theorem coefficientApp_add (U : (Opens Y.carrier)ᵒᵖ) (n n' : F.val.obj U) :
    coefficientApp P Q g β hβ U (n+n') =
      coefficientApp P Q g β hβ U n + coefficientApp P Q g β hβ U n' := by
  apply Q.incl_injective
  rw [Q.incl_add, ← incl_comm_app, ← incl_comm_app, ← incl_comm_app,
    P.incl_add, map_add]

/-- The coefficients commute with the actual pushforward restriction maps. -/
theorem coefficientApp_map {U V : (Opens Y.carrier)ᵒᵖ} (k : U ⟶ V) (n : F.val.obj U) :
    coefficientApp P Q g β hβ V (F.val.map k n) =
      ((modulePushforward g).obj G).val.map k (coefficientApp P Q g β hβ U n) := by
  apply Q.incl_injective
  rw [← incl_comm_app]
  change (β.hom.app V).hom (P.incl V (F.val.map k n)) =
    Q.incl ((Opens.map g.hom.base).op.obj V)
      (G.val.map ((Opens.map g.hom.base).op.map k) (coefficientApp P Q g β hβ U n))
  calc
    (β.hom.app V).hom (P.incl V (F.val.map k n)) =
        (β.hom.app V).hom ((P.sheaf.obj.map k).hom (P.incl U n)) :=
      congrArg (β.hom.app V).hom (P.incl_map U k n).symm
    _ = (Q.sheaf.obj.map ((Opens.map g.hom.base).op.map k)).hom
        ((β.hom.app U).hom (P.incl U n)) :=
      congrArg (fun t => t.hom (P.incl U n)) (β.hom.naturality k)
    _ = (Q.sheaf.obj.map ((Opens.map g.hom.base).op.map k)).hom
        (Q.incl ((Opens.map g.hom.base).op.obj U) (coefficientApp P Q g β hβ U n)) :=
      congrArg (Q.sheaf.obj.map ((Opens.map g.hom.base).op.map k)).hom
        (incl_comm_app P Q g β hβ U n)
    _ = Q.incl ((Opens.map g.hom.base).op.obj V)
        (G.val.map ((Opens.map g.hom.base).op.map k) (coefficientApp P Q g β hβ U n)) :=
      Q.incl_map ((Opens.map g.hom.base).op.obj U) ((Opens.map g.hom.base).op.map k) _

/-- Linearity for structure sections that lift to the first extension. -/
theorem coefficientApp_smul_reduction (U : (Opens Y.carrier)ᵒᵖ)
    (b : P.sheaf.obj.obj U) (n : F.val.obj U) :
    coefficientApp P Q g β hβ U (presentationScalar P.reduction U b • n) =
      presentationScalar P.reduction U b • coefficientApp P Q g β hβ U n := by
  have hb : presentationScalar Q.reduction ((Opens.map g.hom.base).op.obj U)
      ((β.hom.app U).hom b) =
      (g.hom.c.app U).hom (presentationScalar P.reduction U b) :=
    congrArg (fun t : P.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj X.sheaf =>
        (t.hom.app U).hom b) hβ
  change (show G.val.obj ((Opens.map g.hom.base).op.obj U) from
      coefficientApp P Q g β hβ U (presentationScalar P.reduction U b • n)) =
    (g.hom.c.app U).hom (presentationScalar P.reduction U b) •
      (show G.val.obj ((Opens.map g.hom.base).op.obj U) from coefficientApp P Q g β hβ U n)
  rw [← hb]
  apply Q.incl_injective
  calc
    Q.incl _ (coefficientApp P Q g β hβ U (presentationScalar P.reduction U b • n)) =
        (β.hom.app U).hom (P.incl U (presentationScalar P.reduction U b • n)) :=
      (incl_comm_app P Q g β hβ U _).symm
    _ = (β.hom.app U).hom (b * P.incl U n) :=
      congrArg (β.hom.app U).hom (P.incl_smul U b n)
    _ = (β.hom.app U).hom b * (β.hom.app U).hom (P.incl U n) := map_mul _ _ _
    _ = (show Q.sheaf.obj.obj ((Opens.map g.hom.base).op.obj U) from
        (β.hom.app U).hom b) *
        Q.incl ((Opens.map g.hom.base).op.obj U) (coefficientApp P Q g β hβ U n) :=
      congrArg (fun z : Q.sheaf.obj.obj ((Opens.map g.hom.base).op.obj U) =>
        (show Q.sheaf.obj.obj ((Opens.map g.hom.base).op.obj U) from
          (β.hom.app U).hom b) * z) (incl_comm_app P Q g β hβ U n)
    _ = Q.incl _ (presentationScalar Q.reduction ((Opens.map g.hom.base).op.obj U)
        ((β.hom.app U).hom b) •
          (show G.val.obj ((Opens.map g.hom.base).op.obj U) from
            coefficientApp P Q g β hβ U n)) :=
      (Q.incl_smul _ ((β.hom.app U).hom b) _).symm

/-- Full structure-sheaf linearity follows from local lifts and the actual sheaf condition. -/
theorem coefficientApp_smul (U : (Opens Y.carrier)ᵒᵖ)
    (a : ↥((structureSheafRing Y).obj.obj U)) (n : F.val.obj U) :
    coefficientApp P Q g β hβ U (a • n) =
      a • coefficientApp P Q g β hβ U n := by
  obtain ⟨U⟩ := U
  have hsurj := (TopCat.Presheaf.isLocallySurjective_iff P.reduction.hom).1
    P.reduction_surjective U (show ↥(Y.sheaf.obj.obj (op U)) from a)
  choose V hVU hV hxV using fun x : U => hsurj x.1 x.2
  choose b hb using hV
  let N := (modulePushforward g).obj G
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.val.presheaf, N.isSheaf⟩ V U
    (fun x => homOfLE (hVU x))
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxV _⟩) _ _ (fun x => ?_)
  have hres : (structureSheafRing Y).obj.map (homOfLE (hVU x)).op a =
      presentationScalar P.reduction (op (V x)) (b x) := (hb x).symm
  change N.val.map (homOfLE (hVU x)).op _ = N.val.map (homOfLE (hVU x)).op _
  rw [← coefficientApp_map, F.val.map_smul, N.val.map_smul, ← coefficientApp_map, hres]
  exact coefficientApp_smul_reduction P Q g β hβ (op (V x)) (b x) _

/-- The actual coefficient morphism F -> g_*G induced by the original ring map. -/
def coefficientMap : F ⟶ (modulePushforward g).obj G where
  val :=
    { app := fun U => ModuleCat.ofHom (X := F.val.obj U)
        (Y := ((modulePushforward g).obj G).val.obj U)
        { toFun := coefficientApp P Q g β hβ U
          map_add' := coefficientApp_add P Q g β hβ U
          map_smul' := coefficientApp_smul P Q g β hβ U }
      naturality := fun k => ModuleCat.hom_ext (LinearMap.ext fun n =>
        coefficientApp_map P Q g β hβ k n) }

theorem coefficientMap_app (U : (Opens Y.carrier)ᵒᵖ) (n : F.val.obj U) :
    ((coefficientMap P Q g β hβ).val.app U).hom n = coefficientApp P Q g β hβ U n :=
  rfl

/-- The given beta and the constructed module morphism commute with the ORIGINAL inclusions. -/
theorem incl_comm (U : (Opens Y.carrier)ᵒᵖ) (n : F.val.obj U) :
    (β.hom.app U).hom (P.incl U n) =
      Q.incl ((Opens.map g.hom.base).op.obj U)
        (((coefficientMap P Q g β hβ).val.app U).hom n) :=
  incl_comm_app P Q g β hβ U n

end M9Native.ExtensionIdealMapAlong
