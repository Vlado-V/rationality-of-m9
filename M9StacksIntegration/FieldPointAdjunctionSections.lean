module

public import M9StacksIntegration.SpecFieldPullbackSections

/-! The literal canonical pullback-composition comparison takes an
actual local adjunction formula to the actual field-point section map. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.FieldPointAdjunctionSections

open SpecFieldStalkSections SpecFieldPullbackSections

variable (K : Type u) [Field K] {X Y : Scheme.{u}} (i : Y ⟶ X)
  (p : Spec (.of K) ⟶ Y) (M N : X.Modules)

/-- An actual local adjoint formula is preserved by the original field-point pullback,
with the literal native composition comparison on both the source and target. -/
theorem image_of_adjoint (a : (Scheme.Modules.pullback i).obj M ⟶
    (Scheme.Modules.pullback i).obj N) (U : X.Opens)
    (hp : (p ≫ i).base (point K) ∈ U) (tau : Γ(M,U)) (w : Γ(N,U))
    (h : (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _ a).val.app
      (op U)) tau =
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N).val.app (op U)) w) :
    (moduleSpecΓFunctor.map
      (((Scheme.Modules.pullbackComp p i).app M).inv ≫
        (Scheme.Modules.pullback p).map a ≫
          ((Scheme.Modules.pullbackComp p i).app N).hom)).hom
      (pulledSection K (p ≫ i) M U hp tau) =
        pulledSection K (p ≫ i) N U hp w := by
  let V := i ⁻¹ᵁ U
  have hpV : p.base (point K) ∈ V := hp
  have hcomp (P : X.Modules) (s : Γ(P,U)) :=
    Scheme.Modules.pullbackSection_comp p i P U V ⊤ le_rfl
      (preimageTop K p V hpV) (preimageTop K (p ≫ i) U hp) s
  have ht : ((Scheme.Modules.pullbackComp p i).app M).inv.app ⊤
      (pulledSection K (p ≫ i) M U hp tau) =
    pulledSection K p ((Scheme.Modules.pullback i).obj M) V hpV
      (Scheme.Modules.pullbackSection i M U V le_rfl tau) := by
    have hh := congrArg (fun t => ((Scheme.Modules.pullbackComp p i).app M).inv.app ⊤ t)
      (hcomp M tau)
    have hid := congrArg (fun q => q.app ⊤
      (pulledSection K p ((Scheme.Modules.pullback i).obj M) V hpV
        (Scheme.Modules.pullbackSection i M U V le_rfl tau)))
      ((Scheme.Modules.pullbackComp p i).app M).hom_inv_id
    exact hh.symm.trans hid
  have hunit (P : X.Modules) (s : Γ(P,U)) :
      Scheme.Modules.pullbackSection i P U V le_rfl s =
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app P).val.app (op U)) s := by
    change (((Scheme.Modules.pullback i).obj P).presheaf.map (𝟙 (op V))) _ = _
    exact CategoryTheory.Functor.map_id_apply _ _ _
  rw [Adjunction.homEquiv_unit] at h
  change a.app V
    ((((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).val.app (op U)) tau) =
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N).val.app (op U)) w at h
  change ((Scheme.Modules.pullbackComp p i).app N).hom.app ⊤
    (((Scheme.Modules.pullback p).map a).app ⊤
      (((Scheme.Modules.pullbackComp p i).app M).inv.app ⊤
        (pulledSection K (p ≫ i) M U hp tau))) = _
  rw [ht]
  have hn : ((Scheme.Modules.pullback p).map a).app ⊤
      (pulledSection K p ((Scheme.Modules.pullback i).obj M) V hpV
        (Scheme.Modules.pullbackSection i M U V le_rfl tau)) =
    pulledSection K p ((Scheme.Modules.pullback i).obj N) V hpV
      (a.app V (Scheme.Modules.pullbackSection i M U V le_rfl tau)) :=
    pulledSection_naturality K p a V hpV _
  have hs : a.app V (Scheme.Modules.pullbackSection i M U V le_rfl tau) =
      Scheme.Modules.pullbackSection i N U V le_rfl w :=
    (congrArg (a.app V) (hunit M tau)).trans (h.trans (hunit N w).symm)
  exact (congrArg (((Scheme.Modules.pullbackComp p i).app N).hom.app ⊤) hn).trans
    ((congrArg (fun z => ((Scheme.Modules.pullbackComp p i).app N).hom.app ⊤
      (pulledSection K p ((Scheme.Modules.pullback i).obj N) V hpV z)) hs).trans
        (hcomp N w))

end M9Native.FieldPointAdjunctionSections
