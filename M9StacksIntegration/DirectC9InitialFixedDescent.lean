module

public import M9StacksIntegration.DirectC9InitialFixedFibre
public import M9StacksIntegration.CurvePowerGraphRestrictions

/-! Genuine descent of the original fixed degree-seventeen line.
Resetting only the C9 coordinate preserves its actual Picard class;
native Picard equality then gives an actual line isomorphism. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.CurvePower
open CartesianMonoidalCategory

universe u
namespace M9Native.DirectC9InitialFixedDescent

open DirectC9PoincareFamily DirectC9InitialFixedFibre CurvePowerGraphRestrictions
open DirectC9FamilyDegree (familySpace familyClass)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

abbrev firstProjection : familySpace C ⟶ C.left := (fst C (power C 9)).left

theorem oneProjection_isIso : IsIso (coord C 1 0).left := by
  change IsIso (pullback.fst C.hom (𝟙 (Spec (.of k))))
  infer_instance

theorem firstMap_projection :
    (firstMap C 9).left ≫ (coord C 1 0).left = firstProjection k C := by
  have h : firstMap C 9 ≫ coord C 1 0 = fst C (power C 9) := by
    rw [reindex_coord]
    rfl
  exact congrArg Over.Hom.left h

variable (c₀ : power C 0 ⟶ C)

abbrev reset : familySpace C ⟶ familySpace C := firstProjection k C ≫ graph k C c₀

theorem reset_firstProjection : reset k C c₀ ≫ firstProjection k C = firstProjection k C := by
  dsimp only [reset, firstProjection]
  rw [Category.assoc, graph_fst, Category.comp_id]

theorem reset_firstMap : reset k C c₀ ≫ (firstMap C 9).left = (firstMap C 9).left := by
  letI := oneProjection_isIso k C
  apply (cancel_mono (coord C 1 0).left).mp
  simpa only [Category.assoc, firstMap_projection k C] using reset_firstProjection k C c₀

theorem constantGraph_firstClass :
    DirectC9NormalizationClass.graphFamilyClass C (constantPoint C c₀) =
      Stacks.Picard.schemePullbackClass (firstMap C 9).left (pointClass C c₀) :=
  constant_graphClass C c₀ 9

theorem fixedClass_reset :
    Stacks.Picard.schemePullbackClass (reset k C c₀)
        (familyClass C (constantFamily C c₀ 16)) =
      familyClass C (constantFamily C c₀ 16) := by
  rw [DirectC9NormalizationClass.constantFamily_class]
  change (Stacks.Picard.schemePullbackClassHom (reset k C c₀))
      (17 • DirectC9NormalizationClass.graphFamilyClass C (constantPoint C c₀)) = _
  rw [map_nsmul]
  apply congrArg (fun x : Stacks.Picard.ofScheme (familySpace C) => (17 : ℕ) • x)
  let g : familySpace C ⟶ (power C 1).left := (firstMap C 9).left
  let P : Stacks.Picard.ofScheme (power C 1).left := pointClass C c₀
  have hg : DirectC9NormalizationClass.graphFamilyClass C (constantPoint C c₀) =
      Stacks.Picard.schemePullbackClass g P := constantGraph_firstClass k C c₀
  have hr : reset k C c₀ ≫ g = g := reset_firstMap k C c₀
  exact (congrArg (Stacks.Picard.schemePullbackClassHom (reset k C c₀)) hg).trans
    ((Stacks.Picard.schemePullbackClass_comp (reset k C c₀) g P).trans
      ((congrArg (fun f : familySpace C ⟶ (power C 1).left =>
        Stacks.Picard.schemePullbackClass f P) hr).trans hg.symm))

abbrev recoveredLine : (familySpace C).Modules :=
  (Scheme.Modules.pullback (firstProjection k C)).obj (fixedFibreLine k C c₀)

instance recoveredLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf (familySpace C).ringCatSheaf.2
      (recoveredLine k C c₀) :=
  Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj (firstProjection k C)
    (fixedFibreLine k C c₀)

theorem recoveredLine_class :
    @PoincareChern.lineClass (familySpace C) (recoveredLine k C c₀)
        (recoveredLine_isInvertible k C c₀) =
      @PoincareChern.lineClass (familySpace C) (fixedLine C c₀ 16)
        (fixedLine_isInvertible C c₀ 16) := by
  let A : (familySpace C).Modules := fixedLine C c₀ 16
  let hA := fixedLine_isInvertible C c₀ 16
  have hu := @PoincareChern.lineClass_pullback (familySpace C) C.left
    (firstProjection k C) (fixedFibreLine k C c₀) (fixedFibreLine_isInvertible k C c₀)
  have hg := @PoincareChern.lineClass_pullback C.left (familySpace C)
    (graph k C c₀) A hA
  exact hu.trans ((congrArg (Stacks.Picard.schemePullbackClass (firstProjection k C)) hg).trans
    ((Stacks.Picard.schemePullbackClass_comp (firstProjection k C) (graph k C c₀)
      (@PoincareChern.lineClass (familySpace C) A hA)).trans (fixedClass_reset k C c₀)))

theorem nonempty_fixedLine_pullbackIso :
    Nonempty ((fixedLine C c₀ 16 : (familySpace C).Modules) ≅ recoveredLine k C c₀) := by
  apply (Stacks.SheafOfModules.picardClass_eq_iff (familySpace C).presheaf
    (familySpace C).ringCatSheaf.2 (fixedLine C c₀ 16) (recoveredLine k C c₀)
    (fixedLine_isInvertible C c₀ 16) (recoveredLine_isInvertible k C c₀)).1
  exact (recoveredLine_class k C c₀).symm

end M9Native.DirectC9InitialFixedDescent
