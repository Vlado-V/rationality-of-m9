module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionPullback
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization

/-! Actual sections over the spectrum of a field are its sole stalk, with
the scalar inclusion given by the original Spec section and germ maps. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace M9Native.SpecFieldStalkSections

variable (K : Type u) [Field K]

abbrev space := Spec (.of K)
def point : space K := IsLocalRing.closedPoint K
abbrev localRing := (space K).presheaf.stalk (point K)

def terminalNeighborhood : IsTerminal (op (⟨⊤, trivial⟩ : OpenNhds (point K))) :=
  IsTerminal.ofUniqueHom
    (fun V => Quiver.Hom.op (homOfLE (by
      intro y _
      have hy : y = point K := Subsingleton.elim _ _
      simpa only [hy] using V.unop.2)))
    (fun _ _ => Subsingleton.elim _ _)

theorem germ_isIso {C : Type v} [Category.{u} C] [HasColimits.{u} C]
    (F : TopCat.Presheaf C (space K)) : IsIso (F.germ ⊤ (point K) trivial) :=
  isIso_ι_of_isTerminal (terminalNeighborhood K) ((OpenNhds.inclusion (point K)).op ⋙ F)

/-- The original scalar map to the actual local ring at the field point. -/
def scalarStalkMap : K →+* localRing K :=
  ((space K).presheaf.germ ⊤ (point K) trivial).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom

def scalarStalkEquiv : K ≃+* localRing K := by
  haveI := germ_isIso K (space K).presheaf
  exact (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.trans
    (asIso ((space K).presheaf.germ ⊤ (point K) trivial)).commRingCatIsoToRingEquiv

@[simp] theorem scalarStalkEquiv_apply (a : K) : scalarStalkEquiv K a = scalarStalkMap K a := rfl

instance localRingAlgebra : Algebra K (localRing K) := (scalarStalkMap K).toAlgebra

@[instance_reducible] def moduleStalk (M : (space K).Modules) :
    Module K (M.presheaf.stalk (point K)) :=
  letI := Stacks.ModuleStalkSpecialization.stalkModule M (point K)
  Module.compHom _ (scalarStalkMap K)

/-- This is the actual global germ map, made linear for the actual
`moduleSpecΓFunctor` scalar restriction. -/
def sectionsStalkEquiv (M : (space K).Modules) :
    letI := moduleStalk K M
    (moduleSpecΓFunctor.obj M) ≃ₗ[K] M.presheaf.stalk (point K) := by
  letI := Stacks.ModuleStalkSpecialization.stalkModule M (point K)
  letI := moduleStalk K M
  haveI := germ_isIso K M.presheaf
  refine LinearEquiv.ofBijective
    (show (moduleSpecΓFunctor.obj M) →ₗ[K] M.presheaf.stalk (point K) from
    { toFun := fun s => (M.presheaf.germ ⊤ (point K) trivial).hom s
      map_add' := map_add _
      map_smul' := fun c s => ?_ })
    (ConcreteCategory.bijective_of_isIso (M.presheaf.germ ⊤ (point K) trivial))
  change M.presheaf.germ ⊤ (point K) trivial
      ((Scheme.ΓSpecIso (.of K)).inv.hom c • (show Γ(M, ⊤) from s)) = _
  exact Stacks.ModuleStalkSpecialization.germ_smul M
    (U := ⊤) (x := point K) (by trivial) _ s

@[simp] theorem sectionsStalkEquiv_apply (M : (space K).Modules)
    (s : moduleSpecΓFunctor.obj M) :
    letI := moduleStalk K M
    sectionsStalkEquiv K M s = M.presheaf.germ ⊤ (point K) trivial s := rfl

end M9Native.SpecFieldStalkSections
