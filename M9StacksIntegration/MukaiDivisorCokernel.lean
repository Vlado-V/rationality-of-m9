module

public import M9StacksIntegration.MukaiGeneratedImageDegree
public import M9StacksIntegration.MukaiGeneratedCartierImage
public import M9StacksIntegration.CurveDivisorSections
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.Basic

/-!
# The literal cokernel I_D → O_X and its actual length

The object is identified with i_* O_D through the short exact
structure-sheaf sequence. Its H0 is the actual coordinate algebra of D.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace M9Native.MukaiDivisorCokernel

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Cokernel of the literal ideal inclusion. -/
abbrev divisorCokernel (D : X.IdealSheafData) : X.Modules :=
  cokernel (Stacks.Divisors.idealSheafInclusion D)

/-- This is the actual pushforward of the structure sheaf of D. -/
def divisorCokernelIso (D : X.IdealSheafData) :
    divisorCokernel D ≅ (Scheme.Modules.pushforward D.subschemeι).obj
      (MukaiBundle.structureModule D.subscheme) := by
  have hS := Stacks.Cohomology.AmpleH1.shortExact_idealSheaf D.subschemeι
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) hS.exact.gIsCokernel

variable (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The direct image of O_D has no stalk outside the actual image of D. -/
theorem pushforward_structure_support_subset (D : X.IdealSheafData) :
    SheafOfModules.supp ((Scheme.Modules.pushforward D.subschemeι).obj
      (MukaiBundle.structureModule D.subscheme)) ⊆ Set.range D.subschemeι.base := by
  intro x hx
  by_contra hn
  let G := MukaiBundle.structureModule D.subscheme
  let P : D.subscheme.toTopCat.Presheaf Ab.{u} := G.val.presheaf
  have hP : P.IsSheaf := G.isSheaf
  have ht := ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange
    D.subschemeι.base hP (IsClosedImmersion.isClosedEmbedding D.subschemeι) x hn
  let PP : X.toTopCat.Presheaf Ab.{u} :=
    (TopCat.Presheaf.pushforward Ab.{u} D.subschemeι.base).obj P
  have hz : IsZero (TopCat.Presheaf.stalk (C := Ab.{u}) PP x) :=
    (isZero_zero Ab.{u}).of_iso (ht.uniqueUpToIso (isZero_zero Ab.{u}).isTerminal)
  have hs : Subsingleton (TopCat.Presheaf.stalk (C := Ab.{u}) PP x) :=
    AddCommGrpCat.subsingleton_of_isZero hz
  exact hx.elim (fun z hz => hz (hs.elim _ _))

/-- The literal ideal cokernel has zero-dimensional actual support. -/
theorem divisorCokernel_support (D : X.IdealSheafData)
    (hD : topologicalKrullDim D.subscheme ≤ 0) :
    topologicalKrullDim (SheafOfModules.supp (divisorCokernel D)) ≤ 0 := by
  have hs := pushforward_structure_support_subset D
  have he := (IsClosedImmersion.isClosedEmbedding D.subschemeι).isEmbedding
  have hd : topologicalKrullDim (Set.range D.subschemeι.base) =
      topologicalKrullDim D.subscheme := he.toHomeomorph.isHomeomorph.topologicalKrullDim_eq.symm
  have hm := MukaiGeneratedImage.support_dim_le_of_subset hs
  rw [← SheafOfModules.supp_eq_of_iso (divisorCokernelIso D)] at hm
  exact hm.trans (hd.le.trans hD)

theorem divisorCokernel_h0 (D : X.IdealSheafData)
    (hD : topologicalKrullDim D.subscheme ≤ 0) :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop)).toAlgebra
    Module.finrank k (cohomologyOverField k f (divisorCokernel D) 0) =
      Module.finrank k Γ(D.subscheme, ⊤) := by
  letI : Algebra k Γ(D.subscheme, ⊤) :=
    (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop)).toAlgebra
  exact (cohomologyOverFieldIso k f (divisorCokernelIso D) 0).toLinearEquiv.finrank_eq.trans
    ((cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k D.subschemeι f
      (MukaiBundle.structureModule D.subscheme) 0).toLinearEquiv.finrank_eq.symm.trans
        (finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k (D.subschemeι ≫ f)))

end M9Native.MukaiDivisorCokernel

