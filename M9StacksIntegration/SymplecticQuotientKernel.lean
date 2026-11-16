module

public import M9StacksIntegration.SymplecticIsotropicAnnihilation
public import M9StacksIntegration.LagrangianUniversalSectionInjection

/-!
# The genuine symplectic dual is the kernel of the original LG quotient

The proof dualizes the actual quotient short exact sequence. Isotropy
makes the original quotient descend through its dual cokernel. The
induced epimorphism is between rank-three vector bundles and hence an
isomorphism. No kernel identification or exactness is supplied as data.
The endpoint is specialized to every genuine scheme pullback of the
original universal Lagrangian quotient.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance] _root_.Stacks.SchemeCohomology.sheafOfModules_abelian

namespace M9Native.SymplecticQuotientKernel

open LagrangianMatrixChart LagrangianGrassmannian SymplecticQuotientEvaluation
open SymplecticIsotropicAnnihilation

variable {X : Scheme.{u}} {Q : X.Modules}

/-- The actual dual of the kernel map, in the same original symplectic coordinates. -/
def symplecticProjection (q : freeOn X 6 ⟶ Q) :
    freeOn X 6 ⟶ dualSheaf (kernel q) :=
  (symplecticIso X).inv ≫ (MukaiPointLine.coordinatesIso X 6).inv ≫ dualMap (kernel.ι q)

theorem dualEmbedding_comp_symplecticProjection (q : freeOn X 6 ⟶ Q) :
    dualEmbedding q ≫ symplecticProjection q = 0 := by
  change (MukaiPointLine.pointLineMap q ≫ (symplecticIso X).hom) ≫
    ((symplecticIso X).inv ≫ MukaiPointLine.pointCokernelProjection q) = 0
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact MukaiPointLine.pointLineMap_comp q

def dualSequence (q : freeOn X 6 ⟶ Q) : ShortComplex X.Modules :=
  ShortComplex.mk (dualEmbedding q) (symplecticProjection q)
    (dualEmbedding_comp_symplecticProjection q)

/-- Genuine dual exactness, transported by the actual original symplectic isomorphism. -/
theorem dualSequence_shortExact (q : freeOn X 6 ⟶ Q) [Epi q]
    (hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 3) :
    (dualSequence q).ShortExact := by
  let hF := SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) 6
  let hK := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
    q inferInstance 6 3 hF hQ
  let S : ShortComplex X.Modules := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  obtain ⟨w, hd⟩ := exists_dualSheaf_shortExact (kernel.ι q) q (kernel.condition q)
    hS.mono_f hS.epi_g hS.exact
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hK.isFiniteLocallyFree)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hF.isFiniteLocallyFree)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hQ.isFiniteLocallyFree)
  let eF := MukaiPointLine.coordinatesIso X 6 ≪≫ symplecticIso X
  let e : ShortComplex.mk (dualMap q) (dualMap (kernel.ι q)) w ≅ dualSequence q :=
    ShortComplex.isoMk (Iso.refl _) eF (Iso.refl _)
      (by
        change 𝟙 _ ≫ ((dualMap q ≫ (MukaiPointLine.coordinatesIso X 6).hom) ≫
            (symplecticIso X).hom) =
          dualMap q ≫ ((MukaiPointLine.coordinatesIso X 6).hom ≫ (symplecticIso X).hom)
        simp only [Category.id_comp, Category.assoc]) (by
        change eF.hom ≫ (eF.inv ≫ dualMap (kernel.ι q)) = dualMap (kernel.ι q) ≫ 𝟙 _
        rw [Category.comp_id, Iso.hom_inv_id_assoc])
  exact ShortComplex.shortExact_of_iso e hd

/-- The actual symplectic dual embedding and the original quotient form a short exact sequence. -/
theorem quotient_shortExact (q : freeOn X 6 ⟶ Q) [Epi q]
    (hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 3)
    (hq : AnnihilatesSigma X q) :
    (ShortComplex.mk (dualEmbedding q) q
      (@dualEmbedding_comp_quotient X Q hQ.isFiniteLocallyFree q hq)).ShortExact := by
  let hK := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
    q inferInstance 6 3
      (SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) 6) hQ
  let := hQ
  let := hK
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf (kernel q)) 3 :=
    isFiniteLocallyFreeOfRank_dualSheaf (kernel q) 3 hK
  have hS := dualSequence_shortExact q hQ
  let : Epi (dualSequence q).g := hS.epi_g
  have hz : (dualSequence q).f ≫ q = 0 :=
    @dualEmbedding_comp_quotient X Q hQ.isFiniteLocallyFree q hq
  let r : dualSheaf (kernel q) ⟶ Q := hS.exact.desc q hz
  have hr : symplecticProjection q ≫ r = q := hS.exact.g_desc q hz
  let : Epi r := epi_of_epi_fac hr
  let : IsIso r := SheafOfModules.isIso_of_epi_of_isFiniteLocallyFreeOfRank r 3
  let e : dualSequence q ≅ ShortComplex.mk (dualEmbedding q) q hz :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (asIso r)
      (by
        change 𝟙 _ ≫ dualEmbedding q = dualEmbedding q ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]) (by
        change 𝟙 _ ≫ q = symplecticProjection q ≫ r
        rw [Category.id_comp]
        exact hr.symm)
  exact ShortComplex.shortExact_of_iso e hS

/-- The original symplectic dual map satisfies the genuine kernel universal property. -/
def dualEmbedding_isKernel (q : freeOn X 6 ⟶ Q) [Epi q]
    (hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 3)
    (hq : AnnihilatesSigma X q) :
    IsLimit (KernelFork.ofι (dualEmbedding q)
      (@dualEmbedding_comp_quotient X Q hQ.isFiniteLocallyFree q hq)) :=
  (quotient_shortExact q hQ hq).fIsKernel

/-- Canonical actual quotient-kernel/dual-bundle isomorphism. -/
def kernelIsoDual (q : freeOn X 6 ⟶ Q) [Epi q]
    (hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 3)
    (hq : AnnihilatesSigma X q) : kernel q ≅ dualSheaf Q :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel q) (dualEmbedding_isKernel q hQ hq)

variable (K : Type u) [Field K] (l : X ⟶ LagrangianGrassmannian.space K)

/-- The literal original pulled quotient and its actual symplectic dual, as a short complex. -/
def universalSequence : ShortComplex X.Modules :=
  ShortComplex.mk (dualEmbedding (LagrangianUniversalSections.quotientMap K l))
    (LagrangianUniversalSections.quotientMap K l)
    (@dualEmbedding_comp_quotient X (LagrangianUniversalSections.bundle K l)
      (LagrangianUniversalSections.bundle_rank K l).isFiniteLocallyFree
      (LagrangianUniversalSections.quotientMap K l)
      (LagrangianUniversalSectionInjection.universal_quotient_annihilates K l))

/-- The actual original sequence is exact after every genuine scheme pullback. -/
theorem universalSequence_shortExact : (universalSequence K l).ShortExact := by
  let : Epi (LagrangianUniversalSections.quotientMap K l) :=
    (LagrangianUniversalSections.quotient K l).map_epi
  exact quotient_shortExact _ (LagrangianUniversalSections.bundle_rank K l)
    (LagrangianUniversalSectionInjection.universal_quotient_annihilates K l)

/-- No isotropy/kernel premise: every actual pulled universal quotient has this original kernel. -/
def universalDualEmbedding_isKernel :
    IsLimit (KernelFork.ofι (dualEmbedding (LagrangianUniversalSections.quotientMap K l))
      (@dualEmbedding_comp_quotient X (LagrangianUniversalSections.bundle K l)
        (LagrangianUniversalSections.bundle_rank K l).isFiniteLocallyFree
        (LagrangianUniversalSections.quotientMap K l)
        (LagrangianUniversalSectionInjection.universal_quotient_annihilates K l))) := by
  let : Epi (LagrangianUniversalSections.quotientMap K l) :=
    (LagrangianUniversalSections.quotient K l).map_epi
  exact dualEmbedding_isKernel _ (LagrangianUniversalSections.bundle_rank K l)
    (LagrangianUniversalSectionInjection.universal_quotient_annihilates K l)

/-- The literal actual kernel is the actual dual quotient, for any genuine scheme pullback. -/
def universalKernelIsoDual :
    kernel (LagrangianUniversalSections.quotientMap K l) ≅
      dualSheaf (LagrangianUniversalSections.bundle K l) := by
  let : Epi (LagrangianUniversalSections.quotientMap K l) :=
    (LagrangianUniversalSections.quotient K l).map_epi
  exact kernelIsoDual _ (LagrangianUniversalSections.bundle_rank K l)
    (LagrangianUniversalSectionInjection.universal_quotient_annihilates K l)

/-- The native original universal quotient on LG itself, before any pullback presentation. -/
def lagrangianSequence (K : Type u) [Field K] :
    ShortComplex (LagrangianGrassmannian.space K).Modules :=
  let q := (LagrangianPluckerQuotient.quotientOnLG K).map
  ShortComplex.mk (dualEmbedding q) q
    (@dualEmbedding_comp_quotient _ _
      (LagrangianPluckerQuotient.quotientOnLG K).finiteLocallyFree.isFiniteLocallyFree q
      (LagrangianSymplecticAction.lagrangianUniversal_annihilates K))

/-- Genuine original universal symplectic-dual short exactness, with no supplied exactness premise. -/
theorem lagrangianSequence_shortExact (K : Type u) [Field K] :
    (lagrangianSequence K).ShortExact := by
  let : Epi (LagrangianPluckerQuotient.quotientOnLG K).map :=
    (LagrangianPluckerQuotient.quotientOnLG K).map_epi
  exact quotient_shortExact (LagrangianPluckerQuotient.quotientOnLG K).map
    (LagrangianPluckerQuotient.quotientOnLG K).finiteLocallyFree
    (LagrangianSymplecticAction.lagrangianUniversal_annihilates K)

end M9Native.SymplecticQuotientKernel
