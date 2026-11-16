module

public import M9StacksIntegration.MukaiGeneratedImage
public import M9StacksIntegration.MukaiSaturationRank
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.TorsionFreeDimensionOne
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ProperMapping.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# Rank of the literal generated image on a smooth integral curve

The image is exactly `image (biprod.desc j a)`. It is coherent and is a
torsion-free subsheaf of the original ambient bundle, hence finite locally
free on a regular integral curve. The original monomorphisms from `Q` and
into `E`, whose ranks agree, sandwich its actual generic-stalk dimension.
Constancy then proves its rank everywhere. No rank of the image is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.MukaiGeneratedImage

variable {X : Scheme.{u}}

/-- The literal categorical generated image is coherent. The native
coherence theorem for the abelian image is transported by its canonical
isomorphism to this actual categorical image. -/
theorem generatedImage_isCoherent {Q E O : X.Modules}
    [hQ : Q.IsCoherent] [hE : E.IsCoherent] [hO : O.IsCoherent]
    (j : Q ⟶ E) (a : O ⟶ E) : (generatedImage j a).IsCoherent := by
  have hsum : (Q ⊞ O).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_X₂_of_shortExact
      (ShortComplex.Splitting.ofHasBinaryBiproduct Q O).shortExact hQ hO
  let : (CategoryTheory.Abelian.image (biprod.desc j a)).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_image hsum hE (biprod.desc j a)
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    (CategoryTheory.Abelian.imageIsoImage (biprod.desc j a)).symm

/-- Torsion freeness passes to an actual quasi-coherent subsheaf, using
the original injective maps on native local-ring stalks. -/
theorem isTorsionFree_of_mono [IsIntegral X] {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (i : F ⟶ G) [Mono i]
    (hG : IsTorsionFree G) : IsTorsionFree F := by
  refine (AlgebraicGeometry.isTorsionFree_iff_forall_stalk F).mpr fun x => ?_
  let : Module (X.presheaf.stalk x) (MukaiSaturationRank.Stalk F x) :=
    Stacks.SheafOfModules.FlatShortExact.stalkModule F x
  let : Module (X.presheaf.stalk x) (MukaiSaturationRank.Stalk G x) :=
    Stacks.SheafOfModules.FlatShortExact.stalkModule G x
  have : Module.IsTorsionFree (X.presheaf.stalk x) (MukaiSaturationRank.Stalk G x) :=
    (AlgebraicGeometry.isTorsionFree_iff_forall_stalk G).mp hG x
  exact (MukaiSaturationRank.stalkMap_injective i x).moduleIsTorsionFree
    (MukaiSaturationRank.stalkMap i x) (fun r m => (MukaiSaturationRank.stalkMap i x).map_smul r m)

/-- Between bundles of equal rank on a regular integral curve, adjoining
any coherent source to an actual subbundle leaves the literal generated
image finite locally free of that same rank. -/
theorem isFiniteLocallyFreeOfRank_generatedImage [IsIntegral X]
    (hregular : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (r : ℕ) {Q E O : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    [O.IsCoherent] (j : Q ⟶ E) [Mono j] (a : O ⟶ E) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (generatedImage j a) r := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hregular
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q r
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  let hQcoh : Q.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X Q
  let hEcoh : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  let hIcoh : (generatedImage j a).IsCoherent := generatedImage_isCoherent j a
  let : Q.IsFiniteType := hQcoh.isFiniteType
  let : E.IsFiniteType := hEcoh.isFiniteType
  let : (generatedImage j a).IsFiniteType := hIcoh.isFiniteType
  let : Q.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent Q
  let : E.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent E
  let : (generatedImage j a).IsQuasicoherent :=
    _root_.isQuasicoherent_of_isCoherent (generatedImage j a)
  have hEtf : IsTorsionFree E :=
    (AlgebraicGeometry.isTorsionFree_iff_isFiniteLocallyFree hregular hdim E).mpr inferInstance
  have hItf : IsTorsionFree (generatedImage j a) := isTorsionFree_of_mono (inclusion j a) hEtf
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (generatedImage j a) :=
    (AlgebraicGeometry.isTorsionFree_iff_isFiniteLocallyFree hregular hdim
      (generatedImage j a)).mp hItf
  apply Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq
    (generatedImage j a) r (genericPoint X)
  let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  let (F : X.Modules) : Module (X.presheaf.stalk (genericPoint X))
      (MukaiSaturationRank.Stalk F (genericPoint X)) :=
    Stacks.SheafOfModules.FlatShortExact.stalkModule F (genericPoint X)
  let : Module.Finite (X.presheaf.stalk (genericPoint X))
      (MukaiSaturationRank.Stalk Q (genericPoint X)) :=
    Scheme.Modules.finite_stalk_of_isCoherent Q (genericPoint X)
  let : Module.Finite (X.presheaf.stalk (genericPoint X))
      (MukaiSaturationRank.Stalk E (genericPoint X)) :=
    Scheme.Modules.finite_stalk_of_isCoherent E (genericPoint X)
  let : Module.Finite (X.presheaf.stalk (genericPoint X))
      (MukaiSaturationRank.Stalk (generatedImage j a) (genericPoint X)) :=
    Scheme.Modules.finite_stalk_of_isCoherent (generatedImage j a) (genericPoint X)
  have hQdim : Module.finrank (X.presheaf.stalk (genericPoint X))
      (MukaiSaturationRank.Stalk Q (genericPoint X)) = r :=
    (Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk Q).symm.trans
      (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank Q r (genericPoint X))
  have hEdim : Module.finrank (X.presheaf.stalk (genericPoint X))
      (MukaiSaturationRank.Stalk E (genericPoint X)) = r :=
    (Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk E).symm.trans
      (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank E r (genericPoint X))
  have hlo := LinearMap.finrank_le_finrank_of_injective
    (MukaiSaturationRank.stalkMap_injective (subobjectMap j a) (genericPoint X))
  have hhi := LinearMap.finrank_le_finrank_of_injective
    (MukaiSaturationRank.stalkMap_injective (inclusion j a) (genericPoint X))
  have hIdim : Module.finrank (X.presheaf.stalk (genericPoint X))
      (MukaiSaturationRank.Stalk (generatedImage j a) (genericPoint X)) = r :=
    le_antisymm (hhi.trans hEdim.le) (hQdim.symm.le.trans hlo)
  exact (Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk (generatedImage j a)).trans hIdim

/-- In the actual rank-two Mukai modification, the original image of
`Q ⊕ O → E` is a rank-two bundle on the smooth integral curve. -/
theorem rank_two_on_smooth_curve (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    {Q E : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2]
    (j : Q ⟶ E) [Mono j] (a : MukaiBundle.structureModule X ⟶ E) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (generatedImage j a) 2 := by
  have hregular := isRegular_of_smooth_over_field f
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hregular
  let : (MukaiBundle.structureModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  exact isFiniteLocallyFreeOfRank_generatedImage hregular
    (IsCurve.topologicalKrullDim_eq_one f).le 2 j a

end M9Native.MukaiGeneratedImage
