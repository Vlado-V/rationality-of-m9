module

public import M9StacksIntegration.NativeVectorSectionZeroPullback
public import M9StacksIntegration.LagrangianMatrixChart

/-!
# Genuine native vector-zero-scheme transport

An actual bundle comparison carrying the actual pulled section to the
actual target section gives equality of the full native zero ideals.
When the underlying morphism is an actual scheme isomorphism this gives
an actual isomorphism of the full zero schemes, with original inclusion
and arbitrary structural-map triangles. Nilpotents are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.NativeVectorSectionZeroTransport

def closedSubschemeIsoOfComap {X Y : Scheme.{u}} (e : X ≅ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData) (h : J = I.comap e.hom) :
    J.subscheme ≅ I.subscheme :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme h) ≪≫ I.comapIso e.hom ≪≫
    asIso (pullback.snd e.hom I.subschemeι)

private theorem subschemeι_transport {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

private theorem closedSubschemeIsoOfComap_hom_inclusion {X Y : Scheme.{u}} (e : X ≅ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData) (h : J = I.comap e.hom) :
    (closedSubschemeIsoOfComap e I J h).hom ≫ I.subschemeι = J.subschemeι ≫ e.hom := by
  let q := eqToIso (congrArg Scheme.IdealSheafData.subscheme h)
  let a := I.comapIso e.hom
  have hp := congrArg (fun z => (q.hom ≫ a.hom) ≫ z)
    (pullback.condition (f := e.hom) (g := I.subschemeι)).symm
  calc
    _ = (q.hom ≫ a.hom) ≫ pullback.snd e.hom I.subschemeι ≫ I.subschemeι := by
      rfl
    _ = (q.hom ≫ a.hom) ≫ pullback.fst e.hom I.subschemeι ≫ e.hom := by
      simpa only [Category.assoc] using hp
    _ = (q.hom ≫ (I.comap e.hom).subschemeι) ≫ e.hom := by
      simpa only [Category.assoc, a] using congrArg (fun z => q.hom ≫ z ≫ e.hom)
        (Scheme.IdealSheafData.comapIso_hom_fst I e.hom)
    _ = _ := congrArg (fun z => z ≫ e.hom) (subschemeι_transport h)

section Bundles

variable {X Y : Scheme.{u}} (F : Y.Modules) (G : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} F]
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} G]

/-- The full native ideal equality under an actual pulled bundle and
section comparison, for every original scheme morphism. -/
theorem ideal_eq_comap_of_iso (r : ℕ)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
    [hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G r] (f : X ⟶ Y)
    (a : (Scheme.Modules.pullback f).obj F ≅ G)
    (s : Γ(F, ⊤)) (t : Γ(G, ⊤))
    (h : a.hom.app ⊤ (pullbackGlobalSections f F s) = t) :
    Stacks.Chow.zeroSchemeOfSection X G t =
      (Stacks.Chow.zeroSchemeOfSection Y F s).comap f := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback f).obj F) r :=
    AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback
      f.base f.toRingCatSheafHom F r hF
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} ((Scheme.Modules.pullback f).obj F) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      ((Scheme.Modules.pullback f).obj F) r
  calc
    _ = Stacks.Chow.zeroSchemeOfSection X G
        (a.hom.app ⊤ (pullbackGlobalSections f F s)) :=
      congrArg (Stacks.Chow.zeroSchemeOfSection X G) h.symm
    _ = Stacks.Chow.zeroSchemeOfSection X ((Scheme.Modules.pullback f).obj F)
        (pullbackGlobalSections f F s) := by
      rw [NativeVectorSectionZeroPullback.zeroSchemeOfSection_eq_evaluationIdeal,
        NativeVectorSectionZeroPullback.zeroSchemeOfSection_eq_evaluationIdeal]
      exact (LagrangianMatrixChart.sectionZeroIdeal_eq_of_iso r a
        (pullbackGlobalSections f F s)).symm
    _ = _ := NativeVectorSectionZeroPullback.zeroSchemeOfSection_pullback f F r s

/-- Actual scheme and bundle isomorphisms induce the actual full native
zero-scheme isomorphism, with no zero-scheme comparison premise. -/
def zeroSchemeIso (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G r] (e : X ≅ Y)
    (a : (Scheme.Modules.pullback e.hom).obj F ≅ G)
    (s : Γ(F, ⊤)) (t : Γ(G, ⊤))
    (h : a.hom.app ⊤ (pullbackGlobalSections e.hom F s) = t) :
    (Stacks.Chow.zeroSchemeOfSection X G t).subscheme ≅
      (Stacks.Chow.zeroSchemeOfSection Y F s).subscheme :=
  closedSubschemeIsoOfComap e (Stacks.Chow.zeroSchemeOfSection Y F s)
    (Stacks.Chow.zeroSchemeOfSection X G t) (ideal_eq_comap_of_iso F G r e.hom a s t h)

/-- The true original immersion triangle of the full zero schemes. -/
@[reassoc] theorem zeroSchemeIso_hom_inclusion (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G r] (e : X ≅ Y)
    (a : (Scheme.Modules.pullback e.hom).obj F ≅ G)
    (s : Γ(F, ⊤)) (t : Γ(G, ⊤))
    (h : a.hom.app ⊤ (pullbackGlobalSections e.hom F s) = t) :
    (zeroSchemeIso F G r e a s t h).hom ≫
        (Stacks.Chow.zeroSchemeOfSection Y F s).subschemeι =
      (Stacks.Chow.zeroSchemeOfSection X G t).subschemeι ≫ e.hom :=
  closedSubschemeIsoOfComap_hom_inclusion e (Stacks.Chow.zeroSchemeOfSection Y F s)
    (Stacks.Chow.zeroSchemeOfSection X G t) (ideal_eq_comap_of_iso F G r e.hom a s t h)

/-- Every genuine structural triangle, in particular the original
field-scalar projection, is retained by the zero-scheme isomorphism. -/
theorem zeroSchemeIso_over (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G r] (e : X ≅ Y)
    (a : (Scheme.Modules.pullback e.hom).obj F ≅ G)
    (s : Γ(F, ⊤)) (t : Γ(G, ⊤))
    (h : a.hom.app ⊤ (pullbackGlobalSections e.hom F s) = t)
    {B : Scheme.{u}} (p : X ⟶ B) (q : Y ⟶ B) (he : e.hom ≫ q = p) :
    (zeroSchemeIso F G r e a s t h).hom ≫
        ((Stacks.Chow.zeroSchemeOfSection Y F s).subschemeι ≫ q) =
      (Stacks.Chow.zeroSchemeOfSection X G t).subschemeι ≫ p :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ q) (zeroSchemeIso_hom_inclusion F G r e a s t h)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => (Stacks.Chow.zeroSchemeOfSection X G t).subschemeι ≫ z) he)))

end Bundles

end M9Native.NativeVectorSectionZeroTransport
