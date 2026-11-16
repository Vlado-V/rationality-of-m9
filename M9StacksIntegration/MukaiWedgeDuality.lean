module

public import M9StacksIntegration.MukaiCupAlternating
public import M9StacksIntegration.SchemeWedgeDuality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom

/-!
# The actual rank-two wedge duality

The canonical exterior algebra, the native degree-one generator
isomorphism, and the native wedge-duality theorem identify a rank-two
bundle with its sheaf-Hom into the actual second exterior power.
This provides the sheaf-level perfectness needed for the Mukai pairing;
no self-duality is supplied as data.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace M9Native.MukaiWedgeDuality

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

open M9Native.MukaiCupAlternating

/-- The actual scheme, read as a ringed site. -/
abbrev ringedSite (X : Scheme.{u}) : RingedSite.{u,u,u} :=
  ⟨X.Opens, Opens.grothendieckTopology X, X.sheaf⟩

/-- An actual source isomorphism gives the actual precomposition
isomorphism on the native sheaf of local module morphisms. -/
def internalHomPreIso {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) (D : X.Modules) :
    RingedSite.internalHomSheaf (ringedSite X) G D ≅
      RingedSite.internalHomSheaf (ringedSite X) F D where
  hom := RingedSite.internalHomPre (ringedSite X) e.hom
  inv := RingedSite.internalHomPre (ringedSite X) e.inv
  hom_inv_id := by
    apply _root_.SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext φ
    change (_root_.restrFun X.sheaf.obj U.unop).map e.inv.val ≫
      ((_root_.restrFun X.sheaf.obj U.unop).map e.hom.val ≫ φ) = φ
    rw [← Category.assoc, ← Functor.map_comp]
    have h : e.inv.val ≫ e.hom.val = 𝟙 G.val :=
      congrArg _root_.SheafOfModules.Hom.val e.inv_hom_id
    rw [h]
    exact (congrArg (fun t => t ≫ φ) ((_root_.restrFun X.sheaf.obj U.unop).map_id G.val)).trans
      (Category.id_comp φ)
  inv_hom_id := by
    apply _root_.SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext φ
    change (_root_.restrFun X.sheaf.obj U.unop).map e.hom.val ≫
      ((_root_.restrFun X.sheaf.obj U.unop).map e.inv.val ≫ φ) = φ
    rw [← Category.assoc, ← Functor.map_comp]
    have h : e.hom.val ≫ e.inv.val = 𝟙 F.val :=
      congrArg _root_.SheafOfModules.Hom.val e.hom_inv_id
    rw [h]
    exact (congrArg (fun t => t ≫ φ) ((_root_.restrFun X.sheaf.obj U.unop).map_id F.val)).trans
      (Category.id_comp φ)

/-- An actual target isomorphism gives the actual postcomposition
isomorphism on the native sheaf of local module morphisms. -/
def internalHomPostIso {X : Scheme.{u}} {D W : X.Modules}
    (e : D ≅ W) (F : X.Modules) :
    RingedSite.internalHomSheaf (ringedSite X) F D ≅
      RingedSite.internalHomSheaf (ringedSite X) F W where
  hom := RingedSite.internalHomPost (ringedSite X) e.hom
  inv := RingedSite.internalHomPost (ringedSite X) e.inv
  hom_inv_id := by
    apply _root_.SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext φ
    change (φ ≫ (_root_.restrFun X.sheaf.obj U.unop).map
        e.hom.val) ≫
      (_root_.restrFun X.sheaf.obj U.unop).map e.inv.val = φ
    rw [Category.assoc, ← Functor.map_comp]
    have h : e.hom.val ≫ e.inv.val = 𝟙 D.val :=
      congrArg _root_.SheafOfModules.Hom.val e.hom_inv_id
    rw [h]
    exact (congrArg (fun t => φ ≫ t) ((_root_.restrFun X.sheaf.obj U.unop).map_id D.val)).trans
      (Category.comp_id φ)
  inv_hom_id := by
    apply _root_.SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext φ
    change (φ ≫ (_root_.restrFun X.sheaf.obj U.unop).map
        e.inv.val) ≫
      (_root_.restrFun X.sheaf.obj U.unop).map e.hom.val = φ
    rw [Category.assoc, ← Functor.map_comp]
    have h : e.inv.val ≫ e.hom.val = 𝟙 W.val :=
      congrArg _root_.SheafOfModules.Hom.val e.inv_hom_id
    rw [h]
    exact (congrArg (fun t => φ ≫ t) ((_root_.restrFun X.sheaf.obj U.unop).map_id W.val)).trans
      (Category.comp_id φ)

/-- Evaluate the actual native sheaf-Hom at a genuine global section. -/
def evaluateSection {X : Scheme.{u}} (F W : X.Modules) (σ : F.sections) :
    RingedSite.internalHomSheaf (ringedSite X) F W ⟶ W where
  val :=
    { app U :=
        letI := _root_.homModule (ringedSite X).O.obj
          ((ringedSite X).valOf F) ((ringedSite X).valOf W) U.unop
        ModuleCat.ofHom
        { toFun := fun φ => Stacks.SheafOfModules.evalSection X.sheaf.obj F.val W.val U φ (σ.val U)
          map_add' := fun φ ψ =>
            Stacks.SheafOfModules.evalSection_add_left X.sheaf.obj F.val W.val U φ ψ (σ.val U)
          map_smul' := fun r φ =>
            Stacks.SheafOfModules.evalSection_smul_left X.sheaf.obj F.val W.val U r φ (σ.val U) }
      naturality {U V} j := by
        apply ModuleCat.hom_ext
        ext φ
        change Stacks.SheafOfModules.evalSection X.sheaf.obj F.val W.val V
          ((RingedSite.internalHomSheaf (ringedSite X) F W).val.map j φ) (σ.val V) =
          W.val.map j (Stacks.SheafOfModules.evalSection X.sheaf.obj F.val W.val U φ (σ.val U))
        exact (congrArg
          (Stacks.SheafOfModules.evalSection X.sheaf.obj F.val W.val V
            ((RingedSite.internalHomSheaf (ringedSite X) F W).val.map j φ))
          (σ.property j).symm).trans
            (Stacks.SheafOfModules.evalSection_naturality X.sheaf.obj F.val W.val j φ (σ.val U)) }

/-- The actual exterior generator products are skew, derived from the
proved square-zero identity by polarization. -/
theorem generator_mul_swap {X : Scheme.{u}} (F : X.Modules)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X) F) (U : X.Opensᵒᵖ) (x y : F.val.obj U) :
    (A.exterior.mul 1 1).app U (A.exteriorGenerator.val.app U x)
      (A.exteriorGenerator.val.app U y) =
      -(A.exterior.mul 1 1).app U (A.exteriorGenerator.val.app U y)
        (A.exteriorGenerator.val.app U x) := by
  have h := A.squareZero_exteriorGenerator U (x+y)
  have hyx : (A.exterior.mul 1 1).app U (A.exteriorGenerator.val.app U y)
      (A.exteriorGenerator.val.app U x) +
      (A.exterior.mul 1 1).app U (A.exteriorGenerator.val.app U x)
        (A.exteriorGenerator.val.app U y) = 0 := by
    simpa only [map_add, AddMonoidHom.add_apply, A.squareZero_exteriorGenerator U x,
      A.squareZero_exteriorGenerator U y, zero_add, add_zero] using h
  exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hyx)

/-- The actual rank-two wedge pairing is a perfect pairing of sheaves:
F is the native sheaf-Hom from F into its actual second exterior power. -/
def rankTwoWedgeIso {X : Scheme.{u}} (F : X.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2) :
    F ≅ RingedSite.internalHomSheaf (ringedSite X) F (exteriorSquare F) := by
  let A := exteriorAlgebras F
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F (1+1) := hF
  let : IsIso (M9Native.SchemeWedgeDuality.wedgeHom A.exterior 1 1) :=
    M9Native.SchemeWedgeDuality.isIso_wedgeHom A.exterior A.exterior_isExteriorAlgebra 1 1
  exact A.exteriorGeneratorIso ≪≫
    asIso (M9Native.SchemeWedgeDuality.wedgeHom A.exterior 1 1) ≪≫
      internalHomPreIso (X := X) A.exteriorGeneratorIso (exteriorSquare F)

/-- The perfect sheaf pairing is the actual generator-wedge map followed
by actual precomposition; this pins down its evaluation, not only its type. -/
theorem rankTwoWedgeIso_hom {X : Scheme.{u}} (F : X.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2) :
    (rankTwoWedgeIso F hF).hom =
      (exteriorAlgebras F).exteriorGeneratorIso.hom ≫
        M9Native.SchemeWedgeDuality.wedgeHom (exteriorAlgebras F).exterior 1 1 ≫
          RingedSite.internalHomPre (ringedSite X)
            (C := exteriorSquare F) (exteriorAlgebras F).exteriorGeneratorIso.hom := rfl

/-- Its actual local evaluation is the original ordered wedge product. -/
theorem rankTwoWedgeIso_eval {X : Scheme.{u}} (F : X.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2)
    (U : X.Opensᵒᵖ) (x y : F.val.obj U) :
    Stacks.SheafOfModules.evalSection X.sheaf.obj F.val (exteriorSquare F).val U
      ((rankTwoWedgeIso F hF).hom.val.app U x) y =
        ((exteriorAlgebras F).exterior.mul 1 1).app U
          ((exteriorAlgebras F).exteriorGenerator.val.app U x)
          ((exteriorAlgebras F).exteriorGenerator.val.app U y) := by
  rw [rankTwoWedgeIso_hom, (exteriorAlgebras F).exteriorGeneratorIso_hom]
  change ((M9Native.SchemeWedgeDuality.wedgeHom (exteriorAlgebras F).exterior 1 1).val.app U
      ((exteriorAlgebras F).exteriorGenerator.val.app U x)).app
        (op (Over.mk (𝟙 U.unop))) ((exteriorAlgebras F).exteriorGenerator.val.app U y) = _
  exact M9Native.SchemeWedgeDuality.wedgeHom_eval (exteriorAlgebras F).exterior 1 1
    U.unop _ _

/-- Evaluating the actual rank-two duality at σ is minus wedge by σ.
This is the actual sheaf-level contraction identity needed by Serre. -/
theorem rankTwoWedgeIso_comp_evaluateSection {X : Scheme.{u}} (F : X.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2) (σ : F.sections) :
    (rankTwoWedgeIso F hF).hom ≫ evaluateSection F (exteriorSquare F) σ =
      -wedgeBySection F σ := by
  rw [rankTwoWedgeIso_hom, (exteriorAlgebras F).exteriorGeneratorIso_hom]
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext y
  change ((M9Native.SchemeWedgeDuality.wedgeHom (exteriorAlgebras F).exterior 1 1).val.app U
      ((exteriorAlgebras F).exteriorGenerator.val.app U y)).app
        (op (Over.mk (𝟙 U.unop))) ((exteriorAlgebras F).exteriorGenerator.val.app U (σ.val U)) =
    -((exteriorAlgebras F).exterior.mul 1 1).app U
      ((exteriorAlgebras F).exteriorGenerator.val.app U (σ.val U))
      ((exteriorAlgebras F).exteriorGenerator.val.app U y)
  exact (M9Native.SchemeWedgeDuality.wedgeHom_eval (exteriorAlgebras F).exterior 1 1
    U.unop _ _).trans (generator_mul_swap F (exteriorAlgebras F) U y (σ.val U))

/-- With a genuine identification of det(F)=⋀²F with Ω, the actual
rank-two wedge pairing identifies F with SheafHom(F,Ω). -/
def rankTwoDeterminantPairingIso {X : Scheme.{u}} (F : X.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2)
    (Ω : X.Modules) (d : exteriorSquare F ≅ Ω) :
    F ≅ RingedSite.internalHomSheaf (ringedSite X) F Ω :=
  rankTwoWedgeIso F hF ≪≫ internalHomPostIso (X := X) d F

end M9Native.MukaiWedgeDuality
