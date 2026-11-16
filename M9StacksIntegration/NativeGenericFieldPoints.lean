module

public import M9StacksIntegration.NativeGenericPullbackEvaluation

@[expose] public section

/-! Actual generic function-field points over the original coefficient field.
The coefficient algebra is the literal structural map into the generic stalk.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.NativeGenericFieldPoints

open NativeFunctionFieldFunctor NativeGenericPullbackEvaluation

variable {X : Scheme.{u}} [IsIntegral X]

/-- The native generic-stalk point has the actual structural coefficient map. -/
theorem genericSpec_structure (k : Type u) [Field k] (p : X ⟶ Spec (.of k)) :
    genericSpec X ≫ p =
      Spec.map (CommRingCat.ofHom (GrassmannianCharts.structureScalarMap k p)) := by
  apply ext_of_isAffine
  let κ : CommRingCat.of k ⟶ X.functionField :=
    CommRingCat.ofHom (GrassmannianCharts.structureScalarMap k p)
  change (genericSpec X ≫ p).appTop = (Spec.map κ).appTop
  have hr :
      (Spec.map κ).appTop =
      (Scheme.ΓSpecIso (.of k)).hom ≫ κ ≫
        (Scheme.ΓSpecIso X.functionField).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso (.of k)).inv).mp
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
      (Scheme.ΓSpecIso_inv_naturality κ).symm
  rw [Scheme.Hom.comp_appTop, hr]
  simp only [genericSpec, Scheme.fromSpecStalk_appTop, homOfLE_refl, op_id]
  change p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) (by trivial) ≫
      (Scheme.ΓSpecIso X.functionField).inv =
    (Scheme.ΓSpecIso (.of k)).hom ≫
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) (by trivial)) ≫
      (Scheme.ΓSpecIso X.functionField).inv
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The actual coefficient algebra on the original function field. -/
abbrev functionFieldAlgebra (k : Type u) [Field k] (p : X ⟶ Spec (.of k)) :
    Algebra k X.functionField :=
  (GrassmannianCharts.structureScalarMap k p).toAlgebra

section OverBase

variable (k : Type u) [Field k] (p : X ⟶ Spec (.of k))
variable [Algebra k X.functionField]

/-- Every actual coefficient-preserving field embedding gives a point over
the original base, with the structural square proved rather than assumed. -/
theorem point_projection {L : Type u} [Field L] [Algebra k L]
    (hscalar : algebraMap k X.functionField = GrassmannianCharts.structureScalarMap k p)
    (s : X.functionField →ₐ[k] L) :
    point (X := X) s.toRingHom ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  rw [point, Category.assoc, genericSpec_structure, ← Spec.map_comp]
  congr 1
  ext c
  change s (GrassmannianCharts.structureScalarMap k p c) = algebraMap k L c
  rw [← hscalar]
  exact s.commutes c

/-- The actual generic field point as an object over the original base. -/
def overPoint {L : Type u} [Field L] [Algebra k L]
    (hscalar : algebraMap k X.functionField = GrassmannianCharts.structureScalarMap k p)
    (s : X.functionField →ₐ[k] L) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ Over.mk p := by
  exact Over.homMk (point (X := X) s.toRingHom) (point_projection k p hscalar s)

@[simp]
theorem overPoint_left {L : Type u} [Field L] [Algebra k L]
    (hscalar : algebraMap k X.functionField = GrassmannianCharts.structureScalarMap k p)
    (s : X.functionField →ₐ[k] L) :
    (overPoint (X := X) k p hscalar s).left = point (X := X) s.toRingHom := rfl

end OverBase

/-- Change of extension field uses the literal composite field embedding. -/
theorem point_comp {L M : Type u} [Field L] [Field M]
    (s : X.functionField →+* L) (e : L →+* M) :
    Spec.map (CommRingCat.ofHom e) ≫ point s = point (e.comp s) := by
  rw [point, point, ← Category.assoc, ← Spec.map_comp]
  rfl

end M9Native.NativeGenericFieldPoints
