module

public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCN

@[expose] public section

-- bundled from Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCD
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Gen

theorem map_aff {E R S : Type} [CommRing E] [CommRing R] [CommRing S] (i : E →+* R) (f : R →+* S) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) E) (P : Matrix (Fin n) (Fin m) E) (Q : Matrix (Fin m) (Fin m) E) (x : Matrix (Fin n) (Fin n) R) :
    (M.map i * x * P.map i + Q.map i).map f = M.map (f.comp i) * x.map f * P.map (f.comp i) + Q.map (f.comp i) := by
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map,
    Matrix.map_map]
  rfl

theorem map_aff_one {E R S : Type} [CommRing E] [CommRing R] [CommRing S] (i : E →+* R) (f : R →+* S) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) E) (P : Matrix (Fin n) (Fin m) E) (Q : Matrix (Fin m) (Fin m) E) (h : M * P + Q = 1)
    (x : Matrix (Fin n) (Fin n) R) (hx : x.map f = 1) : (M.map i * x * P.map i + Q.map i).map f = 1 := by
  rw [map_aff, hx, Matrix.mul_one]
  have e : (M * P + Q).map (f.comp i) = 1 := by
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← e, Matrix.map_add _ (map_add _), Matrix.map_mul]

end Gen

section Emb

variable {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (hι : HSpace.IsIsomEmb B A ι) {s : GA D B → GA D A}
  (hs : ∀ h, EmbRel A B ι (s h) h)

include hι hs

theorem emb_mat (h : GA D B) : mt A (s h) =
    HMul.hMul (HMul.hMul ((frameMat A B ι).map (incA D)) (mt B h)) ((prM A B ι).map (incA D)) + (coM A B ι).map (incA D) :=
  emb_gen (incA D) _ _ _ (add_sub_cancel _ _) (mt A (s h)) (mt B h) (hs h).1 fun j =>
    (hs h).2 (fun k => coM A B ι k j) (funext fun i => congrFun (congrFun (perp_rel hι) i) j)

theorem emb_fin {k : GA D B} (hk : k ∈ GfC B) : s k ∈ GfC A := by
  have a : infHom B k = 1 := hk
  refine Units.ext (?_ : (mt A (s k)).map (infPart D) = 1)
  rw [emb_mat hι hs]
  exact map_aff_one _ _ _ _ _ (add_sub_cancel _ _) _ (congrArg Units.val a)

end Emb

end Formalism.L2.Fam.ThC

end
end

-- bundled from Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCJ
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

theorem alg_trace_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (h : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), add_add_add_comm]
  | tmul a e =>
    have h4 : (a ⊗ₜ[F] e : R ⊗[F] E) = a • inclR R e := by
      show _ = a • ((1 : R) ⊗ₜ[F] e)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h5 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h5, ← TensorProduct.tmul_add, ← h, h4, map_smul, trace_gen, smul_eq_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one (A := E), ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_comm]

end Gen

variable {D : D7}

variable {V W : HSp D}


end Formalism.L2.Fam.ThC

end
end

