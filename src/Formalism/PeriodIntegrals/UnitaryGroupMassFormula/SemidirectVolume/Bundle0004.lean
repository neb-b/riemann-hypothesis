module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModTop
section
noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct Matrix

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

def sigRLin : R ⊗[F] E →ₗ[R] R ⊗[F] E :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : R →ₗ[R] R) σ.toLinearMap

theorem sigRLin_eq (x : R ⊗[F] E) : sigRLin R σ x = PI.UJClassFin.sigR R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigRLin, PI.UJClassFin.sigR]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

variable [IsTopologicalRing (R ⊗[F] E)]

theorem continuous_sigR : Continuous (PI.UJClassFin.sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (sigRLin R σ) := IsModuleTopology.continuous_of_linearMap _
  have he : (PI.UJClassFin.sigR R σ : R ⊗[F] E → R ⊗[F] E) = sigRLin R σ :=
    funext fun x => (sigRLin_eq R σ x).symm
  rw [he]
  exact hc

theorem continuous_hR {X : Type} [TopologicalSpace X] {u v : X → Fin M → R ⊗[F] E}
    (hu : Continuous u) (hv : Continuous v) : Continuous fun x => hR R σ J (u x) (v x) := by
  unfold hR Formalism.UG.hform
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_sigR R σ).comp ((continuous_apply i).comp hu)).mul continuous_const).mul
    ((continuous_apply j).comp hv)

theorem continuous_linear_action {X : Type} [TopologicalSpace X] {g : X → HA R σ J}
    {v : X → Fin M → R ⊗[F] E} (hg : Continuous g) (hv : Continuous v) :
    Continuous fun x => lin R σ J (g x) (v x) := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  unfold lin
  simp only [Matrix.mulVecLin_apply]
  exact (hm.comp hg).matrix_mulVec hv

end Cont

section HAcont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem mat_inv_eq (hJ : IsHermND σ J) (g : HA R σ J) :
    ((HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (J⁻¹).map (inclR (F := F) R) *
        Formalism.UG.cT (PI.UJClassFin.sigR R σ) ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) :
          Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J := by
  obtain ⟨_, hdet⟩ := hJ
  set A : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
    ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) with hA
  set B : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
    ((HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) with hB
  set Ji : Matrix (Fin M) (Fin M) (R ⊗[F] E) := (J⁻¹).map (inclR (F := F) R) with hJi
  have hmem : Formalism.UG.cT (PI.UJClassFin.sigR R σ) A * JR (F := F) R J * A = JR (F := F) R J := g.2
  have hAB : A * B = 1 := by
    have e : (HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) = (HA.mat R σ J g)⁻¹ := by
      first
        | rfl
        | exact Subgroup.coe_inv _
    rw [hA, hB, e]
    exact Units.mul_inv _
  have hJJ : Ji * JR (F := F) R J = 1 := by
    rw [hJi]
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.mpr hdet)]
    simp
  calc B = (Ji * JR (F := F) R J) * B := by rw [hJJ, Matrix.one_mul]
    _ = Ji * (Formalism.UG.cT (PI.UJClassFin.sigR R σ) A * JR (F := F) R J * A) * B := by rw [hmem]
    _ = Ji * Formalism.UG.cT (PI.UJClassFin.sigR R σ) A * JR (F := F) R J * (A * B) := by simp only [Matrix.mul_assoc]
    _ = Ji * Formalism.UG.cT (PI.UJClassFin.sigR R σ) A * JR (F := F) R J := by rw [hAB, Matrix.mul_one]

variable [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]

theorem continuous_into_HA (hJ : IsHermND σ J) {X : Type} [TopologicalSpace X] {f : X → HA R σ J}
    (hf : Continuous fun x => ((HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E))) : Continuous f := by
  have hcT : Continuous fun x => Formalism.UG.cT (PI.UJClassFin.sigR R σ)
      ((HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
    refine continuous_matrix fun i j => ?_
    exact (continuous_sigR R σ).comp (hf.matrix_elem j i)
  have hI : Continuous fun x =>
      ((HA.mat R σ J (f x)⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
    have e : (fun x =>
        ((HA.mat R σ J (f x)⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) =
        fun x => (J⁻¹).map (inclR (F := F) R) *
          Formalism.UG.cT (PI.UJClassFin.sigR R σ) ((HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) :
            Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J :=
      funext fun x => mat_inv_eq hJ (f x)
    rw [e]
    exact (continuous_const.matrix_mul hcT).matrix_mul continuous_const
  have hGL : Continuous fun x => (HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) :=
    Units.continuous_iff.2 ⟨hf, hI⟩
  first
    | exact continuous_induced_rng.2 hGL
    | exact hGL.subtype_mk fun x => (f x).2

end HAcont

section Raw

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)] (σ : E →ₐ[F] E)
  {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

end Raw

end PI.VolSemiDirect.W.Md
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.NnrealEqOneOfMulSelf
section
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Measure
open scoped NNReal

section Gen

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}

def trG (X : GL (Fin k) A) : GL (Fin k) A where
  val := (X : Matrix (Fin k) (Fin k) A).transpose
  inv := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).transpose
  val_inv := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]

theorem trG_val (X : GL (Fin k) A) :
    ((trG X : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) = (X : Matrix (Fin k) (Fin k) A).transpose :=
  rfl

theorem trG_mul (X Y : GL (Fin k) A) : trG (X * Y) = trG Y * trG X := by
  ext1
  simp [trG_val, Matrix.transpose_mul]

theorem trG_one : trG (1 : GL (Fin k) A) = 1 := by
  ext1
  simp [trG_val]

theorem trG_inv (X : GL (Fin k) A) : trG X⁻¹ = (trG X)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← trG_mul, mul_inv_cancel, trG_one]

theorem modM_transv (hT : TransvHaar) (X : GL (Fin k) A) (i j : Fin k) (hij : i ≠ j) (c : A)
    (hX : (X : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c) : modM X = 1 := by
  have h := hT A k i j hij c (addHaar : Measure (Fin k → A)) inferInstance
  have e : (phi X : (Fin k → A) → (Fin k → A)) = Matrix.mulVec (Matrix.transvection i j c) := by
    funext v
    rw [phi_apply, hX]
  apply modM_of_map X (addHaar : Measure (Fin k → A))
  rw [e]
  exact h

theorem transvection_transpose (i j : Fin k) (c : A) :
    (Matrix.transvection i j c).transpose = Matrix.transvection j i c := by
  ext a b
  simp [Matrix.transvection, Matrix.transpose_apply, Matrix.one_apply, Matrix.single_apply]
  aesop

theorem modM_tr_of_mem (hT : TransvHaar) (X : GL (Fin k) A)
    (hX : X ∈ Subgroup.closure ({g : GL (Fin k) A | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin k → A, (g : Matrix (Fin k) (Fin k) A) = Matrix.diagonal d})) :
    modM (trG X) = modM X := by
  induction hX using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, j, c, hij, hx⟩ | ⟨d, hx⟩
    · rw [modM_transv hT x i j hij c hx, modM_transv hT (trG x) j i hij.symm c
        (by rw [trG_val, hx, transvection_transpose])]
    · have : trG x = x := by
        ext1
        rw [trG_val, hx, Matrix.diagonal_transpose]
      rw [this]
  | one => rw [trG_one]
  | mul x y _ _ hx hy => rw [trG_mul, modM_mul, modM_mul, hx, hy, mul_comm]
  | inv x _ hx => rw [trG_inv, modM_inv, modM_inv, hx]

end Gen

theorem nnreal_eq_one_of_mul_self {x : ℝ≥0} (h : x * x = 1) : x = 1 := by
  have h' : (x : ℝ) * x = 1 := by exact_mod_cast h
  have : (x : ℝ) = 1 := by nlinarith [x.coe_nonneg]
  exact_mod_cast this

theorem orthInv_of (h1 : AdeleStableRankOne) (h2 : ElimSR1) (h3 : TransvHaar) : OrthInv := by
  intro F _ _ k G X hG hXG μ hμ
  obtain ⟨hlc, hsc, ht2⟩ := PI.VolStabSW.TopoAF.afTop_holds F
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hd := congrArg Matrix.det hXG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hdd : X.det * X.det = 1 := by
    have : (X.det * X.det) * G.det = 1 * G.det := by
      calc (X.det * X.det) * G.det = X.det * G.det * X.det := by ring
        _ = 1 * G.det := by rw [hd, one_mul]
    exact hG.mul_left_inj.1 this
  have hX : IsUnit X.det := ⟨⟨X.det, X.det, hdd, hdd⟩, rfl⟩
  let Xu : GL (Fin k) (AF F) := Matrix.nonsingInvUnit X hX
  let Gu : GL (Fin k) (AF F) := Matrix.nonsingInvUnit G hG
  have hrel : trG Xu * Gu * Xu = Gu := by
    ext1
    exact hXG
  have hm := congrArg modM hrel
  rw [modM_mul, modM_mul, modM_tr_of_mem h3 Xu (h2 (AF F) (h1 F) k Xu)] at hm
  have hpos : 0 < modM Gu := addEquivAddHaarChar_pos (phi Gu)
  have hsq : modM Xu * modM Xu = 1 := by
    have : (modM Xu * modM Xu) * modM Gu = 1 * modM Gu := by
      calc (modM Xu * modM Xu) * modM Gu = modM Xu * modM Gu * modM Xu := by ring
        _ = 1 * modM Gu := by rw [hm, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  have hmod := nnreal_eq_one_of_mul_self hsq
  have e := map_phi_of_modM Xu hmod μ
  have e2 : (phi Xu : (Fin k → AF F) → (Fin k → AF F)) = Matrix.mulVec X := by
    funext v
    rfl
  rw [e2] at e
  exact e

end PI.VolSemiDirect.W.Cj
end
end

