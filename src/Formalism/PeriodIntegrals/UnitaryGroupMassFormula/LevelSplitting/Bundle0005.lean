module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjHA

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MapFstConjTranspose
section
noncomputable section

namespace PI.LevelKSplit.W.MVA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Ring

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]

def p1 : (R1 × R2) ⊗[F] E →+* R1 ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.fst F R1 R2) (AlgHom.id F E)).toRingHom

def p2 : (R1 × R2) ⊗[F] E →+* R2 ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.snd F R1 R2) (AlgHom.id F E)).toRingHom


variable {R1 R2} in
def crd (R : Type) [CommRing R] [Algebra F R] :
    R ⊗[F] E ≃ₗ[R] (Fin (Module.finrank F E) → R) :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun

theorem crd_symm (R : Type) [CommRing R] [Algebra F R] (c : Fin (Module.finrank F E) → R) :
    (crd (E := E) R).symm c = ∑ k, c k ⊗ₜ (Module.finBasis F E k) := by
  simp [crd, Module.Basis.equivFun_symm_apply, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

theorem fst_coordinates (x : (R1 × R2) ⊗[F] E) :
    p1 R1 R2 x = (crd R1).symm (fun k => (crd (R1 × R2) x k).1) := by
  conv_lhs => rw [← (crd (E := E) (R1 × R2)).symm_apply_apply x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [crd_symm, crd_symm, map_sum]
  rfl

theorem snd_coordinates (x : (R1 × R2) ⊗[F] E) :
    p2 R1 R2 x = (crd R2).symm (fun k => (crd (R1 × R2) x k).2) := by
  conv_lhs => rw [← (crd (E := E) (R1 × R2)).symm_apply_apply x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [crd_symm, crd_symm, map_sum]
  rfl

def qq (a : R1 ⊗[F] E) (b : R2 ⊗[F] E) : (R1 × R2) ⊗[F] E :=
  (crd (R1 × R2)).symm (fun k => (crd R1 a k, crd R2 b k))

theorem fst_pair (a : R1 ⊗[F] E) (b : R2 ⊗[F] E) : p1 R1 R2 (qq R1 R2 a b) = a := by
  unfold qq
  rw [fst_coordinates, LinearEquiv.apply_symm_apply]
  exact (crd R1).symm_apply_apply a

theorem snd_pair (a : R1 ⊗[F] E) (b : R2 ⊗[F] E) : p2 R1 R2 (qq R1 R2 a b) = b := by
  unfold qq
  rw [snd_coordinates, LinearEquiv.apply_symm_apply]
  exact (crd R2).symm_apply_apply b

theorem qq_p (x : (R1 × R2) ⊗[F] E) : qq R1 R2 (p1 R1 R2 x) (p2 R1 R2 x) = x := by
  apply (crd (E := E) (R1 × R2)).injective
  unfold qq
  rw [LinearEquiv.apply_symm_apply, fst_coordinates, snd_coordinates, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem ext_p {x y : (R1 × R2) ⊗[F] E} (h1 : p1 R1 R2 x = p1 R1 R2 y)
    (h2 : p2 R1 R2 x = p2 R1 R2 y) : x = y := by
  rw [← qq_p R1 R2 x, ← qq_p R1 R2 y, h1, h2]

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem fst_conj_bis (x : (R1 × R2) ⊗[F] E) :
    p1 R1 R2 (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (R1 × R2) σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R1 σ (p1 R1 R2 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem snd_conj_alt (x : (R1 × R2) ⊗[F] E) :
    p2 R1 R2 (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (R1 × R2) σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R2 σ (p2 R1 R2 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fst_inclusion (e : E) : p1 R1 R2 (inclR (F := F) (R1 × R2) e) = inclR (F := F) R1 e := rfl

theorem snd_inclusion (e : E) : p2 R1 R2 (inclR (F := F) (R1 × R2) e) = inclR (F := F) R2 e := rfl

theorem map_fst_conj_transpose (P : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E)) :
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (R1 × R2) σ) P).map (p1 R1 R2) =
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R1 σ) (P.map (p1 R1 R2)) := by
  ext i j
  simp [Formalism.UG.cT, fst_conj_bis]

theorem map_snd_conj_transpose (P : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E)) :
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (R1 × R2) σ) P).map (p2 R1 R2) =
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R2 σ) (P.map (p2 R1 R2)) := by
  ext i j
  simp [Formalism.UG.cT, snd_conj_alt]

theorem map_fst_form : (JR (F := F) (R1 × R2) J).map (p1 R1 R2) = JR (F := F) R1 J := by
  ext i j
  exact fst_inclusion R1 R2 (J i j)

theorem map_snd_form : (JR (F := F) (R1 × R2) J).map (p2 R1 R2) = JR (F := F) R2 J := by
  ext i j
  exact snd_inclusion R1 R2 (J i j)

def mlift (m : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E) :=
  Matrix.of fun i j => qq R1 R2 ((1 : Matrix (Fin M) (Fin M) (R1 ⊗[F] E)) i j) (m i j)

theorem matrix_lift_fst (m : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) : (mlift R1 R2 m).map (p1 R1 R2) = 1 := by
  ext i j
  exact fst_pair R1 R2 _ _

theorem matrix_lift_snd (m : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) : (mlift R1 R2 m).map (p2 R1 R2) = m := by
  ext i j
  exact snd_pair R1 R2 _ _

theorem mext {P Q : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E)} (h1 : P.map (p1 R1 R2) = Q.map (p1 R1 R2))
    (h2 : P.map (p2 R1 R2) = Q.map (p2 R1 R2)) : P = Q := by
  ext i j
  exact ext_p R1 R2 (congrArg (· i j) h1) (congrArg (· i j) h2)

theorem mlift_mul (m m' : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) :
    mlift R1 R2 m * mlift R1 R2 m' = mlift R1 R2 (m * m') := by
  apply mext
  · rw [Matrix.map_mul, matrix_lift_fst, matrix_lift_fst, matrix_lift_fst, one_mul]
  · rw [Matrix.map_mul, matrix_lift_snd, matrix_lift_snd, matrix_lift_snd]

theorem mlift_one : mlift R1 R2 (1 : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) = 1 := by
  apply mext
  · rw [matrix_lift_fst, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [matrix_lift_snd, Matrix.map_one _ (map_zero _) (map_one _)]

def glift (u : GL (Fin M) (R2 ⊗[F] E)) : GL (Fin M) ((R1 × R2) ⊗[F] E) :=
  ⟨mlift R1 R2 (u : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)), mlift R1 R2 (↑u⁻¹ : Matrix (Fin M) (Fin M) _),
    by rw [mlift_mul, u.mul_inv, mlift_one], by rw [mlift_mul, u.inv_mul, mlift_one]⟩

theorem glift_mem (g : HA R2 σ J) : glift R1 R2 (HA.mat R2 σ J g) ∈ HR (R1 × R2) σ J := by
  have hg : HA.mat R2 σ J g ∈ HR R2 σ J := g.2
  change Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R2 σ) ((HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) * JR (F := F) R2 J *
    (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) = JR (F := F) R2 J at hg
  change Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (R1 × R2) σ) (mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) *
    JR (F := F) (R1 × R2) J * mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) = JR (F := F) (R1 × R2) J
  apply mext
  · rw [Matrix.map_mul, Matrix.map_mul, map_fst_conj_transpose, map_fst_form, matrix_lift_fst]
    ext i j
    simp [Formalism.UG.cT, Matrix.one_apply]
  · rw [Matrix.map_mul, Matrix.map_mul, map_snd_conj_transpose, map_snd_form, matrix_lift_snd]
    exact hg

def lift (g : HA R2 σ J) : HA (R1 × R2) σ J :=
  (⟨glift R1 R2 (HA.mat R2 σ J g), glift_mem R1 R2 σ J g⟩ : ↥(HR (R1 × R2) σ J))

def psiE : (Fin M → (R1 × R2) ⊗[F] E) ≃+ (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) where
  toFun x := (fun i => p1 R1 R2 (x i), fun i => p2 R1 R2 (x i))
  invFun y := fun i => qq R1 R2 (y.1 i) (y.2 i)
  left_inv x := funext fun i => qq_p R1 R2 (x i)
  right_inv y := Prod.ext (funext fun i => fst_pair R1 R2 _ _) (funext fun i => snd_pair R1 R2 _ _)
  map_add' x y := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp

theorem psi_lin (g : HA R2 σ J) (x : Fin M → (R1 × R2) ⊗[F] E) :
    psiE R1 R2 (lin (R1 × R2) σ J (lift R1 R2 σ J g) x) =
      ((psiE R1 R2 x).1, lin R2 σ J g (psiE R1 R2 x).2) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show p1 R1 R2 (Matrix.mulVec (mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) x i) = p1 R1 R2 (x i)
    rw [RingHom.map_mulVec, matrix_lift_fst, Matrix.one_mulVec]
    rfl
  · show p2 R1 R2 (Matrix.mulVec (mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) x i) =
      Matrix.mulVec (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) (fun k => p2 R1 R2 (x k)) i
    rw [RingHom.map_mulVec, matrix_lift_snd]
    rfl

end Ring

end PI.LevelKSplit.W.MVA
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCDefs
section
noncomputable section

namespace PI.LevelKSplit.W.NC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open PI.LevelKSplit.W.ExS PI.LevelKSplit.W.CD
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r)

theorem hR_add_right {r0 : ℕ} (P0 : Frame E M r0) (u x y : Fin M → R ⊗[F] E) : hR R σ J u (x + y) = hR R σ J u x + hR R σ J u y := by
  simp [hR, Formalism.UG.hform, mul_add, Finset.sum_add_distrib]

theorem hR_neg_right {r0 : ℕ} (P0 : Frame E M r0) (u x : Fin M → R ⊗[F] E) : hR R σ J u (-x) = -hR R σ J u x := by
  simp [hR, Formalism.UG.hform, mul_neg, Finset.sum_neg_distrib]

def Wp : AddSubgroup (Fin M → R ⊗[F] E) where
  carrier := {w | (∀ a, hR R σ J (ratV (F := F) R (P.e a)) w = 0) ∧
    (∀ a, hR R σ J (ratV (F := F) R (P.f a)) w = 0)}
  zero_mem' := by
    refine ⟨fun a => ?_, fun a => ?_⟩ <;> simp [hR, Formalism.UG.hform]
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hR_add_right R σ J P, hx1, hy1, add_zero]
    · rw [hR_add_right R σ J P, hx2, hy2, add_zero]
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hR_neg_right R σ J P, hx1, neg_zero]
    · rw [hR_neg_right R σ J P, hx2, neg_zero]

def pWp (x : Fin M → R ⊗[F] E) : Fin M → R ⊗[F] E :=
  x - ∑ a, hR R σ J (ratV (F := F) R (P.f a)) x • ratV (F := F) R (P.e a)
    - ∑ a, hR R σ J (ratV (F := F) R (P.e a)) x • ratV (F := F) R (P.f a)

def yH (g : HA R σ J) : Fin r → Fin M → R ⊗[F] E :=
  fun a => pWp R σ J P (lin R σ J g (ratV (F := F) R (P.f a)))

def FixXp : Subgroup (HA R σ J) where
  carrier := {g | ∀ v, InXperp R σ J P v → lin R σ J g v = v}
  one_mem' := fun v _ => lin_one R σ J v
  mul_mem' := by
    intro g h hg hh v hv
    simp only [Set.mem_ofPred_eq] at *
    rw [lin_mul, hh v hv, hg v hv]
  inv_mem' := by
    intro g hg v hv
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hg v hv]
    exact lin_inv_lin R σ J g v

def LevelUnipotentSubgroup : Subgroup (HA R σ J) := Nsub R σ J P ⊓ stabT R σ J P.e

def Zsub : Subgroup (HA R σ J) := Nsub R σ J P ⊓ FixXp R σ J P

end Gen

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def NCoord : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
  ∃ (A Z : Subgroup (HA (Af F) σ J))
    (Ψ : (A × ((Fin r → Wp (Af F) σ J P) × Z)) ≃ₜ Nsub (Af F) σ J P),
    IsClosed (A : Set (HA (Af F) σ J)) ∧ IsClosed (Z : Set (HA (Af F) σ J)) ∧
    (∀ n0 : Nsub (Af F) σ J P, ∃ (a0 : A) (t : A → (Fin r → Wp (Af F) σ J P))
      (c : A × (Fin r → Wp (Af F) σ J P) → Z),
      Continuous t ∧ Continuous c ∧ ∀ u y z, n0 * Ψ (u, y, z) = Ψ (a0 * u, y + t u, c (u, y) * z)) ∧
    ∀ h ∈ Hsub (Af F) σ J P, ∀ u y z, ∃ y' : Fin r → Wp (Af F) σ J P,
      (∀ a, (y' a : Fin M → Af F ⊗[F] E) = lin (Af F) σ J h (y a)) ∧
      h * (Ψ (u, y, z) : HA (Af F) σ J) * h⁻¹ = (Ψ (u, y', z) : HA (Af F) σ J)

def NCAsm : Prop := NCoord F E σ M J → ModV F E σ M J → ConjNH F E σ M J

end Ext

def NCoordAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => NCoord F E σ M J
def NCAsmAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => NCAsm F E σ M J

theorem conjNHAll_of (hC : NCoordAll) (hV : ModVAll) (hA : NCAsmAll) : ConjNHAll := by
  intro F E _ _ _ _ _ σ hCM M J hJ
  exact hA F E σ hCM M J hJ (hC F E σ hCM M J hJ) (hV F E σ hCM M J hJ)

theorem levelSAll_of_parts (hS : SemiNHSAll) (hC : NCoordAll) (hV : ModVAll) (hA : NCAsmAll) :
    PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.MeasAll.levelSAll_of_exist
    (PI.LevelKSplit.W.ExS.existSAll_of PI.VolSemiDirect.W.product_haar_measure_holds (fun _ _ _ => inferInstance) hS
      (conjNHAll_of hC hV hA))

end PI.LevelKSplit.W.NC
end
end

