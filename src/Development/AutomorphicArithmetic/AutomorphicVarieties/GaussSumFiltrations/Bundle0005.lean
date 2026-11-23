module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section
namespace GlobalTheory.HilbertThetaSeries.RatSlash

variable {F : Type} [Field F] [NumberField F]

theorem cmp_scalar_mul (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (v : InfinitePlace F) :
    cmp v (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.map (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v).toMonoidHom t) * cmp v h := by
  rw [map_mul]
  congr 1
  ext i j
  simp [cmp, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem det_scalar_mul (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) t * h : GL (Fin 2) (InfinitePlace F → ℝ)) :
      Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det =
      (t : InfinitePlace F → ℝ) ^ 2 * (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_mul]

theorem unit_ne (t : (InfinitePlace F → ℝ)ˣ) (v : InfinitePlace F) : (t : InfinitePlace F → ℝ) v ≠ 0 := fun h0 => by
  have := congrFun t.mul_inv v
  simp [h0] at this

theorem denom_scalar_mul (u : ℝˣ) (g : GL (Fin 2) ℝ) (z : ℂ) :
    UpperHalfPlane.denom (Matrix.GeneralLinearGroup.scalar (Fin 2) u * g) z = ((u : ℝ) : ℂ) * UpperHalfPlane.denom g z := by
  simp [UpperHalfPlane.denom, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem sl_scalar_mul {k : ℕ} (hk : Even k) (f : Hn F → ℂ) (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f := by
  obtain ⟨m, rfl⟩ := hk
  funext z
  have hact : act (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) z = act h z := by
    unfold act
    funext v
    rw [cmp_scalar_mul, mul_smul, UpperHalfPlane.glScalar_smul]
  have hdet : ∏ v, |((Matrix.GeneralLinearGroup.scalar (Fin 2) t * h : GL (Fin 2) (InfinitePlace F → ℝ)) :
      Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| =
      (∏ v, (t : InfinitePlace F → ℝ) v) ^ 2 * ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| := by
    rw [det_scalar_mul, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    simp [abs_mul, sq_abs]
  have hden : ∏ v, UpperHalfPlane.denom (cmp v (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h)) (z v) =
      ((∏ v, (t : InfinitePlace F → ℝ) v : ℝ) : ℂ) * ∏ v, UpperHalfPlane.denom (cmp v h) (z v) := by
    simp_rw [cmp_scalar_mul, denom_scalar_mul]
    rw [Finset.prod_mul_distrib]
    push_cast
    simp
  have hP : (∏ v, (t : InfinitePlace F → ℝ) v) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => unit_ne t v)
  have hQ : 0 ≤ ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| :=
    Finset.prod_nonneg (fun v _ => abs_nonneg _)
  have hexp : (((m + m : ℕ) : ℝ) / 2) = ((m : ℕ) : ℝ) := by
    push_cast
    ring
  unfold sl sl0
  rw [hact, hdet, hden, Real.mul_rpow (by positivity) hQ, hexp, Real.rpow_natCast, ← pow_mul]
  set P := ∏ v, (t : InfinitePlace F → ℝ) v
  have hPC : (P : ℂ) ≠ 0 := by exact_mod_cast hP
  push_cast
  rw [mul_inv, mul_pow, inv_pow (P : ℂ)]
  field_simp
  ring

variable [IsTotallyReal F]

theorem ofReal_rhom (v : InfinitePlace F) (x : F) : ((rhom x v : ℝ) : ℂ) = v.embedding x :=
  InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x

theorem rhom_apply (v : InfinitePlace F) (x : F) : rhom x v = reAt v x := by
  unfold rhom reAt
  show InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x = (v.embedding x).re
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]

theorem ofReal_reAt (v : InfinitePlace F) (x : F) : ((reAt v x : ℝ) : ℂ) = v.embedding x := by
  rw [← rhom_apply, ofReal_rhom]


variable (F) in
def embEquiv : InfinitePlace F ≃ (F →+* ℂ) where
  toFun v := v.embedding
  invFun φ := InfinitePlace.mk φ
  left_inv v := InfinitePlace.mk_embedding v
  right_inv φ := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))

theorem prod_reAt (x : F) : ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [ofReal_reAt]
  have h1 : ∏ v : InfinitePlace F, v.embedding x = ∏ φ : F →+* ℂ, φ x :=
    Equiv.prod_comp (embEquiv F) (fun φ => φ x)
  have h2 : ∏ φ : F →+* ℂ, φ x = ∏ σ : F →ₐ[ℚ] ℂ, σ x :=
    Equiv.prod_comp (RingHom.equivRatAlgHom F ℂ) (fun σ : F →ₐ[ℚ] ℂ => σ x)
  rw [h1, h2, ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast]

theorem sum_reAt (x : F) : ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [ofReal_reAt]
  have h1 : ∑ v : InfinitePlace F, v.embedding x = ∑ φ : F →+* ℂ, φ x :=
    Equiv.sum_comp (embEquiv F) (fun φ => φ x)
  have h2 : ∑ φ : F →+* ℂ, φ x = ∑ σ : F →ₐ[ℚ] ℂ, σ x :=
    Equiv.sum_comp (RingHom.equivRatAlgHom F ℂ) (fun σ : F →ₐ[ℚ] ℂ => σ x)
  rw [h1, h2, ← trace_eq_sum_embeddings ℂ, eq_ratCast]

theorem det_toInf (γ : GL (Fin 2) F) :
    ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det = rhom γ.val.det := by
  rw [RingHom.map_det]; rfl

theorem toInf_scalar (η : Fˣ) : toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η) := by
  ext i j v
  simp [toInf, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem rat_slash : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ), (∀ v (x : F), rhom x v = reAt v x) ∧ (∀ γ : GL (Fin 2) F, (Pos (toInf γ) ↔ TP γ.val.det) ∧ sl k (toInf γ) f = ((|((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)| ^ ((k : ℝ) / 2) : ℝ) : ℂ) • sl0 k (toInf γ) f) ∧ (Even k → ∀ (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)), Pos h → Pos (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) ∧ sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f) ∧ (∀ η : Fˣ, toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η)) ∧ ∀ x : F, ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) ∧ ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  intro F _ _ _ k f
  refine ⟨rhom_apply, fun γ => ⟨?_, ?_⟩, fun hk t h hh => ⟨?_, sl_scalar_mul hk f t h⟩, toInf_scalar,
    fun x => ⟨prod_reAt x, sum_reAt x⟩⟩
  · unfold Pos TP
    rw [det_toInf]
    simp only [rhom_apply]
  · funext z
    unfold sl
    rw [det_toInf]
    simp only [rhom_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.abs_prod, prod_reAt]
  · unfold Pos at hh ⊢
    intro v
    rw [det_scalar_mul]
    have h1 := unit_ne t v
    have h2 := hh v
    simp only [Pi.mul_apply, Pi.pow_apply]
    positivity

end GlobalTheory.HilbertThetaSeries.RatSlash

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_slash_rational_matrix_properties : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ), (∀ v (x : F), rhom x v = reAt v x) ∧ (∀ γ : GL (Fin 2) F, (Pos (toInf γ) ↔ TP γ.val.det) ∧ sl k (toInf γ) f = ((|((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)| ^ ((k : ℝ) / 2) : ℝ) : ℂ) • sl0 k (toInf γ) f) ∧ (Even k → ∀ (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)), Pos h → Pos (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) ∧ sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f) ∧ (∀ η : Fˣ, toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η)) ∧ ∀ x : F, ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) ∧ ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash | exact GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash | (intros; apply GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntMatrixIsometryPrimeOrderLatticeStability
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.IsoP

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem pow_eq_one {p : ℕ} {S : Matrix κ κ ℤ} (h : ∑ i ∈ Finset.range p, S ^ i = 0) : S ^ p = 1 := by
  have := geom_sum_mul S p
  rw [h, zero_mul] at this
  exact (sub_eq_zero.mp this.symm)

theorem map_pow_eq (S : Matrix κ κ ℤ) (n : ℕ) : (S.map (Int.cast : ℤ → F)) ^ n = (S ^ n).map (Int.cast : ℤ → F) := by
  show ((Int.castRingHom F).mapMatrix S) ^ n = (Int.castRingHom F).mapMatrix (S ^ n)
  rw [map_pow]

theorem iter_eq (A : Matrix κ κ F) (n : ℕ) (x : κ → F) : (fun x => A *ᵥ x)^[n] x = (A ^ n) *ᵥ x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', Matrix.mulVec_mulVec]

theorem mem_LL (x : κ → F) : x ∈ LL F κ ↔ ∀ i, x i ∈ integralClosure ℤ F := by
  simp [LL, AddSubgroup.mem_pi]

theorem mulVec_LL (M : Matrix κ κ ℤ) {x : κ → F} (hx : x ∈ LL F κ) : (M.map (Int.cast : ℤ → F)) *ᵥ x ∈ LL F κ := by
  rw [mem_LL] at hx ⊢
  intro i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (hx j)

theorem mulVec_aL (M : Matrix κ κ ℤ) (a : F) {x : κ → F} (hx : x ∈ aL κ a) : (M.map (Int.cast : ℤ → F)) *ᵥ x ∈ aL κ a := by
  simp only [aL, AddSubgroup.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨_, mulVec_LL M hy, ?_⟩
  simp [Matrix.mulVec_smul]

theorem pow_mulVec_fix (A : Matrix κ κ F) {x : κ → F} (hx : A *ᵥ x = x) (n : ℕ) : (A ^ n) *ᵥ x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hx, ih]

theorem prime_not_dvd_of_neg_one_pow_mul_modEq_one {p : ℕ} (hp : p.Prime) {t : ℕ} {k : ℕ} (h : (-1) ^ k * (t : ℤ) ≡ 1 [ZMOD p]) : ¬ (p : ℤ) ∣ t := by
  intro hd
  have h2 := Int.modEq_iff_dvd.mp h
  have h3 : (p : ℤ) ∣ 1 := by
    have h4 := dvd_add h2 (dvd_mul_of_dvd_right hd ((-1) ^ k))
    simpa using h4
  have h5 : p ∣ 1 := by exact_mod_cast h3
  exact hp.not_dvd_one h5

private theorem sum_pow_map_intCast_eq_zero {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {p : ℕ} {S : Matrix κ κ ℤ} (cyc : ∑ i ∈ Finset.range p, S ^ i = 0) :
    ∑ i ∈ Finset.range p, (S.map (Int.cast : ℤ → F)) ^ i = 0 := by
  simp only [map_pow_eq]
  have e := congrArg (Int.castRingHom F).mapMatrix cyc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at e
  exact e

theorem isometry_order_p : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → (∀ x y : κ → F, BF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) ((S.map (Int.cast : ℤ → F)) *ᵥ y) = BF G x y ∧ QF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) = QF G x) ∧ (∀ x : κ → F, (fun x => (S.map (Int.cast : ℤ → F)) *ᵥ x)^[p] x = x ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x = x → x = 0) ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ dualL F G ↔ x ∈ dualL F G) ∧ ∀ a : F, ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ aL κ a ↔ x ∈ aL κ a)) ∧ (∀ (N : ℕ) (x : κ → F), 0 < N → N.Coprime p → x ∈ aL κ (N : F)⁻¹ → (S.map (Int.cast : ℤ → F)) *ᵥ x - x ∈ aL κ (N : F) → x ∈ aL κ (N : F)) ∧ ¬ (p : ℤ) ∣ t := by
  intro F _ _ p hp κ _ _ G S t hL
  obtain ⟨_, _, iso, cyc, _, cong⟩ := hL
  have hφ : ∀ M : Matrix κ κ ℤ, M.map (Int.cast : ℤ → F) = (Int.castRingHom F).mapMatrix M := fun _ => rfl
  have hsum0 := sum_pow_map_intCast_eq_zero (F := F) cyc
  set S' : Matrix κ κ F := S.map (Int.cast : ℤ → F) with hS'
  have hpow : S' ^ p = 1 := by
    rw [hS', map_pow_eq, pow_eq_one cyc]
    simp
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  have hinv : ∀ y : κ → F, S' *ᵥ ((S ^ (p - 1)).map (Int.cast : ℤ → F) *ᵥ y) = y := by
    intro y
    rw [← map_pow_eq, Matrix.mulVec_mulVec, ← pow_succ', hp1, hpow, Matrix.one_mulVec]
  have hinv' : ∀ y : κ → F, (S ^ (p - 1)).map (Int.cast : ℤ → F) *ᵥ (S' *ᵥ y) = y := by
    intro y
    rw [← map_pow_eq, Matrix.mulVec_mulVec, ← pow_succ, hp1, hpow, Matrix.one_mulVec]
  have hsum : ∑ i ∈ Finset.range p, S' ^ i = 0 := hsum0
  have hBF : ∀ x y : κ → F, BF G (S' *ᵥ x) (S' *ᵥ y) = BF G x y := by
    intro x y
    have key : S'ᵀ * G.map (Int.cast : ℤ → F) * S' = G.map (Int.cast : ℤ → F) := by
      rw [hS', ← Matrix.transpose_map]
      simp only [hφ]
      rw [← map_mul, ← map_mul, iso]
    unfold BF
    rw [← Matrix.vecMul_transpose S' x, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, key]
  have memD : ∀ y : κ → F, y ∈ dualL F G ↔ ∀ l ∈ LL F κ, ∃ n : ℤ, Algebra.trace ℚ F (BF G y l) = n :=
    fun _ => Iff.rfl
  refine ⟨fun x y => ⟨hBF x y, ?_⟩, fun x => ⟨?_, ?_, ?_, ?_⟩, ?_, prime_not_dvd_of_neg_one_pow_mul_modEq_one hp cong⟩
  · unfold QF
    rw [hBF]
  · rw [iter_eq, hpow, Matrix.one_mulVec]
  · intro hx
    have e : ∑ i ∈ Finset.range p, S' ^ i *ᵥ x = 0 := by
      rw [← Matrix.sum_mulVec, hsum, Matrix.zero_mulVec]
    simp only [pow_mulVec_fix S' hx, Finset.sum_const, Finset.card_range] at e
    rw [← Nat.cast_smul_eq_nsmul F] at e
    have hp0 : (p : F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    exact (smul_eq_zero.mp e).resolve_left hp0
  · rw [memD, memD]
    constructor
    · intro h l hl
      have h' := h _ (mulVec_LL S hl)
      rwa [hBF] at h'
    · intro h l hl
      have h' := h _ (mulVec_LL (S ^ (p - 1)) hl)
      rwa [← hBF, hinv] at h'
  · intro a
    constructor
    · intro h
      have h' := mulVec_aL (S ^ (p - 1)) a h
      rwa [hinv'] at h'
    · intro h
      exact mulVec_aL S a h
  · intro N x hN hcop hx hz
    have hstep : ∀ i : ℕ, S' ^ i *ᵥ x - x ∈ aL κ (N : F) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have e : S' ^ (i + 1) *ᵥ x - x = S' *ᵥ (S' ^ i *ᵥ x - x) + (S' *ᵥ x - x) := by
          rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
          abel
        rw [e]
        exact add_mem (mulVec_aL S _ ih) hz
    have hpx : (p : F) • x ∈ aL κ (N : F) := by
      have h0 : ∑ i ∈ Finset.range p, (S' ^ i *ᵥ x - x) = -((p : F) • x) := by
        rw [Finset.sum_sub_distrib, ← Matrix.sum_mulVec, hsum, Matrix.zero_mulVec, Finset.sum_const,
          Finset.card_range, zero_sub, Nat.cast_smul_eq_nsmul]
      have hs := AddSubgroup.sum_mem (aL κ (N : F)) (t := Finset.range p) (fun i _ => hstep i)
      rw [h0] at hs
      exact neg_mem_iff.mp hs
    have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hNx : (N : F) ^ 2 • x ∈ aL κ (N : F) := by
      simp only [aL, AddSubgroup.mem_map] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y, hy, ?_⟩
      simp only [DistribSMul.toAddMonoidHom_apply, smul_smul]
      rw [pow_two, mul_assoc, mul_inv_cancel₀ hN0, mul_one]
    obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) ((N : ℤ) ^ 2) := by
      have hc : Nat.Coprime p (N ^ 2) := Nat.Coprime.pow_right 2 hcop.symm
      exact_mod_cast Nat.isCoprime_iff_coprime.mpr hc
    have hx' : x = u • ((p : F) • x) + v • ((N : F) ^ 2 • x) := by
      rw [← Int.cast_smul_eq_zsmul F, ← Int.cast_smul_eq_zsmul F, smul_smul, smul_smul, ← add_smul]
      have e : (u : F) * p + (v : F) * (N : F) ^ 2 = 1 := by exact_mod_cast huv
      rw [e, one_smul]
    rw [hx']
    exact add_mem (zsmul_mem hpx u) (zsmul_mem hNx v)

end GlobalTheory.HilbertThetaSeries.IsoP

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intMatrix_isometry_prime_order_lattice_stability : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → (∀ x y : κ → F, BF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) ((S.map (Int.cast : ℤ → F)) *ᵥ y) = BF G x y ∧ QF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) = QF G x) ∧ (∀ x : κ → F, (fun x => (S.map (Int.cast : ℤ → F)) *ᵥ x)^[p] x = x ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x = x → x = 0) ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ dualL F G ↔ x ∈ dualL F G) ∧ ∀ a : F, ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ aL κ a ↔ x ∈ aL κ a)) ∧ (∀ (N : ℕ) (x : κ → F), 0 < N → N.Coprime p → x ∈ aL κ (N : F)⁻¹ → (S.map (Int.cast : ℤ → F)) *ᵥ x - x ∈ aL κ (N : F) → x ∈ aL κ (N : F)) ∧ ¬ (p : ℤ) ∣ t := by
  first | exact @GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p | exact GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p | (intros; apply GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IsDelNeZeroCoprimeDenominatorsDifferentGenerator
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HilbertThetaSeries.DenP
variable {F : Type} [Field F] [NumberField F]

theorem val_nat (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) : w.valuation F (n : F) = w.intValuation (n : 𝓞 F) := by
  rw [← map_natCast (algebraMap (𝓞 F) F) n, HeightOneSpectrum.valuation_of_algebraMap]

theorem isIntegral_iff_val (x : F) : IsIntegral ℤ x ↔ ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1 := by
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · have := w.valuation_le_one (K := F) (⟨x, h⟩ : 𝓞 F)
    exact this
  · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x h
    rw [← hr]; exact RingOfIntegers.isIntegral_coe r

theorem not_mem_of_coprime {p N : ℕ} (hc : N.Coprime p) {w : HeightOneSpectrum (𝓞 F)}
    (hp : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) : ((N : ℕ) : 𝓞 F) ∉ w.asIdeal := by
  intro hN
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  have h1 : ((u : 𝓞 F) * (N : 𝓞 F) + (v : 𝓞 F) * (p : 𝓞 F)) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 F) huv
    push_cast at this
    exact this
  have : (1 : 𝓞 F) ∈ w.asIdeal := by
    rw [← h1]; exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hN) (w.asIdeal.mul_mem_left _ hp)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem val_coprime {p N : ℕ} (hc : N.Coprime p) {w : HeightOneSpectrum (𝓞 F)}
    (hp : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) : w.valuation F (N : F) = 1 := by
  rw [val_nat]; exact HeightOneSpectrum.intValuation_eq_one_iff.2 (not_mem_of_coprime hc hp)

theorem val_ordCompl {p : ℕ} (n : ℕ) {w : HeightOneSpectrum (𝓞 F)} (hp : ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    w.valuation F ((n / p ^ n.factorization p : ℕ) : F) = w.valuation F (n : F) := by
  conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  rw [Nat.cast_mul, map_mul, Nat.cast_pow, map_pow, val_nat w p, HeightOneSpectrum.intValuation_eq_one_iff.2 hp,
    one_pow, one_mul]

theorem exists_nat_mul (x : F) : ∃ D : ℕ, D ≠ 0 ∧ IsIntegral ℤ ((D : F) * x) := by
  have ha : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)
  obtain ⟨y, hy0, hy⟩ := ha.exists_integral_multiple
  rw [zsmul_eq_mul] at hy
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · exact ⟨n, by simpa using hy0, by simpa using hy⟩
  · exact ⟨n, by simpa using hy0, by simpa using hy.neg⟩

theorem exists_away {p : ℕ} (hp : p.Prime) (x : F) : ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧
    ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → w.valuation F ((N : F) * x) ≤ 1 := by
  obtain ⟨D, hD0, hD⟩ := exists_nat_mul x
  refine ⟨D / p ^ D.factorization p, Nat.ordCompl_pos p hD0, (Nat.coprime_ordCompl hp hD0).symm, fun w hw => ?_⟩
  rw [map_mul, val_ordCompl D hw, ← map_mul]
  exact (isIntegral_iff_val _).1 hD w

theorem exists_place {p : ℕ} (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have hne : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 := hu.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [← map_natCast (algebraMap ℤ (𝓞 F)) p, Algebra.norm_algebraMap,
      isUnit_pow_iff (Module.finrank_pos (R := ℤ) (M := 𝓞 F)).ne'] at h1
    exact (Nat.prime_iff_prime_int.1 hp).not_unit h1
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((p : ℕ) : 𝓞 F) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hp.ne_zero (by simpa using hmem)

theorem diff_ne : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot

theorem coe_diff_ne : (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 diff_ne

theorem count_diff (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) :=
  FractionalIdeal.count_coe F w diff_ne

theorem mem_diff_iff (x : F) : x ∈ (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ↔
    ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ WithZero.exp (-(ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)) := by
  rw [GlobalTheory.Idele.mem_iff_valuation_le coe_diff_ne]
  simp only [count_diff]

theorem trace_int {y : F} (h : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F y ≤ WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)))
    {x : F} (hx : IsIntegral ℤ x) : ∃ n : ℤ, Algebra.trace ℚ F (y * x) = n := by
  have h1 : y ∈ (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    rw [GlobalTheory.Idele.mem_iff_valuation_le (inv_ne_zero coe_diff_ne)]
    intro w
    rw [FractionalIdeal.count_inv, count_diff, neg_neg]
    exact h w
  rw [coeIdeal_differentIdeal ℤ ℚ F (𝓞 F), inv_inv, FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (𝓞 F)⁰ F))] at h1
  obtain ⟨n, hn⟩ := h1 x ((FractionalIdeal.mem_one_iff _).2 ⟨⟨x, hx⟩, rfl⟩)
  exact ⟨n, by rw [← Algebra.traceForm_apply, ← hn]; simp⟩

end GlobalTheory.HilbertThetaSeries.DenP


open GlobalTheory.HilbertThetaSeries.DenP in
theorem GlobalTheory.HilbertThetaSeries.denominators_prime_to : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → δ ≠ 0 ∧ (∀ x : F, PInt p x → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ IsIntegral ℤ ((N : F) * x)) ∧ (∀ b : F, PInt p (δ * b) → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ ∀ x : F, IsIntegral ℤ x → ∃ n : ℤ, Algebra.trace ℚ F ((N : F) * b * x) = n) ∧ ∃ (d : 𝓞 F) (N : ℕ), d ∈ differentIdeal ℤ (𝓞 F) ∧ N.Coprime p ∧ 0 < N ∧ PUnit p ((d : F) / δ) := by
  intro F _ _ p hp δ hδ
  have h0 : δ ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_place (F := F) hp
    rintro rfl
    have := hδ w hw
    rw [map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  refine ⟨h0, fun x hx => ?_, fun b hb => ?_, ?_⟩
  · obtain ⟨N, hN0, hNc, hN⟩ := exists_away hp x
    refine ⟨N, hN0, hNc, (isIntegral_iff_val _).2 fun w => ?_⟩
    by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [map_mul, val_coprime hNc hw, one_mul]; exact hx w hw
    · exact hN w hw
  · obtain ⟨N, hN0, hNc, hN⟩ := exists_away hp b
    refine ⟨N, hN0, hNc, fun x hx => trace_int (fun w => ?_) hx⟩
    by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [map_mul, val_coprime hNc hw, one_mul]
      have h1 := hb w hw
      rw [map_mul, hδ w hw, WithZero.exp_neg, inv_mul_le_iff₀ WithZero.exp_pos, mul_one] at h1
      exact h1
    · refine (hN w hw).trans ?_
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      positivity
  · obtain ⟨N, hN0, hNc, hN⟩ := exists_away hp δ
    set c : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 F)) with hc
    have hc0 : c ≠ 0 := fun h => diff_ne (Ideal.absNorm_eq_zero_iff.1 h)
    have hcm : (c : F) ∈ (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨c, Ideal.absNorm_mem _, map_natCast _ _⟩
    have hcc : (c / p ^ c.factorization p).Coprime p := (Nat.coprime_ordCompl hp hc0).symm
    have hm : ((c / p ^ c.factorization p : ℕ) : F) * ((N : F) * δ) ∈ (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [mem_diff_iff]
      intro w
      by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
      · rw [map_mul, map_mul, val_coprime hNc hw, val_coprime hcc hw, one_mul, one_mul, hδ w hw]
      · rw [map_mul, val_ordCompl c hw]
        simpa using mul_le_mul' ((mem_diff_iff _).1 hcm w) (hN w hw)
    obtain ⟨d, hd, hd'⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
    refine ⟨d, 1, hd, Nat.coprime_one_left p, one_pos, fun w hw => ?_⟩
    have : (d : F) / δ = ((c / p ^ c.factorization p : ℕ) : F) * (N : F) := by
      rw [div_eq_iff h0, mul_assoc]; exact hd'
    rw [this, map_mul, val_coprime hNc hw, val_coprime hcc hw, one_mul]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDel_ne_zero_coprime_denominators_different_generator : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → δ ≠ 0 ∧ (∀ x : F, PInt p x → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ IsIntegral ℤ ((N : F) * x)) ∧ (∀ b : F, PInt p (δ * b) → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ ∀ x : F, IsIntegral ℤ x → ∃ n : ℤ, Algebra.trace ℚ F ((N : F) * b * x) = n) ∧ ∃ (d : 𝓞 F) (N : ℕ), d ∈ differentIdeal ℤ (𝓞 F) ∧ N.Coprime p ∧ 0 < N ∧ PUnit p ((d : F) / δ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.denominators_prime_to | exact GlobalTheory.HilbertThetaSeries.denominators_prime_to | (intros; apply GlobalTheory.HilbertThetaSeries.denominators_prime_to <;> assumption)
end

