module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
public import Mathlib
public import Lemmata.B110.ExistsMoved
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.DjCurveA
section
open Matrix

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.DjC

section Gen

variable {N j : ℕ}

def Pres (S : Set (Fin N)) (Y : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ c b : Fin N, b ∈ S → c ∉ S → Y c b = 0

theorem pres_mul {S : Set (Fin N)} {X Y : Matrix (Fin N) (Fin N) ℂ} (hX : Pres S X) (hY : Pres S Y) :
    Pres S (X * Y) := by
  intro c b hb hc
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m ∈ S
  · rw [hX c m hm hc, zero_mul]
  · rw [hY m b hb hm, mul_zero]

theorem pres_pow {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) (n : ℕ) :
    Pres S (Y ^ n) := by
  induction n with
  | zero =>
    intro c b hb hc
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl; exact hc hb
  | succ n ih => rw [pow_succ]; exact pres_mul ih hY

theorem pres_smul {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) (z : ℂ) :
    Pres S (z • Y) := by
  intro c b hb hc
  rw [Matrix.smul_apply, hY c b hb hc, smul_zero]

theorem pres_neg {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) : Pres S (-Y) := by
  intro c b hb hc
  rw [Matrix.neg_apply, hY c b hb hc, neg_zero]

open scoped Matrix.Norms.Operator in
theorem pres_exp {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) :
    Pres S (NormedSpace.exp Y) := by
  intro c b hb hc
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h1 := Pi.hasSum.1 h c
  have h2 := Pi.hasSum.1 h1 b
  have h3 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • Y ^ n) c b) 0 := by
    have : (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • Y ^ n) c b) = fun _ => 0 := by
      funext n; rw [Matrix.smul_apply, pres_pow hY n c b hb hc, smul_zero]
    rw [this]; exact hasSum_zero
  exact h2.unique h3

def sub (e : Fin j ↪ Fin N) (E : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => E (e a) (e b)

end Gen

section DetExp

variable {n : Type} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry (X : Matrix n n ℂ) (i j : n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix n n ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_det_of_one (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  first | exact Bl.b110.goal1 .. | (apply Bl.b110.goal1 <;> assumption) | (intros; apply Bl.b110.goal1 <;> assumption) | (apply @Bl.b110.goal1 <;> assumption) | (intros; apply @Bl.b110.goal1 <;> assumption) | (apply @Bl.b110.goal1 <;> first | assumption | infer_instance) | exact @Bl.b110.goal1 n ‹_› ‹_› A A' h0 h | exact @Bl.b110.goal1 n ‹_› ‹_› A A' h0 | exact @Bl.b110.goal1 n ‹_› ‹_› A A' | exact @Bl.b110.goal1 n ‹_› ‹_› A | exact @Bl.b110.goal1 n ‹_› ‹_› | exact @Bl.b110.goal1 n ‹_› | exact @Bl.b110.goal1 n

end DetExp

theorem mul_hom_exp (φ : ℝ → ℂ) (c : ℂ) (hmul : ∀ s t, φ (s + t) = φ s * φ t) (h1 : φ 0 = 1)
    (h0 : HasDerivAt φ c 0) (t : ℝ) : φ t = Complex.exp (t * c) := by
  have hd : ∀ t, HasDerivAt φ (φ t * c) t := by
    intro t
    have h1' : HasDerivAt (fun s => φ (s - t)) c t := by
      have h00 := h0
      rw [← sub_self t] at h00
      exact h00.comp_sub_const t t
    have h2 := h1'.const_mul (φ t)
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show φ s = φ t * φ (s - t)
    rw [← hmul]; congr 1; ring
  let ψ : ℝ → ℂ := fun t => φ t * Complex.exp (-((t : ℂ) * c))
  have hψ : ∀ t, HasDerivAt ψ 0 t := by
    intro t
    have e0 : HasDerivAt (fun t : ℝ => -((t : ℂ) * c)) (-(1 * c)) t := by
      have h := ((hasDerivAt_id t).ofReal_comp.mul_const c).fun_neg
      simpa using h
    have e1 := e0.cexp
    have h3 := (hd t).fun_mul e1
    have h4 : φ t * c * Complex.exp (-((t : ℂ) * c)) +
        φ t * (Complex.exp (-((t : ℂ) * c)) * -(1 * c)) = 0 := by ring
    rw [h4] at h3
    exact h3
  have hc := is_const_of_deriv_eq_zero (fun t => (hψ t).differentiableAt) (fun t => (hψ t).deriv) t 0
  simp only [ψ, h1, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [Complex.exp_neg] at hc
  exact eq_of_mul_inv_eq_one hc

end PI.UnitaryCorollaryDerivatives.DjC
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.DjPoly
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def djVarMat (k j ρ : ℕ) :
    Matrix (Fin j) (Fin j)
      (MvPolynomial ((Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1)) ⊕
        (Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1))) ℂ) :=
  fun a b => MvPolynomial.X (Sum.inl (⟨2 * (j + ρ) + k - a.val, by omega⟩, ⟨b.val, by omega⟩))

theorem isPolyDeg_determinant_derivative (k j ρ : ℕ) : IsPolyDeg j (DjU k j ρ) := by
  refine ⟨∑ σ : Equiv.Perm (Fin j),
      MvPolynomial.C ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) * ∏ i, djVarMat k j ρ (σ i) i, ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    refine Finset.sup_le fun σ _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc (∑ i : Fin j, (djVarMat k j ρ (σ i) i).totalDegree) ≤ ∑ _i : Fin j, 1 := by
          refine Finset.sum_le_sum fun i _ => ?_
          simp [djVarMat, MvPolynomial.totalDegree_X]
      _ = j := by simp
  · intro g
    rw [DjU, Matrix.det_apply']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_prod, MvPolynomial.eval_C]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [djVarMat, Zh, MvPolynomial.eval_X]

theorem determinant_derivative_polynomial : DjPoly := fun k j ρ => isPolyDeg_determinant_derivative k j ρ

end PI.UnitaryCorollaryDerivatives
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.GfPolyA
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

variable {N : ℕ}

theorem pd_mono {a b : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : a ≤ b) (hP : IsPolyDeg a P) :
    IsPolyDeg b P := by
  obtain ⟨q, hq, he⟩ := hP
  exact ⟨q, hq.trans h, he⟩

theorem pd_const (c : ℂ) : IsPolyDeg (N := N) 0 (fun _ => c) :=
  ⟨MvPolynomial.C c, by simp, fun g => by simp⟩

theorem pd_add {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) (hQ : IsPolyDeg a Q) :
    IsPolyDeg a (fun g => P g + Q g) := by
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨q, hq, hqe⟩ := hQ
  exact ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => by simp [hpe, hqe]⟩

theorem pd_sub {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) (hQ : IsPolyDeg a Q) :
    IsPolyDeg a (fun g => P g - Q g) := by
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨q, hq, hqe⟩ := hQ
  exact ⟨p - q, (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq), fun g => by simp [hpe, hqe]⟩

theorem pd_mul {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) (hQ : IsPolyDeg b Q) :
    IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨q, hq, hqe⟩ := hQ
  exact ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (add_le_add hp hq), fun g => by simp [hpe, hqe]⟩

theorem pd_cmul {a : ℕ} (c : ℂ) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) :
    IsPolyDeg a (fun g => c * P g) := by
  have h := pd_mul (pd_const c) hP
  rwa [zero_add] at h

theorem pd_mulc {a : ℕ} (c : ℂ) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) :
    IsPolyDeg a (fun g => P g * c) := by
  have h := pd_mul hP (pd_const c)
  rwa [add_zero] at h

theorem pd_sum {ι : Type*} (s : Finset ι) {a : ℕ} (P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ)
    (h : ∀ i ∈ s, IsPolyDeg a (P i)) : IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact pd_mono (Nat.zero_le a) (pd_const 0)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact pd_add (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem pd_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) (P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ)
    (h : ∀ i ∈ s, IsPolyDeg (d i) (P i)) : IsPolyDeg (∑ i ∈ s, d i) (fun g => ∏ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact pd_const 1
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact pd_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem pd_X (a b : Fin N) : IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => g a b) :=
  ⟨MvPolynomial.X (Sum.inl (a, b)), by simp [MvPolynomial.totalDegree_X], fun g => by simp⟩

theorem pd_Xs (a b : Fin N) : IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g a b)) :=
  ⟨MvPolynomial.X (Sum.inr (a, b)), by simp [MvPolynomial.totalDegree_X], fun g => by simp⟩

theorem pd_det (n : ℕ) (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j, IsPolyDeg 1 (fun g => M g i j)) : IsPolyDeg n (fun g => (M g).det) := by
  simp only [Matrix.det_apply']
  refine pd_sum _ _ fun σ _ => pd_cmul _ ?_
  have h2 := pd_prod (Finset.univ : Finset (Fin n)) (fun _ => 1) (fun i g => M g (σ i) i)
    (fun i _ => h (σ i) i)
  simpa using h2

theorem pd_det_star (n : ℕ) (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j, IsPolyDeg 1 (fun g => star (M g i j))) : IsPolyDeg n (fun g => star (M g).det) := by
  have e : (fun g => star (M g).det) = fun g => ((M g).map (starRingEnd ℂ)).det := by
    funext g
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, starRingEnd_apply]
  rw [e]
  exact pd_det n _ fun i j => h i j

theorem pd_herm (H : Matrix (Fin N) (Fin N) ℂ) (v w : Fin N → ℂ) :
    IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => herm H (g *ᵥ v) w) := by
  simp only [herm, dotProduct, mulVec]
  exact pd_sum _ _ fun i _ => pd_cmul _ (pd_sum _ _ fun j _ => pd_cmul _
    (pd_sum _ _ fun l _ => pd_mulc _ (pd_X j l)))

theorem pd_herm_star (H : Matrix (Fin N) (Fin N) ℂ) (v w : Fin N → ℂ) :
    IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (herm H (g *ᵥ v) w)) := by
  simp only [herm, dotProduct, mulVec, star_sum, star_mul']
  exact pd_sum _ _ fun i _ => pd_cmul _ (pd_sum _ _ fun j _ => pd_cmul _
    (pd_sum _ _ fun l _ => isPolyDeg_one_conj_entry_mul j l))
where
  isPolyDeg_one_conj_entry_mul (j l : Fin N) : IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g j l) * star (v l)) :=
    pd_mulc _ (pd_Xs j l)

end PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.GfWBOf
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem gfWB_of (h1 : GfPoly) (h2 : PolyB) (h3 : CompR) : GfWB := by
  intro k r z z' χε ε n hχ
  obtain ⟨hχs, hχd, -⟩ := hχ
  obtain ⟨hsmC, hwb⟩ :=
    h2 k r (2 * (r + 1)) (fun g => ((Gf k r z z' g : ℝ) : ℂ)) (h1 k r z z')
  have hsmR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => Gf k r z z' g) := by
    have h := Complex.reCLM.contDiff.comp hsmC
    simpa [Function.comp_def] using h
  refine ⟨?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (hχs.comp hsmR)
  · obtain ⟨C₀, hC₀⟩ := hwb n
    refine h3 k r (fun g => Gf k r z z' g) χε (fun _ => 2 * (r + 1)) n C₀ hsmR hχs hχd ?_
    intro u v hu hv hlen hne g hg
    have hb := hC₀ u v hu hv hlen g hg
    have h1g : 1 ≤ B.gN g := gN_ge_one hg
    have hexp : ((2 * (r + 1) : ℕ) : ℝ) + ((((u ++ v).map (fun _ => (0 : ℕ))).sum : ℕ) : ℝ) ≤
        ((((u ++ v).map (fun _ => 2 * (r + 1))).sum : ℕ) : ℝ) := by
      have hl : 1 ≤ (u ++ v).length := List.length_pos_iff.mpr hne
      simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_zero, Nat.cast_zero,
        add_zero]
      exact_mod_cast Nat.le_mul_of_pos_left _ hl
    have hpos : 0 < B.gN g ^ (((2 * (r + 1) : ℕ) : ℝ) +
        ((((u ++ v).map (fun _ => (0 : ℕ))).sum : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos h1g) _
    have hC : 0 ≤ C₀ := (mul_nonneg_iff_of_pos_right hpos).mp ((norm_nonneg _).trans hb)
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1g hexp) hC)

end PI.UnitaryCorollaryDerivatives
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.MxLeOne
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem mx_le_one {k r : ℕ} {X : B.Mat k r} (h : B.unitLie k r X) : mx X ≤ 1 := by
  show ‖Matrix.of.symm X‖ ≤ 1
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  exact h.2 i j

theorem dw_dj (h1 : DjCurve) (k j ρ : ℕ) : ∀ w : List (Bool × B.Mat k (j + ρ)),
    (∀ x ∈ w, inLieP k j ρ x.2 ∧ mx x.2 ≤ 1) →
    ∃ K : ℂ, ‖K‖ ≤ (j : ℝ) ^ w.length ∧ ∀ g, Dw w (DjU k j ρ) g = K * DjU k j ρ g := by
  intro w
  induction w with
  | nil => intro _; exact ⟨1, by simp, fun g => by simp [Dw]⟩
  | cons x w ih =>
    intro hw
    obtain ⟨K, hK, hD⟩ := ih fun y hy => hw y (by simp [hy])
    obtain ⟨hxP, hxm⟩ := hw x (by simp)
    obtain ⟨c₁, c₂, hc₁, hc₂, hcur⟩ := h1 k j ρ x.2 hxP
    have hderiv : ∀ (c D : ℂ), HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c) * D) (c * D) 0 := by
      intro c D
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * c) (1 * c) 0 :=
        (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const c
      have := (h0.cexp).mul_const D
      simpa using this
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    obtain ⟨b, X⟩ := x
    cases b
    · refine ⟨c₁ * K, ?_, fun g => ?_⟩
      · rw [norm_mul, List.length_cons, pow_succ']
        exact mul_le_mul (hc₁.trans (mul_le_of_le_one_right hj hxm)) hK (norm_nonneg _) hj
      · have e : Dw ((false, X) :: w) (DjU k j ρ) = Dx (false, X) (fun g => K • DjU k j ρ g) := by
          show Dx (false, X) (Dw w (DjU k j ρ)) = _
          congr 1; funext g; rw [hD g, smul_eq_mul]
        rw [e, Dx_smul]
        show K • Dx (false, X) (DjU k j ρ) g = _
        rw [Dx_eq]
        have e2 : (fun t : ℝ => DjU k j ρ (crv (false, X) g t)) =
            fun t : ℝ => Complex.exp ((t : ℂ) * c₁) * DjU k j ρ g := by
          funext t; exact (hcur g t).1
        simp only [e2, (hderiv c₁ _).deriv, smul_eq_mul]
        ring
    · refine ⟨c₂ * K, ?_, fun g => ?_⟩
      · rw [norm_mul, List.length_cons, pow_succ']
        exact mul_le_mul (hc₂.trans (mul_le_of_le_one_right hj hxm)) hK (norm_nonneg _) hj
      · have e : Dw ((true, X) :: w) (DjU k j ρ) = Dx (true, X) (fun g => K • DjU k j ρ g) := by
          show Dx (true, X) (Dw w (DjU k j ρ)) = _
          congr 1; funext g; rw [hD g, smul_eq_mul]
        rw [e, Dx_smul]
        show K • Dx (true, X) (DjU k j ρ) g = _
        rw [Dx_eq]
        have e2 : (fun t : ℝ => DjU k j ρ (crv (true, X) g t)) =
            fun t : ℝ => Complex.exp ((t : ℂ) * c₂) * DjU k j ρ g := by
          funext t; exact (hcur g t).2
        simp only [e2, (hderiv c₂ _).deriv, smul_eq_mul]
        ring

theorem djWB_of (h1 : DjCurve) (h2 : PolyB) (h3 : DjPoly) (h4 : CompC) : DjWB := by
  intro k j ρ χ n hχ
  obtain ⟨hcD, hB⟩ := h2 k (j + ρ) j (DjU k j ρ) (h3 k j ρ)
  obtain ⟨CP, hCP⟩ := hB n
  refine ⟨hχ.1.comp hcD, ?_⟩
  obtain ⟨R, hR⟩ := (hχ.2.1 : IsCompact (tsupport χ)).isBounded.exists_norm_le
  refine h4 k (j + ρ) (DjU k j ρ) χ (costP k j ρ) n (|CP| + (max 1 (j : ℝ)) ^ n * |R|) hcD hχ.1 hχ.2.1 ?_
  intro u v hu hv hl hne g hg hgs
  have hg1 := gN_ge_one hg
  have hS0 : (0 : ℝ) ≤ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ |CP| := abs_nonneg _
  have hBn : 0 ≤ (max 1 (j : ℝ)) ^ n * |R| := by positivity
  by_cases hall : ∀ X ∈ u ++ v, inLieP k j ρ X
  ·
    have hw : ∀ x ∈ wL u ++ wR v, inLieP k j ρ x.2 ∧ mx x.2 ≤ 1 := by
      intro x hx
      simp only [wL, wR, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact ⟨hall X (List.mem_append_left _ hX), mx_le_one (hu X hX)⟩
      · exact ⟨hall X (List.mem_append_right _ hX), mx_le_one (hv X hX)⟩
    obtain ⟨K, hK, hD⟩ := dw_dj h1 k j ρ _ hw
    rw [dLR_eq, hD g, norm_mul]
    have hlen : (wL u ++ wR v).length ≤ n := by rw [len_LR]; exact hl
    have hK' : ‖K‖ ≤ (max 1 (j : ℝ)) ^ n :=
      hK.trans ((pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hlen))
    have hDR : ‖DjU k j ρ g‖ ≤ |R| := (hR _ hgs).trans (le_abs_self _)
    have h1' : 1 ≤ B.gN g ^ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := Real.one_le_rpow hg1 hS0
    calc ‖K‖ * ‖DjU k j ρ g‖ ≤ (max 1 (j : ℝ)) ^ n * |R| :=
          mul_le_mul hK' hDR (norm_nonneg _) (by positivity)
      _ ≤ (|CP| + (max 1 (j : ℝ)) ^ n * |R|) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h1' (by positivity)
  · obtain ⟨X, hX, hXP⟩ : ∃ X ∈ u ++ v, ¬ inLieP k j ρ X := by
      by_contra hc; exact hall (fun X hX => by by_contra h; exact hc ⟨X, hX, h⟩)
    have hcX : costP k j ρ X = j := by simp [costP, hXP]
    have hjS : (j : ℝ) ≤ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := costP k j ρ) hX)
      rw [hcX] at this; exact_mod_cast this
    have hb := hCP u v hu hv hl g hg
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_zero, Nat.cast_zero, add_zero] at hb
    calc ‖B.dLR u v (DjU k j ρ) g‖ ≤ CP * B.gN g ^ (j : ℝ) := hb
      _ ≤ |CP| * B.gN g ^ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) :=
          mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hg1 hjS) (by positivity) hA
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end PI.UnitaryCorollaryDerivatives
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.UnitaryCorollaryOfEstimates
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem unitary_corollary_of_estimates (hC : CoreStar) (hD : DjWB) (hG : GfWB) (hM : WBmul) :
    Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator := by
  constructor
  · intro k j ρ Wp Wq _ _ _ _ _ o κ Θ χ hΘ hχ Q mm₀ A₀ hQ
    obtain ⟨hcd, Cφ, hWB⟩ := hD k j ρ χ (Q + o) hχ
    obtain ⟨C, hCf⟩ := hC k j ρ Wp Wq o κ 0 Θ χ (fun g => χ (DjU k j ρ g)) hΘ hχ Q mm₀ A₀ hQ hcd
      (fun g hg => image_eq_zero_of_notMem_tsupport hg) ⟨Cφ, by simpa using hWB⟩
    refine ⟨C, fun f c hf => ?_⟩
    have := hCf f c hf
    simp only [Nat.cast_zero, zero_mul, sub_zero] at this
    exact this
  · intro k j ρ Wp Wq _ _ _ _ _ z z' o κ Θ χ χε ε hΘ hχ hε Q mm₀ A₀ hQ
    obtain ⟨hcd, C1, h1⟩ := hD k j ρ χ (Q + o) hχ
    obtain ⟨hcg, C2, h2⟩ := hG k (j + ρ) z z' χε ε (Q + o) hε
    obtain ⟨C3, h3⟩ := hM k (j + ρ) _ _ _ _ (Q + o) C1 C2 0 0 hcd hcg h1 h2
    rw [zero_add] at h3
    obtain ⟨C, hCf⟩ := hC k j ρ Wp Wq o κ (2 * (j + ρ + 1)) Θ χ
      (fun g => χ (DjU k j ρ g) * ((χε (Gf k (j + ρ) z z' g) : ℝ) : ℂ)) hΘ hχ Q mm₀ A₀ hQ (hcd.mul hcg)
      (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg]) ⟨C3, h3⟩
    refine ⟨C, fun f c hf => ?_⟩
    have := hCf f c hf
    convert this using 2
    · rfl
    · push_cast; ring

end PI.UnitaryCorollaryDerivatives
end
end

