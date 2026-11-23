module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSelfDualClassesRootDiscr
section
open NumberField Module Submodule
open ReciprocityTheory.ChartRestriction.G.FD (herm cc fdeg rdE)

namespace GlobalTheory

namespace RootClassCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isIntegral_herm_iff {n : ℕ} (x y : Fin n → E) :
    IsIntegral ℤ (herm 1 y x) ↔ IsIntegral ℤ (∑ i, IsCMField.complexConj E (x i) * y i) := by
  rw [DualFamily.herm_one_eq]
  simp only [cc, mul_comm]

theorem mul_conjTranspose_eq_one {n : ℕ} (γ : Matrix (Fin n) (Fin n) E)
    (h : ∀ x y, herm 1 (γ.mulVec x) (γ.mulVec y) = herm 1 x y) :
    γ * (γ.map (IsCMField.complexConj E)).transpose = 1 := by
  rw [mul_eq_one_comm]
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rw [DualFamily.herm_one_eq, DualFamily.herm_one_eq] at this
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, cc] at this
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, mul_comm, Matrix.one_apply]
  rw [this]
  simp [Pi.single_apply, eq_comm]

omit [IsCMField E] in
theorem rdE_eq : rdE E = |(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) := rfl

omit [IsCMField E] in
theorem one_le_rootDiscr : 1 ≤ |(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) := by
  refine Real.one_le_rpow ?_ (by positivity)
  exact_mod_cast Int.one_le_abs (discr_ne_zero E)

theorem exists_bounded_basis {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hint : ∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ L, IsIntegral ℤ (herm 1 x y)) → x ∈ L) :
    ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ L) ∧ LinearIndependent E v ∧
      ∀ (σ : E →+* ℂ) (i k : Fin n), ‖σ (herm 1 (v i) (v k))‖ ≤
        4 * (fdeg E : ℝ) ^ 3 * n ^ 4 * rdE E ^ 2 := by
  obtain ⟨v, hv, hli, -, hle⟩ := exists_short_vectors L hfg hint hdual
  obtain ⟨s, hs1, hs2, -⟩ := euclidean_basis_exists E (Fin n → E) _ v hli (by
    simp [ShortVectors.finrank_eq])
  have hsr : s.card = n := by simpa using hs1
  let e : Fin n ≃ s := (s.equivFinOfCardEq hsr).symm
  have h3 : ((fdeg E : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (fdeg E : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_natCast]
    norm_num
  refine ⟨fun i => v (e i), fun i => hv _, hs2.comp e e.injective, fun σ i k => ?_⟩
  refine (SelfDualClasses.norm_herm_le σ _ _ _ (hle _ σ) (hle _ σ)).trans (le_of_eq ?_)
  rw [mul_pow, mul_pow, mul_pow, h3]
  ring

theorem bound_le (f n : ℕ) {r : ℝ} (hf : 0 < f) (hr : 1 ≤ r) :
    (1 + 2 * (4 * (f : ℝ) ^ 3 * n ^ 4 * r ^ 2)) ^ (2 * f * n ^ 2) *
      (n * (4 * (f : ℝ) ^ 3 * n ^ 4 * r ^ 2)) ^ (2 * f * n ^ 2) ≤
      (3 * (((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * r ^ 2)) ^ (3 * (2 * f) * n ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set p : ℝ := ((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * r ^ 2 with hp
  have hp' : p = 4 * (f : ℝ) ^ 2 * (n : ℝ) ^ 4 * r ^ 2 := by rw [hp]; push_cast; ring
  have hB : 4 * (f : ℝ) ^ 3 * n ^ 4 * r ^ 2 = f * p := by rw [hp']; ring
  have h1 : (f : ℝ) ^ 2 * n ≤ p := by
    rw [hp']
    have h2 : (n : ℝ) ≤ n ^ 4 := le_self_pow₀ hn' (by norm_num)
    have h3 : 1 ≤ r ^ 2 := one_le_pow₀ hr
    calc (f : ℝ) ^ 2 * n = 1 * (f : ℝ) ^ 2 * n * 1 := by ring
      _ ≤ _ := by gcongr; norm_num
  have h4 : 1 ≤ (f : ℝ) ^ 2 * n := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hf') hn'
  have h5 : 1 ≤ p := h4.trans h1
  have h6 : 1 ≤ f * p := one_le_mul_of_one_le_of_one_le hf' h5
  rw [hB, ← mul_pow, mul_assoc 3, pow_mul _ 3]
  gcongr
  calc (1 + 2 * (f * p)) * (n * (f * p)) ≤ (3 * (f * p)) * (n * (f * p)) := by
        gcongr; linarith
    _ = 3 * ((f : ℝ) ^ 2 * n) * p ^ 2 := by ring
    _ ≤ 27 * p * p ^ 2 := by gcongr; norm_num
    _ = _ := by ring

end RootClassCount


open RootClassCount in
theorem exists_finset_selfDual_classes_rootDiscr :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    ∃ R : Finset (Submodule (𝓞 E) (Fin n → E)),
      (R.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
        (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (∑ i, IsCMField.complexConj E (x i) * y i)) →
        ∃ L₀ ∈ R, ∃ γ : Matrix (Fin n) (Fin n) E,
          γ * (γ.map (IsCMField.complexConj E)).transpose = 1 ∧
          ∀ x, x ∈ L₀ ↔ γ.mulVec x ∈ L := by
  intro E _ _ _ n
  obtain ⟨R, -, h2, h3⟩ := ClassCount.exists_finset_classes (K := E) (r := n) (G := 1)
    {L | L.FG ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (herm 1 y x)}
    (B := 4 * (fdeg E : ℝ) ^ 3 * n ^ 4 * rdE E ^ 2) (by positivity) fun L hL =>
      ⟨by simp, fun x hx => (hL.2 x).1 hx,
        exists_bounded_basis L hL.1 (fun x hx => (hL.2 x).1 hx) fun x hx => (hL.2 x).2 hx⟩
  refine ⟨R, h3.trans ?_, fun L hfg _ hsd => ?_⟩
  · have h := bound_le (fdeg E) n ClassCount.fdeg_pos (one_le_rootDiscr (E := E))
    rw [← ShortVectors.finrank_eq] at h
    rw [rdE_eq, ← ShortVectors.finrank_eq]
    exact h
  · obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := h2 L ⟨hfg, fun y => by
      simp only [isIntegral_herm_iff]; exact hsd y⟩
    exact ⟨L₀, hL₀, γ, mul_conjTranspose_eq_one _ hγ, hm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GenusOneDatum


open PowerSeries in
theorem exists_fixed_of_contract {R : Type*} [CommRing R] (T : PowerSeries R → PowerSeries R)
    (hT : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ x - y → X ^ (n + 1) ∣ T x - T y) :
    ∃ x, T x = x := by
  have hit : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ T^[n] x - T^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hT n _ _ (ih x y)
  let L : PowerSeries R := PowerSeries.mk fun n => coeff n (T^[n + 1] 0)
  have hL : ∀ n, X ^ n ∣ L - T^[n] 0 := by
    intro n
    rw [X_pow_dvd_iff]
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, n = (m + 1) + k := ⟨n - (m + 1), by omega⟩
    have := X_pow_dvd_iff.1 (hit (m + 1) 0 (T^[k] 0)) m (by omega)
    rw [← Function.iterate_add_apply] at this
    simpa [L] using this
  refine ⟨L, ?_⟩
  ext n
  have h1 := hT n _ _ (hL n)
  have h2 := hL (n + 1)
  rw [Function.iterate_succ_apply'] at h2
  have h3 := dvd_sub h1 h2
  have h4 := X_pow_dvd_iff.1 h3 n (by omega)
  rw [sub_sub_sub_cancel_right, map_sub, sub_eq_zero] at h4
  exact h4

theorem exists_isWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) : ∃ wq, IsWq W wq := by
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  obtain ⟨w, hw⟩ := exists_fixed_of_contract (fun wq : PowerSeries ℂ_[p] =>
    1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3) (by
      rintro n x y ⟨z, hz⟩
      refine ⟨z * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) +
        c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2)), ?_⟩
      have hz' : x - y = X ^ n * z := hz
      change _ = X ^ (n + 1) * _
      linear_combination (X * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) +
        c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2))) * hz')
  exact ⟨w, hw.symm⟩

theorem constantCoeff_of_isWq {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]}
    {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) : PowerSeries.constantCoeff wq = 1 := by
  have h' := congrArg PowerSeries.constantCoeff h
  simpa using h'

theorem coeff_one_flog {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]}
    {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) : PowerSeries.coeff 1 (flog W wq) = 1 := by
  have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  simp [flog, omegaW, PowerSeries.constantCoeff_inv, constantCoeff_of_isWq h, h2]

theorem constantCoeff_flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) : PowerSeries.constantCoeff (flog W wq) = 0 := by
  simp [flog]

theorem exists_subst_eq_X {R : Type*} [CommRing R] (l : PowerSeries R)
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    ∃ ex : PowerSeries R, PowerSeries.constantCoeff ex = 0 ∧
      PowerSeries.subst ex l = PowerSeries.X := by
  have hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1 := by
    ext i j
    exact h1
  obtain ⟨v, hv, h, -⟩ := (GlobalTheory.FormalInv.exists_substInv_iff
    (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)
  exact ⟨v (), hv (), h ()⟩

theorem exists_genusOne_datum : ∀ (D : D7), GL3Theta.modelEx D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∃ g : GL3Theta.G1 p, GL3Theta.At D cc δ g ∧ g.lam = lam ∧ ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
  intro D hm p _ lam cc δ hc hcop
  obtain ⟨⟨C, hC⟩, -, hu⟩ := hm p lam cc δ hc.1 hcop hc.2
  obtain ⟨wq, hwq⟩ := exists_isWq (C • wModel lam (lamOf D cc δ))
  obtain ⟨ex, he0, he⟩ := exists_subst_eq_X _ (constantCoeff_flog _ wq) (coeff_one_flog hwq)
  exact ⟨⟨lam, lamOf D cc δ, C, wq, ex⟩, ⟨hc.1, hcop, hc.2, rfl, hC, hwq, he0, he⟩, rfl, hu C hC⟩

end GlobalTheory.GenusOneDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorPowFractionalIdealNonarchSize
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

theorem nonarch_le_pow_of_mem_ideal_pow {K : Type} [Field K] [NumberField K] (J : Ideal (𝓞 K))
    (v : K →*₀ ℝ) (h0 : ∀ x, 0 ≤ v x) (hadd : ∀ x y, v (x + y) ≤ max (v x) (v y))
    (hint : ∀ c : 𝓞 K, v (c : K) ≤ 1) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ J, v (y : K) ≤ M) (k : ℕ) : ∀ y ∈ J ^ k, v (y : K) ≤ M ^ k := by
  induction k with
  | zero => intro y _; simpa using hint y
  | succ k ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      have : ((a * b : 𝓞 K) : K) = (a : K) * (b : K) := by simp
      rw [this, map_mul, pow_succ]
      exact mul_le_mul (ih a ha) (hM b hb) (h0 _) (pow_nonneg hM0 _)
    · intro a b ha hb
      have : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by simp
      rw [this]
      exact (hadd _ _).trans (max_le ha hb)

theorem exists_generator_pow_fractional_size : ∀ (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 K) K), I ≠ ⊥ → (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : K) * x ∈ (algebraMap (𝓞 K) K).range) → ∃ (h : ℕ) (α : K), 0 < h ∧ α ≠ 0 ∧ ∀ v : K →*₀ ℝ, (∀ x, 0 ≤ v x) → (∀ x y, v (x + y) ≤ max (v x) (v y)) → (∀ c : 𝓞 K, v (c : K) ≤ 1) → ∀ x₀ ∈ I, (∀ x ∈ I, v x ≤ v x₀) → v α = v x₀ ^ h := by
  intro K _ _ I hI ⟨n, hn, hnI⟩
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let J : Ideal (𝓞 K) :=
    { carrier := {c | ∃ x ∈ I, (c : K) = (n : K) * x}
      zero_mem' := ⟨0, I.zero_mem, by simp⟩
      add_mem' := by
        rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
        refine ⟨x + y, I.add_mem hx hy, ?_⟩
        have : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by simp
        rw [this, ha, hb]; ring
      smul_mem' := by
        rintro c a ⟨x, hx, ha⟩
        refine ⟨c • x, I.smul_mem c hx, ?_⟩
        have : ((c • a : 𝓞 K) : K) = (c : K) * (a : K) := by simp
        have h2 : c • x = (c : K) * x := Algebra.smul_def c x
        rw [this, ha, h2]; ring }
  have hmem : ∀ x ∈ I, ∃ c ∈ J, (c : K) = (n : K) * x := by
    intro x hx
    obtain ⟨c, hc⟩ := hnI x hx
    exact ⟨c, ⟨x, hx, hc⟩, hc⟩
  have hJ : J ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨c, hc, hcx⟩ := hmem x hx
    intro h
    rw [h] at hc
    have : c = 0 := by simpa using hc
    rw [this] at hcx
    exact mul_ne_zero hnK hx0 (by simpa using hcx.symm)
  have hJ' : J ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hJ
  set h := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hprin : (J ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨J, hJ'⟩ ^ h : nonZeroDivisors (Ideal (𝓞 K))) = 1 := by
      rw [map_pow]; exact pow_card_eq_one
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hJ' h)).mp h1
  obtain ⟨a, ha⟩ := hprin
  have ha0 : a ≠ 0 := by
    intro h0
    apply pow_ne_zero h hJ
    rw [ha, h0]; simp
  have haK : (a : K) ≠ 0 := by simpa using ha0
  refine ⟨h, (a : K) / (n : K) ^ h, hpos, div_ne_zero haK (pow_ne_zero _ hnK), ?_⟩
  intro v h0 hadd hint x₀ hx₀ hmax
  have hvn : v (n : K) ≠ 0 := (map_ne_zero v).mpr hnK
  have hM : ∀ y ∈ J, v (y : K) ≤ v (n : K) * v x₀ := by
    rintro y ⟨x, hx, hy⟩
    rw [hy, map_mul]
    exact mul_le_mul_of_nonneg_left (hmax x hx) (h0 _)
  have h1 : v (a : K) ≤ (v (n : K) * v x₀) ^ h :=
    nonarch_le_pow_of_mem_ideal_pow J v h0 hadd hint _ (mul_nonneg (h0 _) (h0 _)) hM h a
      (by rw [ha]; exact Submodule.mem_span_singleton_self a)
  have h2 : (v (n : K) * v x₀) ^ h ≤ v (a : K) := by
    obtain ⟨c, hc, hcx⟩ := hmem x₀ hx₀
    have hch : c ^ h ∈ J ^ h := Ideal.pow_mem_pow hc h
    rw [ha] at hch
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hch
    have hd' : (d : K) * (a : K) = (c : K) ^ h := by
      have := congrArg (algebraMap (𝓞 K) K) hd
      simpa using this
    rw [← map_mul, ← hcx, ← map_pow, ← hd', map_mul]
    exact mul_le_of_le_one_left (h0 _) (hint d)
  rw [map_div₀, map_pow, le_antisymm h1 h2, mul_pow]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHighestWeightVectorOfKStable
section
open Formalism.BasicNotions.TH

namespace GlobalTheory.ExistsHW

open GlobalTheory.TensorHW

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma inf_eig_ne_bot_iff (f : Module.End ℂ V) (N : Submodule ℂ V) (hf : ∀ x ∈ N, f x ∈ N) (t : ℂ) :
    N ⊓ f.eigenspace t ≠ ⊥ ↔ Module.End.HasEigenvalue (f.restrict hf) t := by
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, hx0⟩
    refine ⟨⟨x, hx1⟩, ?_, fun h => hx0 (congrArg Subtype.val h)⟩
    rw [Module.End.mem_eigenspace_iff]
    exact Subtype.ext (Module.End.mem_eigenspace_iff.1 hx2)
  · rintro ⟨x, hx, hx0⟩
    refine ⟨x, ⟨x.2, ?_⟩, fun h => hx0 (Subtype.ext h)⟩
    rw [Module.End.mem_eigenspace_iff] at hx
    exact Module.End.mem_eigenspace_iff.2 (congrArg Subtype.val hx)

lemma exists_eig (f : Module.End ℂ V) (N : Submodule ℂ V) [FiniteDimensional ℂ N] (hN : N ≠ ⊥)
    (hf : ∀ x ∈ N, f x ∈ N) : ∃ t, N ⊓ f.eigenspace t ≠ ⊥ := by
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  obtain ⟨t, ht⟩ := Module.End.exists_eigenvalue (f.restrict hf)
  exact ⟨t, (inf_eig_ne_bot_iff f N hf t).2 ht⟩

lemma finite_eig (f : Module.End ℂ V) (N : Submodule ℂ V) [FiniteDimensional ℂ N]
    (hf : ∀ x ∈ N, f x ∈ N) : {t | N ⊓ f.eigenspace t ≠ ⊥}.Finite := by
  simp only [inf_eig_ne_bot_iff f N hf]
  exact Module.End.finite_hasEigenvalue _

lemma exists_common {ι : Type*} (E : ι → Module.End ℂ V) (hE : ∀ a b x, E a (E b x) = E b (E a x))
    (N : Submodule ℂ V) [FiniteDimensional ℂ N] (hN : N ≠ ⊥) (hst : ∀ a, ∀ x ∈ N, E a x ∈ N)
    (s : Finset ι) : ∃ N' : Submodule ℂ V, N' ≤ N ∧ N' ≠ ⊥ ∧ (∀ a, ∀ x ∈ N', E a x ∈ N') ∧
      ∀ a ∈ s, ∃ t, N' ≤ (E a).eigenspace t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨N, le_rfl, hN, hst, by simp⟩
  | insert b s _ ih =>
    obtain ⟨N', h1, h2, h3, h4⟩ := ih
    haveI : FiniteDimensional ℂ N' := Submodule.finiteDimensional_of_le h1
    obtain ⟨t, ht⟩ := exists_eig (E b) N' h2 (h3 b)
    refine ⟨N' ⊓ (E b).eigenspace t, inf_le_left.trans h1, ht, ?_, ?_⟩
    · rintro a x ⟨hx1, hx2⟩
      refine ⟨h3 a x hx1, Module.End.mem_eigenspace_iff.2 ?_⟩
      rw [hE, Module.End.mem_eigenspace_iff.1 hx2, map_smul]
    · intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact ⟨t, inf_le_right⟩
      · obtain ⟨u, hu⟩ := h4 a ha
        exact ⟨u, inf_le_left.trans hu⟩

end General

lemma eig_rat {p q : ℕ} (M : GKMod p q) (a : Ix p q) {t : ℂ} {v : M.V} (hv0 : v ≠ 0)
    (hv : v ∈ (M.act (Eab a a)).eigenspace t) : ∃ r : ℚ, (r : ℂ) = t := by
  by_contra hr
  have hd := Module.End.eigenspaces_iSupIndep (M.act (Eab a a)) t
  have hle : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
      ⨆ (j : ℂ) (_ : j ≠ t), (M.act (Eab a a)).eigenspace j := by
    refine iSup_le fun μ => le_iSup₂_of_le ((μ a : ℚ) : ℂ) (fun h => hr ⟨μ a, h⟩) fun x hx => ?_
    exact Module.End.mem_eigenspace_iff.2 (mem_wt.1 hx a)
  exact hv0 (Submodule.disjoint_def.1 hd v hv (hle (M.wts v)))

theorem exists_highestWeight (p q : ℕ) (M : GKMod p q) (W : Submodule ℂ M.V)
    (hfd : FiniteDimensional ℂ W) (hW : KStable M.act W) (h0 : W ≠ ⊥) :
    ∃ (μ : Ix p q → ℚ) (v : M.V), v ∈ W ∧ IsHW M.act μ v := by
  have hL : Formalism.MainNotions.SchurIrreducible.IsKLieAct M.act := fun X Y _ _ => M.lie X Y
  set c : Ix p q → ℂ := fun a => (grad p q a : ℂ) with hc
  set H : Module.End ℂ M.V := M.act (Matrix.diagonal c) with hH
  have hHW : ∀ x ∈ W, H x ∈ W := hW _ (isKC_diag c)
  obtain ⟨t, ht, hmax⟩ := Set.exists_max_image _ Complex.re (finite_eig H W hHW)
    (exists_eig H W h0 hHW)
  set N := W ⊓ H.eigenspace t with hN
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le inf_le_left
  have hkill : ∀ a b, posC a b → ∀ x ∈ N, M.act (Eab a b) x = 0 := by
    intro a b hab x hx
    by_contra hne
    have := hmax (t + (c a - c b)) ((Submodule.ne_bot_iff _).2 ⟨_,
      ⟨hW _ (isKC_Eab (same_of_pos hab)) x hx.1, eig_shift hL c (same_of_pos hab) hx.2⟩, hne⟩)
    simp only [hc, Complex.add_re, Complex.sub_re, Complex.ofReal_re] at this
    linarith [grad_lt hab]
  have hst : ∀ a, ∀ x ∈ N, M.act (Eab a a) x ∈ N := by
    intro a x hx
    refine ⟨hW _ (isKC_Eab (same_refl a)) x hx.1, ?_⟩
    have := eig_shift hL c (same_refl a) hx.2
    rwa [sub_self, add_zero] at this
  have hcomm : ∀ a b x, M.act (Eab a a) (M.act (Eab b b) x) = M.act (Eab b b) (M.act (Eab a a) x) := by
    intro a b x
    rw [lie_apply hL (isKC_Eab (same_refl a)) (isKC_Eab (same_refl b))]
    have : (Eab a a * Eab b b - Eab b b * Eab a a : Mat p q) = 0 := by
      by_cases hab : a = b
      · rw [hab, sub_self]
      · rw [Eab, Eab, Matrix.single_mul_single_of_ne _ _ _ _ hab,
          Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hab), sub_self]
    rw [this, map_zero, LinearMap.zero_apply, add_zero]
  obtain ⟨N', h1, h2, -, h4⟩ := exists_common (fun a => M.act (Eab a a)) hcomm N ht hst Finset.univ
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h2
  have : ∀ a, ∃ r : ℚ, M.act (Eab a a) v = (r : ℂ) • v := by
    intro a
    obtain ⟨u, hu⟩ := h4 a (Finset.mem_univ a)
    obtain ⟨r, rfl⟩ := eig_rat M a hv0 (hu hv)
    exact ⟨r, Module.End.mem_eigenspace_iff.1 (hu hv)⟩
  choose μ hμ using this
  exact ⟨μ, v, (h1 hv).1, hv0, mem_hw.2 ⟨hμ, fun a b hab => hkill a b hab v (h1 hv)⟩⟩

end GlobalTheory.ExistsHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem isIntegral_half_one_add {L : Type*} [Field L] [CharZero L] (d : ℕ) (hd : d % 16 = 7) (b : L)
    (hb : b ^ 2 = -(d : L)) : IsIntegral ℤ ((1 + b) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
  have hm' : (d : L) + 1 = 4 * (m : L) := by exact_mod_cast hm
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
  · monicity!
  · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_natCast]
    linear_combination (1 / 4 : L) * hb - (1 / 4 : L) * hm'

theorem exists_integer_map_eq_w0 :
    ∀ (D : D7), ∃ a : 𝓞 D.host.K, D.host.φ₀ (((a : D.host.K) : D.host.E)) = w0 D := by
  intro D
  have hsq := D.host.sqd_sq
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hd0 : (0 : ℝ) ≤ D.host.d := Nat.cast_nonneg _
  have key : ∀ b : D.host.K, (b : D.host.E) ^ 2 = -(D.host.d : D.host.E) →
      D.host.φ₀ (b : D.host.E) = Complex.I * (Real.sqrt D.host.d : ℂ) →
      ∃ a : 𝓞 D.host.K, D.host.φ₀ (((a : D.host.K) : D.host.E)) = w0 D := by
    intro b hb hφ
    have hb' : b ^ 2 = -(D.host.d : D.host.K) := by
      apply Subtype.ext
      simpa using hb
    refine ⟨⟨(1 + b) / 2, isIntegral_half_one_add _ hd16 b hb'⟩, ?_⟩
    change D.host.φ₀ (algebraMap D.host.K D.host.E ((1 + b) / 2)) = _
    rw [map_div₀, map_add (f := _), map_one, map_ofNat, map_div₀, map_add (f := _), map_one, map_ofNat]
    change (1 + D.host.φ₀ (b : D.host.E)) / 2 = _
    rw [hφ, w0]
  let b : D.host.K := ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have h1 : (D.host.φ₀ (b : D.host.E)) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
    change (D.host.φ₀ (D.host.sqd)) ^ 2 = _
    rw [← map_pow, hsq, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt hd0]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact key b hsq h
  · refine key (-b) ?_ ?_
    · change (-(D.host.sqd)) ^ 2 = _
      rw [neg_sq, hsq]
    · change D.host.φ₀ (-(b : D.host.E)) = _
      rw [map_neg, h, neg_neg]

end GlobalTheory.NormSum
end

