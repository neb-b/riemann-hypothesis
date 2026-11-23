module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonicFactorCoeffNatDegreeLe
section
open Polynomial

namespace GlobalTheory.MonicFactorDegree

variable {κ : Type} [Field κ]

noncomputable def subst (D : ℕ) : Polynomial (Polynomial κ) →+* Polynomial (Polynomial κ) :=
  eval₂RingHom (mapRingHom (C : κ →+* Polynomial κ)) (C X * X ^ D)

lemma term_coeff (D j m i : ℕ) (p : Polynomial κ) :
    (((mapRingHom (C : κ →+* Polynomial κ)) p * (C X * X ^ D) ^ j).coeff m).coeff i =
      if D * j ≤ m then (if i = j then p.coeff (m - D * j) else 0) else 0 := by
  have hC : (C (X : Polynomial κ) : Polynomial (Polynomial κ)) ^ j = C (X ^ j) := (C_pow ..).symm
  rw [mul_pow, hC, ← pow_mul, ← mul_assoc, coeff_mul_X_pow']
  split_ifs with h1 h2
  · subst h2; rw [coeff_mul_C, coe_mapRingHom, coeff_map, coeff_C_mul_X_pow]; simp
  · rw [coeff_mul_C, coe_mapRingHom, coeff_map, coeff_C_mul_X_pow]; simp [h2]
  · simp

lemma subst_coeff_coeff (D : ℕ) (P : Polynomial (Polynomial κ)) (i k : ℕ) :
    ((subst D P).coeff (k + D * i)).coeff i = (P.coeff i).coeff k := by
  simp only [subst, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum, finsetSum_coeff, term_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro hi; simp [notMem_support_iff.mp hi]

theorem monic_factor_coeff_natDegree_le : ∀ {κ : Type} [Field κ] (Φ A B : Polynomial (Polynomial κ))
    (D : ℕ), Φ.Monic → A.Monic → B.Monic → Φ = A * B → (∀ i, (Φ.coeff i).natDegree ≤ D) →
    ∀ i, (A.coeff i).natDegree ≤ Φ.natDegree * D := by
  intro κ _ Φ A B D hΦ _ hB hAB hD i
  by_cases hi : A.coeff i = 0
  · simp [hi]
  have key : ∀ P : Polynomial (Polynomial κ), ∀ j, P.coeff j ≠ 0 →
      (P.coeff j).natDegree + D * j ≤ (subst D P).natDegree ∧ subst D P ≠ 0 := by
    intro P j hj
    have h := subst_coeff_coeff D P j (P.coeff j).natDegree
    have hne : (subst D P).coeff ((P.coeff j).natDegree + D * j) ≠ 0 := by
      intro h0
      rw [h0, coeff_zero] at h
      exact hj (leadingCoeff_eq_zero.mp h.symm)
    exact ⟨le_natDegree_of_ne_zero hne, fun h0 => hne (by simp [h0])⟩
  have hAi := key A i hi
  have hB0 := (key B B.natDegree (by rw [hB.coeff_natDegree]; exact one_ne_zero)).2
  have hmul : (subst D Φ).natDegree = (subst D A).natDegree + (subst D B).natDegree := by
    rw [hAB, map_mul, natDegree_mul hAi.2 hB0]
  have hup : (subst D Φ).natDegree ≤ Φ.natDegree * D := by
    simp only [subst, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum]
    apply natDegree_sum_le_of_forall_le
    intro j hj
    have hjd : j ≤ Φ.natDegree := le_natDegree_of_mem_supp j hj
    have h1 : (mapRingHom (C : κ →+* Polynomial κ) (Φ.coeff j)).natDegree ≤ (Φ.coeff j).natDegree := by
      rw [coe_mapRingHom]; exact natDegree_map_le
    have h2 : ((C X * X ^ D : Polynomial (Polynomial κ)) ^ j).natDegree ≤ j * D := by
      calc _ ≤ j * (C X * X ^ D : Polynomial (Polynomial κ)).natDegree := natDegree_pow_le
        _ ≤ j * D := by
          apply Nat.mul_le_mul_left
          calc _ ≤ (C X : Polynomial (Polynomial κ)).natDegree + (X ^ D : Polynomial (Polynomial κ)).natDegree :=
                natDegree_mul_le
            _ = D := by simp
    have h3 : (Φ.coeff j).natDegree + j * D ≤ Φ.natDegree * D := by
      rcases hjd.lt_or_eq with h | h
      · have h4 := hD j
        have h5 : (j + 1) * D ≤ Φ.natDegree * D := Nat.mul_le_mul_right _ h
        rw [add_mul, one_mul] at h5
        omega
      · rw [h, hΦ.coeff_natDegree, natDegree_one, zero_add]
    exact (natDegree_mul_le).trans (by omega)
  have := hAi.1
  have h6 : (A.coeff i).natDegree ≤ (subst D A).natDegree := by omega
  omega

end GlobalTheory.MonicFactorDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MvPowerSeriesThreeEqZeroOfSubstLines
section
namespace GlobalTheory

theorem mvPowerSeries_three_eq_zero_of_subst_lines :
    ∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K),
      (∀ t : Fin 3 → K, (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) →
      Φ = 0 := by
  intro K _ _ Φ h
  ext d
  set n := ∑ i, d i with hn
  let S : Finset (Fin 3 →₀ ℕ) :=
    (Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => n)).filter (fun e => ∑ i, e i = n)
  have hS : ∀ e, e ∈ S ↔ ∑ i, e i = n := by
    intro e
    simp only [S, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
    intro he i
    change e i ≤ n
    rw [← he]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  let P : MvPolynomial (Fin 3) K := ∑ e ∈ S, MvPolynomial.monomial e (MvPowerSeries.coeff e Φ)
  have hcoef : ∀ t : Fin 3 → K, PowerSeries.coeff n (MvPowerSeries.subst
      (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) = MvPolynomial.eval t P := by
    intro t
    have ha : MvPowerSeries.HasSubst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
        rw [map_mul]; exact mul_eq_zero_of_right _ (MvPowerSeries.constantCoeff_X ()))
    have hprod : ∀ e : Fin 3 →₀ ℕ,
        (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) =
          PowerSeries.C (∏ s, t s ^ e s) * PowerSeries.X ^ (∑ s, e s) := by
      intro e
      rw [Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]
    have h1 : PowerSeries.coeff n (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) =
        ∑ᶠ e : Fin 3 →₀ ℕ, MvPowerSeries.coeff e Φ • PowerSeries.coeff n
          (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) :=
      MvPowerSeries.coeff_subst ha Φ (Finsupp.single () n)
    have hsupp : Function.support (fun e : Fin 3 →₀ ℕ =>
        MvPowerSeries.coeff e Φ • PowerSeries.coeff n
          (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k)) ⊆ S := by
      intro e he
      rw [Function.mem_support] at he
      rw [hprod, PowerSeries.coeff_C_mul_X_pow, smul_eq_mul] at he
      rw [Finset.mem_coe, hS]
      by_contra hne
      exact he (by simp [Ne.symm hne])
    rw [h1]
    rw [finsum_eq_sum_of_support_subset _ (s := S) hsupp]
    simp only [hprod, PowerSeries.coeff_C_mul_X_pow, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [P, map_sum, MvPolynomial.eval_monomial]
        refine Finset.sum_congr rfl (fun e he => ?_)
        rw [if_pos ((hS e).1 he).symm, Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
  have hP : P = 0 := MvPolynomial.funext (fun t => by rw [← hcoef, h t, map_zero, map_zero])
  have hd := congrArg (AddMonoidAlgebra.coeff · d) hP
  simp only [P, MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hS d).2 rfl)] at hd
  simpa using hd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NewtonPowerSeriesSurjectiveLinearizationSolution
section
open Polynomial

namespace GlobalTheory

theorem newton_powerSeries_of_surjective_linearisation (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ]
    (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k))
    (hL : Function.Surjective L)
    (h0 : ∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0)
    (hG : ∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e -
        PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) :
    ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 := by
  classical
  let r := Function.surjInv hL
  have hLr : ∀ v, L (r v) = v := Function.surjInv_eq hL
  let step : ℕ → (ι → PowerSeries k) → (ι → PowerSeries k) := fun m x i =>
    x i + PowerSeries.X ^ m * PowerSeries.C (r (fun e => -PowerSeries.coeff m (G x e)) i)
  let sq : ℕ → (ι → PowerSeries k) := fun n =>
    Nat.rec (motive := fun _ => ι → PowerSeries k) (fun i => PowerSeries.C (x₀ i)) (fun n x => step (n + 1) x) n
  have sq_zero : sq 0 = fun i => PowerSeries.C (x₀ i) := rfl
  have sq_succ : ∀ n, sq (n + 1) = step (n + 1) (sq n) := fun n => rfl
  have coeffXC : ∀ (m j : ℕ) (c : k),
      PowerSeries.coeff j ((PowerSeries.X : PowerSeries k) ^ m * PowerSeries.C c) = if j = m then c else 0 := by
    intro m j c
    rw [mul_comm, PowerSeries.coeff_C_mul_X_pow]
  have inv : ∀ n, (∀ i, PowerSeries.constantCoeff (sq n i) = x₀ i) ∧
      ∀ e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G (sq n) e := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i => by simp [sq_zero], fun e => ?_⟩
      rw [zero_add, pow_one, PowerSeries.X_dvd_iff, sq_zero]
      exact h0 e
    | succ n ih =>
      have hc : ∀ i, PowerSeries.constantCoeff (sq (n + 1) i) = x₀ i := by
        intro i
        simp [sq_succ, step, ih.1 i]
      refine ⟨hc, fun e => ?_⟩
      set x := sq n with hx
      set v : κ → k := fun e => -PowerSeries.coeff (n + 1) (G x e) with hv
      have key := hG x (fun i => PowerSeries.C (r v i)) (n + 1) (by omega) ih.1 e
      have hcv : (fun i => PowerSeries.constantCoeff (PowerSeries.C (r v i))) = r v := by
        funext i; simp
      rw [hcv, hLr] at key
      have hs : sq (n + 1) = fun i => x i + PowerSeries.X ^ (n + 1) * PowerSeries.C (r v i) := by
        rw [sq_succ]
      have h2 : (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) ∣
          G x e + PowerSeries.X ^ (n + 1) * PowerSeries.C (v e) := by
        rw [PowerSeries.X_pow_dvd_iff]
        intro j hj
        rw [map_add (f := _), coeffXC]
        rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
        · have := (PowerSeries.X_pow_dvd_iff.mp (ih.2 e)) j hj'
          rw [this, if_neg (by omega), add_zero]
        · have hjn : j = n + 1 := by omega
          subst hjn
          simp [hv]
      have := dvd_add key h2
      rw [hs]
      convert this using 1
      ring
  have stab : ∀ i j n, j ≤ n → PowerSeries.coeff j (sq n i) = PowerSeries.coeff j (sq j i) := by
    intro i j n hjn
    induction n, hjn using Nat.le_induction with
    | base => rfl
    | succ n hjn ihn =>
      rw [← ihn, sq_succ]
      simp only [step, map_add (f := _)]
      rw [coeffXC, if_neg (by omega), add_zero]
  let xl : ι → PowerSeries k := fun i => PowerSeries.mk (fun j => PowerSeries.coeff j (sq j i))
  have hdiff : ∀ n i, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ xl i - sq n i := by
    intro n i
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    simp only [xl, map_sub, PowerSeries.coeff_mk]
    rw [stab i j n (by omega), sub_self]
  have hlim : ∀ n e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e := by
    intro n e
    choose d hd using hdiff n
    have hx : xl = fun i => sq n i + PowerSeries.X ^ (n + 1) * d i := by
      funext i; rw [← hd i]; ring
    have key := hG (sq n) d (n + 1) (by omega) (inv n).1 e
    rw [← hx] at key
    have k1 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e - G (sq n) e := by
      have h3 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) :=
        pow_dvd_pow _ (by omega)
      have := dvd_add (h3.trans key) (dvd_mul_right ((PowerSeries.X : PowerSeries k) ^ (n + 1))
        (PowerSeries.C (L (fun i => PowerSeries.constantCoeff (d i)) e)))
      simpa using this
    have := dvd_add k1 ((inv n).2 e)
    simpa using this
  refine ⟨xl, fun i => ?_, fun e => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [xl, PowerSeries.coeff_mk]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (inv 0).1 i
  · ext j
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.mp (hlim j e) j (by omega)

theorem newton_powerSeries_target : ∀ (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ] (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k)), Function.Surjective L →
 (∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0) →
 (∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
   (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e - PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) →
 ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 :=
  fun k ι κ _ _ _ G x₀ L hL h0 hG => newton_powerSeries_of_surjective_linearisation k ι κ G x₀ L hL h0 hG

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAlgebraMapLeOneBis
section
namespace GlobalTheory.AlgebraMapNormLeOne

open Polynomial

theorem norm_algebraMap_le_one (l : ℕ) [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  calc ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖
      = ‖algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] a)‖ := by
        rw [← IsScalarTower.algebraMap_apply]
    _ = ‖algebraMap ℤ_[l] ℚ_[l] a‖ := PadicAlgCl.norm_extends l _
    _ ≤ 1 := PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral (l : ℕ) [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  let v : Valuation (PadicAlgCl l) NNReal := Valued.v
  have hle : ∀ y : PadicAlgCl l, v y ≤ 1 ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  let f : ℤ_[l] →+* v.integer := (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer
    fun a => (hle _).mpr (norm_algebraMap_le_one l a)
  let _ : Algebra ℤ_[l] v.integer := f.toAlgebra
  have : IsScalarTower ℤ_[l] v.integer (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxO : IsIntegral v.integer x := hx.tower_top
  exact (hle x).mp ((Valuation.Integers.isIntegral_iff_v_le_one (Valuation.integer.integers v)).mp hxO)

end GlobalTheory.AlgebraMapNormLeOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAlgebraMapPadicIntLeOne
section
namespace GlobalTheory.PadicIntegralNormLeOne

open Polynomial

theorem norm_algebraMap_padicInt_le_one {l : ℕ} [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l),
    PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  obtain ⟨f, hmon, hf⟩ := hx
  by_contra h
  push_neg at h
  have hsum := hf
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree, hmon.leadingCoeff,
    map_one, one_mul] at hsum
  set n := f.natDegree
  set S := ∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i) * x ^ i
  have hxn : x ^ n = -S := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : S = 0 := by simp [S, hn]
    rw [this, hn, pow_zero, neg_zero] at hxn
    exact one_ne_zero hxn
  · have hx1 : (1 : ℝ) ≤ ‖x‖ := h.le
    have hS : ‖S‖ ≤ ‖x‖ ^ (n - 1) := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      intro i hi
      rw [Finset.mem_range] at hi
      rw [norm_mul, norm_pow]
      calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
            gcongr; exact norm_algebraMap_padicInt_le_one _
        _ = ‖x‖ ^ i := one_mul _
        _ ≤ ‖x‖ ^ (n - 1) := pow_le_pow_right₀ hx1 (by omega)
    have hlt : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ h (by omega)
    have : ‖x ^ n‖ = ‖S‖ := by rw [hxn, norm_neg]
    rw [norm_pow] at this
    linarith

end GlobalTheory.PadicIntegralNormLeOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOfMemSpan
section
namespace GlobalTheory.NormBoundOfSpan

theorem norm_le_of_mem_span {K E ι : Type} [NormedField K] [AddCommGroup E] [Module K E]
    (φ : ι → E →ₗ[K] K) :
    ∀ f ∈ Submodule.span K (Set.range φ), ∃ (C : ℝ), (0 : ℝ) ≤ C ∧ ∀ (p : E) (r : ℝ),
      (0 : ℝ) ≤ r → (∀ (j : ι), ‖(φ j : E → K) p‖ ≤ r) → ‖(f : E → K) p‖ ≤ C * r := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, zero_le_one, fun p r _ h => by simpa using h j⟩
  | zero => exact ⟨0, le_rfl, fun p r _ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C, hC, h1⟩ := hx
    obtain ⟨D, hD, h2⟩ := hy
    refine ⟨C + D, add_nonneg hC hD, fun p r hr h => ?_⟩
    rw [LinearMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h1 p r hr h) (h2 p r hr h))
  | smul a x _ hx =>
    obtain ⟨C, hC, h1⟩ := hx
    refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg a) hC, fun p r hr h => ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 p r hr h) (norm_nonneg a)

end GlobalTheory.NormBoundOfSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemOfMulClosedOfDetNeZero
section
open scoped Matrix
open Polynomial

namespace GlobalTheory

theorem one_mem_of_mulClosed_of_det_ne_zero : ∀ {F K : Type} [Field F] [Field K] [Algebra F K]
    [Algebra.IsIntegral F K] {m : ℕ} (S : Submodule F (Matrix (Fin m) (Fin m) K)),
    (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) → ∀ T ∈ S, T.det ≠ 0 → (1 : Matrix (Fin m) (Fin m) K) ∈ S := by
  intro F K _ _ _ _ m S hS T hT hdet
  classical
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).2 (isUnit_iff_ne_zero.2 hdet)
  have hint : IsIntegral F T := by
    have hK : IsIntegral K T := Algebra.IsIntegral.isIntegral T
    exact isIntegral_trans T hK
  have hpow : ∀ n : ℕ, T ^ (n + 1) ∈ S := by
    intro n
    induction n with
    | zero => simpa using hT
    | succ n ih => rw [pow_succ]; exact hS _ ih _ hT
  have hmul : ∀ q : F[X], T * aeval T q ∈ S := by
    intro q
    rw [aeval_eq_sum_range, Finset.mul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_smul_comm, ← pow_succ']
    exact S.smul_mem _ (hpow i)
  set p := minpoly F T with hpdef
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  have hkey : T * aeval T p.divX + algebraMap F _ (p.coeff 0) = 0 := by
    have h0 : aeval T p = 0 := minpoly.aeval F T
    have e : aeval T p = T * aeval T p.divX + algebraMap F _ (p.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add p, mul_comm p.divX X]
      simp only [map_add (f := _), map_mul, aeval_X, aeval_C]
    rw [← e, h0]
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    rw [hc, map_zero, add_zero] at hkey
    have hq : aeval T p.divX = 0 := by
      exact hTu.mul_right_eq_zero.1 hkey
    have hne : p.divX ≠ 0 := by
      intro h
      rw [divX_eq_zero_iff, hc, map_zero] at h
      exact hp0 h
    have hle := minpoly.degree_le_of_ne_zero F T hne hq
    exact absurd (degree_divX_lt hp0) (not_lt.2 hle)
  have hone : (1 : Matrix (Fin m) (Fin m) K) = (-(p.coeff 0)⁻¹) • (T * aeval T p.divX) := by
    rw [eq_neg_of_add_eq_zero_left hkey, smul_neg, neg_smul, neg_neg, Algebra.smul_def,
      ← map_mul, inv_mul_cancel₀ hc, map_one]
  rw [hone]
  exact S.smul_mem _ (hmul _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicAutomorphismUnique
section
namespace GlobalTheory

open Polynomial

theorem denseRange_of_isAlgClosed_padicAlgCl (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l) : DenseRange j := by
  rw [Metric.denseRange_iff]
  intro a δ δpos
  haveI : CharZero Ω := j.charZero
  have hint : IsIntegral ℚ_[l] a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  set f : ℚ_[l][X] := minpoly ℚ_[l] a with hf
  have fmon : f.Monic := minpoly.monic hint
  have fnatdeg0 : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have fa0 : f.aeval a = 0 := minpoly.aeval _ _
  have hi : DenseRange (algebraMap ℚ ℚ_[l]) := Padic.denseRange_ratCast l
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity
  have he : (g.map (algebraMap ℚ ℚ_[l])).map (algebraMap ℚ_[l] (PadicAlgCl l))
      = (g.map (algebraMap ℚ Ω)).map j := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  rw [Polynomial.aroots_def, he, Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨c, -, hc⟩ := hb
  exact ⟨c, by rw [hc, dist_eq_norm]; exact hab⟩

theorem padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l)
      (σ τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), (∀ x, σ (j x) = τ (j x)) → σ = τ := by
  intro l _ Ω _ _ j σ τ h
  have hc : ∀ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, Continuous g := fun g =>
    (AddMonoidHomClass.isometry_of_norm (g : PadicAlgCl l →+* PadicAlgCl l)
      fun x => (spectralNorm_eq_of_equiv g x).symm).continuous
  have := (denseRange_of_isAlgClosed_padicAlgCl l Ω j).equalizer (hc σ) (hc τ) (funext h)
  exact AlgEquiv.ext fun x => congrFun this x

end GlobalTheory
end

