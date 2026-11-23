module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0009

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.GhostComponentG
section
noncomputable section

namespace PI.WittUnramWork

open WittVector Finset

variable {p : ℕ} [hp : Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

section Restrict

def sigF (σ : Qq ≃+* Qq) (hσ : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y))
    (x : W) : W :=
  x ^ p + (p : W) * (hσ x).choose

theorem sigF_spec (σ : Qq ≃+* Qq)
    (hσ : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) (x : W) :
    algebraMap W Qq (sigF σ hσ x) = σ (algebraMap W Qq x) := (hσ x).choose_spec.symm

def sigW (hinj : Function.Injective (algebraMap W Qq)) (σ : Qq ≃+* Qq)
    (hσ : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) : W →+* W where
  toFun := sigF σ hσ
  map_one' := hinj (by rw [sigF_spec]; simp)
  map_mul' x y := hinj (by simp only [sigF_spec, map_mul])
  map_zero' := hinj (by rw [sigF_spec]; simp)
  map_add' x y := hinj (by simp only [sigF_spec, map_add (f := _)])

theorem sigW_spec (hinj : Function.Injective (algebraMap W Qq)) (σ : Qq ≃+* Qq)
    (hσ : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) (x : W) :
    algebraMap W Qq (sigW hinj σ hσ x) = σ (algebraMap W Qq x) := sigF_spec σ hσ x

theorem sigW_lift (hinj : Function.Injective (algebraMap W Qq)) (σ : Qq ≃+* Qq)
    (hσ : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) (x : W) :
    ∃ y : W, sigW hinj σ hσ x = x ^ p + (p : W) * y := ⟨(hσ x).choose, rfl⟩

end Restrict

section Dwork

variable (p Qq) [Invertible (p : Qq)] (F : W →+* W)

def G (x : W) : WittVector p Qq :=
  (ghostEquiv p Qq).symm (fun n => algebraMap W Qq ((F^[n]) x))

theorem ghostComponent_G (x : W) (n : ℕ) :
    ghostComponent n (G p Qq F x) = algebraMap W Qq ((F^[n]) x) := by
  have h := congrFun ((ghostEquiv p Qq).apply_symm_apply (fun n => algebraMap W Qq ((F^[n]) x))) n
  rw [← WittVector.ghostMap_apply, ← WittVector.ghostEquiv_coe p Qq]
  exact h

theorem ghost_sum_G (x : W) (k : ℕ) :
    ∑ i ∈ range (k + 1), (p : Qq) ^ i * (G p Qq F x).coeff i ^ p ^ (k - i) = algebraMap W Qq ((F^[k]) x) := by
  rw [← ghostComponent_G p Qq F x k, WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, MvPolynomial.aeval_X]

theorem G_coeff_zero (x : W) : (G p Qq F x).coeff 0 = algebraMap W Qq x := by
  have h := ghost_sum_G p Qq F x 0
  simpa using h

theorem G_add (x y : W) : G p Qq F (x + y) = G p Qq F x + G p Qq F y := by
  have hit : ∀ n, (F^[n]) = ⇑(F ^ n) := fun n => (RingHom.coe_pow F n).symm
  simp only [G]
  rw [← map_add (f := _)]
  congr 1
  funext n
  simp only [Pi.add_apply, hit, RingHom.map_add]

theorem G_mul (x y : W) : G p Qq F (x * y) = G p Qq F x * G p Qq F y := by
  have hit : ∀ n, (F^[n]) = ⇑(F ^ n) := fun n => (RingHom.coe_pow F n).symm
  simp only [G]
  rw [← map_mul]
  congr 1
  funext n
  simp only [Pi.mul_apply, hit, RingHom.map_mul]

theorem G_one : G p Qq F (1 : W) = 1 := by
  have hit : ∀ n, (F^[n]) = ⇑(F ^ n) := fun n => (RingHom.coe_pow F n).symm
  simp only [G]
  rw [← map_one (ghostEquiv p Qq).symm]
  congr 1
  funext n
  simp only [Pi.one_apply, hit, RingHom.map_one]

theorem G_zero : G p Qq F (0 : W) = 0 := by
  have hit : ∀ n, (F^[n]) = ⇑(F ^ n) := fun n => (RingHom.coe_pow F n).symm
  simp only [G]
  rw [← map_zero (ghostEquiv p Qq).symm]
  congr 1
  funext n
  simp only [Pi.zero_apply, hit, RingHom.map_zero]

theorem G_frob (x : W) : G p Qq F (F x) = frobenius (G p Qq F x) := by
  apply (ghostEquiv p Qq).injective
  funext n
  have h1 : (ghostEquiv p Qq) (G p Qq F (F x)) n = ghostComponent n (G p Qq F (F x)) := by
    rw [← WittVector.ghostMap_apply, ← WittVector.ghostEquiv_coe p Qq]
    rfl
  have h2 : (ghostEquiv p Qq) (frobenius (G p Qq F x)) n = ghostComponent n (frobenius (G p Qq F x)) := by
    rw [← WittVector.ghostMap_apply, ← WittVector.ghostEquiv_coe p Qq]
    rfl
  rw [h1, h2, WittVector.ghostComponent_frobenius, ghostComponent_G, ghostComponent_G,
    ← Function.iterate_succ_apply]

variable (hF : ∀ x : W, ∃ y : W, F x = x ^ p + (p : W) * y)
include hF

theorem G_coeff_integral (hinj : Function.Injective (algebraMap W Qq)) (x : W) (n : ℕ) :
    ∃ a : W, (G p Qq F x).coeff n = algebraMap W Qq a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | k
  · exact ⟨x, G_coeff_zero p Qq F x⟩
  choose! b hb using ih
  have hbk : ∀ i ∈ range (k + 1), (G p Qq F x).coeff i = algebraMap W Qq (b i) :=
    fun i hi => hb i (by simp at hi; omega)
  have hk : (F^[k]) x = ∑ i ∈ range (k + 1), (p : W) ^ i * b i ^ p ^ (k - i) := by
    apply hinj
    rw [← ghost_sum_G p Qq F x k]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, map_natCast]
    exact Finset.sum_congr rfl fun i hi => by rw [hbk i hi]
  have hk1 : (F^[k + 1]) x = ∑ i ∈ range (k + 1), (p : W) ^ i * F (b i) ^ p ^ (k - i) := by
    rw [Function.iterate_succ_apply', hk]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, map_natCast]
  have hdvd : (p : W) ^ (k + 1) ∣
      (F^[k + 1]) x - ∑ i ∈ range (k + 1), (p : W) ^ i * b i ^ p ^ (k + 1 - i) := by
    rw [hk1, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i hi => ?_
    have hi' : i ≤ k := by simp at hi; omega
    obtain ⟨y, hy⟩ := hF (b i)
    have h1 : (p : W) ∣ F (b i) - b i ^ p := ⟨y, by rw [hy]; ring⟩
    have h2 := dvd_sub_pow_of_dvd_sub h1 (k - i)
    rw [← pow_mul, ← pow_succ'] at h2
    have e : k + 1 - i = k - i + 1 := by omega
    rw [e, ← mul_sub, show (p : W) ^ (k + 1) = (p : W) ^ i * (p : W) ^ (k - i + 1) by
      rw [← pow_add]; congr 1; omega]
    exact mul_dvd_mul_left _ h2
  obtain ⟨d, hd⟩ := hdvd
  refine ⟨d, ?_⟩
  have hs := ghost_sum_G p Qq F x (k + 1)
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one] at hs
  have hsum : ∑ i ∈ range (k + 1), (p : Qq) ^ i * (G p Qq F x).coeff i ^ p ^ (k + 1 - i) =
      algebraMap W Qq (∑ i ∈ range (k + 1), (p : W) ^ i * b i ^ p ^ (k + 1 - i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, map_natCast]
    exact Finset.sum_congr rfl fun i hi => by rw [hbk i hi]
  rw [hsum] at hs
  have hpk : (p : Qq) ^ (k + 1) ≠ 0 := pow_ne_zero _ (Invertible.ne_zero (p : Qq))
  have key : (p : Qq) ^ (k + 1) * (G p Qq F x).coeff (k + 1) =
      (p : Qq) ^ (k + 1) * algebraMap W Qq d := by
    have e2 : algebraMap W Qq ((F^[k + 1]) x -
        ∑ i ∈ range (k + 1), (p : W) ^ i * b i ^ p ^ (k + 1 - i)) =
        (p : Qq) ^ (k + 1) * algebraMap W Qq d := by
      rw [hd, map_mul, map_pow, map_natCast]
    rw [← e2, map_sub, ← hs]
    ring
  exact mul_left_cancel₀ hpk key

def sFun (hinj : Function.Injective (algebraMap W Qq)) (x : W) : WittVector p W :=
  WittVector.mk p fun n => (G_coeff_integral p Qq F hF hinj x n).choose

theorem map_sFun (hinj : Function.Injective (algebraMap W Qq)) (x : W) :
    WittVector.map (algebraMap W Qq) (sFun p Qq F hF hinj x) = G p Qq F x := by
  ext n
  rw [WittVector.map_coeff]
  exact (G_coeff_integral p Qq F hF hinj x n).choose_spec.symm

def sHom (hinj : Function.Injective (algebraMap W Qq)) : W →+* WittVector p W where
  toFun := sFun p Qq F hF hinj
  map_one' := map_injective _ hinj (by rw [map_sFun, map_one, G_one])
  map_mul' x y := map_injective _ hinj (by rw [map_mul, map_sFun, map_sFun, map_sFun, G_mul])
  map_zero' := map_injective _ hinj (by rw [map_sFun, map_zero, G_zero])
  map_add' x y := map_injective _ hinj (by rw [map_add (f := _), map_sFun, map_sFun, map_sFun, G_add])

theorem sHom_apply (hinj : Function.Injective (algebraMap W Qq)) (x : W) :
    sHom p Qq F hF hinj x = sFun p Qq F hF hinj x := rfl

private theorem map_frobenius' (f : W →+* Qq) (w : WittVector p W) :
    WittVector.map f (frobenius w) = frobenius (WittVector.map f w) := by
  have key : ∀ P : MvPolynomial ℕ ℤ,
      f (MvPolynomial.aeval w.coeff P) = MvPolynomial.aeval (fun i => f (w.coeff i)) P := by
    intro P
    first
      | exact DFunLike.congr_fun (MvPolynomial.comp_aeval (f := w.coeff) f.toIntAlgHom) P
      | exact DFunLike.congr_fun (MvPolynomial.comp_aeval w.coeff f.toIntAlgHom) P
      | (induction P using MvPolynomial.induction_on with
          | C a => simp [MvPolynomial.aeval_C, algebraMap_int_eq, eq_intCast, map_intCast]
          | add P Q hP hQ => simp only [map_add (f := _), hP, hQ]
          | mul_X P i hP => simp only [map_mul, hP, MvPolynomial.aeval_X])
  ext n
  rw [WittVector.map_coeff, WittVector.coeff_frobenius, WittVector.coeff_frobenius, key]
  congr 1
  try (funext i; exact (WittVector.map_coeff f w i).symm)

theorem sHom_frob (hinj : Function.Injective (algebraMap W Qq)) (x : W) :
    sHom p Qq F hF hinj (F x) = frobenius (sHom p Qq F hF hinj x) := by
  apply WittVector.map_injective _ hinj
  rw [sHom_apply, map_sFun, G_frob, map_frobenius' p Qq F hF (algebraMap W Qq), sHom_apply, map_sFun]

theorem sHom_coeff_zero (hinj : Function.Injective (algebraMap W Qq)) (x : W) :
    (sHom p Qq F hF hinj x).coeff 0 = x := by
  apply hinj
  rw [← G_coeff_zero p Qq F x, ← map_sFun p Qq F hF hinj x, WittVector.map_coeff]
  try rfl

end Dwork

end PI.WittUnramWork
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.PsiStep
section
noncomputable section

namespace PI.WittUnramWork

open WittVector Finset

variable {p : ℕ} [hp : Fact p.Prime] {W k : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field k] [CharP k p] [PerfectRing k p]

theorem psi_injective (ψ : W →+* WittVector p k) (hirr : Irreducible (p : W)) :
    Function.Injective ψ := by
  refine (injective_iff_map_eq_zero ψ).2 ?_
  intro x hx
  by_contra hne
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hirr
  obtain ⟨u, hu⟩ := hn
  have h2 : ψ ((p : W) ^ n) = 0 := by rw [← hu, map_mul, hx, zero_mul]
  rw [map_pow, map_natCast] at h2
  exact pow_ne_zero n (WittVector.p_nonzero p k) h2

theorem psi_step (ψ : W →+* WittVector p k) (res : W →+* k) (hres : Function.Surjective res)
    (h0 : ∀ x, (ψ x).coeff 0 = res x) (w : WittVector p k) :
    ∃ a : W, ∃ b : WittVector p k, w = ψ a + (p : WittVector p k) * b := by
  obtain ⟨a, ha⟩ := hres (w.coeff 0)
  refine ⟨a, ?_⟩
  by_cases hz : w - ψ a = 0
  · exact ⟨0, by rw [mul_zero, add_zero]; exact sub_eq_zero.mp hz⟩
  · obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul (w - ψ a) hz
    have hc : (w - ψ a).coeff 0 = 0 := by
      have h3 := WittVector.add_coeff_zero (ψ a) (w - ψ a)
      rw [show ψ a + (w - ψ a) = w by abel, h0, ha] at h3
      linear_combination -h3
    have hm : m ≠ 0 := by
      rintro rfl
      apply hb0
      rw [pow_zero, one_mul] at hb
      rw [← hb]
      exact hc
    refine ⟨(p : WittVector p k) ^ (m - 1) * b, ?_⟩
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm), ← hb]
    ring

theorem psi_surjective (ψ : W →+* WittVector p k) (res : W →+* k) (hres : Function.Surjective res)
    (h0 : ∀ x, (ψ x).coeff 0 = res x) (hC : IsAdicComplete (Ideal.span {(p : W)}) W) :
    Function.Surjective ψ := by
  intro w
  choose A B hAB using psi_step ψ res hres h0
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → WittVector p k, r 0 = w ∧ ∀ n, r (n + 1) = B (r n) :=
    ⟨fun n => B^[n] w, rfl, fun n => Function.iterate_succ_apply' B n w⟩
  obtain ⟨s, hs0, hss⟩ : ∃ s : ℕ → W, s 0 = 0 ∧ ∀ n, s (n + 1) = s n + A (r n) * (p : W) ^ n :=
    ⟨fun n => ∑ i ∈ Finset.range n, A (r i) * (p : W) ^ i, by simp, fun n => Finset.sum_range_succ _ _⟩
  have hinv : ∀ n, w = ψ (s n) + (p : WittVector p k) ^ n * r n := by
    intro n
    induction n with
    | zero => rw [hs0, hr0, map_zero, pow_zero, one_mul, zero_add]
    | succ n ih =>
      calc w = ψ (s n) + (p : WittVector p k) ^ n * r n := ih
        _ = ψ (s n) + (p : WittVector p k) ^ n * (ψ (A (r n)) + (p : WittVector p k) * B (r n)) := by
          rw [← hAB (r n)]
        _ = ψ (s (n + 1)) + (p : WittVector p k) ^ (n + 1) * r (n + 1) := by
          rw [hss, hrs, map_add (f := _), map_mul, map_pow, map_natCast]
          ring
  have hdiv : ∀ m n, m ≤ n → (p : W) ^ m ∣ s n - s m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hss, add_sub_right_comm]
      exact dvd_add ih (Dvd.dvd.mul_left (pow_dvd_pow _ hmn) _)
  have hI : ∀ n (x : W), x ∈ (Ideal.span {(p : W)} ^ n • ⊤ : Submodule W W) ↔ (p : W) ^ n ∣ x := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := hC.toIsPrecomplete.prec (f := s) (fun {m n} hmn => by
    rw [SModEq.sub_mem, hI]
    exact dvd_sub_comm.mp (hdiv m n hmn))
  have hw : ∀ n, (p : WittVector p k) ^ n ∣ w - ψ L := by
    intro n
    obtain ⟨c, hc⟩ := (hI n _).1 (SModEq.sub_mem.1 (hL n))
    refine ⟨ψ c + r n, ?_⟩
    have h2 : ψ (s n) - ψ L = (p : WittVector p k) ^ n * ψ c := by
      rw [← map_sub, hc, map_mul, map_pow, map_natCast]
    calc w - ψ L = ψ (s n) + (p : WittVector p k) ^ n * r n - ψ L := by rw [← hinv n]
      _ = (p : WittVector p k) ^ n * (ψ c + r n) := by linear_combination h2
  have hzero : w - ψ L = 0 := by
    by_contra hne
    obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul (w - ψ L) hne
    obtain ⟨c, hc⟩ := hw (m + 1)
    rw [hb, pow_succ, mul_assoc] at hc
    have hp : (p : WittVector p k) ^ m ≠ 0 := pow_ne_zero m (WittVector.p_nonzero p k)
    have hbc := mul_left_cancel₀ hp hc
    apply hb0
    rw [hbc]
    first
    | rw [WittVector.mul_coeff_zero, WittVector.coeff_p_zero, zero_mul]
    | simp
  exact ⟨L, (sub_eq_zero.mp hzero).symm⟩

end PI.WittUnramWork
end
end

