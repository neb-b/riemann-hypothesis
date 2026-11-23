module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LinearIndependentRingHomCompIff
section
namespace GlobalTheory

theorem linearIndependent_ringHom_comp_iff {A F : Type} [CommRing A] [Field F] (φ : A →+* F)
    (hφ : Function.Injective φ) {ι μ : Type} [Finite μ] (c : ι → μ → A) :
    LinearIndependent F (fun i m => φ (c i m)) ↔ LinearIndependent A c := by
  letI : Algebra A F := φ.toAlgebra
  haveI : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).2 hφ
  exact linearIndependent_algebraMap_comp_iff (R := A) (S := F) (v := c)

theorem finrank_span_ringHom_comp_le {A F F' : Type} [CommRing A] [Field F] [Field F']
    (φ : A →+* F) (ψ : A →+* F') (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    {ι μ : Type} [Finite ι] [Finite μ] (c : ι → μ → A) :
    Module.finrank F (Submodule.span F (Set.range fun i m => φ (c i m))) ≤
      Module.finrank F' (Submodule.span F' (Set.range fun i m => ψ (c i m))) := by
  obtain ⟨κ, a, ha, hs, hl⟩ := exists_linearIndependent' F (fun i m => φ (c i m))
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have h1 : LinearIndependent A (fun k => c (a k)) :=
    (linearIndependent_ringHom_comp_iff φ hφ (fun k => c (a k))).1 hl
  have h2 : LinearIndependent F' (fun k m => ψ (c (a k) m)) :=
    (linearIndependent_ringHom_comp_iff ψ hψ (fun k => c (a k))).2 h1
  rw [← hs, finrank_span_eq_card hl, ← finrank_span_eq_card h2]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  exact ⟨a k, rfl⟩

theorem finrank_span_ringHom_comp_eq {A F F' : Type} [CommRing A] [Field F] [Field F']
    (φ : A →+* F) (ψ : A →+* F') (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    {ι μ : Type} [Finite ι] [Finite μ] (c : ι → μ → A) :
    Module.finrank F (Submodule.span F (Set.range fun i m => φ (c i m))) =
      Module.finrank F' (Submodule.span F' (Set.range fun i m => ψ (c i m))) :=
  le_antisymm (finrank_span_ringHom_comp_le φ ψ hφ hψ c)
    (finrank_span_ringHom_comp_le ψ φ hψ hφ c)

theorem mem_span_iff_finrank_option_eq {F V ι : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (v : Option ι → V) :
    v none ∈ Submodule.span F (Set.range fun i => v (some i)) ↔
      Module.finrank F (Submodule.span F (Set.range fun i => v (some i))) =
        Module.finrank F (Submodule.span F (Set.range v)) := by
  have hle : Submodule.span F (Set.range fun i => v (some i)) ≤ Submodule.span F (Set.range v) := by
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨some k, rfl⟩
  constructor
  · intro h
    have : Submodule.span F (Set.range fun i => v (some i)) = Submodule.span F (Set.range v) := by
      refine le_antisymm hle (Submodule.span_le.2 ?_)
      rintro _ ⟨_ | k, rfl⟩
      · exact h
      · exact Submodule.subset_span ⟨k, rfl⟩
    rw [this]
  · intro h
    rw [Submodule.eq_of_le_of_finrank_eq hle h]
    exact Submodule.subset_span ⟨none, rfl⟩

theorem rank_indep_mem_embedding_invariant :
    ∀ (A F F' : Type) [CommRing A] [Field F] [Field F'] (φ : A →+* F) (ψ : A →+* F'), Function.Injective φ → Function.Injective ψ → ∀ (ι μ : Type) [Fintype ι] [Fintype μ] (c : ι → μ → A), (LinearIndependent F (fun i m => φ (c i m)) ↔ LinearIndependent F' (fun i m => ψ (c i m))) ∧ (∀ q : μ → A, (fun m => φ (q m)) ∈ Submodule.span F (Set.range fun i m => φ (c i m)) ↔ (fun m => ψ (q m)) ∈ Submodule.span F' (Set.range fun i m => ψ (c i m))) ∧ Module.finrank F (Submodule.span F (Set.range fun i m => φ (c i m))) = Module.finrank F' (Submodule.span F' (Set.range fun i m => ψ (c i m))) := by
  intro A F F' _ _ _ φ ψ hφ hψ ι μ _ _ c
  refine ⟨?_, fun q => ?_, finrank_span_ringHom_comp_eq φ ψ hφ hψ c⟩
  · rw [linearIndependent_ringHom_comp_iff φ hφ, linearIndependent_ringHom_comp_iff ψ hψ]
  · let d : Option ι → μ → A := fun o => o.elim q c
    have h1 := mem_span_iff_finrank_option_eq (F := F) (fun o m => φ (d o m))
    have h2 := mem_span_iff_finrank_option_eq (F := F') (fun o m => ψ (d o m))
    have e1 := finrank_span_ringHom_comp_eq φ ψ hφ hψ c
    have e2 := finrank_span_ringHom_comp_eq φ ψ hφ hψ d
    refine h1.trans (Iff.trans ?_ h2.symm)
    rw [e2]
    exact e1 ▸ Iff.rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogExpMulLeOfGeneratorSupBound
section
namespace GlobalTheory

private theorem log_one_add_le_log_two_add_of_log_le (x M : ℝ) (hx : 0 < x) (hM : 0 ≤ M)
    (h : Real.log x ≤ M) : Real.log (1 + x) ≤ Real.log 2 + M := by
  rcases le_or_gt x 1 with h1 | h1
  · have : Real.log (1 + x) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
    linarith
  · have : Real.log (1 + x) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hx.ne'] at this
    linarith


set_option maxHeartbeats 800000 in
theorem log_exp_mul_le_of_generator_sup_bound : ∀ (f r n d : ℕ) (L ℓ a rd lam t c S v p1 : ℝ), 2 ≤ L → 1 ≤ f → 1 ≤ r → r ≤ n → (d : ℝ) ≤ a → Real.log (1 + a) ≤ 2 * L → Real.log n ≤ L → Real.log f ≤ 2 * L → 1 ≤ rd → Real.log rd ≤ 2 * L → 0 < lam → Real.log (1 / lam ^ 2) ≤ 80 * L → 0 < t → 0 ≤ ℓ → 0 ≤ p1 → p1 ≤ Real.exp ℓ → 0 ≤ c → c ≤ Real.exp (f * r * n * L) → 0 ≤ S → S ≤ 2 * v → v ≤ c * (p1 * (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (f * r : ℕ) * n) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd) / (Real.sqrt Real.pi * lam)) ^ (f * r * n)) → Real.log (Real.exp (-((d : ℝ) / 2) * Real.log (Real.pi * t)) * S) ≤ ℓ + 10 * L * a + 200 * f * r * n * L := by
  intro f r n d L ℓ a rd lam t c S v p1 hL hf hr hrn hda ha hn hfL hrd hrdL hlam hlamL ht hℓ hp1
    hp1ℓ hc hcL hS hSv hv
  have hf' : 0 < f := by omega
  have hr' : 0 < r := by omega
  have hn' : 0 < n := by omega
  have hf0 : (0:ℝ) < f := by exact_mod_cast hf'
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr'
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn'
  have hrd0 : (0:ℝ) < rd := by linarith
  have hfr0 : (0:ℝ) < ((f * r : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hf' hr'
  have hrnR : (r:ℝ) ≤ n := by exact_mod_cast hrn
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have ha0 : 0 ≤ a := hd0.trans hda
  have hK1 : (1:ℝ) ≤ (f:ℝ) * r * n := by
    have h1 : 1 ≤ f * r * n := Nat.mul_pos (Nat.mul_pos hf' hr') hn'
    exact_mod_cast h1
  have hlog2 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hsqpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hsq1 : 0 < Real.sqrt (2 * ((f * r : ℕ) : ℝ) * n) := Real.sqrt_pos.mpr (by positivity)
  have hfp : 0 < (f : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hf0 _
  set X := 4 * Real.sqrt (2 * ((f * r : ℕ) : ℝ) * n) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)
    / (Real.sqrt Real.pi * lam) with hX
  have hX0 : 0 < X := by positivity
  have hlogX : Real.log X ≤ 3.5 * Real.log 2 + 49 * L := by
    have e1 : Real.log (Real.sqrt (2 * ((f * r : ℕ) : ℝ) * n))
        = (Real.log 2 + Real.log f + Real.log r + Real.log n) / 2 := by
      rw [Real.log_sqrt (by positivity)]
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
      ring
    have e2 : Real.log (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)
        = Real.log 2 + 3 / 2 * Real.log f + 2 * Real.log n + Real.log rd := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_rpow hf0, Real.log_pow]
      push_cast
      ring
    have e3 : Real.log (Real.sqrt Real.pi * lam) = Real.log Real.pi / 2 + Real.log lam := by
      rw [Real.log_mul hsqpi.ne' hlam.ne', Real.log_sqrt hpi.le]
    have e4 : Real.log (1 / lam ^ 2) = -2 * Real.log lam := by
      rw [one_div, Real.log_inv, Real.log_pow]
      push_cast
      ring
    have e5 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have hlr : Real.log r ≤ Real.log n := Real.log_le_log hr0 hrnR
    have hlogf0 : 0 ≤ Real.log f := Real.log_nonneg (by exact_mod_cast hf)
    have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
    rw [hX, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), e1, e2, e3, e5]
    rw [e4] at hlamL
    nlinarith
  have hC : Real.log (1 + X) ≤ 55 * L := by
    have := log_one_add_le_log_two_add_of_log_le X (3.5 * Real.log 2 + 49 * L) hX0
      (by nlinarith) hlogX
    nlinarith
  have hRHS0 : 0 ≤ ℓ + 10 * L * a + 200 * f * r * n * L := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ L) ha0,
      mul_nonneg (by linarith : (0:ℝ) ≤ (f:ℝ) * r * n) (by linarith : (0:ℝ) ≤ L)]
  rcases hS.eq_or_lt with hS0 | hSpos
  · rw [← hS0, mul_zero, Real.log_zero]
    exact hRHS0
  set E := (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) with hEdef
  have hE : 0 < E ∧ Real.log E - (d / 2) * Real.log (Real.pi * t) ≤ 10 * L * a := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp only [hEdef, Nat.cast_zero, zero_div, Real.rpow_zero, Real.log_one, zero_mul, sub_zero]
      exact ⟨one_pos, by nlinarith⟩
    · have hdR : (0:ℝ) < d := by exact_mod_cast hd
      have hB : 0 < Real.pi * Real.exp 1 * t * d := by positivity
      refine ⟨Real.rpow_pos_of_pos hB _, ?_⟩
      rw [hEdef, Real.log_rpow hB, Real.log_mul (by positivity) hdR.ne',
        Real.log_mul (by positivity) ht.ne', Real.log_mul hpi.ne' (Real.exp_pos 1).ne',
        Real.log_mul hpi.ne' ht.ne', Real.log_exp]
      have hld : Real.log d ≤ 2 * L :=
        (Real.log_le_log hdR (by linarith)).trans ha
      nlinarith [mul_le_mul_of_nonneg_left hld (by linarith : (0:ℝ) ≤ d / 2),
        mul_nonneg (by linarith : (0:ℝ) ≤ a - d) (by linarith : (0:ℝ) ≤ 1 + 2 * L),
        mul_nonneg ha0 (by linarith : (0:ℝ) ≤ L - 2)]
  obtain ⟨hE0, hEb⟩ := hE
  have hvpos : 0 < v := by linarith
  have hcpos : 0 < c := by
    rcases hc.eq_or_lt with h | h
    · rw [← h, zero_mul] at hv
      linarith
    · exact h
  have hp1pos : 0 < p1 := by
    rcases hp1.eq_or_lt with h | h
    · rw [← h, zero_mul, zero_mul, zero_mul, mul_zero] at hv
      linarith
    · exact h
  have hsq2 : 0 < Real.sqrt 2 := by positivity
  have hC0 : 0 < 1 + X := by linarith
  have hprod : Real.log (c * (p1 * E * Real.sqrt 2 * (1 + X) ^ (f * r * n)))
      = Real.log c + Real.log p1 + Real.log E + Real.log 2 / 2
        + ((f:ℝ) * r * n) * Real.log (1 + X) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_sqrt (by norm_num)]
    push_cast
    ring
  have hlv : Real.log v ≤ Real.log (c * (p1 * E * Real.sqrt 2 * (1 + X) ^ (f * r * n))) :=
    Real.log_le_log hvpos hv
  have hlS : Real.log S ≤ Real.log 2 + Real.log v := by
    rw [← Real.log_mul (by norm_num) hvpos.ne']
    exact Real.log_le_log hSpos hSv
  have hlc : Real.log c ≤ (f:ℝ) * r * n * L := by
    have := Real.log_le_log hcpos hcL
    rwa [Real.log_exp] at this
  have hlp : Real.log p1 ≤ ℓ := by
    have := Real.log_le_log hp1pos hp1ℓ
    rwa [Real.log_exp] at this
  have hKC : ((f:ℝ) * r * n) * Real.log (1 + X) ≤ ((f:ℝ) * r * n) * (55 * L) :=
    mul_le_mul_of_nonneg_left hC (by linarith)
  have hKL : 2 ≤ ((f:ℝ) * r * n) * L := by nlinarith
  rw [Real.log_mul (Real.exp_pos _).ne' hSpos.ne', Real.log_exp]
  rw [hprod] at hlv
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogShortFamilyNumbersLe
section
namespace GlobalTheory

theorem log_shortFamilyNumbers_le : ∀ (N n a f : ℕ) (rd L : ℝ), 1 ≤ N → N ≤ n → 1 ≤ a → 1 ≤ f → 1 ≤ rd → 2 ≤ L → Real.log rd ≤ 2 * L → Real.log f ≤ 2 * L → Real.log (1 + a) ≤ 2 * L → Real.log n ≤ L → Real.log (((N : ℝ) * Real.sqrt n * ((N + 1).factorial * ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)) ^ (2 * N + 1))) ^ a) ≤ 140 * N * L * a := by
  intro N n a f rd L hN hNn ha hf hrd hL h1 h2 h3 h4
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNn' : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ n := hN'.trans hNn'
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp L := ⟨_, rfl⟩
  have hE3 : 3 ≤ E := by have := Real.add_one_le_exp L; linarith
  have hE1 : 1 ≤ E := by linarith
  have hE2 : Real.exp (2 * L) = E ^ 2 := by rw [hE, ← Real.exp_nat_mul]; norm_num
  have bn : (n : ℝ) ≤ E := by rw [hE]; exact (Real.log_le_iff_le_exp (by linarith)).1 h4
  have bf : (f : ℝ) ≤ E ^ 2 := by rw [← hE2]; exact (Real.log_le_iff_le_exp (by linarith)).1 h2
  have brd : rd ≤ E ^ 2 := by rw [← hE2]; exact (Real.log_le_iff_le_exp (by linarith)).1 h1
  have ba : (a : ℝ) ≤ E ^ 2 := by
    have : (1 + a : ℝ) ≤ E ^ 2 := by
      rw [← hE2]; exact (Real.log_le_iff_le_exp (by linarith)).1 h3
    linarith
  have bN : (N : ℝ) ≤ E := hNn'.trans bn
  have b2 : (2 : ℝ) ≤ E := by linarith
  have b2N : (2 * N + 1 : ℝ) ≤ E ^ 2 := by nlinarith
  have bN1 : (N + 1 : ℝ) ≤ E ^ 2 := by nlinarith
  have bsq : Real.sqrt n ≤ E := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have bf32 : (f : ℝ) ^ ((3 : ℝ) / 2) ≤ (E ^ 2) ^ 2 := by
    calc (f : ℝ) ^ ((3 : ℝ) / 2) ≤ (f : ℝ) ^ ((2 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hf' (by norm_num)
      _ = (f : ℝ) ^ 2 := Real.rpow_natCast _ _
      _ ≤ (E ^ 2) ^ 2 := by gcongr
  have bfact : ((N + 1).factorial : ℝ) ≤ E ^ (4 * N) := by
    calc ((N + 1).factorial : ℝ) ≤ (((N + 1) ^ (N + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.factorial_le_pow (N + 1)
      _ = (N + 1 : ℝ) ^ (N + 1) := by push_cast; rfl
      _ ≤ (E ^ 2) ^ (N + 1) := by gcongr
      _ = E ^ (2 * (N + 1)) := by rw [← pow_mul]
      _ ≤ E ^ (4 * N) := pow_le_pow_right₀ hE1 (by omega)
  have binner : ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd) : ℝ)
      ≤ E ^ 17 := by
    calc ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd) : ℝ)
        ≤ (E * E ^ 2 * E) * (E ^ 2 * E ^ 2) * (E * (E ^ 2) ^ 2 * E ^ 2 * E ^ 2) := by gcongr
      _ = E ^ 17 := by ring
  have hpos : (0 : ℝ) < (N : ℝ) * Real.sqrt n * ((N + 1).factorial * ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)) ^ (2 * N + 1)) := by
    have : (0 : ℝ) < N := by linarith
    have : (0 : ℝ) < n := by linarith
    have : (0 : ℝ) < a := by linarith
    have : (0 : ℝ) < f := by linarith
    have : (0 : ℝ) < rd := by linarith
    positivity
  have hle : (N : ℝ) * Real.sqrt n * ((N + 1).factorial * ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)) ^ (2 * N + 1)) ≤ E ^ (140 * N) := by
    calc _ ≤ E * E * (E ^ (4 * N) * (E ^ 17) ^ (2 * N + 1)) := by gcongr
      _ = E ^ (2 + 4 * N + 17 * (2 * N + 1)) := by ring
      _ ≤ E ^ (140 * N) := pow_le_pow_right₀ hE1 (by omega)
  rw [Real.log_pow]
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_pow, hE, Real.log_exp] at hlog
  push_cast at hlog
  calc _ ≤ (a : ℝ) * (140 * N * L) := by gcongr
    _ = _ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowAddGenericRowAddTerm
section
open MvPolynomial

namespace GlobalTheory

section RowAdd

variable {K σ ι : Type*} [Field K] [DecidableEq σ] [Fintype ι]

noncomputable def rowAddTerm (K : Type*) [Field K] (u w : ι → σ) (s : σ) : MvPolynomial σ K :=
  ∑ k, if s = w k then X (u k) else 0

noncomputable def rowAddGeneric (u w : ι → σ) :
    MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun s => Polynomial.C (X s) + Polynomial.X * Polynomial.C (rowAddTerm K u w s)

theorem eval_rowAddGeneric (u w : ι → σ) (t : K) (P : MvPolynomial σ K) :
    Polynomial.eval (C t) (rowAddGeneric u w P) =
      bind₁ (fun s => X s + ∑ k, if s = w k then C t * X (u k) else 0) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowAddGeneric, Polynomial.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul]
    congr 1
    simp [rowAddGeneric, rowAddTerm, Finset.mul_sum, Polynomial.eval_finsetSum]
    simp only [mul_comm]

theorem eval_zero_rowAddGeneric (u w : ι → σ) (P : MvPolynomial σ K) :
    Polynomial.eval 0 (rowAddGeneric u w P) = P := by
  have h := eval_rowAddGeneric u w (0 : K) P
  simpa using h

theorem rowAddGeneric_rowAddTerm (u w : ι → σ) (huw : ∀ k l, u k ≠ w l) (s : σ) :
    rowAddGeneric u w (rowAddTerm K u w s) = Polynomial.C (rowAddTerm K u w s) := by
  have h0 : ∀ k, rowAddTerm K u w (u k) = 0 := fun k => by
    simp [rowAddTerm, huw k]
  conv_lhs => rw [rowAddTerm]
  conv_rhs => rw [rowAddTerm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · simp [rowAddGeneric, h0]
  · simp

theorem sum_X_mul_pderiv_X (u w : ι → σ) (s : σ) :
    ∑ k, X (u k) * pderiv (w k) (X s : MvPolynomial σ K) = rowAddTerm K u w s := by
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · simp [h]
  · simp [pderiv_X_of_ne h]

theorem derivative_rowAddGeneric (u w : ι → σ) (huw : ∀ k l, u k ≠ w l)
    (P : MvPolynomial σ K) :
    Polynomial.derivative (rowAddGeneric u w P) =
      rowAddGeneric u w (∑ k, X (u k) * pderiv (w k) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowAddGeneric, Polynomial.algebraMap_apply]
  | add p q hp hq =>
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib, hp, hq]
  | mul_X p s hp =>
    have h : ∑ k, X (u k) * pderiv (w k) (p * X s) =
        (∑ k, X (u k) * pderiv (w k) p) * X s + p * rowAddTerm K u w s := by
      rw [← sum_X_mul_pderiv_X, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [h, map_add (f := _), map_mul (rowAddGeneric u w), map_mul (rowAddGeneric u w),
      map_mul (rowAddGeneric u w), Polynomial.derivative_mul, hp,
      rowAddGeneric_rowAddTerm u w huw]
    have hX : Polynomial.derivative (rowAddGeneric u w (X s : MvPolynomial σ K)) =
        Polynomial.C (rowAddTerm K u w s) := by
      simp [rowAddGeneric]
    rw [hX]

end RowAdd


set_option linter.unusedVariables false in
theorem rowAdd_invariant_iff {K σ ι : Type*} [Field K] [CharZero K] [DecidableEq σ] [Fintype ι]
    (u w : ι → σ) (hw : Function.Injective w)
    (huw : ∀ k l, u k ≠ w l) (P : MvPolynomial σ K) :
    List.TFAE [∀ t : ℤ, bind₁ (fun s => X s + ∑ k, if s = w k then C (t : K) * X (u k) else 0) P = P,
      ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = w k then C t * X (u k) else 0) P = P,
      ∑ k, X (u k) * pderiv (w k) P = 0] := by
  tfae_have 2 → 1 := fun h t => h t
  tfae_have 1 → 3 := by
    intro h
    have hc : rowAddGeneric u w P = Polynomial.C P := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hinj : Function.Injective fun t : ℤ => (C (t : K) : MvPolynomial σ K) :=
        fun a b hab => Int.cast_injective (C_injective σ K hab)
      refine Set.infinite_of_injective_forall_mem hinj fun t => ?_
      simp only [Set.mem_ofPred_eq, Polynomial.eval_C]
      rw [eval_rowAddGeneric, h t]
    have hd := derivative_rowAddGeneric u w huw P
    rw [hc, Polynomial.derivative_C] at hd
    rw [← eval_zero_rowAddGeneric u w (∑ k, X (u k) * pderiv (w k) P), ← hd, Polynomial.eval_zero]
  tfae_have 3 → 2 := by
    intro h t
    have hd := derivative_rowAddGeneric u w huw P
    rw [h, map_zero] at hd
    have hc := Polynomial.eq_C_of_derivative_eq_zero hd
    rw [← eval_rowAddGeneric]
    conv_rhs => rw [← eval_zero_rowAddGeneric u w P]
    rw [hc, Polynomial.eval_C, Polynomial.eval_C]
  tfae_finish

end GlobalTheory
end

