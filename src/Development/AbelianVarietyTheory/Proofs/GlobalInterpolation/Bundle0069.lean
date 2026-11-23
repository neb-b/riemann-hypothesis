module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Formalism.GL3MeanSquares.Bundle0002
public import Formalism.CyclotomicNorms.Bundle0001
public import Formalism.LandauZeroFreeBounds.Statement
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceWindowRankConditions
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem nWv_lower (R : Ranks) (s : Scale) :
    10 * R.r * (R.f + R.f * (R.k - 1) ^ 3) ≤ nWv R s := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  have hm : (0 : ℝ) < R.m := by
    have := R.two_le_m
    exact_mod_cast (by omega : 0 < R.m)
  have hmf : (R.m : ℝ) ≤ R.f := by
    have : R.m ≤ R.f := R.m_le_f
    exact_mod_cast this
  have hL : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le
  have hk' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ R.k := by exact_mod_cast hk
    linarith
  have hL2 : 1 ≤ s.L ^ 2 := one_le_pow₀ hL
  have h1 : (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 ≤
      (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by
    rw [le_div_iff₀ hm]
    have hA : (0 : ℝ) ≤ (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 := by positivity
    have hf : (0 : ℝ) ≤ R.f := by positivity
    calc (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 * R.m ≤ (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 * R.f :=
          mul_le_mul_of_nonneg_left hmf hA
      _ = (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL2 (by positivity)
  have h2 := Nat.le_ceil (10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8)
  have h3 : 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3) ≤
      10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : ((10 * R.r * (R.f + R.f * (R.k - 1) ^ 3) : ℕ) : ℝ) ≤ (nWv R s : ℕ) := by
    unfold nWv
    push_cast [Nat.cast_sub hk]
    linarith
  exact_mod_cast h4

theorem nWv_three_lower (R : Ranks) (s : Scale) :
    R.f * R.r * (R.r + 1) ≤ nWv R s ∧ (R.k - 1) * R.f + 2 * R.r ≤ nWv R s ∧
      8 * R.f * R.r + 4 ≤ nWv R s := by
  have h := nWv_lower R s
  have h2 := R.two_le_m
  have h3 := R.m_add_three_le_k
  have hf : 2 ≤ R.f := le_trans h2 R.m_le_f
  have hr : R.r = R.k + R.m - 1 := rfl
  generalize nWv R s = W at h
  generalize R.f = f at *
  generalize R.r = r at *
  obtain ⟨j, hj⟩ : ∃ j, R.k - 1 = j := ⟨_, rfl⟩
  rw [hj] at h ⊢
  have hj1 : 1 ≤ j := by omega
  have hjr : j ≤ r := by omega
  have hrj : r + 1 ≤ 2 * j := by omega
  have hj3 : j ≤ j ^ 3 := Nat.le_self_pow (by norm_num) j
  have hfr : 2 * 2 ≤ f * r := Nat.mul_le_mul hf (by omega)
  have e : 10 * r * (f + f * j ^ 3) = 10 * (f * r) + f * r * (10 * j ^ 3) := by ring
  rw [e] at h
  have a1 : f * r * (r + 1) ≤ f * r * (10 * j ^ 3) := Nat.mul_le_mul_left _ (by omega)
  have a2 : j * f ≤ f * r := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hjr
  have a3 : 2 * r ≤ f * r := Nat.mul_le_mul_right _ hf
  have a4 : 8 * f * r = 8 * (f * r) := by ring
  refine ⟨by omega, by omega, by omega⟩

theorem szRow_nW : SzRow (fun C D L => (nW L C.P.CnW ≤ ((nWv D.R L.sc : ℕ) : ℝ) ∧ ((nWv D.R L.sc : ℕ) : ℝ) < nW L C.P.CnW + 8) ∧ (8 ∣ (nWv D.R L.sc : ℕ)) ∧ (D.R.r + D.R.t = (8 * D.R.f * D.R.r + 4 : ℕ) + (TOv L.sc : ℕ) * (nWv D.R L.sc : ℕ)) ∧ ((TOv L.sc : ℕ) = ⌈L.sc.x ^ C.T.cTO⌉₊) ∧ (Odd (D.R.r + 6 : ℕ)) ∧ (D.R.r + 5 < (D.R.r + 6 : ℕ)) ∧ ((D.R.r + 6 : ℕ) ≤ D.R.r + 7) ∧ (D.R.f * D.R.r * (D.R.r + 1) ≤ (nWv D.R L.sc : ℕ) ∧ (D.R.k - 1) * D.R.f + 2 * D.R.r ≤ (nWv D.R L.sc : ℕ) ∧ (8 * D.R.f * D.R.r + 4 : ℕ) ≤ (nWv D.R L.sc : ℕ))) := by
  intro eps _ _ C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ hV => ?_⟩⟩⟩
  have hW : C.P.CnW = 10 := by
    have hF := hC.1
    unfold FC.Fixed at hF
    tauto
  have hT : C.T.cTO = 377 := hC.2.2.2.2.2.2.2.2.2.1
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) - 1 := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    have : (1 : ℝ) ≤ D.R.k := by exact_mod_cast this
    linarith
  refine ⟨⟨?_, ?_⟩, Dvd.intro _ rfl, hV.ranks.2.2.2, ?_, ?_, by omega, by omega, nWv_three_lower _ _⟩
  · rw [hW]; unfold nW nWv
    have := Nat.le_ceil (10 * (D.R.r : ℝ) * ((D.R.f : ℝ) + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) / 8)
    push_cast
    linarith
  · rw [hW]; unfold nW nWv
    have := Nat.ceil_lt_add_one (a := 10 * (D.R.r : ℝ) * ((D.R.f : ℝ) + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) / 8) (by positivity)
    push_cast
    linarith
  · rw [hT]; rfl
  · obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    exact ⟨a + b + 2, by omega⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceWindowRankLePolyBound
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem nWv_le_zBase_pow_four {D : D7} (L : SizeData₂ D) :
    1 ≤ zBase L ∧ (D.R.f : ℝ) * D.R.m ≤ zBase L ∧ ((nWv D.R L.sc : ℕ) : ℝ) ≤ 28 * zBase L ^ 4 := by
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have h2m := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hm : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by omega
    exact_mod_cast this
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by
    have : D.R.m ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by omega
    exact_mod_cast this
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  unfold nWv zBase
  push_cast
  generalize (D.R.f : ℝ) = f at *
  generalize (D.R.r : ℝ) = r at *
  generalize (D.R.m : ℝ) = m at *
  generalize (D.R.k : ℝ) = k at *
  generalize L.sc.L = l at *
  have hfr : 1 ≤ f * r := one_le_mul_of_one_le_of_one_le hf hr
  have hfrZ : f * r ≤ f * r * l := le_mul_of_one_le_right (by positivity) hL
  have hZ : 1 ≤ f * r * l := hfr.trans hfrZ
  refine ⟨hZ, le_trans (by gcongr) hfrZ, ?_⟩
  have hk0 : 0 ≤ k - 1 := by linarith
  have hk3 : (k - 1) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hk0 (by linarith) 3
  have hc := (Nat.ceil_lt_add_one (a := 10 * r * (f + f ^ 2 * (k - 1) ^ 3 * l ^ 2 / m) / 8) (by positivity)).le
  have a1 : f ^ 2 * (k - 1) ^ 3 * l ^ 2 / m ≤ f ^ 2 * r ^ 3 * l ^ 2 := by
    refine (div_le_self (by positivity) hm).trans ?_
    gcongr
  have a2 : 10 * r * (f + f ^ 2 * (k - 1) ^ 3 * l ^ 2 / m) ≤ 10 * r * (f + f ^ 2 * r ^ 3 * l ^ 2) := by gcongr
  have m0 : 1 ≤ (f * r * l) ^ 4 := one_le_pow₀ hZ
  have m1 : f * r * l ≤ (f * r * l) ^ 4 := le_self_pow₀ hZ (by norm_num)
  have m2 : f ^ 2 * r ^ 4 * l ^ 2 ≤ (f * r * l) ^ 4 := by
    have b1 : f ^ 2 ≤ f ^ 4 := pow_le_pow_right₀ hf (by norm_num)
    have b2 : l ^ 2 ≤ l ^ 4 := pow_le_pow_right₀ hL (by norm_num)
    calc f ^ 2 * r ^ 4 * l ^ 2 ≤ f ^ 4 * r ^ 4 * l ^ 4 := by gcongr
      _ = (f * r * l) ^ 4 := by ring
  have e : 10 * r * (f + f ^ 2 * r ^ 3 * l ^ 2) = 10 * (f * r) + 10 * (f ^ 2 * r ^ 4 * l ^ 2) := by ring
  rw [e] at a2
  linarith

theorem szRow_nW_le_PP : SzRow (fun C D L => ((2 * (D.R.f : ℝ) * D.R.m) ^ 4 * ((nWv D.R L.sc : ℕ) : ℝ) ≤ (C.T.CP * zBase L ^ C.T.eP)) ∧ (((nWv D.R L.sc : ℕ) : ℝ) ≤ (C.T.CP * zBase L ^ C.T.eP))) := by
  intro eps _ _ C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ _ => ?_⟩⟩⟩
  obtain ⟨hZ, hfm, hn⟩ := nWv_le_zBase_pow_four L
  obtain ⟨-, -, -, -, -, -, -, -, heP, -, -, -, -, hCP, -⟩ := hC
  have e : zBase L ^ C.T.eP = zBase L ^ (12 : ℕ) := by
    rw [heP, ← Real.rpow_natCast]; norm_num
  have hP : 1000 * zBase L ^ (12 : ℕ) ≤ C.T.CP * zBase L ^ C.T.eP := by
    rw [e]
    exact mul_le_mul_of_nonneg_right hCP (by positivity)
  have h8 : zBase L ^ 8 ≤ zBase L ^ 12 := pow_le_pow_right₀ hZ (by norm_num)
  have h4 : zBase L ^ 4 ≤ zBase L ^ 12 := pow_le_pow_right₀ hZ (by norm_num)
  have h12 : 0 ≤ zBase L ^ 12 := by positivity
  refine ⟨le_trans ?_ hP, le_trans ?_ hP⟩
  · have ha : 2 * (D.R.f : ℝ) * D.R.m ≤ 2 * zBase L := by linarith
    calc (2 * (D.R.f : ℝ) * D.R.m) ^ 4 * ((nWv D.R L.sc : ℕ) : ℝ)
        ≤ (2 * zBase L) ^ 4 * (28 * zBase L ^ 4) := by gcongr
      _ = 448 * zBase L ^ 8 := by ring
      _ ≤ 1000 * zBase L ^ 12 := by linarith
  · linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaClosed
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.ExplicitFormulaClosed

theorem exists_open_eq_closed (f : ℂ → ℂ) (T : ℝ)
    (hfin : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - 0| ≤ T + 1 ∧ f ρ = 0}.Finite) :
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
      {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - 0| ≤ T ∧ f ρ = 0} =
        {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ f ρ = 0} := by
  have h1 : ∀ᶠ T' in 𝓝[>] T, ∀ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - 0| ≤ T + 1 ∧ f ρ = 0},
      T < |ρ.im| → T' < |ρ.im| := by
    rw [Filter.eventually_all_finite hfin]
    intro ρ _
    by_cases h : T < |ρ.im|
    · exact ((eventually_lt_nhds h).filter_mono nhdsWithin_le_nhds).mono fun _ h' _ => h'
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' h
  have h2 : ∀ᶠ T' in 𝓝[>] T, T' < T + 1 :=
    (eventually_lt_nhds (by linarith)).filter_mono nhdsWithin_le_nhds
  have h3 : ∀ᶠ T' in 𝓝[>] T, T < T' := self_mem_nhdsWithin
  obtain ⟨T', a1, a2, a3⟩ := (h1.and (h2.and h3)).exists
  refine ⟨T', a3.le, a2.le, ?_⟩
  ext ρ
  simp only [Set.mem_setOf_eq, sub_zero] at a1 ⊢
  constructor
  · rintro ⟨b0, b1, b2, b3⟩
    exact ⟨b0, b1, by linarith, b3⟩
  · rintro ⟨b0, b1, b2, b3⟩
    refine ⟨b0, b1, ?_, b3⟩
    by_contra h
    have := a1 ρ ⟨b0, b1, by linarith, b3⟩ (not_le.1 h)
    linarith

theorem explicit_formula_closed : ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.ZeroBand.zeros_band
  refine ⟨C₁ + C₂, fun q _ χ hχ u T hT hu => ?_⟩
  obtain ⟨T', hT1, hT2, hset⟩ := exists_open_eq_closed (DirichletCharacter.LFunction χ) T
    (GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult q χ 0 (T + 1)).1
  have e1 := (h₁ q χ hχ u T hT hu).2
  have e2 := (h₂ q χ hχ u T T' hT hu hT1 hT2).2
  have hz : zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ) =
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ DirichletCharacter.LFunction χ ρ = 0},
        ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ) := by
    rw [← hset]; rfl
  have hF := (GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ DirichletCharacter.LFunction χ ρ = 0} ⊆
      zerosIn χ 0 1 := by
    rintro ρ ⟨b0, b1, b2, b3⟩
    exact ⟨b0, b1, by rw [sub_zero]; exact b2.le, b3⟩
  have hZ : ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧
        DirichletCharacter.LFunction χ ρ = 0},
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ ≤
      zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
    unfold zsumR
    rw [finsum_mem_eq_finite_toFinset_sum _ hF, finsum_mem_eq_finite_toFinset_sum _ (hF.subset hsub)]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun ρ _ => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_subset_toFinset.2 hsub)
        fun ρ _ _ => by positivity)
    rw [mul_one_div]; rfl
  have hZ0 : 0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hB : 0 ≤ Real.log (q * u) := Real.log_nonneg (by nlinarith)
  have key : ∀ P Z Z' : ℂ, ‖P + Z'‖ ≤ ‖P + Z‖ + ‖Z' - Z‖ := by
    intro P Z Z'
    have : P + Z' = (P + Z) + (Z' - Z) := by ring
    rw [this]
    exact norm_add_le _ _
  rw [hz]
  refine (key _ _ _).trans ((add_le_add e1 e2).trans ?_)
  generalize (∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧
        DirichletCharacter.LFunction χ ρ = 0},
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) = Z at hZ ⊢
  generalize zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) = Z' at hZ hZ0 ⊢
  generalize u * Real.log (q * u * T) ^ 2 / T = A
  generalize Real.log (q * u) = B at hB ⊢
  have a1 : C₁ * (A + B + Z) ≤ C₁ * (A + B + Z') := mul_le_mul_of_nonneg_left (by linarith) hC₁.le
  have a2 : C₂ * A ≤ C₂ * (A + B + Z') := mul_le_mul_of_nonneg_left (by linarith) hC₂.le
  nlinarith

end GlobalTheory.ExplicitFormulaClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rank_const_absorb {x : ℝ} (hx : 1 < x) (hK : (1000 : ℝ) ≤ x ^ ((1 : ℝ) / 1000)) {a b C : ℝ}
    (hC : C ≤ 1000) (hab : a + 1 / 1000 ≤ b) : C * x ^ a ≤ x ^ b := by
  have hx0 : 0 < x := by linarith
  calc C * x ^ a ≤ x ^ ((1 : ℝ) / 1000) * x ^ a :=
        mul_le_mul_of_nonneg_right (hC.trans hK) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (a + 1 / 1000) := by rw [Real.rpow_add hx0, mul_comm]
    _ ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx.le hab

theorem rank_mul_le {x : ℝ} (hx : 0 < x) {u v a b : ℝ} (hv : 0 ≤ v) (hu : u ≤ x ^ a) (hv' : v ≤ x ^ b) :
    u * v ≤ x ^ (a + b) := by
  rw [Real.rpow_add hx]
  exact mul_le_mul hu hv' hv (Real.rpow_nonneg hx.le _)

theorem rank_basic_bounds : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → (R.f : ℝ) ≤ s.x ^ (3 : ℝ) ∧ (R.m : ℝ) ≤ s.x ∧ (R.r : ℝ) ≤ s.x ^ (5 : ℝ) ∧ R.k ≤ R.r ∧ R.r ≤ 2 * R.k ∧ s.L ≤ s.x ∧ 1 ≤ s.L ∧ s.x ^ ((13 : ℝ) / 2) ≤ (R.f : ℝ) * R.r * s.L ∧ (R.f : ℝ) * R.r * s.L ≤ s.x ^ ((687 : ℝ) / 100) ∧ ((R.f * R.r.choose 2 : ℕ) : ℝ) ≤ s.x ^ (12 : ℝ) ∧ (R.k : ℝ) * R.f / R.m ≤ s.x ^ (7 : ℝ) ∧ ((nWv R s : ℕ) : ℝ) ≤ s.x ^ ((229 : ℝ) / 10) ∧ s.x ^ (377 : ℝ) ≤ (R.t : ℝ) ∧ (R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ (R.N R.m : ℝ) ≤ s.x ^ (402 : ℝ) ∧ s.x ^ ((1 : ℝ) / 2 - s.eps / 16) ≤ (R.m : ℝ) ∧ (R.m : ℝ) ≤ 2 * s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
  intro eps he0 he1
  refine ⟨(1000 : ℝ) ^ (1000 : ℝ), fun s R hs hx0 hR => ?_⟩
  have hn2 := RankVal.n_le hR
  obtain ⟨⟨hn1, -⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, ht⟩ := hR
  have hx := s.one_lt_alt
  have hxp : 0 < s.x := lt_trans one_pos hx
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have hK : (1000 : ℝ) ≤ s.x ^ ((1 : ℝ) / 1000) := by
    calc (1000 : ℝ) = ((1000 : ℝ) ^ (1000 : ℝ)) ^ ((1 : ℝ) / 1000) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hx0 (by norm_num)
  clear hx0
  have ab : ∀ {a b C : ℝ}, C ≤ 1000 → a + 1 / 1000 ≤ b → C * s.x ^ a ≤ s.x ^ b :=
    fun hC hab => rank_const_absorb hx hK hC hab
  have mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b :=
    fun h => Real.rpow_le_rpow_of_exponent_le hx.le h
  have one : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ s.x ^ a := fun h => Real.one_le_rpow hx.le h
  have hsq : Real.sqrt (s.x * s.delta1) = s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
    have : s.x * s.delta1 = s.x ^ (1 + -(s.eps / 8)) := by
      rw [Real.rpow_add hxp, Real.rpow_one]; rfl
    rw [this, Real.sqrt_eq_rpow, ← Real.rpow_mul hxp.le]
    congr 1; ring
  rw [hsq] at hm1 hm2
  have h2m := R.two_le_m
  have hmk := R.m_add_three_le_k
  have hkr : R.k ≤ R.r := by unfold Ranks.r; omega
  have hrk : R.r ≤ 2 * R.k := by unfold Ranks.r; omega
  have hkr' : (R.k : ℝ) ≤ R.r := by exact_mod_cast hkr
  have hrk' : (R.r : ℝ) ≤ 2 * R.k := by exact_mod_cast hrk
  have hfn : (R.f : ℝ) = 2 * R.n := by unfold Ranks.f; push_cast; ring
  have hf : (R.f : ℝ) ≤ s.x ^ ((2156 : ℝ) / 1000) := by
    have := ab (C := 4) (a := 2 + 8 * s.eps + s.eps / 100) (b := 2156 / 1000) (by norm_num) (by linarith)
    linarith
  have hr : (R.r : ℝ) ≤ s.x ^ ((4694 : ℝ) / 1000) := by
    have := ab (C := 4) (a := 9 / 2 + 10 * s.eps) (b := 4694 / 1000) (by norm_num) (by linarith)
    linarith
  have hk : (R.k : ℝ) ≤ s.x ^ ((4694 : ℝ) / 1000) := hkr'.trans hr
  have hL : s.L ≤ s.x ^ ((20 : ℝ) / 1000) := mono (by linarith)
  have hL1 : 1 ≤ s.L := one e0.le
  have hmu : (R.m : ℝ) ≤ s.x ^ ((501 : ℝ) / 1000) := by
    have := ab (C := 2) (a := 1 / 2 - s.eps / 16) (b := 501 / 1000) (by norm_num) (by linarith)
    linarith
  have hmp : (0 : ℝ) < R.m := by exact_mod_cast (by omega : 0 < R.m)
  have hmi : (R.m : ℝ)⁻¹ ≤ s.x ^ (-(498 : ℝ) / 1000) := by
    have h1 : s.x ^ ((498 : ℝ) / 1000) ≤ R.m := (mono (by linarith)).trans hm1
    rw [neg_div, Real.rpow_neg hxp.le]
    exact inv_anti₀ (by positivity) h1
  have f0 : (0 : ℝ) ≤ R.f := by positivity
  have r0 : (0 : ℝ) ≤ R.r := by positivity
  have k0 : (0 : ℝ) ≤ R.k := by positivity
  have L0 : (0 : ℝ) ≤ s.L := by linarith
  have mi0 : (0 : ℝ) ≤ (R.m : ℝ)⁻¹ := by positivity
  have k1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have hf1 : 1 ≤ R.f := by
    have : R.m ≤ R.f := R.m_le_f
    omega
  have hf1' : (1 : ℝ) ≤ R.f := by exact_mod_cast hf1
  have hfr := rank_mul_le hxp r0 hf hr

  have hB0 : 0 ≤ (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by
    have : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    positivity
  have hApos : 0 < 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 := by
    have : (0 : ℝ) < R.r := by linarith
    have : (0 : ℝ) < (R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by linarith
    positivity
  have hW1 : 1 ≤ nWv R s := by
    have := Nat.ceil_pos.mpr hApos
    unfold nWv; omega
  have hW : ((nWv R s : ℕ) : ℝ) ≤ s.x ^ ((229 : ℝ) / 10) := by
    have h1 := (Nat.ceil_lt_add_one hApos.le).le
    have hk' : (R.k : ℝ) - 1 ≤ s.x ^ ((4694 : ℝ) / 1000) := by linarith
    have k0' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    have h2 := rank_mul_le hxp mi0 (rank_mul_le hxp L0 (rank_mul_le hxp L0 (rank_mul_le hxp k0'
      (rank_mul_le hxp k0' (rank_mul_le hxp k0' (rank_mul_le hxp f0 hfr hf) hk') hk') hk') hL) hL) hmi
    have h3 := h2.trans (mono (b := 227 / 10) (by norm_num))
    have h4 := hfr.trans (mono (b := 227 / 10) (by norm_num))
    have h5 : 1 ≤ s.x ^ ((227 : ℝ) / 10) := one (by norm_num)
    have h6 := ab (C := 28) (a := 227 / 10) (b := 229 / 10) (by norm_num) (by norm_num)
    have h7 : 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8
        = (10 * ((R.f : ℝ) * R.r) + 10 * ((R.f : ℝ) * R.r * R.f * ((R.k : ℝ) - 1) * ((R.k : ℝ) - 1)
          * ((R.k : ℝ) - 1) * s.L * s.L * (R.m : ℝ)⁻¹)) / 8 := by
      rw [div_eq_mul_inv ((R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2)]; ring
    unfold nWv
    push_cast
    linarith
  have hT1 : s.x ^ (377 : ℝ) ≤ (TOv s : ℝ) := Nat.le_ceil _
  have hT2 : (TOv s : ℝ) ≤ s.x ^ (378 : ℝ) := by
    have h1 : (TOv s : ℝ) ≤ s.x ^ (377 : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have h5 : 1 ≤ s.x ^ (377 : ℝ) := one (by norm_num)
    have h6 := ab (C := 2) (a := 377) (b := 378) (by norm_num) (by norm_num)
    linarith
  have ht1 : TOv s ≤ R.t := by
    have h1 : TOv s ≤ TOv s * nWv R s := Nat.le_mul_of_pos_right _ hW1
    have h2 : R.r ≤ 8 * R.f * R.r := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have ht2 : (R.t : ℝ) ≤ s.x ^ (401 : ℝ) := by
    have h1 : R.t ≤ 8 * R.f * R.r + 4 + TOv s * nWv R s := by omega
    have h2 : (R.t : ℝ) ≤ 8 * (R.f * R.r) + 4 + TOv s * nWv R s := by
      have : ((R.t : ℕ) : ℝ) ≤ ((8 * R.f * R.r + 4 + TOv s * nWv R s : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    have h3 := (rank_mul_le hxp (by positivity) hT2 hW).trans (mono (b := 4009 / 10) (by norm_num))
    have h4 := hfr.trans (mono (b := 4009 / 10) (by norm_num))
    have h5 : 1 ≤ s.x ^ ((4009 : ℝ) / 10) := one (by norm_num)
    have h6 := ab (C := 13) (a := 4009 / 10) (b := 401) (by norm_num) (by norm_num)
    linarith
  refine ⟨hf.trans (mono (by norm_num)), ?_, hr.trans (mono (by norm_num)), hkr, hrk, ?_, hL1, ?_, ?_, ?_, ?_,
    hW, hT1.trans (by exact_mod_cast ht1), ht2, ?_, hm1, hm2⟩
  · simpa using hmu.trans (mono (b := 1) (by norm_num))
  · simpa using hL.trans (mono (b := 1) (by norm_num))
  · have h1 : s.x ^ (2 : ℝ) ≤ R.f := by
      have := mono (a := 2) (b := 2 + 8 * s.eps) (by linarith)
      have : (0 : ℝ) ≤ R.n := by positivity
      linarith
    have h2 : s.x ^ ((9 : ℝ) / 2) ≤ R.r := by
      have := mono (a := 9 / 2) (b := 9 / 2 + 10 * s.eps) (by linarith)
      linarith
    calc s.x ^ ((13 : ℝ) / 2) = s.x ^ (2 : ℝ) * s.x ^ ((9 : ℝ) / 2) * 1 := by
          rw [← Real.rpow_add hxp]; norm_num
      _ ≤ _ := by gcongr
  · exact (rank_mul_le hxp L0 hfr hL).trans (mono (by norm_num))
  · have h1 : ((R.r.choose 2 : ℕ) : ℝ) ≤ R.r * R.r := by
      have := Nat.choose_le_pow R.r 2
      rw [sq] at this
      exact_mod_cast this
    have h2 := (rank_mul_le hxp r0 hfr hr).trans (mono (b := 12) (by norm_num))
    push_cast
    calc (R.f : ℝ) * (R.r.choose 2 : ℕ) ≤ R.f * (R.r * R.r) := by gcongr
      _ ≤ _ := by rw [← mul_assoc]; exact h2
  · rw [div_eq_mul_inv]
    exact (rank_mul_le hxp mi0 (rank_mul_le hxp f0 hk hf) hmi).trans (mono (by norm_num))
  · have h3 := (rank_mul_le hxp (by positivity) hmu ht2).trans (mono (b := 4016 / 10) (by norm_num))
    have h4 := hk.trans (mono (b := 4016 / 10) (by norm_num))
    have h5 := hmu.trans (mono (b := 4016 / 10) (by norm_num))
    have h6 := ab (C := 3) (a := 4016 / 10) (b := 402) (by norm_num) (by norm_num)
    unfold Ranks.N
    push_cast
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemFormsIffExistsEquivariantExtension
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem PtModel.mem_Fi_iff_exists_isExt : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i)
    (φ : Fn X i), φ ∈ X.fm.Fi i ↔ ∃ Φ, M.IsExt φ Φ := by
  intro D u X i M φ
  rw [M.mem_Fi]
  constructor
  · intro h
    choose y hy hfix using h
    choose cl gp hp using M.rep_surj
    have key : ∀ (c c' : X.C.cls i) (g g' : M.G), g • M.rep c = g' • M.rep c' →
        M.act g (y c) = M.act g' (y c') := by
      intro c c' g g' hgg
      have h1 : (g'⁻¹ * g) • M.rep c = M.rep c' := by
        rw [mul_smul, hgg, inv_smul_smul]
      have hc := M.rep_inj c c' _ h1
      subst hc
      have h2 := hfix c _ h1
      have h3 : g = g' * (g'⁻¹ * g) := by group
      conv_lhs => rw [h3, map_mul, Module.End.mul_apply, h2]
    refine ⟨fun p => M.act (gp p) (y (cl p)), fun c => ?_, fun g p => ?_⟩
    · have := key (cl (M.rep c)) c (gp (M.rep c)) 1 (by rw [hp, one_smul])
      rw [hy c]
      simp only [this, map_one, Module.End.one_apply]
    · have := key (cl (g • p)) (cl p) (gp (g • p)) (g * gp p) (by rw [hp, mul_smul, hp])
      simp only [this, map_mul, Module.End.mul_apply]
  · rintro ⟨Φ, h1, h2⟩ c
    refine ⟨Φ (M.rep c), h1 c, fun g hg => ?_⟩
    rw [← h2, hg]

end GlobalTheory.LvT
end

