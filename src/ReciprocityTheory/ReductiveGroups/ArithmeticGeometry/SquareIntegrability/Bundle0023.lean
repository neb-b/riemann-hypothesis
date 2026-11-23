module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.InvBuild
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitO
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.UQEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropAC

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CharMain
section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section

namespace ChA

lemma omega_fin {E : Type} [Field E] [NumberField E] [IsCMField E] :
    ∃ ω : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun j => (ω j : E)) ∧
      ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ omStar (E := E) := by
  obtain ⟨n, ω, hωB, hspan⟩ := omega_exists' (E := E)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' (K := ℚ) (fun j => (ω j : E))
  have htop : Submodule.span ℚ (Set.range ((fun j => (ω j : E)) ∘ a)) = ⊤ := by
    rw [hsp, eq_top_iff, ← (NumberField.integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [NumberField.integralBasis_apply]
    exact hspan _
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Module.finrank ℚ E := by
    rw [← finrank_span_eq_card hli, htop, finrank_top]
  let e : Fin (Module.finrank ℚ E) ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨fun j => ω (a (e j)), hli.comp e e.injective, fun j τ => hωB _ τ⟩

set_option maxHeartbeats 1000000 in
theorem char_main (hx : Ext.All) : CharStatement := by
  intro E _ _ _ X DF P I hI σ ρ hρ
  classical
  have hNP : Ext.NearestPlane := hx.2.2.2.2.1
  obtain ⟨ω, hω, hωB⟩ := omega_fin (E := E)
  have hf1n : 1 ≤ PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have hF1 : (1 : ℝ) ≤ PT.f E := by exact_mod_cast hf1n
  have hm1 : (1 : ℝ) ≤ P.m := by exact_mod_cast P.hm1
  have hrd := P.hrd
  have hmf : ((P.m : ℝ)) ^ 4 ≤ PT.f E := by exact_mod_cast P.hmf
  have hf2 := P.hf2
  have hdR : (dstar (E := E) P.m : ℝ) = 2 * PT.f E * P.m := by simp [dstar]
  have hd2 : (2 : ℝ) ≤ dstar (E := E) P.m := by rw [hdR]; nlinarith
  have hFd : (PT.f E : ℝ) ≤ dstar (E := E) P.m := by rw [hdR]; nlinarith
  have hΩ2 : omStar (E := E) ^ 2 = 4 * (PT.f E : ℝ) ^ 3 * PT.rd E ^ 2 := by
    rw [omStar, mul_pow, mul_pow, ← Real.rpow_natCast ((PT.f E : ℝ) ^ ((3 : ℝ) / 2)),
      ← Real.rpow_mul (by positivity)]
    norm_num
  have hK0 : (0 : ℝ) < (dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E := by positivity
  have hK : (dstar (E := E) P.m : ℝ) * omStar (E := E) ^ 2 / 4 ≤
      ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) ^ 2 := by
    rw [hΩ2]
    have h3 : (PT.f E : ℝ) ^ 3 ≤ (dstar (E := E) P.m : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hFd 3
    have h4 : 0 ≤ (dstar (E := E) P.m : ℝ) * PT.rd E ^ 2 := by positivity
    calc (dstar (E := E) P.m : ℝ) * (4 * (PT.f E : ℝ) ^ 3 * PT.rd E ^ 2) / 4
        = ((dstar (E := E) P.m : ℝ) * PT.rd E ^ 2) * (PT.f E : ℝ) ^ 3 := by ring
      _ ≤ ((dstar (E := E) P.m : ℝ) * PT.rd E ^ 2) * (dstar (E := E) P.m : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 h4
      _ = _ := by ring
  have hD : Module.finrank ℝ (IR I) ≤ dstar (E := E) P.m := by
    obtain ⟨ρ', hρ'm, hρ'⟩ := hI.rank
    rw [hρ', dstar, mul_assoc, mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hρ'm)
  obtain ⟨xb, ub, hxub, hspan, hbnd⟩ := exists_short_real_span hI
  have hex : ∀ W : Submodule ℂ (Vsp X.dim), Module.finrank ℂ W < ρ →
      ∃ y ∈ Xg X.L I, prj σ y ∉ W ∧
        ‖y‖ ^ 2 ≤ PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E) := by
    intro W hW
    obtain ⟨j, hj⟩ := exists_out (by exact hρ) ub hspan W hW
    exact ⟨ub j, ⟨xb j, (hxub j).1, (hxub j).2⟩, hj, hbnd j⟩
  have hρm : ρ ≤ P.m := rho_le hI ω hω (by exact hρ)
  have hρmR : (ρ : ℝ) ≤ P.m := by exact_mod_cast hρm
  obtain ⟨χ, w, R, μ, ε, hinv⟩ := inv_build hNP X.stable hI.stable hI.iso (sep_X hI) ω hω
    (omStar (E := E)) hωB (dstar (E := E) P.m) hD σ ρ _ _ hK0 hK hex ρ le_rfl
  obtain ⟨hχX, hwW, hort, hdec, hεz, hεn, hRb, hred, hflag, hμB⟩ := hinv
  have hph : 0 ≤ P.ph := by
    rw [Par.ph, PT.ph]; split_ifs
    · positivity
    · exact le_rfl
  have hs2 : Real.sqrt 2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num

  have hcmp : ∀ s : Fin ρ, 30 ≤ 30 * (ρ : ℝ) ^ 2 ∧
      Real.sqrt 2 * (30 * (ρ : ℝ) ^ 2 + 1) + 1 ≤ 3 / 2 * (30 * (ρ : ℝ) ^ 2) := by
    intro s
    have : (1 : ℝ) ≤ ρ := by exact_mod_cast (show 1 ≤ ρ by have := s.2; omega)
    constructor <;> nlinarith [Real.sqrt_nonneg 2]
  have hχn : ∀ s : Fin ρ, ‖χ s‖ ≤ 3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s := by
    intro s
    have h1 := (hRb s s.2).2
    have h2 := (hcmp s).2
    have hμ := (hred s s.2).1
    have h3 : 0 ≤ ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s := by positivity
    have := mul_le_mul_of_nonneg_right h2 h3
    nlinarith
  refine ⟨fun s => w s, fun s => (hχX s s.2).choose, fun s => χ s, fun s => R s,
    fun s s' => ε s s', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    have := Wk_le hI.stable σ χ (s + 1) (fun j hj => hχX j (by omega)) (hwW s s.2)
    exact ⟨(Submodule.mem_inf.mp this).2, (Submodule.mem_inf.mp this).1⟩
  · intro s s'
    show Hf (w s) (w s') = _
    rw [Hf_eq_inner, hort s' s'.2 s s.2]
    by_cases h : s = s'
    · subst h; simp
    · rw [if_neg (fun e => h (Fin.ext e).symm), if_neg h]
  · intro s
    exact (hχX s s.2).choose_spec
  · intro s s' h
    exact hεz s s.2 s' (Fin.lt_def.mp h).le
  · intro s
    have hsum : ∑ s' : Fin ρ, ‖ε s s'‖ ^ 2 = ∑ i ∈ Finset.range s, ‖ε s i‖ ^ 2 := by
      rw [show (∑ s' : Fin ρ, ‖ε s s'‖ ^ 2) = ∑ i ∈ Finset.range ρ, ‖ε s i‖ ^ 2 from
        Fin.sum_univ_eq_sum_range (fun i => ‖ε s i‖ ^ 2) ρ]
      symm
      refine Finset.sum_subset (Finset.range_mono s.2.le) fun i _ hi => ?_
      rw [hεz s s.2 i (by simpa using hi), norm_zero]; norm_num
    have hb := hεn s s.2
    have hA := (hcmp s).1
    have hq : 0 ≤ 1 / (30 * (ρ : ℝ) ^ 2) := by positivity
    constructor
    · show Real.sqrt (∑ s' : Fin ρ, ‖ε s s'‖ ^ 2) ≤ _
      rw [hsum, ← Real.sqrt_sq hq]; exact Real.sqrt_le_sqrt hb
    · show ∑ s' : Fin ρ, ‖ε s s'‖ ≤ _
      have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun s' : Fin ρ => ‖ε s s'‖)
      simp only [Finset.card_univ, Fintype.card_fin] at hcs
      rw [hsum] at hcs
      have h0 : 0 ≤ ∑ s' : Fin ρ, ‖ε s s'‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have h1 : (∑ s' : Fin ρ, ‖ε s s'‖) ^ 2 ≤ (Real.sqrt ρ / (30 * (ρ : ℝ) ^ 2)) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        calc _ ≤ (ρ : ℝ) * ∑ i ∈ Finset.range s, ‖ε s i‖ ^ 2 := hcs
          _ ≤ (ρ : ℝ) * (1 / (30 * (ρ : ℝ) ^ 2)) ^ 2 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
          _ = _ := by ring
      have hb0 : 0 ≤ Real.sqrt ρ / (30 * (ρ : ℝ) ^ 2) := by positivity
      nlinarith
  · intro s v hv
    have hR : (R s : ℂ) ≠ 0 := by
      have h1 := (hRb s s.2).1
      have hμ := (hred s s.2).1
      have hA := (hcmp s).1
      have h2 : 0 < (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s := mul_pos (mul_pos (by linarith) hK0) (by linarith)
      have : 0 < R s := lt_of_lt_of_le h2 h1
      exact_mod_cast this.ne'
    show Hf v (χ s) / (R s : ℂ) = Hf v (w s) + ∑ s' : Fin ρ, ε s s' * Hf v (w s')
    rw [← Hf_prj_right hv (χ s), hdec s s.2]
    simp only [Hf_eq_inner, inner_smul_left, inner_add_left, sum_inner, Complex.conj_ofReal,
      Complex.conj_conj]
    rw [mul_div_cancel_left₀ _ hR]
    congr 1
    rw [show (∑ s' : Fin ρ, ε s s' * inner ℂ (w s') v) = ∑ i ∈ Finset.range ρ, ε s i * inner ℂ (w i) v from
      Fin.sum_univ_eq_sum_range (fun i => ε s i * inner ℂ (w i) v) ρ]
    refine Finset.sum_subset (Finset.range_mono s.2.le) fun i _ hi => ?_
    rw [hεz s s.2 i (by simpa using hi), zero_mul]
  · intro s
    show ‖χ s‖ ≤ 1.5 * R s ∧ 1 ≤ 2 * Real.pi * R s
    have hRs := (hRb s s.2).1
    have hμ := (hred s s.2).1
    have hA := (hcmp s).1
    have hn := hχn s
    have hK1 : 1 ≤ ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) := by nlinarith
    have h1 : 30 ≤ (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) := by nlinarith
    have hX : 30 ≤ (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s := by nlinarith
    have e15 : (1.5 : ℝ) = 3 / 2 := by norm_num
    rw [e15]
    constructor
    · nlinarith
    · nlinarith [Real.pi_gt_three]
  · intro s y hy uy hU
    show |2 * inner ℝ (χ s) uy| ≤ M1 (E := E) P.m * ‖uy‖ ^ 2
    have huy : uy ∈ Xg X.L I := ⟨y, hy, hU⟩
    have hA := (hcmp s).1
    have hM : 3 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) ≤ M1 (E := E) P.m := by
      rw [M1]
      have h1 : (ρ : ℝ) ^ 2 ≤ (P.m : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hρmR 2
      have h2 := mul_le_mul_of_nonneg_right h1 hK0.le
      nlinarith
    have hK1 : 1 ≤ ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) := by nlinarith
    have hM1 : 1 ≤ M1 (E := E) P.m := by nlinarith
    have e1 : |2 * inner ℝ (χ s) uy| ≤ 2 * (‖χ s‖ * ‖uy‖) := by
      rw [abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
    rcases (hred s s.2).2 uy huy with h | h
    · have := mul_le_mul_of_nonneg_right hM1 (sq_nonneg ‖uy‖)
      linarith
    · have hn := hχn s
      have h2 : ‖χ s‖ ≤ 3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * ‖uy‖ :=
        le_trans hn (mul_le_mul_of_nonneg_left h (by positivity))
      have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg uy)
      have h4 := mul_le_mul_of_nonneg_right hM (sq_nonneg ‖uy‖)
      nlinarith
  · intro s
    show ‖χ s‖ ^ 2 ≤ Cchi (E := E) P.m * P.ph
    have hn := hχn s
    have hμ := (hred s s.2).1
    have hB := hμB s s.2
    have h0 : 0 ≤ 3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) := by positivity
    have h1 : ‖χ s‖ ^ 2 ≤ (3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E)) ^ 2 * (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * (PT.f E : ℝ))) := by
      calc ‖χ s‖ ^ 2 ≤ (3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ = (3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E)) ^ 2 * μ s ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
    have hFpos : (0 : ℝ) < (PT.f E : ℝ) := by linarith
    have hd4 : (dstar (E := E) P.m : ℝ) ^ 4 ≤ 8 * (PT.f E : ℝ) * PT.rd E ^ 3 := by
      rw [hdR]
      have h5 : 16 * (PT.f E : ℝ) ^ 4 * (P.m : ℝ) ^ 4 ≤ 16 * (PT.f E : ℝ) ^ 5 := by
        have := mul_le_mul_of_nonneg_left hmf (by positivity : (0 : ℝ) ≤ 16 * (PT.f E : ℝ) ^ 4)
        nlinarith
      have h6 : (PT.f E : ℝ) ^ 4 ≤ PT.rd E ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hf2 2
        nlinarith
      have h7 : 16 * (PT.f E : ℝ) ^ 4 ≤ PT.rd E * PT.rd E ^ 2 := by nlinarith
      have h8a := mul_le_mul_of_nonneg_left h7 hFpos.le
      have h8b : 0 ≤ (PT.f E : ℝ) * PT.rd E ^ 3 := by positivity
      have h8 : 16 * (PT.f E : ℝ) ^ 5 ≤ 8 * (PT.f E : ℝ) * PT.rd E ^ 3 := by nlinarith
      nlinarith
    have hρ4 : (ρ : ℝ) ^ 4 ≤ (P.m : ℝ) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hρmR 4
    have hdF : (dstar (E := E) P.m : ℝ) ^ 4 / (PT.f E : ℝ) ≤ 8 * PT.rd E ^ 3 := by rw [div_le_iff₀ hFpos]; linarith
    have hC : 0 ≤ 2025 / 2 * (dstar (E := E) P.m : ℝ) ^ 4 * PT.rd E ^ 4 * P.ph := mul_nonneg (by positivity) hph
    refine h1.trans ?_
    calc _ = (2025 / 2 * (dstar (E := E) P.m : ℝ) ^ 4 * PT.rd E ^ 4 * P.ph) * ((ρ : ℝ) ^ 4 * ((dstar (E := E) P.m : ℝ) ^ 4 / (PT.f E : ℝ))) := by
          field_simp; ring
      _ ≤ (2025 / 2 * (dstar (E := E) P.m : ℝ) ^ 4 * PT.rd E ^ 4 * P.ph) * ((P.m : ℝ) ^ 4 * (8 * PT.rd E ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hρ4 hdF (by positivity) (by positivity)) hC
      _ = Cchi (E := E) P.m * P.ph := by rw [Cchi, RR]; ring

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DifferentiableZeroModeLiftOf
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

theorem norm_uc_sq {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (v : EuclideanSpace ℂ ι) :
    ‖uc K v‖ ^ 2 = ∑ k, (z K k v).im ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_uc _ v _ (uc_mem _ v), uc, Hf_sum_r, Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hf_rsmul_r, Complex.im_ofReal_mul, z]; ring

theorem re_S {ι : Type} [Fintype ι] {K : Submodule ℝ (EuclideanSpace ℂ ι)}
    (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0) (w : EuclideanSpace ℂ ι) :
    (S K w).re = ‖w‖ ^ 2 - ‖p2 K w‖ ^ 2 - 2 * ‖uc K w‖ ^ 2 := by
  rw [norm_sq_decomp hK, norm_uc_sq, S, Complex.re_sum]
  have hz : ∀ k, ‖z K k w‖ ^ 2 = (z K k w).re ^ 2 + (z K k w).im ^ 2 := fun k => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [hz, sq, Complex.mul_re]
  rw [Finset.mul_sum]
  have h3 : ∑ k, ((z K k w).re * (z K k w).re - (z K k w).im * (z K k w).im) =
      ∑ k, ((z K k w).re * (z K k w).re + (z K k w).im * (z K k w).im) -
        ∑ k, 2 * ((z K k w).im * (z K k w).im) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [h3]; ring

section Nsec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)
include hI

theorem norm_Tm (γ : X.L) (v : Vsp X.dim) :
    ‖Tm X I q β γ v‖ = Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2) *
      Real.exp (-(q * Real.pi) * ‖uc (IR I) (v - γ)‖ ^ 2) *
        (‖β (wmap (IR I) (v - γ))‖ * Real.exp (-(q * Real.pi) * ‖wmap (IR I) (v - γ)‖ ^ 2 / 2)) := by
  have hK := hK_of hI
  have he : ‖(X.eps (γ : Vsp X.dim) : ℂ)‖ = 1 := by
    rcases X.eps_pm _ γ.2 with h | h <;> simp [h]
  simp only [Tm, Uh, Uq, F0, norm_mul, norm_pow, he, one_pow, one_mul, Complex.norm_exp]
  set w := v - (γ : Vsp X.dim) with hw
  have h1 : (Hf v (γ : Vsp X.dim)).re = (‖v‖ ^ 2 + ‖(γ : Vsp X.dim)‖ ^ 2 - ‖w‖ ^ 2) / 2 := by
    have := Hf_self_re w
    rw [hw, Hf_sub_l, Hf_sub_r, Hf_sub_r, Complex.sub_re, Complex.sub_re, Complex.sub_re,
      Hf_self_re, Hf_self_re, Hf_swap v (γ : Vsp X.dim), Complex.conj_re] at this
    rw [← hw] at this
    linarith
  have h2 := re_S hK w
  rw [norm_wmap hK]
  have hre1 : (q * Real.pi * Hf v (γ : Vsp X.dim) - q * Real.pi * Hf (γ : Vsp X.dim) γ / 2 : ℂ).re =
      q * Real.pi * (Hf v (γ : Vsp X.dim)).re - q * Real.pi * ‖(γ : Vsp X.dim)‖ ^ 2 / 2 := by
    simp [Complex.mul_re, Hf_self_re]
  have hre2 : ((q * Real.pi / 2 : ℂ) * S (IR I) w).re = q * Real.pi / 2 * (S (IR I) w).re := by
    simp [Complex.mul_re]
  rw [hre1, hre2, h1, h2]
  rw [← mul_assoc, ← Real.exp_add, mul_comm (‖β _‖), ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

theorem exp_shift_le (a : ℝ) (ha : 0 ≤ a) (u w : Vsp X.dim) :
    Real.exp (-a * ‖u - w‖ ^ 2) ≤ Real.exp (a * ‖u‖ ^ 2) * Real.exp (-(a / 2) * ‖w‖ ^ 2) := by
  have h1 : ‖w‖ ≤ ‖u‖ + ‖u - w‖ := by
    calc ‖w‖ = ‖u - (u - w)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖u‖ + ‖u - w‖ := norm_sub_le _ _
  have h2 : ‖w‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖u - w‖ ^ 2 := by
    nlinarith [norm_nonneg w, norm_nonneg u, norm_nonneg (u - w), sq_nonneg (‖u‖ - ‖u - w‖)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left h2 ha]

theorem cond_tail (a : ℝ) (ha : 1 / 2 ≤ a) : (dK (IR I) : ℝ) + 1 ≤ a * P.q * b0 (E := E) P.q P.R0 := by
  obtain ⟨ρ, hρm, hρ⟩ := hI.rank
  have hdK : (dK (IR I) : ℝ) ≤ dstar (E := E) P.m := by
    rw [dK, hρ, dstar]; push_cast
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hρm) (by positivity)
  have h6 := P.C6
  have hr : 0 ≤ (X.r : ℝ) * Real.log X.r := by
    rcases Nat.eq_zero_or_pos X.r with h | h
    · simp [h]
    · exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast h))
  have hDF : 0 ≤ ((DF : ℝ) + 1) * (X.r * Real.log X.r + 3 * X.r + 3) := by positivity
  have hg : 0 ≤ (X.gA : ℝ) * Real.log 2 := by positivity
  have ht0 : t0 (E := E) P.q P.R0 = P.q * b0 (E := E) P.q P.R0 := rfl
  have hb := cutoff_pos P
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hqb : 0 < (P.q : ℝ) * b0 (E := E) P.q P.R0 := mul_pos hq hb
  rw [ht0] at h6
  nlinarith

theorem summable_gauss (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (a : ℝ) (ha : 1 / 2 ≤ a) :
    Summable (fun c : Qc X I => Real.exp (-(a * P.q) * ‖uQ X I c‖ ^ 2)) :=
  (Finset.summable_compl_iff {0}).1 (tailQ hI hP hA a (by linarith) (cond_tail hI a ha)).1

variable {q β}

theorem norm_Tc_le {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖t‖ ^ 2) ≤ B ^ 2) (c : Qc X I) (v : Vsp X.dim) :
    ‖Tc X I q β c v‖ ≤ B * Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2) *
      Real.exp (-(q * Real.pi) * ‖uc (IR I) v - uQ X I c‖ ^ 2) := by
  rw [Tc, norm_Tm hI, uc_sub, ← uQ_out]
  have hN : ‖β (wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim)))‖ *
      Real.exp (-(q * Real.pi) * ‖wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim))‖ ^ 2 / 2) ≤ B := by
    set t := wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim))
    have h := hB t
    have hsq : (‖β t‖ * Real.exp (-(q * Real.pi) * ‖t‖ ^ 2 / 2)) ^ 2 =
        ‖β t‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖t‖ ^ 2) := by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    rw [← hsq] at h
    exact (pow_le_pow_iff_left₀ (by positivity) hB0 two_ne_zero).1 h
  calc _ ≤ Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2) * Real.exp (-(q * Real.pi) * ‖uc (IR I) v - uQ X I c‖ ^ 2) * B :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = _ := by ring

omit hI in
theorem diff_Hf (a : Vsp X.dim) : Differentiable ℂ (fun v : Vsp X.dim => Hf v a) := by
  unfold Hf
  first
    | fun_prop
    | exact Differentiable.fun_sum fun i _ =>
        (EuclideanSpace.proj i : Vsp X.dim →L[ℂ] ℂ).differentiable.mul_const _
    | exact Differentiable.sum fun i _ =>
        (EuclideanSpace.proj i : Vsp X.dim →L[ℂ] ℂ).differentiable.mul_const _

omit hI in
theorem differentiable_zeroModeLift_of (hβd : Differentiable ℂ β) : Differentiable ℂ (F0 I q β) := by
  unfold F0
  apply Differentiable.mul
  · apply Differentiable.cexp
    apply Differentiable.const_mul
    unfold S z
    exact Differentiable.fun_sum (fun k _ => (diff_Hf _).pow 2)
  · exact hβd.comp (wmap (IR I)).differentiable

omit hI in
theorem diff_Tm (hβd : Differentiable ℂ β) (γ : Vsp X.dim) : Differentiable ℂ (Uh X q γ (F0 I q β)) := by
  unfold Uh Uq
  apply Differentiable.const_mul
  apply Differentiable.mul
  · apply Differentiable.cexp
    exact ((diff_Hf γ).const_mul _).sub_const _
  · exact (differentiable_zeroModeLift_of hβd).comp (differentiable_id.sub_const γ)

end Nsec

section Ssec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  {β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ} (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound)
  {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖t‖ ^ 2) ≤ B ^ 2)
include hI hP hA hB0 hB

theorem Tc_bound (R : ℝ) (c : Qc X I) (v : Vsp X.dim) (hv : ‖v‖ ≤ R) :
    ‖Tc X I P.q β c v‖ ≤ B * Real.exp (P.q * Real.pi * R ^ 2 / 2) *
      (Real.exp (P.q * Real.pi * R ^ 2) * Real.exp (-(Real.pi / 2 * P.q) * ‖uQ X I c‖ ^ 2)) := by
  have hq : (0 : ℝ) ≤ P.q * Real.pi := by positivity
  have hv2 : ‖v‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hv 2
  have hu2 : ‖uc (IR I) v‖ ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ((norm_uc_le hI.iso v).trans hv) 2
  refine (norm_Tc_le hI hB0 hB c v).trans ?_
  rw [mul_assoc, mul_assoc B]
  apply mul_le_mul_of_nonneg_left _ hB0
  apply mul_le_mul (Real.exp_le_exp.2 (by nlinarith)) _ (by positivity) (by positivity)
  refine (exp_shift_le hI (P.q * Real.pi) hq _ _).trans ?_
  apply mul_le_mul (Real.exp_le_exp.2 (by nlinarith)) (le_of_eq ?_) (by positivity) (by positivity)
  congr 1; ring

theorem summable_Tc (v : Vsp X.dim) : Summable (fun c : Qc X I => Tc X I P.q β c v) := by
  refine Summable.of_norm_bounded ?_ (fun c => Tc_bound hI hP hA hB0 hB ‖v‖ c v le_rfl)
  exact ((summable_gauss hI hP hA (Real.pi / 2) (by linarith [Real.pi_gt_three])).mul_left _).mul_left _

theorem diff_sP (hβd : Differentiable ℂ β) : Differentiable ℂ (sP X I P.q β) := by
  intro x
  have hb : ∀ R : ℝ, ∃ u : Qc X I → ℝ, Summable u ∧
      ∀ c v, ‖v‖ ≤ R → ‖Tc X I P.q β c v‖ ≤ u c := by
    intro R
    exact ⟨_, ((summable_gauss hI hP hA (Real.pi / 2) (by linarith [Real.pi_gt_three])).mul_left
      (Real.exp (P.q * Real.pi * R ^ 2))).mul_left (B * Real.exp (P.q * Real.pi * R ^ 2 / 2)),
      fun c v hv => Tc_bound hI hP hA hB0 hB R c v hv⟩
  exact (pa_tsum_hasFDeriv (fun c => Tc X I P.q β c)
    (fun c => diff_Tm (q := P.q) hβd _) hb x).2.differentiableAt

def colS (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ) :
    (Fin 1 → Vsp X.dim) → ℂ :=
  fun w => sP X I q β (w 0)

theorem colS_mem (hβ : β ∈ (YB hI hP P.q).Sec P.q) : colS X I P.q β ∈ X.Sec P.q 1 := by
  refine ⟨(diff_sP hI hP hA hB0 hB hβ.1).comp (differentiable_apply 0), fun γ hγ v => ?_⟩
  have h := sP_shift hI hP P.q hβ ⟨γ 0, hγ 0⟩ (v 0)
  simp only [colS, Pi.add_apply, Fin.prod_univ_one, HC, Fin.sum_univ_one]
  exact h

end Ssec

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
end

