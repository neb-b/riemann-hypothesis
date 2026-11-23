module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TwoNeZeroNat

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisVan
section
open ModularForm UpperHalfPlane Matrix EisensteinSeries Filter Topology
open scoped MatrixGroups

namespace UpperTheory.V.Sd

private def cSet {N : ℕ} (b : Fin 2 → ZMod N) : Set (Fin 2 → ℤ) := {v | (↑) ∘ v = b}

private lemma vecMul_mem_cSet {N : ℕ} {b : Fin 2 → ZMod N} {v : Fin 2 → ℤ} (hv : v ∈ cSet b)
    (γ : SL(2, ℤ)) : v ᵥ* γ ∈ cSet (b ᵥ* γ) := by
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  have hv' : (fun x : ℤ => (x : ZMod N)) ∘ v = b := hv
  change (Int.cast : ℤ → ZMod N) ∘ (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) = b ᵥ* _
  funext i
  rw [Function.comp_apply, this i, hv']
  simp [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

private def cEquiv {N : ℕ} (b : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : cSet b ≃ cSet (b ᵥ* γ) where
  toFun v := ⟨v.1 ᵥ* γ, vecMul_mem_cSet v.2 γ⟩
  invFun v := ⟨v.1 ᵥ* ↑(γ⁻¹), by
      have := vecMul_mem_cSet v.2 γ⁻¹
      have h1 : ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) *
          (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
        have h0 : (γ : SL(2, ZMod N)) * ((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) = 1 :=
          (map_mul (SpecialLinearGroup.map (Int.castRingHom (ZMod N))) γ γ⁻¹).symm.trans (by simp)
        exact congrArg Subtype.val h0
      rwa [vecMul_vecMul, h1, vecMul_one] at this⟩
  left_inv v := by
    have h : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
      congrArg Subtype.val (mul_inv_cancel γ)
    refine Subtype.ext ?_
    exact (vecMul_vecMul _ _ _).trans (by rw [h, vecMul_one])
  right_inv v := by
    have h : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
      congrArg Subtype.val (inv_mul_cancel γ)
    refine Subtype.ext ?_
    exact (vecMul_vecMul _ _ _).trans (by rw [h, vecMul_one])

private noncomputable def cSer {N : ℕ} (b : Fin 2 → ZMod N) (k : ℤ) (z : ℍ) : ℂ :=
  ∑' x : cSet b, eisSummand k x z

private lemma cSer_slash {N : ℕ} (b : Fin 2 → ZMod N) (k : ℤ) (γ : SL(2, ℤ)) :
    cSer b k ∣[k] γ = cSer (b ᵥ* γ) k := by
  ext1 z
  simp_rw [SL_slash_apply, _root_.zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z),
    cSer, eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (cEquiv b γ).tsum_eq (eisSummand k · z)

private noncomputable def cSIF {N : ℕ} (b : Fin 2 → ZMod N) (k : ℤ) :
    SlashInvariantForm (CongruenceSubgroup.Gamma N) k where
  toFun := cSer b k
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ CongruenceSubgroup.Gamma N), rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, cSer_slash, CongruenceSubgroup.Gamma_mem'.mp hA]

private lemma summand_le {k : ℕ} (v : Fin 2 → ℤ) (hv : v 0 ≠ 0) (z : ℍ) :
    ‖eisSummand k v z‖ ≤ (z.im ^ k)⁻¹ := by
  have hz := z.im_pos
  have him : z.im ≤ ‖(v 0 : ℂ) * (z : ℂ) + v 1‖ := by
    have h1 : ((v 0 : ℂ) * (z : ℂ) + v 1).im = (v 0 : ℝ) * z.im := by simp
    have h2 : (1 : ℝ) ≤ |(v 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hv
    calc z.im ≤ |(v 0 : ℝ)| * z.im := by nlinarith
      _ = |((v 0 : ℂ) * (z : ℂ) + v 1).im| := by rw [h1, abs_mul, abs_of_pos hz]
      _ ≤ _ := Complex.abs_im_le_norm _
  simp only [eisSummand, norm_zpow]
  rw [_root_.zpow_neg, zpow_natCast]
  exact inv_anti₀ (pow_pos hz k) (pow_le_pow_left₀ hz.le him k)

private lemma cSer_zero {N : ℕ} [NeZero N] (b : Fin 2 → ZMod N) (hb : b 0 ≠ 0) {k : ℕ}
    (hk : 3 ≤ k) : IsZeroAtImInfty (cSer b k) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hkr : (2 : ℝ) < k := by exact_mod_cast (show 2 < k by omega)
  have hv0 : ∀ v : cSet b, v.1 0 ≠ 0 := by
    intro v h
    apply hb
    have h2 := congrFun v.2 0
    simp only [Function.comp_apply, h, Int.cast_zero] at h2
    exact h2.symm
  have hper : ∀ (n : ℤ) (z : ℍ), cSer b k ((N : ℝ) * (n : ℝ) +ᵥ z) = cSer b k z :=
    fun n z => SlashInvariantForm.vAdd_width_periodic N k n (cSIF b k) z
  set F : Filter ℍ := atImInfty ⊓ 𝓟 (verticalStrip N 1) with hF
  set C : ℝ := r ⟨⟨N, 1⟩, one_pos⟩ with hC
  have hsum : Summable (fun v : cSet b => C ^ (-(k : ℝ)) * ‖v.1‖ ^ (-(k : ℝ))) :=
    ((summable_one_div_norm_rpow hkr).subtype (fun v => v ∈ cSet b)).mul_left _
  have hT : Tendsto (fun z => cSer b k z) F (𝓝 0) := by
    have h0 : (0 : ℂ) = ∑' v : cSet b, (0 : ℂ) := by simp
    rw [h0]
    apply tendsto_tsum_of_dominated_convergence hsum
    · intro v
      have him : Tendsto (fun z : ℍ => z.im) F atTop :=
        tendsto_comap.mono_left inf_le_left
      have hdec : Tendsto (fun z : ℍ => (z.im ^ k)⁻¹) F (𝓝 0) :=
        tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by omega)).comp him)
      exact squeeze_zero_norm' (Eventually.of_forall (fun z => summand_le v.1 (hv0 v) z)) hdec
    · rw [hF, eventually_inf_principal]
      apply Eventually.of_forall
      intro z hz v
      have h1 := summand_bound_of_mem_verticalStrip (k := (k : ℝ)) (by positivity) v.1 one_pos hz
      calc ‖eisSummand k v.1 z‖ = ‖(v.1 0 : ℂ) * z + v.1 1‖ ^ (-(k : ℝ)) := by
            rw [eisSummand, norm_zpow, ← Real.rpow_intCast]
            push_cast
            rfl
        _ ≤ _ := h1
  have hn : Tendsto (fun z => ‖cSer b k z‖) F (𝓝 0) := by simpa using hT.norm
  rw [isZeroAtImInfty_iff]
  intro ε hε
  have hev : ∀ᶠ z in F, ‖cSer b k z‖ ≤ ε := hn.eventually (Iic_mem_nhds hε)
  rw [hF, eventually_inf_principal] at hev
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hev
  refine ⟨max A 1, fun z hz => ?_⟩
  have hfl1 := Int.floor_le (z.re / N)
  have hfl2 := Int.lt_floor_add_one (z.re / N)
  have e1 : (N : ℝ) * ⌊z.re / N⌋ ≤ z.re := by
    have := mul_le_mul_of_nonneg_left hfl1 hN.le
    rwa [mul_div_cancel₀ _ hN.ne'] at this
  have e2 : z.re < (N : ℝ) * ⌊z.re / N⌋ + N := by
    have := mul_lt_mul_of_pos_left hfl2 hN
    rwa [mul_div_cancel₀ _ hN.ne', mul_add, mul_one] at this
  have hmem : ((N : ℝ) * ((-⌊z.re / N⌋ : ℤ) : ℝ) +ᵥ z) ∈ verticalStrip N 1 := by
    rw [mem_verticalStrip_iff, vadd_re, vadd_im, abs_le]
    push_cast
    refine ⟨⟨by nlinarith, by nlinarith⟩, by linarith [le_max_right A 1]⟩
  have hz' := hA ((N : ℝ) * ((-⌊z.re / N⌋ : ℤ) : ℝ) +ᵥ z)
    (by rw [vadd_im]; linarith [le_max_left A 1]) hmem
  rwa [hper] at hz'

private lemma eisFun_eq (N k : ℕ) (a : ZMod N) :
    eisFun N k a = ((N : ℂ) ^ k / lipC k) • cSer ![0, a] k := by
  let e : {v : ℤ × ℤ // ((v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = a)} ≃ cSet (![0, a] : Fin 2 → ZMod N) :=
    { toFun := fun v => ⟨![v.1.1, v.1.2], by
        show (Int.cast : ℤ → ZMod N) ∘ ![v.1.1, v.1.2] = ![0, a]
        funext i
        fin_cases i
        · simpa using v.2.1
        · simpa using v.2.2⟩
      invFun := fun w => ⟨(w.1 0, w.1 1), by
        have h := w.2
        change (Int.cast : ℤ → ZMod N) ∘ w.1 = ![0, a] at h
        exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp
      right_inv := fun w => by
        apply Subtype.ext
        funext i
        fin_cases i <;> simp }
  funext z
  simp only [eisFun, cSer, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [← e.tsum_eq]
  congr 1

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.eisVan :
    UpperTheory.V.Sd.EisVan := by
  intro N k _ hk a ha hN γ hγ
  rw [UpperTheory.V.Sd.eisFun_eq, ModularForm.SL_smul_slash, UpperTheory.V.Sd.cSer_slash]
  apply Filter.ZeroAtFilter.smul
  apply UpperTheory.V.Sd.cSer_zero _ _ hk
  have hc : ((γ 1 0 : ℤ) : ZMod N) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hγ
  have e : (![0, a] ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) 0 = a * ((γ 1 0 : ℤ) : ZMod N) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply]
  rw [e]
  intro h
  exact hc ((ha.mul_right_eq_zero).mp h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EulerianNumeratorThree
section
open Formalism.ConjugateSelfDual Polynomial

namespace UpperTheory.V.Sd

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private lemma nsub_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))

private lemma nadd_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

private lemma nadd_eq {a b : K} (ha : ‖a‖ = 1) (hb : ‖b‖ < 1) : ‖a + b‖ = 1 := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [ha]; exact hb.ne'), ha]
  exact max_eq_left hb.le

private lemma norm_root {N : ℕ} (hN : 0 < N) {x : K} (hx : x ^ N = 1) : ‖x‖ = 1 := by
  have h : ‖x‖ ^ N = 1 := by rw [← norm_pow, hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hN.ne').1 h

private lemma norm_one_sub_pow_le {x : K} (hx : ‖x‖ = 1) (i : ℕ) : ‖1 - x ^ i‖ ≤ ‖1 - x‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have : 1 - x ^ (i + 1) = (1 - x) + x * (1 - x ^ i) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
    rw [norm_mul, hx, one_mul]; exact ih

private lemma norm_one_sub {N : ℕ} (hN : 0 < N) (hn : ‖(N : K)‖ = 1) {x : K} (hx : x ^ N = 1) (h1 : x ≠ 1) :
    ‖1 - x‖ = 1 := by
  have hx1 := norm_root hN hx
  refine le_antisymm (nsub_le (by simp) hx1.le) ?_
  have hs : ∑ i ∈ Finset.range N, x ^ i = 0 := by
    have := mul_geom_sum x N
    rw [hx, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)
  have hN' : (N : K) = ∑ i ∈ Finset.range N, (1 - x ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [← hn, hN']
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    fun i _ => norm_one_sub_pow_le hx1 i

private lemma norm_aeval_le {x : K} (hx : ‖x‖ ≤ 1) (p : ℤ[X]) : ‖aeval x p‖ ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact nadd_le hp hq
  | monomial n a =>
    rw [aeval_monomial, norm_mul, norm_pow]
    have h1 : ‖algebraMap ℤ K a‖ ≤ 1 := by
      rw [eq_intCast]; exact IsUltrametricDist.norm_intCast_le_one K a
    exact mul_le_one₀ h1 (by positivity) (pow_le_one₀ (norm_nonneg _) hx)

end

private lemma eulerian_numerator_three : numL 3 = X * (1 + X) := by
  simp only [numL]; simp; ring

private lemma eulerian_numerator_four : numL 4 = X * (1 + 4 * X + X ^ 2) := by
  have : numL 4 = X * (derivative (numL 3) * (1 - X) + C (((2 : ℕ) : ℤ) + 1) * numL 3) := rfl
  rw [this, eulerian_numerator_three]; simp; ring

private lemma eulerian_numerator_five : numL 5 = X * (1 + X) * (1 + 10 * X + X ^ 2) := by
  have : numL 5 = X * (derivative (numL 4) * (1 - X) + C (((3 : ℕ) : ℤ) + 1) * numL 4) := rfl
  rw [this, eulerian_numerator_four]; simp; ring

section
variable {K : Type} [Field K]

private lemma eulerian_three_eq (x : K) : Lk 3 x = x * (1 + x) / (1 - x) ^ 3 := by
  simp [Lk, eulerian_numerator_three]

private lemma eulerian_four_eq {x : K} (h : 1 - x ≠ 0) :
    Lk 4 x = (x / (1 - x) ^ 2) * (1 + 6 * (x / (1 - x) ^ 2)) := by
  have : Lk 4 x = x * (1 + 4 * x + x ^ 2) / (1 - x) ^ 4 := by
    simp [Lk, eulerian_numerator_four, map_ofNat]
  rw [this]; field_simp; ring

private lemma eulerian_five_eq {x : K} (h : 1 - x ≠ 0) :
    Lk 5 x = Lk 3 x * (1 + 12 * (x / (1 - x) ^ 2)) := by
  have : Lk 5 x = x * (1 + x) * (1 + 10 * x + x ^ 2) / (1 - x) ^ 5 := by
    simp [Lk, eulerian_numerator_five, map_ofNat]
  rw [this, eulerian_three_eq]; field_simp; ring

end

private lemma norm_nat {l : ℕ} [Fact l.Prime] {N : ℕ} (h : ¬ l ∣ N) : ‖(N : Qbar l)‖ = 1 := by
  have h1 : (N : Qbar l) = algebraMap ℚ_[l] (Qbar l) (N : ℚ_[l]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 h

private lemma norm_nat_lt {l : ℕ} [Fact l.Prime] {N : ℕ} (h : l ∣ N) : ‖(N : Qbar l)‖ < 1 := by
  have h1 : (N : Qbar l) = algebraMap ℚ_[l] (Qbar l) (N : ℚ_[l]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_lt_one_iff]
  exact h

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.lkSep :
    UpperTheory.V.Sd.LkSep := by
  intro l _ hl2 N hN hlN
  have hn : ‖(N : Qbar l)‖ = 1 := norm_nat hlN
  have h1 : ∀ (k : ℕ) (x : Qbar l), x ^ N = 1 → x ≠ 1 → ‖Lk k x‖ ≤ 1 := by
    intro k x hx h
    rw [Lk, norm_div, norm_pow, norm_one_sub hN hn hx h, one_pow, div_one]
    exact norm_aeval_le (norm_root hN hx).le _
  have hne : ∀ x : Qbar l, x ^ 2 ≠ 1 → x ≠ 1 := by
    rintro x h rfl; exact h (one_pow 2)
  have h3 : ∀ x : Qbar l, x ^ N = 1 → x ^ 2 ≠ 1 → ‖Lk 3 x‖ = 1 := by
    intro x hx h
    have ha := norm_one_sub hN hn hx (hne x h)
    have hb : ‖1 - x ^ 2‖ = 1 :=
      norm_one_sub hN hn (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) h
    have hc : ‖1 + x‖ = 1 := by
      have : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
      rwa [this, norm_mul, ha, one_mul] at hb
    rw [eulerian_three_eq, norm_div, norm_mul, norm_pow, ha, hc, norm_root hN hx]; norm_num
  refine ⟨h1, h3, ?_⟩
  intro x y hx hy hx2 hy2 hyx hyx'
  have hax := norm_one_sub hN hn hx (hne x hx2)
  have hay := norm_one_sub hN hn hy (hne y hy2)
  have hnx := norm_root hN hx
  have hny := norm_root hN hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at hnx
  have hx1 : 1 - x ≠ 0 := sub_ne_zero.2 (hne x hx2).symm
  have hy1 : 1 - y ≠ 0 := sub_ne_zero.2 (hne y hy2).symm
  have hxy : ‖1 - x * y‖ = 1 := by
    refine norm_one_sub hN hn (by rw [mul_pow, hx, hy, one_mul]) fun h => hyx' ?_
    exact eq_inv_of_mul_eq_one_right h
  have hxy' : ‖1 - y / x‖ = 1 := by
    refine norm_one_sub hN hn (by rw [div_pow, hx, hy, div_one]) fun h => hyx ?_
    exact (div_eq_one_iff_eq hx0).1 h
  have h4x := eulerian_four_eq hx1
  have h4y := eulerian_four_eq hy1
  have h5x := eulerian_five_eq hx1
  have h5y := eulerian_five_eq hy1
  have hu : ‖x / (1 - x) ^ 2‖ = 1 := by rw [norm_div, norm_pow, hax, hnx]; norm_num
  have hv : ‖y / (1 - y) ^ 2‖ = 1 := by rw [norm_div, norm_pow, hay, hny]; norm_num
  have huv : ‖x / (1 - x) ^ 2 - y / (1 - y) ^ 2‖ = 1 := by
    have : x / (1 - x) ^ 2 - y / (1 - y) ^ 2
        = x * (1 - y / x) * (1 - x * y) / ((1 - x) ^ 2 * (1 - y) ^ 2) := by
      field_simp; ring
    rw [this, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, hax, hay, hnx, hxy, hxy']
    norm_num
  generalize x / (1 - x) ^ 2 = u at *
  generalize y / (1 - y) ^ 2 = v at *
  by_cases h6 : l ∣ 6
  · left
    have h6' : ‖(6 : Qbar l)‖ < 1 := by exact_mod_cast norm_nat_lt h6
    have : Lk 4 x - Lk 4 y = (u - v) * (1 + 6 * (u + v)) := by rw [h4x, h4y]; ring
    rw [this, norm_mul, huv, one_mul]
    refine nadd_eq norm_one ?_
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h6' (nadd_le hu.le hv.le)
  · right
    have h12 : ¬ l ∣ 12 := by
      intro h
      have hp : l.Prime := Fact.out
      have h' : l ∣ 6 ^ 2 := h.trans (by norm_num)
      exact h6 (hp.dvd_of_dvd_pow h')
    have h12' : ‖(12 : Qbar l)‖ = 1 := by exact_mod_cast norm_nat h12
    have hA := h3 x hx hx2
    have hB := h3 y hy hy2
    have hle : ‖Lk 3 x ^ 2 - Lk 3 y ^ 2‖ ≤ 1 :=
      nsub_le (by rw [norm_pow, hA]; norm_num) (by rw [norm_pow, hB]; norm_num)
    rcases hle.eq_or_lt with h | h
    · exact Or.inl h
    · right
      have : Lk 3 x * Lk 5 x - Lk 3 y * Lk 5 y
          = 12 * Lk 3 x ^ 2 * (u - v) + (Lk 3 x ^ 2 - Lk 3 y ^ 2) * (1 + 12 * v) := by
        rw [h5x, h5y]; ring
      rw [this]
      refine nadd_eq (by rw [norm_mul, norm_mul, norm_pow, h12', hA, huv]; norm_num) ?_
      rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h
        (nadd_le norm_one.le (by rw [norm_mul, h12', hv]; norm_num))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HeckeEx
section
noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularForm UpperTheory.V.Af
open scoped MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Sd

private def hM (p : ℕ) : Option (Fin p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(p : ℤ), 0; 0, 1]
  | some u => !![1, ((u : ℕ) : ℤ); 0, (p : ℤ)]

private theorem hM_det (p : ℕ) (x : Option (Fin p)) : (hM p x).det = p := by
  cases x <;> simp [hM, Matrix.det_fin_two_of]

private def hG {p : ℕ} (hp : p.Prime) (x : Option (Fin p)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix (hM p x)) (by
    rw [← RingHom.map_det, hM_det]; simpa using hp.ne_zero)

private def hT {p : ℕ} (hp : p.Prime) (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ x : Option (Fin p), χ ((hM p x 0 0 : ℤ) : ZMod N) • f ∣[(k : ℤ)] hG hp x

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.heckeEx :
    UpperTheory.V.Sd.HeckeEx :=
  _root_.UpperTheory.Reformulated.B.hecke_existence.heckeEx
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.LevelOne
section
open UpperHalfPlane CongruenceSubgroup UpperTheory.V.Af
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

private def GoodWt (k : ℕ) : Prop :=
  ∃ f : ModularForm 𝒮ℒ (k : ℤ), coef f 0 = 1 ∧ ∀ n, ∃ c : ℤ, coef f n = c

private lemma bern4 : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

private lemma bern6 : bernoulli 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
  norm_num [Finset.sum_range_succ, h5, Nat.choose, bernoulli'_four, bernoulli'_three, bernoulli'_two]

private lemma good0 : GoodWt 0 := by
  refine ⟨(1 : ModularForm 𝒮ℒ 0), ?_, fun n => ?_⟩
  · simp [coef, qExpansion_one]
  · refine ⟨if n = 0 then 1 else 0, ?_⟩
    simp [coef, qExpansion_one, PowerSeries.coeff_one]

private lemma good4 : GoodWt 4 := by
  refine ⟨ModularForm.E (k := 4) (by norm_num), ?_, fun n => ?_⟩
  · exact EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
  · refine ⟨if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ), ?_⟩
    unfold coef
    rw [EisensteinSeries.E_qExpansion_coeff _ (by decide), bern4]
    split_ifs
    · simp
    · push_cast; ring

private lemma good6 : GoodWt 6 := by
  refine ⟨ModularForm.E (k := 6) (by norm_num), ?_, fun n => ?_⟩
  · exact EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
  · refine ⟨if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ), ?_⟩
    unfold coef
    rw [EisensteinSeries.E_qExpansion_coeff _ (by decide), bern6]
    split_ifs
    · simp
    · push_cast; ring

private lemma good_add {a b : ℕ} (ha : GoodWt a) (hb : GoodWt b) : GoodWt (a + b) := by
  obtain ⟨f, hf0, hf⟩ := ha
  obtain ⟨g, hg0, hg⟩ := hb
  have h := ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f g
  have key : ∀ n, coef (ModularForm.mcast (show (a : ℤ) + b = ((a + b : ℕ) : ℤ) by push_cast; ring) (f.mul g)) n =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coef f p.1 * coef g p.2 := by
    intro n
    unfold coef
    rw [ModularForm.coe_mcast, h, PowerSeries.coeff_mul]
  refine ⟨ModularForm.mcast (show (a : ℤ) + b = ((a + b : ℕ) : ℤ) by push_cast; ring) (f.mul g), ?_, fun n => ?_⟩
  · rw [key]; simp [hf0, hg0]
  · choose c hc using hf
    choose d hd using hg
    refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * d p.2, ?_⟩
    rw [key]
    simp [hc, hd]

private lemma good_all (k : ℕ) (hk : Even k) (h2 : k ≠ 2) : GoodWt k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨m, hm⟩ := hk
    by_cases h0 : k = 0
    · subst h0; exact good0
    by_cases h6 : k = 6
    · subst h6; exact good6
    have : k = (k - 4) + 4 := by omega
    rw [this]
    exact good_add (ih _ (by omega) ⟨m - 2, by omega⟩ (by omega)) good4

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.levelOne :
    UpperTheory.V.Sd.LevelOne := by
  intro N k _ hk h2
  obtain ⟨f, hf0, hf⟩ := UpperTheory.V.Sd.good_all k hk h2
  have hle : (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)) ≤ 𝒮ℒ := Subgroup.map_le_range _ _
  refine ⟨⟨⟨f, fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (hle hγ)⟩, ModularFormClass.holo f,
    fun hc => f.bdd_at_cusps' (hc.mono hle)⟩, fun γ => ?_, hf0, hf⟩
  exact SlashInvariantFormClass.slash_action_eq f (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩
end

