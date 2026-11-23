module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModPrincNorm
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem sqD_indep {d : ℕ} (hd : 0 < d) (u v : ℚ) (h : (u : ℂ) + v * sqD d = 0) : u = 0 ∧ v = 0 := by
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sqD] at hre him
  exact ⟨hre, him.resolve_right (by
    intro h0
    apply hs
    simpa using h0)⟩

theorem sqK_li {d : ℕ} (hd : 0 < d) : LinearIndependent ℚ ![(1 : KQ d), sqK d] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  apply sqD_indep hd
  have := congrArg (fun z : KQ d => (z : ℂ)) h
  simpa [sqK, Algebra.smul_def] using this

theorem sqK_decomp {d : ℕ} (z : KQ d) (p q : ℚ) (h : (z : ℂ) = p + q * sqD d) :
    z = p • (1 : KQ d) + q • sqK d := by
  apply Subtype.ext
  simp [sqK, Algebra.smul_def, h]

theorem sqK_span {d : ℕ} : ⊤ ≤ Submodule.span ℚ (Set.range ![(1 : KQ d), sqK d]) := by
  intro z _
  obtain ⟨u, v, h⟩ := (KQ_mem_iff d z).1 z.2
  rw [sqK_decomp z u v h]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

def bKQ {d : ℕ} (hd : 0 < d) : Module.Basis (Fin 2) ℚ (KQ d) := Module.Basis.mk (sqK_li hd) sqK_span

theorem sqK_mul_self (d : ℕ) : sqK d * sqK d = -(d : KQ d) := by
  apply Subtype.ext
  have := sqD_sq d
  simp [sqK, ← this, sq]

theorem norm_KQ {d : ℕ} (hd : 0 < d) (z : KQ d) (p q : ℚ) (h : (z : ℂ) = p + q * sqD d) :
    Algebra.norm ℚ z = p ^ 2 + d * q ^ 2 := by
  have h0 : bKQ hd 0 = 1 := by simp [bKQ]
  have h1 : bKQ hd 1 = sqK d := by simp [bKQ]
  have hz := sqK_decomp z p q h
  have e0 : z * bKQ hd 0 = p • bKQ hd 0 + q • bKQ hd 1 := by
    rw [h0, h1, mul_one]; exact hz
  have e1 : z * bKQ hd 1 = (-(d : ℚ) * q) • bKQ hd 0 + p • bKQ hd 1 := by
    rw [h0, h1, hz, add_mul, smul_mul_assoc, smul_mul_assoc, sqK_mul_self, one_mul]
    simp only [Algebra.smul_def, mul_one]
    push_cast
    ring
  rw [Algebra.norm_eq_matrix_det (bKQ hd), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1, map_add (f := _), map_smul, Module.Basis.repr_self]
  simp
  ring

theorem absNorm_span {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (x : 𝓞 (KQ d)) (a b : ℤ)
    (h : (((x : KQ d) : ℂ)) = a + b * omegaK d) :
    4 * (Ideal.absNorm (Ideal.span {x}) : ℤ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
  have hd0 : 0 < d := by omega
  have hn := norm_KQ hd0 (x : KQ d) (a + b / 2) (b / 2) (by
    rw [h]; simp only [omegaK, sqD]; push_cast; ring)
  rw [← Algebra.coe_norm_int] at hn
  have hn' : 4 * Algebra.norm ℤ x = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
    have : (4 : ℚ) * (Algebra.norm ℤ x : ℚ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
      rw [hn]; ring
    exact_mod_cast this
  have hpos : 0 ≤ Algebra.norm ℤ x := by
    have : 0 ≤ 4 * Algebra.norm ℤ x := by
      rw [hn']
      have : 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + (d : ℤ)) = (2 * a + b) ^ 2 + d * b ^ 2 := by ring
      rw [this]; positivity
    omega
  rw [Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg hpos, hn']

theorem princ_form {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (v : HeightOneSpectrum (𝓞 (KQ d)))
    (hv : ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ = 1) :
    ∃ a b : ℤ, 4 * (Nat.card (𝓞 (KQ d) ⧸ v.asIdeal) : ℤ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
  rw [ClassGroup.mk0_eq_one_iff] at hv
  obtain ⟨x, hx⟩ := hv.principal
  obtain ⟨a, b, hab⟩ := quadInt hsf hd x
  refine ⟨a, b, ?_⟩
  rw [← absNorm_span hsf hd x a b hab, Ideal.absNorm_apply, Submodule.cardQuot_apply, hx]

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem IsMF.analytic {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) : AnalyticAt ℂ (cuspFunction 1 f) 0 := by
  obtain ⟨g, hg⟩ := hf
  have hfg : f = ⇑g := funext fun τ => (hg τ).symm
  subst hfg
  exact ModularFormClass.analyticAt_cuspFunction_zero g one_pos (by simp)

theorem qExp_AA_pow (n : ℕ) : qExpansion 1 (fun τ => AA τ ^ n) = aC ^ n := by
  induction n with
  | zero =>
    have : (fun τ => AA τ ^ 0) = (1 : ℍ → ℂ) := by funext τ; simp
    rw [this, qExpansion_one, pow_zero]
  | succ n ih =>
    have : (fun τ => AA τ ^ (n + 1)) = (fun τ => AA τ ^ n) * AA := by funext τ; simp [pow_succ]
    rw [this, qExpansion_mul (isMF_AA.pow n).analytic isMF_AA.analytic, ih, pow_succ, aC_eq]

theorem aC_coeff_zero : PowerSeries.coeff 0 aC = 1 := by
  have h4 : PowerSeries.coeff 0 e4Z = 1 := by rw [e4Z, PowerSeries.coeff_mk, if_pos rfl]
  rw [aC, aZ, PowerSeries.coeff_map]
  simp [pow_succ, PowerSeries.coeff_mul, h4]

theorem IsMF.div_DD {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f)
    (h0 : PowerSeries.coeff 0 (qExpansion 1 f) = 0) :
    ∃ h : ℍ → ℂ, IsMF (k - 12) h ∧ (∀ τ, f τ = DD τ * h τ) ∧
      qExpansion 1 f = dC * qExpansion 1 h := by
  obtain ⟨g, hg⟩ := hf
  obtain rfl : (⇑g : ℍ → ℂ) = f := funext hg
  refine ⟨CuspForm.discriminantEquiv (toCuspForm g h0), ⟨_, fun _ => rfl⟩, fun τ => ?_, ?_⟩
  · exact (discriminant_mul_discriminantEquiv_apply (toCuspForm g h0) τ).symm
  · rw [dC_eq]
    exact qExpansion_eq_qExpansion_discriminant_mul g h0

theorem coeff_mul_low (V G : PowerSeries ℂ) (hV : PowerSeries.coeff 0 V = 1) (n : ℕ)
    (hG : ∀ i < n, PowerSeries.coeff i G = 0) :
    (∀ i < n, PowerSeries.coeff i (V * G) = 0) ∧
      PowerSeries.coeff n (V * G) = PowerSeries.coeff n G := by
  constructor
  · intro i hi
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hG x.2 (by omega), mul_zero]
  · rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
    · rw [hV, one_mul]
    · intro x hx hne
      obtain ⟨a, b⟩ := x
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have hb : b < n := by
        by_contra hb'
        apply hne
        have ha0 : a = 0 := by simp only at hx; omega
        have hbn : b = n := by simp only at hx; omega
        rw [ha0, hbn]
      rw [hG b hb, mul_zero]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h

theorem exists_dC_inv : ∃ v : PowerSeries ℤ, PowerSeries.coeff 0 v = 1 ∧
    ∀ H : PowerSeries ℂ, PowerSeries.X * H = v.map (Int.castRingHom ℂ) * (dC * H) := by
  set u : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) dZ with hu
  have hd0 : PowerSeries.coeff 0 dZ = 0 := by
    rw [dZ, PowerSeries.coeff_mk]
    simp [e4Z, e6Z, pow_succ, PowerSeries.coeff_mul]
  have hd1 : PowerSeries.coeff 1 dZ = 1 := by
    rw [dZ, PowerSeries.coeff_mk]
    simp [e4Z, e6Z, pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ] <;> norm_num
  have hXu : dZ = PowerSeries.X * u := by
    ext n
    rcases n with _ | n
    · rw [hd0, PowerSeries.coeff_zero_X_mul]
    · rw [PowerSeries.coeff_succ_X_mul, hu, PowerSeries.coeff_mk]
  have hu0 : PowerSeries.constantCoeff u = ((1 : ℤˣ) : ℤ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hu, PowerSeries.coeff_mk, zero_add, hd1, Units.val_one]
  refine ⟨PowerSeries.invOfUnit u 1, ?_, fun H => ?_⟩
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
  · have hinv := PowerSeries.mul_invOfUnit u 1 hu0
    have hdC : dC = PowerSeries.X * u.map (Int.castRingHom ℂ) := by
      rw [dC, hXu, map_mul, PowerSeries.map_X]
    rw [hdC]
    have h1 : (u.map (Int.castRingHom ℂ)) * (PowerSeries.invOfUnit u 1).map (Int.castRingHom ℂ) = 1 := by
      rw [← map_mul, hinv, map_one]
    linear_combination (-(PowerSeries.X * H)) * h1

theorem coeffIn_of_dC_mul (R : Subring ℂ) (H : PowerSeries ℂ) (h : CoeffIn R (dC * H)) : CoeffIn R H := by
  obtain ⟨v, -, hv⟩ := exists_dC_inv
  intro n
  rw [← PowerSeries.coeff_succ_X_mul, hv H, PowerSeries.coeff_mul]
  refine sum_mem fun x _ => mul_mem ?_ (h x.2)
  rw [PowerSeries.coeff_map, eq_intCast]
  exact intCast_mem _ _

theorem low_of_dC_mul (H : PowerSeries ℂ) (n0 : ℕ) (u : ℂ) (hu : u ≠ 0)
    (h0 : ∀ n < n0, PowerSeries.coeff n (dC * H) = 0) (h1 : PowerSeries.coeff n0 (dC * H) = u) :
    ∃ k, n0 = k + 1 ∧ (∀ n < k, PowerSeries.coeff n H = 0) ∧ PowerSeries.coeff k H = u := by
  obtain ⟨v, hv0, hv⟩ := exists_dC_inv
  have hV : PowerSeries.coeff 0 (v.map (Int.castRingHom ℂ)) = 1 := by
    rw [PowerSeries.coeff_map, hv0, map_one]
  obtain ⟨hlow, hn0⟩ := coeff_mul_low _ _ hV n0 h0
  rw [h1, ← hv H] at hn0
  rw [← hv H] at hlow
  rcases n0 with _ | k
  · rw [PowerSeries.coeff_zero_X_mul] at hn0
    exact absurd hn0.symm hu
  · refine ⟨k, rfl, fun n hn => ?_, ?_⟩
    · rw [← PowerSeries.coeff_succ_X_mul]
      exact hlow _ (by omega)
    · rw [← PowerSeries.coeff_succ_X_mul]
      exact hn0

theorem exists_integral_poly_of_qExpansion (R : Subring ℂ) (N : ℕ) : ∀ f : ℍ → ℂ, IsMF (12 * (N : ℤ)) f →
    CoeffIn R (qExpansion 1 f) →
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧
      (∀ τ, f τ = DD τ ^ N * P.eval (jT τ)) ∧
      ∀ (n0 : ℕ) (u : ℂ), u ≠ 0 → (∀ n < n0, PowerSeries.coeff n (qExpansion 1 f) = 0) →
        PowerSeries.coeff n0 (qExpansion 1 f) = u → P.leadingCoeff = u := by
  induction N with
  | zero =>
    intro f hf hR
    obtain ⟨g, hg⟩ := hf.congr_weight (k' := 0) (by simp)
    obtain ⟨c, hc⟩ := levelOne_weight_zero_const g
    have hfc : f = c • (1 : ℍ → ℂ) := by
      funext τ; rw [← hg τ, hc]; simp
    have hq : qExpansion 1 f = c • (1 : PowerSeries ℂ) := by
      have h1 : AnalyticAt ℂ (cuspFunction 1 (1 : ℍ → ℂ)) 0 := by
        have : IsMF 0 (1 : ℍ → ℂ) := ⟨1, fun τ => by simp⟩
        exact this.analytic
      rw [hfc, qExpansion_smul h1, qExpansion_one]
    refine ⟨Polynomial.C c, fun i => ?_, by simp, fun τ => ?_, fun n0 u hu h0 h1 => ?_⟩
    · have := hR 0
      rw [hq] at this
      rw [Polynomial.coeff_C]
      split_ifs
      · simpa using this
      · exact R.zero_mem
    · rw [hfc]; simp
    · rw [hq] at h1
      rw [Polynomial.leadingCoeff_C]
      cases n0 with
      | zero => simpa using h1
      | succ k =>
        exfalso; apply hu; rw [← h1]
        simp [PowerSeries.coeff_one]
  | succ N ih =>
    intro f hf hR
    set a0 : ℂ := PowerSeries.coeff 0 (qExpansion 1 f) with ha0
    have hA : IsMF (12 * ((N + 1 : ℕ) : ℤ)) (fun τ => AA τ ^ (N + 1)) :=
      (isMF_AA.pow (N + 1)).congr_weight (by ring)
    have hcA : IsMF (12 * ((N + 1 : ℕ) : ℤ)) (fun τ => a0 * AA τ ^ (N + 1)) := hA.const_mul a0
    have hg : IsMF (12 * ((N + 1 : ℕ) : ℤ)) (fun τ => f τ - a0 * AA τ ^ (N + 1)) := hf.sub hcA
    have hqg : qExpansion 1 (fun τ => f τ - a0 * AA τ ^ (N + 1)) =
        qExpansion 1 f - a0 • aC ^ (N + 1) := by
      have e1 : (fun τ => f τ - a0 * AA τ ^ (N + 1)) = f - a0 • (fun τ => AA τ ^ (N + 1)) := by
        funext τ; simp
      have e2 : (fun τ => a0 * AA τ ^ (N + 1)) = a0 • (fun τ => AA τ ^ (N + 1)) := by
        funext τ; simp
      rw [e1, qExpansion_sub hf.analytic (e2 ▸ hcA.analytic), qExpansion_smul hA.analytic,
        qExp_AA_pow]
    have haR : a0 ∈ R := hR 0
    have hac : ∀ n, PowerSeries.coeff n (aC ^ (N + 1)) ∈ R := by
      intro n
      have : aC ^ (N + 1) = (aZ ^ (N + 1)).map (Int.castRingHom ℂ) := by rw [map_pow]; rfl
      rw [this, PowerSeries.coeff_map]
      exact intCast_mem R _
    have hac0 : PowerSeries.coeff 0 (aC ^ (N + 1)) = 1 := by
      have := aC_coeff_zero
      simp only [PowerSeries.coeff_zero_eq_constantCoeff] at this ⊢
      rw [map_pow, this, one_pow]
    have hg0 : PowerSeries.coeff 0 (qExpansion 1 (fun τ => f τ - a0 * AA τ ^ (N + 1))) = 0 := by
      rw [hqg, map_sub, PowerSeries.coeff_smul, hac0]; simp [ha0]
    obtain ⟨h, hh, hfh, hqh⟩ := hg.div_DD hg0
    have hh' : IsMF (12 * (N : ℤ)) h := hh.congr_weight (by push_cast; ring)
    have hRh : CoeffIn R (qExpansion 1 h) := by
      apply coeffIn_of_dC_mul
      rw [← hqh, hqg]
      intro n
      rw [map_sub, PowerSeries.coeff_smul]
      exact R.sub_mem (hR n) (R.mul_mem haR (hac n))
    obtain ⟨P', hP1, hP2, hP3, hP4⟩ := ih h hh' hRh
    refine ⟨Polynomial.C a0 * Polynomial.X ^ (N + 1) + P', fun i => ?_, ?_, fun τ => ?_,
      fun n0 u hu h0 h1 => ?_⟩
    · rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
      refine R.add_mem ?_ (hP1 i)
      split_ifs
      · exact haR
      · exact R.zero_mem
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by omega))
      exact Polynomial.natDegree_C_mul_X_pow_le _ _
    · have hD := DD_ne_zero τ
      have e := hfh τ
      rw [hP3 τ] at e
      have : f τ = a0 * AA τ ^ (N + 1) + DD τ * (DD τ ^ N * P'.eval (jT τ)) := by
        rw [← e]; ring
      rw [this]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      have hj : DD τ ^ (N + 1) * jT τ ^ (N + 1) = AA τ ^ (N + 1) := by
        rw [← mul_pow, jT, mul_div_cancel₀ _ hD]
      rw [← hj]; ring
    · by_cases hz : a0 = 0
      · have hq' : qExpansion 1 f = dC * qExpansion 1 h := by
          rw [← hqh, hqg, hz]; simp
        rw [hq'] at h0 h1
        obtain ⟨k, -, hk0, hk1⟩ := low_of_dC_mul _ n0 u hu h0 h1
        rw [hz]; simp only [map_zero, zero_mul, zero_add]
        exact hP4 k u hu hk0 hk1
      · have hn0 : n0 = 0 := by
          by_contra hne
          exact hz (h0 0 (Nat.pos_of_ne_zero hne))
        subst hn0
        rw [Polynomial.leadingCoeff_add_of_degree_lt', Polynomial.leadingCoeff_mul_X_pow,
          Polynomial.leadingCoeff_C]
        · exact h1
        · rw [Polynomial.degree_C_mul_X_pow _ hz]
          refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hP2) ?_
          exact_mod_cast Nat.lt_succ_self N

theorem qPrin (R : Subring ℂ) (N : ℕ) (f : ℍ → ℂ) (hf : IsMF (12 * (N : ℤ)) f)
    (hR : CoeffIn R (qExpansion 1 f)) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧
      ∀ τ, f τ = DD τ ^ N * P.eval (jT τ) := by
  obtain ⟨P, h1, h2, h3, -⟩ := exists_integral_poly_of_qExpansion R N f hf hR
  exact ⟨P, h1, h2, h3⟩

theorem qPrin_low (R : Subring ℂ) (N : ℕ) (f : ℍ → ℂ) (hf : IsMF (12 * (N : ℤ)) f)
    (hR : CoeffIn R (qExpansion 1 f)) (n0 : ℕ) (u : ℂ) (hu : u ≠ 0)
    (h0 : ∀ n < n0, PowerSeries.coeff n (qExpansion 1 f) = 0)
    (h1 : PowerSeries.coeff n0 (qExpansion 1 f) = u) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧ P.leadingCoeff = u ∧
      ∀ τ, f τ = DD τ ^ N * P.eval (jT τ) := by
  obtain ⟨P, hc, hd, he, hl⟩ := exists_integral_poly_of_qExpansion R N f hf hR
  exact ⟨P, hc, hd, hl n0 u hu h0 h1, he⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModSepInt
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_int_multiple {Ω : Type*} [Field Ω] [CharZero Ω] {β : Ω} (hβ : IsIntegral ℤ β) (h0 : β ≠ 0) :
    ∃ (n : ℤ) (γ : Ω), n ≠ 0 ∧ IsIntegral ℤ γ ∧ (n : Ω) = β * γ := by
  obtain ⟨p, hpm, hp0⟩ := id hβ
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpm.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hq
  have hq0 : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  have haq : Polynomial.aeval β q = 0 := by
    have h1 : Polynomial.aeval β p = 0 := by rw [Polynomial.aeval_def]; exact hp0
    rw [hpq, map_mul, map_pow, Polynomial.aeval_X] at h1
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ h0)
  refine ⟨q.coeff 0, -(Polynomial.aeval β q.divX), hq0, ?_, ?_⟩
  · have hmem := adjoin_le_integralClosure hβ (Polynomial.aeval_mem_adjoin_singleton ℤ β (p := q.divX))
    exact (neg_mem hmem : _ ∈ integralClosure ℤ Ω)
  · have h2 := congrArg (Polynomial.aeval β) (Polynomial.divX_mul_X_add q)
    rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, haq, eq_intCast] at h2
    linear_combination h2

theorem mem_valuationSubring_of_isIntegral {Ω : Type*} [Field Ω] {x : Ω} (hx : IsIntegral ℤ x)
    (A : ValuationSubring Ω) : x ∈ A := by
  have hA : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hA
  rw [← hy]
  exact y.2

theorem sepInt {Ω : Type*} [Field Ω] [CharZero Ω] (s : Finset Ω) (hs : ∀ r ∈ s, IsIntegral ℤ r) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ A : ValuationSubring Ω, r - r' ∈ A.nonunits →
      (n : Ω) ∈ A.nonunits := by
  classical
  have key : ∀ q ∈ s.offDiag, ∃ (m : ℤ) (γ : Ω), m ≠ 0 ∧ IsIntegral ℤ γ ∧ (m : Ω) = (q.1 - q.2) * γ := by
    intro q hq
    rw [Finset.mem_offDiag] at hq
    exact exists_int_multiple ((hs _ hq.1).sub (hs _ hq.2.1)) (sub_ne_zero.2 hq.2.2)
  choose! m γ hm hγ hmγ using key
  refine ⟨∏ q ∈ s.offDiag, m q, Finset.prod_ne_zero_iff.2 hm, ?_⟩
  intro r hr r' hr' hne A hA
  have hq : (r, r') ∈ s.offDiag := Finset.mem_offDiag.2 ⟨hr, hr', hne⟩
  rw [Int.cast_prod, ← Finset.mul_prod_erase _ _ hq]
  rw [ValuationSubring.mem_nonunits_iff] at hA ⊢
  rw [Valuation.map_mul, hmγ _ hq, Valuation.map_mul]
  have h1 : A.valuation (γ (r, r')) ≤ 1 :=
    (A.valuation_le_one_iff _).2 (mem_valuationSubring_of_isIntegral (hγ _ hq) A)
  have h2 : A.valuation (∏ q ∈ s.offDiag.erase (r, r'), (m q : Ω)) ≤ 1 :=
    (A.valuation_le_one_iff _).2 (prod_mem fun q _ => intCast_mem _ _)
  calc _ ≤ A.valuation (r - r') * 1 * 1 := mul_le_mul' (mul_le_mul' le_rfl h1) h2
    _ < 1 := by rw [mul_one, mul_one]; exact hA

theorem finite_places (E : Type*) [Field E] [NumberField E] {n : ℤ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 E) | (n : 𝓞 E) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {(n : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

end ReciprocityTheory.ChartRestriction.L1
end
end

