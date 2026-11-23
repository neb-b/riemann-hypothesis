module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelInverseSymmetry
section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.KernelInverseSymmetry

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

def cK (k : I → ℕ) : ℝ := ∏ v, ((k v : ℝ) - 1) / (4 * Real.pi)

def T (k : I → ℕ) (p : X I × Gf) (γ : PG F) (y : D.Y) : ℂ :=
  D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) * (qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2)

theorem cK_nonneg (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) : 0 ≤ cK k :=
  Finset.prod_nonneg fun v _ => div_nonneg (by
    have h : (4 : ℝ) ≤ k v := by exact_mod_cast hk v
    linarith) (by positivity)

theorem nrm_pos (k : I → ℕ) (z : X I) : 0 < nrm k z :=
  Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.2 (z v).2) _

theorem act_out (γ : PG F) (z : D.Xs) : D.act γ.out z = γ • z := by
  rw [← D.mk_smulX]
  congr 1
  exact Quotient.out_eq γ

theorem norm_qj (hB : B1b) (k : ℕ) (hk : 1 ≤ k) (g : GL (Fin 2) ℝ) (z w : P) :
    ‖q1 k z (g • w)‖ * ‖j1 k g w‖ * |z.1.im| ^ ((k : ℝ) / 2) =
      ((k : ℝ) - 1) / (4 * Real.pi) * kap z (g • w) ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) := by
  obtain ⟨-, -, -, -, hj, hq, -⟩ := hB
  have e1 := hq k z (g • w) hk
  have e2 := hj k g w
  calc _ = (‖q1 k z (g • w)‖ * |z.1.im| ^ ((k : ℝ) / 2)) * ‖j1 k g w‖ := by ring
    _ = _ := by rw [e1, ← e2]; ring

theorem norm_term (hB : B1b) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (g : GL (Fin 2) F) (z w : X I) :
    ‖qq k z (D.act g w) * D.J k g w‖ * nrm k z = cK k * Kap k z (D.act g w) * nrm k w := by
  simp only [qq, Dat.J, Kap, nrm, cK, norm_mul, norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact norm_qj hB (k v) (hk v) (D.r v g) (z v) (w v)

theorem Kap_smul (hB : B1b) (k : I → ℕ) (δ : PG F) (z w : D.Xs) :
    Kap k (δ • z : D.Xs) (δ • w : D.Xs) = Kap k z w := by
  obtain ⟨-, -, -, hkap, -⟩ := hB
  rw [← act_out, ← act_out]
  unfold Kap
  refine Finset.prod_congr rfl fun v _ => ?_
  show kap (D.r v δ.out • z v) (D.r v δ.out • w v) ^ _ = _
  rw [hkap]

theorem Kap_symm (hBc : B1c) (k : I → ℕ) (z w : X I) : Kap k z w = Kap k w z := by
  obtain ⟨hsym, -⟩ := hBc
  unfold Kap
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [(hsym _ _).2.2]

theorem Kap_swap (hB : B1b) (hBc : B1c) (k : I → ℕ) (γ : PG F) (z w : D.Xs) :
    Kap k z (γ • w : D.Xs) = Kap k w (γ⁻¹ • z : D.Xs) := by
  rw [← Kap_smul D hB k γ⁻¹ z (γ • w), inv_smul_smul]
  exact Kap_symm hBc k _ _

theorem ee_mem (x : Gf) (h : D.ee x ≠ 0) : x ∈ D.H := by
  unfold Dat.ee at h
  split_ifs at h with hx
  · exact hx
  · exact absurd rfl h

theorem norm_ee (hAx : D.Ax) (x : Gf) : ‖D.ee x‖ ≤ 1 := by
  unfold Dat.ee
  split_ifs with hx
  · rw [hAx.χn]
  · simp

theorem supp (γ : PG F) (ω : D.Om) (x : Gf) (h : D.ee ((D.rep ω)⁻¹ * (D.j γ.out)⁻¹ * x) ≠ 0) :
    γ • ω = (show D.Om from (x : Gf ⧸ D.H)) := by
  have hm := ee_mem D _ h
  rw [mul_assoc] at hm
  have e : ((D.rep ω : Gf) : Gf ⧸ D.H) = (((D.j γ.out)⁻¹ * x : Gf) : Gf ⧸ D.H) := QuotientGroup.eq.2 hm
  have hω : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := Quotient.out_eq ω
  have hγ : ((γ.out : GL (Fin 2) F) : PG F) = γ := Quotient.out_eq γ
  have key : ((γ.out : GL (Fin 2) F) : PG F) • (show D.Om from (((D.j γ.out)⁻¹ * x : Gf) : Gf ⧸ D.H)) =
      (show D.Om from (x : Gf ⧸ D.H)) := by
    rw [D.mk_smulO, mul_inv_cancel_left]
  rw [← hω, e]
  rw [hγ] at key
  exact key

def xH (_D : Dat F I Gf) (p : X I × Gf) : _D.Om := (p.2 : Gf ⧸ _D.H)

def zX (_D : Dat F I Gf) (p : X I × Gf) : _D.Xs := p.1

def invEquiv (ω x : D.Om) : {γ : PG F // γ • ω = x} ≃ {δ : PG F // δ • x = ω} where
  toFun γ := ⟨γ.1⁻¹, by rw [inv_smul_eq_iff, γ.2]⟩
  invFun δ := ⟨δ.1⁻¹, by rw [inv_smul_eq_iff, δ.2]⟩
  left_inv γ := Subtype.ext (inv_inv _)
  right_inv δ := Subtype.ext (inv_inv _)

theorem T_le (hB : B1b) (hBc : B1c) (hAx : D.Ax) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (p : X I × Gf) (γ : PG F) (y : D.Y) :
    ‖T D k p γ y‖ₑ ≤ {γ : PG F | γ • y.1 = (xH D p)}.indicator
      (fun γ => ENNReal.ofReal (cK k / nrm k p.1 * nrm k y.2) *
        ENNReal.ofReal (Kap k y.2 (γ⁻¹ • (zX D p) : D.Xs))) γ := by
  by_cases hγ : γ • y.1 = (xH D p)
  · rw [Set.indicator_of_mem (show γ ∈ {γ : PG F | γ • y.1 = (xH D p)} from hγ)]
    rw [← ENNReal.ofReal_mul (mul_nonneg (div_nonneg (cK_nonneg k hk) (nrm_pos k p.1).le) (nrm_pos k y.2).le),
      ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have hn := norm_term D hB k (fun v => le_trans (by norm_num) (hk v)) γ.out p.1 y.2
    have hK : Kap k p.1 (D.act γ.out y.2) = Kap k y.2 (γ⁻¹ • (zX D p) : D.Xs) := by
      rw [act_out]
      exact Kap_swap D hB hBc k γ p.1 y.2
    rw [hK] at hn
    have hN := eq_div_of_mul_eq (nrm_pos k p.1).ne' hn
    have he := norm_ee D hAx ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2)
    unfold T
    rw [norm_mul]
    calc _ ≤ 1 * ‖qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = _ := by rw [hN]; ring
  · rw [Set.indicator_of_notMem (show γ ∉ {γ : PG F | γ • y.1 = (xH D p)} from hγ)]
    have h0 : D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) = 0 := by
      by_contra hne
      exact hγ (supp D γ y.1 p.2 hne)
    simp [T, h0]

theorem tsum_le (hB : B1b) (hBc : B1c) (hAx : D.Ax) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (p : X I × Gf) (Bnd : ℝ)
    (hS : ∀ (ω : D.Om) (w : X I), ∑' δ : {δ : PG F // δ • (xH D p) = ω},
      ENNReal.ofReal (Kap k w (δ.1 • (zX D p) : D.Xs)) ≤ ENNReal.ofReal Bnd) (y : D.Y) :
    ∑' γ, ‖T D k p γ y‖ₑ ≤ ENNReal.ofReal (cK k / nrm k p.1 * nrm k y.2) * ENNReal.ofReal Bnd := by
  have h1 := ENNReal.tsum_le_tsum fun γ => T_le D hB hBc hAx k hk p γ y
  rw [← tsum_subtype] at h1
  beta_reduce at h1
  rw [ENNReal.tsum_mul_left] at h1
  refine h1.trans (mul_le_mul' le_rfl (Eq.trans_le ?_ (hS y.1 y.2)))
  exact Equiv.tsum_eq (invEquiv D y.1 (xH D p))
    (fun δ => ENNReal.ofReal (Kap k y.2 (δ.1 • (zX D p) : D.Xs)))

theorem main (hB1a : B1a) (hB : B1b) (hBc : B1c) (hE0a : E0a) (hKS : KapSum) (hAx : D.Ax)
    (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (p : X I × Gf) :
    (∀ y : D.Y, Summable fun γ : PG F => ‖D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) *
      (qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2)‖) ∧
    Measurable (fun y => D.Kern k y p) ∧ ∃ C, ∀ y, ‖D.Kern k y p‖ ≤ C * nrm k y.2 := by
  obtain ⟨hcount, -, -, -, -, -, hborel, -⟩ := hE0a F I Gf D hAx
  obtain ⟨c₀, hc₀, hmink⟩ := hAx.mink
  obtain ⟨C, hCb⟩ := hKS F I Gf D hAx k hk c₀ hc₀
  obtain ⟨s, hs, hsle⟩ := hmink p.1 (D.rep (xH D p))
  obtain ⟨Bnd, hBnd, hS⟩ : ∃ Bnd : ℝ, 0 ≤ Bnd ∧ ∀ (ω : D.Om) (w : X I),
      ∑' δ : {δ : PG F // δ • (xH D p) = ω},
        ENNReal.ofReal (Kap k w (δ.1 • (zX D p) : D.Xs)) ≤ ENNReal.ofReal Bnd :=
    ⟨max (C * (1 + D.HtY s ((xH D p), p.1))) 0, le_max_right _ _, fun ω w =>
      (hCb ((xH D p), p.1) s hs hsle ω w).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hT := fun y => tsum_le D hB hBc hAx k hk p Bnd hS y
  have hfin : ∀ y : D.Y, ∑' γ, ‖T D k p γ y‖ₑ ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hT y)
  have hsumm : ∀ y : D.Y, Summable fun γ => ‖T D k p γ y‖ := fun y => by
    simpa only [toReal_enorm] using ENNReal.summable_toReal (hfin y)
  have hc0 : 0 ≤ cK k / nrm k p.1 := div_nonneg (cK_nonneg k hk) (nrm_pos k p.1).le
  have hbound : ∀ y : D.Y, ∑' γ, ‖T D k p γ y‖ ≤ cK k / nrm k p.1 * Bnd * nrm k y.2 := fun y => by
    have h1 : ∑' γ, ‖T D k p γ y‖ = (∑' γ, ‖T D k p γ y‖ₑ).toReal := by
      rw [ENNReal.tsum_toReal_eq (fun γ => enorm_ne_top)]
      simp only [toReal_enorm]
    rw [h1]
    refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg hc0 hBnd) (nrm_pos k y.2).le) ?_
    calc _ ≤ _ := hT y
      _ = ENNReal.ofReal (cK k / nrm k p.1 * Bnd * nrm k y.2) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hc0 (nrm_pos k y.2).le)]
        congr 1
        ring
  refine ⟨hsumm, ?_, ⟨cK k / nrm k p.1 * Bnd, fun y => (norm_tsum_le_tsum_norm (hsumm y)).trans (hbound y)⟩⟩
  haveI := hcount
  haveI := hborel
  obtain ⟨-, -, -, -, -, -, hjc, hqc, -⟩ := hB
  have hgc : ∀ g : GL (Fin 2) ℝ, Continuous fun z : P => g • z := fun g => (hB1a.2.2 g).1
  have hTm : ∀ γ : PG F, Measurable (T D k p γ) := fun γ => by
    have hG : Continuous fun w : D.Xs => qq k p.1 (D.act γ.out w) * D.J k γ.out w := by
      refine Continuous.mul ?_ ?_
      · refine continuous_finsetProd _ fun v _ => ?_
        exact (hqc (k v)).comp (continuous_const.prodMk ((hgc (D.r v γ.out)).comp (continuous_apply v)))
      · exact continuous_finsetProd _ fun v _ => (hjc (k v) (D.r v γ.out)).comp (continuous_apply v)
    exact ((Measurable.of_discrete (f := fun ω : D.Om => D.ee ((D.rep ω)⁻¹ * (D.j γ.out)⁻¹ * p.2))).comp
      measurable_fst).mul (hG.measurable.comp measurable_snd)
  have hlim : Tendsto (fun (s : Finset (PG F)) (y : D.Y) => ∑ γ ∈ s, T D k p γ y) atTop
      (𝓝 fun y => ∑' γ, T D k p γ y) :=
    tendsto_pi_nhds.2 fun y => ((hsumm y).of_norm).hasSum
  exact measurable_of_tendsto_metrizable' atTop (fun s => Finset.measurable_sum s fun γ _ => hTm γ) hlim

end UpperTheory.Esk.KernelInverseSymmetry

theorem UpperTheory.Esk.kernel_inverse_symmetry : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.faceMap_zero_comp_eq_one := by
  intro hB1a hB1b hB1c hE0a _ hKS F I Gf _ _ _ D hAx k hk _ p
  exact UpperTheory.Esk.KernelInverseSymmetry.main D hB1a hB1b hB1c hE0a hKS hAx k hk p
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelSeriesConvergesProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.KernelSeriesConvergence

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I]

theorem ht_e (D : Dat F I Gf) (z : X I) (x : Gf) :
    D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap; split_ifs <;> positivity

theorem Kap_nonneg (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun v _ => Real.rpow_nonneg (kap_nonneg _ _) _

theorem N_pos (z : X I) : 0 < ∏ v, |(z v).1.im| :=
  Finset.prod_pos fun v _ => abs_pos.2 (z v).2

theorem fix_of (γ : PG F) (h : γ.out 1 0 = 0) : Fix ![0, 1] γ := by
  refine ⟨γ.out 1 1, ?_⟩
  ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h]

theorem e_ne : (![0, 1] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 1

theorem kap_split (k : I → ℕ) (z w : X I) :
    Kap k z w = (Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)) *
      ((∏ v, |(w v).1.im|) / ∏ v, |(z v).1.im|) ^ ((1 : ℝ) / 2) := by
  rw [← Finset.prod_div_distrib, ← Real.finsetProd_rpow _ _ (fun v _ => by positivity), mul_assoc,
    ← Finset.prod_mul_distrib, Finset.prod_eq_one, mul_one]
  intro v _
  have h1 := abs_pos.2 (z v).2
  have h2 := abs_pos.2 (w v).2
  rw [← Real.mul_rpow (by positivity) (by positivity),
    show |(z v).1.im| / |(w v).1.im| * (|(w v).1.im| / |(z v).1.im|) = 1 by field_simp, Real.one_rpow]

theorem ratio (hE0d : E0d) {ι : Type} [Fintype ι] (D : Dat F I Gf) (hax : D.Ax) (a : ι → Gf) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (y : D.Y) (γ : PG F) (i : ι), ¬ Fix ![0, 1] γ →
      γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H) →
      (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.HtY ![0, 1] y ^ 2 ≤ C' * ∏ v, |(y.2 v).1.im| := by
  obtain ⟨h1, h2, -, h4, h5, -⟩ := hE0d F I Gf D hax
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := e_ne
  choose Cm hCm using fun i => hax.mul (a i)⁻¹
  refine ⟨∑ i, max (Cm i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _, fun y γ i hγ hi => ?_⟩
  have hγ' : γ.out 1 0 ≠ 0 := fun h => hγ (fix_of γ h)
  have hy : D.HtY ![0, 1] y = (∏ v, |(y.2 v).1.im|) * D.hf ![0, 1] (D.rep y.1) := ht_e D y.2 (D.rep y.1)
  have hgy : D.HtY ![0, 1] (γ • y) =
      (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1 * a i) := by
    have : γ • y = (((D.rep y.1 * a i : Gf) : Gf ⧸ D.H), γ • y.2) := Prod.ext hi rfl
    rw [this]; exact (h1 _ he _ _).trans (ht_e D _ _)
  have hprod : D.HtY ![0, 1] (γ • y) * D.HtY ![0, 1] y ≤ 1 := by
    have := h2 _ he γ.out y
    rw [QuotientGroup.out_eq'] at this
    rw [this, mul_comm]
    apply h5
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using hγ'
  have hx : 0 < D.hf ![0, 1] (D.rep y.1) := hax.pos _ he _
  have hxa : 0 < D.hf ![0, 1] (D.rep y.1 * a i) := hax.pos _ he _
  have hmul : D.hf ![0, 1] (D.rep y.1) ≤ Cm i * D.hf ![0, 1] (D.rep y.1 * a i) := by
    simpa using hCm i _ he (D.rep y.1 * a i)
  have hCm0 : 0 ≤ Cm i := by nlinarith
  have hNg : 0 ≤ ∏ v, |((γ • y.2 : D.Xs) v).1.im| := Finset.prod_nonneg fun v _ => abs_nonneg _
  have hN := (N_pos y.2).le
  have hHt : 0 ≤ D.HtY ![0, 1] y := (h4 _ he y).le
  have hHg : 0 ≤ D.HtY ![0, 1] (γ • y) := (h4 _ he _).le
  have hCi : Cm i ≤ ∑ j, max (Cm j) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (Cm j) 0) (fun j _ => le_max_right (Cm j) 0) (Finset.mem_univ i))
  have e1 : (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.HtY ![0, 1] y ^ 2 =
      ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1)) * D.HtY ![0, 1] y * ∏ v, |(y.2 v).1.im| := by
    rw [sq, hy]; ring
  have e2 : (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1) ≤ Cm i * D.HtY ![0, 1] (γ • y) := by
    rw [hgy]; nlinarith [mul_le_mul_of_nonneg_left hmul hNg]
  rw [e1]
  calc ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1)) * D.HtY ![0, 1] y * ∏ v, |(y.2 v).1.im|
      ≤ (Cm i * D.HtY ![0, 1] (γ • y)) * D.HtY ![0, 1] y * ∏ v, |(y.2 v).1.im| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e2 hHt) hN
    _ = Cm i * (D.HtY ![0, 1] (γ • y) * D.HtY ![0, 1] y) * ∏ v, |(y.2 v).1.im| := by ring
    _ ≤ Cm i * 1 * ∏ v, |(y.2 v).1.im| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hCm0) hN
    _ ≤ (∑ j, max (Cm j) 0) * ∏ v, |(y.2 v).1.im| := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_right hCi hN

theorem main (hE0c : KernelTermsInvariantBounded) (hE0d : E0d) (hPack : Pack) (hMult : Mult) (hKI : KapInt)
    {ι : Type} [Fintype ι] (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (hyp : D.Hyp k a) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ≥0, ∀ y : D.Y, c₀ ≤ D.HtY ![0, 1] y →
      ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ ≤ C := by
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := e_ne
  obtain ⟨-, -, -, ⟨CE, hCE⟩, hTe, -⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨C', hC'0, hC'⟩ := ratio hE0d D hyp.ax a
  obtain ⟨Cp, hCp⟩ := hPack F I Gf D hyp.ax
  obtain ⟨CM, hCM⟩ := hMult F I Gf D hyp.ax (1 / 16) c₀ (by norm_num) hc₀
  obtain ⟨CK, A, hK⟩ := hKI I k hyp.four
  have hm : ∀ v, Measurable fun w : D.Xs => (w v).1.im := fun v =>
    Complex.measurable_im.comp (measurable_subtype_coe.comp (measurable_pi_apply v))
  refine ⟨(Fintype.card ι : ℝ≥0) * Cp * A * CK *
    Real.toNNReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)), fun y hy => ?_⟩
  have hHt : 0 < D.HtY ![0, 1] y := hc₀.trans_le hy
  set Ht := D.HtY ![0, 1] y with hHtdef
  set h : D.Xs → ℝ≥0∞ := fun w => ENNReal.ofReal (Kap k y.2 w * ∏ v, (|(y.2 v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2))
    with hhdef
  set K : ℝ := max CE 0 * Real.sqrt C' / Ht with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ ≤
      ∑ i, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ.1 := by
    rintro ⟨γ, hγ⟩
    by_cases h0 : D.Te a γ.out (D.rep y.1) = 0
    · have : D.kk k a γ y = 0 := by simp [Dat.kk, Dat.kt, h0]
      simp [this]
    obtain ⟨i, hi⟩ := hTe γ y.1 h0
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ) (fun _ _ => bot_le) (Finset.mem_univ i))
    simp only [Set.indicator_of_mem (show γ ∈ {γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)} from hi)]
    rw [hhdef, ← ofReal_norm, ← ENNReal.ofReal_mul hK0]
    apply ENNReal.ofReal_le_ofReal
    have hr := hC' y γ i hγ hi
    have hN := N_pos y.2
    have hsq : ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ^ ((1 : ℝ) / 2) ≤ Real.sqrt C' / Ht := by
      rw [← Real.sqrt_eq_rpow]
      have : (∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im| ≤ C' / Ht ^ 2 := by
        rw [div_le_div_iff₀ hN (by positivity)]; linarith
      calc Real.sqrt ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ≤ Real.sqrt (C' / Ht ^ 2) :=
            Real.sqrt_le_sqrt this
        _ = Real.sqrt C' / Ht := by rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hHt.le]
    have hX : 0 ≤ Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2) :=
      mul_nonneg (Kap_nonneg _ _ _) (Finset.prod_nonneg fun v _ => by positivity)
    calc ‖D.kk k a γ y‖ ≤ CE * Kap k y.2 (γ • y.2 : D.Xs) := hCE γ y
      _ ≤ max CE 0 * Kap k y.2 (γ • y.2 : D.Xs) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Kap_nonneg _ _ _)
      _ = max CE 0 * ((Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) *
            ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ^ ((1 : ℝ) / 2)) := by
          congr 1; exact kap_split k y.2 _
      _ ≤ max CE 0 * ((Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) *
            (Real.sqrt C' / Ht)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hX) (le_max_right _ _)
      _ = K * (Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) := by
          rw [hKdef]; ring

  have hmeas : Measurable h :=
    ((hK y.2).1.mul (Finset.measurable_prod _ fun v _ =>
      (measurable_const.div (hm v).abs).pow_const _)).ennreal_ofReal
  have hA : ∀ w w' : D.Xs, Near (1 / 2) w w' → h w ≤ A * h w' := by
    intro w w' hn
    have := ENNReal.ofReal_le_ofReal ((hK y.2).2.2.2 w w' hn).2
    rwa [ENNReal.ofReal_mul A.coe_nonneg, ENNReal.ofReal_coe_nnreal] at this
  obtain ⟨hfin, hcard⟩ := hCM y ![0, 1] he hy
  have hcard' : ((({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal (max CM 0 * (1 + Ht)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hint : ∫⁻ w, h w ≤ CK := (hK y.2).2.2.1
  have hcos : ∀ i, ∑' γ : PG F, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ ≤
      ENNReal.ofReal K * (Cp * A * ENNReal.ofReal (max CM 0 * (1 + Ht)) * CK) := by
    intro i
    rw [← tsum_subtype, ENNReal.tsum_mul_left]
    gcongr
    calc ∑' γ : {γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}, h (γ.1 • y.2)
        ≤ Cp * A * ({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℝ≥0∞) * ∫⁻ w, h w :=
          hCp y _ h A hmeas hA hfin
      _ ≤ Cp * A * ENNReal.ofReal (max CM 0 * (1 + Ht)) * CK := by gcongr
  have hfinal : ENNReal.ofReal K * ENNReal.ofReal (max CM 0 * (1 + Ht)) ≤
      ENNReal.ofReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)) := by
    rw [← ENNReal.ofReal_mul hK0]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (1 + Ht) / Ht ≤ 1 + 1 / c₀ := by
      have := one_div_le_one_div_of_le hc₀ hy
      rw [add_div, div_self hHt.ne']; linarith
    have h2 : 0 ≤ max CE 0 * Real.sqrt C' * max CM 0 := by positivity
    calc K * (max CM 0 * (1 + Ht)) = max CE 0 * Real.sqrt C' * max CM 0 * ((1 + Ht) / Ht) := by
          rw [hKdef]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
  calc ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ
      ≤ ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ∑ i, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ.1 := ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' γ : PG F, ∑ i, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ :=
        (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective Subtype.val_injective _); exact _root_.le_rfl)
    _ = ∑ i, ∑' γ : PG F, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ := Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ ≤ ∑ i : ι, ENNReal.ofReal K * (Cp * A * ENNReal.ofReal (max CM 0 * (1 + Ht)) * CK) :=
        Finset.sum_le_sum fun i _ => hcos i
    _ = (Fintype.card ι : ℝ≥0∞) * Cp * A * CK * (ENNReal.ofReal K * ENNReal.ofReal (max CM 0 * (1 + Ht))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ (Fintype.card ι : ℝ≥0∞) * Cp * A * CK * ENNReal.ofReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)) := by
        gcongr
    _ = (((Fintype.card ι : ℝ≥0) * Cp * A * CK *
          Real.toNNReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)) : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.ofReal]; push_cast; ring

end UpperTheory.Esk.KernelSeriesConvergence

open UpperTheory.Esk in
theorem UpperTheory.Esk.kernel_series_converges_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.Pack → UpperTheory.Esk.Mult → UpperTheory.Esk.KapInt → UpperTheory.Esk.E1 := by
  intro _ hE0c hE0d hPack hMult hKI F I Gf ι _ _ _ _ D k a hyp c₀ hc₀
  obtain ⟨C, hC⟩ := KernelSeriesConvergence.main hE0c hE0d hPack hMult hKI D k a hyp c₀ hc₀
  refine ⟨C, fun y s hs hy => ?_⟩
  obtain ⟨-, h2, -, -, -, -, -, -, -, h10, h11⟩ := hE0d F I Gf D hyp.ax
  obtain ⟨-, h2c, -⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨δ, hδ⟩ := h10 s hs
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := KernelSeriesConvergence.e_ne
  have hy' : c₀ ≤ D.HtY ![0, 1] ((δ : PG F) • y) := by rw [h2 _ he δ y, hδ]; exact hy
  have hfix : ∀ γ : PG F, ¬ Fix s γ ↔ ¬ Fix ![0, 1] (MulAut.conj (δ : PG F) γ) := by
    intro γ
    have := h11 ![0, 1] γ.out δ
    rw [QuotientGroup.out_eq', hδ] at this
    exact not_congr this.symm
  let e : {γ : PG F // ¬ Fix s γ} ≃ {γ : PG F // ¬ Fix ![0, 1] γ} :=
    (MulAut.conj (δ : PG F)).toEquiv.subtypeEquiv hfix
  calc ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a γ.1 y‖ₑ
      = ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a (e γ).1 ((δ : PG F) • y)‖ₑ := by
        congr 1; funext γ
        rw [show (e γ).1 = (δ : PG F) * γ.1 * (δ : PG F)⁻¹ from rfl, h2c]
    _ = ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 ((δ : PG F) • y)‖ₑ :=
        e.tsum_eq (fun γ => ‖D.kk k a γ.1 ((δ : PG F) • y)‖ₑ)
    _ ≤ C := hC _ hy'
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfKapSum
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

theorem UpperTheory.Esk.pf_KapSum : UpperTheory.Esk.Pack → UpperTheory.Esk.Mult → UpperTheory.Esk.KapInt → UpperTheory.Esk.KapSum := by
  intro hPack hMult hKap F I Gf _ _ _ D hD k hk c₀ hc₀
  obtain ⟨C₁, hC₁⟩ := hPack F I Gf D hD
  obtain ⟨C₃, A₃, hK⟩ := hKap I k hk
  obtain ⟨C₂, hC₂⟩ := hMult F I Gf D hD (1 / 16) c₀ (by norm_num) hc₀
  refine ⟨(C₁ : ℝ) * A₃ * max C₂ 0 * C₃, ?_⟩
  intro y s hs hy ω' z
  obtain ⟨hfin, hcard⟩ := hC₂ y s hs hy
  obtain ⟨hmeas, hint, -, hnear⟩ := hK z
  have hpos : 0 ≤ 1 + D.HtY s y := by linarith
  have key : ∀ n : ℕ, (n : ℝ) ≤ C₂ * (1 + D.HtY s y) →
      (n : ℝ≥0∞) ≤ ENNReal.ofReal (max C₂ 0 * (1 + D.HtY s y)) := by
    intro n hn
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos))
  have hA : ∀ w w' : D.Xs, Near (1 / 2) w w' →
      ENNReal.ofReal (Kap k z w) ≤ (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w') := by
    intro w w' hww
    calc ENNReal.ofReal (Kap k z w) ≤ ENNReal.ofReal (A₃ * Kap k z w') :=
          ENNReal.ofReal_le_ofReal (hnear w w' hww).1
      _ = (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w') := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have hpack := hC₁ y ω' (fun w => ENNReal.ofReal (Kap k z w)) A₃
    (ENNReal.measurable_ofReal.comp hmeas) hA hfin
  refine hpack.trans ((mul_le_mul' (mul_le_mul' le_rfl (key _ hcard)) hint).trans (le_of_eq ?_))
  rw [show (C₁ : ℝ) * A₃ * max C₂ 0 * C₃ * (1 + D.HtY s y)
      = ((C₁ * A₃ * C₃ : ℝ≥0) : ℝ) * (max C₂ 0 * (1 + D.HtY s y)) by push_cast; ring,
    ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  push_cast
  ring
end
end

