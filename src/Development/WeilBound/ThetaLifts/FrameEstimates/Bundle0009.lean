module

public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0006
public import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0002
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0001
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.DomContinuous
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem dom_continuous (hB : ThetaBasic) (hT : GrpTop) (hE : EpsOf) (hp : IsPair B M χX χW om r s r' s') {𝓕}
    (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕) (hsb : φ ∈ SB _) (f : SInf F (Fin n × Fin d)) :
    Continuous (M.I om (pureA F f φ)) := by
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨hJ', -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  obtain ⟨i1, i2, -, -, -, -, -, hb⟩ := hT F E σ hp.base.cm d W.J hJ'
  obtain ⟨p, k, G, -, hG, hfin, hbd⟩ := hD φ hφ
  have hc := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 _ (pureA_mem f hsb)).1
  haveI : FirstCountableTopology (UA σ W.J) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i2
  refine continuous_iff_continuousAt.2 fun h₀ => ?_
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds h₀
  obtain ⟨C, hC⟩ := hb K hK
  have hpf : 0 ≤ p f := apply_nonneg p f
  refine continuousAt_of_dominated (bound := fun g => p f * (C : ℝ) ^ k * (G g).toReal)
    (Eventually.of_forall fun h => (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable) ?_
    ((integrable_toReal_of_lintegral_ne_top hG.aemeasurable hfin.ne).const_mul _)
    (Eventually.of_forall fun g => (hc.comp (continuous_const.prodMk continuous_id)).continuousAt)
  filter_upwards [hK0] with h hh
  filter_upwards [ae_lt_top hG hfin.ne] with g hg
  have e := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.ne) (hbd f g h)
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at e
  refine e.trans ?_
  have : (ht h : ℝ) ≤ C := hC h hh
  gcongr

theorem dom_bound (hp : IsPair B M χX χW om r s r' s') {𝓕} (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕) :
    ∃ k : ℕ, ∀ f : SInf F (Fin n × Fin d), ∃ C : ℝ, ∀ h, ‖M.I om (pureA F f φ) h‖ ≤ C * (ht h : ℝ) ^ k := by
  obtain ⟨p, k, G, -, hG, hfin, hb⟩ := hD φ hφ
  refine ⟨k, fun f => ⟨p f * (∫⁻ g in M.dom, G g ∂M.μ).toReal, fun h => ?_⟩⟩
  have h1 : ‖M.I om (pureA F f φ) h‖ₑ ≤ ENNReal.ofReal (p f * (ht h : ℝ) ^ k) * ∫⁻ g in M.dom, G g ∂M.μ := by
    rw [← lintegral_const_mul _ hG]
    exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun g => hb f g h)
  have e := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) h1
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (apply_nonneg p f) (by positivity))] at e
  exact e.trans (le_of_eq (by ring))

end

theorem iUMG_of (hB : ThetaBasic) (hT : GrpTop) (hE : EpsOf) (hD : IDer) (hL : Level) (hI : IInv) : IUMG := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp 𝓕 hdom φ hφ hsb f hf
  obtain ⟨k, hk⟩ := dom_bound hp hdom hφ
  refine ⟨⟨k, {u | ∃ f₁ ∈ M.Pol B.ψ B.emb, u = M.I om (pureA F f₁ φ)}, ⟨f, hf, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨f₁, hf₁, rfl⟩
    refine ⟨dom_continuous hB hT hE hp hdom hφ hsb f₁, hk f₁, fun γ hγ => ?_⟩
    obtain ⟨f₂, hf₂, -, hd⟩ := (hD F E σ B n d X W M χX χW om r s r' s' hp 𝓕 hdom φ hφ hsb f₁ hf₁).1 γ hγ
    exact ⟨_, ⟨f₂, hf₂, rfl⟩, hd⟩
  · obtain ⟨U, hU, hu⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp φ hsb
    refine ⟨U, hU, fun u huU h1 h => ?_⟩
    rw [← (hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem f hsb)).2.2 h u, hu u huU h1]

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.DomWeil
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem domWeilU_of (hT : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hQ : SqAll) (hI : LatInv) (hM : LatMeas) (hK : LatCpt)
    (hA : LatArch) (hL : LatTor) (hP : PosWt) (h2 : ConeIntegralsFinite) : DomWeilU := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp hw
  have hc := hp.base.cm
  obtain ⟨hJ, -, hr⟩ := hE F E σ B hp.base n X r s (Or.inl hp.herm)
  obtain ⟨hJ', -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  obtain ⟨fr, hg, -, -, hint, -⟩ := hS F E σ hc n X.J hJ
  obtain ⟨fr', hg', -, -, -, -⟩ := hS F E σ hc d W.J hJ'
  obtain ⟨N, hN⟩ := hL F E σ hc B.emb n d X.J W.J hJ hJ' fr fr' hg hg'
  obtain ⟨k, hk⟩ := latSum_redH hT hS hI hK hA hc B.emb hJ hJ' N
  refine ⟨k, fun φ hφ => ?_⟩
  obtain ⟨p, C, hpc, hC, hb⟩ := hQ F E σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨C', K, hC', hK0, hb'⟩ := hk C hC
  obtain ⟨K₀, Ω, hK₀, hΩ, hi⟩ := hint M.μ M.dom hp.good.haar hp.good.dom
  obtain ⟨C₁, K₁, hC₁, h₁⟩ := hK F E σ hc B.emb n d X.J W.J hJ hJ' Ω {1} hΩ isCompact_singleton C' N hC'
  obtain ⟨K₂, h₂'⟩ := hN C₁ hC₁
  have ha0 : fr'.a 0 = 1 := by
    have := hg'.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have h0 : (0 : Fin fr'.r → ℝ) ∈ Cone fr'.r := ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  have hmeas : Measurable fun g : UA σ X.J => latSum B.emb C' N Set.univ g (1 : UA σ W.J) ^ (1 / 2 : ℝ) :=
    (hM F E σ hc B.emb n d X.J W.J hJ hJ' C' N Set.univ hC' 1).pow_const _
  set D : ℝ := (Module.finrank ℚ E : ℝ) with hD
  have hD0 : 0 < D := by
    rw [hD]; exact_mod_cast Module.finrank_pos
  refine ⟨NNReal.mk K hK0 • p, fun g => latSum B.emb C' N Set.univ g (1 : UA σ W.J) ^ (1 / 2 : ℝ), ?_, hmeas, ?_, ?_⟩
  · exact (continuous_const.mul hpc : Continuous fun f => K * p f)
  · have hq : fr.r = 0 ∨ d + 2 * fr.r < 2 * n := by
      have := hr fr hg
      omega
    have hfin := (h2 n d fr.r 0 D hD0 hq (Or.inl rfl)).1
    set c : ℝ≥0∞ := ((K₁ : ℝ≥0∞) * K₂) ^ (1 / 2 : ℝ) with hcdef
    have hcfin : c < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
    have key := hi (fun t => c * ENNReal.ofReal (Real.exp (D * (d / 2 * ∑ i, t i)))) (by fun_prop) _ hmeas
      (fun γ hγ g => by
        have := hI F E σ hc B.emb n d X.J W.J hJ hJ' C' N Set.univ (by simp) γ hγ 1 (one_mem _) g 1
        rw [mul_one] at this
        rw [this])
      (fun t ht' κ hκ => by
        have e1 := h₁ Set.univ (fr.a t) 1 κ hκ 1 rfl
        rw [mul_one] at e1
        have e2 := h₂' t ht' 0 h0
        rw [ha0] at e2
        have e3 : posWt n d t (0 : Fin fr'.r → ℝ) ≤ d * ∑ i, t i := by
          simpa using (hP n d fr.r fr'.r t 0 ht' h0).1
        have e4 : latSum B.emb C' N Set.univ (fr.a t * κ) (1 : UA σ W.J) ≤
            ((K₁ : ℝ≥0∞) * K₂) * ENNReal.ofReal (Real.exp (D * (d / 2 * ∑ i, t i))) ^ (2 : ℝ) := by
          refine e1.trans ?_
          rw [mul_assoc]
          refine mul_le_mul_right (e2.trans (mul_le_mul_right ?_ _)) _
          rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          nlinarith
        refine (ENNReal.rpow_le_rpow e4 (by norm_num)).trans (le_of_eq ?_)
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num [hcdef])
    refine key.trans_lt (ENNReal.mul_lt_top hK₀ ?_)
    simp only [mul_assoc c]
    rw [lintegral_const_mul' _ _ hcfin.ne]
    exact ENNReal.mul_lt_top hcfin hfin
  · intro f g h
    have e := (hb f g h).trans (mul_le_mul_right (hb' g h) _)
    have hpf : 0 ≤ p f := apply_nonneg p f
    have e2 : ‖theta om (pureA F f φ) g h‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (K * p f * (ht h : ℝ) ^ k) ^ (2 : ℝ) * latSum B.emb C' N Set.univ g (1 : UA σ W.J) := by
      rw [ENNReal.rpow_two, ENNReal.rpow_two]
      refine e.trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_pow hpf, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
      congr 2
      ring
    have e3 := ENNReal.rpow_le_rpow e2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at e3
    norm_num at e3
    simpa [NNReal.smul_def] using e3

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.ExistsColsDetNeZero
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_cols_det_ne_zero {K : Type} [Field K] {i d : ℕ} (A : Matrix (Fin i) (Fin d) K)
    (hA : LinearIndependent K A.row) : ∃ c : Fin i → Fin d, Function.Injective c ∧ (A.submatrix id c).det ≠ 0 := by
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K A.col
  haveI : Fintype κ := Fintype.ofInjective a ha
  have hcard : Fintype.card κ = i := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_cols, hA.rank_matrix, Fintype.card_fin]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hu : IsUnit (A.submatrix id (a ∘ e)) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

theorem exists_one_le_emb {x : E} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) : ∃ φ : E →+* ℂ, 1 ≤ ‖φ x‖ := by
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace E, 1 ≤ w x := by
    by_contra hne
    push Not at hne
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact absurd (InfinitePlace.one_le_of_lt_one (w := w) (a := (⟨x, hx⟩ : 𝓞 E))
      (fun h => h0 (congrArg Subtype.val h)) fun z _ => hne z) (not_le.2 (hne w))
  exact ⟨w.embedding, by rwa [InfinitePlace.norm_embedding_eq]⟩

theorem sum_lam_le_psum {d y : ℕ} {lam : Fin d → (Fin y → ℝ) →ₗ[ℝ] ℝ} {jx jy : Fin y ↪ Fin d} (h1 : ∀ i j, jx i ≠ jy j)
    (h2 : ∀ i t, lam (jx i) t = t i ∧ lam (jy i) t = -t i) (h3 : ∀ k, (∀ i, jx i ≠ k ∧ jy i ≠ k) → lam k = 0)
    {t : Fin y → ℝ} (ht : t ∈ Cone y) {i : ℕ} {c : Fin i → Fin d} (hc : Function.Injective c) :
    ∑ a, lam (c a) t ≤ psum t i := by
  classical
  have key : ∀ θ : ℝ, 0 ≤ θ → ∑ a, lam (c a) t ≤ ∑ j, max 0 (t j - θ) + i * θ := by
    intro θ hθ
    have e := sum_lam h1 h2 h3 (fun u => max 0 (u - θ)) t
    have e1 : ∀ j, max 0 (-t j - θ) = 0 := fun j => max_eq_left (by linarith [ht.2 j])
    simp only [e1, max_eq_left (show 0 - θ ≤ 0 by linarith), Finset.sum_const_zero, add_zero, mul_zero] at e
    rw [← e]
    have e2 : ∑ a, max 0 (lam (c a) t - θ) ≤ ∑ k, max 0 (lam k t - θ) := by
      exact (Finset.sum_map Finset.univ ⟨c, hc⟩ fun k => max 0 (lam k t - θ)).symm.trans_le
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => le_max_left _ _)
    have e3 : ∑ a, lam (c a) t ≤ ∑ a, (max 0 (lam (c a) t - θ) + θ) :=
      Finset.sum_le_sum fun a _ => by linarith [le_max_right 0 (lam (c a) t - θ)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e3
    linarith
  by_cases hi : i < y
  · refine (key (t ⟨i, hi⟩) (ht.2 _)).trans (le_of_eq ?_)
    have e : ∀ j : Fin y, max 0 (t j - t ⟨i, hi⟩) =
        (if j.val < i then t j else 0) - if j.val < i then t ⟨i, hi⟩ else 0 := by
      intro j
      split_ifs with h
      · exact max_eq_right (sub_nonneg.2 (ht.1 (show j ≤ ⟨i, hi⟩ from h.le)))
      · rw [sub_zero]
        exact max_eq_left (sub_nonpos.2 (ht.1 (show (⟨i, hi⟩ : Fin y) ≤ j from not_lt.1 h)))
    have hcard : (Finset.univ.filter fun j : Fin y => j.val < i).card = i := by
      rw [Fin.card_filter_val_lt]
      omega
    simp only [e, Finset.sum_sub_distrib]
    rw [← Finset.sum_filter (fun j : Fin y => j.val < i) fun _ => t ⟨i, hi⟩, Finset.sum_const, hcard, nsmul_eq_mul, psum]
    ring
  · refine (key 0 le_rfl).trans (le_of_eq ?_)
    rw [mul_zero, add_zero, psum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos (by omega), sub_zero, max_eq_right (ht.2 j)]

theorem psum_eq {q i : ℕ} (hi : i ≤ q) (s : Fin q → ℝ) : psum s i = ∑ a : Fin i, s (Fin.castLE hi a) := by
  exact (Fintype.sum_of_injective _ (Fin.castLE_injective hi) _ (fun j : Fin q => if j.val < i then s j else 0)
    (fun j hj => if_neg fun h => hj ⟨⟨j, h⟩, rfl⟩) fun a => (if_pos a.2).symm).symm

theorem minor_of : FrameBasis → Minor := by
  intro hB F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' C hC
  classical
  obtain ⟨b, lam, ix, iy, h1, h2, h3, -, hb⟩ := hB F E σ hσ n J hJ fr hfr
  obtain ⟨b', lam', jx, jy, h1', h2', h3', -, hb'⟩ := hB F E σ hσ d J' hJ' fr' hfr'
  obtain ⟨m, K, hm, hK, h⟩ := diag_coords τ hfr hfr' hb hb' hC
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast n.factorial_pos
  set A : ℝ := n.factorial * m * K with hA
  have hA1 : 1 ≤ A := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hm') hK
  refine ⟨A⁻¹, by positivity, fun s hs t ht x hx hsupp => ?_⟩
  obtain ⟨ha, hsz⟩ := h s t x
  have hint := ha hsupp
  have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ)
  set z := sz τ (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ)
  set ξ := (b⁻¹).1 * x * (b'⁻¹).1ᵀ with hξ
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin (fr.r + 1) => psum s i.val - psum t i.val)
  have hiq : i.val ≤ fr.r := Nat.lt_succ_iff.1 i.2
  have hqn : fr.r ≤ n := by simpa using Fintype.card_le_of_embedding iy
  have hrk : ξ.rank = n := by
    rw [hξ, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by
      rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _))]
    exact hx
  have hli : LinearIndependent E ξ.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← Matrix.rank_eq_finrank_span_row, hrk,
      Fintype.card_fin]
  let ρ : Fin i.val → Fin n := fun a => iy (Fin.castLE hiq a)
  obtain ⟨c, hc, hdet⟩ := exists_cols_det_ne_zero (ξ.submatrix ρ id)
    (hli.comp ρ (iy.injective.comp (Fin.castLE_injective hiq)))
  set M : Matrix (Fin i.val) (Fin i.val) E := (ξ.submatrix ρ id).submatrix id c with hM
  have hI : IsIntegral ℤ ((m : E) • M).det := IsIntegral.det fun a a' => hint _ _
  have hI0 : ((m : E) • M).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hm.ne')) hdet
  obtain ⟨φ, hφ⟩ := exists_one_le_emb hI hI0
  obtain ⟨w, hw⟩ := norm_emb hσ τ φ
  rw [hw, Matrix.det_smul, map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast,
    Fintype.card_fin] at hφ
  let N : Matrix (Fin i.val) (Fin i.val) ℂ := Matrix.of fun a a' =>
    (Real.exp (s (Fin.castLE hiq a)) : ℂ) * ((Real.exp (-lam' (c a') t) : ℂ) * (τ w).1 (M a a'))
  have hN : ‖N.det‖ = Real.exp (psum s i - ∑ a, lam' (c a) t) * ‖(τ w).1 M.det‖ := by
    have e1 : N.det = (∏ a, (Real.exp (s (Fin.castLE hiq a)) : ℂ)) * ((∏ a, (Real.exp (-lam' (c a) t) : ℂ)) *
        (τ w).1 M.det) := by
      rw [RingHom.map_det, ← Matrix.det_mul_row, ← Matrix.det_mul_column]
      rfl
    rw [e1, ← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Real.exp_sum, ← Real.exp_sum, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add, psum_eq hiq, Finset.sum_neg_distrib,
      sub_eq_add_neg]
  have hent : ∀ a a', ‖N a a'‖ ≤ K * (1 + z) := by
    intro a a'
    let T : InfinitePlace F → Fin n → Fin d → ℝ := fun w k l => Real.exp (-(lam k s + lam' l t)) * ‖(τ w).1 (ξ k l)‖
    have hT : ∀ w k l, 0 ≤ T w k l := fun w k l => by positivity
    have e : ‖N a a'‖ = T w (ρ a) (c a') := by
      simp only [N, T, ρ, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        (h2 _ _).2, neg_add, neg_neg, Real.exp_add, mul_assoc]
      rfl
    have l1 := Finset.single_le_sum (f := T w (ρ a)) (fun _ _ => hT _ _ _) (Finset.mem_univ (c a'))
    have l2 := Finset.single_le_sum (f := fun k => ∑ l, T w k l)
      (fun _ _ => Finset.sum_nonneg fun _ _ => hT _ _ _) (Finset.mem_univ (ρ a))
    have l3 := Finset.single_le_sum (f := fun w => ∑ k, ∑ l, T w k l)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hT _ _ _) (Finset.mem_univ w)
    have l4 : ∑ w, ∑ k, ∑ l, T w k l ≤ K * z := hsz
    linarith
  have hdle : ‖N.det‖ ≤ i.val.factorial * (K * (1 + z)) ^ i.val := by
    have := Matrix.det_le (A := N) (abv := NormedField.toAbsoluteValue ℂ) (x := K * (1 + z)) hent
    rw [Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hv : Real.exp (viol s t) ≤ (A * (1 + z)) ^ (n + 1) := by
    have e1 : Real.exp (viol s t) ≤ Real.exp (psum s i - ∑ a, lam' (c a) t) := by
      rw [viol, ← hi]
      exact Real.exp_le_exp.2 (by linarith [sum_lam_le_psum h1' h2' h3' ht hc])
    have hin : i.val ≤ n := hiq.trans hqn
    have e2 : (i.val.factorial : ℝ) ≤ (n.factorial : ℝ) ^ (n + 1) :=
      le_trans (by exact_mod_cast Nat.factorial_le hin) (le_self_pow₀ hf (by omega))
    have hB1 : 1 ≤ (m : ℝ) * (K * (1 + z)) :=
      one_le_mul_of_one_le_of_one_le hm' (one_le_mul_of_one_le_of_one_le hK (by linarith))
    calc _ ≤ Real.exp (psum s i - ∑ a, lam' (c a) t) * ((m : ℝ) ^ i.val * ‖(τ w).1 M.det‖) :=
          e1.trans (le_mul_of_one_le_right (Real.exp_pos _).le hφ)
      _ = (m : ℝ) ^ i.val * ‖N.det‖ := by rw [hN]; ring
      _ ≤ (m : ℝ) ^ i.val * (i.val.factorial * (K * (1 + z)) ^ i.val) := by gcongr
      _ = i.val.factorial * ((m : ℝ) * (K * (1 + z))) ^ i.val := by rw [mul_pow (m : ℝ)]; ring
      _ ≤ (n.factorial : ℝ) ^ (n + 1) * ((m : ℝ) * (K * (1 + z))) ^ (n + 1) :=
          mul_le_mul e2 (pow_le_pow_right₀ hB1 (by omega)) (by positivity) (by positivity)
      _ = _ := by rw [← mul_pow, hA]; congr 1; ring
  rw [inv_mul_le_iff₀ (by positivity)]
  refine le_of_pow_le_pow_left₀ (n := n + 1) (by omega) (by positivity) ?_
  rw [← Real.exp_nat_mul, show ((n + 1 : ℕ) : ℝ) * (viol s t / (n + 1)) = viol s t by push_cast; field_simp]
  exact hv

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.IInvOfParts
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem topGroup_UA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) : IsTopologicalGroup (UA σ J) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin n) (AE F E)) := inferInstance
  exact Subgroup.instIsTopologicalGroupSubtypeMem _

theorem iInv_of_parts (hB : ThetaBasic) (hU : PositivityTheory.ThKF.Unimod) (hE : EpsOf) : IInv := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp Φ hΦ
  have hi := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1
  refine ⟨fun γ hγ h => ?_, fun g₀ => funext fun h => ?_, fun h h' => ?_⟩
  · simp only [Model.I]
    congr 1
    funext g
    simpa using hi 1 (one_mem _) γ hγ g h
  · obtain ⟨h1, -, h3⟩ := hU F E σ hp.base.cm n X.J 1 (fun i j => by simpa using hp.herm.herm i j)
      (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1.2
    have := topGroup_UA σ X.J
    have := h3 _ hp.good.haar
    have := hp.good.haar
    have : BorelSpace (UA σ X.J) := ⟨rfl⟩
    have e : ∀ g, theta om (om (g₀, 1) Φ) g h = theta om Φ (g * g₀) h := fun g => by
      simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [Model.I, e]
    exact PositivityTheory.ThKF.L2.integral_right hp.good.dom (fun g => theta om Φ g h)
      (fun γ hγ g => by simpa using hi γ hγ 1 (one_mem _) g h) g₀
  · simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem iInv_of (hB : ThetaBasic) : IInv := iInv_of_parts hB PositivityTheory.ThKF.unimodularity_holds epsOf_of

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LatFull
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem latFull_of : LatTor → Minor → LatFull := by
  intro hT hM F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' m
  obtain ⟨N, hN⟩ := hT F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr'
  refine ⟨N + m * (n + 1), fun C hC => ?_⟩
  obtain ⟨K, hK⟩ := hN C hC
  obtain ⟨c, hc, h⟩ := hM F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' C hC
  refine ⟨((c ^ (m * (n + 1)))⁻¹).toNNReal * K, fun s hs t ht => ?_⟩
  let i : fullRank E n d → (Set.univ : Set (Matrix (Fin n) (Fin d) E)) := fun x => ⟨x.1, trivial⟩
  have hi : Function.Injective i := fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)
  let g : ↥(Set.univ : Set (Matrix (Fin n) (Fin d) E)) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (maj τ C N (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ))
  calc _ ≤ ∑' x, ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) * g (i x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := h s hs t ht x.1 x.2
        have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        unfold maj
        split_ifs with hx
        · have h2 := pow_le_pow_left₀ (by positivity) (h1 hx) (m * (n + 1))
          rw [mul_pow, ← Real.exp_nat_mul,
            show ((m * (n + 1) : ℕ) : ℝ) * (viol s t / (n + 1)) = m * viol s t by push_cast; field_simp] at h2
          rw [pow_add, mul_inv, mul_comm, Real.exp_neg, ← mul_inv (c ^ _)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) h2) (by positivity)
        · simp
    _ ≤ ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) *
          (K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * posWt n d s t))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective hi g).trans (hK s hs t ht)
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.coe_mul]
        change _ = ENNReal.ofReal _ * _ * _
        ring

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.UMGLin
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem umgLin_pow_le {x C : ℝ} {z : ℂ} (hx : 1 ≤ x) {k m : ℕ} (hk : k ≤ m) (h : ‖z‖ ≤ C * x ^ k) :
    ‖z‖ ≤ |C| * x ^ m :=
  h.trans <| mul_le_mul (le_abs_self C) (pow_le_pow_right₀ hx hk) (pow_nonneg (zero_le_one.trans hx) k) (abs_nonneg C)

theorem umgLin_of : UMGLin := by
  intro F E _ _ _ _ _ σ _ _ d W _ f f' hf hf' a b
  obtain ⟨k, S, hfS, hS⟩ := hf
  obtain ⟨k', S', hfS', hS'⟩ := hf'
  refine ⟨max k k', {g | ∃ f₁ ∈ S, ∃ f₁' ∈ S', g = a • f₁ + b • f₁'}, ⟨f, hfS, f', hfS', rfl⟩, ?_⟩
  rintro _ ⟨g, hg, g', hg', rfl⟩
  obtain ⟨hc, ⟨C, hC⟩, hd⟩ := hS g hg
  obtain ⟨hc', ⟨C', hC'⟩, hd'⟩ := hS' g' hg'
  refine ⟨(hc.const_smul a).add (hc'.const_smul b), ⟨‖a‖ * |C| + ‖b‖ * |C'|, fun h => ?_⟩, fun γ hγ => ?_⟩
  · have hx : (1 : ℝ) ≤ (ht h : ℝ) := by exact_mod_cast one_le_ht h
    have h1 := umgLin_pow_le hx (le_max_left k k') (hC h)
    have h2 := umgLin_pow_le hx (le_max_right k k') (hC' h)
    have h3 : ‖(a • g + b • g') h‖ ≤ ‖a‖ * ‖g h‖ + ‖b‖ * ‖g' h‖ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    have h4 := mul_le_mul_of_nonneg_left h1 (norm_nonneg a)
    have h5 := mul_le_mul_of_nonneg_left h2 (norm_nonneg b)
    linarith
  · obtain ⟨g₂, hg₂, e⟩ := hd γ hγ
    obtain ⟨g₂', hg₂', e'⟩ := hd' γ hγ
    exact ⟨a • g₂ + b • g₂', ⟨g₂, hg₂, g₂', hg₂', rfl⟩, fun h => ((e h).const_mul a).add ((e' h).const_mul b)⟩

end PositivityTheory.ThKEst

end
end

