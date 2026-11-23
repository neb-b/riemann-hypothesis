module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivVanishesOfTranslationInvariance

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsOpenFrames
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical Topology

namespace GlobalTheory.SW.Neumann

noncomputable section

theorem diffOn_tsum {H ι : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    {U : Set H} (hU : IsOpen U) {w : H → ℝ} (hw : ContinuousOn w U) {g : ι → H → ℂ}
    (hg : ∀ i, DifferentiableOn ℂ (g i) U) {u : ι → ℝ} (hu : Summable u) (hu0 : ∀ i, 0 ≤ u i)
    (hb : ∀ i, ∀ x ∈ U, ‖g i x‖ ≤ u i * w x) :
    DifferentiableOn ℂ (fun x => ∑' i, g i x) U := by
  refine GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal hU hg fun x hx => ?_
  have h1 : ∀ᶠ z in 𝓝 x, w z < w x + 1 :=
    (hw.continuousAt (hU.mem_nhds hx)).eventually (gt_mem_nhds (by linarith))
  refine ⟨_, Filter.inter_mem (hU.mem_nhds hx) h1, fun i => u i * (w x + 1), hu.mul_right _,
    fun i z hz => (hb i z hz.1).trans (mul_le_mul_of_nonneg_left (le_of_lt hz.2) (hu0 i))⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cont_dmin (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
  have h : Continuous fun x : Frame X.Ψ r => FD.gram τ.1 X.Gm (mat x τ) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [FD.gram, hermC, FD.col, mat, Matrix.of_apply]
    fun_prop
  exact (h.matrix_submatrix _ _).matrix_det

theorem isOpen_frames : IsOpen X.dom := by
  have h : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x; simp [Data.dom, GG]
  rw [h]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun
      (show Continuous fun x : Frame X.Ψ r => mat x τ from continuous_apply τ).matrix_det
      continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp
      (cont_dmin X τ i)))

theorem dmin_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h
  have := (hx τ).2 i
  rw [h] at this
  simp at this

def fac (la : Wt X.Ψ r) (x : Frame X.Ψ r) : ℝ :=
  ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)

theorem fac_pos (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : 0 < fac X la x :=
  Finset.prod_pos fun τ _ => Finset.prod_pos fun _ _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _))) _

theorem fac_cont (la : Wt X.Ψ r) : ContinuousOn (fun x => (fac X la x)⁻¹) X.dom := by
  refine ContinuousOn.inv₀ ?_ fun x hx => (fac_pos X la hx).ne'
  refine continuousOn_finsetProd _ fun τ _ => continuousOn_finsetProd _ fun i _ => ?_
  refine ContinuousOn.rpow_const ?_ fun x hx => Or.inl ?_
  · exact (((cont_dmin X τ _).continuousOn).div (cont_dmin X τ _).continuousOn
      fun x hx => dmin_ne X hx τ _).norm
  · exact norm_ne_zero_iff.mpr (div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _))

theorem pnorm_le_iff (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (B : ℝ) : X.pnorm la P x ≤ B ↔ ‖P x‖ ≤ B * (fac X la x)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (fac_pos X la hx)]; rfl

omit [IsCMField E] in
theorem mapL_mul (γ δ : GL (Fin r) E) (L : Lt E r) : mapL (γ * δ) L = mapL γ (mapL δ L) := by
  unfold mapL
  rw [← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]
  rfl

omit [IsCMField E] in
theorem mapL_one (L : Lt E r) : mapL (1 : GL (Fin r) E) L = L := by
  unfold mapL
  rw [Units.val_one, Matrix.toLin'_one]
  exact Submodule.map_id L

def mapE (γ : GL (Fin r) E) : Lt E r ≃ Lt E r where
  toFun := mapL γ
  invFun := mapL γ⁻¹
  left_inv L := by rw [← mapL_mul, inv_mul_cancel, mapL_one]
  right_inv L := by rw [← mapL_mul, mul_inv_cancel, mapL_one]

def op (𝓛 : Set (Lt E r)) (C : Lt E r → Lt E r → ℂ) (a : ℝ) (G : Lt E r → Frame X.Ψ r → ℂ)
    (L : Lt E r) (x : Frame X.Ψ r) : ℂ :=
  -(a : ℂ)⁻¹ * ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, C L L'.1 * G L'.1 x

variable {X} {Δ : Subgroup (GL (Fin r) E)} {𝓛 : Set (Lt E r)} {μ : GL (Fin r) E → Lt E r → ℂ}
  {la : Wt X.Ψ r} {C : Lt E r → Lt E r → ℂ} {a θ : ℝ}

theorem op_bound (ha : 0 < a)
    (hC : ∀ L ∈ 𝓛, Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖C L L'.1‖) ∧
      ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖ ≤ θ * a)
    {G : Lt E r → Frame X.Ψ r → ℂ} {B : ℝ} (hB : 0 ≤ B) {x : Frame X.Ψ r}
    (hG : ∀ L ∈ 𝓛, ‖G L x‖ ≤ B) {L : Lt E r} (hL : L ∈ 𝓛) :
    ‖op X 𝓛 C a G L x‖ ≤ θ * B := by
  have h1 : ‖∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, C L L'.1 * G L'.1 x‖ ≤
      (∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖) * B := by
    refine tsum_of_norm_bounded ((hC L hL).1.hasSum.mul_right B) fun L' => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hG _ L'.2.1) (norm_nonneg _)
  have h2 := h1.trans (mul_le_mul_of_nonneg_right (hC L hL).2 hB)
  unfold op
  rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg ha.le,
    inv_mul_le_iff₀ ha]
  linarith

theorem op_form (ha : 0 < a)
    (hμ : ∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛 ∧ ‖μ γ L‖ = 1)
    (hC : ∀ L ∈ 𝓛, Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖C L L'.1‖) ∧
      ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖ ≤ θ * a)
    (hinv : ∀ γ ∈ Δ, ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛,
      C (mapL γ L) (mapL γ L') * μ γ L * conj (μ γ L') = C L L')
    {G : Lt E r → Frame X.Ψ r → ℂ} (hG : IsForm X Δ 𝓛 μ la G) :
    IsForm X Δ 𝓛 μ la (op X 𝓛 C a G) := by
  obtain ⟨B, hB⟩ := hG.bdd
  have hB' : ∀ L ∈ 𝓛, ∀ x ∈ X.dom, ‖G L x‖ ≤ max B 0 * (fac X la x)⁻¹ := fun L hL x hx =>
    (pnorm_le_iff X la _ hx _).1 ((hB L hL x hx).trans (le_max_left _ _))
  refine ⟨fun L hL => ?_, fun L hL x hx b hb => ?_, fun γ hγ L hL x hx => ?_,
    θ * max B 0, fun L hL x hx => ?_⟩
  · refine DifferentiableOn.const_mul (diffOn_tsum (isOpen_frames X) (fac_cont X la)
      (fun L' => (hG.hol _ L'.2.1).const_mul _) ((hC L hL).1.mul_right (max B 0))
      (fun L' => mul_nonneg (norm_nonneg _) (le_max_right _ _)) fun L' x hx => ?_) _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB' _ L'.2.1 x hx) (norm_nonneg _)
  · unfold op
    rw [mul_left_comm, ← tsum_mul_left (a := bchar la b)]
    congr 1
    refine tsum_congr fun L' => ?_
    rw [hG.bor _ L'.2.1 x hx b hb]; ring
  · have he : ∀ L', (L' ∈ 𝓛 ∧ L' ≠ L) ↔ (mapE γ L' ∈ 𝓛 ∧ mapE γ L' ≠ mapL γ L) := by
      intro L'
      refine and_congr ⟨fun h => (hμ γ hγ L' h).1, fun h => ?_⟩ (mapE γ).injective.ne_iff.symm
      have := (hμ γ⁻¹ (Δ.inv_mem hγ) _ h).1
      rwa [show mapL γ⁻¹ (mapE γ L') = L' from (mapE γ).left_inv L'] at this
    unfold op
    rw [mul_left_comm, ← tsum_mul_left (a := (μ γ L)⁻¹),
      ← ((mapE γ).subtypeEquiv he).tsum_eq]
    congr 1
    refine tsum_congr fun L' => ?_
    change C (mapL γ L) (mapL γ L'.1) * G (mapL γ L'.1) (lact γ x) = _
    rw [hG.aut γ hγ _ L'.2.1 x hx, ← hinv γ hγ L hL _ L'.2.1,
      ← Complex.inv_eq_conj (hμ γ hγ _ L'.2.1).2]
    have h0 : μ γ L ≠ 0 := norm_ne_zero_iff.1 (by rw [(hμ γ hγ L hL).2]; exact one_ne_zero)
    field_simp
  · rw [pnorm_le_iff X la _ hx, mul_assoc]
    exact op_bound ha hC (mul_nonneg (le_max_right _ _) (inv_pos.2 (fac_pos X la hx)).le)
      (fun L hL => hB' L hL x hx) hL

end

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (μ : GL (Fin r) E → Lt E r → ℂ) (la : Wt X.Ψ r) (C : Lt E r → Lt E r → ℂ) (a θ : ℝ), 0 < a → θ < 1 → (∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛 ∧ ‖μ γ L‖ = 1) → (∀ γ ∈ Δ, ∀ x ∈ X.dom, lact γ x ∈ X.dom) → (∀ L ∈ 𝓛, C L L = a ∧ Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖C L L'.1‖) ∧ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖ ≤ θ * a) → (∀ γ ∈ Δ, ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, C (mapL γ L) (mapL γ L') * μ γ L * conj (μ γ L') = C L L') → ∀ F, IsForm X Δ 𝓛 μ la F → ∃ F', IsForm X Δ 𝓛 μ la F' ∧ ∀ L ∈ 𝓛, ∀ x ∈ X.dom, F L x = ∑' L' : 𝓛, C L L'.1 * F' L'.1 x := by
  intro E _ _ _ r X Δ 𝓛 μ la C a θ₀ ha hθ₀ hμ _ hC₀ hinv F hF
  set θ : ℝ := max θ₀ 0 with hθ
  have hθ0 : 0 ≤ θ := le_max_right _ _
  have hθ1 : θ < 1 := max_lt hθ₀ one_pos
  have hC : ∀ L ∈ 𝓛, Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖C L L'.1‖) ∧
      ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖ ≤ θ * a := fun L hL =>
    ⟨(hC₀ L hL).2.1, (hC₀ L hL).2.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ha.le)⟩
  obtain ⟨G, hG0, hGs⟩ : ∃ G : ℕ → Lt E r → Frame X.Ψ r → ℂ, G 0 = F ∧
      ∀ k, G (k + 1) = op X 𝓛 C a (G k) :=
    ⟨fun k => (op X 𝓛 C a)^[k] F, rfl, fun k => Function.iterate_succ_apply' _ _ _⟩
  have hGf : ∀ k, IsForm X Δ 𝓛 μ la (G k) := by
    intro k
    induction k with
    | zero => rwa [hG0]
    | succ k ih => rw [hGs]; exact op_form ha hμ hC hinv ih
  obtain ⟨B₀, hB₀⟩ := hF.bdd
  set B : ℝ := max B₀ 0 with hBd
  have hB0 : 0 ≤ B := le_max_right _ _
  have hw : ∀ x ∈ X.dom, 0 ≤ (fac X la x)⁻¹ := fun x hx => (inv_pos.2 (fac_pos X la hx)).le
  have hGb : ∀ k, ∀ x ∈ X.dom, ∀ L ∈ 𝓛, ‖G k L x‖ ≤ θ ^ k * B * (fac X la x)⁻¹ := by
    intro k x hx
    induction k with
    | zero =>
      intro L hL
      rw [hG0, pow_zero, one_mul]
      exact (pnorm_le_iff X la _ hx _).1 ((hB₀ L hL x hx).trans (le_max_left _ _))
    | succ k ih =>
      intro L hL
      rw [hGs]
      refine (op_bound ha hC (mul_nonneg (by positivity) (hw x hx)) ih hL).trans (le_of_eq ?_)
      ring
  have hgeo : Summable fun k : ℕ => θ ^ k * B :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_right B
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  refine ⟨fun L x => (a : ℂ)⁻¹ * ∑' k, G k L x, ⟨fun L hL => ?_, fun L hL x hx b hb => ?_,
    fun γ hγ L hL x hx => ?_, ‖(a : ℂ)⁻¹‖ * ∑' k : ℕ, θ ^ k * B, fun L hL x hx => ?_⟩,
    fun L hL x hx => ?_⟩
  · exact (diffOn_tsum (isOpen_frames X) (fac_cont X la) (fun k => (hGf k).hol L hL) hgeo
      (fun k => by positivity) fun k x hx => hGb k x hx L hL).const_mul _
  · rw [mul_left_comm, ← tsum_mul_left (a := bchar la b)]
    congr 1
    exact tsum_congr fun k => (hGf k).bor L hL x hx b hb
  · rw [mul_left_comm, ← tsum_mul_left (a := (μ γ L)⁻¹)]
    congr 1
    exact tsum_congr fun k => (hGf k).aut γ hγ L hL x hx
  · rw [pnorm_le_iff X la _ hx, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (tsum_of_norm_bounded (hgeo.hasSum.mul_right _)
      fun k => hGb k x hx L hL) (norm_nonneg _)
  · have hs : Summable fun k => G k L x :=
      Summable.of_norm_bounded (hgeo.mul_right _) fun k => hGb k x hx L hL
    have hp : Summable fun p : {L' // L' ∈ 𝓛 ∧ L' ≠ L} × ℕ =>
        (a : ℂ)⁻¹ * (C L p.1.1 * G p.2 p.1.1 x) := by
      refine Summable.mul_left _ (Summable.of_norm_bounded
        (Summable.mul_of_nonneg (hC L hL).1 (hgeo.mul_right (fac X la x)⁻¹)
          (fun _ => norm_nonneg _) fun k => mul_nonneg (by positivity) (hw x hx)) fun p => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hGb _ x hx _ p.1.2.1) (norm_nonneg _)
    have hcomm := Summable.tsum_comm (f := fun (L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}) (k : ℕ) =>
      (a : ℂ)⁻¹ * (C L L'.1 * G k L'.1 x)) hp
    have hterm : ∀ L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ∑' k, (a : ℂ)⁻¹ * (C L L'.1 * G k L'.1 x) =
        C L L'.1 * ((a : ℂ)⁻¹ * ∑' k, G k L'.1 x) := by
      intro L'
      rw [tsum_mul_left, tsum_mul_left]; ring
    have hk : ∀ k, ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, (a : ℂ)⁻¹ * (C L L'.1 * G k L'.1 x) =
        -G (k + 1) L x := by
      intro k
      rw [tsum_mul_left, hGs, op]; ring
    have hsum : HasSum (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} =>
        C L L'.1 * ((a : ℂ)⁻¹ * ∑' k, G k L'.1 x)) (-∑' k, G (k + 1) L x) := by
      have h := hp.prod.hasSum
      simp only at h
      rw [← hcomm] at h
      simp only [hterm, hk, tsum_neg] at h
      exact h
    have hall : ∀ s : Set (Lt E r), s = {L} ∪ {L' | L' ∈ 𝓛 ∧ L' ≠ L} →
        HasSum (fun L' : s => C L L'.1 * ((a : ℂ)⁻¹ * ∑' k, G k L'.1 x))
          (C L L * ((a : ℂ)⁻¹ * ∑' k, G k L x) + -∑' k, G (k + 1) L x) := by
      rintro s rfl
      exact HasSum.add_disjoint (f := fun L' => C L L' * ((a : ℂ)⁻¹ * ∑' k, G k L' x))
        (by simp) (hasSum_singleton L fun L' => C L L' * ((a : ℂ)⁻¹ * ∑' k, G k L' x)) hsum
    rw [(hall 𝓛 ?_).tsum_eq, (hC₀ L hL).1, mul_inv_cancel_left₀ hac, hs.tsum_eq_zero_add, hG0]
    · ring
    · ext L'
      by_cases h : L' = L <;> simp [h, hL]

end GlobalTheory.SW.Neumann
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivEqSumList
section
open Filter Topology
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.SW.KernSym

variable {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

noncomputable abbrev lst (m : σ →₀ ℕ) : List σ := (Finsupp.toMultiset m).toList

theorem polyDeriv_eq_sum_list (P : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} {x : W}
    (hF : AnalyticAt ℂ F x) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F x = ∑ m ∈ P.support, P.coeff m * lineDerivList ℂ ((lst m).map u) F x := by
  rw [dirPolyDeriv_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dirPolyDeriv_monomial_eq_lineDerivList (Multiset.coe_toList _) u hF]

theorem polyDeriv_polyDeriv (P Q : MvPolynomial σ ℂ) (u : σ → W) {F : W × W → ℂ}
    (hF : ∀ p, AnalyticAt ℂ F p) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => ReciprocityTheory.ChartRestriction.G.I2.polyDeriv Q u (fun w => F (z, w)) 0) 0 =
      ∑ m ∈ P.support, ∑ m' ∈ Q.support, P.coeff m * Q.coeff m' *
        lineDerivList ℂ ((lst m).map (fun s => (u s, 0)) ++ (lst m').map (fun s => (0, u s)))
          F 0 := by
  have h1 (z : W) : ReciprocityTheory.ChartRestriction.G.I2.polyDeriv Q u (fun w => F (z, w)) 0 = ∑ m' ∈ Q.support, Q.coeff m' •
      lineDerivList ℂ ((lst m').map (fun s => (0, u s))) F (LinearMap.inl ℂ W W z) := by
    have ha : AnalyticAt ℂ (fun w => F (z, w)) 0 := (hF _).comp₂ analyticAt_const analyticAt_id
    rw [polyDeriv_eq_sum_list _ _ ha]
    refine Finset.sum_congr rfl fun m' _ => ?_
    have h2 := congrFun (lineDerivList_comp_linearMap (LinearMap.inr ℂ W W) ((lst m').map u)
      (fun p => F (p + (z, 0)))) 0
    rw [lineDerivList_comp_add_const] at h2
    simp only [LinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero, List.map_map] at h2
    rw [h2]
    rfl
  have h3 (m' : σ →₀ ℕ) : AnalyticAt ℂ (fun z => Q.coeff m' •
      lineDerivList ℂ ((lst m').map (fun s => (0, u s))) F (LinearMap.inl ℂ W W z)) 0 :=
    analyticAt_const.fun_smul
      ((analyticAt_lineDerivList (hF _) _).comp ((ContinuousLinearMap.inl ℂ W W).analyticAt 0))
  simp only [h1]
  rw [polyDeriv_eq_sum_list _ _ (Finset.analyticAt_fun_sum _ fun m' _ => h3 m')]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [lineDerivList_sum _ fun m' _ => h3 m', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [lineDerivList_const_smul, lineDerivList_comp_linearMap, lineDerivList_append, List.map_map,
    mul_assoc]
  simp only [map_zero]
  rfl

theorem lineDerivList_conj {V : Type} [AddCommGroup V] [Module ℂ V] [StarAddMonoid V]
    [StarModule ℂ V] (l : List V) (hl : ∀ v ∈ l, star v = v) (F : V → ℂ) :
    lineDerivList ℂ l (fun z => conj (F (star z))) =
      fun z => conj (lineDerivList ℂ l F (star z)) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    rw [lineDerivList_cons, ih fun w hw => hl w (List.mem_cons_of_mem _ hw), lineDerivList_cons]
    simp only [lineDeriv, star_add, star_smul, hl v List.mem_cons_self]
    have h := congrFun (deriv_conj_conj (f := fun t : ℂ => lineDerivList ℂ l F (star z + t • v))) 0
    simpa [Function.comp_def] using h

theorem polyDeriv_barP_symm [StarAddMonoid W] [StarModule ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W)
    (hu : ∀ s, star (u s) = u s) {F G : W → W → ℂ}
    (hF : ∀ p, AnalyticAt ℂ (fun p : W × W => F p.1 p.2) p)
    (hG : ∀ p, AnalyticAt ℂ (fun p : W × W => G p.1 p.2) p)
    (h : ∀ z w, G z w = conj (F (star w) (star z))) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (barP P) u (G z) 0) 0 =
      conj (ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (barP P) u (F z) 0) 0) := by
  have hs : (barP P).support = P.support :=
    MvPolynomial.support_map_of_injective _ (starRingEnd ℂ).injective
  have hc (m : σ →₀ ℕ) : (barP P).coeff m = conj (P.coeff m) := MvPolynomial.coeff_map _ _ _
  have e1 := polyDeriv_polyDeriv P (barP P) u hF
  have e2 := polyDeriv_polyDeriv P (barP P) u hG
  dsimp only at e1 e2
  rw [e1, e2, hs, Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc, Complex.conj_conj]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  have h1 : (fun p : W × W => G p.1 p.2) =
      fun p => conj ((fun q : W × W => F q.2 q.1) (star p)) := funext fun p => h p.1 p.2
  have h2 (l : List (W × W)) := congrFun (lineDerivList_comp_linearMap
    (LinearEquiv.prodComm ℂ W W).toLinearMap l (fun p : W × W => F p.1 p.2)) 0
  simp only [LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
    Prod.swap_zero] at h2
  rw [h1, lineDerivList_conj _ (by
    simp only [List.mem_append, List.mem_map]
    rintro v (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) <;> simp [Prod.ext_iff, hu]) fun q : W × W => F q.2 q.1]
  simp only [star_zero]
  rw [h2, List.map_append, List.map_map, List.map_map,
    lineDerivList_perm (hF 0) List.perm_append_comm, mul_comm (P.coeff m')]
  rfl

theorem lineDerivList_exp (ℓ : W →L[ℂ] ℂ) (C : ℂ) (l : List W) :
    lineDerivList ℂ l (fun w => C * Complex.exp (ℓ w)) =
      fun w => (l.map ℓ).prod * (C * Complex.exp (ℓ w)) := by
  induction l with
  | nil => simp [lineDerivList]
  | cons v l ih =>
    funext w
    rw [lineDerivList_cons, ih]
    have h := (((ℓ.hasFDerivAt (x := w)).cexp.const_mul C).const_mul
      (l.map ℓ).prod).hasLineDerivAt v
    simp only [h.lineDeriv, List.map_cons, List.prod_cons, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring

theorem polyDeriv_exp (Q : MvPolynomial σ ℂ) (u : σ → W) (ℓ : W →L[ℂ] ℂ) (C : ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv Q u (fun w => C * Complex.exp (ℓ w)) 0 =
      C * MvPolynomial.eval (fun s => ℓ (u s)) Q := by
  have ha : AnalyticAt ℂ (fun w => C * Complex.exp (ℓ w)) 0 :=
    analyticAt_const.mul (ℓ.analyticAt 0).cexp
  rw [polyDeriv_eq_sum_list _ _ ha, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : ((List.map u (lst m)).map ℓ).prod = ∏ i ∈ m.support, ℓ (u i) ^ m i := by
    rw [List.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList,
      Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index (by simp)
        (by simp [pow_add])]
    rfl
  rw [lineDerivList_exp, h]
  simp only [map_zero, Complex.exp_zero]
  ring

theorem coeff_aeval_smul_X [Fintype σ] (t : σ → ℂ) (Q : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m
      (MvPolynomial.aeval (fun s => t s • (MvPowerSeries.X s : MvPowerSeries σ ℂ)) Q) =
      (∏ s, t s ^ m s) * Q.coeff m := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial n c =>
    have h : n.prod (fun s k => (t s • (MvPowerSeries.X s : MvPowerSeries σ ℂ)) ^ k) =
        (∏ s, t s ^ n s) • MvPowerSeries.monomial n 1 := by
      rw [← MvPolynomial.coe_monomial, MvPolynomial.monomial_eq,
        ← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
      simp only [map_one, one_mul, smul_pow, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod, map_pow]
      rw [Finsupp.prod_fintype _ _ (by simp), Finset.prod_smul]
      simp
    rw [MvPolynomial.aeval_monomial, h, ← Algebra.smul_def, map_smul, map_smul,
      MvPowerSeries.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases e : m = n
    · subst e; simp [mul_comm]
    · simp [e, Ne.symm e]
  | add P Q hP hQ => simp only [map_add (f := _), hP, hQ, MvPolynomial.coeff_add, mul_add]

theorem polyDeriv_barP_exp [Fintype σ] [DecidableEq σ] (P : MvPolynomial σ ℂ) (u : σ → W)
    (π : σ → W →L[ℂ] ℂ) (hπ : ∀ s s', π s (u s') = if s = s' then 1 else 0) (t : σ → ℝ) (C : ℝ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (barP P) u
      (fun w => C * Complex.exp (∑ s, t s * π s z * π s w)) 0) 0 =
      ((C * ∑ m ∈ P.support, (∏ s, (m s).factorial : ℕ) * (∏ s, t s ^ m s) *
        Complex.normSq (P.coeff m) : ℝ) : ℂ) := by
  have h1 (z : W) : ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (barP P) u
      (fun w => C * Complex.exp (∑ s, t s * π s z * π s w)) 0 =
      C * MvPolynomial.eval (fun s => ((t s : ℂ) • π s) z) (barP P) := by
    have h := polyDeriv_exp (barP P) u (∑ s, (t s * π s z) • π s) C
    simpa [hπ] using h
  have h2 (s : σ) : taylorDir u ((t s : ℂ) • π s : W →L[ℂ] ℂ) = (t s : ℂ) • MvPowerSeries.X s := by
    rw [taylorDir_clm]
    simp [hπ]
  have ha (s : σ) : AnalyticAt ℂ ((t s : ℂ) • π s : W →L[ℂ] ℂ) 0 := ContinuousLinearMap.analyticAt _ _
  have h3 : taylorDir u (fun z => C * MvPolynomial.eval (fun s => ((t s : ℂ) • π s) z) (barP P)) =
      (C : ℂ) • MvPolynomial.aeval (fun s => (t s : ℂ) • (MvPowerSeries.X s : MvPowerSeries σ ℂ))
        (barP P) := by
    simp only [← h2]
    rw [← taylorDir_eval u ha, ← taylorDir_smul]
    · rfl
    · exact AnalyticAt.aeval_mvPolynomial ha _
  simp only [h1]
  rw [dirPolyDeriv_eq_sum_coeff_taylorDir, h3]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, coeff_aeval_smul_X, barP, MvPolynomial.coeff_map, ← Complex.mul_conj, smul_eq_mul]
  ring

theorem apolar_norm_pos [Fintype σ] {P : MvPolynomial σ ℂ} (hP : P ≠ 0) {t : σ → ℝ}
    (ht : ∀ s, 0 < t s) :
    0 < ∑ m ∈ P.support, ((∏ s, (m s).factorial : ℕ) : ℝ) * (∏ s, t s ^ m s) *
        Complex.normSq (P.coeff m) := by
  refine Finset.sum_pos (fun m hm => ?_) (MvPolynomial.support_nonempty.2 hP)
  refine mul_pos (mul_pos ?_ (Finset.prod_pos fun s _ => pow_pos (ht s) _))
    (Complex.normSq_pos.2 (MvPolynomial.mem_support_iff.1 hm))
  exact_mod_cast Finset.prod_pos fun s _ => Nat.factorial_pos _

end GlobalTheory.SW.KernSym
end

