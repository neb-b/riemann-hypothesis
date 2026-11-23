module

public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0006
public import Development.WeilBound.ThetaLifts.FrameEstimates.LinDerA
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0007
public import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LatTor
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sum_pos_lam {n d q y : ℕ} {lam : Fin n → (Fin q → ℝ) →ₗ[ℝ] ℝ} {ix iy : Fin q ↪ Fin n} (h1 : ∀ i j, ix i ≠ iy j)
    (h2 : ∀ i t, lam (ix i) t = t i ∧ lam (iy i) t = -t i) (h3 : ∀ k, (∀ i, ix i ≠ k ∧ iy i ≠ k) → lam k = 0)
    {lam' : Fin d → (Fin y → ℝ) →ₗ[ℝ] ℝ} {jx jy : Fin y ↪ Fin d} (h1' : ∀ i j, jx i ≠ jy j)
    (h2' : ∀ i t, lam' (jx i) t = t i ∧ lam' (jy i) t = -t i) (h3' : ∀ k, (∀ i, jx i ≠ k ∧ jy i ≠ k) → lam' k = 0)
    {s : Fin q → ℝ} {t : Fin y → ℝ} (hs : s ∈ Cone q) (ht : t ∈ Cone y) :
    ∑ k, ∑ l, max 0 (lam k s + lam' l t) = posWt n d s t := by
  let G : ℝ → ℝ := fun u => ∑ l, max 0 (u + lam' l t)
  have hG : ∀ u, G u = ∑ j, max 0 (u + t j) + ∑ j, max 0 (u + -t j) + ((d : ℝ) - 2 * y) * max 0 (u + 0) := fun u =>
    sum_lam h1' h2' h3' (fun v => max 0 (u + v)) t
  have h0 : G 0 = ∑ j, t j := by
    rw [hG]
    have a : ∀ j, max 0 (0 + t j) = t j := fun j => by rw [zero_add, max_eq_right (ht.2 j)]
    have b : ∀ j, max 0 (0 + -t j) = 0 := fun j => by rw [zero_add, max_eq_left (by linarith [ht.2 j])]
    simp only [a, b]
    simp
  have hs' : ∀ i, G (s i) + G (-s i) = ∑ j, 2 * max (s i) (t j) + ((d : ℝ) - 2 * y) * s i := by
    intro i
    have a : ∀ j, 2 * max (s i) (t j) =
        max 0 (s i + t j) + max 0 (s i + -t j) + (max 0 (-s i + t j) + max 0 (-s i + -t j)) := by
      intro j
      have := hs.2 i
      have := ht.2 j
      simp only [max_def]
      split_ifs <;> linarith
    rw [hG, hG, add_zero, add_zero, max_eq_right (hs.2 i), max_eq_left (by linarith [hs.2 i] : -s i ≤ 0)]
    simp only [a, Finset.sum_add_distrib]
    ring
  have := sum_lam h1 h2 h3 G s
  rw [← Finset.sum_add_distrib, h0] at this
  simp only [hs', Finset.sum_add_distrib, ← Finset.mul_sum] at this
  refine this.trans ?_
  simp only [posWt, ← Finset.mul_sum]

theorem tsum_fin_prod {α : Type} (q : ℕ) (φ : Fin q → α → ℝ≥0∞) :
    ∑' x : Fin q → α, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← (Fin.consEquiv fun _ : Fin (q + 1) => α).tsum_eq, ENNReal.tsum_prod', Fin.prod_univ_succ, ← ih,
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [Fin.prod_univ_succ]
    rfl

theorem tsum_fun_prod {ι α : Type} [Fintype ι] (φ : ι → α → ℝ≥0∞) :
    ∑' x : ι → α, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  let e := (Fintype.equivFin ι).symm
  rw [← e.prod_comp, ← tsum_fin_prod, ← (e.arrowCongr (Equiv.refl α)).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [← e.prod_comp]
  simp

def oneMaj (τ : ∀ w : InfinitePlace F, EmbOver E w) (m N : ℕ) (ν : ℝ) : E → ℝ≥0∞ :=
  Set.indicator {x | IsIntegral ℤ ((m : E) * x)} fun x =>
    ENNReal.ofReal (((1 + Real.exp (-ν) * ∑ w, ‖(τ w).1 x‖) ^ N)⁻¹)

theorem tsum_oneMaj (hO : OneVar) (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ≥0, ∀ ν, ∑' x, oneMaj τ m (Module.finrank ℚ E + 1) ν x ≤
      K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * max 0 ν)) := by
  classical
  obtain ⟨K, hK⟩ := hO (mixedEmbedding.mixedSpace E) (mixedEmbedding.integerLattice E) (Module.finrank ℚ E + 1)
    (by rw [mixedEmbedding.finrank]; omega)
  rw [mixedEmbedding.finrank] at hK
  set N := Module.finrank ℚ E + 1
  refine ⟨(m : ℝ≥0) ^ N * K, fun ν => ?_⟩
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let i : {x : E | IsIntegral ℤ ((m : E) * x)} → mixedEmbedding.integerLattice E := fun x =>
    ⟨mixedEmbedding E (m * x.1), ⟨⟨_, x.2⟩, rfl⟩⟩
  have hi : Function.Injective i := fun x y hxy => by
    have := (mixedEmbedding E).injective (congrArg Subtype.val hxy)
    exact Subtype.ext (mul_left_cancel₀ (by exact_mod_cast hm.ne') this)
  have hn : ∀ x : E, ‖mixedEmbedding E x‖ ≤ ∑ w, ‖(τ w).1 x‖ := by
    intro x
    rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun v _ => ?_
    obtain ⟨w, hw⟩ := norm_emb h τ v.embedding
    rw [mixedEmbedding.normAtPlace_apply, ← InfinitePlace.norm_embedding_eq, hw]
    exact Finset.single_le_sum (f := fun w => ‖(τ w).1 x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  rw [oneMaj, ← tsum_subtype]
  calc _ ≤ ∑' x : {x : E | IsIntegral ℤ ((m : E) * x)}, ((m : ℝ≥0) ^ N : ℝ≥0) *
          ENNReal.ofReal (((1 + Real.exp (-ν) * ‖(i x : mixedEmbedding.mixedSpace E)‖) ^ N)⁻¹) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hS : 0 ≤ ∑ w, ‖(τ w).1 x.1‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have h1 : ‖(i x : mixedEmbedding.mixedSpace E)‖ ≤ m * ∑ w, ‖(τ w).1 x.1‖ := by
          refine (hn _).trans (le_of_eq ?_)
          simp [Finset.mul_sum]
        have h2 : 1 + Real.exp (-ν) * ‖(i x : mixedEmbedding.mixedSpace E)‖ ≤
            m * (1 + Real.exp (-ν) * ∑ w, ‖(τ w).1 x.1‖) := by
          have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-ν)).le
          linarith
        have h3 := pow_le_pow_left₀ (by positivity) h2 N
        rw [mul_pow] at h3
        push_cast
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
        exact h3.trans_eq (mul_comm _ _)
    _ ≤ ((m : ℝ≥0) ^ N : ℝ≥0) * (K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * max 0 ν))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective hi _).trans (hK ν)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]

theorem latTor_of : FrameBasis → OneVar → LatTor := by
  intro hB hO F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr'
  classical
  obtain ⟨b, lam, ix, iy, h1, h2, h3, -, hb⟩ := hB F E σ hσ n J hJ fr hfr
  obtain ⟨b', lam', jx, jy, h1', h2', h3', -, hb'⟩ := hB F E σ hσ d J' hJ' fr' hfr'
  set N₀ := Module.finrank ℚ E + 1 with hN₀
  set c := Fintype.card (Fin n × Fin d) with hc
  refine ⟨N₀ * c, fun C hC => ?_⟩
  obtain ⟨m, K, hm, hK, h⟩ := diag_coords τ hfr hfr' hb hb' hC
  obtain ⟨K₁, hK₁⟩ := tsum_oneMaj hO hσ τ hm
  refine ⟨K.toNNReal ^ (N₀ * c) * K₁ ^ c, fun s hs t ht => ?_⟩
  let i : ↥(Set.univ : Set (Matrix (Fin n) (Fin d) E)) → (Fin n × Fin d → E) := fun x p =>
    ((b⁻¹).1 * x.1 * (b'⁻¹).1ᵀ) p.1 p.2
  have hi : Function.Injective i := fun x y hxy => by
    have e : (b⁻¹).1 * x.1 * (b'⁻¹).1ᵀ = (b⁻¹).1 * y.1 * (b'⁻¹).1ᵀ := by
      ext k l
      exact congrFun hxy (k, l)
    have e' : ∀ z : Matrix (Fin n) (Fin d) E, b.1 * ((b⁻¹).1 * z * (b'⁻¹).1ᵀ) * b'.1ᵀ = z := by
      intro z
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]
    exact Subtype.ext (by rw [← e' x.1, e, e'])
  let g : (Fin n × Fin d → E) → ℝ≥0∞ := fun ξ => ∏ p, oneMaj τ m N₀ (lam p.1 s + lam' p.2 t) (ξ p)
  calc _ ≤ ∑' x, (K.toNNReal ^ (N₀ * c) : ℝ≥0) * g (i x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        obtain ⟨ha, hb⟩ := h s t x.1
        unfold maj
        split_ifs with hx
        swap
        · simp
        have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        set z := sz τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        let A : Fin n × Fin d → ℝ := fun p => Real.exp (-(lam p.1 s + lam' p.2 t)) * ∑ w, ‖(τ w).1 (i x p)‖
        have hA0 : ∀ p, 0 ≤ A p := fun p => by positivity
        have hA : ∀ p, 1 + A p ≤ K * (1 + z) := fun p => by
          have : ∑ p, A p ≤ K * z := by
            refine le_trans (le_of_eq ?_) hb
            rw [Fintype.sum_prod_type, Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace F)))]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace F)))]
            exact Finset.sum_congr rfl fun l _ => Finset.mul_sum _ _ _
          have h4 := Finset.single_le_sum (f := A) (fun p _ => hA0 p) (Finset.mem_univ p)
          linarith
        have hg : g (i x) = ENNReal.ofReal (∏ p, (1 + A p) ^ N₀)⁻¹ := by
          rw [← Finset.prod_inv_distrib, ENNReal.ofReal_prod_of_nonneg fun p _ => by have := hA0 p; positivity]
          exact Finset.prod_congr rfl fun p _ =>
            Set.indicator_of_mem (s := {x | IsIntegral ℤ ((m : E) * x)}) (a := i x p) (ha hx p.1 p.2) _
        have h5 : ∏ p, (1 + A p) ^ N₀ ≤ (K * (1 + z)) ^ (N₀ * c) := by
          rw [pow_mul, hc, ← Finset.card_univ, ← Finset.prod_const]
          exact Finset.prod_le_prod₀ (fun p _ => by have := hA0 p; positivity)
            fun p _ => pow_le_pow_left₀ (by have := hA0 p; positivity) (hA p) _
        have h6 : 0 < ∏ p, (1 + A p) ^ N₀ := Finset.prod_pos fun p _ => by have := hA0 p; positivity
        rw [hg, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        rw [Real.coe_toNNReal _ (by linarith), ← div_eq_mul_inv, le_div_iff₀ h6, inv_mul_le_iff₀ (by positivity),
          ← mul_pow]
        exact h5.trans_eq (by rw [mul_comm K])
    _ ≤ (K.toNNReal ^ (N₀ * c) : ℝ≥0) * ∏ p : Fin n × Fin d, (K₁ * ENNReal.ofReal
          (Real.exp (Module.finrank ℚ E * max 0 (lam p.1 s + lam' p.2 t)))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        refine (ENNReal.tsum_comp_le_tsum_of_injective hi g).trans ?_
        rw [tsum_fun_prod]
        exact Finset.prod_le_prod' fun p _ => hK₁ _
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hc,
          ← ENNReal.ofReal_prod_of_nonneg fun p _ => (Real.exp_pos _).le, ← Real.exp_sum, ← Finset.mul_sum,
          Fintype.sum_prod_type, sum_pos_lam h1 h2 h3 h1' h2' h3' hs ht]
        push_cast
        rw [mul_assoc]

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LinDer
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LinDerPf

section Cx

variable {ι : Type} [Fintype ι] {d : ℕ}

def adj (J : ι → Matrix (Fin d) (Fin d) ℂ) : (ι → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] (ι → Matrix (Fin d) (Fin d) ℂ) where
  toFun x w := ((J w)⁻¹ * (x w)ᵀ * J w).map star
  map_add' x y := by
    funext w
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, Pi.add_apply, Matrix.map_apply, Matrix.add_apply,
      star_add]
  map_smul' r x := by
    funext w
    ext i j
    simp only [Matrix.transpose_smul, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_apply,
      Matrix.smul_apply, star_smul, RingHom.id_apply, star_trivial]

omit [Fintype ι] in
theorem adj_iff {J : ι → Matrix (Fin d) (Fin d) ℂ} (hJ : ∀ w, IsUnit (J w).det) (Y : ι → Matrix (Fin d) (Fin d) ℂ) :
    adj J Y = -Y ↔ ∀ w, (Y w)ᵀ * J w + J w * (Y w).map star = 0 := by
  rw [funext_iff]
  refine forall_congr' fun w => ?_
  change ((J w)⁻¹ * (Y w)ᵀ * J w).map star = -Y w ↔ _
  have e : ((J w)⁻¹ * (Y w)ᵀ * J w).map star = -Y w ↔ (J w)⁻¹ * (Y w)ᵀ * J w = -(Y w).map star := by
    simp only [← Matrix.ext_iff, Matrix.map_apply, Matrix.neg_apply]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [star_eq_iff_star_eq, star_neg, eq_comm]
  rw [e, add_eq_zero_iff_eq_neg, ← Matrix.mul_neg]
  constructor
  · intro h
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hJ w)]
  · intro h
    rw [Matrix.mul_assoc, h, Matrix.nonsing_inv_mul_cancel_left _ _ (hJ w)]

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
theorem mainM {J : ι → Matrix (Fin d) (Fin d) ℂ} (hJ : ∀ w, IsUnit (J w).det) :
    ∃ (m : ℕ) (Y : Fin m → ι → Matrix (Fin d) (Fin d) ℂ) (c : Fin m → (ι → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] ℝ),
      (∀ i w, (Y i w)ᵀ * J w + J w * (Y i w).map star = 0) ∧ ∀ Z Z' : ι → Matrix (Fin d) (Fin d) ℂ,
      (∀ w, (Z' w)ᵀ * J w + J w * (Z' w).map star = 0) →
      (∀ w (t : ℝ), NormedSpace.exp ((t : ℂ) • Z w) = NormedSpace.exp ((t : ℂ) • Z' w)) →
      ∃ s : Fin m → ℝ → ℝ, (∀ i, s i 0 = 0) ∧ (∀ i, HasDerivAt (s i) (c i Z) 0) ∧
        ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ w, NormedSpace.exp ((t : ℂ) • Z w) =
          (List.ofFn fun i => NormedSpace.exp ((s i t : ℂ) • Y i w)).prod := by
  let a : (ι → Matrix (Fin d) (Fin d) ℂ) →L[ℝ] (ι → Matrix (Fin d) (Fin d) ℂ) := LinearMap.toContinuousLinearMap (adj J)
  have ha : ∀ x y, a (x * y) = a y * a x := fun x y => by
    funext w
    change ((J w)⁻¹ * (x w * y w)ᵀ * J w).map (starRingEnd ℂ) =
      ((J w)⁻¹ * (y w)ᵀ * J w).map (starRingEnd ℂ) * ((J w)⁻¹ * (x w)ᵀ * J w).map (starRingEnd ℂ)
    rw [← Matrix.map_mul, Matrix.transpose_mul]
    congr 1
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hJ w)]
  have h1 : a 1 = 1 := by
    funext w
    change ((J w)⁻¹ * (1 : Matrix (Fin d) (Fin d) ℂ)ᵀ * J w).map (starRingEnd ℂ) = 1
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hJ w), Matrix.map_one _ (map_zero _) (map_one _)]
  have hx : ∀ (t : ℝ) (x : ι → Matrix (Fin d) (Fin d) ℂ) w,
      NormedSpace.exp (t • x) w = NormedSpace.exp ((t : ℂ) • x w) := fun t x w => by
    rw [Pi.coe_exp, Pi.smul_apply, Complex.coe_smul]
  obtain ⟨m, Y, c, hY, h⟩ := main (a := a) ha h1
  refine ⟨m, Y, c, fun i => (adj_iff hJ _).1 (hY i), fun Z Z' hZ e => ?_⟩
  obtain ⟨s, s0, sd, se⟩ := h Z fun t => by
    have e' : NormedSpace.exp (t • Z) = NormedSpace.exp (t • Z') := funext fun w => by rw [hx, hx, e]
    rw [e']
    refine gr_exp ha h1 ?_
    rw [map_smul, ← smul_neg]
    exact congrArg _ ((adj_iff hJ _).2 hZ)
  refine ⟨s, s0, sd, se.mono fun t ht w => ?_⟩
  rw [← hx, ht, Pi.list_prod_apply, List.map_ofFn]
  congr 2
  funext i
  exact hx _ _ _

end Cx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}

omit [NumberField E] in
theorem uat_prod {W : Spc F E d} (l : List (UA σ W.J)) (hl : ∀ g ∈ l, g ∈ UAt σ W (evI F)) :
    l.prod ∈ UAt σ W (evI F) := by
  induction l with
  | nil =>
    intro c _
    change c • ((1 : Matrix (Fin d) (Fin d) (AE F E)) - 1) = 0
    rw [sub_self, smul_zero]
  | cons x l ih =>
    intro c hc
    have h1 := hl x (by simp) c hc
    have h2 := ih (fun g hg => hl g (by simp [hg])) c hc
    rw [List.prod_cons]
    change c • (mat x * mat l.prod - 1) = 0
    have e : mat x * mat l.prod - 1 = mat x * (mat l.prod - 1) + (mat x - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one, sub_add_sub_cancel]
    rw [e, smul_add, ← Matrix.mul_smul, h1, h2, Matrix.mul_zero, add_zero]

omit [NumberField E] in
theorem mat_prod {J : Matrix (Fin d) (Fin d) E} (p : AE F E →+* ℂ) (l : List (UA σ J)) :
    (mat l.prod).map p = (l.map fun g => (mat g).map p).prod := by
  induction l with
  | nil => exact Matrix.map_one _ (map_zero _) (map_one _)
  | cons x l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih, ← Matrix.map_mul]
    rfl

theorem uat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {W : Spc F E d} {u v : UA σ W.J}
    (hu : u ∈ UAt σ W (evI F)) (hv : v ∈ UAt σ W (evI F))
    (e : ∀ w, (mat u).map (piInf (τ w)) = (mat v).map (piInf (τ w))) : u = v := by
  refine Subtype.ext (Units.ext ?_)
  change mat u = mat v
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_)
  · have e1 : c • (mat u - mat v) = 0 := by
      rw [← sub_sub_sub_cancel_right _ _ 1, smul_sub, hu c hc, hv c hc, sub_zero]
    exact congrFun (congrFun e1 i) j
  · rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (e w) i) j)

end LinDerPf

open LinDerPf in
theorem linDer_of (hG : LineGen) (hX : LineEx) : LinDer := by
  intro F E _ _ _ _ _ σ h τ d W hW
  have hJ : ∀ w, IsUnit (W.J.map (τ w).1).det := fun w => by
    have e : (W.J.map (τ w).1).det = (τ w).1 W.J.det := (RingHom.map_det (τ w).1 W.J).symm
    rw [e]
    exact ((map_ne_zero (τ w).1).2 hW.2).isUnit
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  have : IsTopologicalGroup (UA σ W.J) := inferInstance
  obtain ⟨m, Y, c, hY, hm⟩ := mainM hJ
  choose β hβ hβY _ using fun i => hX F E σ h τ d W hW (Y i) (hY i)
  refine ⟨m, β, c, hβ, fun f f' hf γ hγ Z hZ g => ?_⟩
  obtain ⟨Z', hZ', hZZ⟩ := hG F E σ h τ d W hW γ hγ
  obtain ⟨s, s0, sd, se⟩ := hm Z Z' hZ' fun w t => (hZ w t).symm.trans (hZZ w t)
  have h1 := chain f m β (fun i => (hβ i).1) f' (fun i => (hf i).1) (fun i => (hf i).2) (fun _ => g)
    continuousAt_const s (fun i => c i Z) sd s0 0 (hasDerivAt_const _ _)
  rw [zero_add] at h1
  refine h1.congr_of_eventuallyEq (se.mono fun t ht => ?_)
  have e : γ (Multiplicative.ofAdd t) = (List.ofFn fun i => β i (Multiplicative.ofAdd (s i t))).prod := by
    refine uat_ext h τ (hγ.2 _) (uat_prod _ fun x hx => ?_) fun w => ?_
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact (hβ i).2 _
    · rw [hZ w t, ht w, mat_prod, List.map_ofFn]
      congr 2
      funext i
      exact (hβY i w _).symm
  simp only [e]

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.OneMemLines
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

theorem exists_clm (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {𝓕} (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕)
    (hsb : φ ∈ SB _) (h : UA σ W.J) :
    ∃ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), L f = M.I om (pureA F f φ) h := by
  obtain ⟨h1, h2⟩ := dom_facts hB hp hD hφ hsb
  refine ⟨⟨⟨⟨fun f => M.I om (pureA F f φ) h, fun f f' => ?_⟩, fun c f => ?_⟩, h2 h⟩, fun _ => rfl⟩
  · have e : pureA F (f + f' : SInf F _) φ = pureA F f φ + pureA F f' φ := by
      funext x; simp [pureA, add_mul]
    unfold Model.I
    rw [e, ← integral_add ((h1 f).1 h) ((h1 f').1 h)]
    exact integral_congr_ae (Eventually.of_forall fun g => theta_add hp (pureA_mem f hsb) (pureA_mem f' hsb) g h)
  · have e : pureA F (c • f : SInf F _) φ = c • pureA F f φ := by
      funext x; simp [pureA, mul_assoc]
    change M.I om (pureA F (c • f : SInf F _) φ) h = c * M.I om (pureA F f φ) h
    unfold Model.I
    rw [e, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun g => theta_smul hp c (pureA_mem f hsb) g h)

theorem one_mem_UAt : (1 : UA σ X.J) ∈ UAt σ X (evI F) := fun u _ => by
  have : mat (1 : UA σ X.J) = 1 := rfl
  rw [this, sub_self, smul_zero]

theorem one_mem_Lines : (1 : Multiplicative ℝ →* UA σ X.J) ∈ Lines σ X := ⟨continuous_const, fun _ => one_mem_UAt⟩

end

theorem iDer_of (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) (hI : IInv) : IDer := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp 𝓕 hD φ hφ hsb f hf
  obtain ⟨-, i2, i3⟩ := hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem f hsb)
  refine ⟨fun γ hγ => ?_, fun γ hγ => ?_⟩
  · choose T hT using fun t : ℝ => hO F E σ B n d X W M χX χW om r s r' s' hp 1 one_mem_UAt _ (hγ.2 (Multiplicative.ofAdd t))
    obtain ⟨f₁, hf₁, ha, hd⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp 1 one_mem_Lines γ hγ T (fun t => (hT t).1) f hf
    refine ⟨f₁, hf₁, ha, fun h => ?_⟩
    obtain ⟨L, hLf⟩ := exists_clm hB hp hD hφ hsb h
    have := hd L
    rw [hLf] at this
    convert this using 2 with t
    rw [hLf, ← (hT t).1.1 f φ hsb, i3]
  · choose T hT using fun t : ℝ => hO F E σ B n d X W M χX χW om r s r' s' hp _ (hγ.2 (Multiplicative.ofAdd t)) 1 one_mem_UAt
    obtain ⟨f₁, hf₁, ha, hd⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp γ hγ 1 one_mem_Lines T (fun t => (hT t).1) f hf
    refine ⟨f₁, hf₁, ha, funext fun h => ?_⟩
    obtain ⟨L, hLf⟩ := exists_clm hB hp hD hφ hsb h
    have h1 := hd L
    have h2 : (fun t => L (T t f)) = fun _ => M.I om (pureA F f φ) h := funext fun t => by
      rw [hLf, ← (hT t).1.1 f φ hsb, i2]
    rw [h2] at h1
    rw [← hLf]
    exact h1.unique (hasDerivAt_const _ _)

end PositivityTheory.ThKEst

end
end

