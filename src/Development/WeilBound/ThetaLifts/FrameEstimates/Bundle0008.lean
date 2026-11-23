module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LintegralLeOfCover
section
noncomputable section

namespace PositivityTheory.ThKEst.Sieg

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def shf (r : ℕ) (c : ℝ) : Fin r → ℝ := fun i => ((r : ℝ) - i.val) * |Real.log c|

theorem exp_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ} (ht : t ∈ Cone r) :
    (fun i => Real.exp ((t + shf r c) i)) ∈ GlobalTheory.SiegelSet.cone r c := by
  have h1 := le_abs_self (Real.log c)
  refine ⟨fun i => Real.exp_pos _, fun i j e => ?_, fun i e => ?_⟩
  · rw [← Real.exp_log hc, ← Real.exp_add, Real.exp_log hc]
    refine Real.exp_le_exp.2 ?_
    have h2 : t j ≤ t i := ht.1 (by rw [Fin.le_def]; omega)
    simp only [Pi.add_apply, shf, e]
    push_cast
    nlinarith
  · refine (Real.log_le_iff_le_exp hc).1 ?_
    have h2 : (r : ℝ) = i.val + 1 := by exact_mod_cast e.symm
    have h3 := ht.2 i
    simp only [Pi.add_apply, shf, h2]
    nlinarith

theorem log_mem_Cone {r : ℕ} {c : ℝ} (hc : 0 < c) {u : Fin r → ℝ} (hu : u ∈ GlobalTheory.SiegelSet.cone r c) :
    ((fun i => Real.log (u i)) + shf r c) ∈ Cone r := by
  have h1 := neg_abs_le (Real.log c)
  obtain _ | r := r
  · exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have ha : Antitone ((fun i => Real.log (u i)) + shf (r + 1) c) := by
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    have h2 := Real.log_le_log (mul_pos hc (hu.1 _)) (hu.2.1 i.castSucc i.succ (by simp))
    rw [Real.log_mul hc.ne' (hu.1 _).ne'] at h2
    simp only [Pi.add_apply, shf, Fin.val_succ, Fin.val_castSucc]
    push_cast
    nlinarith
  refine ⟨ha, fun i => le_trans ?_ (ha (Fin.le_last i))⟩
  have h2 := Real.log_le_log hc (hu.2.2 (Fin.last r) (by simp))
  simp only [Pi.add_apply, shf, Fin.val_last]
  push_cast
  nlinarith

theorem isClosed_Cone (r : ℕ) : IsClosed (Cone r) := by
  have : Cone r = (⋂ i, ⋂ j, ⋂ (_ : i ≤ j), {t : Fin r → ℝ | t j ≤ t i}) ∩ ⋂ i, {t | 0 ≤ t i} := by
    ext t; simp [Cone, Antitone]
  rw [this]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le (continuous_apply j) (continuous_apply i)).inter
    (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))

theorem modulus_exp (F : Type) [Field F] [NumberField F] (n : ℕ) {r : ℕ} (v : Fin r → ℝ) :
    GlobalTheory.SiegelSet.modulus F n (fun i => Real.exp (v i)) = Real.exp (2 * Module.finrank ℚ F * rho2 n v) := by
  rw [GlobalTheory.SiegelSet.modulus, rho2, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_intCast, ← Real.exp_mul]
  congr 1
  push_cast
  ring

theorem rho_sub_alt (n : ℕ) {r : ℕ} (s t : Fin r → ℝ) : rho2 n (s - t) = rho2 n s - rho2 n t := by
  simp [rho2, mul_sub, Finset.sum_sub_distrib]

theorem cone_integral_le (F : Type) [Field F] [NumberField F] (n r : ℕ) {c : ℝ} (hc : 0 < c)
    (φ : (Fin r → ℝ) → ℝ≥0∞) :
    ∫⁻ u in GlobalTheory.SiegelSet.cone r c, φ ((fun i => Real.log (u i)) + shf r c) *
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n u * ∏ i, u i)⁻¹) ≤
      ENNReal.ofReal (Real.exp (2 * Module.finrank ℚ F * rho2 n (shf r c))) *
        ∫⁻ t in Cone r, φ t * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * rho2 n t))) := by
  let Φ : (Fin r → ℝ) → Fin r → ℝ := fun t i => Real.exp ((t - shf r c) i)
  let Φ' : (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] Fin r → ℝ := fun t =>
    LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.diagonal (Φ t)))
  have hd : ∀ t ∈ Cone r, HasFDerivWithinAt Φ (Φ' t) (Cone r) t := fun t _ => by
    refine HasFDerivAt.hasFDerivWithinAt (hasFDerivAt_pi'.2 fun i => ?_)
    have := ((hasFDerivAt_apply (𝕜 := ℝ) i t).sub_const (shf r c i)).exp
    refine this.congr_fderiv ?_
    ext v
    simp [Φ', Φ, Matrix.mulVec_diagonal]
  have hi : Set.InjOn Φ (Cone r) := fun s _ t _ e => funext fun i => by
    have := Real.exp_injective (congrFun e i)
    simpa using this
  have hs : GlobalTheory.SiegelSet.cone r c ⊆ Φ '' Cone r := fun u hu =>
    ⟨_, log_mem_Cone hc hu, funext fun i => by simp [Φ, Real.exp_log (hu.1 i)]⟩
  refine (lintegral_mono_set hs).trans ?_
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (isClosed_Cone r).measurableSet hd hi,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_of_eq (lintegral_congr fun t => ?_)
  have e1 : (fun i => Real.log (Φ t i)) + shf r c = t := funext fun i => by simp [Φ]
  have e2 : (Φ' t).det = ∏ i, Φ t i := by
    simp [Φ', ContinuousLinearMap.det, LinearMap.det_toLin']
  have e3 : 0 < ∏ i, Φ t i := Finset.prod_pos fun i _ => Real.exp_pos _
  rw [e1, e2, abs_of_pos e3, mul_left_comm, mul_left_comm (ENNReal.ofReal _), ← ENNReal.ofReal_mul e3.le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, modulus_exp, rho_sub_alt, ← Real.exp_add]
  congr 2
  rw [mul_inv, mul_left_comm, mul_inv_cancel₀ e3.ne', mul_one, ← Real.exp_neg]
  congr 1
  ring

theorem lintegral_le_of_cover {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] {D S : Set G} (hD : IsFundamentalDomain Γ D μ) (hS : MeasurableSet S)
    (hc : ∀ g, ∃ γ ∈ Γ, γ * g ∈ S) {f : G → ℝ≥0∞} (hf : Measurable f) (hi : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫⁻ g in D, f g ∂μ ≤ ∫⁻ g in S, f g ∂μ := by
  have : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul γ.1⟩
  have : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ γ.1 s⟩
  rw [← lintegral_indicator hS, hD.lintegral_eq_tsum'', ← lintegral_tsum
    (f := fun (γ : Γ) x => S.indicator f (γ • x)) fun γ =>
    ((hf.indicator hS).comp (measurable_const_smul γ)).aemeasurable]
  refine lintegral_mono fun g => ?_
  obtain ⟨γ, hγ, h⟩ := hc g
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ, hγ⟩ : Γ))
  exact ((Set.indicator_of_mem h f).trans (hi γ hγ g)).symm

theorem le_exp_of_add {G : Type} [Group G] {r : ℕ} (h : G → ℝ≥0) (hm : ∀ x y, h (x * y) ≤ h x * h y)
    (a : (Fin r → ℝ) → G) (ha : ∀ s t, a (s + t) = a s * a t) (hc : Continuous fun t => h (a t)) :
    ∃ (C : ℝ) (k : ℕ), ∀ t : Fin r → ℝ, (∀ i, 0 ≤ t i) → (h (a t) : ℝ) ≤ C * Real.exp (k * ∑ i, t i) := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin r → ℝ) 1).bddAbove_image
    (NNReal.continuous_coe.comp hc).continuousOn
  have hB' : ∀ t : Fin r → ℝ, ‖t‖ ≤ 1 → (h (a t) : ℝ) ≤ B := fun t ht => hB ⟨t, by simpa using ht, rfl⟩
  obtain ⟨k, hk⟩ := exists_nat_ge B
  have hk' : B ≤ Real.exp k := hk.trans (by linarith [Real.add_one_le_exp (k : ℝ)])
  have hp : ∀ (m : ℕ) (t : Fin r → ℝ), ‖t‖ ≤ 1 → (h (a (((m : ℝ) + 1) • t)) : ℝ) ≤ Real.exp k ^ (m + 1) := by
    intro m t ht
    induction m with
    | zero => simpa using (hB' t ht).trans hk'
    | succ m ih =>
      rw [Nat.cast_succ, add_smul, one_smul, ha, pow_succ]
      refine le_trans (NNReal.coe_le_coe.2 (hm _ _)) ?_
      rw [NNReal.coe_mul]
      exact mul_le_mul ih ((hB' t ht).trans hk') (by positivity) (by positivity)
  refine ⟨Real.exp k, k, fun t ht => ?_⟩
  have h0 : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i _ => ht i
  have h1 : ‖t‖ ≤ ∑ i, t i := (pi_norm_le_iff_of_nonneg h0).2 fun i => by
    rw [Real.norm_of_nonneg (ht i)]; exact Finset.single_le_sum (fun i _ => ht i) (Finset.mem_univ i)
  have h2 := Nat.floor_le h0
  have h3 := Nat.lt_floor_add_one (∑ i, t i)
  set m := ⌊∑ i, t i⌋₊
  have h4 : (0 : ℝ) < m + 1 := by positivity
  have h5 := hp m (((m : ℝ) + 1)⁻¹ • t) (by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg h4.le, inv_mul_le_iff₀ h4]; linarith)
  rw [smul_inv_smul₀ h4.ne'] at h5
  refine h5.trans ?_
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  push_cast
  nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

end PositivityTheory.ThKEst.Sieg

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.SqAllC
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

theorem sq_alg_inj : Function.Injective (algebraMap F (AF F)) := NumberField.AdeleRing.algebraMap_injective (𝓞 F) F

theorem sq_inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := AF F) (B := E) sq_alg_inj

theorem exists_ratEquiv (hp : IsPair B M χX χW om r s r' s') :
    ∃ e : Matrix (Fin n) (Fin d) E ≃ (Fin n × Fin d → F) × (Fin n × Fin d → F), ∀ x,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) ((e x).1 i), fun i => algebraMap F (AF F) ((e x).2 i)) := by
  choose y z hyz using hp.good.rat
  have hadd : ∀ a b : Matrix (Fin n) (Fin d) E, incM F (a + b) = incM F a + incM F b := fun a b =>
    Matrix.ext fun i j => map_add (inclR (F := F) (AF F)) _ _
  have hsm : ∀ (c : F) (a : Matrix (Fin n) (Fin d) E), incM F (c • a) = algebraMap F (AF F) c • incM F a := fun c a =>
    Matrix.ext fun i j => by
      change (1 : AF F) ⊗ₜ[F] (c • a i j) = algebraMap F (AF F) c • ((1 : AF F) ⊗ₜ[F] a i j)
      rw [TensorProduct.tmul_smul, algebraMap_smul]
  let l : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    { toFun := fun x => (y x, z x)
      map_add' := fun a b => by
        have h := hyz (a + b)
        rw [hadd, map_add (f := _), hyz a, hyz b] at h
        refine Prod.ext (funext fun i => sq_alg_inj ?_) (funext fun i => sq_alg_inj ?_)
        · exact (congrFun (congrArg Prod.fst h) i).symm.trans (map_add _ _ _).symm
        · exact (congrFun (congrArg Prod.snd h) i).symm.trans (map_add _ _ _).symm
      map_smul' := fun c a => by
        have h := hyz (c • a)
        rw [hsm, map_smul, hyz a] at h
        refine Prod.ext (funext fun i => sq_alg_inj ?_) (funext fun i => sq_alg_inj ?_)
        · exact (congrFun (congrArg Prod.fst h) i).symm.trans (map_mul _ _ _).symm
        · exact (congrFun (congrArg Prod.snd h) i).symm.trans (map_mul _ _ _).symm }
  have hinj : Function.Injective l := fun a b hab => by
    have h1 : y a = y b := congrArg Prod.fst hab
    have h2 : z a = z b := congrArg Prod.snd hab
    have h3 : incM F a = incM F b := M.co.e.injective (by rw [hyz a, hyz b, h1, h2])
    exact Matrix.ext fun i j => sq_inclR_inj (congrFun (congrFun h3 i) j)
  have h2 : Module.finrank F E = 2 := hp.base.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hdim : Module.finrank F (Matrix (Fin n) (Fin d) E) =
      Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) := by
    rw [Module.finrank_matrix, h2]
    simp
    ring
  exact ⟨Equiv.ofBijective l ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩, hyz⟩

theorem theta_mul_le (hS : CoefSum) (hE : CoefEq) (hp : IsPair B M χX χW om r s r' s') (μ : Measure (Fin n × Fin d → AF F))
    (hμ : μ.IsAddHaarMeasure) : ∃ c : ℝ, 0 < c ∧ ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ g h,
      ‖theta om Φ₁ g h‖ₑ * ‖theta om Φ₂ g h‖ₑ ≤ ENNReal.ofReal c * ∑' x : Matrix (Fin n) (Fin d) E,
        ‖coef F B.ψ μ Φ₁ Φ₂ (M.co.e (mat g⁻¹ * incM F x * (mat h⁻¹)ᵀ))‖ₑ := by
  obtain ⟨c, hc, h1⟩ := hS F _ B.ψ hp.base.std μ hμ
  obtain ⟨e, he⟩ := exists_ratEquiv hp
  refine ⟨c, hc, fun Φ₁ h₁ Φ₂ h₂ g h => ?_⟩
  have hs := (IsUWeilPair.isUSplitting hp.weil).pres (g, h)
  refine (h1 _ (hs _ h₁) _ (hs _ h₂)).trans (le_of_eq ?_)
  rw [← e.tsum_eq]
  congr 1
  refine tsum_congr fun x => ?_
  rw [← he x, hE F E σ B n d X W M χX χW om r s r' s' hp μ hμ Φ₁ h₁ Φ₂ h₂ g h]

theorem sq_maj_nonneg (τ : ∀ w : InfinitePlace F, EmbOver E w) (C : Set (Ten F E n d)) (N : ℕ) (z : Ten F E n d) :
    0 ≤ maj τ C N z := by
  unfold maj sz
  split_ifs
  · positivity
  · exact le_rfl

theorem sq_le_of_coef {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) {t : ℝ≥0∞} {S : Set (Matrix (Fin n) (Fin d) E)}
    {u : Matrix (Fin n) (Fin d) E → ℂ} {C : Set (Ten F E n d)} {N : ℕ} {g : UA σ X.J} {h : UA σ W.J}
    (h1 : t * t ≤ ENNReal.ofReal c * ∑' x, ‖u x‖ₑ) (h0 : ∀ x ∉ S, u x = 0)
    (h2 : ∀ x, ‖u x‖ ≤ a * a * maj B.emb C N (mat g⁻¹ * incM F x * (mat h⁻¹)ᵀ)) :
    t ^ 2 ≤ ENNReal.ofReal (√c * a) ^ 2 * latSum B.emb C N S g h := by
  rw [sq]
  refine h1.trans ?_
  have e : ∑' x, ‖u x‖ₑ = ∑' x : S, ‖u x.1‖ₑ := by
    refine (tsum_subtype_eq_of_support_subset (f := fun x => ‖u x‖ₑ) fun x hx => ?_).symm
    by_contra hn
    exact hx (by simp [h0 x hn])
  rw [e, ← ENNReal.ofReal_pow (by positivity), mul_pow, Real.sq_sqrt hc.le, ENNReal.ofReal_mul hc.le, mul_assoc, latSum]
  refine mul_le_mul_right ?_ _
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity), sq]
  exact ENNReal.ofReal_le_ofReal (h2 x.1)

end

theorem sqAll_of' (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) : SqAll := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨c, hc, h1⟩ := theta_mul_le hS hE hp μ hμ
  obtain ⟨p, C, hpc, hC, h2⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ N
  refine ⟨NNReal.mk √c (Real.sqrt_nonneg c) • p, C, (continuous_const.mul hpc : Continuous fun f => √c * p f), hC,
    fun f g h => ?_⟩
  have hm : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  exact sq_le_of_coef hc (apply_nonneg p f) (h1 _ hm _ hm g h) (fun x hx => absurd (Set.mem_univ x) hx) fun x => h2 f f _

end PositivityTheory.ThKEst

end
end

