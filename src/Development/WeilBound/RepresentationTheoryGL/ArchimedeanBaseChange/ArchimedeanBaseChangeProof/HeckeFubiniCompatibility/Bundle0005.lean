module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.TrMulComm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfConv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.PChart
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PTestVeryCuspMulConst

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ContinuousCoshSqrt
section
noncomputable section

open MeasureTheory Filter Topology
open PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG

theorem norm_cosh_le_exp (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp ‖z‖ := by
  show ‖(Complex.exp z + Complex.exp (-z)) / 2‖ ≤ _
  have h1 : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (le_trans (le_abs_self _) (Complex.abs_re_le_norm z))
  have h2 : ‖Complex.exp (-z)‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by
      have := Complex.abs_re_le_norm z
      simp only [Complex.neg_re]
      linarith [neg_abs_le z.re])
  rw [norm_div]
  have h2' : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2']
  have := norm_add_le (Complex.exp z) (Complex.exp (-z))
  linarith

theorem sqrt_sq' (c : ℂ) : (c ^ (1 / 2 : ℂ)) ^ 2 = c := by
  have h := Complex.cpow_nat_inv_pow c (n := 2) (by norm_num)
  rw [one_div]
  push_cast at h
  exact h

theorem norm_sqrt_le (c : ℂ) : ‖c ^ (1 / 2 : ℂ)‖ ≤ 1 + ‖c‖ := by
  have h : ‖c ^ (1 / 2 : ℂ)‖ ^ 2 = ‖c‖ := by rw [← norm_pow, sqrt_sq']
  nlinarith [sq_nonneg (‖c ^ (1 / 2 : ℂ)‖ - 1), norm_nonneg (c ^ (1 / 2 : ℂ))]

theorem continuous_cosh_sqrt (t : ℂ) : Continuous fun c : ℂ => Complex.cosh (t * c ^ (1 / 2 : ℂ)) := by
  rw [Metric.continuous_iff]
  intro c₀ ε hε
  have hc : Continuous fun w : ℂ => Complex.cosh (t * w) :=
    Complex.continuous_cosh.comp (continuous_const.mul continuous_id)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.1 hc (c₀ ^ (1 / 2 : ℂ)) ε hε
  refine ⟨δ ^ 2, by positivity, fun c hcc => ?_⟩
  have hprod : (c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)) * (c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)) = c - c₀ := by
    have h1 := sqrt_sq' c
    have h2 := sqrt_sq' c₀
    linear_combination h1 - h2
  have hlt : ‖c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ * ‖c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)‖ < δ * δ := by
    rw [← norm_mul, hprod, ← dist_eq_norm, ← sq]
    exact hcc
  by_cases h : ‖c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ < δ
  · exact hδε _ (by rwa [dist_eq_norm])
  · have h' : ‖-c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ < δ := by
      push Not at h
      have he : ‖-c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ = ‖c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)‖ := by
        rw [← norm_neg]
        ring_nf
      rw [he]
      by_contra h2
      push Not at h2
      have := mul_le_mul h h2 hδ.le (norm_nonneg _)
      linarith
    have := hδε (-c ^ (1 / 2 : ℂ)) (by rwa [dist_eq_norm])
    simpa only [mul_neg, Complex.cosh_neg] using this

theorem continuous_coshT {g : ℝ → ℝ} {T : ℝ} (hg : IsBump g T) : Continuous (coshT g) := by
  rw [continuous_iff_continuousAt]
  intro c₀
  have hgc : Continuous g := hg.1.continuous
  have hF : ∀ c : ℂ, Continuous fun t : ℝ => (g t : ℂ) * Complex.cosh (t * c ^ (1 / 2 : ℂ)) := fun c =>
    (Complex.continuous_ofReal.comp hgc).mul
      (Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const))
  have hbc : Continuous fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖)) :=
    (Complex.continuous_ofReal.comp hgc).norm.mul
      (Real.continuous_exp.comp (continuous_abs.mul continuous_const))
  have hbs : HasCompactSupport fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht => ?_
    have hT : T < |t| := by
      rw [Set.mem_Icc, not_and_or] at ht
      rcases ht with ht | ht
      · push Not at ht
        have := neg_abs_le t
        linarith
      · push Not at ht
        exact lt_of_lt_of_le ht (le_abs_self t)
    simp [hg.2.2 t hT]
  unfold coshT
  refine continuousAt_of_dominated (bound := fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖)))
    (Eventually.of_forall fun c => (hF c).aestronglyMeasurable) ?_ (hbc.integrable_of_hasCompactSupport hbs)
    (ae_of_all _ fun t => (continuous_const.mul (continuous_cosh_sqrt (t : ℂ))).continuousAt)
  filter_upwards [Metric.ball_mem_nhds c₀ one_pos] with c hc
  refine ae_of_all _ fun t => ?_
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_cosh_le_exp _).trans (Real.exp_le_exp.2 ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
  have h1 := norm_sqrt_le c
  have h2 : ‖c‖ ≤ ‖c₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' c c₀
    rw [Metric.mem_ball, dist_eq_norm] at hc
    linarith
  linarith

theorem valCont : ValCont := by
  intro n _ μ M k val T χ χ₀ hk hχ
  obtain ⟨m, c, w, g, ks, hg, -, hval⟩ := hk
  have hv : val = fun χ => ∑ i, c i * zVal (w i) χ * coshT (g i) (cas χ) := funext hval
  rw [hv]
  have hz : ∀ l : List (Bool × ℕ), Tendsto (fun j => zVal l (χ j)) atTop (𝓝 (zVal l χ₀)) := by
    intro l
    induction l with
    | nil => simp only [zVal, List.map_nil, List.prod_nil]; exact tendsto_const_nhds
    | cons p l ih =>
      simp only [zVal, List.map_cons, List.prod_cons] at ih ⊢
      exact (hχ p.1 p.2).mul ih
  have hcas : Tendsto (fun j => cas (χ j)) atTop (𝓝 (cas χ₀)) := by
    unfold cas
    exact ((hχ true 2).add (hχ false 2)).const_mul 2
  refine tendsto_finsetSum _ fun i _ => ?_
  exact (tendsto_const_nhds.mul (hz (w i))).mul (((continuous_coshT (hg i).1).tendsto _).comp hcas)

end PositivityTheory.Rg.BcB.CG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ContinuousEmbInf
section
noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace PositivityTheory.Rg.BcB.CG

namespace PSumH

variable {n : ℕ}

theorem isClosed_nilrad (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    IsClosed (nilrad W₁ W₂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hW : ∀ W : Submodule ℂ (Fin n → ℂ), IsClosed (W : Set (Fin n → ℂ)) := fun W =>
    W.closed_of_finiteDimensional
  have hc : ∀ y : Fin n → ℂ, Continuous fun X : Matrix (Fin n) (Fin n) ℂ => X *ᵥ y := fun y =>
    continuous_id.matrix_mulVec continuous_const
  have e : (nilrad W₁ W₂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
      (⋂ y, (fun X : Matrix (Fin n) (Fin n) ℂ => X *ᵥ y) ⁻¹' W₂) ∩
        ((⋂ y ∈ W₂, (fun X : Matrix (Fin n) (Fin n) ℂ => X *ᵥ y) ⁻¹' W₁) ∩
          ⋂ y ∈ W₁, (fun X : Matrix (Fin n) (Fin n) ℂ => X *ᵥ y) ⁻¹' {0}) := by
    ext X
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, Set.mem_singleton_iff]
    exact Iff.rfl
  rw [e]
  refine (isClosed_iInter fun y => (hW W₂).preimage (hc y)).inter
    ((isClosed_biInter fun y _ => (hW W₁).preimage (hc y)).inter
      (isClosed_biInter fun y _ => isClosed_singleton.preimage (hc y)))

theorem integrable_nil {f : GL (Fin n) ℂ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (u : nilrad W₁ W₂ → GL (Fin n) ℂ) (hu : ∀ X, (u X).val = 1 + X.1)
    (d : GL (Fin n) ℂ) [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂))
    [ν.IsAddHaarMeasure] : Integrable (fun X => f (u X * d)) ν := by
  have hu' : u = fun X => ((PVC.eH W₁ W₂ X : PVC.nilSub W₁ W₂) : GL (Fin n) ℂ) :=
    funext fun X => Units.ext (by rw [hu X]; rfl)
  have hcu : Continuous u := by
    rw [hu']; exact continuous_subtype_val.comp (PVC.eH W₁ W₂).continuous
  have hF : Continuous fun X => f (u X * d) := hf.comp (hcu.mul continuous_const)
  refine hF.integrable_of_hasCompactSupport ?_
  have hL : IsCompact ((fun k : GL (Fin n) ℂ => (k * d⁻¹).val - 1) '' tsupport f) :=
    hfc.isCompact.image ((Units.continuous_val.comp (continuous_id.mul continuous_const)).sub continuous_const)
  have hK : IsCompact (Subtype.val ⁻¹' ((fun k : GL (Fin n) ℂ => (k * d⁻¹).val - 1) '' tsupport f) :
      Set (nilrad W₁ W₂)) :=
    (isClosed_nilrad W₁ W₂).isClosedEmbedding_subtypeVal.isCompact_preimage hL
  refine HasCompactSupport.intro hK fun X hX => ?_
  by_contra h
  apply hX
  refine ⟨u X * d, subset_tsupport _ h, ?_⟩
  show ((u X * d) * d⁻¹).val - 1 = X.1
  rw [mul_inv_cancel_right, hu X, add_sub_cancel_left]

theorem veryCusp_add {f g : GL (Fin n) ℂ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hf' : VeryCusp f) (hg' : VeryCusp g) : VeryCusp fun x => f x + g x := by
  refine ⟨fun k d hk => by dsimp only; rw [hf'.1 k d hk, hg'.1 k d hk], fun d W₁ W₂ hne hle hp1 hp2 u hu _ _ ν _ => ?_⟩
  rw [integral_add (integrable_nil hf hfc u hu d ν) (integrable_nil hg hgc u hu d ν),
    hf'.2 d W₁ W₂ hne hle hp1 hp2 u hu ν, hg'.2 d W₁ W₂ hne hle hp1 hp2 u hu ν, add_zero]

theorem veryCusp_smul {f : GL (Fin n) ℂ → ℂ} (c : ℂ) (hf : VeryCusp f) : VeryCusp fun x => c * f x := by
  refine ⟨fun k d hk => by dsimp only; rw [hf.1 k d hk], fun d W₁ W₂ hne hle hp1 hp2 u hu _ _ ν _ => ?_⟩
  rw [integral_const_mul, hf.2 d W₁ W₂ hne hle hp1 hp2 u hu ν, mul_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gInf_embInf (v : InfinitePlace E) (d : GL (Fin n) ℂ) : gInf v (embInf n v d) = d := by
  classical
  have e : embInf n v d = infP n (Pi.mulSingle v d) := rfl
  rw [e, gInf_infP, Pi.mulSingle_eq_same]

theorem continuous_embInf (v : InfinitePlace E) : Continuous (embInf (E := E) n v) := by
  classical
  have e : (embInf (E := E) n v : GL (Fin n) ℂ → GA E n) = fun d => infP n (Pi.mulSingle v d) := rfl
  rw [e]
  exact (continuous_infP n).comp (continuous_mulSingle (A := fun _ : InfinitePlace E => GL (Fin n) ℂ) v)

theorem slice {φ : GA E n → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ) (v : InfinitePlace E) (g : GA E n)
    (hg : GeneralLinearGroup.map (cV v) g = 1) :
    Continuous (fun d => φ (embInf n v d * g)) ∧ HasCompactSupport (fun d => φ (embInf n v d * g)) := by
  refine ⟨hφ.comp ((continuous_embInf v).mul continuous_const), ?_⟩
  refine HasCompactSupport.intro (hc.isCompact.image (continuous_gInf n v)) fun d hd => ?_
  by_contra h
  apply hd
  refine ⟨embInf n v d * g, subset_tsupport _ h, ?_⟩
  have hg' : gInf v g = 1 := hg
  rw [map_mul, gInf_embInf, hg', mul_one]

omit [IsCMField E] in
theorem isTest_add [_root_.NumberField.IsTotallyComplex E] {φ ψ : GA E n → ℂ} (hφ : IsTest φ) (hψ : IsTest ψ) : IsTest fun x => φ x + ψ x := by
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  obtain ⟨U', hU', hUψ⟩ := hψ.level
  refine ⟨hφ.cont.add hψ.cont, hφ.supp.add hψ.supp, U ⊓ U', by rw [Subgroup.coe_inf]; exact hU.inter hU',
    fun u hu g => ?_⟩
  rw [Subgroup.mem_inf] at hu
  exact ⟨by rw [(hUφ u hu.1 g).1, (hUψ u hu.2 g).1], by rw [(hUφ u hu.1 g).2, (hUψ u hu.2 g).2]⟩

omit [IsCMField E] in
theorem isTest_smul [_root_.NumberField.IsTotallyComplex E] {φ : GA E n → ℂ} (c : ℂ) (hφ : IsTest φ) : IsTest fun x => c * φ x := by
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  refine ⟨continuous_const.mul hφ.cont, hφ.supp.mono fun x hx => right_ne_zero_of_mul hx, U, hU,
    fun u hu g => ?_⟩
  exact ⟨by rw [(hUφ u hu g).1], by rw [(hUφ u hu g).2]⟩

theorem regSupp_add {φ ψ : GA E n → ℂ} (hφ : RegSupp φ) (hψ : RegSupp ψ) : RegSupp fun x => φ x + ψ x := by
  intro d x h
  dsimp only at h
  by_cases h0 : φ (twConj (thetaA E n) x (ratGL E n d)) = 0
  · exact hψ d x (by rwa [h0, zero_add] at h)
  · exact hφ d x h0

theorem regSupp_smul {φ : GA E n → ℂ} (c : ℂ) (hφ : RegSupp φ) : RegSupp fun x => c * φ x :=
  fun d x h => hφ d x (right_ne_zero_of_mul h)

theorem vCAt_add {φ ψ : GA E n → ℂ} (hφ : IsTest φ) (hψ : IsTest ψ) (v : InfinitePlace E) (h₁ : VCAt v φ)
    (h₂ : VCAt v ψ) : VCAt v fun x => φ x + ψ x := fun g hg =>
  veryCusp_add (slice hφ.cont hφ.supp v g hg).1 (slice hφ.cont hφ.supp v g hg).2
    (slice hψ.cont hψ.supp v g hg).1 (slice hψ.cont hψ.supp v g hg).2 (h₁ g hg) (h₂ g hg)

theorem vCAt_smul {φ : GA E n → ℂ} (c : ℂ) (v : InfinitePlace E) (h : VCAt v φ) : VCAt v fun x => c * φ x :=
  fun g hg => veryCusp_smul c (h g hg)

end PSumH

open PSumH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem isTest2J_zero (r : ℝ) : IsTest2J (0 : GA E a × GA E b → ℂ) r :=
  ⟨⟨continuous_const, HasCompactSupport.zero, fun _ h => absurd rfl h,
    fun _ => ⟨isTest_zero, regSupp_zero, fun _ _ _ => veryCusp_zero⟩,
    fun _ => ⟨isTest_zero, regSupp_zero, fun _ _ _ => veryCusp_zero⟩⟩,
    ⊤, ⊤, isOpen_univ, isOpen_univ, fun _ _ _ _ _ => ⟨rfl, rfl⟩⟩

theorem isTest2J_smul {φ : GA E a × GA E b → ℂ} {r : ℝ} (c : ℂ) (h : IsTest2J φ r) : IsTest2J (c • φ) r := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU⟩ := h.level
  refine ⟨⟨h.cont.const_smul c, h.supp.mono fun x hx => right_ne_zero_of_mul hx,
    fun g hg => h.size g (right_ne_zero_of_mul hg), fun g₂ => ?_, fun g₁ => ?_⟩,
    U₁, U₂, hU₁, hU₂, fun u₁ h₁ u₂ h₂ g => ?_⟩
  · obtain ⟨t, s, w⟩ := h.test₁ g₂
    exact ⟨isTest_smul c t, regSupp_smul c s, fun v => vCAt_smul c v (w v)⟩
  · obtain ⟨t, s, w⟩ := h.test₂ g₁
    exact ⟨isTest_smul c t, regSupp_smul c s, fun v => vCAt_smul c v (w v)⟩
  · exact ⟨by simp only [Pi.smul_apply, (hU u₁ h₁ u₂ h₂ g).1], by simp only [Pi.smul_apply, (hU u₁ h₁ u₂ h₂ g).2]⟩

theorem isTest2J_add {φ ψ : GA E a × GA E b → ℂ} {r : ℝ} (h : IsTest2J φ r) (h' : IsTest2J ψ r) :
    IsTest2J (φ + ψ) r := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU⟩ := h.level
  obtain ⟨U₁', U₂', hU₁', hU₂', hU'⟩ := h'.level
  refine ⟨⟨h.cont.add h'.cont, h.supp.add h'.supp, fun g hg => ?_, fun g₂ => ?_, fun g₁ => ?_⟩,
    U₁ ⊓ U₁', U₂ ⊓ U₂', by rw [Subgroup.coe_inf]; exact hU₁.inter hU₁', by rw [Subgroup.coe_inf]; exact hU₂.inter hU₂',
    fun u₁ h₁ u₂ h₂ g => ?_⟩
  · by_cases h0 : φ g = 0
    · exact h'.size g (by simpa [h0] using hg)
    · exact h.size g h0
  · obtain ⟨t, s, w⟩ := h.test₁ g₂
    obtain ⟨t', s', w'⟩ := h'.test₁ g₂
    exact ⟨isTest_add t t', regSupp_add s s', fun v => vCAt_add t t' v (w v) (w' v)⟩
  · obtain ⟨t, s, w⟩ := h.test₂ g₁
    obtain ⟨t', s', w'⟩ := h'.test₂ g₁
    exact ⟨isTest_add t t', regSupp_add s s', fun v => vCAt_add t t' v (w v) (w' v)⟩
  · rw [Subgroup.mem_inf] at h₁ h₂
    exact ⟨by simp only [Pi.add_apply, (hU u₁ h₁.1 u₂ h₂.1 g).1, (hU' u₁ h₁.2 u₂ h₂.2 g).1],
      by simp only [Pi.add_apply, (hU u₁ h₁.1 u₂ h₂.1 g).2, (hU' u₁ h₁.2 u₂ h₂.2 g).2]⟩

theorem isTest2J_mono {φ : GA E a × GA E b → ℂ} {r r' : ℝ} (h : IsTest2J φ r) (hr : r ≤ r') : IsTest2J φ r' :=
  ⟨⟨h.cont, h.supp, fun g hg => ⟨(h.size g hg).1.trans hr, (h.size g hg).2.trans hr⟩, h.test₁, h.test₂⟩, h.level⟩

theorem isTest2J_sum {ι : Type*} (s : Finset ι) {φ : ι → GA E a × GA E b → ℂ} {r : ℝ}
    (h : ∀ i ∈ s, IsTest2J (φ i) r) : IsTest2J (∑ i ∈ s, φ i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isTest2J_zero r
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isTest2J_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end PositivityTheory.Rg.BcB.CG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfEx
section
noncomputable section

open Polynomial Finset NumberField GlobalTheory.CuspRep
open PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.CG.InfiniteConvergence

namespace PositivityTheory.Rg.BcB.CG

namespace HeckeFubiniEvaluationDefect

theorem eval_sS (t : ℕ → ℂ) (m N : ℕ) : (sS t m N).eval (m : ℂ) = (-1) ^ N * t N := by
  rw [sS, sum_range_succ, eval_add, eval_finsetSum, sum_eq_zero]
  · simp
  · intro k hk
    have := mem_range.mp hk
    simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
    rw [zero_pow (by omega), mul_zero]

theorem eq_of_defect (m : ℕ) (t t' : ℕ → ℂ) (Q : ℂ[X]) (hQ : Q.natDegree = m + 1)
    (h : ∀ N, (defect t m N Q).natDegree ≤ m) (h' : ∀ N, (defect t' m N Q).natDegree ≤ m) (k : ℕ) : t k = t' k := by
  have hQ0 : Q ≠ 0 := by intro e; rw [e, natDegree_zero] at hQ; omega
  have hS : sS t m k = sS t' m k := by
    have e : defect t m k Q - defect t' m k Q = Q * (sS t' m k - sS t m k) := by
      simp only [defect_eq]; ring
    by_contra hne
    have hD : sS t' m k - sS t m k ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h1 : (Q * (sS t' m k - sS t m k)).natDegree ≤ m := by
      rw [← e]; exact (natDegree_sub_le _ _).trans (max_le (h k) (h' k))
    rw [natDegree_mul hQ0 hD, hQ] at h1
    omega
  have e := congrArg (fun p => p.eval (m : ℂ)) hS
  simp only [eval_sS] at e
  have hu : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hu e

theorem exists_enum (s : Multiset ℂ) : ∀ n, Multiset.card s = n → ∃ r : Fin n → ℂ, Multiset.map r univ.val = s := by
  induction s using Multiset.induction_on with
  | empty =>
    intro n hn
    simp only [Multiset.card_zero] at hn
    subst hn
    exact ⟨Fin.elim0, by simp⟩
  | cons a s ih =>
    intro n hn
    rw [Multiset.card_cons] at hn
    subst hn
    obtain ⟨r, hr⟩ := ih _ rfl
    refine ⟨Fin.cons a r, ?_⟩
    conv_rhs => rw [← hr]
    simp [Fin.univ_succ, Multiset.map_map, Function.comp_def]

theorem exists_gelf (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (M : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V)
    (hM : Formalism.REAL.GlRel M) (v : V) (hv : v ≠ 0) (t : ℕ → ℂ) (ht : ∀ k, Formalism.REAL.etr M k v = t k • v) :
    ∃ χ : Fin (m + 1) → ℂ, ∀ k, GlobalTheory.Dec.gelfVal χ k = t k := by
  obtain ⟨f₀, hf₀⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).mp hc)
  set f : Module.Dual ℂ V := (f₀ v)⁻¹ • f₀ with hfd
  have hf : f v = 1 := by
    rw [hfd, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]
  obtain ⟨c, hc1, hc⟩ := _root_.GlobalTheory.qdet_polyMap_monic (Module.End ℂ V) (m + 1) M
  set Q := GlobalTheory.CapelliNewton.polyOf (m + 1) c f v with hQd
  have hQ : ∀ u : ℂ, Q.eval u = f (Formalism.REAL.qdet M u v) := fun u => by
    rw [hQd, GlobalTheory.CapelliNewton.polyOf_eval, hc]
  have hQc : Q.coeff (m + 1) = 1 := by
    rw [hQd, GlobalTheory.CapelliNewton.polyOf_coeff, hc1]
    exact hf
  have hQn : Q.natDegree = m + 1 :=
    le_antisymm (GlobalTheory.CapelliNewton.polyOf_natDegree _ _ _ _)
      (le_natDegree_of_ne_zero (by rw [hQc]; exact one_ne_zero))
  have hQm : Q.Monic := by
    rw [Monic, leadingCoeff, hQn, hQc]
  have hcard : Multiset.card Q.roots = m + 1 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hQn]
  have hprod : (Q.roots.map fun a => X - Polynomial.C a).prod = Q :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm (by rw [hcard, hQn])
  obtain ⟨r, hr⟩ := exists_enum Q.roots (m + 1) hcard
  refine ⟨fun s => (m : ℂ) / 2 - r s, fun k => ?_⟩
  have hcq : (∏ s, (X + Polynomial.C ((m : ℂ) / 2 - r s - (m : ℂ) / 2))) = Q := by
    conv_rhs => rw [← hprod, ← hr]
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun s _ => ?_
    simp only [Function.comp_apply, map_sub]
    ring
  have h1 : ∀ N, (defect (GlobalTheory.Dec.gelfVal fun s => (m : ℂ) / 2 - r s) m N Q).natDegree ≤ m := by
    intro N
    have := natDegree_defect_gelf m (fun s => (m : ℂ) / 2 - r s) N
    rwa [hcq] at this
  have h2 : ∀ N, (defect t m N Q).natDegree ≤ m := fun N =>
    natDegree_defect_op V m M hM v t ht f Q hQ N
  exact eq_of_defect m _ t Q hQn h1 h2 k

theorem one_mem_GLs' {a : ℕ} : (1 : Matrix (Fin a) (Fin a) ℂ) ∈ PositivityTheory.RgBcC.GLs a := by
  simp [PositivityTheory.RgBcC.GLs]

end HeckeFubiniEvaluationDefect

open HeckeFubiniEvaluationDefect in
theorem infEx : InfEx := by
  intro E _ _ _ n S v t ⟨φ, hφS, hφ0⟩ h
  have hs : ∀ s k, Formalism.REAL.etr (eopW v s) k φ = t s k • φ := by
    intro s k
    apply Subtype.ext
    funext g
    have h1 := h φ hφS g s k 1 one_mem_GLs'
    rw [gel_along v g s k φ one_mem_GLs', along_one, along_one] at h1
    rw [Submodule.coe_smul, Pi.smul_apply]
    exact h1
  rcases n with _ | m
  · refine ⟨fun _ => Fin.elim0, fun s k => ?_⟩
    have ht0 : t s k = 0 := by
      have e : t s k • φ = 0 := by rw [← hs s k]; simp [Formalism.REAL.etr]
      exact (smul_eq_zero.mp e).resolve_right hφ0
    rw [ht0]
    simp [GlobalTheory.Dec.gelfVal]
  · have hgl : ∀ s, Formalism.REAL.GlRel (eopW (E := E) (a := m + 1) v s) := by
      intro s
      unfold eopW
      split <;> exact glRel_Eop _
    choose χ hχ using fun s => exists_gelf (Sm E (m + 1)) m (eopW v s) (hgl s) φ hφ0 (t s) (hs s)
    exact ⟨χ, fun s k => hχ s k⟩

end PositivityTheory.Rg.BcB.CG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PTestJ
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)

namespace PositivityTheory.Rg.BcB.CG

def Test2J : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) (R r : ℝ)
  (U : Subgroup (Hf E a b)), 0 ≤ R →
  (∀ v, Continuous (fa v) ∧ VeryCusp (fa v) ∧ ∀ y, fa v y ≠ 0 → lg y.val ≤ R) →
  (∀ v, Continuous (fb v) ∧ VeryCusp (fb v) ∧ ∀ y, fb v y ≠ 0 → lg y.val ≤ R) →
  HasCompactSupport ψ → IsOpen (U : Set (Hf E a b)) → (∀ u ∈ U, ∀ h, ψ (u * h) = ψ h ∧ ψ (h * u) = ψ h) →
  (∀ h, ψ h ≠ 0 → logSize (finGL E a h.1) ≤ r ∧ logSize (finGL E b h.2) ≤ r) →
  (∀ d x h₂, ψ (gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E a) x (ratGL E a d)), h₂) ≠ 0 → IsRegD d) →
  (∀ d x h₁, ψ (h₁, gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E b) x (ratGL E b d))) ≠ 0 → IsRegD d) →
  PositivityTheory.Rg.BcB.D4.IsTest2J (fun g : H E a b => (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g))
    (2 * Fintype.card (InfinitePlace E) * R + r)

theorem test2J : Test2J := fun E _ _ _ a b fa fb ψ R r U hR ha hb hψs hUo hψU hsz hr₁ hr₂ =>
  have h := pTest_main fa fb ψ R r U hR ha hb hψs hUo hψU hsz hr₁ hr₂
  { toIsTest2 := h.1, level := h.2 }

end PositivityTheory.Rg.BcB.CG
end
end

