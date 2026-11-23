module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ActEig
section
noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem hasDerivAt_cosh_smul' {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (a : ℂ) (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.cosh ((s : ℂ) * a) • v) ((a * Complex.sinh ((t : ℂ) * a)) • v) t := by
  have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * a) a t := by
    have := ((hasDerivAt_id (t : ℂ)).mul_const a).comp_ofReal
    rw [one_mul] at this
    exact this
  have h2 := ((Complex.hasDerivAt_cosh ((t : ℂ) * a)).comp t hl).smul_const v
  rw [mul_comm a]
  exact h2

private theorem hasDerivAt_sinh_smul' {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (a : ℂ) (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.sinh ((s : ℂ) * a) • v) ((a * Complex.cosh ((t : ℂ) * a)) • v) t := by
  have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * a) a t := by
    have := ((hasDerivAt_id (t : ℂ)).mul_const a).comp_ofReal
    rw [one_mul] at this
    exact this
  have h2 := ((Complex.hasDerivAt_sinh ((t : ℂ) * a)).comp t hl).smul_const v
  rw [mul_comm a]
  exact h2

private theorem iteratedDeriv_two_cosh_smul' {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (a : ℂ) (v : V) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => Complex.cosh ((s : ℂ) * a) • v) t
      = (a * a * Complex.cosh ((t : ℂ) * a)) • v := by
  have hd : deriv (fun s : ℝ => Complex.cosh ((s : ℂ) * a) • v)
      = fun s : ℝ => a • (Complex.sinh ((s : ℂ) * a) • v) := by
    funext s
    rw [(hasDerivAt_cosh_smul' a v s).deriv, mul_smul]
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
  have h : HasDerivAt (fun s : ℝ => a • (Complex.sinh ((s : ℂ) * a) • v))
      (a • ((a * Complex.cosh ((t : ℂ) * a)) • v)) t := (hasDerivAt_sinh_smul' a v t).const_smul a
  rw [h.deriv, smul_smul, mul_assoc]

private theorem half_mul_half' (c : ℂ) : c ^ (1 / 2 : ℂ) * c ^ (1 / 2 : ℂ) = c := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [Complex.zero_cpow (by norm_num)]
    ring
  · rw [← Complex.cpow_add _ _ hc]
    norm_num

private theorem contDiff_cosh_fst {n : ℕ} (a : ℂ) :
    ContDiff ℝ ∞ (fun p : ℝ × Mat n => Complex.cosh ((p.1 : ℂ) * a)) := by
  have h0 : ContDiff ℝ ∞ Complex.cosh := Complex.contDiff_cosh.restrict_scalars ℝ
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × Mat n => (p.1 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  exact h0.comp (h1.mul contDiff_const)

private theorem eigWave {n : ℕ} (E : KMod n) (χ : Inf n) (f : Mat n → E.V) (hf : f ∈ CE E) (he : IsEig χ f) :
    IsWave E (fun (t : ℝ) y => Complex.cosh ((t : ℂ) * cas χ ^ (1 / 2 : ℂ)) • f y) := by
  have ha2 := half_mul_half' (cas χ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => f p.2) (Set.univ ×ˢ GLs n) :=
      hf.1.comp contDiff_snd.contDiffOn (fun p hp => hp.2)
    exact (contDiff_cosh_fst _).contDiffOn.smul h2
  · intro t
    refine ⟨contDiffOn_const.smul hf.1, ?_⟩
    intro g hg k
    simp only [hf.2 g hg k, map_smul]
  · intro t g hg
    have h := ((UpperTheory.RealTr.zEig n E.V χ f hf.1 he (Complex.cosh ((t : ℂ) * cas χ ^ (1 / 2 : ℂ)))).1 g hg)
    beta_reduce
    rw [iteratedDeriv_two_cosh_smul', h, ha2, smul_smul]
  · intro g hg
    beta_reduce
    rw [(hasDerivAt_cosh_smul' _ (f g) 0).deriv]
    simp

private theorem val_mem_GLs' {n : ℕ} (y : G n) : y.val ∈ GLs n := by
  exact ((UpperTheory.RealTr.basic n).2.1 _).2 y.isUnit

private theorem integrable_ker {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (κ : Mat n → (E.V →L[ℂ] E.V)) (hc : ContinuousOn κ (GLs n))
    (hs : ∃ R, ∀ y ∈ GLs n, R < lg y → κ y = 0) (f : Mat n → E.V) (hf : ContinuousOn f (GLs n))
    (x : Mat n) (hx : x ∈ GLs n) : Integrable (fun y : G n => κ y.val (f (x * y.val))) μ := by
  obtain ⟨R, hR⟩ := hs
  have hcont : Continuous (fun y : G n => κ y.val (f (x * y.val))) := by
    refine Continuous.clm_apply (hc.comp_continuous Units.continuous_val fun y => val_mem_GLs' y) ?_
    refine hf.comp_continuous (continuous_const.mul Units.continuous_val) fun y => ?_
    show det (x * y.val) ≠ 0
    rw [det_mul]
    exact mul_ne_zero hx (val_mem_GLs' y)
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (UpperTheory.RealTr.lgCpt n R) ?_)
  intro y hy
  simp only [Set.mem_setOf_eq, not_le] at hy
  simp [hR _ (val_mem_GLs' y) hy]

theorem UpperTheory.RealTr.actEig :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ) (T : ℝ), IsMult μ E k val T →
      ∀ χ, ∀ f ∈ CE E, IsEig χ f → ∀ x ∈ GLs n, act μ E k f x = val χ • f x := by
  intro n _ _ μ _ E k val T hM χ f hf he x hx
  obtain ⟨m, c, w, g, ks, hks, hk, hval⟩ := hM
  have hf' := hf
  obtain ⟨hf1, hf2⟩ := hf'
  have hint : ∀ i, Integrable (fun y : G n => ks i y.val (f (x * y.val))) μ := fun i =>
    integrable_ker μ E (ks i) (hks i).2.1.continuousOn (hks i).2.2.1 f hf1.continuousOn x hx
  have hu := eigWave E χ f hf he
  have hact : ∀ i, act μ E (ks i) f x = (coshT (g i) (cas χ) * zVal (w i) χ) • f x := by
    intro i
    have key := (hks i).2.2.2.2 _ hu x hx
    have e1 : act μ E (ks i) f x =
        act μ E (ks i) (fun y => Complex.cosh (((0 : ℝ) : ℂ) * cas χ ^ (1 / 2 : ℂ)) • f y) x := by
      simp
    have e2 : (fun x' => ∫ t : ℝ, ((g i t : ℝ) : ℂ) • (Complex.cosh ((t : ℂ) * cas χ ^ (1 / 2 : ℂ)) • f x')) =
        fun x' => coshT (g i) (cas χ) • f x' := by
      funext x'
      simp only [smul_smul]
      rw [integral_smul_const]
      rfl
    rw [e1]
    refine key.trans ((congrArg (fun F => zOp (w i) F x) e2).trans ?_)
    exact (UpperTheory.RealTr.zEig n E.V χ f hf1 he _).2 (w i) x hx
  have hk' : ∀ y : G n, k y.val = ∑ i, c i • ks i y.val := fun y => hk _ (val_mem_GLs' y)
  have hsum : act μ E k f x = ∑ i, c i • act μ E (ks i) f x := by
    simp only [act, hk', ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    rw [integral_finsetSum]
    · simp only [integral_smul]
    · intro i _
      exact (hint i).smul (c i)
  rw [hsum, hval]
  simp only [hact, smul_smul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ChiInj
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private def chi {n : ℕ} (x : Wt n) : Multiplicative (Wt n) →* ℂ where
  toFun θ := Complex.exp (Complex.I * ∑ a, ((Multiplicative.toAdd θ a : ℝ) : ℂ) * (x a : ℂ))
  map_one' := by simp
  map_mul' s t := by
    simp [← Complex.exp_add, add_mul, mul_add, Finset.sum_add_distrib]

private theorem chi_inj {n : ℕ} : Function.Injective (chi (n := n)) := by
  intro x y hxy
  funext a
  by_contra hne
  have hd' : x a - y a ≠ 0 := sub_ne_zero.2 hne
  have e := congrArg (fun φ : Multiplicative (Wt n) →* ℂ =>
    φ (Multiplicative.ofAdd (Pi.single a (Real.pi / (x a - y a))))) hxy
  simp [chi, Pi.single_apply] at e
  rw [Complex.exp_eq_exp_iff_exists_int] at e
  obtain ⟨m, hm⟩ := e
  have hi := congrArg Complex.im hm
  simp at hi
  have hp : Real.pi / (x a - y a) * (x a - y a) = Real.pi := div_mul_cancel₀ _ hd'
  have h2 : Real.pi * 1 = Real.pi * (2 * m) := by linear_combination hi - hp
  have h3 := mul_left_cancel₀ Real.pi_ne_zero h2
  have h4 : (1 : ℤ) = 2 * m := by exact_mod_cast h3
  omega

private theorem evT_eq_sum_coeff_chi {n : ℕ} (θ : Wt n) (f : FR n) :
    evT θ f = ∑ x ∈ f.coeff.support, f.coeff x * chi x (Multiplicative.ofAdd θ) := by
  simp [evT, AddMonoidAlgebra.lift_apply, Finsupp.sum, chi]

private theorem ev_zero {n : ℕ} (f : FR n) (h : ∀ θ : Wt n, evT θ f = 0) : f = 0 := by
  have hli : LinearIndependent ℂ (fun x : Wt n => ((chi x : Multiplicative (Wt n) → ℂ))) :=
    (linearIndependent_monoidHom (Multiplicative (Wt n)) ℂ).comp chi chi_inj
  apply AddMonoidAlgebra.ext
  apply linearIndependent_iff.1 hli
  ext θ
  have hθ := h (Multiplicative.toAdd θ)
  rw [evT_eq_sum_coeff_chi] at hθ
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  simpa [Finset.sum_apply] using hθ

theorem UpperTheory.RealTr.evInj :
    ∀ (n : ℕ) (f : FR n), (∀ θ : Wt n, (Function.Injective fun a => Complex.exp (Complex.I * θ a) ^ 2) → evT θ f = 0) → f = 0 := by
  intro n f hf
  apply ev_zero f
  intro θ0
  let v : Wt n := fun a => ((a : ℕ) : ℝ)
  obtain ⟨bad, hbad, hmem⟩ : ∃ S : Set ℝ, S.Countable ∧ ∀ t : ℝ, t ∉ S →
      Function.Injective fun a => Complex.exp (Complex.I * (((θ0 + t • v) a : ℝ) : ℂ)) ^ 2 := by
    refine ⟨⋃ p : Fin n × Fin n, ⋃ m : ℤ,
      {((m : ℝ) * Real.pi - (θ0 p.1 - θ0 p.2)) / (v p.1 - v p.2)}, ?_, ?_⟩
    · exact Set.countable_iUnion fun p => Set.countable_iUnion fun m => Set.countable_singleton _
    · intro t ht a b hab
      by_contra hne
      apply ht
      simp only at hab
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int] at hab
      obtain ⟨m, hm⟩ := hab
      have hi := congrArg Complex.im hm
      simp [Pi.add_apply, Pi.smul_apply] at hi
      have hv : v a - v b ≠ 0 := sub_ne_zero.2 (fun e => hne (Fin.ext (by simpa [v] using e)))
      refine Set.mem_iUnion.2 ⟨(a, b), Set.mem_iUnion.2 ⟨m, Set.mem_singleton_iff.2 ?_⟩⟩
      rw [eq_div_iff hv]
      linarith
  have hφ : (fun t : ℝ => evT (θ0 + t • v) f) = fun t => ∑ x ∈ f.coeff.support,
      f.coeff x * Complex.exp (Complex.I * ∑ a, (((θ0 a + t * v a : ℝ)) : ℂ) * (x a : ℂ)) := by
    funext t
    simp [evT, AddMonoidAlgebra.lift_apply, Finsupp.sum]
  have hcont : Continuous fun t : ℝ => evT (θ0 + t • v) f := by
    rw [hφ]
    fun_prop
  have hzero := Continuous.ext_on (hbad.dense_compl ℝ) hcont continuous_const
    (fun t ht => hf (θ0 + t • v) (hmem t ht))
  simpa using congrFun hzero 0
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem rearr_gap (n : ℕ) (a b : Fin n) : rhoV n a - rhoV n b = ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
  simp only [rhoV]
  ring

private theorem sum_mul_perm_le_and_eq_one_of_antitone {n : ℕ} (x y : Fin n → ℝ) (hx : Antitone x) (hy : Antitone y) (w : Equiv.Perm (Fin n)) :
    ∑ a, x a * y (w a) ≤ ∑ a, x a * y a ∧
      (StrictAnti x → StrictAnti y → ∑ a, x a * y (w a) = ∑ a, x a * y a → w = 1) := by
  have hm : Monovary x y := hx.monovary hy
  refine ⟨hm.sum_mul_comp_perm_le_sum_mul, fun sx sy he => ?_⟩
  have h2 := hm.sum_mul_comp_perm_eq_sum_mul_iff.1 he
  have hmono : StrictMono w := by
    intro i j hij
    by_contra hc
    push_neg at hc
    rcases hc.lt_or_eq with hlt | heq
    · exact absurd (h2 (show y (w i) < y (w j) from sy hlt)) (not_le.2 (sx hij))
    · exact absurd (w.injective heq) (ne_of_gt hij)
  have := hmono.eq_id
  ext i
  simp [this]

private theorem rearr_lemma_2 {n : ℕ} (x : Fin n → ℝ) :
    Antitone (domC x) ∧ (∃ w : Equiv.Perm (Fin n), domC x = x ∘ w) ∧ (Antitone x → domC x = x) ∧
      (∀ w : Equiv.Perm (Fin n), domC (x ∘ w) = domC x) ∧ nsq (domC x) = nsq x := by
  refine ⟨?_, ⟨_, rfl⟩, fun hx => ?_, fun w => ?_, ?_⟩
  · intro a b hab
    have := Tuple.monotone_sort (fun a => -x a) hab
    simpa [domC] using this
  · have : Tuple.sort (fun a => -x a) = Equiv.refl (Fin n) :=
      Tuple.sort_eq_refl_iff_monotone.2 (fun a b hab => neg_le_neg (hx hab))
    simp [domC, this]
  · have h := Tuple.comp_perm_comp_sort_eq_comp_sort (f := fun a => -x a) (σ := w)
    funext a
    show (x ∘ w) ((Tuple.sort ((fun a => -x a) ∘ w)) a) = x ((Tuple.sort fun a => -x a) a)
    have := congrFun h a
    simp only [Function.comp_apply, neg_inj] at this
    exact this
  · unfold nsq domC
    exact Equiv.sum_comp (Tuple.sort fun a => -x a) (fun a => x a ^ 2)

private theorem strictAnti_rhoV_and_dom_rhoV (n : ℕ) : StrictAnti (rhoV n) ∧ Dom (rhoV n) := by
  constructor
  · intro a b hab
    have h1 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith [rearr_gap n a b]
  · unfold Dom
    intro a b hab
    refine ⟨(b : ℕ) - (a : ℕ), ?_⟩
    rw [rearr_gap, Nat.cast_sub (Fin.lt_def.mp hab).le]

private theorem antitone_and_dom_domC_sub_rhoV_of_dom (n : ℕ) (x : Wt n) (hx : Dom x) : Antitone x ∧ Dom (domC (x - rhoV n)) := by
  unfold Dom at hx
  have hint : ∀ a b, ∃ k : ℤ, (x - rhoV n) a - (x - rhoV n) b = k := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · obtain ⟨m, hm⟩ := hx a b h
      refine ⟨(m : ℤ) - ((b : ℕ) : ℤ) + ((a : ℕ) : ℤ), ?_⟩
      simp only [Pi.sub_apply]
      push_cast
      linarith [rearr_gap n a b]
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨m, hm⟩ := hx b a h
      refine ⟨-(m : ℤ) + ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ), ?_⟩
      simp only [Pi.sub_apply]
      push_cast
      linarith [rearr_gap n b a]
  refine ⟨fun a b hab => ?_, ?_⟩
  · rcases hab.lt_or_eq with h | h
    · obtain ⟨m, hm⟩ := hx a b h
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · rw [h]
  · unfold Dom
    intro a b hab
    obtain ⟨w, hw⟩ := (rearr_lemma_2 (x - rhoV n)).2.1
    have hanti := (rearr_lemma_2 (x - rhoV n)).1
    obtain ⟨k, hk⟩ := hint (w a) (w b)
    have hk0 : (0 : ℝ) ≤ k := by
      have := hanti hab.le
      rw [hw] at this
      simp only [Function.comp_apply] at this
      linarith
    have hk1 : (0 : ℤ) ≤ k := by exact_mod_cast hk0
    refine ⟨k.toNat, ?_⟩
    rw [hw]
    simp only [Function.comp_apply]
    rw [hk, ← Int.cast_natCast, Int.toNat_of_nonneg hk1]

private theorem nsq_le_and_eq_of_nsq_le_sum_mul {n : ℕ} (x y : Fin n → ℝ) (h : nsq x ≤ ∑ a, x a * y a) :
    nsq x ≤ nsq y ∧ (nsq y ≤ nsq x → x = y) := by
  have hsq : 0 ≤ ∑ a, (x a - y a) ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hexp : ∑ a, (x a - y a) ^ 2 = nsq x - 2 * ∑ a, x a * y a + nsq y := by
    unfold nsq
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  refine ⟨by linarith, fun h2 => ?_⟩
  have h0 : ∑ a, (x a - y a) ^ 2 = 0 := by linarith
  funext a
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (x a - y a))).1 h0 a (Finset.mem_univ a)
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)

theorem UpperTheory.RealTr.rearr :
    ∀ n : ℕ, (∀ x y : Wt n, Antitone x → Antitone y → ∀ w : Equiv.Perm (Fin n), ∑ a, x a * y (w a) ≤ ∑ a, x a * y a ∧
        (StrictAnti x → StrictAnti y → ∑ a, x a * y (w a) = ∑ a, x a * y a → w = 1)) ∧
      (∀ x : Wt n, Antitone (domC x) ∧ (∃ w : Equiv.Perm (Fin n), domC x = x ∘ w) ∧ (Antitone x → domC x = x) ∧
        (∀ w : Equiv.Perm (Fin n), domC (x ∘ w) = domC x) ∧ nsq (domC x) = nsq x) ∧
      StrictAnti (rhoV n) ∧ Dom (rhoV n) ∧ (∀ x : Wt n, Dom x → Antitone x ∧ Dom (domC (x - rhoV n))) ∧
      ∀ x y : Wt n, nsq x ≤ ∑ a, x a * y a → nsq x ≤ nsq y ∧ (nsq y ≤ nsq x → x = y) := by
  intro n
  exact ⟨fun x y hx hy w => sum_mul_perm_le_and_eq_one_of_antitone x y hx hy w, fun x => rearr_lemma_2 x, (strictAnti_rhoV_and_dom_rhoV n).1, (strictAnti_rhoV_and_dom_rhoV n).2,
    fun x hx => antitone_and_dom_domC_sub_rhoV_of_dom n x hx, fun x y h => nsq_le_and_eq_of_nsq_le_sum_mul x y h⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DualEx
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

section SlopeTestRemainingChoices

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

private def eD : (V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) where
  toFun ξ := WithLp.toLp 2 fun i => ξ (stdOrthonormalBasis ℂ V i)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp
  invFun y := ∑ i, y i • innerSL ℂ (stdOrthonormalBasis ℂ V i)
  left_inv ξ := by
    ext v
    have h := (stdOrthonormalBasis ℂ V).sum_repr' v
    conv_rhs => rw [← h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [sum_apply, map_sum, mul_comm]
  right_inv y := by
    ext j
    simp [sum_apply, OrthonormalBasis.inner_eq_ite]

private theorem eD_apply (ξ : V →L[ℂ] ℂ) (i) : eD ξ i = ξ (stdOrthonormalBasis ℂ V i) := rfl

private theorem norm_eD (ξ : V →L[ℂ] ℂ) : ‖eD ξ‖ = ‖ξ‖ := by
  set b := stdOrthonormalBasis ℂ V
  set u := (InnerProductSpace.toDual ℂ V).symm ξ
  have hu : ∀ v, ξ v = ⟪u, v⟫_ℂ := fun v => (InnerProductSpace.toDual_symm_apply).symm
  rw [← (InnerProductSpace.toDual ℂ V).symm.norm_map ξ, ← b.repr.norm_map u,
    EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eD_apply, hu, b.repr_apply_apply, ← inner_conj_symm, Complex.norm_conj]

private def pr (A : V →L[ℂ] V) :
    EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
  ((eD (V := V)).toContinuousLinearEquiv : (V →L[ℂ] ℂ) →L[ℂ] _).comp
    (((ContinuousLinearMap.compL ℂ V V ℂ).flip A).comp
      ((eD (V := V)).toContinuousLinearEquiv.symm : _ →L[ℂ] (V →L[ℂ] ℂ)))

private theorem pr_apply (A : V →L[ℂ] V) (y) : pr A y = eD ((eD.symm y).comp A) := rfl

private theorem pr_eD (A : V →L[ℂ] V) (ξ : V →L[ℂ] ℂ) : pr A (eD ξ) = eD (ξ.comp A) := by
  rw [pr_apply, LinearEquiv.symm_apply_apply]

private theorem pr_one : pr (1 : V →L[ℂ] V) = 1 := by
  ext1 y
  rw [pr_apply, one_apply_eq_self]
  show eD ((eD.symm y).comp (ContinuousLinearMap.id ℂ V)) = y
  rw [ContinuousLinearMap.comp_id, LinearEquiv.apply_symm_apply]

private theorem pr_mul (A B : V →L[ℂ] V) : pr (A * B) = pr B * pr A := by
  ext1 y
  rw [mul_apply_eq_comp, pr_apply, pr_apply, pr_apply, LinearEquiv.symm_apply_apply,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

private theorem continuous_pr : Continuous (pr (V := V)) := by
  unfold pr
  fun_prop

private theorem trace_pr (A : V →L[ℂ] V) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (Module.finrank ℂ V)))
      ((pr A : EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :
        EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) =
      LinearMap.trace ℂ V (A : V →ₗ[ℂ] V) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin (Module.finrank ℂ V)) ℂ).toBasis,
    LinearMap.trace_eq_matrix_trace ℂ (stdOrthonormalBasis ℂ V).toBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe, pr_apply]
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, eD_apply, ContinuousLinearMap.comp_apply]
  show (∑ j, (EuclideanSpace.single i (1 : ℂ)) j • innerSL ℂ (stdOrthonormalBasis ℂ V j))
    (A (stdOrthonormalBasis ℂ V i)) = _
  simp [PiLp.single_apply]

end SlopeTestRemainingChoices

theorem UpperTheory.RealTr.dualEx :
    ∀ (n : ℕ) (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) → ∃ (E' : KMod n) (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] E'.V) (T' : Module.End ℂ E'.V),
      (∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = E'.ρ k (e ξ)) ∧ (∀ ξ, e (dualT E T ξ) = T' (e ξ)) ∧
      ∀ k, LinearMap.trace ℂ E'.V (E'.ρ k : E'.V →ₗ[ℂ] E'.V) = LinearMap.trace ℂ E.V (E.ρ k⁻¹ : E.V →ₗ[ℂ] E.V) ∧
        LinearMap.trace ℂ E'.V ((E'.ρ k : E'.V →ₗ[ℂ] E'.V) * T') = LinearMap.trace ℂ E.V ((E.ρ k⁻¹ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) := by
  intro n E T hT
  have hnorm : ∀ (k : UK n) (ξ : E.V →L[ℂ] ℂ), ‖ξ.comp (E.ρ k)‖ ≤ ‖ξ‖ := by
    intro k ξ
    have hk : ‖E.ρ k‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [E.iso, one_mul]
    calc ‖ξ.comp (E.ρ k)‖ ≤ ‖ξ‖ * ‖E.ρ k‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖ξ‖ * 1 := by gcongr
      _ = ‖ξ‖ := mul_one _
  have hinv : Continuous (fun k : UK n => k⁻¹) := by
    exact continuous_inv
  let ρ' : UK n →* (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) :=
    { toFun := fun k => pr (E.ρ k⁻¹)
      map_one' := by simp [pr_one]
      map_mul' := by
        intro k l
        simp only [_root_.mul_inv_rev, map_mul, pr_mul] }
  let E' : KMod n :=
    { V := EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))
      ρ := ρ'
      iso := by
        intro k y
        obtain ⟨ξ, rfl⟩ := eD.surjective y
        show ‖pr (E.ρ k⁻¹) (eD ξ)‖ = ‖eD ξ‖
        rw [pr_eD, norm_eD, norm_eD]
        apply le_antisymm (hnorm _ ξ)
        calc ‖ξ‖ = ‖(ξ.comp (E.ρ k⁻¹)).comp (E.ρ k)‖ := by
              rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.mul_def, ← map_mul, inv_mul_cancel,
                map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
          _ ≤ ‖ξ.comp (E.ρ k⁻¹)‖ := hnorm _ _
      cont := continuous_pr.comp (E.cont.comp hinv) }
  refine ⟨E', eD, (pr T : E'.V →L[ℂ] E'.V), ?_, ?_, ?_⟩
  · intro k ξ
    exact (pr_eD _ ξ).symm
  · intro ξ
    exact (pr_eD T ξ).symm
  · intro k
    constructor
    · exact trace_pr (E.ρ k⁻¹)
    · show LinearMap.trace ℂ _ ((pr (E.ρ k⁻¹) : E'.V →ₗ[ℂ] E'.V) * (pr T : E'.V →ₗ[ℂ] E'.V)) = _
      rw [← ContinuousLinearMap.toLinearMap_mul, ← pr_mul, trace_pr, hT]
end
end

