module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaMeromorphicFromTwists
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.TwoRelations

open Filter Topology

noncomputable def mult (l : ℕ) (s : ℂ) : ℂ := (l : ℂ) ^ (1 - s)

noncomputable def efac (l h : ℕ) (s : ℂ) : ℂ := mult l s ^ h - 1

noncomputable def wsum {G : Type} (T : G → ℂ → ℂ) (l : ℕ) (τ : Equiv.Perm G) (h : ℕ)
    (c : G) (s : ℂ) : ℂ :=
  ∑ e ∈ Finset.range h, mult l s ^ e * T ((τ ^ e) c) s

lemma mult_differentiable {l : ℕ} (hl : l.Prime) : Differentiable ℂ (mult l) := by
  intro s
  have h0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h0)

lemma efac_differentiable {l : ℕ} (hl : l.Prime) (h : ℕ) : Differentiable ℂ (efac l h) := by
  intro s
  exact (((mult_differentiable hl) s).pow h).sub (differentiableAt_const _)

lemma wsum_differentiable {G : Type} {T : G → ℂ → ℂ} {l : ℕ} (hl : l.Prime)
    (hT : ∀ c, Differentiable ℂ (T c)) (τ : Equiv.Perm G) (h : ℕ) (c : G) :
    Differentiable ℂ (wsum T l τ h c) := by
  intro s
  unfold wsum
  refine DifferentiableAt.fun_sum fun e _ => ?_
  exact (((mult_differentiable hl) s).pow e).mul (hT _ s)

lemma norm_mult_lt_one {l : ℕ} (hl : l.Prime) {s : ℂ} (hs : 1 < s.re) : ‖mult l s‖ < 1 := by
  unfold mult
  rw [Complex.norm_natCast_cpow_of_pos hl.pos]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hl.one_lt
  · simp only [Complex.sub_re, Complex.one_re]; linarith

lemma efac_ne_zero {l h : ℕ} (hl : l.Prime) (hh : h ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    efac l h s ≠ 0 := by
  intro h0
  have h1 : mult l s ^ h = 1 := sub_eq_zero.mp h0
  have h2 : ‖mult l s‖ ^ h = 1 := by rw [← norm_pow, h1, norm_one]
  have h3 := pow_lt_one₀ (norm_nonneg _) (norm_mult_lt_one hl hs) hh
  linarith

lemma telescope {G : Type} {D T : G → ℂ → ℂ} {l : ℕ} {τ : Equiv.Perm G} {s : ℂ}
    (hrel : ∀ c, mult l s * D (τ c) s - D c s = T c s) (c : G) (n : ℕ) :
    wsum T l τ n c s = mult l s ^ n * D ((τ ^ n) c) s - D c s := by
  induction n with
  | zero => simp [wsum]
  | succ n ih =>
    have ih' : ∑ e ∈ Finset.range n, mult l s ^ e * T ((τ ^ e) c) s
        = mult l s ^ n * D ((τ ^ n) c) s - D c s := ih
    have hstep : (τ ^ (n + 1)) c = τ ((τ ^ n) c) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    unfold wsum
    rw [Finset.sum_range_succ, ih', ← hrel ((τ ^ n) c), hstep]
    ring

lemma efac_mul_eq {G : Type} [Fintype G] {D T : G → ℂ → ℂ} {l : ℕ} {τ : Equiv.Perm G} {s : ℂ}
    (hrel : ∀ c, mult l s * D (τ c) s - D c s = T c s) (c : G) :
    efac l (orderOf τ) s * D c s = wsum T l τ (orderOf τ) c s := by
  rw [telescope hrel c, pow_orderOf_eq_one]
  simp only [efac, Equiv.Perm.coe_one, id_eq]
  ring

lemma no_common_zero {l l' h h' : ℕ} (hl : l.Prime) (hl' : l'.Prime) (hne : l ≠ l')
    (hh : h ≠ 0) (hh' : h' ≠ 0) {s : ℂ} (hs : s ≠ 1)
    (h1 : efac l h s = 0) (h2 : efac l' h' s = 0) : False := by
  have hexp : ∀ {p : ℕ}, p.Prime → ∀ m : ℕ, mult p s ^ m
      = Complex.exp ((m : ℂ) * (((Real.log p : ℝ) : ℂ) * (1 - s))) := by
    intro p hp m
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [Complex.exp_nat_mul, mult, Complex.cpow_def_of_ne_zero hp0, Complex.natCast_log]
  have hu : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hL : 0 < Real.log l := Real.log_pos (by exact_mod_cast hl.one_lt)
  have hL' : 0 < Real.log l' := Real.log_pos (by exact_mod_cast hl'.one_lt)
  have e1 : Complex.exp ((h : ℂ) * (((Real.log l : ℝ) : ℂ) * (1 - s))) = 1 := by
    rw [← hexp hl]; exact sub_eq_zero.mp h1
  have e2 : Complex.exp ((h' : ℂ) * (((Real.log l' : ℝ) : ℂ) * (1 - s))) = 1 := by
    rw [← hexp hl']; exact sub_eq_zero.mp h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp e1
  obtain ⟨n', hn'⟩ := Complex.exp_eq_one_iff.mp e2
  have hLc : ((Real.log l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLc' : ((Real.log l' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL'.ne'
  have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hhc' : (h' : ℂ) ≠ 0 := by exact_mod_cast hh'
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : (h : ℂ) * (((Real.log l : ℝ) : ℂ) * (1 - s)) ≠ 0 :=
      mul_ne_zero hhc (mul_ne_zero hLc hu)
    apply this; rw [hn]; simp
  have hn0' : n' ≠ 0 := by
    rintro rfl
    have : (h' : ℂ) * (((Real.log l' : ℝ) : ℂ) * (1 - s)) ≠ 0 :=
      mul_ne_zero hhc' (mul_ne_zero hLc' hu)
    apply this; rw [hn']; simp
  have hcross : ((n' : ℂ) * h * ((Real.log l : ℝ) : ℂ)) = (n : ℂ) * h' * ((Real.log l' : ℝ) : ℂ) := by
    apply mul_right_cancel₀ hu
    calc (n' : ℂ) * h * ((Real.log l : ℝ) : ℂ) * (1 - s)
        = (n' : ℂ) * ((h : ℂ) * (((Real.log l : ℝ) : ℂ) * (1 - s))) := by ring
      _ = (n : ℂ) * ((h' : ℂ) * (((Real.log l' : ℝ) : ℂ) * (1 - s))) := by
          rw [hn, hn']; ring
      _ = (n : ℂ) * h' * ((Real.log l' : ℝ) : ℂ) * (1 - s) := by ring
  have hreal : (n' : ℝ) * h * Real.log l = (n : ℝ) * h' * Real.log l' := by
    exact_mod_cast hcross
  have habs : (n'.natAbs : ℝ) * h * Real.log l = (n.natAbs : ℝ) * h' * Real.log l' := by
    have := congrArg abs hreal
    simp only [abs_mul, Nat.abs_cast, abs_of_pos hL, abs_of_pos hL'] at this
    rw [Nat.cast_natAbs, Nat.cast_natAbs]
    push_cast
    exact this
  have hlog : Real.log ((l : ℝ) ^ (n'.natAbs * h)) = Real.log ((l' : ℝ) ^ (n.natAbs * h')) := by
    rw [Real.log_pow, Real.log_pow]
    push_cast
    exact habs
  have hpos : (0 : ℝ) < (l : ℝ) ^ (n'.natAbs * h) := by
    have : (0 : ℝ) < l := by exact_mod_cast hl.pos
    positivity
  have hpos' : (0 : ℝ) < (l' : ℝ) ^ (n.natAbs * h') := by
    have : (0 : ℝ) < l' := by exact_mod_cast hl'.pos
    positivity
  have heq := Real.log_injOn_pos (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hpos') hlog
  have hnat : l ^ (n'.natAbs * h) = l' ^ (n.natAbs * h') := by exact_mod_cast heq
  have hexp0 : n'.natAbs * h ≠ 0 := Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hn0') hh
  have hdvd : l ∣ l' ^ (n.natAbs * h') := by
    rw [← hnat]; exact dvd_pow_self l hexp0
  exact hne ((Nat.prime_dvd_prime_iff_eq hl hl').mp (hl.dvd_of_dvd_pow hdvd))

lemma entire_eq_of_halfplane {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfg : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) := hopen.mem_nhds (by simp)
  refine hfa.eq_of_eventuallyEq hga (z₀ := 2) ?_
  filter_upwards [hmem] with s hs using hfg s hs

lemma glue_differentiableAt {E E' W W' : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hE' : Differentiable ℂ E') (hW : Differentiable ℂ W) (hW' : Differentiable ℂ W')
    (hcross : ∀ s, W s * E' s = W' s * E s) {s : ℂ} (hs : E s ≠ 0 ∨ E' s ≠ 0) :
    DifferentiableAt ℂ (fun t => if E t ≠ 0 then W t / E t else W' t / E' t) s := by
  by_cases h : E s ≠ 0
  · have hev : ∀ᶠ t in 𝓝 s, E t ≠ 0 := hE.continuous.continuousAt.eventually_ne h
    refine ((hW s).div (hE s) h).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    simp [ht]
  · have h' : E' s ≠ 0 := hs.resolve_left h
    have hev : ∀ᶠ t in 𝓝 s, E' t ≠ 0 := hE'.continuous.continuousAt.eventually_ne h'
    refine ((hW' s).div (hE' s) h').congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [Pi.div_apply]
    by_cases h0 : E t ≠ 0
    · rw [if_pos h0, div_eq_div_iff h0 ht]
      exact hcross t
    · rw [if_neg h0]

lemma mult_at_neg {l k : ℕ} : mult l (1 - (k : ℂ)) = ((l ^ k : ℕ) : ℂ) := by
  simp [mult]

theorem continuation_of_two_relations :
    ∀ (G : Type) [Fintype G] (D T T' : G → ℂ → ℂ) (l l' : ℕ) (τ τ' : Equiv.Perm G),
    l.Prime → l'.Prime → l ≠ l' →
    (∀ c, Differentiable ℂ (T c)) → (∀ c, Differentiable ℂ (T' c)) →
    (∀ c s, 1 < s.re → (l : ℂ) ^ (1 - s) * D (τ c) s - D c s = T c s) →
    (∀ c s, 1 < s.re → (l' : ℂ) ^ (1 - s) * D (τ' c) s - D c s = T' c s) →
    ∃ Z : G → ℂ → ℂ, (∀ c, DifferentiableOn ℂ (Z c) {1}ᶜ) ∧ (∀ c s, 1 < s.re → Z c s = D c s) ∧
      ∀ k : ℕ, 1 ≤ k → (∀ c, ∃ q : ℚ, T c (1 - (k : ℂ)) = (q : ℂ)) →
        ∀ c, ∃ q : ℚ, Z c (1 - (k : ℂ)) = (q : ℂ) := by
  intro G _ D T T' l l' τ τ' hl hl' hne hT hT' hrel hrel'
  have hh : orderOf τ ≠ 0 := (orderOf_pos τ).ne'
  have hh' : orderOf τ' ≠ 0 := (orderOf_pos τ').ne'
  have hED : ∀ c s, 1 < s.re →
      efac l (orderOf τ) s * D c s = wsum T l τ (orderOf τ) c s :=
    fun c s hs => efac_mul_eq (fun c => hrel c s hs) c
  have hED' : ∀ c s, 1 < s.re →
      efac l' (orderOf τ') s * D c s = wsum T' l' τ' (orderOf τ') c s :=
    fun c s hs => efac_mul_eq (fun c => hrel' c s hs) c
  have hEd := efac_differentiable hl (orderOf τ)
  have hEd' := efac_differentiable hl' (orderOf τ')
  have hWd := fun c => wsum_differentiable hl hT τ (orderOf τ) c
  have hWd' := fun c => wsum_differentiable hl' hT' τ' (orderOf τ') c
  have hcross : ∀ c s, wsum T l τ (orderOf τ) c s * efac l' (orderOf τ') s
      = wsum T' l' τ' (orderOf τ') c s * efac l (orderOf τ) s := by
    intro c s
    have := entire_eq_of_halfplane
      (f := fun s => wsum T l τ (orderOf τ) c s * efac l' (orderOf τ') s)
      (g := fun s => wsum T' l' τ' (orderOf τ') c s * efac l (orderOf τ) s)
      ((hWd c).mul hEd') ((hWd' c).mul hEd)
      (fun s hs => by
        show wsum T l τ (orderOf τ) c s * efac l' (orderOf τ') s
          = wsum T' l' τ' (orderOf τ') c s * efac l (orderOf τ) s
        rw [← hED c s hs, ← hED' c s hs]; ring)
    exact congrFun this s
  refine ⟨fun c t => if efac l (orderOf τ) t ≠ 0 then
      wsum T l τ (orderOf τ) c t / efac l (orderOf τ) t
    else wsum T' l' τ' (orderOf τ') c t / efac l' (orderOf τ') t, ?_, ?_, ?_⟩
  · intro c s hs
    have hs1 : s ≠ 1 := hs
    have hor : efac l (orderOf τ) s ≠ 0 ∨ efac l' (orderOf τ') s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact no_common_zero hl hl' hne hh hh' hs1 hcon.1 hcon.2
    exact (glue_differentiableAt hEd hEd' (hWd c) (hWd' c) (hcross c) hor).differentiableWithinAt
  · intro c s hs
    have h0 := efac_ne_zero hl hh hs
    show (if efac l (orderOf τ) s ≠ 0 then _ else _) = _
    rw [if_pos h0, ← hED c s hs, mul_div_cancel_left₀ _ h0]
  · intro k hk hq c
    choose q hq using hq
    have hm : mult l (1 - (k : ℂ)) = ((l ^ k : ℕ) : ℂ) := mult_at_neg
    have hnat : (l ^ k) ^ orderOf τ ≠ 1 :=
      ne_of_gt (Nat.one_lt_pow hh (Nat.one_lt_pow (by omega) hl.one_lt))
    have hE : efac l (orderOf τ) (1 - (k : ℂ)) = (((((l ^ k) ^ orderOf τ : ℕ) : ℚ) - 1 : ℚ) : ℂ) := by
      simp only [efac, hm]
      push_cast
      ring
    have h0 : efac l (orderOf τ) (1 - (k : ℂ)) ≠ 0 := by
      rw [hE]
      intro hz
      have hz' : ((((l ^ k) ^ orderOf τ : ℕ) : ℚ) - 1 : ℚ) = 0 := by exact_mod_cast hz
      apply hnat
      have : (((l ^ k) ^ orderOf τ : ℕ) : ℚ) = 1 := by linarith
      exact_mod_cast this
    have hW : wsum T l τ (orderOf τ) c (1 - (k : ℂ))
        = ((∑ e ∈ Finset.range (orderOf τ), (((l ^ k : ℕ) : ℚ)) ^ e * q ((τ ^ e) c) : ℚ) : ℂ) := by
      simp only [wsum, hm, hq]
      push_cast
      rfl
    refine ⟨(∑ e ∈ Finset.range (orderOf τ), (((l ^ k : ℕ) : ℚ)) ^ e * q ((τ ^ e) c)) /
      ((((l ^ k) ^ orderOf τ : ℕ) : ℚ) - 1), ?_⟩
    show (if efac l (orderOf τ) (1 - (k : ℂ)) ≠ 0 then _ else _) = _
    rw [if_pos h0, hW, hE, Rat.cast_div]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.TwoRelations
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTwistedEntireDifference
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

variable {F : Type} [Field F] [NumberField F]

def conePt {r : ℕ} (y : 𝓞 F) (v : Fin r → 𝓞 F) (m : Fin r → ℕ) : 𝓞 F := y + ∑ i, (m i : 𝓞 F) * v i


open Classical in
def coneWeight {r : ℕ} (l : ℕ) (A : Ideal (𝓞 F)) (y : 𝓞 F) (v : Fin r → 𝓞 F) (m : Fin r → ℕ) : ℚ :=
  if conePt y v m ∈ A then (l : ℚ) - 1 else -1

theorem conePt_add_single {r : ℕ} (y : 𝓞 F) (v : Fin r → 𝓞 F) (m : Fin r → ℕ) (i : Fin r) (e : ℕ) :
    conePt y v (m + (Pi.single i e : Fin r → ℕ)) = conePt y v m + (e : 𝓞 F) * v i := by
  simp only [conePt, Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib, add_assoc]
  congr 2
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem relIndex_mul_eq_absNorm (𝔠 𝔟 : Ideal (𝓞 F)) (hb : 𝔟 ≠ ⊥) :
    (𝔠 * 𝔟).toAddSubgroup.relIndex 𝔟.toAddSubgroup = Ideal.absNorm 𝔠 := by
  have hle : (𝔠 * 𝔟).toAddSubgroup ≤ 𝔟.toAddSubgroup := (Submodule.toAddSubgroup_le _ _).2 Ideal.mul_le_right
  have h := AddSubgroup.relIndex_mul_index hle
  have e : ∀ I : Ideal (𝓞 F), I.toAddSubgroup.index = Ideal.absNorm I := fun I => by
    rw [Ideal.absNorm_apply, Submodule.cardQuot]
  rw [e, e, map_mul] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hb)) h

theorem exists_unique_shift_mem {𝔠 𝔟 : Ideal (𝓞 F)} (hb : 𝔟 ≠ ⊥) (hl : (Ideal.absNorm 𝔠).Prime) {x v : 𝓞 F}
    (hx : x ∈ 𝔟) (hv : v ∈ 𝔟) (hv' : v ∉ 𝔠 * 𝔟) :
    ∃ e₀ < Ideal.absNorm 𝔠, ∀ e < Ideal.absNorm 𝔠, (x + (e : 𝓞 F) * v ∈ 𝔠 * 𝔟 ↔ e = e₀) := by
  classical
  haveI : Fact (Ideal.absNorm 𝔠).Prime := ⟨hl⟩
  let B := 𝔟.toAddSubgroup
  let H : AddSubgroup B := (𝔠 * 𝔟).toAddSubgroup.addSubgroupOf B
  have hcard : Nat.card (B ⧸ H) = Ideal.absNorm 𝔠 := relIndex_mul_eq_absNorm 𝔠 𝔟 hb
  haveI : Finite (B ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hl.ne_zero)
  let X : B := ⟨x, hx⟩
  let V : B := ⟨v, hv⟩
  have hz : ∀ z : B, (z : B ⧸ H) = 0 ↔ (z : 𝓞 F) ∈ 𝔠 * 𝔟 := fun z => by
    rw [QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_addSubgroupOf
  have hV : (V : B ⧸ H) ≠ 0 := fun h => hv' ((hz V).1 h)
  have hord : addOrderOf (V : B ⧸ H) = Ideal.absNorm 𝔠 :=
    addOrderOf_eq_prime (by rw [← hcard]; exact card_nsmul_eq_zero') hV
  have hmem : -(X : B ⧸ H) ∈ AddSubgroup.zmultiples (V : B ⧸ H) := mem_zmultiples_of_prime_card hcard hV
  rw [← mem_multiples_iff_mem_zmultiples, mem_multiples_iff_mem_range_addOrderOf, hord] at hmem
  obtain ⟨e₀, he₀, h₀⟩ := Finset.mem_image.1 hmem
  have he₀' := Finset.mem_range.1 he₀
  refine ⟨e₀, he₀', fun e he => ?_⟩
  have hc : x + (e : 𝓞 F) * v = ((X + e • V : B) : 𝓞 F) := by simp [X, V, nsmul_eq_mul]
  rw [hc, ← hz]
  have hq : ((X + e • V : B) : B ⧸ H) = (X : B ⧸ H) + e • (V : B ⧸ H) := rfl
  have hX : (X : B ⧸ H) = -(e₀ • (V : B ⧸ H)) := by
    have h₀' : e₀ • (V : B ⧸ H) = -(X : B ⧸ H) := h₀
    rw [h₀', neg_neg]
  rw [hq, hX, neg_add_eq_zero]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  exact nsmul_injOn_Iio_addOrderOf (by simpa [hord] using he) (by simpa [hord] using he₀') h.symm

theorem goodWeight_coneWeight {𝔠 𝔟 : Ideal (𝓞 F)} (hb : 𝔟 ≠ ⊥) (hl : (Ideal.absNorm 𝔠).Prime) {r : ℕ} {y : 𝓞 F}
    {v : Fin r → 𝓞 F} (hy : y ∈ 𝔟) (hv : ∀ i, v i ∈ 𝔟) (hv' : ∀ i, v i ∉ 𝔠 * 𝔟) :
    GoodWeight (Ideal.absNorm 𝔠) (coneWeight (Ideal.absNorm 𝔠) (𝔠 * 𝔟) y v) := by
  classical
  have hpt : ∀ m, conePt y v m ∈ 𝔟 := fun m =>
    𝔟.add_mem hy (𝔟.sum_mem fun i _ => 𝔟.mul_mem_left _ (hv i))
  refine ⟨fun m i => ?_, fun m i => ?_⟩
  · have h : ((Ideal.absNorm 𝔠 : ℕ) : 𝓞 F) * v i ∈ 𝔠 * 𝔟 := Ideal.mul_mem_mul (Ideal.absNorm_mem 𝔠) (hv i)
    have : conePt y v (m + (Pi.single i (Ideal.absNorm 𝔠) : Fin r → ℕ)) ∈ 𝔠 * 𝔟 ↔ conePt y v m ∈ 𝔠 * 𝔟 := by
      rw [conePt_add_single]
      exact Ideal.add_mem_iff_left _ h
    simp only [coneWeight, this]
  · obtain ⟨e₀, he₀, h⟩ := exists_unique_shift_mem hb hl (hpt m) (hv i) (hv' i)
    have h2 : ∀ e ∈ Finset.range (Ideal.absNorm 𝔠),
        coneWeight (Ideal.absNorm 𝔠) (𝔠 * 𝔟) y v (m + (Pi.single i e : Fin r → ℕ)) =
          (if e = e₀ then (Ideal.absNorm 𝔠 : ℚ) else 0) - 1 := fun e he => by
      simp only [coneWeight, conePt_add_single, h e (Finset.mem_range.1 he)]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp [he₀]

theorem le_iff_mem_mul_of_span {I 𝔠 𝔟 : Ideal (𝓞 F)} (hb : 𝔟 ≠ ⊥) {x : 𝓞 F} (h : I * 𝔟 = Ideal.span {x}) :
    I ≤ 𝔠 ↔ x ∈ 𝔠 * 𝔟 := by
  rw [← Ideal.span_singleton_le_iff_mem, ← h, ← Ideal.dvd_iff_le, ← Ideal.dvd_iff_le, mul_dvd_mul_iff_right hb]

theorem ofReal_finset_prod_cpow {ι : Type} (S : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (s : ℂ) :
    ∏ i ∈ S, ((f i : ℝ) : ℂ) ^ s = ((∏ i ∈ S, f i : ℝ) : ℂ) ^ s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf i) (Finset.prod_nonneg fun j _ => hf j)]

def realEmbeddingsEquiv (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : (F →+* ℝ) ≃ (F →+* ℂ) :=
  Equiv.ofBijective (fun σ => Complex.ofRealHom.comp σ)
    ⟨fun σ τ h => RingHom.ext fun x => Complex.ofReal_injective (by simpa using RingHom.congr_fun h x), fun φ => by
      have hφ : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))
      exact ⟨hφ.embedding, RingHom.ext fun x => by simpa using hφ.coe_embedding_apply x⟩⟩

theorem prod_real_embeddings_eq_norm [IsTotallyReal F] [Fintype (F →+* ℝ)] (x : F) :
    ∏ σ : F →+* ℝ, σ x = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 : ∏ σ : F →+* ℝ, ((σ x : ℝ) : ℂ) = ∏ τ : F →ₐ[ℚ] ℂ, τ x :=
    Fintype.prod_equiv ((realEmbeddingsEquiv F).trans (RingHom.equivRatAlgHom F ℂ)) _ _ (fun σ => rfl)
  rw [Complex.ofReal_prod, h2, ← h]
  simp

theorem prod_real_embeddings_eq_absNorm [IsTotallyReal F] [Fintype (F →+* ℝ)] (x : 𝓞 F) (hx : TotPos F (x : F)) :
    ∏ σ : F →+* ℝ, σ (x : F) = ((Ideal.absNorm (Ideal.span {x}) : ℕ) : ℝ) := by
  have hpos : 0 ≤ ∏ σ : F →+* ℝ, σ (x : F) := Finset.prod_nonneg fun σ _ => (hx σ).le
  have h := prod_real_embeddings_eq_norm (x : F)
  rw [← Algebra.coe_norm_int] at h
  rw [Ideal.absNorm_span_singleton]
  rw [h] at hpos ⊢
  push_cast at hpos ⊢
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hpos]

theorem embedding_conePt {r : ℕ} (σ : F →+* ℝ) (y : 𝓞 F) (v : Fin r → 𝓞 F) (m : Fin r → ℕ) :
    σ (conePt y v m : F) = σ (y : F) + ∑ i, σ (v i : F) * (m i : ℝ) := by
  have : ((conePt y v m : 𝓞 F) : F) = (y : F) + ∑ i, (m i : F) * (v i : F) := by
    change algebraMap (𝓞 F) F (conePt y v m) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp [conePt, map_add (f := _), map_sum, map_mul, map_natCast]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_add (f := _), map_sum]
  simp [mul_comm]

theorem totPos_conePt {r : ℕ} {y : 𝓞 F} {v : Fin r → 𝓞 F} (hy : TotPos F (y : F)) (hv : ∀ i, TotPos F (v i : F))
    (m : Fin r → ℕ) : TotPos F (conePt y v m : F) := fun σ => by
  rw [embedding_conePt]
  exact add_pos_of_pos_of_nonneg (hy σ) (Finset.sum_nonneg fun i _ => mul_nonneg (hv i σ).le (Nat.cast_nonneg _))

theorem coneTerm_eq_absNorm_cpow [IsTotallyReal F] [Fintype (F →+* ℝ)] {r : ℕ} {y : 𝓞 F} {v : Fin r → 𝓞 F}
    (hy : TotPos F (y : F)) (hv : ∀ i, TotPos F (v i : F)) (s : ℂ) (m : Fin r → ℕ) :
    coneTerm (fun (σ : F →+* ℝ) i => σ (v i : F)) (fun σ => σ (y : F)) s m =
      ((Ideal.absNorm (Ideal.span {conePt y v m}) : ℕ) : ℂ) ^ (-s) := by
  have h := prod_real_embeddings_eq_absNorm (conePt y v m) (totPos_conePt hy hv m)
  have h2 := ofReal_finset_prod_cpow Finset.univ (fun σ : F →+* ℝ => σ (conePt y v m : F))
    (fun σ => (totPos_conePt hy hv m σ).le) (-s)
  rw [h, Complex.ofReal_natCast] at h2
  simp only [coneTerm, ← embedding_conePt]
  exact h2

theorem classTwist_entire : AbelContinuation → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J]
  (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime →
    (∀ j i, v j i ∉ 𝔠 * 𝔟) →
    ∃ T : ℂ → ℂ, Differentiable ℂ T ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
        (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) := by
  intro AC F _ _ _ 𝔣 𝔞 𝔟 𝔠 J _ r y v hP hc hl hv'
  obtain ⟨hb, hy, hv, hr, e, he⟩ := hP
  haveI : Fintype (F →+* ℝ) := Fintype.ofEquiv _ (realEmbeddingsEquiv F).symm
  have hcard : Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
    rw [Fintype.card_congr (realEmbeddingsEquiv F), Embeddings.card]
  have key := fun j => AC (F →+* ℝ) (r j) (Ideal.absNorm 𝔠) (fun σ i => σ (v j i : F)) (fun σ => σ (y j : F))
    (coneWeight (Ideal.absNorm 𝔠) (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl.pos
    (fun σ i => (hv j i).2 σ) (fun σ => (hy j).2 σ)
    (goodWeight_coneWeight hb hl (hy j).1 (fun i => (hv j i).1) (hv' j))
  choose T hTd hTs hTv using key
  have hN0 : Ideal.absNorm 𝔟 ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using hb
  have hNb : ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hterm : ∀ (p : Σ j, (Fin (r j) → ℕ)) (s : ℂ),
      (classWeight (Ideal.absNorm 𝔠) 𝔠 (e p).1 : ℂ) * ((Ideal.absNorm (e p).1 : ℕ) : ℂ) ^ (-s) =
        ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * (((coneWeight (Ideal.absNorm 𝔠) (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℚ) : ℂ) *
          coneTerm (fun (σ : F →+* ℝ) i => σ (v p.1 i : F)) (fun σ => σ (y p.1 : F)) s p.2) := by
    intro p s
    have h1 : classWeight (Ideal.absNorm 𝔠) 𝔠 (e p).1 = coneWeight (Ideal.absNorm 𝔠) (𝔠 * 𝔟) (y p.1) (v p.1) p.2 := by
      have hI : (e p).1 ≤ 𝔠 ↔ conePt (y p.1) (v p.1) p.2 ∈ 𝔠 * 𝔟 := le_iff_mem_mul_of_span hb (he p)
      simp only [classWeight, coneWeight]
      by_cases h : (e p).1 ≤ 𝔠
      · rw [if_pos h, if_pos (hI.1 h)]
      · rw [if_neg h, if_neg fun h' => h (hI.2 h')]
    have h2 := he p
    have h3 : Ideal.absNorm (Ideal.span {conePt (y p.1) (v p.1) p.2}) = Ideal.absNorm (e p).1 * Ideal.absNorm 𝔟 := by
      rw [← map_mul, h2, conePt]
    have hne : ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hNb]
    rw [coneTerm_eq_absNorm_cpow (hy p.1).2 (fun i => (hv p.1 i).2), h1, h3, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, Complex.cpow_neg ((Ideal.absNorm 𝔟 : ℕ) : ℂ) s]
    field_simp
  refine ⟨fun s => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, T j s, ?_, ?_, ?_⟩
  · exact (differentiable_id.const_cpow (Or.inl hNb)).mul (Differentiable.fun_sum fun j _ => hTd j)
  · intro s hs
    rw [← e.hasSum_iff]
    beta_reduce
    rw [Finset.mul_sum]
    have h1 : ∀ j, HasSum (fun m => ((fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
        (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) ∘ e) ⟨j, m⟩)
        (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * T j s) := fun j => by
      have e1 := funext fun m => hterm ⟨j, m⟩ s
      simp only [Function.comp]
      rw [e1]
      exact (hTs j s hs).mul_left _
    refine HasSum.sigma_of_hasSum (hasSum_fintype _) h1 (Summable.of_norm ?_)
    exact (summable_sigma_of_nonneg fun _ => norm_nonneg _).2 ⟨fun j => (h1 j).summable.norm, Summable.of_finite⟩
  · intro k hk
    obtain ⟨p, rfl⟩ : ∃ p, k = p + 1 := ⟨k - 1, by omega⟩
    have hs : (1 - ((p + 1 : ℕ) : ℂ)) = -(p : ℂ) := by push_cast; ring
    have hq : ∀ j, ∃ q : ℚ, T j (-(p : ℂ)) = (q : ℂ) := fun j => hTv j p fun m => by
      refine ⟨((Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) : ℕ) : ℚ) ^ p, ?_⟩
      have h := prod_real_embeddings_eq_absNorm (conePt (y j) (v j) m)
        (totPos_conePt (hy j).2 (fun i => (hv j i).2) m)
      simp only [← embedding_conePt]
      rw [Finset.prod_pow, h]
      push_cast
      rfl
    choose q hq using hq
    refine ⟨((Ideal.absNorm 𝔟 : ℚ) ^ p)⁻¹ * ∑ j, q j, ?_⟩
    simp only [hs, hq]
    rw [Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

