module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCompactEmbedded
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem normSq_pos {z : (Σ k, ι k) → ℂ} {k : K} (h : ∃ i, z ⟨k, i⟩ ≠ 0) :
    0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := h
  exact Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩

theorem proj_smul (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    proj (fun q => c q.1 * z q) = proj z := by
  funext q
  obtain ⟨k, i, j⟩ := q
  simp only [proj, norm_mul, mul_pow, ← Finset.mul_sum, map_mul]
  have h1 : ((‖c k‖ ^ 2 : ℝ) : ℂ) = c k * starRingEnd ℂ (c k) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : c k * starRingEnd ℂ (c k) ≠ 0 := mul_ne_zero (hc k) (by simpa using hc k)
  rw [Complex.ofReal_mul, h1, ← mul_div_mul_left (z ⟨k, i⟩ * starRingEnd ℂ (z ⟨k, j⟩)) _ h2]
  congr 1
  ring

theorem continuousOn_proj :
    ContinuousOn (proj (ι := ι)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  refine continuousOn_pi.2 fun q => ?_
  refine ContinuousOn.div₀ (by fun_prop) (by fun_prop) fun z hz => ?_
  exact Complex.ofReal_ne_zero.2 (normSq_pos (hz q.1)).ne'

theorem compactSpace_pts {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    CompactSpace (Pts P) := by
  let S : Set ((Σ k, ι k) → ℂ) := {z | (∀ k, ∑ i, ‖z ⟨k, i⟩‖ ^ 2 = 1) ∧ ∀ f ∈ P, eval z f = 0}
  have hne : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
    intro z hz k
    by_contra h
    push Not at h
    have := hz.1 k
    simp [h] at this
  have hS : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · simp only [S, Set.setOf_and, Set.setOf_forall]
      refine IsClosed.inter (isClosed_iInter fun k => isClosed_eq (by fun_prop) continuous_const)
        (isClosed_iInter fun f => isClosed_iInter fun _ =>
          isClosed_eq (MvPolynomial.continuous_eval f) continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : (Σ k, ι k) → ℂ)) (r := 1)).subset fun z hz => ?_
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      rintro ⟨k, i⟩
      have h1 : ‖z ⟨k, i⟩‖ ^ 2 ≤ 1 := by
        rw [← hz.1 k]
        exact Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2) (fun j _ => by positivity)
          (Finset.mem_univ i)
      nlinarith [norm_nonneg (z ⟨k, i⟩)]
  have hE : Pts P = proj '' S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := fun k => normSq_pos (hz.1 k)
      let c : K → ℂ := fun k => (((√(∑ i, ‖z ⟨k, i⟩‖ ^ 2))⁻¹ : ℝ) : ℂ)
      have hc : ∀ k, c k ≠ 0 := fun k =>
        Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 (hpos k)).ne')
      refine ⟨fun q => c q.1 * z q, ⟨fun k => ?_, eval_eq_zero_of_smul hP c z hz.2⟩, proj_smul c hc z⟩
      simp only [norm_mul, mul_pow, ← Finset.mul_sum, c, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        inv_pow]
      rw [Real.sq_sqrt (hpos k).le, inv_mul_cancel₀ (hpos k).ne']
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, ⟨hne z hz, hz.2⟩, rfl⟩
  rw [← isCompact_iff_compactSpace, hE]
  exact hS.image_of_continuousOn (continuousOn_proj.mono hne)

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

theorem mem_src_iff (p : (k : K) → ι k) (x : Pts P) :
    x ∈ src P p ↔ ∀ k, x.1 ⟨k, (p k, p k)⟩ ≠ 0 := by
  refine forall_congr' fun k => ?_
  have h : ((∑ i, ‖rep x ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (normSq_pos ((rep_mem x).1 k)).ne'
  rw [← proj_rep x]
  simp only [proj, ne_eq, div_eq_zero_iff, h, or_false, mul_eq_zero, map_eq_zero, or_self]

theorem isOpen_alt_bis (p : (k : K) → ι k) : IsOpen (src P p) := by
  have : src P p = ⋂ k, {x : Pts P | x.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
    ext x; simp [mem_src_iff]
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val) continuous_const

theorem affCoord_rep (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) (q : Σ k, ι k) :
    affCoord p (rep x) q = x.1 ⟨q.1, (q.2, p q.1)⟩ / x.1 ⟨q.1, (p q.1, p q.1)⟩ := by
  obtain ⟨k, i⟩ := q
  have h : ((∑ i, ‖rep x ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (normSq_pos ((rep_mem x).1 k)).ne'
  have h1 : rep x ⟨k, p k⟩ ≠ 0 := hx k
  have h2 : starRingEnd ℂ (rep x ⟨k, p k⟩) ≠ 0 := by simpa using h1
  rw [← proj_rep x]
  simp only [proj, affCoord]
  rw [div_div_div_cancel_right₀ h, mul_div_mul_right _ _ h2]

theorem proj_affCoord (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    proj (affCoord p (rep x)) = x.1 := by
  have hA : affCoord p (rep x) = fun q => (rep x ⟨q.1, p q.1⟩)⁻¹ * rep x q := by
    funext q; simp [affCoord, div_eq_inv_mul]
  rw [hA, proj_smul (fun k => (rep x ⟨k, p k⟩)⁻¹) (fun k => inv_ne_zero (hx k)), proj_rep]

theorem isEmbedding_affCoord (p : (k : K) → ι k) :
    Topology.IsEmbedding (fun x : src P p => affCoord p (rep x.1)) := by
  have hc : Continuous (fun x : src P p => affCoord p (rep x.1)) := by
    refine continuous_pi fun q => ?_
    simp only [affCoord_rep p _ (Subtype.prop _)]
    have hv : ∀ r : (Σ k, ι k × ι k), Continuous fun a : src P p => a.1.1 r := fun r =>
      (continuous_apply r).comp (continuous_subtype_val.comp continuous_subtype_val)
    exact Continuous.div (hv _) (hv _) fun x => (mem_src_iff p x.1).1 x.2 q.1
  let U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  have hU : ∀ x : src P p, affCoord p (rep x.1) ∈ U := fun x k =>
    ⟨p k, by simpa [affCoord] using x.2 k⟩
  let f : src P p → U := fun x => ⟨_, hU x⟩
  have hf : Continuous f := hc.subtype_mk _
  have hg : Continuous (U.restrict proj) := continuousOn_proj.restrict
  have hgf : U.restrict proj ∘ f = Subtype.val ∘ Subtype.val := by
    funext x; exact proj_affCoord p x.1 x.2
  have he : Topology.IsEmbedding f :=
    Topology.IsEmbedding.of_comp hf hg
      (hgf ▸ Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)
  exact Topology.IsEmbedding.subtypeVal.comp he

theorem isEmbedding_coord (p : (k : K) → ι k) :
    Topology.IsEmbedding (fun x : src P p => coord P p x) := by
  have h : Topology.IsEmbedding
      (fun y : (Σ k, ι k) → ℂ => (renPt y : Fin (Fintype.card (Σ k, ι k)) → ℂ)) :=
    Function.LeftInverse.isEmbedding (f := fun t => t ∘ Fintype.equivFin (Σ k, ι k))
      (fun y => by funext q; simp [renPt]) (by fun_prop) (by fun_prop)
  exact h.comp (isEmbedding_affCoord p)

theorem compact_open_embedding (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    CompactSpace (Pts P) ∧ ∀ p : (k : K) → ι k,
      IsOpen (src P p) ∧ Topology.IsEmbedding (fun x : src P p => coord P p x) :=
  ⟨compactSpace_pts hP, fun p => ⟨isOpen_alt_bis p, isEmbedding_coord p⟩⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCoverAndCone
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  simp only
  rw [inv_mul_cancel_left₀ (hc q.1)]

theorem sameOrbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  refine ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), ?_⟩
  funext q
  simp only
  ring

theorem proj_eq_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : proj z = proj z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext ⟨k, i, j⟩
  simp only [proj]
  have hN : (∑ l, ‖c k * z' ⟨k, l⟩‖ ^ 2 : ℝ) = ‖c k‖ ^ 2 * ∑ l, ‖z' ⟨k, l⟩‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [norm_mul, mul_pow]
  have hcc : c k * starRingEnd ℂ (c k) ≠ 0 :=
    mul_ne_zero (hc k) ((map_ne_zero _).2 (hc k))
  rw [hN, map_mul]
  push_cast
  rw [← Complex.mul_conj', show c k * z' ⟨k, i⟩ * (starRingEnd ℂ (c k) * starRingEnd ℂ (z' ⟨k, j⟩)) =
    (c k * starRingEnd ℂ (c k)) * (z' ⟨k, i⟩ * starRingEnd ℂ (z' ⟨k, j⟩)) by ring]
  exact mul_div_mul_left _ _ hcc

theorem blockNorm_ne_zero {z : (Σ k, ι k) → ℂ} {k : K} {j : ι k} (hj : z ⟨k, j⟩ ≠ 0) :
    ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
  have h1 : 0 < ‖z ⟨k, j⟩‖ ^ 2 := by positivity
  have h2 : ‖z ⟨k, j⟩‖ ^ 2 ≤ ∑ l, ‖z ⟨k, l⟩‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ‖z ⟨k, l⟩‖ ^ 2) (fun l _ => by positivity) (Finset.mem_univ j)
  exact Complex.ofReal_ne_zero.2 (lt_of_lt_of_le h1 h2).ne'

theorem sameOrbit_of_proj_eq {z z' : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : proj z = proj z') : SameOrbit z z' := by
  have key : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ ∀ i, z ⟨k, i⟩ = c * z' ⟨k, i⟩ := by
    intro k
    obtain ⟨j, hj⟩ := hz k
    obtain ⟨j', hj'⟩ := hz' k
    have hN := blockNorm_ne_zero hj
    have hN' := blockNorm_ne_zero hj'
    have hp : ∀ a b, z ⟨k, a⟩ * starRingEnd ℂ (z ⟨k, b⟩) / ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) =
        z' ⟨k, a⟩ * starRingEnd ℂ (z' ⟨k, b⟩) / ((∑ l, ‖z' ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) :=
      fun a b => congrFun h ⟨k, a, b⟩
    have hcj : starRingEnd ℂ (z ⟨k, j⟩) ≠ 0 := (map_ne_zero _).2 hj
    have hw : z' ⟨k, j⟩ ≠ 0 := by
      intro h0
      have := hp j j
      rw [h0, zero_mul, zero_div, div_eq_zero_iff] at this
      rcases this with h1 | h1
      · exact (mul_ne_zero hj hcj) h1
      · exact hN h1
    have hcw : starRingEnd ℂ (z' ⟨k, j⟩) ≠ 0 := (map_ne_zero _).2 hw
    refine ⟨starRingEnd ℂ (z' ⟨k, j⟩) * ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) /
      (((∑ l, ‖z' ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (z ⟨k, j⟩)),
      div_ne_zero (mul_ne_zero hcw hN) (mul_ne_zero hN' hcj), fun i => ?_⟩
    have := hp i j
    rw [div_eq_div_iff hN hN'] at this
    field_simp
    linear_combination this
  choose c hc hci using key
  exact ⟨c, hc, funext fun q => hci q.1 q.2⟩

theorem lift_vec {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k) (x : Pts P)
    (hx : x ∈ src P p) :
    (fun q => eval (coord P p x) (lift p q)) = affCoord p (rep x) :=
  funext (eval_lift p x hx)

theorem orbit_rep_lift {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k) (x : Pts P)
    (hx : x ∈ src P p) :
    SameOrbit (rep x) (fun q => eval (coord P p x) (lift p q)) := by
  rw [lift_vec p x hx]
  exact sameOrbit_affCoord p (rep x) hx

theorem lift_mem_conePts {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    (fun q => eval (coord P p x) (lift p q)) ∈ conePts P := by
  rw [lift_vec p x hx]
  exact (conePts_of_chartIdeal hP p _
    ((mem_conePts_iff_chartIdeal hP p (rep x) hx).1 (rep_mem x))).1

theorem isMultiHomogIdeal_sup {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : IsMultiHomogIdeal P) (hD : IsMultiHomogIdeal D) : IsMultiHomogIdeal (P ⊔ D) := by
  obtain ⟨S, hS, rfl⟩ := hP
  obtain ⟨T, hT, rfl⟩ := hD
  refine ⟨S ∪ T, ?_, (Ideal.span_union S T).symm⟩
  rintro f (hf | hf)
  · exact hS f hf
  · exact hT f hf

theorem zero_bd_iff {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hD : IsMultiHomogIdeal D) (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    (∀ h ∈ bd P D p, eval (coord P p x) h = 0) ↔
      (fun q => eval (coord P p x) (lift p q)) ∈ conePts D := by
  have hmem := lift_mem_conePts hP p x hx
  rw [lift_vec p x hx] at hmem ⊢
  have hone : ∀ k, affCoord p (rep x) ⟨k, p k⟩ = 1 := fun k => by
    simp [affCoord, hx k]
  constructor
  · intro h
    have hz : ∀ f ∈ chartIdeal (P ⊔ D) p, eval (affCoord p (rep x)) f = 0 := by
      intro f hf
      rw [← eval_renC]
      exact h _ (Ideal.le_radical (Ideal.mem_map_of_mem _ hf))
    have := (conePts_of_chartIdeal (isMultiHomogIdeal_sup hP hD) p _ hz).1
    exact ⟨this.1, fun f hf => this.2 f (Ideal.mem_sup_right hf)⟩
  · intro hDm g hg
    have hle : chartIdeal (P ⊔ D) p ≤ RingHom.ker (eval (affCoord p (rep x))) := by
      refine sup_le (sup_le (fun f hf => hmem.2 f hf) (fun f hf => hDm.2 f hf)) ?_
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show eval _ _ = 0
      simp [hone k]
    obtain ⟨n, hn⟩ := hg
    have h0 := renPt_zero (chartIdeal (P ⊔ D) p) (affCoord p (rep x)) (fun f hf => hle hf) _ hn
    rw [map_pow] at h0
    exact eq_zero_of_pow_eq_zero h0

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ReciprocityTheory.AnForm.R.IsMultiHomogIdeal D → (∀ x : SncRes.Pts P, ∃ p : (k : K) → ι k, x ∈ SncRes.src P p) ∧ (∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts P) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p ∩ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x) (SncRes.lift p' q))) ∧ (∀ z ∈ ReciprocityTheory.AnForm.R.conePts P, ∃ p : (k : K) → ι k, ∃ x ∈ SncRes.src P p, ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) z) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ x' ∈ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x') (SncRes.lift p' q)) → x = x') ∧ ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ((∀ h ∈ SncRes.bd P D p, eval (SncRes.coord P p x) h = 0) ↔ (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts D) := by
  intro K _ ι _ P D hP hD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart (rep x) (rep_mem x).1
    exact ⟨p, hp⟩
  · exact fun p x hx => SncRes.lift_mem_conePts hP p x hx
  · intro p p' x hx
    exact SncRes.sameOrbit_trans (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p x hx.1))
      (SncRes.orbit_rep_lift p' x hx.2)
  · intro z hz
    obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart z hz.1
    let x : SncRes.Pts P := ⟨SncRes.proj z, z, hz, rfl⟩
    have hrz : ReciprocityTheory.AnForm.R.SameOrbit (SncRes.rep x) z :=
      SncRes.sameOrbit_of_proj_eq (SncRes.rep_mem x).1 hz.1 (SncRes.proj_rep x)
    have hx : x ∈ SncRes.src P p := by
      obtain ⟨c, hc, he⟩ := hrz
      intro k
      rw [he]
      exact mul_ne_zero (hc k) (hp k)
    exact ⟨p, x, hx, SncRes.sameOrbit_trans
      (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p x hx)) hrz⟩
  · intro p p' x hx x' hx' h
    have h1 : ReciprocityTheory.AnForm.R.SameOrbit (SncRes.rep x) (SncRes.rep x') :=
      SncRes.sameOrbit_trans (SncRes.orbit_rep_lift p x hx)
        (SncRes.sameOrbit_trans h (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p' x' hx')))
    apply Subtype.ext
    rw [← SncRes.proj_rep x, ← SncRes.proj_rep x']
    exact SncRes.proj_eq_of_sameOrbit h1
  · exact fun p x hx => SncRes.zero_bd_iff hP hD p x hx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartContinuousProjection
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.SncProd

theorem compat_restr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (h : IsCompatChart A ψ) (V : Set X) (hV : IsOpen V) :
    IsCompatChart A (ψ.restrOpen V hV) := by
  intro j
  refine ⟨?_, ?_⟩
  · refine (h j).1.mono ?_
    rintro z ⟨hz, hs⟩
    refine ⟨hz, ?_⟩
    have : (A.chart j).symm z ∈ ψ.source ∩ V := by
      simpa [OpenPartialHomeomorph.restrOpen_source] using hs
    exact this.1
  · have hsymm : ((ψ.restrOpen V hV).symm : (Fin e → ℂ) → X) = ψ.symm := rfl
    rw [hsymm]
    refine (h j).2.mono ?_
    rintro z ⟨hz, hs⟩
    refine ⟨?_, hs⟩
    have h1 : ψ.symm z ∈ ψ.source ∩ V := by
      have := (ψ.restrOpen V hV).map_target hz
      rwa [OpenPartialHomeomorph.restrOpen_source] at this
    have h2 : ψ (ψ.symm z) = z := (ψ.restrOpen V hV).right_inv hz
    rw [← h2]
    exact ψ.map_source h1.1

theorem holoOn_comp {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (B : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A B pr) (S : Set Z) (g : Z → ℂ) (hg : B.HoloOn S g) :
    A.HoloOn (pr ⁻¹' S) (fun y => g (pr y)) := by
  rintro j z ⟨hzt, hzS⟩
  obtain ⟨k, hk⟩ := B.cover (pr ((A.chart j).symm z))
  have h1 : AnalyticAt ℂ (B.chart k ∘ pr ∘ (A.chart j).symm) z := hp.2 j k z ⟨hzt, hk⟩
  have h2 : AnalyticAt ℂ (g ∘ (B.chart k).symm) ((B.chart k ∘ pr ∘ (A.chart j).symm) z) := by
    refine hg k _ ⟨(B.chart k).map_source hk, ?_⟩
    have : (B.chart k).symm ((B.chart k) (pr ((A.chart j).symm z))) = pr ((A.chart j).symm z) :=
      (B.chart k).left_inv hk
    simpa [this] using hzS
  have h3 := h2.comp h1
  refine h3.congr ?_
  have hc : ContinuousAt (pr ∘ (A.chart j).symm) z :=
    hp.1.continuousAt.comp ((A.chart j).continuousAt_symm hzt)
  filter_upwards [hc.preimage_mem_nhds ((B.chart k).open_source.mem_nhds hk)] with w hw
  have : (B.chart k).symm ((B.chart k) (pr ((A.chart j).symm w))) = pr ((A.chart j).symm w) :=
    (B.chart k).left_inv hw
  simp [this]

theorem snoc_inj {r n e : ℕ} (σb : Fin r → Option (Fin n)) (s : Fin n ↪ Fin e) (i₀ : Fin e)
    (hne : ∀ i, s i ≠ i₀) (hσ : ∀ k k' i, σb k = some i → σb k' = some i → k = k') (k k' : Fin (r + 1)) (i : Fin e)
    (h : (Fin.snoc (α := fun _ => Option (Fin e)) (fun k => (σb k).map s) (some i₀) : Fin (r + 1) → Option (Fin e)) k = some i)
    (h' : (Fin.snoc (α := fun _ => Option (Fin e)) (fun k => (σb k).map s) (some i₀) : Fin (r + 1) → Option (Fin e)) k' = some i) :
    k = k' := by
  induction k using Fin.lastCases with
  | last =>
    induction k' using Fin.lastCases with
    | last => rfl
    | cast l =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Option.some.injEq] at h h'
      obtain ⟨b, -, hb⟩ := Option.map_eq_some_iff.1 h'
      exact absurd (hb.trans h.symm) (hne b)
  | cast l =>
    induction k' using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Option.some.injEq] at h h'
      obtain ⟨b, -, hb⟩ := Option.map_eq_some_iff.1 h
      exact absurd (hb.trans h'.symm) (hne b)
    | cast l' =>
      simp only [Fin.snoc_castSucc] at h h'
      obtain ⟨b, hb, hbi⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨b', hb', hbi'⟩ := Option.map_eq_some_iff.1 h'
      have : b = b' := s.injective (hbi.trans hbi'.symm)
      subst this
      rw [hσ l l' b hb hb']

theorem mul_rearrange (A B a b c : ℂ) (h : A = B) : a * A * (b * c) = a * b * (B * c) := by
  subst h
  ring

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (BM : BaseMetric M n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → BM.Rb.X) (hc : Continuous pr) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin BM.Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M BM.Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), HoloMap RW.A BM.Rb.A pr → ∀ c : ℝ, IsSNC RW.A (BM.L.pullback pr hc + secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (fun x y => BM.s (pr x) (pr y) * diagSec ψ i₀ u x y) (Fin.snoc BM.m 1) (Fin.snoc (fun k => pr ⁻¹' BM.W k) (diagSet k₀ RW)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e BM τ a k₀ ca cb RW pr hc ψ kb σ i₀ V u hL hp c x
  obtain ⟨⟨F, H, hW⟩, hVo, hxV, hVs, hVU, huh, hu0, hdiag, -⟩ := hL x
  obtain ⟨hcomp, -, hne, hbase, -, -⟩ := hW
  obtain ⟨ψb, hψbc, hxb, hψbU, σb, hσi, hσW, ub, hubh, hub0, hs⟩ := BM.snc (pr x)
  obtain ⟨ψ', hψ'c, hsrc, hk1, hk2⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap_keep e n RW.X BM.Rb.X RW.A BM.Rb.A pr (ψ x) (kb x) (σ x) ψb hcomp hψbc hbase
  have hsrc'' : (ψ'.restrOpen (V x) hVo).source = ψ'.source ∩ V x := ψ'.restrOpen_source (V x) hVo
  have hcoe : ∀ y, (ψ'.restrOpen (V x) hVo) y = ψ' y := fun y => rfl
  have hmem : ∀ y ∈ (ψ'.restrOpen (V x) hVo).source, y ∈ ψ'.source ∧ y ∈ V x ∧ pr y ∈ ψb.source := by
    intro y hy
    rw [hsrc''] at hy
    refine ⟨hy.1, hy.2, ?_⟩
    have := hy.1
    rw [hsrc] at this
    exact this.2
  refine ⟨ψ'.restrOpen (V x) hVo, compat_restr _ _ hψ'c _ hVo, ?_, ?_,
    Fin.snoc (α := fun _ => Option (Fin e)) (fun k => (σb k).map (σ x)) (some (i₀ x)),
    snoc_inj σb (σ x) (i₀ x) hne hσi, ?_, fun y => ub (pr y) * u x y, ?_, ?_, ?_⟩
  · rw [hsrc'', hsrc]
    exact ⟨⟨hVs hxV, hxb⟩, hxV⟩
  · intro y hy
    obtain ⟨-, hyV, hyb⟩ := hmem y hy
    exact ⟨hψbU hyb, hyV⟩
  · intro k
    induction k using Fin.lastCases with
    | last =>
      ext y
      simp only [Fin.snoc_last, Set.mem_inter_iff, Set.mem_setOf_eq, Option.some.injEq, exists_eq_left']
      constructor
      · rintro ⟨hd, hy⟩
        obtain ⟨hy', hyV, -⟩ := hmem y hy
        refine ⟨hy, ?_⟩
        rw [hcoe, hk2 y hy' _ hne]
        exact (hdiag y hyV).2 hd
      · rintro ⟨hy, h0⟩
        obtain ⟨hy', hyV, -⟩ := hmem y hy
        refine ⟨(hdiag y hyV).1 ?_, hy⟩
        rw [hcoe, hk2 y hy' _ hne] at h0
        exact h0
    | cast k =>
      ext y
      simp only [Fin.snoc_castSucc, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
      have hWk := Set.ext_iff.1 (hσW k) (pr y)
      constructor
      · rintro ⟨hw, hy⟩
        obtain ⟨hy', -, hyb⟩ := hmem y hy
        obtain ⟨-, i, hi, h0⟩ := hWk.1 ⟨hw, hyb⟩
        refine ⟨hy, σ x i, by rw [hi]; rfl, ?_⟩
        rw [hcoe, hk1 y hy']
        exact h0
      · rintro ⟨hy, i', hi', h0⟩
        obtain ⟨hy', -, hyb⟩ := hmem y hy
        obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hi'
        rw [hcoe, hk1 y hy'] at h0
        exact ⟨(hWk.2 ⟨hyb, i, hi, h0⟩).1, hy⟩
  · intro l z hz
    have h1 := holoOn_comp RW.A BM.Rb.A pr hp ψb.source ub hubh l z ⟨hz.1, (hmem _ hz.2).2.2⟩
    have h2 := huh l z ⟨hz.1, (hmem _ hz.2).2.1⟩
    exact h1.mul h2
  · intro y hy
    obtain ⟨-, hyV, hyb⟩ := hmem y hy
    exact mul_ne_zero (hub0 _ hyb) (hu0 _ hyV)
  · intro y hy
    obtain ⟨hy', hyV, hyb⟩ := hmem y hy
    have hi₀ : ψ' y (i₀ x) = ψ x y (i₀ x) := hk2 y hy' _ hne
    beta_reduce
    rw [Fin.prod_univ_castSucc, hs (pr y) hyb]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, pow_one, hcoe, diagSec, hi₀]
    refine mul_rearrange _ _ _ _ _ (Finset.prod_congr rfl fun k _ => ?_)
    cases h : σb k <;> simp [hk1 y hy']

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.SncProd
end
end

