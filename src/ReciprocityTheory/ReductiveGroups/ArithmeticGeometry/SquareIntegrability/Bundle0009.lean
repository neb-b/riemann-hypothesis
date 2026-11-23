module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0007

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfEqInner
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def VP {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Submodule ℂ (Vsp dim) where
  carrier := {v | InPart σ v}
  add_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c v hv j hj => by simp [hv j hj]


open scoped Classical in
open Classical in
def prj {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : Vsp dim :=
  WithLp.toLp 2 fun j => if j.1 = σ then v j else 0

def mulc {dim : (E →+* ℂ) → ℕ} (c : (E →+* ℂ) → ℂ) (v : Vsp dim) : Vsp dim :=
  WithLp.toLp 2 fun j => c j.1 * v j

theorem emb_sep {σ τ : E →+* ℂ} (h : σ ≠ τ) : ∃ α : 𝓞 E, σ (α : E) ≠ τ (α : E) := by
  by_contra hc
  push Not at hc
  apply h
  exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => hc x)

theorem mulc_mem {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim))
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (σ : E →+* ℂ) :
    ∀ v ∈ Submodule.span ℂ (I : Set (Vsp dim)), prj σ v ∈ Submodule.span ℂ (I : Set (Vsp dim)) := by
  classical
  set S := Submodule.span ℂ (I : Set (Vsp dim)) with hS

  have hact : ∀ (α : 𝓞 E), ∀ v ∈ S, act α v ∈ S := by
    intro α
    let A : Vsp dim →ₗ[ℂ] Vsp dim :=
      { toFun := act α
        map_add' := fun x y => by ext j; simp [act]; ring
        map_smul' := fun c x => by ext j; simp [act]; ring }
    have hle : S.map A ≤ S := by
      rw [hS, Submodule.map_span]
      apply Submodule.span_le.2
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.subset_span (hst α x hx)
    intro v hv
    exact hle ⟨v, hv, rfl⟩

  have hα : ∀ τ : E →+* ℂ, ∃ α : 𝓞 E, τ ≠ σ → σ (α : E) ≠ τ (α : E) := by
    intro τ
    by_cases h : τ = σ
    · exact ⟨0, fun h' => (h' h).elim⟩
    · obtain ⟨α, hα⟩ := emb_sep (Ne.symm h)
      exact ⟨α, fun _ => hα⟩
  choose α hα using hα
  let c : (E →+* ℂ) → (E →+* ℂ) → ℂ := fun τ τ' =>
    (τ' (α τ : E) - τ (α τ : E)) * (σ (α τ : E) - τ (α τ : E))⁻¹
  have hstep : ∀ τ, ∀ v ∈ S, mulc (c τ) v ∈ S := by
    intro τ v hv
    have : mulc (c τ) v = (σ (α τ : E) - τ (α τ : E))⁻¹ • (act (α τ) v - (τ (α τ : E)) • v) := by
      ext j; simp [mulc, act, c]; ring
    rw [this]
    exact S.smul_mem _ (S.sub_mem (hact _ v hv) (S.smul_mem _ hv))
  have hprod : ∀ T : Finset (E →+* ℂ), ∀ v ∈ S, mulc (fun τ' => ∏ τ ∈ T, c τ τ') v ∈ S := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro v hv
      have : mulc (fun τ' => ∏ τ ∈ (∅ : Finset (E →+* ℂ)), c τ τ') v = v := by ext j; simp [mulc]
      rw [this]; exact hv
    | insert τ T hτ ih =>
      intro v hv
      have : mulc (fun τ' => ∏ t ∈ insert τ T, c t τ') v = mulc (c τ) (mulc (fun τ' => ∏ t ∈ T, c t τ') v) := by
        ext j; simp [mulc, Finset.prod_insert hτ]; ring
      rw [this]
      exact hstep τ _ (ih v hv)
  intro v hv
  have : prj σ v = mulc (fun τ' => ∏ τ ∈ Finset.univ.erase σ, c τ τ') v := by
    ext j
    simp only [prj, mulc, PiLp.toLp_apply]
    by_cases hj : j.1 = σ
    · rw [if_pos hj, hj, Finset.prod_eq_one, one_mul]
      intro τ hτ
      have hne := hα τ (Finset.ne_of_mem_erase hτ)
      simp only [c]
      exact mul_inv_cancel₀ (sub_ne_zero.2 hne)
    · rw [if_neg hj, Finset.prod_eq_zero (i := j.1) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩), zero_mul]
      simp [c]
  rw [this]
  exact hprod _ v hv

theorem Hf_prj {dim : (E →+* ℂ) → ℕ} {σ : E →+* ℂ} {ξ : Vsp dim} (hξ : InPart σ ξ) (a : Vsp dim) :
    Hf ξ a = Hf ξ (prj σ a) := by
  unfold Hf
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [prj, PiLp.toLp_apply]
  by_cases hj : j.1 = σ
  · rw [if_pos hj]
  · rw [if_neg hj, hξ j hj]; simp

theorem Hf_eq_inner' {ι : Type} [Fintype ι] (w v : EuclideanSpace ℂ ι) : Hf w v = inner ℂ v w :=
  lemS_Hf_eq_inner w v

theorem prj_inpart {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (a : Vsp dim) : InPart σ (prj σ a) := by
  intro j hj; simp [prj, hj]

theorem onb_data (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (σ : E →+* ℂ) (ρ : ℕ)
    (hρ : Module.finrank ℂ (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) = ρ)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (w : Fin ρ → Vsp X.dim) (hw : ∀ s, InPart σ (w s) ∧ w s ∈ Submodule.span ℂ (I : Set (Vsp X.dim)))
    (hon : ∀ s s', Hf (w s) (w s') = if s = s' then 1 else 0) :
    ∃ (N : ℕ) (b : Fin N → Vsp X.dim), N ≤ X.r ∧ ρ ≤ N ∧
      (∀ k (h : k.val < ρ), b k = w ⟨k, h⟩) ∧
      (∀ k, InPart σ (b k)) ∧
      (∀ k, ρ ≤ k.val → ‖b k‖ = 1 ∧ ∀ a ∈ I, Hf (b k) a = 0) ∧
      (∀ x y : Vsp X.dim, InPart σ x → InPart σ y → ∑ k, Hf x (b k) * Hf (b k) y = Hf x y) := by
  classical
  set N := Module.finrank ℂ (VP (dim := X.dim) σ) with hN
  have hw_inner : ∀ s s', inner ℂ (w s) (w s') = if s = s' then (1 : ℂ) else 0 := by
    intro s s'
    rw [← Hf_eq_inner', hon s' s]
    by_cases h : s = s' <;> simp [h, eq_comm]
  have hwo : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]; exact hw_inner
  have hρN : ρ ≤ N := hρ ▸ Submodule.finrank_mono inf_le_right
  have hNr : N ≤ X.r := by
    let f : VP (dim := X.dim) σ →ₗ[ℂ] (Fin (X.dim σ) → ℂ) :=
      { toFun := fun v a => (v : Vsp X.dim) ⟨σ, a⟩
        map_add' := fun x y => by funext a; simp
        map_smul' := fun c x => by funext a; simp }
    have hinj : Function.Injective f := by
      intro v v' h
      apply Subtype.ext
      ext j
      obtain ⟨τ, a⟩ := j
      by_cases hτ : τ = σ
      · subst hτ; exact congrFun h a
      · rw [(v.2 : InPart σ (v : Vsp X.dim)) ⟨τ, a⟩ hτ, (v'.2 : InPart σ (v' : Vsp X.dim)) ⟨τ, a⟩ hτ]
    have h1 := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun] at h1
    have h2 := X.dim_conj σ
    omega
  let vv : Fin N → VP (dim := X.dim) σ := fun k =>
    if h : k.val < ρ then ⟨w ⟨k, h⟩, (hw _).1⟩ else 0
  have hon' : Orthonormal ℂ (Set.domRestrict {k : Fin N | k.val < ρ} vv) := by
    rw [orthonormal_iff_ite]
    rintro ⟨k, hk⟩ ⟨k', hk'⟩
    have hk0 : k.val < ρ := hk
    have hk0' : k'.val < ρ := hk'
    show inner ℂ (vv k) (vv k') = if (⟨k, hk⟩ : {k : Fin N | k.val < ρ}) = ⟨k', hk'⟩ then 1 else 0
    simp only [vv, dif_pos hk0, dif_pos hk0', Submodule.coe_inner, hw_inner]
    simp [Fin.ext_iff, Subtype.ext_iff]
  obtain ⟨bb, hbb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := VP (dim := X.dim) σ) (ι := Fin N) (by simp [hN]) hon'
  have hbw : ∀ k (h : k.val < ρ), (bb k : Vsp X.dim) = w ⟨k, h⟩ := by
    intro k h
    rw [hbb k h]
    simp [vv, h]
  refine ⟨N, fun k => (bb k : Vsp X.dim), hNr, hρN, hbw, fun k => (bb k).2, ?_, ?_⟩
  · intro k hk
    constructor
    · exact bb.orthonormal.1 k
    · intro a ha
      rw [Hf_prj ((bb k).2 : InPart σ (bb k : Vsp X.dim)) a]
      have hpa : prj σ a ∈ (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) :=
        ⟨mulc_mem I hst σ a (Submodule.subset_span ha), prj_inpart σ a⟩
      have hspan : Submodule.span ℂ (Set.range w) =
          (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) := by
        apply Submodule.eq_of_le_of_finrank_eq
        · rw [Submodule.span_le]; rintro _ ⟨s, rfl⟩; exact ⟨(hw s).2, (hw s).1⟩
        · rw [finrank_span_eq_card hwo.linearIndependent, Fintype.card_fin, hρ]
      rw [← hspan] at hpa
      rw [Hf_eq_inner']
      refine Submodule.span_induction (p := fun z _ => inner ℂ z (bb k : Vsp X.dim) = 0) ?_ ?_ ?_ ?_ hpa
      · rintro _ ⟨s, rfl⟩
        have hs : (⟨s.val, lt_of_lt_of_le s.2 hρN⟩ : Fin N).val < ρ := s.2
        have e1 : w s = (bb ⟨s.val, lt_of_lt_of_le s.2 hρN⟩ : Vsp X.dim) := by
          rw [hbw _ hs]
        rw [e1, ← Submodule.coe_inner]
        refine bb.orthonormal.2 ?_
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      · simp
      · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
      · intro c x _ hx; rw [inner_smul_left, hx, mul_zero]
  · intro x y hx hy
    have := bb.sum_inner_mul_inner (⟨y, hy⟩ : VP (dim := X.dim) σ) ⟨x, hx⟩
    simp only [Submodule.coe_inner] at this
    rw [Hf_eq_inner', ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Hf_eq_inner', Hf_eq_inner', mul_comm]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

theorem contDiff_of_diff {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {f : W → ℂ} (hf : Differentiable ℂ f) : ContDiff ℂ (⊤ : ℕ∞) f := by
  let e := (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  have h1 : Differentiable ℂ (f ∘ e.symm) := by
    first
    | exact hf.comp e.symm.differentiable
    | exact hf.comp (e.symm.contDiff.differentiable (by simp))
  have h3 := (contDiff_of_differentiable h1 (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp e.contDiff
  convert h3 using 1
  funext v; simp

theorem jof_Hf_self_re {ι : Type} [Fintype ι] (x : EuclideanSpace ℂ ι) : (Hf x x).re = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq x, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Hf, Complex.re_sum, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
  | rw [← Complex.ofReal_pow, Complex.ofReal_re]
  | norm_cast
  | simp [sq]

variable {E : Type} [Field E] [NumberField E] (X : PT E)

def tens {n : ℕ} (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ) : (Fin n → Vsp X.dim) → ℂ :=
  fun v => ∏ k, s k (fun _ => v k)

theorem sec_contDiff {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q n) :
    ContDiff ℂ (⊤ : ℕ∞) F := by
  exact contDiff_of_diff (show Differentiable ℂ F ∧ _ from hF).1

theorem tens_mem {n q : ℕ} {s : Fin n → (Fin 1 → Vsp X.dim) → ℂ} (hs : ∀ k, s k ∈ X.Sec q 1) :
    tens X s ∈ X.Sec q n := by
  have hd : ∀ k, Differentiable ℂ (s k) := fun k => (show Differentiable ℂ (s k) ∧ _ from hs k).1
  show _ ∧ _
  refine ⟨?_, fun γ hγ v => ?_⟩
  · show Differentiable ℂ (fun v : Fin n → Vsp X.dim => ∏ k, s k (fun _ => v k))
    first
    | exact Differentiable.finset_prod (fun k _ => (hd k).comp (differentiable_pi.mpr fun _ => differentiable_apply k))
    | fun_prop
  · have he : ∀ k, s k (fun _ => (v + γ) k) = ((X.eps (γ k) : ℂ)) ^ q *
        cexp (q * Real.pi * Hf (v k) (γ k) + q * Real.pi * Hf (γ k) (γ k) / 2) * s k (fun _ => v k) := by
      intro k
      have := (show Differentiable ℂ (s k) ∧ ∀ γ' : Fin 1 → Vsp X.dim, (∀ j, γ' j ∈ X.L) →
        ∀ w, s k (w + γ') = (∏ j, (X.eps (γ' j) : ℂ)) ^ q *
          cexp (q * Real.pi * HC w γ' + q * Real.pi * HC γ' γ' / 2) * s k w from hs k).2
        (fun _ => γ k) (fun _ => hγ k) (fun _ => v k)
      simpa [HC, Pi.add_def] using this
    have hsum : ∑ k, ((q : ℂ) * Real.pi * Hf (v k) (γ k) + q * Real.pi * Hf (γ k) (γ k) / 2) =
        q * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2 := by
      simp only [HC, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
    show ∏ k, s k (fun _ => (v + γ) k) = (∏ k, (X.eps (γ k) : ℂ)) ^ q *
      cexp (q * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2) * ∏ k, s k (fun _ => v k)
    rw [Finset.prod_congr rfl fun k _ => he k, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow, ← Complex.exp_sum, hsum]

theorem pointNormSq_tensor {n : ℕ} (q : ℕ) (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ) (v : Fin n → Vsp X.dim) :
    X.ptN2 q (tens X s) v = ∏ k, X.ptN2 q (s k) (fun _ => v k) := by
  have hHC : (HC v v).re = ∑ k, (HC (fun _ : Fin 1 => v k) (fun _ => v k)).re := by
    simp [HC, Complex.re_sum]
  simp only [PT.ptN2, tens]
  rw [norm_prod, ← Finset.prod_pow, hHC, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]

theorem avg_fd_prod {n : ℕ} (f : Fin n → Vsp X.dim → ℝ) :
    ⨍ v in X.fd n, ∏ k, f k (v k) = ∏ k, ⨍ x in ZSpan.fundamentalDomain X.b, f k x := by
  have hfd : X.fd n = Set.univ.pi (fun _ : Fin n => ZSpan.fundamentalDomain X.b) := by
    ext v; simp [PT.fd]
  rw [hfd]
  simp only [MeasureTheory.setAverage_eq, smul_eq_mul]
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
  simp only [MeasureTheory.measureReal_def]
  rw [MeasureTheory.Measure.pi_pi, ENNReal.toReal_prod, ← Finset.prod_inv_distrib]
  first
  | rw [MeasureTheory.integral_fintype_prod_eq_prod, ← Finset.prod_mul_distrib]
  | rw [MeasureTheory.integral_fintype_prod_eq_prod (μ := fun _ => _), ← Finset.prod_mul_distrib]

theorem l2_norm_fundamental_domain (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    X.l2 q s = ⨍ x in ZSpan.fundamentalDomain X.b, X.ptN2 q s (fun _ => x) := by
  have hv : ∀ v : Fin 1 → Vsp X.dim, (fun _ : Fin 1 => v 0) = v :=
    fun v => funext fun k => by rw [Subsingleton.elim k 0]
  have h := avg_fd_prod X (n := 1) (fun _ x => X.ptN2 q s (fun _ => x))
  simp only [Fin.prod_univ_one, hv] at h
  exact h

theorem l2_tens_eq_prod {n : ℕ} (q : ℕ) (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ) :
    X.l2 q (tens X s) = ∏ k, X.l2 q (s k) := by
  rw [Finset.prod_congr rfl fun k _ => l2_norm_fundamental_domain X q (s k)]
  rw [PT.l2]
  simp_rw [pointNormSq_tensor X q s]
  exact avg_fd_prod X (fun k x => X.ptN2 q (s k) (fun _ => x))

theorem l2_smul {n : ℕ} (q : ℕ) (c : ℂ) (F : (Fin n → Vsp X.dim) → ℂ) :
    X.l2 q (c • F) = ‖c‖ ^ 2 * X.l2 q F := by
  have h : ∀ v, X.ptN2 q (c • F) v = ‖c‖ ^ 2 * X.ptN2 q F v := by
    intro v
    simp only [PT.ptN2, Pi.smul_apply, smul_eq_mul, norm_mul]
    ring
  simp only [PT.l2, h]
  first
  | exact MeasureTheory.integral_const_mul _ _
  | exact MeasureTheory.integral_mul_left _ _
  | simp [MeasureTheory.average, MeasureTheory.integral_const_mul]

def gtOf (q : ℕ) : GT (Idx X.dim) where
  b := X.b
  integral := X.integral
  perfect := X.perfect
  ka := fun γ => (X.eps γ : ℂ) ^ q
  ka_abs := fun x hx => by rcases X.eps_pm x hx with h | h <;> simp [h]

theorem eq_zero_of_l2_eq_zero (hP : Ext.PackingCount) {q : ℕ} (hq : 1 ≤ q) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec q 1) (h0 : X.l2 q s = 0) : s = 0 := by
  have hd : Differentiable ℂ s := (show Differentiable ℂ s ∧ _ from hs).1
  set g : Vsp X.dim → ℂ := fun z => s (fun _ => z) with hgdef
  have hgc : Continuous g := (hd.comp (differentiable_pi.mpr fun _ => differentiable_id)).continuous
  have hq' : ∀ γ ∈ X.L, ∀ x, g (x + γ) = ((X.eps γ : ℂ)) ^ q *
      cexp (q * Real.pi * Hf x γ + q * Real.pi * Hf γ γ / 2) * g x := by
    intro γ hγ x
    have := (show Differentiable ℂ s ∧ ∀ γ' : Fin 1 → Vsp X.dim, (∀ j, γ' j ∈ X.L) →
        ∀ w, s (w + γ') = (∏ j, (X.eps (γ' j) : ℂ)) ^ q *
          cexp (q * Real.pi * HC w γ' + q * Real.pi * HC γ' γ' / 2) * s w from hs).2
      (fun _ => γ) (fun _ => hγ) (fun _ => x)
    simpa [HC, Pi.add_def, hgdef] using this
  have hne : ∀ γ ∈ X.L, ∀ x, g (x + γ) = 0 ↔ g x = 0 := by
    intro γ hγ x
    rw [hq' γ hγ x]
    have h1 : (X.eps γ : ℂ) ≠ 0 := by rcases X.eps_pm γ hγ with h | h <;> simp [h]
    simp [h1, Complex.exp_ne_zero]
  have hpx : ∀ x, X.ptN2 q s (fun _ => x) = ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2) := by
    intro x
    have hre : (HC (fun _ : Fin 1 => x) (fun _ => x)).re = ‖x‖ ^ 2 := by simp [HC, jof_Hf_self_re]
    simp only [PT.ptN2, hre, hgdef]
  have hl := l2_norm_fundamental_domain X q s
  rw [h0] at hl
  simp only [hpx] at hl
  set D := ZSpan.fundamentalDomain X.b with hD
  have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet X.b
  have hDb : Bornology.IsBounded D := ZSpan.fundamentalDomain_isBounded X.b
  haveI : MeasureTheory.VAddInvariantMeasure (Submodule.span ℤ (Set.range X.b)) (Vsp X.dim)
      MeasureTheory.volume :=
    ⟨fun c s _ => by
      simpa [Submodule.vadd_def, vadd_eq_add] using
        MeasureTheory.measure_preimage_add MeasureTheory.volume (c : Vsp X.dim) s⟩
  have hfd := ZSpan.isAddFundamentalDomain X.b (MeasureTheory.volume : MeasureTheory.Measure (Vsp X.dim))
  have hD0 : MeasureTheory.volume D ≠ 0 := hfd.measure_ne_zero (NeZero.ne _)
  have hDt : MeasureTheory.volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hcont : Continuous fun x : Vsp X.dim => ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2) := by
    first
    | fun_prop
    | exact ((continuous_norm.comp hgc).pow 2).mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hint : MeasureTheory.IntegrableOn
      (fun x : Vsp X.dim => ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2)) D :=
    (hcont.continuousOn.integrableOn_compact hDb.isCompact_closure).mono_set subset_closure
  rw [MeasureTheory.setAverage_eq, smul_eq_mul] at hl
  have hI : ∫ x in D, ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2) = 0 := by
    have hr : MeasureTheory.volume.real D ≠ 0 := by
      rw [MeasureTheory.measureReal_def]
      exact ENNReal.toReal_ne_zero.mpr ⟨hD0, hDt⟩
    rcases mul_eq_zero.mp hl.symm with h | h
    · exact absurd (inv_eq_zero.mp h) hr
    · exact h
  have hae := (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae
    (MeasureTheory.ae_of_all _ fun x => by show (0:ℝ) ≤ _; positivity) hint).mp hI
  have h2 : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Vsp X.dim)), x ∈ D → g x = 0 := by
    rw [← MeasureTheory.ae_restrict_iff' hDm]
    filter_upwards [hae] with x hx
    simpa [Real.exp_ne_zero] using hx
  rw [MeasureTheory.ae_iff] at h2
  have hset : {x | ¬(x ∈ D → g x = 0)} = {x | g x ≠ 0} ∩ D := by
    ext x; simp [and_comm]
  rw [hset] at h2
  open Pointwise in
  have hinv : ∀ γ : Submodule.span ℤ (Set.range X.b), γ +ᵥ {x | g x ≠ 0} = {x | g x ≠ 0} := by
    intro γ
    ext y
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [Set.mem_setOf_eq]
    have e : (-γ) +ᵥ y = y + -(γ : Vsp X.dim) := by
      first
      | (rw [Submodule.vadd_def, add_comm]; rfl)
      | simp [Submodule.vadd_def, add_comm]
      | (show ((-γ : Submodule.span ℤ (Set.range X.b)) : Vsp X.dim) + y = _; simp [add_comm])
    rw [e]
    exact not_congr (hne _ (neg_mem γ.2) y)
  have ht0 := hfd.measure_zero_of_invariant {x | g x ≠ 0} hinv h2
  have hopen : IsOpen {x | g x ≠ 0} := isOpen_ne_fun hgc continuous_const
  have hempty : {x | g x ≠ 0} = ∅ := (hopen.measure_eq_zero_iff MeasureTheory.volume).mp ht0
  funext v
  show s v = 0
  have hv : v = fun _ => v 0 := funext fun k => by rw [Subsingleton.elim k 0]
  have hz : g (v 0) = 0 := by
    by_contra hc
    have hm : v 0 ∈ ({x | g x ≠ 0} : Set (Vsp X.dim)) := hc
    rw [hempty] at hm
    exact hm
  rw [hv]
  exact hz

theorem polyDeriv_zero_fun {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (x : W) : polyDeriv P u (0 : W → ℂ) x = 0 := by
  simp [polyDeriv, Pi.zero_def]

theorem polyDeriv_smul_fun {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (c : ℂ) (x : W) :
    polyDeriv P u (c • F) x = c * polyDeriv P u F x := by
  unfold polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  first
  | rw [iteratedFDeriv_const_smul_apply ((hF.of_le (by exact_mod_cast le_top)).contDiffAt)]
  | rw [iteratedFDeriv_const_smul_apply (hF.of_le (by exact_mod_cast le_top))]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

end

end ReciprocityTheory.ChartRestriction.G.I2
end

