module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0001
public import ReciprocityTheory.SemistableReduction.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EventuallyComparable
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate ComplexOrder

namespace GlobalTheory.MajorantContinuity

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
lemma hermC_smul_l {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (u v : Fin r → ℂ) :
    hermC τ G (a • u) v = a * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

omit [NumberField E] [IsCMField E] in
lemma hermC_smul_r {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (a • v) = conj a * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma scale_lemma {n : ℕ} (s : ℝ) (A B : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, (s : ℂ) * A a * M a b * ((s : ℂ) * B b) = ((s ^ 2 : ℝ) : ℂ) * ∑ a, ∑ b, A a * M a b * B b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

lemma maj_real_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (t : ℝ) (v : Fin r → ℂ) :
    X.maj x τ ((t : ℂ) • v) = t ^ 2 * X.maj x τ v := by
  have hc : conj (t : ℂ) = t := Complex.conj_ofReal t
  have e2 : hermC τ.1 X.Gm ((t : ℂ) • v) ((t : ℂ) • v) = ((t ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hermC_smul_l, hermC_smul_r, hc]; push_cast; ring
  unfold Data.maj Data.posPart
  rw [e2]
  simp_rw [hermC_smul_l (a := (t : ℂ)) (u := v), map_mul, hc]
  rw [scale_lemma, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

lemma continuousAt_maj {r : ℕ} (X : Data E r) (τ : X.Ψ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (v : Fin r → ℂ) :
    ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2) (x, v) := by
  have hH : ∀ f g : Frame X.Ψ r × (Fin r → ℂ) → (Fin r → ℂ), Continuous f → Continuous g →
      Continuous fun p => hermC τ.1 X.Gm (f p) (g p) := by
    intro f g hf hg
    unfold hermC
    have hf' : ∀ a, Continuous fun p => f p a := fun a => (continuous_apply a).comp hf
    have hg' : ∀ b, Continuous fun p => g p b := fun b => (continuous_apply b).comp hg
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((hf' a).mul continuous_const).mul (Complex.continuous_conj.comp (hg' b))
  have hcol : ∀ k : Fin r, Continuous fun p : Frame X.Ψ r × (Fin r → ℂ) => col (mat p.1 τ) k := by
    intro k
    change Continuous fun p : Frame X.Ψ r × (Fin r → ℂ) => fun i => p.1 τ i k
    exact continuous_pi fun i => (continuous_apply k).comp ((continuous_apply i).comp
      ((continuous_apply τ).comp continuous_fst))
  have hG : Continuous fun y : Frame X.Ψ r => X.gramPos y τ := by
    unfold Data.gramPos
    exact (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.cont_gram X τ).matrix_submatrix _ _
  have hdet : (X.gramPos x τ).det ≠ 0 := (X.gramPos_posDef hx τ).det_pos.ne'
  have hI : ContinuousAt (fun y : Frame X.Ψ r => (X.gramPos y τ)⁻¹) x := by
    refine (continuousAt_matrix_inv _ ?_).comp hG.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hIab : ∀ a b : Fin X.p0,
      ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => (X.gramPos p.1 τ)⁻¹ a b) (x, v) :=
    fun a b => by
      have hI' : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => (X.gramPos p.1 τ)⁻¹) (x, v) :=
        ContinuousAt.comp (g := fun y : Frame X.Ψ r => (X.gramPos y τ)⁻¹) (f := Prod.fst) hI
          continuous_fst.continuousAt
      exact ContinuousAt.comp (g := fun M : Matrix (Fin X.p0) (Fin X.p0) ℂ => M a b)
        (continuous_id.matrix_elem a b).continuousAt hI'
  unfold Data.maj Data.posPart
  refine ContinuousAt.sub (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp ?_))
    (Complex.continuous_re.comp (hH _ _ continuous_snd continuous_snd)).continuousAt
  refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
  exact (((hH _ _ continuous_snd (hcol _)).continuousAt.mul (hIab a b)).mul
    (Complex.continuous_conj.comp (hH _ _ continuous_snd (hcol _))).continuousAt)

lemma exists_sphere {r : ℕ} {v : Fin r → ℂ} (hv : v ≠ 0) :
    ∃ w ∈ Metric.sphere (0 : Fin r → ℂ) 1, v = ((‖v‖ : ℝ) : ℂ) • w := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  refine ⟨((‖v‖ : ℝ) : ℂ)⁻¹ • v, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_norm, inv_mul_cancel₀ hn]
  · rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hn), one_smul]

lemma maj_at_zero {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  simp [Data.maj, Data.posPart, hermC]

lemma ne_zero_of_sphere {r : ℕ} {w : Fin r → ℂ} (hw : w ∈ Metric.sphere (0 : Fin r → ℂ) 1) :
    w ≠ 0 := by
  rintro rfl
  rw [mem_sphere_zero_iff_norm, norm_zero] at hw
  exact zero_ne_one hw

theorem eventually_comparable {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v := by
  have hdom : ∀ᶠ y in 𝓝 x, y ∈ X.dom := (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X).mem_nhds hx
  have key : ∀ τ : X.Ψ, ∀ᶠ y in 𝓝 x, ∀ w ∈ Metric.sphere (0 : Fin r → ℂ) 1,
      X.maj x τ w < (1 + ε) * X.maj y τ w ∧ X.maj y τ w < (1 + ε) * X.maj x τ w := by
    intro τ
    refine (isCompact_sphere (0 : Fin r → ℂ) 1).eventually_forall_of_forall_eventually ?_
    intro w hw
    have hpos : 0 < X.maj x τ w := X.maj_pos hx τ (ne_zero_of_sphere hw)
    have h1 : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2) (x, w) :=
      continuousAt_maj X τ hx w
    have h2 : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj x τ p.2) (x, w) :=
      ContinuousAt.comp_of_eq (g := fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2)
        (f := fun p : Frame X.Ψ r × (Fin r → ℂ) => (x, p.2)) h1
        (continuous_const.prodMk continuous_snd).continuousAt rfl
    refine (h2.eventually_lt (continuousAt_const.mul h1) ?_).and
      (h1.eventually_lt (continuousAt_const.mul h2) ?_)
    · show X.maj x τ w < (1 + ε) * X.maj x τ w
      nlinarith
    · show X.maj x τ w < (1 + ε) * X.maj x τ w
      nlinarith
  filter_upwards [hdom, Filter.eventually_all.2 key] with y hy hk
  refine ⟨hy, fun τ v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp [maj_at_zero]
  obtain ⟨w, hw, hvw⟩ := exists_sphere hv
  have hx' : X.maj x τ v = ‖v‖ ^ 2 * X.maj x τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X x τ _ w
  have hy' : X.maj y τ v = ‖v‖ ^ 2 * X.maj y τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X y τ _ w
  obtain ⟨k1, k2⟩ := hk τ w hw
  have ht : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  rw [hx', hy']
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left k1.le ht]
  · nlinarith [mul_le_mul_of_nonneg_left k2.le ht]

theorem compact_bounds {r : ℕ} (X : Data E r) {K : Set (Frame X.Ψ r)} (hK : IsCompact K)
    (hKd : K ⊆ X.dom) : ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2 := by
  classical
  have hKS := hK.prod (isCompact_sphere (0 : Fin r → ℂ) 1)
  have hcont : ∀ τ : X.Ψ, ContinuousOn (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2)
      (K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1) :=
    fun τ => continuousOn_of_forall_continuousAt fun p hp => continuousAt_maj X τ (hKd hp.1) p.2
  have hlow : ∀ τ : X.Ψ, ∃ c', 0 < c' ∧ ∀ p ∈ K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1,
      c' ≤ X.maj p.1 τ p.2 :=
    fun τ => hKS.exists_forall_le' (hcont τ) fun p hp => X.maj_pos (hKd hp.1) τ (ne_zero_of_sphere hp.2)
  have hup : ∀ τ : X.Ψ, ∃ C', ∀ p ∈ K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1, ‖X.maj p.1 τ p.2‖ ≤ C' :=
    fun τ => hKS.exists_bound_of_continuousOn (hcont τ)
  choose cτ hcpos hcle using hlow
  choose Cτ hCle using hup
  have hsum : 0 ≤ ∑ σ, (cτ σ)⁻¹ := Finset.sum_nonneg fun σ _ => (inv_pos.2 (hcpos σ)).le
  refine ⟨(1 + ∑ σ, (cτ σ)⁻¹)⁻¹, ∑ σ, |Cτ σ|, inv_pos.2 (by linarith), ?_⟩
  intro x hx τ v
  have hc_le : (1 + ∑ σ, (cτ σ)⁻¹)⁻¹ ≤ cτ τ := by
    have h1 : (cτ τ)⁻¹ ≤ ∑ σ, (cτ σ)⁻¹ :=
      Finset.single_le_sum (f := fun σ => (cτ σ)⁻¹) (fun σ _ => (inv_pos.2 (hcpos σ)).le)
        (Finset.mem_univ τ)
    rw [inv_le_comm₀ (by linarith) (hcpos τ)]
    linarith
  have hC_le : Cτ τ ≤ ∑ σ, |Cτ σ| :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun σ => |Cτ σ|) (fun σ _ => abs_nonneg _)
      (Finset.mem_univ τ))
  rcases eq_or_ne v 0 with rfl | hv
  · simp [maj_at_zero]
  obtain ⟨w, hw, hvw⟩ := exists_sphere hv
  have hm : X.maj x τ v = ‖v‖ ^ 2 * X.maj x τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X x τ _ w
  have hlo : cτ τ ≤ X.maj x τ w := hcle τ (x, w) ⟨hx, hw⟩
  have hhi : X.maj x τ w ≤ Cτ τ := (le_abs_self _).trans
    ((Real.norm_eq_abs _).symm.trans_le (hCle τ (x, w) ⟨hx, hw⟩))
  have ht : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  rw [hm]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (hc_le.trans hlo) ht]
  · nlinarith [mul_le_mul_of_nonneg_left (hhi.trans hC_le) ht]

theorem majorant_continuity :
    ((∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v) ∧ (∀ (r : ℕ) (X : Data E r) (K : Set (Frame X.Ψ r)), IsCompact K → K ⊆ X.dom → ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ), c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2)) := ⟨fun _ X _ hx _ hε => eventually_comparable X hx hε,
    fun _ X _ hK hKd => compact_bounds X hK hKd⟩

end GlobalTheory.MajorantContinuity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LatFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [IsCMField E] in
theorem exists_int_mul_integral (x : E) : ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ ((k : E) * x) := by
  have h : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨k, hk, hi⟩ := h.exists_integral_multiple
  exact ⟨k, hk, by simpa [zsmul_eq_mul] using hi⟩


omit [IsCMField E] in
theorem finite_bounded (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (k : ℤ) (hk : k ≠ 0) (R : ℝ) :
    {x : E | IsIntegral ℤ ((k : E) * x) ∧ ∀ τ : Ψ, ‖τ.1 x‖ ≤ R}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ (‖(k : ℂ)‖ * R)
  have hk' : (k : E) ≠ 0 := Int.cast_ne_zero.2 hk
  refine Set.Finite.of_finite_image (f := fun x => (k : E) * x) (hfin.subset ?_)
    (fun x _ y _ h => mul_left_cancel₀ hk' h)
  rintro _ ⟨x, ⟨hi, hb⟩, rfl⟩
  refine ⟨hi, fun φ => ?_⟩
  have : ‖φ x‖ ≤ R := by
    by_cases hφ : φ ∈ Ψ
    · exact hb ⟨φ, hφ⟩
    · have h2 : ComplexEmbedding.conjugate φ ∈ Ψ := by
        by_contra h3
        exact hφ ((hΨ φ).2 h3)
      have := hb ⟨_, h2⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using this
  simp only [map_mul, map_intCast, norm_mul]
  exact mul_le_mul_of_nonneg_left this (norm_nonneg _)


omit [IsCMField E] in
theorem exists_common_den {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ v ∈ Λ, ∀ a, IsIntegral ℤ ((k : E) * v a) := by
  classical
  obtain ⟨S, rfl⟩ := hΛ
  choose d hd hdi using (exists_int_mul_integral (E := E))
  refine ⟨∏ p ∈ S ×ˢ (Finset.univ : Finset (Fin r)), d (p.1 p.2),
    Finset.prod_ne_zero_iff.2 fun p _ => hd _, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    intro a
    have hm : (v, a) ∈ S ×ˢ (Finset.univ : Finset (Fin r)) :=
      Finset.mem_product.2 ⟨hv, Finset.mem_univ _⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : (Fin r → E) × Fin r => d (p.1 p.2)) hm
    rw [hc]
    have := (hdi (v a)).mul (isIntegral_algebraMap (R := ℤ) (A := E) (x := c))
    have e : ((d (v a) * c : ℤ) : E) * v a = (d (v a) : E) * v a * algebraMap ℤ E c := by
      simp only [Int.cast_mul, eq_intCast]
      ring
    exact e ▸ this
  | zero => intro a; simpa using isIntegral_zero
  | add x y _ _ hx hy =>
    intro a
    rw [Pi.add_apply, mul_add]
    exact (hx a).add (hy a)
  | smul c x _ hx =>
    intro a
    have := (hx a).mul (RingOfIntegers.isIntegral_coe c)
    rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm, mul_comm]
    exact this


omit [IsCMField E] in
theorem exists_int_smul_mem {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ k : ℤ, k ≠ 0 ∧ k • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntegralMultiples.main
  | exact _root_.GlobalTheory.IntegralMultiples.main
  | (apply _root_.GlobalTheory.IntegralMultiples.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultiples.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultiples.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultiples.main ..)

theorem finite_vectors (r : ℕ) (X : Data E r) (R : ℝ) :
    {v : Fin r → E | v ∈ X.Λ ∧ ∀ (τ : X.Ψ) (a : Fin r), ‖τ.1 (v a)‖ ≤ R}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den X.Λ X.Λ_fg
  refine (Set.Finite.pi' fun _ : Fin r => finite_bounded X.Ψ X.cmType k hk R).subset ?_
  rintro v ⟨hv, hb⟩ a
  exact ⟨hi v hv a, fun τ => hb τ a⟩

theorem finite_automorphisms (r : ℕ) (X : Data E r) (R : ℝ) :
    {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
      ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den X.Λ X.Λ_fg
  choose l hl hm using fun b : Fin r => exists_int_smul_mem X.Λ X.Λ_span (Pi.single b 1)
  have hfin := Set.Finite.pi' fun _ : Fin r => Set.Finite.pi' fun b : Fin r =>
    finite_bounded X.Ψ X.cmType (k * l b) (mul_ne_zero hk (hl b)) R
  refine Set.Finite.of_finite_image
    (f := fun γ : GL (Fin r) E => fun a b => (γ : Matrix (Fin r) (Fin r) E) a b)
    (hfin.subset ?_) (fun x _ y _ h => Units.ext h)
  rintro _ ⟨γ, ⟨hγ, hb⟩, rfl⟩ a b
  refine ⟨?_, fun τ => hb τ a b⟩
  have := hi _ ((hγ.2 _).1 (hm b)) a
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at this
  simpa [mul_assoc, Matrix.col] using this

theorem latFin : ((∀ (r : ℕ) (X : Data E r) (R : ℝ), {v : Fin r → E | v ∈ X.Λ ∧ ∀ (τ : X.Ψ) (a : Fin r), ‖τ.1 (v a)‖ ≤ R}.Finite) ∧ (∀ (r : ℕ) (X : Data E r) (R : ℝ), {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r), ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite)) :=
  ⟨finite_vectors, finite_automorphisms⟩

end GlobalTheory.LatFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsLowerUnitriangularMulUpperTriangular
section
open Matrix MvPolynomial ReciprocityTheory.MultiplicativeHeights

namespace GlobalTheory

theorem exists_lowerUnitriangular_mul_upperTriangular :
    ∀ (p : ℕ) (x : Matrix (Fin p) (Fin p) ℂ), (∀ i, leadMinor x i ≠ 0) →
      ∃ n b : Matrix (Fin p) (Fin p) ℂ, x = n * b ∧ (∀ i, n i i = 1) ∧
        (∀ i j, i < j → n i j = 0) ∧ (∀ i j, j < i → b i j = 0) := by
  intro p x hx
  have hM : ∀ k : Fin (p + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor x k ≠ 0 := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
      have : IsEmpty (Fin ((0 : Fin (p + 1)) : ℕ)) := inferInstanceAs (IsEmpty (Fin 0))
      rw [Matrix.det_isEmpty]
      exact one_ne_zero
    · exact hx i
  set L := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm x with hL
  have hu : IsUnit L.det := by
    rw [hL, ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_det]; exact isUnit_one
  have hup : ∀ i k : Fin p, i < k → L i k = 0 := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_up x
  have hd : ∀ i : Fin p, L i i = 1 := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_diag x
  have hbt : L.BlockTriangular OrderDual.toDual := fun i k h => hup i k h
  let : Invertible L := L.invertibleOfIsUnitDet hu
  have hinv : L⁻¹.BlockTriangular OrderDual.toDual := blockTriangular_inv_of_blockTriangular hbt
  have hup' : ∀ i k : Fin p, i < k → L⁻¹ i k = 0 := fun i k h => hinv h
  refine ⟨L⁻¹, L * x, ?_, fun i => ?_, hup', fun i j h => ?_⟩
  · rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
  · have h := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.row_expand L L⁻¹ i i (hup i) (hd i)
    rw [mul_nonsing_inv _ hu, Matrix.one_apply_eq, Finset.sum_eq_zero, zero_add] at h
    · exact h.symm
    · intro k _
      rw [hup' _ i (by rw [Fin.lt_def]; exact k.isLt), mul_zero]
  · exact ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_mul_up x hM i j h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMaximalMinorNeZeroOfLinearIndependent
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
theorem _root_.GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent
    (K : Type) [Field K] (r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → K)
    (hw : LinearIndependent K w) :
    ∃ e : ι → Fin r, Function.Injective e ∧ (Matrix.of fun k a => w a (e k)).det ≠ 0 := by
  classical
  set A : Matrix (Fin r) ι K := Matrix.of fun k a => w a k with hA
  have hcol : A.col = w := rfl
  have hrank : A.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_cols, hcol, finrank_span_eq_card hw]
  have htop : Submodule.span K (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
  haveI : Fintype κ := Fintype.ofInjective a ha
  let b := Module.Basis.mk hli (by rw [hspan, htop])
  have hcard : Fintype.card ι = Fintype.card κ := by
    rw [← Module.finrank_fintype_fun_eq_card (R := K), Module.finrank_eq_card_basis b]
  let f : ι ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ f, ha.comp f.injective, ?_⟩
  have hrow : LinearIndependent K (Matrix.of fun k a' => w a' ((a ∘ f) k)).row :=
    hli.comp f f.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrow)).ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndexRangeMulVecLinEqAbsNormDet
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [IsCMField E] in
theorem _root_.GlobalTheory.index_range_mulVecLin_eq_abs_norm_det :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (𝓞 E)), A.det ≠ 0 →
      (((LinearMap.range A.mulVecLin).toAddSubgroup.index : ℕ) : ℚ) =
        |Algebra.norm ℚ ((A.det : 𝓞 E) : E)|) := by
  intro ι _ _ A hA
  classical
  set f := A.mulVecLin with hf
  have hinj : Function.Injective f := by
    intro u v huv
    have h : A.mulVec (u - v) = 0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr huv
    exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hA h)
  let b := Module.Free.chooseBasis ℤ (ι → 𝓞 E)
  let fZ : (ι → 𝓞 E) →ₗ[ℤ] (ι → 𝓞 E) := f.restrictScalars ℤ
  have hinjZ : Function.Injective fZ := hinj
  let e := LinearEquiv.ofInjective fZ hinjZ
  have key := AddSubgroup.index_eq_natAbs_det b (LinearMap.range f).toAddSubgroup (b.map e)
  rw [key]
  have hdet : (b.det fun i ↦ ((b.map e i : LinearMap.range fZ) : ι → 𝓞 E)) = LinearMap.det fZ := by
    rw [Module.Basis.det_apply, ← LinearMap.det_toMatrix b]
    congr 1
    ext i j
    simp [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply, e]
  have h2 : (((b.det fun i ↦ ((b.map e i : LinearMap.range fZ) : ι → 𝓞 E)).natAbs : ℕ) : ℚ) =
      |Algebra.norm ℚ ((A.det : 𝓞 E) : E)| := by
    rw [hdet, LinearMap.det_restrictScalars, hf, ← Matrix.toLin'_apply', LinearMap.det_toLin',
      Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsCompactOrthBounded
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FinCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isCompact_orth_bounded :
    (∀ (r : ℕ) (X : Data E r) (R : ℝ),
      IsCompact {x : Frame X.Ψ r | IsOrth X x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R}) := by
  intro r X R
  have h1 : IsClosed {x : Frame X.Ψ r | IsOrth X x} := by
    simp only [IsOrth, Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    refine continuous_matrix fun a b => ?_
    simp only [gram, hermC, col, mat, Matrix.of_apply]
    fun_prop
  have h2 : IsClosed {x : Frame X.Ψ r | ∀ τ a b, ‖x τ a b‖ ≤ R} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le ?_ continuous_const
    fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (h1.inter h2) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := |R|)).subset ?_
  rintro x ⟨-, hx⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro τ
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro a
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro b
  exact (hx τ a b).trans (le_abs_self R)

end GlobalTheory.FinCovol
end

