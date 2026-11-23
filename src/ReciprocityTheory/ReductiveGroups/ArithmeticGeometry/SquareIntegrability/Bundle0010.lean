module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.NormProjectionSq
section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

private lemma Hf_im_IR_lemma {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) {x y : Vsp dim} (hx : x ∈ IR I) (hy : y ∈ IR I) :
    (Hf x y).im = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hI x hx y hy
    | zero => simp [Hf]
    | add y z _ _ h1 h2 =>
      have e : Hf x (y + z) = Hf x y + Hf x z := by
        simp only [Hf, PiLp.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      rw [e, Complex.add_im, h1, h2, add_zero]
    | smul r y _ h =>
      have e : Hf x (r • y) = (r : ℂ) * Hf x y := by
        unfold Hf
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Complex.conj_ofReal]
        ring
      simp [e, h]
  | zero => simp [Hf]
  | add a b _ _ h1 h2 =>
    have e : Hf (a + b) y = Hf a y + Hf b y := by
      simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    rw [e, Complex.add_im, h1, h2, add_zero]
  | smul r a _ h =>
    have e : Hf (r • a) y = (r : ℂ) * Hf a y := by
      unfold Hf
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp
      ring
    simp [e, h]

lemma norm_projection_sq [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (σ : E →+* ℂ) (u : Vsp dim)
    (h1 : Mc σ 1 u ∈ IR I) (hi : Mc σ Complex.I u ∈ IR I) :
    ‖Mc σ 1 u‖ ^ 2 = 2 * ‖prj σ u‖ ^ 2 := by
  classical
  have hσ : ComplexEmbedding.conjugate σ ≠ σ := fun h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk σ)))
      (ComplexEmbedding.isReal_iff.2 h)
  have hσ' : σ ≠ ComplexEmbedding.conjugate σ := fun h => hσ h.symm
  set S1 : ℝ := ∑ i : Idx dim, if i.1 = σ then ‖u i‖ ^ 2 else 0 with hS1
  set S2 : ℝ := ∑ i : Idx dim, if i.1 = ComplexEmbedding.conjugate σ then ‖u i‖ ^ 2 else 0 with hS2
  have e1 : ‖Mc σ 1 u‖ ^ 2 = S1 + S2 := by
    rw [EuclideanSpace.norm_sq_eq, hS1, hS2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i.1 σ with h1 | h1
    · simp [Mc_apply, h1, hσ']
    · by_cases h2 : i.1 = ComplexEmbedding.conjugate σ
      · simp [Mc_apply, h1, h2, hσ]
      · simp [Mc_apply, h1, h2]
  have e2 : ‖prj σ u‖ ^ 2 = S1 := by
    rw [EuclideanSpace.norm_sq_eq, hS1]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : i.1 = σ <;> simp [prj_apply, h1]
  have e3 : (Hf (Mc σ 1 u) (Mc σ Complex.I u)).im = S2 - S1 := by
    rw [Hf, Complex.im_sum, hS1, hS2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i.1 σ with h1 | h1
    · simp [Mc_apply, h1, hσ', Complex.mul_im, Complex.sq_norm, Complex.normSq_apply] <;> ring
    · by_cases h2 : i.1 = ComplexEmbedding.conjugate σ
      · simp [Mc_apply, h1, h2, hσ, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply] <;> ring
      · simp [Mc_apply, h1, h2]
  have e4 := Hf_im_IR_lemma hI h1 hi
  linarith

lemma orth_prj [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (σ : E →+* ℂ) {t y : Vsp dim} (ht : t ∈ IR I)
    (hy : ∀ c, Mc σ c y ∈ IR I) (horth : ∀ c, inner ℝ t (Mc σ c y) = 0) :
    Hf (prj σ t) (prj σ y) = 0 := by
  classical
  have hσ : ComplexEmbedding.conjugate σ ≠ σ := fun h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk σ)))
      (ComplexEmbedding.isReal_iff.2 h)
  have hσ' : σ ≠ ComplexEmbedding.conjugate σ := fun h => hσ h.symm
  have hre : ∀ a : Vsp dim, inner ℝ t a = (Hf t a).re := by
    intro a
    rw [PiLp.inner_apply, Hf, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.inner, Complex.mul_re]
    ring
  have key : ∀ c : ℂ, Hf t (Mc σ c y) = (starRingEnd ℂ) c * Hf (prj σ t) (prj σ y) +
      c * Hf (prj (ComplexEmbedding.conjugate σ) t) (prj (ComplexEmbedding.conjugate σ) y) := by
    intro c
    rw [Hf, Hf, Hf, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i.1 σ with h1 | h1
    · simp [Mc_apply, prj_apply, h1, hσ'] <;> ring
    · by_cases h2 : i.1 = ComplexEmbedding.conjugate σ
      · simp [Mc_apply, prj_apply, h1, h2, hσ] <;> ring
      · simp [Mc_apply, prj_apply, h1, h2]
  have hz : ∀ c : ℂ, Hf t (Mc σ c y) = 0 := fun c =>
    Complex.ext (by rw [← hre]; simpa using horth c) (by simpa using Hf_im_IR_lemma hI ht (hy c))
  have e1 := (key 1).symm.trans (hz 1)
  have e2 := (key Complex.I).symm.trans (hz Complex.I)
  rw [map_one] at e1
  rw [Complex.conj_I] at e2
  linear_combination (1 / 2 : ℂ) * e1 + (Complex.I / 2) * e2 +
    ((Hf (prj σ t) (prj σ y) - Hf (prj (ComplexEmbedding.conjugate σ) t) (prj (ComplexEmbedding.conjugate σ) y)) / 2) *
      Complex.I_sq

abbrev conjO [IsCMField E] (α : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E α

lemma emb_conjO [IsCMField E] (α : 𝓞 E) (τ : E →+* ℂ) :
    τ ((conjO α : 𝓞 E) : E) = (starRingEnd ℂ) (τ (α : E)) := by
  simp [conjO, NumberField.IsCMField.coe_ringOfIntegersComplexConj,
    NumberField.IsCMField.complexEmbedding_complexConj]

lemma act_apply {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v : Vsp dim) (i : Idx dim) :
    act α v i = i.1 (α : E) * v i := rfl

def actL {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun := act α
  map_add' v w := by ext i; simp only [act_apply, PiLp.add_apply]; ring
  map_smul' c v := by ext i; simp only [act_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma Hf_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (x a : Vsp dim) :
    Hf (act α x) a = Hf x (act (conjO α) a) := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [act, emb_conjO]
  ring

lemma inner_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (u a : Vsp dim) :
    inner ℝ (act α u) a = inner ℝ u (act (conjO α) a) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [act, emb_conjO, Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

lemma act_mem_IR {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (α : 𝓞 E) {a : Vsp dim} (ha : a ∈ IR I) :
    act α a ∈ IR I := by
  have key : Submodule.span ℝ (I : Set (Vsp dim)) ≤ (IR I).comap ((actL α).restrictScalars ℝ) := by
    rw [Submodule.span_le]
    intro x hx
    exact Submodule.subset_span (hs α x hx)
  exact key ha

lemma isU_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (α : 𝓞 E) {x u : Vsp dim} (h : IsU I x u) :
    IsU I (act α x) (act α u) := by
  exact ⟨act_mem_IR hs α h.1, fun a ha => by
    rw [inner_act, h.2 _ (act_mem_IR hs _ ha), Hf_act]⟩

lemma norm_act_le {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (B : ℝ) (hB : ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ B)
    (v : Vsp dim) : ‖act α v‖ ≤ B * ‖v‖ := by
  by_cases hv : v = 0
  · subst hv
    rw [show act α (0 : Vsp dim) = 0 from (actL α).map_zero]
    simp
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (by ext i; simpa using h i)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i.1)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hB0, ← Real.sqrt_mul (sq_nonneg B)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simp only [act, PiLp.toLp_apply, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB j.1) 2) (sq_nonneg _)

def Xg {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) : AddSubgroup (Vsp dim) where
  carrier := {u | ∃ x ∈ L, IsU I x u}
  add_mem' := by
    rintro u v ⟨x, hx, hu⟩ ⟨y, hy, hv⟩; exact ⟨x + y, L.add_mem hx hy, isU_add hu hv⟩
  zero_mem' := ⟨0, L.zero_mem, isU_zero I⟩
  neg_mem' := by rintro u ⟨x, hx, hu⟩; exact ⟨-x, L.neg_mem hx, isU_neg hu⟩

lemma Xg_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hL : ∀ (α : 𝓞 E) x, x ∈ L → act α x ∈ L) (hs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (α : 𝓞 E) {u : Vsp dim} (hu : u ∈ Xg L I) : act α u ∈ Xg L I := by
  obtain ⟨x, hx, h⟩ := hu
  exact ⟨act α x, hL α x hx, isU_act hs α h⟩

lemma Xg_IR {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)} {u : Vsp dim}
    (hu : u ∈ Xg L I) : u ∈ IR I := by
  obtain ⟨x, -, h⟩ := hu
  exact h.1

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SupRatioLeOfPhaseZero
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem HC_one {dim : (E →+* ℂ) → ℕ} (v w : Vsp dim) :
    HC (n := 1) (fun _ => v) (fun _ => w) = Hf v w := by
  simp [HC]

theorem Hf_self_re {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) : (Hf v v).re = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Hf, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

namespace PT

variable (X : PT E)

def toGT : GT (Idx X.dim) where
  b := X.b
  integral := X.integral
  perfect := X.perfect
  ka := fun x => (X.eps x : ℂ)
  ka_abs := fun x hx => by
    rcases X.eps_pm x hx with h | h <;> simp [h]

def col1 (s : (Fin 1 → Vsp X.dim) → ℂ) : Vsp X.dim → ℂ := fun v => s fun _ => v

theorem column_mem_sections {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) : X.col1 s ∈ X.toGT.Sec 1 := by
  obtain ⟨hd, hf⟩ := hs
  refine (show Differentiable ℂ (X.col1 s) ∧ ∀ γ ∈ lat X.toGT.b, ∀ v, X.col1 s (v + γ) =
      X.toGT.ka γ * cexp (((1 : ℕ) : ℂ) * Real.pi * Hf v γ + ((1 : ℕ) : ℂ) * Real.pi * Hf γ γ / 2) *
        X.col1 s v from ⟨?_, ?_⟩)
  · exact hd.comp (differentiable_pi.mpr fun _ => differentiable_id)
  · intro γ hγ v
    have h := hf (fun _ => γ) (fun _ => hγ) (fun _ => v)
    simp only [HC_one, Fin.prod_univ_one, pow_one] at h
    exact h

theorem pointNormSq_column (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Vsp X.dim) :
    X.ptN2 1 s (fun _ => a) = X.toGT.ptN2 1 (X.col1 s) a := by
  simp only [PT.ptN2, GT.ptN2, PT.col1, HC_one, Hf_self_re]

theorem l2_one_eq_toGT_l2_col1 (s : (Fin 1 → Vsp X.dim) → ℂ) : X.l2 1 s = X.toGT.l2 1 (X.col1 s) := by
  have hfd : X.fd 1 = (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim)) ⁻¹'
      ZSpan.fundamentalDomain X.b := by
    ext v
    simp only [PT.fd, Set.mem_setOf_eq, Set.mem_preimage]
    exact ⟨fun h => h default, fun h k => by rwa [Subsingleton.elim k default]⟩
  have hf : ∀ v : Fin 1 → Vsp X.dim, X.ptN2 1 s v =
      X.toGT.ptN2 1 (X.col1 s) (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim) v) := by
    intro v
    have hv : v = fun _ => v default := funext fun k => by rw [Subsingleton.elim k default]
    rw [hv, pointNormSq_column]
    rfl
  have hmp := MeasureTheory.volume_preserving_funUnique (Fin 1) (Vsp X.dim)
  have he := (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim)).measurableEmbedding
  unfold PT.l2 GT.l2
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, hfd]
  simp only [MeasureTheory.measureReal_def]
  erw [hmp.measure_preimage_emb he]
  simp_rw [hf]
  erw [hmp.setIntegral_preimage_emb he (X.toGT.ptN2 1 (X.col1 s))]
  rfl

theorem card_idx [IsCMField E] : Fintype.card (Idx X.dim) = X.gA := by
  have hinv : Function.Involutive
      (NumberField.ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
    fun φ => RingHom.ext fun x => by simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hsum : ∑ τ, X.dim (NumberField.ComplexEmbedding.conjugate τ) = ∑ τ, X.dim τ :=
    Equiv.sum_comp (Function.Involutive.toPerm _ hinv) X.dim
  have h2 : 2 * ∑ τ, X.dim τ = Fintype.card (E →+* ℂ) * X.r := by
    rw [two_mul]
    nth_rewrite 2 [← hsum]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun τ _ => X.dim_conj τ), Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  haveI : NumberField.IsTotallyComplex E := NumberField.IsCMField.to_isTotallyComplex
  rw [NumberField.Embeddings.card, NumberField.IsTotallyComplex.finrank] at h2
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  unfold PT.gA PT.f
  rw [NumberField.IsTotallyComplex.finrank, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  linarith

theorem firstMinimum_toTorus : X.toGT.la1 = X.la1 := rfl

end PT

theorem f_pos {X : PT E} {DF : ℕ} (P : Par X DF) : 1 ≤ PT.f E := by
  have h := P.hfr
  rcases Nat.eq_zero_or_pos (PT.f E) with h0 | h0
  · rw [h0, zero_mul] at h
    omega
  · exact h0

theorem firstMinimum_pos_bis [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) : 0 < X.la1 := by
  rw [← X.firstMinimum_toTorus]
  apply firstMinimum_pos
  rw [X.card_idx]
  have h := P.hfr
  unfold PT.gA
  omega

theorem threshold_le_firstMinimum [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (h0 : P.ph = 0) :
    th (E := E) P.q P.R0 ≤ X.la1 := by
  by_contra hlt
  push_neg at hlt
  have hp : P.ph = 2 * PT.f E / (PT.rd E ^ 2 * X.la1 ^ 2) := by
    simp only [Par.ph, PT.ph, if_pos hlt]
  rw [hp] at h0
  have hla := firstMinimum_pos_bis P
  have hf : (1 : ℝ) ≤ PT.f E := by exact_mod_cast f_pos P
  have hrd : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hpos : 0 < 2 * (PT.f E : ℝ) / (PT.rd E ^ 2 * X.la1 ^ 2) :=
    div_pos (by linarith) (mul_pos (pow_pos (by linarith) 2) (pow_pos hla 2))
  linarith

theorem one_le_sqrt_q_th {X : PT E} {DF : ℕ} (P : Par X DF) :
    1 ≤ Real.sqrt P.q * th (E := E) P.q P.R0 := by
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hf : (1 : ℝ) ≤ PT.f E := by exact_mod_cast f_pos P
  have hR : (270 : ℝ) ≤ P.R0 ^ 2 := P.hR0.1
  have hrd : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hRR : 1 ≤ RR (E := E) := by
    unfold RR
    exact one_le_pow₀ (by linarith)
  have h3 : 1 ≤ RR (E := E) ^ 3 := one_le_pow₀ hRR
  unfold th
  rw [← Real.sqrt_mul hq.le]
  have hA : (P.q : ℝ) * (PT.f E * P.R0 ^ 2 * RR (E := E) ^ 3 / P.q) =
      PT.f E * P.R0 ^ 2 * RR (E := E) ^ 3 := by
    field_simp
  rw [hA, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  apply Real.sqrt_le_sqrt
  have h1 : (270 : ℝ) ≤ PT.f E * P.R0 ^ 2 := by nlinarith
  nlinarith

theorem sup_ratio_le_of_phase_zero [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hS : GSupStatement)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) (h0 : P.ph = 0) (a : Vsp X.dim) :
    Real.sqrt (X.ptN2 1 s fun _ => a) / Real.sqrt (X.l2 1 s) ≤ Real.exp P.p1 := by
  have hN : Fintype.card (Idx X.dim) = X.gA := X.card_idx
  have hth := threshold_le_firstMinimum P h0
  have hsq := one_le_sqrt_q_th P
  have hla : 0 < X.la1 := firstMinimum_pos_bis P
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hsqrtq : 0 < Real.sqrt P.q := Real.sqrt_pos.mpr hq
  have hB := hS (Idx X.dim) X.toGT 1 le_rfl (X.col1 s) (X.column_mem_sections hs) a
  rw [← X.pointNormSq_column, ← X.l2_one_eq_toGT_l2_col1, X.firstMinimum_toTorus, hN] at hB
  simp only [Nat.cast_one, one_pow, one_mul, mul_one] at hB
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 1 + 6 * Real.sqrt (X.gA * P.q) := ⟨_, rfl⟩
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hspi1 : 1 ≤ Real.sqrt Real.pi := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hs2 : Real.sqrt 2 ≤ 1.5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h1 : 1 ≤ Real.sqrt P.q * X.la1 :=
    le_trans hsq (mul_le_mul_of_nonneg_left hth hsqrtq.le)
  have hsN := Real.sqrt_nonneg (X.gA : ℝ)
  have hterm : 4 * Real.sqrt (2 * X.gA) / (Real.sqrt Real.pi * X.la1) ≤
      6 * Real.sqrt (X.gA * P.q) := by
    rw [div_le_iff₀ (mul_pos hspi hla), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_mul (Nat.cast_nonneg _)]
    have e1 : 4 * (Real.sqrt 2 * Real.sqrt X.gA) ≤ Real.sqrt X.gA * (6 * Real.sqrt Real.pi) := by
      nlinarith
    have e2 : Real.sqrt X.gA * (6 * Real.sqrt Real.pi) ≤
        Real.sqrt X.gA * (6 * Real.sqrt Real.pi) * (Real.sqrt P.q * X.la1) :=
      le_mul_of_one_le_right (by positivity) h1
    nlinarith
  have hBC : 1 + 4 * Real.sqrt (2 * X.gA) / (Real.sqrt Real.pi * X.la1) ≤ C := by
    rw [hC]; linarith
  have hB0 : 0 ≤ 1 + 4 * Real.sqrt (2 * X.gA) / (Real.sqrt Real.pi * X.la1) := by positivity
  have hCpos : 0 < C := by rw [hC]; positivity
  rcases le_or_gt (X.l2 1 s) 0 with hL | hL
  · rw [Real.sqrt_eq_zero'.mpr hL, div_zero]
    exact (Real.exp_pos _).le
  · have hpow := pow_le_pow_left₀ hB0 hBC (2 * X.gA)
    have hA : X.ptN2 1 s (fun _ => a) ≤ 2 * C ^ (2 * X.gA) * X.l2 1 s := by
      refine hB.trans ?_
      gcongr
    have hexp : Real.exp P.p1 = Real.exp 1 * C ^ X.gA := by
      unfold Par.p1
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by rw [← hC]; exact hCpos), hC]
    have he2 : Real.sqrt 2 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hL), hexp]
    have hsplit : Real.sqrt (2 * C ^ (2 * X.gA) * X.l2 1 s) =
        Real.sqrt 2 * C ^ X.gA * Real.sqrt (X.l2 1 s) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        show C ^ (2 * X.gA) = (C ^ X.gA) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    calc Real.sqrt (X.ptN2 1 s fun _ => a) ≤ Real.sqrt (2 * C ^ (2 * X.gA) * X.l2 1 s) :=
          Real.sqrt_le_sqrt hA
      _ = Real.sqrt 2 * C ^ X.gA * Real.sqrt (X.l2 1 s) := hsplit
      _ ≤ Real.exp 1 * C ^ X.gA * Real.sqrt (X.l2 1 s) := by gcongr

end

end ReciprocityTheory.ChartRestriction.G.I2
end

