module

public import Development.WeilBound.CoreStatements.SesquilinearFractions.HermSplit

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.ImIMulDivSq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem trace_sum (A : E) : (((Algebra.trace ℚ E A : ℚ) : ℝ) : ℂ) = ∑ σ : E →+* ℂ, σ A := by
  rw [Complex.ofReal_ratCast,
    show ((Algebra.trace ℚ E A : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E A) from (eq_ratCast _ _).symm,
    trace_eq_sum_embeddings]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)

theorem trace_re (A : E) : ((Algebra.trace ℚ E A : ℚ) : ℝ) =
    ∑ σ ∈ Finset.univ.filter (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0), 2 * (σ A).re := by
  have h1 := congrArg Complex.re (trace_sum A)
  rw [Complex.ofReal_re, Complex.re_sum, sum_split (H := H)] at h1
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  ring

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)
variable (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) E)
variable {D : Datum H} (c : D.La →ₗ[𝓞 E] (Fin p ⊕ Fin q →₀ 𝓞 E)) (n : ℕ)

theorem per_at_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0) (y : D.La) (a : Fin p) :
    per hty c n y ((eP hty σ h).symm a).1 = σ ((c y (.inl a) : 𝓞 E) : E) / n := by
  rw [per_apply, blk_inl hty σ h _ ((eP hty σ h).symm a).2, ((eP hty σ h).symm a).2]
  simp

theorem per_at_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0) (y : D.La) (a : Fin q) :
    per hty c n y ((eQ hty σ h).symm a).1 = σ ((c y (.inr a) : 𝓞 E) : E) / n := by
  rw [per_apply, blk_inr hty σ h _ ((eQ hty σ h).symm a).2, ((eQ hty σ h).symm a).2]
  simp

def blkA (y y' : D.La) : E := ∑ a : Fin p, ∑ b : Fin p,
  ((c y (.inl a) : 𝓞 E) : E) * G (.inl a) (.inl b) * IsCMField.complexConj E ((c y' (.inl b) : 𝓞 E) : E)

def blkB (y y' : D.La) : E := ∑ a : Fin q, ∑ b : Fin q,
  ((c y (.inr a) : 𝓞 E) : E) * G (.inr a) (.inr b) * IsCMField.complexConj E ((c y' (.inr b) : 𝓞 E) : E)

theorem Q_per_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0) (y y' : D.La) :
    Q hty G σ (per hty c n y) (per hty c n y') = Complex.I * (2 * σ (blkA G c y y') / ((n : ℂ) * n)) := by
  rw [Q_inl hty G σ h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [per_at_inl, blkA, map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_div₀, map_natCast,
    Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem Q_per_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0) (y y' : D.La) :
    Q hty G σ (per hty c n y) (per hty c n y') = Complex.I * (2 * σ (blkB G c y y') / ((n : ℂ) * n)) := by
  rw [Q_inr hty G σ h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [per_at_inr, blkB, map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_div₀, map_natCast,
    Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem im_I_mul_div_sq (z : ℂ) (n : ℕ) : (Complex.I * (2 * z / ((n : ℂ) * n))).im = 2 * z.re / ((n : ℝ) * n) := by
  have e : (2 * z / ((n : ℂ) * n)) = ((2 / ((n : ℝ) * n) : ℝ) : ℂ) * z := by push_cast; ring
  rw [e, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.re_ofReal_mul]
  ring

theorem herm_im (y y' : D.La) :
    (hermForm (Hm hty G) (per hty c n y) (per hty c n y')).im =
      ((Algebra.trace ℚ E (blkA G c y y' + blkB G c y y') : ℚ) : ℝ) / ((n : ℝ) * n) := by
  rw [herm_split, Complex.im_sum, sum_split (H := H), ← Finset.sum_add_distrib, trace_re (H := H),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have h : σ (H.rt : E) = H.rt0 := (Finset.mem_filter.mp hσ).2
  have h' : ComplexEmbedding.conjugate σ (H.rt : E) ≠ H.rt0 := fun hc => (conjugate_rt σ).mp hc h
  rw [Q_per_inl hty G c n σ h, Q_per_inr hty G c n _ h', im_I_mul_div_sq, im_I_mul_div_sq,
    ComplexEmbedding.conjugate_coe_eq, Complex.conj_re, map_add, Complex.add_re]
  ring

theorem sesq_blocks (x : Fin p ⊕ Fin q → D.La) (hc : ∀ y, ∑ m, c y m • x m = n • y)
    (horth : ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) (y y' : D.La) :
    blkA (gramE D x) c y y' + blkB (gramE D x) c y y' = (n : E) * n * sesq D y y' := by
  obtain ⟨-, hl, hr, hsl, hsr, hsk, -⟩ := sesq_sesquilinear_properties D
  let L : D.La → D.La →+ E := fun y' => AddMonoidHom.mk' (fun u => sesq D u y') (fun a b => hl a b y')
  let R : D.La → D.La →+ E := fun u => AddMonoidHom.mk' (fun v => sesq D u v) (fun a b => hr u a b)
  have key : sesq D (n • y) (n • y') = (n : E) * n * sesq D y y' := by
    have e1 : sesq D (n • y) (n • y') = n • sesq D y (n • y') := map_nsmul (L (n • y')) n y
    have e2 : sesq D y (n • y') = n • sesq D y y' := map_nsmul (R y) n y'
    rw [e1, e2, nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [← key, ← hc y, ← hc y']
  have e3 : sesq D (∑ m, c y m • x m) (∑ m, c y' m • x m) = ∑ m, ∑ m', ((c y m : 𝓞 E) : E) *
      sesq D (x m) (x m') * IsCMField.complexConj E ((c y' m' : 𝓞 E) : E) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show sesq D (∑ m, c y m • x m) (∑ m, c y' m • x m) =
      L (∑ m, c y' m • x m) (∑ m, c y m • x m) from rfl, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show L (∑ m, c y' m • x m) (c y m • x m) = sesq D (c y m • x m) (∑ m, c y' m • x m) from rfl,
      hsl, show sesq D (x m) (∑ m', c y' m' • x m') = R (x m) (∑ m', c y' m' • x m') from rfl,
      map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [show R (x m) (c y' m' • x m') = sesq D (x m) (c y' m' • x m') from rfl, hsr]
    ring
  have horth' : ∀ a b, sesq D (x (.inr b)) (x (.inl a)) = 0 := fun a b => by
    rw [hsk, horth, map_zero, neg_zero]
  rw [e3]
  simp only [Fintype.sum_sum_type, blkA, blkB, gramE, Matrix.of_apply, horth, horth', mul_zero,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add]

theorem herm_EF (hn : 0 < n) (x : Fin p ⊕ Fin q → D.La) (hc : ∀ y, ∑ m, c y m • x m = n • y)
    (horth : ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) (y y' : D.La) :
    (hermForm (Hm hty (gramE D x)) (per hty c n y) (per hty c n y')).im = D.EF y y' := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h1 := trace_mul_sesq_eq_form D 1 y y'
  rw [one_smul, show ((1 : 𝓞 E) : E) = 1 by simp, _root_.one_mul] at h1
  have ht : Algebra.trace ℚ E ((n : E) * n * sesq D y y') = ((n * n : ℕ) : ℚ) * (D.EF y y' : ℚ) := by
    rw [show (n : E) * n * sesq D y y' = (n * n : ℕ) • sesq D y y' by rw [nsmul_eq_mul]; push_cast; ring,
      map_nsmul, h1, nsmul_eq_mul]
  rw [herm_im, sesq_blocks c n x hc horth, ht]
  push_cast
  field_simp

end PositivityTheory.Xgf.DPer

end
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.QReInr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)
variable (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) E)

theorem Hm_herm (hskew : ∀ m m', G m' m = -IsCMField.complexConj E (G m m')) : (Hm hty G).IsHermitian := by
  ext k k'
  simp only [Matrix.conjTranspose_apply, Hm, Matrix.of_apply]
  by_cases h : ty k = ty k'
  · rw [if_pos h.symm, if_pos h, hskew (blk hty k) (blk hty k'), map_neg,
      IsCMField.complexEmbedding_complexConj, h]
    simp [Complex.conj_I]
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

private theorem re_star_dotProduct_mulVec_pos_of_posDef {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (hN : N.PosDef) (x : Fin n → ℂ) :
    0 ≤ (star x ⬝ᵥ N *ᵥ x).re ∧ (x ≠ 0 → 0 < (star x ⬝ᵥ N *ᵥ x).re) :=
  ⟨(Complex.nonneg_iff.mp (hN.posSemidef.dotProduct_mulVec_nonneg x)).1,
    fun hx => (Complex.pos_iff.mp (hN.dotProduct_mulVec_pos hx)).1⟩

theorem Q_re_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0)
    (hG1 : (Matrix.of fun a b : Fin p => Complex.I * σ (G (.inl a) (.inl b))).PosDef) (z : Fin g → ℂ) :
    0 ≤ (Q hty G σ z z).re ∧ ((∃ a, z ((eP hty σ h).symm a) ≠ 0) → 0 < (Q hty G σ z z).re) := by
  set x : Fin p → ℂ := fun a => star (z ((eP hty σ h).symm a)) with hx
  have hQ : Q hty G σ z z =
      2 * (star x ⬝ᵥ (Matrix.of fun a b : Fin p => Complex.I * σ (G (.inl a) (.inl b))) *ᵥ x) := by
    rw [Q_inl hty G σ h]
    simp only [hx, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum, Pi.star_apply, star_star,
      Complex.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  obtain ⟨h0, h1⟩ := re_star_dotProduct_mulVec_pos_of_posDef _ hG1 x
  have hre : (Q hty G σ z z).re = 2 * (star x ⬝ᵥ (Matrix.of fun a b : Fin p =>
      Complex.I * σ (G (.inl a) (.inl b))) *ᵥ x).re := by
    rw [hQ, Complex.mul_re]
    norm_num
  rw [hre]
  refine ⟨by positivity, fun ⟨a, ha⟩ => ?_⟩
  have hx0 : x ≠ 0 := fun h0' => ha (by simpa [hx] using congrFun h0' a)
  have := h1 hx0
  positivity

theorem Q_re_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0)
    (hG2 : (-(Matrix.of fun a b : Fin q => Complex.I * ComplexEmbedding.conjugate σ (G (.inr a) (.inr b)))).PosDef)
    (z : Fin g → ℂ) :
    0 ≤ (Q hty G σ z z).re ∧ ((∃ a, z ((eQ hty σ h).symm a) ≠ 0) → 0 < (Q hty G σ z z).re) := by
  set x : Fin q → ℂ := fun a => z ((eQ hty σ h).symm a) with hx
  set M : Matrix (Fin q) (Fin q) ℂ :=
    -(Matrix.of fun a b : Fin q => Complex.I * ComplexEmbedding.conjugate σ (G (.inr a) (.inr b))) with hM
  have hQ : Q hty G σ z z = 2 * starRingEnd ℂ (star x ⬝ᵥ M *ᵥ x) := by
    rw [Q_inr hty G σ h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hx, hM, dotProduct, mulVec, Matrix.neg_apply, Matrix.of_apply, Finset.mul_sum, map_sum,
      map_mul, map_neg, Pi.star_apply, Complex.star_def, Complex.conj_conj, Complex.conj_I,
      ComplexEmbedding.conjugate_coe_eq]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  obtain ⟨h0, h1⟩ := re_star_dotProduct_mulVec_pos_of_posDef _ hG2 x
  have hre : (Q hty G σ z z).re = 2 * (star x ⬝ᵥ M *ᵥ x).re := by
    rw [hQ, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    norm_num
  rw [hre]
  refine ⟨by positivity, fun ⟨a, ha⟩ => ?_⟩
  have hx0 : x ≠ 0 := fun h0' => ha (by simpa [hx] using congrFun h0' a)
  have := h1 hx0
  positivity

theorem Hm_pos
    (hG1 : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
      (Matrix.of fun a b : Fin p => Complex.I * τ (G (.inl a) (.inl b))).PosDef)
    (hG2 : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
      (-(Matrix.of fun a b : Fin q => Complex.I * τ (G (.inr a) (.inr b)))).PosDef)
    (z : Fin g → ℂ) (hz : z ≠ 0) : 0 < (hermForm (Hm hty G) z z).re := by
  rw [herm_split, Complex.re_sum]
  have hQ : ∀ σ : E →+* ℂ, 0 ≤ (Q hty G σ z z).re ∧
      ((∃ k, ty k = σ ∧ z k ≠ 0) → 0 < (Q hty G σ z z).re) := by
    intro σ
    by_cases h : σ (H.rt : E) = H.rt0
    · obtain ⟨h1, h2⟩ := Q_re_inl hty G σ h (hG1 σ h) z
      refine ⟨h1, fun ⟨k, hk, hz⟩ => h2 ⟨eP hty σ h ⟨k, hk⟩, by simpa using hz⟩⟩
    · have hc : ComplexEmbedding.conjugate σ (H.rt : E) = H.rt0 := (conjugate_rt σ).2 h
      obtain ⟨h1, h2⟩ := Q_re_inr hty G σ h (hG2 _ hc) z
      refine ⟨h1, fun ⟨k, hk, hz⟩ => h2 ⟨eQ hty σ h ⟨k, hk⟩, by simpa using hz⟩⟩
  obtain ⟨k0, hk0⟩ : ∃ k, z k ≠ 0 := by
    by_contra hc; push Not at hc; exact hz (funext hc)
  exact Finset.sum_pos' (fun σ _ => (hQ σ).1) ⟨ty k0, Finset.mem_univ _, (hQ (ty k0)).2 ⟨k0, rfl, hk0⟩⟩

end PositivityTheory.Xgf.DPer

end
end

