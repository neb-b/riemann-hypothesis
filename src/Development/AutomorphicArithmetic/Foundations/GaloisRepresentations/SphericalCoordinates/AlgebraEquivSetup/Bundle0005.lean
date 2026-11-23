module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.OrientEv
section
noncomputable section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.Ori

variable {E : Type} [Field E] [NumberField E]

def ev1 (σ : E →+* ℂ) : ℝ ⊗[ℚ] E →ₐ[ℝ] ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ ℂ) σ.toRatAlgHom (fun _ _ => Commute.all _ _)

def evM {n : ℕ} (σ : E →+* ℂ) : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ _) (σ.mapMatrix).toRatAlgHom
    (fun x _ => Algebra.commute_algebraMap_left x _)

theorem realTensorEvalAlgHom_tmul (σ : E →+* ℂ) (r : ℝ) (x : E) : ev1 σ (r ⊗ₜ x) = r • σ x := by
  simp [ev1, Algebra.ofId_apply, Algebra.smul_def]

theorem evM_tmul {n : ℕ} (σ : E →+* ℂ) (r : ℝ) (x : Matrix (Fin n) (Fin n) E) :
    evM σ (r ⊗ₜ x) = r • x.map σ := by
  unfold evM
  refine (Algebra.TensorProduct.lift_tmul _ _ _ r x).trans ?_
  rw [Algebra.smul_def]
  rfl

theorem evM_conj {n : ℕ} (σ : E →+* ℂ) (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    evM (ComplexEmbedding.conjugate σ) z = (evM σ z).map (starRingEnd ℂ) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [evM_tmul, evM_tmul]
    ext i j
    simp [ComplexEmbedding.conjugate_coe_eq]
  | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _), Matrix.map_add _ (map_add _)]

def Th {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V] (β : V →ₗ[ℚ] (Fin n → E)) :
    ℝ ⊗[ℚ] V →ₗ[ℝ] (K × Fin n → ℂ) :=
  LinearMap.liftBaseChange ℝ
    { toFun := fun w k => f k.1 (β w k.2)
      map_add' := fun a b => by ext k; simp
      map_smul' := fun q a => by ext k; simp [map_rat_smul] }

theorem Th_tmul {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (β : V →ₗ[ℚ] (Fin n → E)) (r : ℝ) (w : V) (k : K × Fin n) :
    Th f β (r ⊗ₜ w) k = r • f k.1 (β w k.2) := by
  simp [Th]

private theorem th_actOn_tmul_eq_evM_mulVec {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (β : V →ₗ[ℚ] (Fin n → E)) (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ V)
    (hβ : ∀ x z, β (rep x z) = x *ᵥ β z) (r s : ℝ) (m : Matrix (Fin n) (Fin n) E) (w : V) (τ : K) (i : Fin n) :
    Th f β (actOn rep ℝ (r ⊗ₜ m) (s ⊗ₜ w)) (τ, i) = (evM (f τ) (r ⊗ₜ m) *ᵥ fun j => Th f β (s ⊗ₜ w) (τ, j)) i := by
  have hl : actOn rep ℝ (r ⊗ₜ m) = algebraMap ℝ _ r * (Module.End.baseChangeHom ℚ ℝ V) (rep m) := by
    unfold actOn
    exact Algebra.TensorProduct.lift_tmul _ _ _ r m
  have ha : actOn rep ℝ (r ⊗ₜ m) (s ⊗ₜ w) = (r * s) ⊗ₜ rep m w := by
    rw [hl, Module.End.mul_apply, Module.algebraMap_end_apply]
    show r • LinearMap.baseChange ℝ (rep m) (s ⊗ₜ w) = _
    rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  rw [ha, Th_tmul, evM_tmul, hβ]
  simp only [Th_tmul]
  rw [RingHom.map_mulVec]
  simp [Matrix.mulVec, dotProduct, Finset.smul_sum, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem Th_act {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (β : V →ₗ[ℚ] (Fin n → E)) (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ V)
    (hβ : ∀ x z, β (rep x z) = x *ᵥ β z) (y : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) (x : ℝ ⊗[ℚ] V) (τ : K) (i : Fin n) :
    Th f β (actOn rep ℝ y x) (τ, i) = (evM (f τ) y *ᵥ fun j => Th f β x (τ, j)) i := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    induction x using TensorProduct.induction_on with
    | zero =>
      simp
      exact (congrFun (Matrix.mulVec_zero _) i).symm
    | tmul s w => exact th_actOn_tmul_eq_evM_mulVec f β rep hβ r s m w τ i
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), Pi.add_apply, ha, hb]
      have : (fun j => Th f β (a + b) (τ, j)) = (fun j => Th f β a (τ, j)) + (fun j => Th f β b (τ, j)) := by
        ext j
        simp
      rw [this, Matrix.mulVec_add, Pi.add_apply]
  | add c d hc hd =>
    rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), Pi.add_apply, hc, hd, map_add (f := _), Matrix.add_mulVec, Pi.add_apply]

variable [IsCMField E]

theorem evM_star {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (hH : (H.map (IsCMField.complexConj E : E →+* E))ᵀ = H)
    (hdet : H.det ≠ 0) (σ : E →+* ℂ) (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    gramAt H σ * evM σ (starT (hermStar H hdet) ℝ z).unop = (evM σ z)ᴴ * gramAt H σ := by
  have hc : ∀ M : Matrix (Fin n) (Fin n) E,
      (M.map (IsCMField.complexConj E : E →+* E)).map σ = (M.map σ).map (starRingEnd ℂ) := by
    intro M
    ext i j
    simp [IsCMField.complexEmbedding_complexConj]
  have hHc : (H.map (IsCMField.complexConj E : E →+* E)).map σ = gramAt H σ := by
    have h1 := congrArg Matrix.transpose hH
    rw [Matrix.transpose_transpose] at h1
    rw [h1, gramAt, Matrix.transpose_map]
  have hu : IsUnit (H.map (IsCMField.complexConj E : E →+* E)).det := by
    rw [show (H.map (IsCMField.complexConj E : E →+* E)).det = (IsCMField.complexConj E : E →+* E) H.det from
      (RingHom.map_det _ H).symm]
    exact ((map_ne_zero _).mpr hdet).isUnit
  have hG : IsUnit (gramAt H σ).det := by
    rw [gramAt, Matrix.det_transpose, show (H.map σ).det = σ H.det from (RingHom.map_det σ H).symm]
    exact ((map_ne_zero _).mpr hdet).isUnit
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [starT_tmul, hermStar_apply, evM_tmul, evM_tmul, Matrix.map_mul, Matrix.map_mul,
      map_nonsingInv σ hu, hHc, Matrix.transpose_map, hc x, Matrix.conjTranspose_smul]
    have hx : ((x.map σ).map (starRingEnd ℂ))ᵀ = (x.map σ)ᴴ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [hx, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG,
      Matrix.one_mul, star_trivial, Matrix.smul_mul]
  | add a b ha hb =>
    rw [map_add (f := _), MulOpposite.unop_add, map_add (f := _), map_add (f := _), Matrix.mul_add, ha, hb,
      Matrix.conjTranspose_add, Matrix.add_mul]

theorem term_pos (D h z : ℂ) (hD : D.re = 0) (hD' : D.im < 0) (hi : h.im = 0) (hr : h.re ≠ 0) :
    0 ≤ (D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z).re ∧
    (z ≠ 0 → 0 < (D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z).re) := by
  have hz : z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  have e : D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z =
      D * h * (if 0 < h.re then Complex.I else -Complex.I) * (Complex.normSq z : ℂ) := by
    rw [← hz]
    ring
  rw [e]
  have hc : (D * h * (if 0 < h.re then Complex.I else -Complex.I)).re = |D.im| * |h.re| := by
    split_ifs with hp
    · simp [Complex.mul_re, Complex.mul_im, hD, hi]
      rw [abs_of_neg hD', abs_of_pos hp]
      ring
    · have hn : h.re < 0 := lt_of_le_of_ne (not_lt.mp hp) hr
      simp [Complex.mul_re, Complex.mul_im, hD, hi]
      rw [abs_of_neg hD', abs_of_neg hn]
      ring
  have hpos : 0 < |D.im| * |h.re| := mul_pos (abs_pos.mpr hD'.ne) (abs_pos.mpr hr)
  rw [Complex.re_mul_ofReal, hc]
  refine ⟨mul_nonneg hpos.le (Complex.normSq_nonneg z), fun hz0 => ?_⟩
  exact mul_pos hpos (Complex.normSq_pos.mpr hz0)

end UpperTheory.Gal.W2.Seed.Ori
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCodiffGen
section
noncomputable section

open NumberField nonZeroDivisors

namespace UpperTheory.Gal.W2.Seed

private theorem exists_ideal (E : Type) [Field E] [NumberField E] :
    ∃ (a : 𝓞 E) (J : Ideal (𝓞 E)), a ≠ 0 ∧ J ≠ ⊥ ∧
      ∀ z : E, InCodiff z ↔ ∃ j ∈ J, z = (a : E)⁻¹ * (j : E) := by
  classical
  have h1ne : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  set D : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.dual ℤ ℚ 1 with hDdef
  have hD : D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ h1ne
  have hmem : ∀ z : E, InCodiff z ↔ z ∈ D := by
    intro z
    unfold InCodiff
    rw [hDdef, FractionalIdeal.mem_dual h1ne]
    constructor
    · rintro h b hb
      obtain ⟨x, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
      obtain ⟨m, hm⟩ := h x
      exact ⟨m, by simpa [Algebra.traceForm_apply] using hm.symm⟩
    · intro h x
      obtain ⟨m, hm⟩ := h (x : E) ((FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩)
      exact ⟨m, by simpa [Algebra.traceForm_apply] using hm.symm⟩
  set d : E := algebraMap (𝓞 E) E (D.den : 𝓞 E) with hddef
  have hd0 : d ≠ 0 := by
    rw [hddef]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.coe_ne_zero _)
  have key := FractionalIdeal.den_mul_self_eq_num' (𝓞 E)⁰ E D
  have key2 : D = FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ * (D.num : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← key, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hd0,
      FractionalIdeal.spanSingleton_one, one_mul]
  refine ⟨(D.den : 𝓞 E), D.num, nonZeroDivisors.coe_ne_zero _, ?_, ?_⟩
  · intro h
    apply hD
    rw [← FractionalIdeal.num_eq_zero_iff]
    exact h
  · intro z
    rw [hmem]
    constructor
    · intro hz
      have h1 : d * z ∈ (D.num : FractionalIdeal (𝓞 E)⁰ E) := by
        rw [← key]
        exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hz
      obtain ⟨j, hj, hjeq⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
      refine ⟨j, hj, ?_⟩
      have h2 : (j : E) = d * z := hjeq
      have h3 : ((D.den : 𝓞 E) : E) = d := rfl
      rw [h3, h2, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
    · rintro ⟨j, hj, hz⟩
      have h4 : d⁻¹ * (j : E) ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ * (D.num : FractionalIdeal (𝓞 E)⁰ E) :=
        FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
          ((FractionalIdeal.mem_coeIdeal _).2 ⟨j, hj, rfl⟩)
      rw [← key2] at h4
      rw [hz]
      exact h4

theorem pCodiffGen : CodiffGen := by
  unfold CodiffGen
  intro E _ _ M hM
  classical
  obtain ⟨a, J, ha, hJ, hcod⟩ := exists_ideal E
  have hM0 : ((M : 𝓞 E)) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hI0 : J * Ideal.span {(M : 𝓞 E)} ≠ 0 := by
    refine mul_ne_zero (show J ≠ 0 from hJ) ?_
    intro h
    exact hM0 (Ideal.span_singleton_eq_bot.1 h)
  have hle : J * Ideal.span {(M : 𝓞 E)} ≤ J := Ideal.mul_le.2 fun r hr s _ => J.mul_mem_right s hr
  obtain ⟨j, hj⟩ := IsDedekindDomain.exists_sup_span_eq hle hI0
  have hjJ : j ∈ J := by
    rw [← hj]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self j)
  obtain ⟨K, hK⟩ : J ∣ Ideal.span {j} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hjJ)
  have hKM : K ⊔ Ideal.span {(M : 𝓞 E)} = ⊤ := by
    have h1 : J * (Ideal.span {(M : 𝓞 E)} ⊔ K) = J * ⊤ := by
      rw [Ideal.mul_sup, ← hK, hj, Ideal.mul_top]
    rw [sup_comm]
    exact mul_left_cancel₀ (show J ≠ 0 from hJ) h1
  set e := Ideal.absNorm K with hedef
  have heK : (e : 𝓞 E) ∈ K := Ideal.absNorm_mem K
  refine ⟨(a : E)⁻¹ * (j : E), (hcod _).2 ⟨j, hjJ, rfl⟩, e, ?_, ?_⟩
  · refine Nat.coprime_of_dvd fun q hq hqe hqM => ?_
    have hMq : (M : 𝓞 E) ∈ Ideal.span {(q : 𝓞 E)} :=
      Ideal.mem_span_singleton.2 (Nat.cast_dvd_cast hqM)
    have hKq : K ⊔ Ideal.span {(q : 𝓞 E)} = ⊤ := by
      rw [eq_top_iff, ← hKM]
      exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 hMq) K
    have h1 : (1 : 𝓞 E) ∈ K ⊔ Ideal.span {(q : 𝓞 E)} := by rw [hKq]; trivial
    obtain ⟨k, hk, m, hm, hkm⟩ := Submodule.mem_sup.1 h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hm
    by_cases hK0 : K = ⊥
    · subst hK0
      have hk0 : k = 0 := (Submodule.mem_bot _).1 hk
      rw [hk0, zero_add] at hkm
      have hunit : IsUnit (q : 𝓞 E) := isUnit_iff_exists_inv.2 ⟨t, by rw [mul_comm]; exact hkm⟩
      have htop : Ideal.span {(q : 𝓞 E)} = ⊤ := Ideal.span_singleton_eq_top.2 hunit
      have hn := Ideal.absNorm_span_natCast (S := 𝓞 E) q
      rw [htop, Ideal.absNorm_top] at hn
      have hpos : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
      rcases (Nat.pow_eq_one.1 hn.symm) with h | h
      · exact hq.ne_one h
      · omega
    · haveI : Finite (𝓞 E ⧸ K) := Ideal.finiteQuotientOfFreeOfNeBot K hK0
      haveI : Fact q.Prime := ⟨hq⟩
      have hcard : q ∣ Nat.card (𝓞 E ⧸ K) := by
        rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
        exact hqe
      obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hcard
      have hqx : (q : 𝓞 E ⧸ K) * x = 0 := by
        rw [← nsmul_eq_mul, ← hx]
        exact addOrderOf_nsmul_eq_zero x
      have hu : (q : 𝓞 E ⧸ K) * Ideal.Quotient.mk K t = 1 := by
        have := congrArg (Ideal.Quotient.mk K) hkm
        rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hk, zero_add, map_mul, map_one, map_natCast] at this
        rw [mul_comm]
        exact this
      have hx0 : x = 0 := by
        linear_combination (-x) * hu + (Ideal.Quotient.mk K t) * hqx
      rw [hx0, addOrderOf_zero] at hx
      exact hq.one_lt.ne hx
  · intro z hz
    obtain ⟨j', hj', rfl⟩ := (hcod z).1 hz
    have hmem : j' * (e : 𝓞 E) ∈ Ideal.span {j} := by
      rw [hK]
      exact Ideal.mul_mem_mul hj' heK
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨x, ?_⟩
    have hcast : ((x : E) * (j : E)) = (j' : E) * (e : E) := by
      have := congrArg (fun w : 𝓞 E => (w : E)) hx
      simpa using this
    linear_combination (-(a : E)⁻¹) * hcast

end UpperTheory.Gal.W2.Seed
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDeltaEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pDeltaEx :
    DeltaEx := by
  intro E _ _ _ bar hbar ω tr nm htr hnm hD M hcop t ht hgen hpos τ₀
  obtain ⟨hti, e, he, hez⟩ := hgen
  have hbω : bar ω = (tr : 𝓞 E) - ω := eq_sub_of_add_eq' htr
  have hnm' : ω * ((tr : 𝓞 E) - ω) = (nm : 𝓞 E) := by rw [← hbω]; exact hnm
  set u : 𝓞 E := 2 * ω - (tr : 𝓞 E) with hu
  set D : ℤ := tr ^ 2 - 4 * nm with hDdef
  have huu : u * u = (D : 𝓞 E) := by
    rw [hu, hDdef]; push_cast; linear_combination (-4 : 𝓞 E) * hnm'
  have huuE : (u : E) * (u : E) = (D : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) huu
    simpa using this
  have huE : (u : E) = 2 * (ω : E) - (tr : E) := by
    rw [hu]; norm_cast
  have h1 : (IsCMField.complexConj E) (ω : E) = (tr : E) - ω := by
    rw [← hbar ω, hbω]; norm_cast
  have hconj : (IsCMField.complexConj E) (u : E) = -(u : E) := by
    rw [huE, map_sub, map_mul, h1, map_intCast, map_ofNat]; ring
  have hτu : ∀ τ : E →+* ℂ, (τ u).re = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj E τ (u : E)
    rw [hconj, map_neg] at h
    have h2 := congrArg Complex.re h
    simp at h2
    linarith
  have hτt : ∀ τ : E →+* ℂ, (τ t).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj E τ t
    rw [ht] at h
    have h2 := congrArg Complex.im h
    simp at h2
    linarith
  have hu0 : (τ₀ u).im ≠ 0 := by
    intro h
    have h0 : τ₀ u = 0 := Complex.ext (hτu τ₀) h
    have h3 := congrArg τ₀ huuE
    rw [map_mul, h0, zero_mul, map_intCast] at h3
    have : D = 0 := by exact_mod_cast h3.symm
    linarith
  obtain ⟨c, hc, hcs⟩ : ∃ c : ℤ, c * c = 1 ∧ (c : ℝ) * (τ₀ u).im < 0 := by
    rcases lt_or_gt_of_ne hu0 with h | h
    · exact ⟨1, by norm_num, by simpa using h⟩
    · exact ⟨-1, by norm_num, by simpa using h⟩
  have hcE : (c : E) * (c : E) = 1 := by exact_mod_cast hc
  have hDabs : ((D.natAbs : ℕ) : E) = -((u : E) * (u : E)) := by
    rw [huuE]
    have : ((D.natAbs : ℕ) : ℤ) = -D := Int.ofNat_natAbs_of_nonpos hD.le
    have h2 := congrArg (fun k : ℤ => (k : E)) this
    simpa using h2
  refine ⟨(c : E) * t * u, ?_, ⟨?_, e * D.natAbs, ?_, ?_⟩, ?_⟩
  · rw [map_mul, map_mul, map_intCast, ht, hconj]; ring
  · intro x
    obtain ⟨m, hm⟩ := hti ((c : 𝓞 E) * u * x)
    refine ⟨m, ?_⟩
    have hcast : (((c : 𝓞 E) * u * x : 𝓞 E) : E) = (c : E) * u * x := by norm_cast
    rw [hcast] at hm
    rw [← hm]; congr 1; ring
  · have h2 : Int.gcd D (M : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
    have h3 : Nat.Coprime D.natAbs M := by
      simpa [Int.gcd, Nat.Coprime] using h2
    exact Nat.Coprime.mul_left he h3
  · intro z hz
    obtain ⟨x, hx⟩ := hez z hz
    refine ⟨-(c : 𝓞 E) * u * x, ?_⟩
    have hcast : ((-(c : 𝓞 E) * u * x : 𝓞 E) : E) = -(c : E) * u * x := by norm_cast
    rw [hcast]
    push_cast
    linear_combination ((D.natAbs : ℕ) : E) * hx + (t * (x : E)) * hDabs + (t * (u : E) * (u : E) * (x : E)) * hcE
  · intro τ hτ
    have hτu' : τ u = τ₀ u := by
      rw [huE, map_sub, map_mul, map_sub, map_mul, hτ, map_intCast, map_intCast, map_ofNat, map_ofNat]
    rw [map_mul, map_mul, map_intCast, hτu']
    simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, hτt τ, hτu τ₀]
    nlinarith [mul_neg_of_pos_of_neg (hpos τ) hcs]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDiagTrace
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pDiagTrace :
    DiagTrace := by
  intro I _ a M hM
  classical
  have hdec : M = ∑ k, (LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ
      ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k) := by
    refine LinearMap.ext fun z => funext fun j => ?_
    simp [hM, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]
  have hk : ∀ k : I, LinearMap.trace ℝ (I → ℂ) ((LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ
      ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k)) = 2 * (a k).re := by
    intro k
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.proj_comp_single_same,
      LinearMap.comp_id, ← Algebra.trace_complex_apply, Algebra.trace_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdec, map_sum, Finset.sum_congr rfl (fun k _ => hk k), Complex.re_sum, Finset.mul_sum]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormCoord
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pFormCoord :
    TraceType → FormCoord := by
  intro hT E _ _ _ A n Θ hΘ x y
  classical
  have hconj : ∀ (τ : E →+* ℂ) (b : 𝓞 E),
      τ ((A.bar b : 𝓞 E) : E) = (starRingEnd ℂ) (τ (b : E)) := fun τ b => by
    rw [A.bar_eq, IsCMField.complexEmbedding_complexConj]
  have hkey : ∀ a b : Fin n → 𝓞 E, ((A.EF n a b : ℤ) : ℝ) =
      ∑ k : Phi A × Fin n, 2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * k.1.1 (a k.2 : E) *
        (starRingEnd ℂ) (k.1.1 (b k.2 : E))).re := by
    intro a b
    have h1 : ((A.EF n a b : ℤ) : ℝ) =
        ((Algebra.trace ℚ E (A.δ * ((∑ i, A.hd n i * a i * A.bar (b i) : 𝓞 E) : E)) : ℚ) : ℝ) := by
      rw [← A.trd_spec, A.EF_apply]; norm_cast
    rw [h1, (hT E A).1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h2 : ((∑ i, A.hd n i * a i * A.bar (b i) : 𝓞 E) : E) =
        ∑ i, ((A.hd n i : 𝓞 E) : E) * (a i : E) * ((A.bar (b i) : 𝓞 E) : E) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simpa using map_sum (algebraMap (𝓞 E) E) (fun i => A.hd n i * a i * A.bar (b i)) Finset.univ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_mul, map_sum, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, hconj, mul_assoc]
  have hx : ∀ (r : ℝ) (a : Fin n → 𝓞 E) (k : Phi A × Fin n),
      Θ (r ⊗ₜ[ℤ] a) k = (r : ℂ) * k.1.1 (a k.2 : E) := by
    rintro r a ⟨τ, i⟩
    have h : r ⊗ₜ[ℤ] a = r • ((1 : ℝ) ⊗ₜ[ℤ] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, Pi.smul_apply, hΘ, Complex.real_smul]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add (f := _), LinearMap.add_apply, h₁, h₂, Pi.add_apply, mul_add, add_mul, Complex.add_re,
      Finset.sum_add_distrib]
  | tmul r a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add (f := _), h₁, h₂, Pi.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib]
    | tmul s b =>
      rw [LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul, hkey, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hx, hx, map_mul, Complex.conj_ofReal]
      have h : k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * ((r : ℂ) * k.1.1 (a k.2 : E)) *
          ((s : ℂ) * (starRingEnd ℂ) (k.1.1 (b k.2 : E))) =
          ((r * s : ℝ) : ℂ) * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * k.1.1 (a k.2 : E) *
            (starRingEnd ℂ) (k.1.1 (b k.2 : E))) := by
        push_cast; ring
      rw [h, Complex.re_ofReal_mul]; ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLiftEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pLiftEx :
    LiftEx := by
  unfold UpperTheory.Gal.W2.Seed.LiftEx
  intro E _ _ τ₀
  let sA : E →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra E (AlgebraicClosure ℚ) := sA.toRingHom.toAlgebra
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (sA.commutes x).symm)
  haveI hQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic E (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let iA : AlgebraicClosure ℚ →ₐ[E] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨sA.toRingHom, iA.toRingHom, fun x => ?_⟩
  exact iA.commutes x
end

