module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewFamilyEqOfStrictLowerOfDiagIm
section
open scoped ComplexConjugate

namespace GlobalTheory

theorem skewFamily_eq_of_strictLower_of_diagIm
    {ι : Type} [Fintype ι] {r : ℕ} (s : Fin r → ℝ) (hs : ∀ a, s a * s a = 1)
    (Y Y' : ι × Fin r × Fin r → ℂ)
    (hY : ∀ τ a b, Y (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y (τ, a, b)))
    (hYt : ∀ τ, ∑ a, Y (τ, a, a) = 0)
    (hY' : ∀ τ a b, Y' (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y' (τ, a, b)))
    (hY't : ∀ τ, ∑ a, Y' (τ, a, a) = 0)
    (hlt : ∀ τ a b, b < a → Y (τ, a, b) = Y' (τ, a, b))
    (him : ∀ τ (a : Fin r), (a : ℕ) + 1 < r → (Y (τ, a, a)).im = (Y' (τ, a, a)).im) :
    Y = Y' := by
  have hre : ∀ (Z : ι × Fin r × Fin r → ℂ),
      (∀ τ a b, Z (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Z (τ, a, b))) →
      ∀ τ a, (Z (τ, a, a)).re = 0 := by
    intro Z hZ τ a
    have h := hZ τ a a
    rw [hs a] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.ofReal_one, neg_mul, one_mul, Complex.neg_re, Complex.conj_re] at h2
    linarith
  have hoff : ∀ τ (c : Fin r), (c : ℕ) + 1 < r → Y (τ, c, c) = Y' (τ, c, c) :=
    fun τ c hc => Complex.ext (by rw [hre Y hY τ c, hre Y' hY' τ c]) (him τ c hc)
  have hdiag : ∀ τ (a : Fin r), Y (τ, a, a) = Y' (τ, a, a) := by
    intro τ a
    by_cases ha : (a : ℕ) + 1 < r
    · exact hoff τ a ha
    · have hsum : ∀ c ∈ Finset.univ.erase a, Y (τ, c, c) = Y' (τ, c, c) := by
        intro c hc
        apply hoff
        have hca : c ≠ a := Finset.ne_of_mem_erase hc
        have hcv : (c : ℕ) ≠ a := fun h => hca (Fin.ext h)
        have := c.isLt
        have := a.isLt
        omega
      have e1 : Y (τ, a, a) + ∑ c ∈ Finset.univ.erase a, Y (τ, c, c) = 0 := by
        exact (Finset.add_sum_erase Finset.univ (fun c => Y (τ, c, c)) (Finset.mem_univ a)).trans (hYt τ)
      have e2 : Y' (τ, a, a) + ∑ c ∈ Finset.univ.erase a, Y' (τ, c, c) = 0 := by
        exact (Finset.add_sum_erase Finset.univ (fun c => Y' (τ, c, c)) (Finset.mem_univ a)).trans (hY't τ)
      rw [Finset.sum_congr rfl hsum] at e1
      linear_combination e1 - e2
  funext p
  obtain ⟨τ, a, b⟩ := p
  rcases lt_trichotomy a b with h | rfl | h
  · rw [hY τ b a, hY' τ b a, hlt τ b a h]
  · exact hdiag τ a
  · exact hlt τ a b h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewFamilyInnerReEqStrictLowerAddDiagIm
section
open scoped ComplexConjugate

namespace GlobalTheory

theorem skew_family_inner_re_split : ∀ {ι : Type} [Fintype ι] {r : ℕ} (s : Fin r → ℝ), (∀ a, s a * s a = 1) → ∀ (Y Y' : ι × Fin r × Fin r → ℂ), (∀ τ a b, Y (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y (τ, a, b))) → (∀ τ a b, Y' (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y' (τ, a, b))) → ∑ p, (conj (Y p) * Y' p).re = 2 * ∑ q : ι × {p : Fin r × Fin r // p.2 < p.1}, (conj (Y (q.1, q.2.1.1, q.2.1.2)) * Y' (q.1, q.2.1.1, q.2.1.2)).re + ∑ τ, ∑ a, (Y (τ, a, a)).im * (Y' (τ, a, a)).im := by
  intro ι _ r s hs Y Y' hY hY'
  set F : ι → Fin r → Fin r → ℝ := fun τ a b => (conj (Y (τ, a, b)) * Y' (τ, a, b)).re with hF
  have key : ∀ τ a b, F τ b a = F τ a b := by
    intro τ a b
    have h2 : (s a * s b) * (s a * s b) = 1 := by rw [mul_mul_mul_comm, hs, hs, one_mul]
    simp only [hF, hY τ a b, hY' τ a b, map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal,
      Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, Complex.mul_im, Complex.neg_im]
    linear_combination ((Y (τ, a, b)).re * (Y' (τ, a, b)).re + (Y (τ, a, b)).im * (Y' (τ, a, b)).im) * h2
  have diag : ∀ τ a, F τ a a = (Y (τ, a, a)).im * (Y' (τ, a, a)).im := by
    intro τ a
    have h1 := congrArg Complex.re (hY τ a a)
    have h2 := congrArg Complex.re (hY' τ a a)
    simp only [hs, Complex.ofReal_one, Complex.neg_re, Complex.mul_re, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_im] at h1 h2
    simp only [hF, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have e1 : (Y (τ, a, a)).re = 0 := by linarith
    rw [e1]; ring
  have per : ∀ τ, ∑ a, ∑ b, F τ a b
      = 2 * ∑ p : {p : Fin r × Fin r // p.2 < p.1}, F τ p.1.1 p.1.2 + ∑ a, F τ a a := by
    intro τ
    have hsplit : ∀ a b, F τ a b = ((if b < a then F τ a b else 0) + (if a < b then F τ a b else 0))
        + (if a = b then F τ a b else 0) := by
      intro a b
      rcases lt_trichotomy a b with h | rfl | h
      · simp [h, not_lt_of_gt h, h.ne]
      · simp
      · simp [h, not_lt_of_gt h, h.ne']
    have hsub : ∑ p : {p : Fin r × Fin r // p.2 < p.1}, F τ p.1.1 p.1.2
        = ∑ a, ∑ b, if b < a then F τ a b else 0 := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin r × Fin r => p.2 < p.1)) (by simp)
        (fun p : Fin r × Fin r => F τ p.1 p.2), Finset.sum_filter, Fintype.sum_prod_type]
    have hsym : (∑ a, ∑ b, if a < b then F τ a b else 0) = ∑ a, ∑ b, if b < a then F τ a b else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [key]
    have hdiag : (∑ a, ∑ b, if a = b then F τ a b else 0) = ∑ a, F τ a a := by
      simp
    calc ∑ a, ∑ b, F τ a b
        = ∑ a, ∑ b, (((if b < a then F τ a b else 0) + (if a < b then F τ a b else 0))
            + (if a = b then F τ a b else 0)) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsplit a b))
      _ = ((∑ a, ∑ b, if b < a then F τ a b else 0) + (∑ a, ∑ b, if a < b then F τ a b else 0))
            + ∑ a, ∑ b, if a = b then F τ a b else 0 := by
          simp only [Finset.sum_add_distrib]
      _ = _ := by rw [hsym, hdiag, hsub]; ring
  have lhs : ∑ p, (conj (Y p) * Y' p).re = ∑ τ, ∑ a, ∑ b, F τ a b := by
    simp only [hF, Fintype.sum_prod_type]
  rw [lhs, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [per τ]
  simp only [diag]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianPerturbIdempotentDetNeZero
section
open scoped Matrix

namespace GlobalTheory

theorem skewHermitian_perturb_idempotent_det_ne_zero :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (E D : Matrix (Fin n) (Fin n) k), E * E = E → (E.map σ)ᵀ = E → E * (D.map σ)ᵀ + D * E = 0 →
    (∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (E * V + D).det ≠ 0 := by
  intro k _ σ hσ ε hε hσε n E D hEE hEh hED hrank
  have h1 : E * (D.map σ)ᵀ = -(D * E) := eq_neg_of_add_eq_zero_left hED
  have h2 : E * (D.map σ)ᵀ = -(E * D * E) := by
    calc E * (D.map σ)ᵀ = E * (E * (D.map σ)ᵀ) := by rw [← Matrix.mul_assoc, hEE]
      _ = E * (-(D * E)) := by rw [h1]
      _ = -(E * D * E) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
  have hDE : D * E = E * D * E := by
    have := h1.symm.trans h2
    exact neg_inj.mp this
  have h3 : E * (D.map σ)ᵀ * E = -(E * D * E) := by
    rw [h2, Matrix.neg_mul, Matrix.mul_assoc (E * D) E E, hEE]
  have hV : E * (ε • (1 : Matrix (Fin n) (Fin n) k) - D) * E = ε • E - E * D * E := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hEE]
  refine ⟨E * (ε • 1 - D) * E, ?_, ?_⟩
  · rw [hV]
    have hm : ((ε • E - E * D * E).map σ)ᵀ = (σ ε) • (E.map σ)ᵀ - (E.map σ)ᵀ * (D.map σ)ᵀ * (E.map σ)ᵀ := by
      ext i j
      have hs : ((ε • E).map σ)ᵀ = σ ε • (E.map σ)ᵀ := by
        ext i j
        simp
      rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_sub, Matrix.transpose_mul,
        Matrix.transpose_mul, ← Matrix.mul_assoc, hs]
    rw [hm, hEh, h3, hσε, neg_smul, sub_neg_eq_add, neg_sub]
    abel
  · have hM : E * (E * (ε • 1 - D) * E) + D = ε • E - E * D * E + D := by
      rw [hV, Matrix.mul_sub, Matrix.mul_smul, hEE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hEE]
    rw [hM]
    have hME : (ε • E - E * D * E + D) * E = ε • E := by
      rw [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, hEE, Matrix.mul_assoc (E * D) E E, hEE, hDE]
      abel
    intro hdet
    obtain ⟨a, ha0, ha⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have haE : a ᵥ* E = 0 := by
      have : a ᵥ* ((ε • E - E * D * E + D) * E) = 0 := by rw [← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
      rw [hME, Matrix.vecMul_smul] at this
      exact (smul_eq_zero.mp this).resolve_left hε
    have haD : a ᵥ* D = 0 := by
      have hx : a ᵥ* (E * D * E) = 0 := by
        rw [Matrix.mul_assoc, ← Matrix.vecMul_vecMul, haE, Matrix.zero_vecMul]
      rw [Matrix.vecMul_add, Matrix.vecMul_sub, Matrix.vecMul_smul, haE, hx] at ha
      simpa using ha
    exact ha0 (hrank a haE haD)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRangeOfIdempotentAlgHom
section
namespace GlobalTheory

theorem idempotent_algHom_ker_fg {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (e : A →ₐ[R] A) (he : ∀ x, e (e x) = e x) :
    (RingHom.ker e.rangeRestrict.toRingHom).FG := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)
  refine ⟨s.image (fun x => x - e x), ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨x, _, rfl⟩
    change e.rangeRestrict (x - e x) = 0
    apply Subtype.ext
    simp [he]
  · intro b hb
    have hb' : e b = 0 := by
      have := congrArg Subtype.val (show e.rangeRestrict b = 0 from hb)
      simpa using this
    have key : ∀ y : A, y - e y ∈ Ideal.span ((fun x => x - e x) '' (s : Set A)) := by
      intro y
      have hy : y ∈ Algebra.adjoin R (s : Set A) := by rw [hs]; exact Algebra.mem_top
      induction hy using Algebra.adjoin_induction with
      | mem x hx => exact Ideal.subset_span ⟨x, hx, rfl⟩
      | algebraMap r => simp
      | add x y _ _ hx hy =>
        have h : x + y - e (x + y) = (x - e x) + (y - e y) := by rw [map_add (f := _)]; ring
        rw [h]; exact Ideal.add_mem _ hx hy
      | mul x y _ _ hx hy =>
        have h : x * y - e (x * y) = x * (y - e y) + e y * (x - e x) := by rw [map_mul]; ring
        rw [h]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hx)
    simpa [hb'] using key b

theorem smooth_range_of_idempotent : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (e : A →ₐ[R] A), (∀ x, e (e x) = e x) → Algebra.Smooth R e.range := by
  intro R A _ _ _ _ e he
  have hq : ∀ b : e.range, e.rangeRestrict (b : A) = b := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    simp [he]
  have hsurj : Function.Surjective e.rangeRestrict := fun b => ⟨b, hq b⟩
  refine { formallySmooth := ?_, finitePresentation := ?_ }
  · refine Algebra.FormallySmooth.of_split e.rangeRestrict
      ((Ideal.Quotient.mkₐ R _).comp e.range.val) ?_
    ext b
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_id, id_eq,
      Subalgebra.coe_val]
    rw [AlgHom.kerSquareLift_mk, hq]
  · exact Algebra.FinitePresentation.of_surjective hsurj (idempotent_algHom_ker_fg e he)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfMaximalIdealPowOfLocallySurjective
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem smul_mem_of_maximalIdeal_pow_of_locally_eq :
    ∀ (R B : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup B] [Module R B]
      [Module.Finite R B] (N : Submodule R B),
      (∀ (p : Ideal R), p.IsPrime → p ≠ maximalIdeal R → ∀ b : B, ∃ t ∉ p, t • b ∈ N) →
      ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ N := by
  intro R B _ _ _ _ _ _ N h
  classical
  set J : Ideal R := N.colon (Set.univ : Set B) with hJ
  have hmem : ∀ r : R, r ∈ J ↔ ∀ b : B, r • b ∈ N := by
    intro r
    rw [hJ, Submodule.mem_colon]
    simp
  have hrad : maximalIdeal R ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro p ⟨hJp, hp⟩
    by_cases hpm : p = maximalIdeal R
    · exact hpm.ge
    exfalso
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R B).FG)
    have hg : ∀ g : B, ∃ t ∉ p, t • g ∈ N := h p hp hpm
    choose t ht1 ht2 using hg
    set u : R := ∏ g ∈ s, t g with hu
    have hu_notin : u ∉ p := by
      rw [hu, Ideal.IsPrime.prod_mem_iff]
      rintro ⟨i, -, hi⟩
      exact ht1 i hi
    apply hu_notin
    apply hJp
    rw [hmem]
    intro b
    have hb : b ∈ Submodule.span R (s : Set B) := by rw [hs]; trivial
    have hle : Submodule.span R (s : Set B) ≤ N.comap (u • LinearMap.id) := by
      rw [Submodule.span_le]
      intro g hgs
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hu, ← Finset.prod_erase_mul s t hgs, mul_smul]
      exact N.smul_mem _ (ht2 g)
    have := hle hb
    simpa using this
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian (maximalIdeal R))
  exact ⟨k, fun x hx b => (hmem x).1 (hk hx) b⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndEqSum
section
namespace GlobalTheory.SecondComponentSum

theorem snd_eq_sum {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k])
    (hB : ∀ i : Fin D, B i = KaehlerDifferential.D k A (f i))
    {K : Type} [Field K] (θ : A →+* DualNumber K)
    (hθ : ∀ a : k, TrivSqZeroExt.snd (θ (algebraMap k A a)) = (0 : K)) (s : A) :
    TrivSqZeroExt.snd (θ s) = ∑ b : Fin D, TrivSqZeroExt.snd (θ (f b)) *
      TrivSqZeroExt.fst (θ ((LinearMap.compDer (Module.Basis.coord B b)
        (KaehlerDifferential.D k A)) s)) := by
  classical

  let φ : A →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom.comp θ
  let _ : Module A K := Module.compHom K φ
  let _ : Module k K := Module.compHom K (φ.comp (algebraMap k A))
  have : IsScalarTower k A K := ⟨fun c a x => by
    change φ (c • a) * x = φ (algebraMap k A c) * (φ a * x)
    rw [Algebra.smul_def, map_mul, mul_assoc]⟩
  have hsmul : ∀ (a : A) (x : K), a • x = TrivSqZeroExt.fst (θ a) * x := fun _ _ => rfl
  have hsndmul : ∀ a b : A, TrivSqZeroExt.snd (θ (a * b)) =
      TrivSqZeroExt.fst (θ a) * TrivSqZeroExt.snd (θ b) +
        TrivSqZeroExt.snd (θ a) * TrivSqZeroExt.fst (θ b) := by
    intro a b
    rw [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul]
  let ℓ : A →ₗ[k] K :=
    { toFun := fun a => TrivSqZeroExt.snd (θ a)
      map_add' := fun a b => by
        simp only [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun c a => by
        change TrivSqZeroExt.snd (θ (c • a)) = φ (algebraMap k A c) * TrivSqZeroExt.snd (θ a)
        rw [Algebra.smul_def, hsndmul, hθ, zero_mul, add_zero]
        rfl }
  let d : Derivation k A K := Derivation.mk' ℓ fun a b => by
    change TrivSqZeroExt.snd (θ (a * b)) = TrivSqZeroExt.fst (θ a) * TrivSqZeroExt.snd (θ b) +
      TrivSqZeroExt.fst (θ b) * TrivSqZeroExt.snd (θ a)
    rw [hsndmul, mul_comm (TrivSqZeroExt.snd (θ a))]

  have key := congrArg d.liftKaehlerDifferential (B.sum_repr (KaehlerDifferential.D k A s))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Derivation.liftKaehlerDifferential_comp_D, map_sum] at key
  change d s = _
  rw [← key]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.map_smul, hB, Derivation.liftKaehlerDifferential_comp_D, hsmul, mul_comm]
  rfl

end GlobalTheory.SecondComponentSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCoeffProdLinear
section
open MvPolynomial

namespace GlobalTheory
namespace GaussContentLinearForms

variable {V : Type} [CommRing V] {σ : Type}

theorem span_coeff_C_mul (a : V) (f : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (C a * f).coeff s) =
      Ideal.span {a} * Ideal.span (Set.range fun s => f.coeff s) := by
  rw [Ideal.span_mul_span]
  congr 1
  ext x
  simp only [coeff_C_mul, Set.mem_range, Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨a, rfl, _, ⟨s, rfl⟩, rfl⟩
  · rintro ⟨b, rfl, y, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, rfl⟩

theorem span_coeff_eq_top_iff [IsLocalRing V] (f : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => f.coeff s) = ⊤ ↔
      MvPolynomial.map (IsLocalRing.residue V) f ≠ 0 := by
  have h1 : MvPolynomial.map (IsLocalRing.residue V) f = 0 ↔
      Ideal.span (Set.range fun s => f.coeff s) ≤ IsLocalRing.maximalIdeal V := by
    rw [Ideal.span_le, Set.range_subset_iff, MvPolynomial.ext_iff]
    refine forall_congr' fun s => ?_
    rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      IsLocalRing.residue_eq_zero_iff]
    rfl
  rw [ne_eq, h1]
  constructor
  · intro h h'
    rw [h, top_le_iff] at h'
    exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top h'
  · intro h
    by_contra h'
    exact h (IsLocalRing.le_maximalIdeal h')

theorem span_coeff_one :
    Ideal.span (Set.range fun s => (1 : MvPolynomial σ V).coeff s) = ⊤ := by
  classical
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨0, by simp⟩

theorem exists_primitive_part [IsDomain V] [IsDiscreteValuationRing V] (f : MvPolynomial σ V) :
    ∃ (a : V) (g : MvPolynomial σ V), f = C a * g ∧
      Ideal.span (Set.range fun s => g.coeff s) = ⊤ := by
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal
    (Ideal.span (Set.range fun s => f.coeff s))).principal
  have ha' : Ideal.span (Set.range fun s => f.coeff s) = Ideal.span {a} := ha
  have hd : C a ∣ f := by
    rw [C_dvd_iff_dvd_coeff]
    intro s
    rw [← Ideal.mem_span_singleton, ← ha']
    exact Ideal.subset_span ⟨s, rfl⟩
  obtain ⟨g, rfl⟩ := hd
  by_cases h0 : a = 0
  · exact ⟨0, 1, by simp [h0], span_coeff_one⟩
  · refine ⟨a, g, rfl, ?_⟩
    rw [span_coeff_C_mul] at ha'
    have hne : Ideal.span {a} ≠ (0 : Ideal V) := by
      rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
      exact h0
    apply mul_left_cancel₀ hne
    rw [ha', Ideal.mul_top]

theorem span_coeff_mul [IsDomain V] [IsDiscreteValuationRing V] (f g : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (f * g).coeff s) =
      Ideal.span (Set.range fun s => f.coeff s) * Ideal.span (Set.range fun s => g.coeff s) := by
  obtain ⟨a, f', rfl, hf⟩ := exists_primitive_part f
  obtain ⟨b, g', rfl, hg⟩ := exists_primitive_part g
  have hfg : Ideal.span (Set.range fun s => (f' * g').coeff s) = ⊤ := by
    rw [span_coeff_eq_top_iff] at hf hg ⊢
    rw [map_mul]
    exact mul_ne_zero hf hg
  have e : C a * f' * (C b * g') = C (a * b) * (f' * g') := by
    rw [map_mul]; ring
  rw [e, span_coeff_C_mul, span_coeff_C_mul, span_coeff_C_mul, hf, hg, hfg, Ideal.mul_top,
    Ideal.mul_top, Ideal.mul_top, Ideal.span_singleton_mul_span_singleton]

theorem span_coeff_prod [IsDomain V] [IsDiscreteValuationRing V] {ι : Type} (t : Finset ι)
    (f : ι → MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (∏ j ∈ t, f j).coeff s) =
      ∏ j ∈ t, Ideal.span (Set.range fun s => (f j).coeff s) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, span_coeff_one, Ideal.one_eq_top]
  | insert j t hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, span_coeff_mul, ih]

theorem span_coeff_linear {m : ℕ} (c : Fin m → V) :
    Ideal.span (Set.range fun s => (∑ i, C (c i) * X i : MvPolynomial (Fin m) V).coeff s) =
      Ideal.span (Set.range c) := by
  classical
  apply le_antisymm
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro s
    simp only [coeff_sum, coeff_C_mul, SetLike.mem_coe]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_mono
    rintro _ ⟨i, rfl⟩
    refine ⟨Finsupp.single i 1, ?_⟩
    simp only [coeff_sum, coeff_C_mul, coeff_X]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [ite_eq_right, mul_zero]
      intro h
      exact hj (Finsupp.single_left_injective one_ne_zero h)
    · simp

theorem span_coeff_prod_linear (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (d m : ℕ) (c : Fin d → Fin m → V) :
    Ideal.span (Set.range fun s =>
        (∏ j, ∑ i, C (c j i) * X i : MvPolynomial (Fin m) V).coeff s) =
      ∏ j, Ideal.span (Set.range (c j)) := by
  rw [span_coeff_prod]
  exact Finset.prod_congr rfl fun j _ => span_coeff_linear (c j)

end GaussContentLinearForms
end GlobalTheory
end

