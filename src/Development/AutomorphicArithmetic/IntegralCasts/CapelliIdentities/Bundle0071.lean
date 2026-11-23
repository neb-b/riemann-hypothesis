module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import GroundTheory.PAdicHodge.BdRAlg
public import GroundTheory.PAdicHodge.FactorizationFactorialLe
public import GroundTheory.PAdicHodge.PerfectoidField
public import GroundTheory.PAdicHodge.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjEmbeddingRt
section
theorem UpperTheory.Reformulated.B.Gc4.conj_embedding_rt :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ),
    (starRingEnd ℂ : ℂ → ℂ) ((τ : E → ℂ) (↑H.rt : E)) =
      -(τ : E → ℂ)
          (↑H.rt :
            E) := by
  intro E _ _ _ H τ
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (NumberField.RingOfIntegers E) E) H.rt_sq
  have h2 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, h1, map_neg, map_natCast]
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  generalize τ (H.rt : E) = z at h2 ⊢
  have hre : z.re * z.re - z.im * z.im = -(H.d : ℝ) := by simpa [sq] using congrArg Complex.re h2
  have him : z.re * z.im + z.im * z.re = 0 := by simpa [sq] using congrArg Complex.im h2
  have hz : z.im ≠ 0 := fun h => by rw [h] at hre; nlinarith [mul_self_nonneg z.re]
  have h0 : z.re = 0 := mul_right_cancel₀ hz (by linarith)
  apply Complex.ext <;> simp [h0]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZero
section
theorem UpperTheory.Reformulated.B.ComplexConjugateRootEqNeg.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re * H.rt0.im = 0 := by linarith
  have hr : H.rt0.re = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext
  · rw [Complex.conj_re, Complex.neg_re, hr, neg_zero]
  · rw [Complex.conj_im, Complex.neg_im]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZeroSecond
section
theorem UpperTheory.Reformulated.B.ConjugateRootZeroSecond.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have him0 : H.rt0.im = 0 := by
      have hm : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.mp hm).resolve_left hne
    rw [him0] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZeroThird
section
theorem UpperTheory.Reformulated.B.StarRingEndRootEqNeg.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    simpa [pow_two, Complex.mul_re] using congrArg Complex.re h
  have him : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    simpa [pow_two, Complex.mul_im] using congrArg Complex.im h
  have ha : H.rt0.re = 0 := by
    by_contra ha
    have hm : H.rt0.re * H.rt0.im = 0 := by linarith
    have hb : H.rt0.im = 0 := (mul_eq_zero.mp hm).resolve_left ha
    rw [hb] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext
  · simp [ha]
  · simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CubicCharpolyDiscriminant
section
open Matrix Polynomial UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.Reformulated.B.CubicCharpolyDiscriminant

private lemma charpoly_three {R : Type} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M.charpoly = X ^ 3 - C M.trace * X ^ 2 + C M.adjugate.trace * X - C M.det := by
  simp [Matrix.charpoly, Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.adjugate_fin_three,
    Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne]
  ring

private lemma charpoly_tw {R : Type} [CommRing R] [StarRing R] (A M : Matrix (Fin 3) (Fin 3) R)
    (hA : A * star A = 1) (hM : M * star M = 1) (h : M = A * A.map star) :
    star M.trace = M.trace ∧ M.charpoly = (X - 1) * (X ^ 2 - C (M.trace - 1) * X + 1) := by
  have h1 : star M.trace = M.trace := by
    subst h
    simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
      star_add, star_mul', star_star]
    ring
  have h2 : M.det = 1 := by
    have e : A.map star = (star A)ᵀ := by
      ext i j
      simp [Matrix.star_apply]
    rw [h, det_mul, e, det_transpose, ← det_mul, hA, det_one]
  have h3 : M.adjugate = star M := by
    calc M.adjugate = M.adjugate * (M * star M) := by rw [hM, Matrix.mul_one]
      _ = star M := by rw [← Matrix.mul_assoc, adjugate_mul, h2, one_smul, Matrix.one_mul]
  refine ⟨h1, ?_⟩
  rw [charpoly_three, h3, h2, star_eq_conjTranspose, trace_conjTranspose, h1]
  simp only [map_sub, map_one]
  ring

open scoped Matrix.Norms.L2Operator in
private lemma disc_nonpos (M : Matrix (Fin 3) (Fin 3) ℂ) (hM : M ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ)) (t : ℝ)
    (h : M.charpoly = (X - 1) * (X ^ 2 - C (t : ℂ) * X + 1)) : t ^ 2 - 4 ≤ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s ^ 2 = t ^ 2 - 4 := ⟨√(t ^ 2 - 4), Real.sq_sqrt hc.le⟩
  set r : ℝ := (t + s) / 2 with hr
  have e : r ^ 2 - t * r + 1 = 0 := by rw [hr]; linarith
  have hroot : (r : ℂ) ∈ spectrum ℂ M := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, h]
    have e' : (r : ℂ) ^ 2 - t * r + 1 = 0 := by exact_mod_cast e
    simp [e']
  have hn := spectrum.norm_eq_one_of_unitary hM hroot
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  have h2 : r ^ 2 = 1 := by rw [← sq_abs, hn]; norm_num
  have h3 : t * r = 2 := by linarith
  have h4 : t ^ 2 = 4 := by
    calc t ^ 2 = (t * r) ^ 2 := by rw [mul_pow, h2, mul_one]
      _ = 4 := by rw [h3]; norm_num
  linarith

private lemma exists_emb {F : Type} [Field F] (Δ : F) (σ : F →+* ℝ) (h : σ Δ < 0) :
    ∃ φ : Lsq F Δ →+* ℂ, (∀ x, φ (star x) = star (φ x)) ∧ ∀ a, φ (algebraMap F _ a) = σ a := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s * s = -σ Δ := ⟨√(-σ Δ), Real.mul_self_sqrt (by linarith)⟩
  refine ⟨{ toFun := fun x => ⟨σ x.re, σ x.im * s⟩
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · apply Complex.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · intro x y
    apply Complex.ext
    · simp
      linear_combination (σ x.im * σ y.im) * hs
    · simp
      ring
  · apply Complex.ext <;> simp
  · intro x y
    apply Complex.ext
    · simp
    · simp
      ring
  · intro x
    apply Complex.ext <;> simp
  · intro a
    apply Complex.ext <;> simp

end UpperTheory.Reformulated.B.CubicCharpolyDiscriminant

theorem UpperTheory.Reformulated.B.CubicCharpolyDiscriminant.tauEx :
    UpperTheory.V.Z.Sym.Glob.TauEx := by
  intro F _ _ Δ D hD δ
  set M : U3 Δ := δ * theta Δ δ with hMdef
  obtain ⟨h1, h2⟩ := charpoly_tw (δ : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ))
    δ.2.2 M.2.2 rfl
  have him : (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace.im = 0 := by
    have := congrArg QuadraticAlgebra.im h1
    rw [QuadraticAlgebra.im_star] at this
    linear_combination (-1 / 2 : F) * this
  have hτ : algebraMap F (Lsq F Δ) ((M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace.re - 1) =
      (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace - 1 := by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, him]
  rw [← hτ] at h2
  generalize (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace.re - 1 = τ at h2
  refine ⟨τ, h2, fun hne σ => ?_⟩
  obtain ⟨φ, hφ, hφa⟩ := exists_emb Δ σ (hD.neg σ)
  have hs : star ((M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).map φ) = (star (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ))).map φ := by
    ext i j
    simp only [Matrix.star_apply, Matrix.map_apply, hφ]
  have hu : (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).map φ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) := by
    constructor
    · rw [hs, ← Matrix.map_mul, M.2.1, Matrix.map_one _ (map_zero φ) (map_one φ)]
    · rw [hs, ← Matrix.map_mul, M.2.2, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hle := disc_nonpos _ hu (σ τ) (by
    rw [Matrix.charpoly_map, h2]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add (f := _), Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_C, hφa])
  have hne' : σ (τ ^ 2 - 4) ≠ 0 := (map_ne_zero σ).2 hne
  have e : σ (τ ^ 2 - 4) = σ τ ^ 2 - 4 := by
    rw [map_sub, map_pow, map_ofNat]
  exact lt_of_le_of_ne (e ▸ hle) hne'
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCoordinate
section
open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.ExistsCoordinate.exists_coord :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {y : E},
    y ∈ ℚ[(↑H.rt : E)] →
      ∃ (u : ℚ) (v : ℚ),
        y =
          (↑u : E) +
            (↑v : E) *
              (↑H.rt :
                E) := by
  intro E _ _ _ H y hy
  have hsq : (H.rt : E) * (H.rt : E) = -(H.d : E) := by
    have h := congrArg (fun z : NumberField.RingOfIntegers E => (z : E)) H.rt_sq
    simpa [sq] using h
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hx]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x z _ _ hx hz =>
    obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hz
    exact ⟨a * c - b * e * H.d, a * e + b * c, by push_cast; linear_combination (b * e : E) * hsq⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedHomology
section
theorem UpperTheory.Reformulated.B.FinitelyGeneratedHomology.omHT_fg :
    ∀ {A K : Type} [inst : CommRing A] [inst_1 : Field K] [inst_2 : Algebra A K] {E : Type} [inst_3 : Field E]
      [inst_4 : NumberField E] {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [inst_5 : AddCommGroup Ω] [inst_6 : _root_.Module K Ω]
      [inst_7 : _root_.Module A Ω] [inst_8 : IsScalarTower A K Ω] (D : GlobalTheory.CompanionTheory.Ar.HT.HTChart A K c p R N Ω) (σ : E →+* K),
      (D.omHT σ).FG := by
  intro A K _ _ _ E _ _ c p R N Ω _ _ _ _ D σ
  have hZ : (LinearMap.range D.h.toIntLinearMap).FG := Submodule.fg_range _
  have hA : (Submodule.span A (Set.range D.h)).FG := by
    obtain ⟨S, hS⟩ := hZ
    refine ⟨S, ?_⟩
    have h1 : Set.range D.h = (Submodule.span ℤ (S : Set Ω) : Set Ω) := by
      rw [hS]; rfl
    rw [h1, Submodule.span_span_of_tower]
  exact (hA.sup (D.om_lat.fg.map _)).map _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocPairValLinear
section
theorem UpperTheory.Reformulated.B.Qp9.locPair_val_linear :
    ∀ (O : Type) [inst : CommRing O] [inst_1 : IsDomain O]
    [inst_2 : IsDiscreteValuationRing O] (K : Type) [Fintype K] [inst_4 : DecidableEq K] (ι : K → Type)
    [(k : K) → Fintype (ι k)] (σ : Type) [inst_6 : Fintype σ] (T : GlobalTheory.CompanionTheory.Ar.Num.LocPair ι O σ)
    (P : Ideal (GroundTheory.Heights₂.Heights.NumbersDVR.MRing ι O)),
    (∀ (Gs Hs : σ → MvPolynomial (σ ⊕ σ) ℝ), T.val P (Gs + Hs) = T.val P Gs + T.val P Hs) ∧
      (∀ (c : ℝ) (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ),
          (T.val P fun (i : σ) ↦ (MvPolynomial.C : ℝ → MvPolynomial (σ ⊕ σ) ℝ) c * Gs i) = c * T.val P Gs) ∧
        ∀ (α : Type) (s : Finset α) (Gs : α → σ → MvPolynomial (σ ⊕ σ) ℝ),
          (T.val P fun (i : σ) ↦ ∑ a ∈ s, Gs a i) =
            ∑ a ∈ s,
              T.val P
                (Gs
                  a) := by
  intro O _ _ _ K _ _ ι _ σ _ T P
  have key : ∀ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ, T.val P Gs = ∑ i, Finsupp.linearCombination ℝ
      (fun μ => (GlobalTheory.CompanionTheory.Ar.Num.cycList (GroundTheory.Heights₂.Heights.NumbersDVR.ratDiv P (T.f i) (T.g i))
        (GroundTheory.Heights₂.Heights.NumbersDVR.classList (Sum.elim T.x T.x') μ ++ []) : ℝ))
      (MvPolynomial.basisMonomials (σ ⊕ σ) ℝ |>.repr (Gs i)) := fun Gs => rfl
  refine ⟨fun Gs Hs => ?_, fun c Gs => ?_, fun α s Gs => ?_⟩
  · simp only [key, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
  · simp only [key, MvPolynomial.C_mul', map_smul, smul_eq_mul, Finset.mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [key, map_sum]
      exact Finset.sum_comm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Rt0ConjNegNeZero
section
theorem UpperTheory.Reformulated.B.Ga10.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    (starRingEnd ℂ : ℂ → ℂ) H.rt0 =
      -H.rt0 := by
  intro E _ _ _ H
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [sq] at h1 h2
  have hre : H.rt0.re = 0 := by
    by_contra hne
    have him : H.rt0.im = 0 := mul_left_cancel₀ hne (by linarith)
    rw [him] at h1
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [hre]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ZASmul
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi53.Acris :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ GroundTheory.PAdicHodge.ACris.ACris ℂ_[l] l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi53.Ainf :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ GroundTheory.PAdicHodge.AInf ℂ_[l] l

noncomputable def UpperTheory.Reformulated.B.Qi53.zA :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → ℤ_[l] →+* UpperTheory.Reformulated.B.Qi53.Acris l :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Algebra.algebraMap (UpperTheory.Reformulated.B.Qi53.Ainf l) (UpperTheory.Reformulated.B.Qi53.Acris l)).comp
        (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt l)

theorem UpperTheory.Reformulated.B.Qi53.zA_smul.{u_1} :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {N : Type u_1} [inst_1 : AddCommGroup N]
      [inst_2 : _root_.Module (UpperTheory.Reformulated.B.Qi53.Acris l) N] (n : ℕ),
      (∀ (y : N), (↑l : UpperTheory.Reformulated.B.Qi53.Acris l) ^ n • y = (0 : N)) →
        ∀ (z : ℤ_[l]) (y : N),
          (UpperTheory.Reformulated.B.Qi53.zA l : ℤ_[l] → UpperTheory.Reformulated.B.Qi53.Acris l) z • y =
            ((PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n)) z).val • y := by
  intro l _ N _ _ n h z y
  have hz : z - (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) := by
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero n (Fact.out : Nat.Prime l).ne_zero⟩
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hz
  obtain ⟨w, hw⟩ := hz
  have hz' : z = (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by
    rw [← hw]; ring
  generalize (PadicInt.toZModPow n z).val = m at hz' ⊢
  rw [hz', map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_smul, mul_smul, h, add_zero,
    Nat.cast_smul_eq_nsmul]
end

