module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0061
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0001
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AddCharInverseDifferentAndResidueSumEqZero
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

private theorem UpperTheory.sum_reAt_eq_trace' (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    ∑ v : InfinitePlace F, reAt v x = (Algebra.trace ℚ F x : ℝ) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)
  have hbij : Function.Bijective (fun v : InfinitePlace F => v.embedding) := by
    constructor
    · intro v w h
      simpa [InfinitePlace.mk_embedding] using congrArg InfinitePlace.mk h
    · intro φ
      have hr : ComplexEmbedding.IsReal φ := by
        have := IsTotallyReal.isReal (InfinitePlace.mk φ)
        rwa [InfinitePlace.isReal_mk_iff] at this
      exact ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal hr⟩
  have h2 : ∑ v : InfinitePlace F, v.embedding x = ∑ φ : F →+* ℂ, φ x :=
    Fintype.sum_bijective _ hbij _ _ (fun _ => rfl)
  have h3 : ∑ φ : F →+* ℂ, φ x = ∑ σ : F →ₐ[ℚ] ℂ, σ x :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)
  have h4 : ((Algebra.trace ℚ F x : ℝ) : ℂ) = ∑ v : InfinitePlace F, v.embedding x := by
    rw [h2, h3, ← h1]; simp
  unfold reAt
  rw [← Complex.re_sum, ← h4, Complex.ofReal_re]

private theorem UpperTheory.mem_dual_of_valuation_le_different (F : Type) [Field F] [NumberField F] (x : F)
    (hx : ∀ v : Pl F, v.valuation F x ≤ WithZero.exp (ordI v (differentIdeal ℤ (𝓞 F)) : ℤ)) :
    x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
  classical
  have hdvd : ∀ v : Pl F,
      v.asIdeal ^ ordI v (differentIdeal ℤ (𝓞 F)) ∣ differentIdeal ℤ (𝓞 F) := by
    intro v
    unfold ordI
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr differentIdeal_ne_bot)
      v.associates_irreducible).mpr le_rfl
  have hD := coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hne : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) :
      FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa using differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)
  rw [← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)), ← hD,
    FractionalIdeal.mem_inv_iff hne]
  intro y hy
  obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
  rw [FractionalIdeal.mem_one_iff]
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F (x * algebraMap (𝓞 F) F d) ?_
  intro v
  have h1 : v.intValuation d ≤ WithZero.exp (-(ordI v (differentIdeal ℤ (𝓞 F)) : ℤ)) :=
    (v.intValuation_le_pow_iff_dvd d _).mpr
      ((hdvd v).trans (Ideal.dvd_span_singleton.mpr hd))
  rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap]
  calc v.valuation F x * v.intValuation d
      ≤ WithZero.exp (ordI v (differentIdeal ℤ (𝓞 F)) : ℤ) *
          WithZero.exp (-(ordI v (differentIdeal ℤ (𝓞 F)) : ℤ)) := mul_le_mul' (hx v) h1
    _ = 1 := by rw [← WithZero.exp_add]; simp

private theorem UpperTheory.false_of_mem_dual_of_valuation_eq_different_succ (F : Type) [Field F] [NumberField F] (x : F) (w : Pl F)
    (hx : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))
    (hw : w.valuation F x = WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) + 1)) : False := by
  classical
  have hD := coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hne : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) :
      FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa using differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)
  rw [← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)), ← hD,
    FractionalIdeal.mem_inv_iff hne] at hx
  have hnd : ¬ w.asIdeal ^ (ordI w (differentIdeal ℤ (𝓞 F)) + 1) ∣ differentIdeal ℤ (𝓞 F) := by
    unfold ordI
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr differentIdeal_ne_bot)
        w.associates_irreducible]
    omega
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨d, hd, hd'⟩ := SetLike.not_le_iff_exists.mp hnd
  have hint := hx _ ((FractionalIdeal.mem_coeIdeal _).mpr ⟨d, hd, rfl⟩)
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp hint
  have h1 : w.valuation F x * w.intValuation d ≤ 1 := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F), ← map_mul, ← ha,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact w.intValuation_le_one a
  apply hd'
  rw [← w.intValuation_le_pow_iff_mem]
  rw [hw] at h1
  calc w.intValuation d
      = WithZero.exp (-((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) + 1)) *
          (WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) + 1) * w.intValuation d) := by
        rw [← mul_assoc, ← WithZero.exp_add]; simp
    _ ≤ WithZero.exp (-((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) + 1)) * 1 := mul_le_mul' le_rfl h1
    _ = WithZero.exp (-((ordI w (differentIdeal ℤ (𝓞 F)) + 1 : ℕ) : ℤ)) := by push_cast; simp

private theorem UpperTheory.mem_dual_one_iff_trace_mul_int (F : Type) [Field F] [NumberField F] (x : F) :
    x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ↔
      ∀ b : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (x * b) = n := by
  rw [FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 F)) F) _ _ _)]
  constructor
  · intro h b
    obtain ⟨n, hn⟩ := h _ ((FractionalIdeal.mem_one_iff _).mpr ⟨b, rfl⟩)
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply] at hn
    simpa using hn.symm
  · intro h a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨n, hn⟩ := h b
    exact ⟨n, by rw [Algebra.traceForm_apply, hn]; simp⟩

private theorem UpperTheory.cexp_two_pi_I_mul_eq_one_iff_int (t : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) = 1 ↔ ∃ n : ℤ, t = n := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (t : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hpi
      rw [hn]; ring
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

theorem UpperTheory.addChar_inverseDifferent_and_residue_sum_eq_zero :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (η : F), ((∀ v : Pl F, v.valuation F η ≤ WithZero.exp (ordI v (differentIdeal ℤ (𝓞 F)) : ℤ)) → ∀ b : 𝓞 F, Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v (η * (b : F)) : ℂ)) = 1) ∧ ∀ (w : Pl F) [Fintype (𝓞 F ⧸ w.asIdeal)] (s : 𝓞 F ⧸ w.asIdeal → 𝓞 F), (∀ r, Ideal.Quotient.mk w.asIdeal (s r) = r) → (∀ v : Pl F, v ≠ w → v.valuation F η ≤ WithZero.exp (ordI v (differentIdeal ℤ (𝓞 F)) : ℤ)) → w.valuation F η = WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) + 1) → ∑ r, Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v (η * (s r : F)) : ℂ)) = 0 := by
  intro F _ _ _ η
  have key : ∀ x : F, (∃ n : ℤ, Algebra.trace ℚ F x = n) ↔
      Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v x : ℂ)) = 1 := by
    intro x
    rw [← Complex.ofReal_sum, UpperTheory.sum_reAt_eq_trace', UpperTheory.cexp_two_pi_I_mul_eq_one_iff_int]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [hn]; push_cast; rfl⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by exact_mod_cast hn⟩
  have part1 : ∀ x : F, (∀ v : Pl F, v.valuation F x ≤
      WithZero.exp (ordI v (differentIdeal ℤ (𝓞 F)) : ℤ)) → ∀ b : 𝓞 F,
      Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v (x * (b : F)) : ℂ)) = 1 := by
    intro x hx b
    exact (key _).mp ((UpperTheory.mem_dual_one_iff_trace_mul_int F x).mp (UpperTheory.mem_dual_of_valuation_le_different F x hx) b)
  refine ⟨part1 η, ?_⟩
  intro w _ s hs hv hw
  set ψ : 𝓞 F → ℂ := fun b =>
    Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v (η * (b : F)) : ℂ)) with hψ
  have hadd : ∀ a b : 𝓞 F, ψ (a + b) = ψ a * ψ b := by
    intro a b
    simp only [hψ, ← Complex.exp_add]
    congr 1
    have e : ∀ v : InfinitePlace F, (reAt v (η * ((a + b : 𝓞 F) : F)) : ℂ) =
        (reAt v (η * (a : F)) : ℂ) + (reAt v (η * (b : F)) : ℂ) := by
      intro v
      simp only [reAt, map_add (f := _), mul_add, Complex.add_re, Complex.ofReal_add]
    rw [Finset.sum_congr rfl (fun v _ => e v), Finset.sum_add_distrib]
    ring
  have hker : ∀ c ∈ w.asIdeal, ψ c = 1 := by
    intro c hc
    have h := part1 (η * (c : F)) ?_ 1
    · simpa [hψ] using h
    intro v
    have hcv : v.valuation F (c : F) = v.intValuation c :=
      HeightOneSpectrum.valuation_of_algebraMap (K := F) v c
    by_cases hvw : v = w
    · subst hvw
      rw [map_mul, hw, hcv]
      have hc1 : v.intValuation c ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
        (v.intValuation_le_pow_iff_mem c 1).mpr (by simpa using hc)
      calc _ ≤ WithZero.exp ((ordI v (differentIdeal ℤ (𝓞 F)) : ℤ) + 1) *
            WithZero.exp (-((1 : ℕ) : ℤ)) := mul_le_mul' le_rfl hc1
        _ = _ := by rw [← WithZero.exp_add]; congr 1; push_cast; ring
    · rw [map_mul, hcv]
      calc _ ≤ WithZero.exp (ordI v (differentIdeal ℤ (𝓞 F)) : ℤ) * 1 :=
            mul_le_mul' (hv v hvw) (v.intValuation_le_one c)
        _ = _ := mul_one _
  have hcoset : ∀ a b : 𝓞 F, a - b ∈ w.asIdeal → ψ a = ψ b := by
    intro a b hab
    have e : a = b + (a - b) := by ring
    rw [e, hadd, hker _ hab, mul_one]
  obtain ⟨b0, hb0⟩ : ∃ b0 : 𝓞 F, ψ b0 ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hdual := (UpperTheory.mem_dual_one_iff_trace_mul_int F η).mpr (fun b => (key _).mpr (hcon b))
    exact UpperTheory.false_of_mem_dual_of_valuation_eq_different_succ F η w hdual hw
  have hsum : ψ b0 * ∑ r, ψ (s r) = ∑ r, ψ (s r) := by
    rw [Finset.mul_sum]
    calc ∑ r, ψ b0 * ψ (s r) = ∑ r, ψ (s (r + Ideal.Quotient.mk w.asIdeal b0)) := by
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [← hadd]
          apply hcoset
          rw [← Ideal.Quotient.eq]
          simp only [map_add (f := _), hs]
          ring
      _ = ∑ r, ψ (s r) := Fintype.sum_equiv (Equiv.addRight _) _ _ (fun _ => rfl)
  have h0 : (ψ b0 - 1) * ∑ r, ψ (s r) = 0 := by rw [sub_mul, hsum, one_mul, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) hb0
  · exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BijectiveResidueUnitMulLift
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

theorem UpperTheory.bijective_residue_unit_mul_lift :
    ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (u : w.adicCompletionIntegers F), Valued.v (u : w.adicCompletion F) = 1 → ∀ s : 𝓞 F ⧸ w.asIdeal → 𝓞 F, (∀ r, Ideal.Quotient.mk w.asIdeal (s r) = r) → Function.Bijective fun r => IsLocalRing.residue (w.adicCompletionIntegers F) (u * algebraMap (𝓞 F) (w.adicCompletionIntegers F) (s r)) := by
  intro F _ _ w u hu s hs
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  have hv : ∀ k : F, Valued.v (algebraMap F (w.adicCompletion F) k) = w.valuation F k :=
    fun k => IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w k
  have hmem : ∀ x : w.adicCompletionIntegers F,
      x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ↔ Valued.v (x : w.adicCompletion F) < 1 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have hx : Valued.v (x : w.adicCompletion F) ≤ 1 := x.2
    exact ⟨fun h => lt_of_le_of_ne hx h, fun h => ne_of_lt h⟩
  have hcoe : ∀ b : 𝓞 F, ((algebraMap (𝓞 F) (w.adicCompletionIntegers F) b : w.adicCompletionIntegers F) : w.adicCompletion F)
      = algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F b) := fun b => rfl
  have hker : ∀ a ∈ w.asIdeal,
      ((IsLocalRing.residue (w.adicCompletionIntegers F)).comp
        (algebraMap (𝓞 F) (w.adicCompletionIntegers F))) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hmem, hcoe, hv]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem w a).mpr ha
  let g := Ideal.Quotient.lift w.asIdeal ((IsLocalRing.residue (w.adicCompletionIntegers F)).comp
        (algebraMap (𝓞 F) (w.adicCompletionIntegers F))) hker
  have hg : ∀ r, IsLocalRing.residue (w.adicCompletionIntegers F)
      (algebraMap (𝓞 F) (w.adicCompletionIntegers F) (s r)) = g r := by
    intro r
    conv_rhs => rw [← hs r]
    rfl
  have hinj : Function.Injective g := g.injective
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    have hU : {z : w.adicCompletion F | Valued.v (z - (y : w.adicCompletion F)) < 1} ∈ nhds (y : w.adicCompletion F) := by
      rw [Valued.mem_nhds]
      refine ⟨1, fun z hz => ?_⟩
      simpa [Valuation.restrict_lt_iff_lt_embedding] using hz
    obtain ⟨a, ha⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) w).mem_nhds hU
    have ha' : Valued.v (algebraMap F (w.adicCompletion F) a - (y : w.adicCompletion F)) < 1 := ha
    have hale : w.valuation F a ≤ 1 := by
      rw [← hv]
      have hy : Valued.v (y : w.adicCompletion F) ≤ 1 := y.2
      have e : algebraMap F (w.adicCompletion F) a
          = (algebraMap F (w.adicCompletion F) a - (y : w.adicCompletion F)) + (y : w.adicCompletion F) := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le ha'.le hy)
    obtain ⟨b, hb⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer w hale 1
    have hb' : Valued.v (algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F b - a)) < 1 := by
      rw [hv]; simpa using hb
    refine ⟨Ideal.Quotient.mk w.asIdeal b, ?_⟩
    change IsLocalRing.residue _ (algebraMap (𝓞 F) (w.adicCompletionIntegers F) b) = _
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmem]
    have e : ((algebraMap (𝓞 F) (w.adicCompletionIntegers F) b - y : w.adicCompletionIntegers F) : w.adicCompletion F)
        = algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F b - a)
          + (algebraMap F (w.adicCompletion F) a - (y : w.adicCompletion F)) := by
      rw [map_sub]
      change ((algebraMap (𝓞 F) (w.adicCompletionIntegers F) b : w.adicCompletionIntegers F) : w.adicCompletion F) - (y : w.adicCompletion F) = _
      rw [hcoe]
      ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt hb' ha')
  have hc : IsUnit (IsLocalRing.residue (w.adicCompletionIntegers F) u) :=
    ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr hu).map _
  have hf : (fun r => IsLocalRing.residue (w.adicCompletionIntegers F)
      (u * algebraMap (𝓞 F) (w.adicCompletionIntegers F) (s r)))
      = (fun z => (hc.unit : IsLocalRing.ResidueField (w.adicCompletionIntegers F)) * z) ∘ g := by
    funext r
    simp only [Function.comp_apply, map_mul, hg, IsUnit.unit_spec]
  rw [hf]
  exact (Units.mulLeft_bijective hc.unit).comp ⟨hinj, hsurj⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CentralCharSqEqOfIsSelfDualBy
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.central_char_sq_eq_of_isSelfDualBy :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (χ : HChar F), π.IsSelfDualBy χ → ∀ (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))), LocIsotypic π.finPart w σ → ∀ (z : (w.adicCompletion F)ˣ) (c : ℂ), (∀ v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = c • v) → c ^ 2 = ((χ.loc w z : ℂˣ) : ℂ) ^ 2 := by
  intro F _ _ _ π χ hπ w σ hσ z c hc
  obtain ⟨B, d, hl, -, -, hf, -, -⟩ := hπ
  obtain ⟨hnt, htop⟩ := hσ
  set k := locGL F 2 w (Matrix.GeneralLinearGroup.scalar (Fin 2) z) with hk
  have hact : ∀ φ : π.V, π.finPart k φ = c • φ := by
    intro φ
    have hφ : φ ∈ (⊤ : Submodule ℂ π.V) := Submodule.mem_top
    rw [← htop] at hφ
    refine Submodule.iSup_induction _ (motive := fun φ => π.finPart k φ = c • φ) hφ ?_ ?_ ?_
    · rintro f _ ⟨v, rfl⟩
      rw [hk, ← f.2, hc, map_smul]
    · simp
    · intro x y hx hy
      rw [map_add (f := _), hx, hy, smul_add]
  have hop : ∀ φ : π.V, π.op (.fin k) φ = c • φ := fun φ => hact φ
  obtain ⟨φ, hφ⟩ := exists_ne (0 : π.V)
  obtain ⟨ψ, hψ⟩ : ∃ ψ, B φ ψ ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (hl φ h)
  have h1 := hf k φ ψ
  rw [hop, hop, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
  have h2 := mul_right_cancel₀ hψ h1
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z ^ 2 := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_two, sq]
  have h3 : chiDet 2 χ (finGL F 2 k) = χ.loc w (z ^ 2) := by
    rw [← hdet]
    exact TR.CuspSub.chiDet_locGL χ w _
  rw [sq, h2, h3, map_pow, Units.val_pow_eq_pow_val]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EventuallyMemHeckeLevelAndIwahoriCongruence
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem cmp_of {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) : cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem cmp_not {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ¬ ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : Ga l L n) : cmp n w x = 1 := by
  unfold CaseU.cmp
  rw [dite_eq_right h]
  rfl

private theorem cmp_cont (l : ℕ) [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : Plc L) :
    Continuous fun k : finU (E := L) (n := n) => cmp n w ((away l L n).rangeRestrict (k : UA L n)) := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  · simp only [cmp_of h]
    exact ((UpperTheory.unitaryAdelic_localComponents_continuous_levels_open L n).1 w).comp continuous_subtype_val
  · simp only [cmp_not h]
    exact continuous_const

private theorem cmp_ev (l : ℕ) [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : Plc L)
    (U : Subgroup (GLw n w)) (hU : IsOpen (U : Set (GLw n w))) :
    ∀ᶠ k : finU (E := L) (n := n) in nhds 1, cmp n w ((away l L n).rangeRestrict (k : UA L n)) ∈ U := by
  refine (hU.preimage (cmp_cont l n w)).mem_nhds ?_
  change cmp n w ((away l L n).rangeRestrict ((1 : finU (E := L) (n := n)) : UA L n)) ∈ U
  rw [OneMemClass.coe_one, map_one, map_one]
  exact one_mem U

private theorem cmp_int {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (x : UA L n) (hx : cLoc w x ∈ KO (w.adicCompletion L) (Fin n)) :
    cmp n w ((away l L n).rangeRestrict x) ∈ KO (w.adicCompletion L) (Fin n) := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  · rwa [cmp_of h]
  · rw [cmp_not h]
    exact one_mem _

private theorem pi_mem_first_iwahori_filtration {σ : Type} [Finite σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v)) (b : ℕ)
    (g : ∀ v, G v) (hg : ∀ v, g v ∈ (I v).I1 b) : g ∈ (piIwa I).I1 b := by
  choose x hx t ht y hy e using fun v => (iwMem _ (I v) b (g v)).2.1.1 (hg v)
  exact (iwMem _ (piIwa I) b g).2.1.2 ⟨x, fun v _ => hx v, t, fun v _ => ht v, y, fun v _ => hy v, funext e⟩

theorem UpperTheory.eventually_mem_heckeLevel_and_iwahoriCongruence :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), IsOpen (τ₀.ker : Set (KT n (wt s))) → ∀ (K : (hset Q τ₀).Lev) (b : ℕ), ∀ᶠ k : finU (E := L) (n := n) in nhds 1, (∃ u : Ub n s, u ∈ (hset Q τ₀).lev K ∧ (u : Ga l L n) = (away l L n).rangeRestrict (k : UA L n) ∧ τ₀ (toKT n s u) = 1) ∧ (fun v : V.frame.Vl => cLoc (s.w v.1) (k : UA L n)) ∈ (hset Q τ₀).X.I.I1 b := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ hτ K b
  obtain ⟨hc, hK, hint⟩ := UpperTheory.unitaryAdelic_localComponents_continuous_levels_open L n
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hτ
  have h1 : ∀ᶠ k : finU (E := L) (n := n) in nhds 1,
      (fun u : s.St => cmp n (s.w u) ((away l L n).rangeRestrict (k : UA L n)) : GV n (wt s)) ∈ U := by
    refine (hU.preimage (continuous_pi fun u : s.St => cmp_cont l n (s.w u))).mem_nhds ?_
    have h0 : (1 : KT n (wt s)) ∈ Subtype.val ⁻¹' U := by
      rw [hUe]
      exact one_mem τ₀.ker
    have e : (fun u : s.St => cmp n (s.w u) ((away l L n).rangeRestrict ((1 : finU (E := L) (n := n)) : UA L n)) : GV n (wt s)) = 1 := by
      funext u
      rw [OneMemClass.coe_one, map_one, map_one]
      rfl
    rw [Set.mem_preimage, e]
    exact h0
  have h2 := cmp_ev l n (s.w s.v0) _ (hK (s.w s.v0) 1)
  have h3 : ∀ᶠ k : finU (E := L) (n := n) in nhds 1, ∀ q : Q.Q, cmp n (Q.wq q) ((away l L n).rangeRestrict (k : UA L n)) ∈ K.1 q :=
    Filter.eventually_all.2 fun q => cmp_ev l n (Q.wq q) (K.1 q) (K.2 q).1
  have h4 : ∀ᶠ k : finU (E := L) (n := n) in nhds 1, ∀ v : V.frame.Vl,
      cLoc (s.w v.1) (k : UA L n) ∈ Kc ((s.w v.1).adicCompletion L) n (b + 1) := by
    haveI : Finite V.frame.Vl := (hset Q τ₀).finV.finite
    refine Filter.eventually_all.2 fun v => ?_
    refine ((hK (s.w v.1) (b + 1)).preimage ((hc (s.w v.1)).comp continuous_subtype_val)).mem_nhds ?_
    change cLoc (s.w v.1) ((1 : finU (E := L) (n := n)) : UA L n) ∈ Kc ((s.w v.1).adicCompletion L) n (b + 1)
    rw [OneMemClass.coe_one, map_one]
    exact one_mem _
  filter_upwards [hint, h1, h2, h3, h4] with k k0 k1 k2 k3 k4
  have hu : (away l L n).rangeRestrict (k : UA L n) ∈ Ub n s :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u => cmp_int _ (k0 _), k2⟩
  refine ⟨⟨⟨_, hu⟩, UpperTheory.mem_heckeLevel_of_local_components_mem l L Ω s n hn V Q c m τ₀ K _ (fun w _ => cmp_int _ (k0 w)) k3, rfl, ?_⟩, ?_⟩
  · have : toKT n s ⟨_, hu⟩ ∈ Subtype.val ⁻¹' U := k1
    rw [hUe] at this
    exact this
  · exact pi_mem_first_iwahori_filtration (fun v : V.frame.Vl => glIwa ((s.w v.1).adicCompletion L) n) b _ fun v =>
      (glBridge ((s.w v.1).adicCompletion L) n ℂ 1).2.2.2.2.1 b (k4 v)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsGlobalElementValuationEqIdeleAtPlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

theorem UpperTheory.exists_global_element_valuation_eq_idele_at_place :
    ∀ (F : Type) [Field F] [NumberField F] (y : (Af F)ˣ) (w : Pl F), ∃ β : F, w.valuation F β = Valued.v (pLoc F w (y : Af F)) ∧ ∀ v : Pl F, v.valuation F β ≤ Valued.v (pLoc F v (y : Af F)) := by
  intro F _ _ y w
  obtain ⟨p, hpw, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have hp : algebraMap (𝓞 F) F p ≠ 0 := by simpa using hp0
  have hval : ∀ (v : Pl F) (f : F), Valued.v (pLoc F v (algebraMap F (Af F) f)) = v.valuation F f :=
    fun v f => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v f
  set z : Af F := algebraMap F (Af F) (algebraMap (𝓞 F) F p)⁻¹ * ((y⁻¹ : (Af F)ˣ) : Af F) with hz
  have hc : Continuous fun a : Af F => z * (a - (y : Af F)) :=
    continuous_const.mul (continuous_id.sub continuous_const)
  obtain ⟨β, hβ⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).exists_mem_open
    ((GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 F) (K := F)).preimage hc)
    ⟨(y : Af F), by simp⟩
  have hβ' : ∀ v : Pl F, Valued.v (pLoc F v (z * (algebraMap F (Af F) β - (y : Af F)))) ≤ 1 :=
    fun v => GroundTheory.Global.mem_integralFiniteAdeles.1 hβ v
  have e : algebraMap F (Af F) β - (y : Af F) =
      (y : Af F) * algebraMap F (Af F) (algebraMap (𝓞 F) F p) * (z * (algebraMap F (Af F) β - (y : Af F))) := by
    have h1 : algebraMap F (Af F) (algebraMap (𝓞 F) F p) * algebraMap F (Af F) (algebraMap (𝓞 F) F p)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hp, map_one]
    have h2 : (y : Af F) * ((y⁻¹ : (Af F)ˣ) : Af F) = 1 := y.mul_inv
    have h3 : (y : Af F) * algebraMap F (Af F) (algebraMap (𝓞 F) F p) * z = 1 := by
      rw [hz]
      linear_combination ((y : Af F) * ((y⁻¹ : (Af F)ˣ) : Af F)) * h1 + h2
    rw [← mul_assoc, h3, one_mul]
  have key : ∀ v : Pl F, Valued.v (pLoc F v (algebraMap F (Af F) β) - pLoc F v (y : Af F)) ≤
      Valued.v (pLoc F v (y : Af F)) * v.valuation F (algebraMap (𝓞 F) F p) := fun v => by
    rw [← map_sub, e, map_mul, map_mul, map_mul, map_mul, hval]
    exact mul_le_of_le_one_right' (hβ' v)
  refine ⟨β, ?_, fun v => ?_⟩
  · rw [← hval]
    refine Valuation.map_eq_of_sub_lt _ ((key w).trans_lt ?_)
    have h0 : 0 < Valued.v (pLoc F w (y : Af F)) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (y.isUnit.map (pLoc F w)).ne_zero)
    exact (mul_lt_mul_of_pos_left ((w.valuation_lt_one_iff_mem p).2 hpw) h0).trans_eq (mul_one _)
  · rw [← hval, ← sub_add_cancel (pLoc F v (algebraMap F (Af F) β)) (pLoc F v (y : Af F))]
    exact (Valuation.map_add _ _ _).trans
      (max_le ((key v).trans (mul_le_of_le_one_right' (v.valuation_le_one p))) le_rfl)
end

