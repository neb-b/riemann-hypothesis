module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.BaseChangeNorms.PropMHol
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.CharPolSupp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.OrdPlain
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJacqOfU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPropMHol
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Base UpperTheory.V.Sd
section SlopeTestRemainingChoices
variable {l : ℕ} [Fact l.Prime]
private theorem sm_add {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)
private theorem sm_sub {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]; exact sm_add hx (by rwa [norm_neg])
private theorem sm_mul {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1) : ‖x * y‖ < 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt hy
private theorem le_of_cong {x y : Qbar l} (h : ‖x - y‖ < 1) (hy : ‖y‖ ≤ 1) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.le hy)
private theorem eq_of_cong {x y : Qbar l} (h : ‖x - y‖ < 1) (hy : ‖y‖ = 1) : ‖x‖ = 1 := by
  refine le_antisymm (le_of_cong h hy.le) (not_lt.1 fun hx => ?_)
  have := sm_sub hx h
  rw [sub_sub_cancel, hy] at this
  exact lt_irrefl _ this
private theorem inv_cong {x : Qbar l} (h : ‖x⁻¹ - 1‖ < 1) : ‖x - 1‖ < 1 := by
  have h1 := eq_of_cong h norm_one
  rw [norm_inv, inv_eq_one] at h1
  have h0 : x ≠ 0 := by rintro rfl; simp at h1
  have := sm_mul h1.le h
  rw [mul_sub, mul_inv_cancel₀ h0, mul_one, norm_sub_rev] at this
  exact this
private theorem norm_nat_lt {n : ℕ} (h : l ∣ n) : ‖(n : Qbar l)‖ < 1 := by
  obtain ⟨m, rfl⟩ := h
  rw [Nat.cast_mul, mul_comm]
  refine sm_mul (IsUltrametricDist.norm_natCast_le_one _ _) ?_
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one
private theorem pow_cong {n k : ℕ} (h : ¬ l ∣ n) (hk : l - 1 ∣ k) : ‖(n : Qbar l) ^ k - 1‖ < 1 := by
  obtain ⟨m, rfl⟩ := hk
  have hp : l.Prime := Fact.out
  have h1 : n ^ (l - 1) ≡ 1 [MOD l] := by
    rw [← Nat.totient_prime hp]
    exact Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
  have h2 : n ^ ((l - 1) * m) ≡ 1 [MOD l] := by
    rw [pow_mul]; simpa using h1.pow m
  have h0 : 1 ≤ n ^ ((l - 1) * m) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h))
  have := norm_nat_lt ((Nat.modEq_iff_dvd' h0).1 h2.symm)
  rwa [Nat.cast_sub h0, Nat.cast_pow, Nat.cast_one] at this
variable {F : Type} [Field F] [NumberField F]
private theorem dvd_normV (w : Pl F) : l ∣ normV w ↔ ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  rw [normV, Nat.card_eq_fintype_card, ← prime_dvd_char_iff_dvd_card, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    ringChar.spec]
  have hq : (ringChar (𝓞 F ⧸ w.asIdeal)).Prime := CharP.prime_ringChar _
  rw [Nat.prime_dvd_prime_iff_eq Fact.out hq, Nat.prime_dvd_prime_iff_eq hq Fact.out, eq_comm]
private theorem norm_val (ι : Qbar l ≃+* ℂ) {η : HChar F} (h : IsOfFinOrder η) (x : Ideles F) :
    ‖ι.symm (η.1 x : ℂˣ)‖ = 1 := by
  obtain ⟨m, hm, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : η.1 x ^ m = 1 := DFunLike.congr_fun (congrArg Subtype.val e) x
  have e2 : ‖ι.symm (η.1 x : ℂˣ)‖ ^ m = 1 := by
    rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, e1, Units.val_one, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e2
private theorem chiI_prime (ω : HChar F) (c : Pl F → ℕ) (w : Pl F) :
    chiI ω c w.asIdeal = if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0 := by
  classical
  rw [chiI, finprod_eq_single _ w]
  · rw [ordI, Associates.count_self w.associates_irreducible, pow_one]
  · intro v hv
    rw [ordI, Associates.count_eq_zero_of_ne v.associates_irreducible w.associates_irreducible, pow_zero]
    intro e
    exact hv (HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 e)))
private theorem gal_of (hA : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {η₁ η₂ : HChar F} (h₁ : IsOfFinOrder η₁)
    (h₂ : IsOfFinOrder η₂) {S : Set (Pl F)} (hS : S.Finite)
    (h : ∀ w ∉ S, η₁.UnrAt w ∧ η₂.UnrAt w ∧ (‖ι.symm (η₁.val w : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.val w : ℂˣ) - 1‖ < 1))
    (x : Ideles F) : ‖ι.symm (η₁.1 x : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.1 x : ℂˣ) - 1‖ < 1 := by
  obtain ⟨art, ha⟩ := hA F (AlgebraicClosure F)
  obtain ⟨m₁, hm₁, e₁⟩ := isOfFinOrder_iff_pow_eq_one.1 h₁
  obtain ⟨m₂, hm₂, e₂⟩ := isOfFinOrder_iff_pow_eq_one.1 h₂
  obtain ⟨δ₁, c₁, L₁⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η₁) hm₁ e₁)
  obtain ⟨δ₂, c₂, L₂⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η₂) hm₂ e₂)
  have hcl : IsClosed ((fun σ => (δ₁ σ : Qbar l)) ⁻¹' Metric.ball 1 1 ∪ (fun σ => (δ₂ σ : Qbar l)) ⁻¹' Metric.ball 1 1) :=
    ((IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp c₁)).union
      ((IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp c₂))
  obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
  have hd := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := AlgebraicClosure F) GlobalTheory.Published.chebotarevDegreeOne' hS
  have hm := hcl.closure_subset_iff.2 ?_ (hd σ)
  · have f₁ := L₁ x σ hσ.symm
    have f₂ := L₂ x σ hσ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one] at f₁ f₂
    simpa only [Set.mem_union, Set.mem_preimage, mem_ball_iff_norm, f₁, f₂] using hm
  · rintro τ ⟨v, hv, -, B, hB, hτ⟩
    obtain ⟨u₁, u₂, hh⟩ := h v hv
    simp only [Set.mem_union, Set.mem_preimage, mem_ball_iff_norm, L₁.frob_unr ha (Or.inr rfl) u₁ hB hτ,
      L₂.frob_unr ha (Or.inr rfl) u₂ hB hτ]
    exact hh.imp (fun t => inv_cong (by rwa [inv_inv])) fun t => inv_cong (by rwa [inv_inv])
end SlopeTestRemainingChoices
theorem UpperTheory.V.Z.Bc.propMHolZ_alt :
    _root_.UpperTheory.V.Z.Bc.Hypotheses4Z' → UpperTheory.V.Sd.PropMHol := by
  intro PP F _ _ _ l _ hl ι ω c hω hodd hc hne hcl P hP hQ B
  have hp : l.Prime := Fact.out
  obtain ⟨v, hvP, hvl, hv⟩ := hP
  obtain ⟨v', hvQ, hvl', hv'⟩ := hQ
  obtain ⟨φ, a, hφ, eφ, a1, aint, aeig⟩ := emix PP.eis F l ι ω c hω hodd hc hne hcl P ⟨v, hvP, hvl⟩
  have hl1 : 0 < l - 1 := Nat.sub_pos_of_lt hp.one_lt
  obtain ⟨k, hkB, hk0, hkd', ψ, d₀, b, hψ, eψ, hd, hb⟩ := PP.one F l hl ι B
  obtain ⟨χ, a', hχ, eχ, ha'⟩ := holMul F l ι 1 k (levL l c) ω hω φ ψ a d₀ b hφ hψ eφ eψ aint hd hb
  rw [add_comm 1 k] at hχ eχ
  simp only [map_sub] at ha'
  have hfin : {w | levL l c w ≠ 0}.Finite := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
    refine ((Ideal.finite_factors h0).union (GlobalTheory.Mem.UnrAe.unr_ae_and_level F ω).1).subset fun w hw => ?_
    by_cases h : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · exact Or.inl (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
    · refine Or.inr fun hu => hw ?_
      rw [levL, if_neg h]
      exact Nat.le_zero.1 ((hc w).2 fun x hx _ => hu x hx)
  have hL0 : ∀ w, levL l c w = 0 → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ∧ c w = 0 := fun w hw => by
    by_cases h : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [levL, if_pos h] at hw; exact absurd hw one_ne_zero
    · rw [levL, if_neg h] at hw; exact ⟨h, hw⟩
  have nval : ∀ {η : HChar F}, IsOfFinOrder η → ∀ w, ‖ι.symm (η.val w : ℂˣ)‖ = 1 := fun h w => norm_val ι h _
  have hpow : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖(normV w : Qbar l) ^ k - 1‖ < 1 := fun w hw =>
    pow_cong (mt (dvd_normV w).1 hw) hkd'
  have ht : ∀ w, ‖ι.symm (eisT l ω c P w)‖ ≤ 1 := fun w => by
    rw [eisT]
    split_ifs
    · exact (nval hω w).le
    · simp
    · rw [map_add (f := _), map_one]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le norm_one.le (nval hω w).le)
    · simp
  obtain ⟨g, lam, hg, hlam⟩ := _root_.UpperTheory.V.Sd.holLift_alt PP.h F l ι (k + 1) (Nat.le_add_left _ _) (levL l c) hfin ω hω χ 0 a'
    (eisT l ω c P) hχ eχ (fun 𝔪 h => le_of_cong (ha' 𝔪 h) (aint 𝔪 h))
    (eq_of_cong (ha' ⊤ top_ne_bot) (by rw [a1, map_one, norm_one])) ht (fun w 𝔪 h𝔪 => by
      have e := aeig w 𝔪 h𝔪
      have h1 := ha' _ (mul_ne_zero w.ne_bot h𝔪)
      have h2 := sm_mul (ht w) (ha' 𝔪 h𝔪)
      have h3 : ‖ι.symm (coefDiv a w.asIdeal 𝔪)‖ ≤ 1 ∧
          ‖ι.symm (coefDiv a' w.asIdeal 𝔪) - ι.symm (coefDiv a w.asIdeal 𝔪)‖ < 1 := by
        unfold coefDiv
        split_ifs with h
        · have h0 : h.choose ≠ ⊥ := fun h0 => h𝔪 (by rw [h.choose_spec, h0, Ideal.mul_bot])
          exact ⟨aint _ h0, ha' _ h0⟩
        · simp
      rw [hkCoef, chiI_prime, Nat.sub_self, pow_zero, mul_one] at e
      have e' := congrArg ι.symm e
      rw [hkCoef, chiI_prime, Nat.add_sub_cancel]
      split_ifs at e' ⊢ with h0
      · have h4 := sm_mul (nval hω w).le (sm_add (sm_mul (le_of_cong (hpow w (hL0 w h0).1) norm_one.le) h3.2)
          (sm_mul h3.1 (hpow w (hL0 w h0).1)))
        convert sm_add (sm_sub h1 h2) h4 using 2
        simp only [map_add (f := _), map_sub, map_mul, map_pow, map_natCast] at e' ⊢
        linear_combination e'
      · convert sm_sub h1 h2 using 2
        simp only [map_add (f := _), map_sub, map_mul, map_pow, map_natCast, map_zero] at e' ⊢
        linear_combination e')
  refine ⟨k, hkB, hkd', g, lam, hg, ?_, hlam⟩
  by_contra hcusp
  obtain ⟨η₁, η₂, f₁, f₂, rfl, hu, hr⟩ := holEis F (k + 1) (Nat.le_add_left _ _) (levL l c) hfin ω hω g lam hg hcusp
  simp only [map_sub, Nat.add_sub_cancel] at hlam hu hr
  have key := gal_of PP.h.litN.aut.art ι f₁ f₂ hfin fun w hw => by
    have h0 : levL l c w = 0 := not_not.1 hw
    obtain ⟨u₁, u₂, e⟩ := hu w h0
    refine ⟨u₁, u₂, ?_⟩
    have h1 := hlam w
    rw [e, eisT, if_neg (hL0 w h0).1, if_pos (hL0 w h0).2, HChar.val_mul] at h1
    have h2 := sm_sub (sm_mul (nval f₂ w).le (hpow w (hL0 w h0).1)) h1
    have h3 : ‖ι.symm (η₁.val w : ℂˣ) - 1‖ * ‖ι.symm (η₂.val w : ℂˣ) - 1‖ < 1 := by
      rw [← norm_mul]
      convert h2 using 2
      simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_one, Units.val_mul]
      ring
    by_contra hn
    rw [not_or, not_lt, not_lt] at hn
    exact h3.not_ge (one_le_mul_of_one_le_of_one_le hn.1 hn.2)
  have hab : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l (η₁ * η₂) c P w)‖ = 1 →
      ‖ι.symm (η₁.val w : ℂˣ) - ι.symm (eisT l (η₁ * η₂) c P w)‖ < 1 := fun w hw h1 => by
    have h2 := eq_of_cong (hlam w) h1
    rcases hr w (fun h0 => (hL0 w h0).1 hw) with e | ⟨-, e⟩ | ⟨-, e⟩
    · simp [e] at h2
    · exact e ▸ hlam w
    · rw [e, map_mul, map_pow, map_natCast, ← Nat.cast_pow] at h2
      exact absurd h2 (sm_mul (nval f₂ w).le (norm_nat_lt (dvd_pow ((dvd_normV w).2 hw) hk0.ne'))).ne
  have e₁ : eisT l (η₁ * η₂) c P v = ((η₁ * η₂).val v : ℂˣ) := by rw [eisT, if_pos hvl, if_pos hvP]
  have e₂ : eisT l (η₁ * η₂) c P v' = 1 := by rw [eisT, if_pos hvl', if_neg hvQ]
  have a₁ := hab v hvl (by rw [e₁]; exact nval hω v)
  have a₂ := hab v' hvl' (by rw [e₂, map_one, norm_one])
  rw [e₁] at a₁
  rw [e₂, map_one] at a₂
  have kk : ‖ι.symm (η₁.val v * η₁.val v' : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.val v * η₂.val v' : ℂˣ) - 1‖ < 1 := by
    have := key (localIdele F v (atFin v (unif v)) * localIdele F v' (atFin v' (unif v')))
    rw [map_mul η₁.1, map_mul η₂.1] at this
    exact this
  simp only [HChar.val_mul, Units.val_mul, map_mul] at kk a₁ hv hv'
  have n₁ := nval f₁ v
  have n₂ := nval f₂ v
  have n₃ := nval f₁ v'
  have n₄ := nval f₂ v'
  generalize ι.symm (η₁.val v : ℂˣ) = x at *
  generalize ι.symm (η₂.val v : ℂˣ) = y at *
  generalize ι.symm (η₁.val v' : ℂˣ) = x' at *
  generalize ι.symm (η₂.val v' : ℂˣ) = y' at *
  have hy : ‖y - 1‖ < 1 := by
    rwa [← mul_one_sub, norm_mul, n₁, one_mul, norm_sub_rev] at a₁
  rcases kk with h | h
  · refine hv ?_
    convert sm_sub (sm_sub h (sm_mul n₁.le a₂)) a₁ using 2
    ring
  · refine hv' ?_
    convert sm_add (sm_sub h (sm_mul n₄.le hy)) (sm_mul n₄.le a₂) using 2
    ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RROrdAbove
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.Gal.SV
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Win.RR.ordAbove_of_alt (hX : ExRS) (hGd : GdOf) :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.OrdAbove := by
  intro hP F Ω _ _ _ _ _ _ l _ hl _ ι ξ s c m a π r H w hw A h
  obtain ⟨-, hm, hs, ha, ⟨lam, hU, hlam⟩, hinf⟩ := H.above w hw
  obtain ⟨χ₀, hpol⟩ := H.pol
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results hP.toClassicalTheorems F 2 π w
  have hiso := hiso σ hσ
  obtain ⟨rc, hrc⟩ := recTExists F Ω A w h
  obtain ⟨ar, har, ε, hLV⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  have hq0 : ((normV w : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (one_lt_normV w).ne_bot
  have hqc : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (one_lt_normV w).ne_bot
  have hqn : ‖((normV w : ℕ) : Qbar l)‖ ≠ 0 := norm_ne_zero_iff.2 hq0
  have hn : ‖ι.symm lam * (normV w : Qbar l) ^ m w 0‖ = 1 := by
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := ι.symm lam * (normV w : Qbar l) ^ m w 0 - a w) (y := a w)
      (by rw [ha]; exact hlam.ne)
    rwa [sub_add_cancel, ha, max_eq_right hlam.le] at this
  have hl0 : lam ≠ 0 := by
    rintro rfl
    simp at hn
  have hn' : ‖ι.symm lam‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (-m w 0) := by
    rw [norm_mul, norm_zpow] at hn
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left hn
  obtain ⟨μ₁, μ₂, Lf, hL0, hunr, hval, hLf⟩ := _root_.UpperTheory.V.Sd.jacqOfU_alt hP.toClassicalTheorems F w σ 1 (Units.mk0 lam hl0) one_ne_zero
    (UpperTheory.hasUEigenvalue_of_locIsotypic F w _ π.finPart σ hiso 1 lam hU)
  obtain ⟨s1, s2, hsub, hcen⟩ := UpperTheory.isSubquotient_principalSeries_of_borel_functional F w σ μ₁ μ₂ Lf hL0 hLf
  set ω : Fin 2 → (w.adicCompletion F)ˣ →* ℂˣ := ![μ₁ * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1), μ₂] with hω
  have habs (t : Weil h) :
      (GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) (ar t) : ℂ) =
        ((normV w : ℕ) : ℂ) ^ GlobalTheory.SmGL.ord (w.adicCompletion F) (ar t) := by
    obtain ⟨hnorm, hord, -⟩ := (GlobalTheory.CompletionNorm.norm_nabs_valuation F w).1 (ar t)
    rw [GlobalTheory.SmGL.val_absPow, ← hnorm, hord, Complex.cpow_neg_one]
    push_cast
    rw [zpow_neg, inv_inv]
  have hω0 : ∀ t : Weil h, (ω 0 (ar t) : ℂ) = lam ^ (-deg t) := fun t => by
    have hvalAr : μ₁ (ar t) =
        μ₁ (atFin w (Formalism.L2.Host.unif w)) ^ GlobalTheory.SmGL.ord (w.adicCompletion F) (ar t) := by
      have hvaluation := ((GlobalTheory.CompletionNorm.norm_nabs_valuation F w).1 (ar t)).2.2
      have hvalUnif : Valued.v ((atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
          WithZero.exp (-1 : ℤ) := unif_spec w
      have hunit : IsUnitAt w (ar t *
          (atFin w (Formalism.L2.Host.unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion F) (ar t))⁻¹) := by
        unfold IsUnitAt
        rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀,
          map_zpow₀, hvaluation, hvalUnif, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
        simp
      have hchar := hunr _ hunit
      rwa [map_mul, map_inv, map_zpow, mul_inv_eq_one] at hchar
    change ((μ₁ (ar t) * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) (ar t) : ℂˣ) : ℂ) = _
    rw [Units.val_mul, habs, hvalAr, har.ord_eq,
      Units.val_zpow_eq_zpow_val, ← mul_zpow, mul_comm, hval]
    rfl
  have hsm : ∀ j, GlobalTheory.SmGL.IsSmoothChar (ω j) := by
    refine Fin.forall_fin_two.2 ⟨?_, s2⟩
    exact Subgroup.isOpen_mono (H₁ := μ₁.ker ⊓ (GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1)).ker)
      (fun x hx => by
        change μ₁ x * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) x = 1
        rw [hx.1, hx.2, mul_one])
      (IsOpen.inter s1 (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow _ _)))
  have hn0 : ∀ t : Weil h, ‖ι.symm (ω 0 (ar t) : ℂ)‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (m w 0 * deg t) := fun t => by
    rw [hω0, map_zpow₀, norm_zpow, hn', ← zpow_mul, neg_mul_neg]
  have hn1 : ∀ t : Weil h, ‖ι.symm (ω 1 (ar t) : ℂ)‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (m w 1 * deg t) := fun t => by
    have h1 := _root_.UpperTheory.V.Sd.OrdinaryAbove.central_weil_ordinary_above hP H hw h har hiso t _ (hcen (ar t))
    have h2 : ((μ₁ (ar t) * μ₂ (ar t) : ℂˣ) : ℂ) = (ω 0 (ar t) : ℂ) * (ω 1 (ar t) : ℂ) * ((normV w : ℕ) : ℂ) ^ deg t := by
      change _ = ((μ₁ (ar t) * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) (ar t) : ℂˣ) : ℂ) * (μ₂ (ar t) : ℂ) * _
      rw [Units.val_mul, Units.val_mul, habs, har.ord_eq, zpow_neg]
      field_simp
    rw [h2, map_mul, map_mul, norm_mul, norm_mul, hn0, map_zpow₀, map_natCast, norm_zpow, ← hs,
      show (m w 0 + m w 1 + 1) * deg t = m w 0 * deg t + m w 1 * deg t + deg t by ring, zpow_add₀ hqn, zpow_add₀ hqn] at h1
    exact mul_left_cancel₀ (zpow_ne_zero _ hqn) (mul_right_cancel₀ (zpow_ne_zero _ hqn) h1)
  have hcp := RR.ps_alg hLV σ ω hsm hsub
  obtain ⟨-, wt, HT, -, -, hall⟩ := hX F Ω l ι 2 one_le_two π χ₀ H.reg hpol
  have hG := hall r H.cont H.att
  have hpl := (Birth.ordPlain F Ω l ι ξ s c m a π r H w σ hσ).elim id fun ⟨B, hB⟩ => hG.plain w B hB σ hσ
  have hdr : Hi.DRat ι h (r.comp (Dec (F := F) A).subtype) (fun _ => Finset.univ.val.map fun j => -m w j)
      fun s => (rc (algNorm σ)).charPol s := by
    intro O _ _ _ Bw hj
    obtain ⟨k1, k2⟩ := hG.loc w σ hσ hpl
    obtain ⟨h1, h2⟩ := k2 A h O Bw hj
    refine ⟨h1, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
    · have e : HT τ = Finset.univ.val.map fun j => -m w j := by
        refine Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective ?_
        have hEmb : EmbAt w τ := by
          intro x
          rw [hτ]
          let τval := LL'.1.val.comp τ'
          let y : Bw.Kw.1 := ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩
          have hnorm : ‖τval y‖ = ‖(y : PadicAlgCl l)‖ := by
            rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
              minpoly.algHom_eq τval τval.injective, ← minpoly.algHom_eq Bw.Kw.1.val Bw.Kw.1.val.injective]
            rfl
          refine ((hj.valuation_lt_one_iff _).symm.trans (h x)).symm.trans ?_
          exact iff_of_eq (congrArg (· < 1) hnorm.symm)
        have := hG.weights τ _ (hinf τ hEmb)
        simp only [this, infOf, Multiset.map_map]
        exact Multiset.map_congr rfl fun i _ => by simp
      exact e ▸ h2 τ LL' τ' hτ
    · rw [((k1 A h rc hrc).2 O Bw hj (hGd F Ω A w h rc hrc 2 σ hpl)).2]
  rw [funext hcp] at hdr
  obtain ⟨κ, hκ, hv⟩ := _root_.UpperTheory.deRham_weights_of_localArtin_characters' hP.litN F Ω l hl ι 2 w hw A h ar har _ (H.cont.comp continuous_subtype_val) (m w)
    (fun i j hij => by fin_cases i <;> fin_cases j <;> first | exact hm | exact absurd hij (by decide)) ω hsm
    (Fin.forall_fin_two.2 ⟨hn0, hn1⟩) hdr
  have k0 : ∀ g : ↥(Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → κ 0 g = cycBar F Ω l g ^ m w 0 := fun g hg => by
    have h1 := hv 0 (ineIncl h ⟨g, hg⟩)
    rw [hω0, deg_ineIncl, mul_zero, zpow_zero, neg_zero, zpow_zero, map_one, mul_one, one_mul] at h1
    exact Units.ext (h1.trans (Units.val_zpow_eq_zpow_val _ _).symm)
  refine ⟨κ, hκ, Fin.forall_fin_two.2 ⟨k0, fun g hg => ?_⟩, fun g hg => ?_⟩
  · have h1 : Matrix.GeneralLinearGroup.det (r g) = κ 0 g * κ 1 g := by
      obtain ⟨b, hb⟩ := hκ
      have hdet : Matrix.GeneralLinearGroup.det (b * r g * b⁻¹) = Matrix.GeneralLinearGroup.det (r g) := by
        rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hb
      rw [← hdet]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hb g).2 0, (hb g).2 1,
        (hb g).1 1 0 (by decide)]
      simp
    have h2 : Matrix.GeneralLinearGroup.det (r g) = cycBar F Ω l g ^ s * ξ g := DFunLike.congr_fun H.det (g : G F Ω)
    have h3 : ξ g = 1 := (H.ram w A h).2 (Or.inr hw) hg
    rw [h3, mul_one, ← hs, _root_.zpow_add] at h2
    rw [k0 g hg] at h1
    exact mul_left_cancel (h1.symm.trans h2)
  · let t : Weil h := ⟨g, mem_Weil_of_isFrob h hg⟩
    have hd : deg t = 1 := deg_eq_one_iff.2 hg
    have h1 := hv 0 t⁻¹
    rw [hω0, deg_inv, hd, neg_neg, zpow_one, mul_neg_one, zpow_neg] at h1
    have h2 : (κ 0 g⁻¹ : Qbar l) * ((normV w : Qbar l) ^ m w 0)⁻¹ = ι.symm lam * (cycBar F Ω l (g : G F Ω)⁻¹ : Qbar l) ^ m w 0 := h1
    have h3 : ((κ 0 g⁻¹ * cycBar F Ω l (g : G F Ω) ^ m w 0 : (Qbar l)ˣ) : Qbar l) = ι.symm lam * (normV w : Qbar l) ^ m w 0 := by
      rw [mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hq0), map_inv (cycBar F Ω l), Units.val_inv_eq_inv_val (cycBar F Ω l _), inv_zpow] at h2
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, h2, mul_right_comm _ _ (_ ^ _), inv_mul_cancel_right₀ (zpow_ne_zero _ (Units.ne_zero _))]
    rw [h3]
    exact hlam
end
end

