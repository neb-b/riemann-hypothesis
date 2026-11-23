module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowers
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0107
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCompleteIsAlgClosedAddValuation
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ImaginaryRootConj
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesBoundedOneTorsionTranslateCmTheta
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslateNorm

theorem inOK_neg {d : ℕ} {z : ℂ} (h : InOK d z) : InOK d (-z) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨-u, -v, by push_cast; ring⟩

theorem thetaTranslateValueAtZero_neg (d : ℕ) (θ : ℂ → ℂ) (he : ∀ z, θ (-z) = θ z) (t z : ℂ) :
    U1 d (-t) θ z = U1 d t θ (-z) := by
  unfold U1 h1
  rw [← he (z + -t)]
  congr 2
  · ring
  · simp only [map_neg]; ring

theorem cmLatticeTranslationOperator_mul_neg_translate (d : ℕ) (θ : ℂ → ℂ) (t w : ℂ) :
    U1 d t θ w * U1 d (-t) θ (w + t) = θ w * θ (w + t) := by
  unfold U1 h1
  have h0 : w + t + -t = w := by ring
  rw [h0, mul_mul_mul_comm, ← Complex.exp_add]
  have : -(Real.pi : ℂ) * (((2 / Real.sqrt d : ℝ) : ℂ) * (w * conj t)) -
      (Real.pi : ℂ) / 2 * (((2 / Real.sqrt d : ℝ) : ℂ) * (t * conj t)) +
      (-(Real.pi : ℂ) * (((2 / Real.sqrt d : ℝ) : ℂ) * ((w + t) * conj (-t))) -
      (Real.pi : ℂ) / 2 * (((2 / Real.sqrt d : ℝ) : ℂ) * (-t * conj (-t)))) = 0 := by
    simp only [map_neg]; ring
  rw [this, Complex.exp_zero]; ring

theorem differentiable_cmLatticeTranslationOperator_of_diff (d : ℕ) (θ : ℂ → ℂ) (hθ : Differentiable ℂ θ) (t : ℂ) : Differentiable ℂ (U1 d t θ) := by
  unfold U1 h1
  fun_prop

theorem ell_shift {L : PeriodPair} {φ : ℂ → ℂ} (h : Ell L φ) (a : ℂ) : Ell L (fun z => φ (z + a)) := by
  refine ⟨fun x => ?_, fun l hl z => ?_⟩
  · have h1 : MeromorphicAt φ ((fun z : ℂ => z + a) x) := h.1 _
    exact h1.comp_analyticAt (f := φ) (g := fun z : ℂ => z + a) (by fun_prop)
  · have := h.2 l hl (z + a)
    show φ (z + l + a) = φ (z + a)
    rw [← this]; congr 1; ring

theorem bd_one_of_inv {q : ℕ} [Fact q.Prime] (f g : ℂ_[q]⟦X⟧) (hf : Bdd f) (hg : Bdd g) (hfg : f * g = 1)
    (h : ∀ B, Bd B g → Bd B f) : Bd 1 f := by
  have h1 : Bd 1 (f * g) := by
    rw [hfg]
    intro n
    rw [coeff_one]
    split_ifs <;> simp
  have hm := (sup_norm_laws q).2.2.2.1 f g 1 hf hg h1
  intro i
  by_contra hi
  push_neg at hi
  have hp : 0 < ‖coeff i f‖ := lt_trans one_pos hi
  have hb : Bd (1 / ‖coeff i f‖) g := fun j => by
    rw [le_div_iff₀ hp, mul_comm]; exact hm i j
  have := h _ hb i
  rw [le_div_iff₀ hp] at this
  nlinarith

theorem bd_translate : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ t : ℂ, PrimeTo d q t → ¬ InOK d (t - 1 / 2) → Bd 1 (hat M.ι (C ω * logS) (U1 d t θ)) := by
  intro d q _ M ω θ hd h16 hsp hOK hch hth t hpt hnt
  obtain ⟨s, hs, hsq, hst⟩ := id hpt
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  obtain ⟨hdiff, h0, hev, -, hz⟩ := id hth
  have hθt : θ t ≠ 0 := fun h => hnt (hz t h)
  have hP := GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic d q M ω θ hd h16 hsp hOK hch hth t s hs hsq hst
  have hN := GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic d q M ω θ hd h16 hsp hOK hch hth (-t) s hs hsq
    (by have := inOK_neg hst; rwa [← mul_neg] at this)
  simp only at hP hN
  set φp : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z) with hφp
  set φm : ℂ → ℂ := fun z => U1 d (-t) θ ((s : ℂ) * z) / θ ((s : ℂ) * z) with hφm
  obtain ⟨-, hPa, -, hPs, hPb⟩ := hP
  obtain ⟨hNe, hNa, hNp, -, hNb⟩ := hN
  set t' : ℂ := t / s with ht'
  have hst' : (s : ℂ) * t' = t := by rw [ht']; field_simp
  set ψ : ℂ → ℂ := fun z => φm (z + t') with hψ
  have hψe : Ell M.L ψ := ell_shift hNe t'
  have hψan : ∀ p, AnalyticAt ℂ φm (p + t') → AnalyticAt ℂ ψ p := fun p hp =>
    AnalyticAt.comp (g := φm) (f := fun z : ℂ => z + t') hp (by fun_prop)
  have hψ0 : AnalyticAt ℂ ψ 0 := hψan 0 (hNp _ (by rwa [zero_add, hst']))
  have hψt : AnalyticAt ℂ ψ (-t') := hψan _ (by rwa [neg_add_cancel])
  have hψp : ∀ p, meromorphicOrderAt ψ p < 0 → ¬ M.Small p := by
    intro p hp
    apply hPs p t hpt hnt
    by_contra hne
    have : AnalyticAt ℂ ψ p := hψan p (hNp _ (by rwa [mul_add, hst']))
    exact absurd this.meromorphicOrderAt_nonneg (not_le.mpr hp)
  have hψb := _root_.GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell q M _ ψ hch hψe hψ0 hψp
  have hback : (fun z => ψ (z + -t')) = φm := by
    funext z; simp [hψ]
  have hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hch.2.1
  have hat1 := TaylorRead.hat_laws q M.ι _ hℓ
  have hmul := MulSeries.mulS_laws q

  have hb1 : ∀ B, Bd B (hat M.ι (C ω * logS) ψ) → Bd B (hat M.ι (C ω * logS) φm) := by
    intro B hB
    by_cases hsm : M.Small (-t')
    · have hin : InOK d (-t') := (_root_.GlobalTheory.MomOne.smallTors d q M ω hd h16 hsp hOK hch).2.2.1 (-t')
        ⟨s * s, Nat.mul_pos hs hs, Nat.Coprime.mul_left hsq hsq, by
          have : ((s * s : ℕ) : ℂ) * (-t') = -((s : ℂ) * t) := by
            rw [← hst']; push_cast; ring
          rw [this]; exact inOK_neg hst⟩ hsm
      have hl : t' ∈ M.L.lattice := (hOK t').2 (by simpa using inOK_neg hin)
      have : ψ = φm := funext fun z => hNe.2 t' hl z
      rwa [← this]
    · have := _root_.GlobalTheory.MomOne.TransNorm.translate_norm_le q M _ ψ (-t') B hch hψe hψ0 hψt hψp hsm (by rwa [hback]) hB
      rwa [hback] at this

  have hmp : φm = fun z => φp ((-1 : ℂ) * z) := by
    funext z
    simp only [hφm, hφp]
    rw [thetaTranslateValueAtZero_neg d θ hev, ← hev ((s : ℂ) * z)]
    congr 2 <;> ring
  have hb2 : ∀ B, Bd B (hat M.ι (C ω * logS) φm) → Bd B (hat M.ι (C ω * logS) φp) := by
    intro B hB
    rw [hmp, (hat_multiplicative_chart q M.ι ω φp hPa).2.2.1 (-1) (-1) (by simp [zc])] at hB
    exact (hmul.2.2.2.1 (-1) _ B (by simp)).1 hB

  have hprod : hat M.ι (C ω * logS) φp * hat M.ι (C ω * logS) ψ = 1 := by
    rw [← (hat1.1 φp ψ hPa hψ0).2.1]
    have hc := hat1.2.1 1
    rw [map_one, map_one] at hc
    rw [← hc]
    apply (hat1.1 _ _ (hPa.mul hψ0) analyticAt_const).2.2.1
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    have c1 : ContinuousAt (fun z : ℂ => θ ((s : ℂ) * z)) 0 :=
      (hdiff.continuous.comp (by fun_prop)).continuousAt
    have c2 : ContinuousAt (fun z : ℂ => θ ((s : ℂ) * z + t)) 0 :=
      (hdiff.continuous.comp (by fun_prop)).continuousAt
    filter_upwards [c1.eventually_ne (y := 0) (by simp [h0]), c2.eventually_ne (y := 0) (by simpa using hθt)]
      with z hz1 hz2
    simp only [hψ, hφm, hφp, Pi.mul_apply]
    rw [mul_add, hst', div_mul_div_comm, cmLatticeTranslationOperator_mul_neg_translate]
    exact div_self (mul_ne_zero hz1 hz2)
  have hP1 : Bd 1 (hat M.ι (C ω * logS) φp) :=
    bd_one_of_inv _ _ hPb hψb hprod fun B hB => hb2 B (hb1 B hB)

  have hθa : AnalyticAt ℂ θ 0 := hdiff.analyticAt 0
  have hUa : AnalyticAt ℂ (U1 d t θ) 0 := (differentiable_cmLatticeTranslationOperator_of_diff d θ hdiff t).analyticAt 0
  set f : ℂ → ℂ := fun z => U1 d t θ z / θ z with hf
  have hfa : AnalyticAt ℂ f 0 := hUa.div hθa (by simp [h0])
  have hf1 : Bd 1 (hat M.ι (C ω * logS) f) := by
    have e := (hat_multiplicative_chart q M.ι ω f hfa).2.2.1 (s : ℂ) (s : ℤ_[q]) (by simp [zc])
    have e' : φp = fun z => f ((s : ℂ) * z) := rfl
    rw [e', e] at hP1
    exact (hmul.2.2.2.1 (s : ℤ_[q]) _ 1 (PadicInt.norm_natCast_eq_one_iff.2 hsq.symm)).1 hP1
  have hθ1 := _root_.GlobalTheory.MomOne.theta_series_integral d q M ω θ hd h16 hsp hOK hch hth
  have hfin : hat M.ι (C ω * logS) (U1 d t θ) = hat M.ι (C ω * logS) f * hat M.ι (C ω * logS) θ := by
    rw [← (hat1.1 f θ hfa hθa).2.1]
    apply (hat1.1 _ _ hUa (hfa.mul hθa)).2.2.1
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [hdiff.continuous.continuousAt.eventually_ne (y := 0) (x := 0) (by simp [h0])] with z hz1
    simp only [hf, Pi.mul_apply]
    rw [div_mul_cancel₀ _ hz1]
  rw [hfin]
  simpa using ((sup_norm_laws q).1 _ _ 1 1 hf1 hθ1).2

end GlobalTheory.MomOne.TranslateNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsClosedCompleteFieldOverPlace
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.PlaceClosedField

theorem vLa_pos_of_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    {x : 𝓞 K} (hx : x ∈ la.asIdeal) (h0 : x ≠ 0) : 0 < vLa la ((x : 𝓞 K) : K) := by
  have h1 : la.intValuation x < 1 := (la.intValuation_lt_one_iff_mem _).2 hx
  have h2 : WithZero.log (la.intValuation x) < 0 := by
    have := (WithZero.log_lt_log (la.intValuation_ne_zero _ h0) one_ne_zero).2 h1
    simpa using this
  have h : ((x : 𝓞 K) : K) = algebraMap (𝓞 K) K x := rfl
  rw [vLa, h, HeightOneSpectrum.valuation_of_algebraMap]
  omega

theorem ramOverZ_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    0 < ramOverZ la := by
  have h := Crude.crv_vLa_char la
  have h0 : ((resCharOf la : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (Crude.resCharOf_prime la).ne_zero
  have h1 := vLa_pos_of_mem la (Crude.crv_char_mem la) h0
  have h2 : ((((resCharOf la : ℕ) : 𝓞 K)) : K) = ((resCharOf la : ℕ) : K) := map_natCast (algebraMap (𝓞 K) K) _
  rw [h2, h] at h1
  exact_mod_cast h1

theorem vV_unit (T : CDVR) {x : T.V} (hx : IsUnit x) : vV T.V (algebraMap T.V T.Fr x) = 0 := by
  have h : valV T.V (algebraMap T.V T.Fr x) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hx
  simp [vV, h]

theorem le_nval_mul (T : CDVR) {e r : ℕ} (hr : 0 < r) (ν : ℝ) (x : T.Fr)
    (h : (((r : ℝ) * ν : ℝ) : EReal) ≤ nval T.V e x) : (ν : EReal) ≤ nval T.V (e * r) x := by
  by_cases hx : x = 0
  · subst hx; rw [nval_zero]; exact le_top
  rw [nval_of_ne hx, EReal.coe_le_coe_iff] at h ⊢
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Nat.cast_mul, ← div_div, le_div_iff₀ hr', mul_comm]
  exact h

theorem exists_closed_field_over_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∃ (C : Type) (_ : Field C) (_ : CharZero C) (V : VF C) (ι : T.Fr →+* C), V.l = resCharOf la ∧ EmbOK T V ι ∧ IsAlgClosed C ∧ (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) ∧ (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) ∧ (∀ m : ℕ, ¬ resCharOf la ∣ m → V.v (m : C) = 0) ∧ ∀ (y : IntFr Xo c T io) (C3 : IntChart T io y) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C3 e k a n → (ν : EReal) ≤ nuLocC C3 (eOf T V) k a n := by
  intro E _ _ _ H Dw lv Xo c _ la T io e ho
  have hp := Crude.resCharOf_prime la
  have hr := ramOverZ_pos la
  have he : 0 < e := ho.1
  have hv : vV T.V ((resCharOf la : ℕ) : T.Fr) = (e : ℤ) * (ramOverZ la : ℤ) := by
    rw [← map_natCast io, ho.2, Crude.crv_vLa_char]
  have hpos : (0 : ℤ) < (e : ℤ) * (ramOverZ la : ℤ) := by positivity
  have hnu : ¬ IsUnit ((resCharOf la : ℕ) : T.V) := by
    intro hu
    have h0 := vV_unit T hu
    rw [map_natCast, hv] at h0
    omega
  obtain ⟨C, _, _, v, ι, h1, h2, h3, h4⟩ :=
    GlobalTheory.DvrClosedEmbedding.exists_complete_isAlgClosed_addValuation T _ hp hnu
  refine ⟨C, inferInstance, inferInstance, ⟨v, resCharOf la, hp, h1⟩, ι, rfl, h2, h3, h4, ?_, ?_, ?_⟩
  · intro x hx
    show (0 : WithTop ℝ) < v _
    by_cases h0 : x = 0
    · subst h0; simp
    have hx0 : ((x : 𝓞 c.F) : c.F) ≠ 0 := by simpa using h0
    rw [h2 _ ((map_ne_zero io).2 hx0), ho.2, hv]
    have := vLa_pos_of_mem la hx h0
    have h5 : (0 : ℝ) < (((e : ℤ) * vLa la ((x : 𝓞 c.F) : c.F) : ℤ) : ℝ) / (((e : ℤ) * (ramOverZ la : ℤ) : ℤ) : ℝ) := by
      apply div_pos
      · exact_mod_cast mul_pos (by exact_mod_cast he) this
      · exact_mod_cast hpos
    exact_mod_cast h5
  · intro m hm
    have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero _)
    have hm1 : ((m : ℕ) : c.F) ≠ 0 := by exact_mod_cast hm0
    show v (m : C) = 0
    rw [← map_natCast ι, ← map_natCast io, h2 _ ((map_ne_zero io).2 hm1), ho.2, Crude.crv_vLa_coprime la hm]
    simp
  · intro y C3 k a n ν h
    have hE : eOf T (⟨v, resCharOf la, hp, h1⟩ : VF C) = e * ramOverZ la := by
      show (vV T.V ((resCharOf la : ℕ) : T.Fr)).toNat = _
      rw [hv, ← Nat.cast_mul, Int.toNat_natCast]
    rw [hE]
    unfold nuLocC at h ⊢
    simp only [le_iInf_iff] at h ⊢
    intro P hP f hf
    exact le_nval_mul T hr ν _ (h P hP f hf)

end GlobalTheory.PlaceClosedField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFrobAllEmbeddings
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

def frobKer {R C : Type} [CommRing R] [Field C] (V : VF C) (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : Ideal R where
  carrier := {x | V.MM (f x)}
  add_mem' := fun {a b} ha hb => by
    show 0 < V.v (f (a + b))
    rw [map_add (f := _)]
    exact V.v.map_lt_add ha hb
  zero_mem' := by
    show 0 < V.v (f 0)
    rw [map_zero, V.v.map_zero]
    exact WithTop.coe_lt_top (0 : ℝ)
  smul_mem' := fun a b hb => by
    show 0 < V.v (f (a * b))
    rw [map_mul, V.v.map_mul]
    exact lt_of_lt_of_le hb (le_add_of_nonneg_left (hf a))

theorem frobKer_isPrime {R C : Type} [CommRing R] [Field C] (V : VF C) (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) :
    (frobKer V f hf).IsPrime := by
  constructor
  · rw [Ideal.ne_top_iff_one]
    show ¬ 0 < V.v (f 1)
    rw [map_one, V.v.map_one]
    exact lt_irrefl _
  · intro a b h
    have h' : 0 < V.v (f (a * b)) := h
    rw [map_mul, V.v.map_mul] at h'
    change 0 < V.v (f a) ∨ 0 < V.v (f b)
    by_contra! hn
    exact (not_le_of_gt h') (add_nonpos hn.1 hn.2)

theorem exists_frob_of_hom {E C : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field C] (V : VF C)
    (f : 𝓞 E →+* C) (hf : ∀ x, V.Ge 0 (f x)) :
    ∃ φ : E ≃ₐ[ℚ] E, ∀ x : 𝓞 E, V.MM (f (φ • x) - f x ^ V.l) := by
  set P := frobKer V f hf with hP
  haveI : P.IsPrime := frobKer_isPrime V f hf
  have hl : ((V.l : ℕ) : 𝓞 E) ∈ P := by
    show 0 < V.v (f _)
    rw [map_natCast, V.v_l]
    exact zero_lt_one
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hl
    exact V.l_prime.ne_zero (by exact_mod_cast hl)
  haveI : Finite (𝓞 E ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  have hu : P.under ℤ = Ideal.span {(V.l : ℤ)} := by
    have hmax : (Ideal.span {(V.l : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast V.l_prime.ne_zero)).2
        (Nat.prime_iff_prime_int.1 V.l_prime)).isMaximal (by
          rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast V.l_prime.ne_zero)
    refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hl
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) P
  refine ⟨φ, fun x => ?_⟩
  have h := hφ x
  rw [hu, Int.card_ideal_quot] at h
  have h' : V.MM (f (φ • x - x ^ V.l)) := h
  rwa [map_sub, map_pow] at h'

theorem exists_aut_comp_eq {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (τ₀ τ : E →+* ℂ) :
    ∃ σ : E ≃ₐ[ℚ] E, τ = τ₀.comp (σ : E →+* E) := by
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) τ₀ τ (Subsingleton.elim _ _)
  exact ⟨σ.symm, hσ.symm⟩

theorem exists_frob_all_embeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → IsGalois ℚ E → (∀ σ σ' : E ≃ₐ[ℚ] E, σ * σ' = σ' * σ) → ∃ φ : E ≃ₐ[ℚ] E, ∀ (τ : E →+* ℂ) (x : 𝓞 E), V.MM (emA3 io ι (τ.comp (φ : E →+* E)) x - emA3 io ι τ x ^ V.l) := by
  intro E _ _ _ H lv c T io C _ _ V ι hι hG hab
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have key : ∀ (τ : E →+* ℂ) (s : E ≃ₐ[ℚ] E) (x : 𝓞 E),
      emA3 io ι (τ.comp (s : E →+* E)) x = emA3 io ι τ (s • x) := fun τ s x => rfl
  obtain ⟨φ, hφ⟩ := exists_frob_of_hom V (emA3 io ι τ₀)
    (fun x => GlobalTheory.RowChartCounterexample.em_int_holds τ₀ x hι)
  refine ⟨φ, fun τ x => ?_⟩
  obtain ⟨σ, rfl⟩ := exists_aut_comp_eq τ₀ τ
  rw [key, key, key, ← mul_smul, hab, mul_smul]
  exact hφ _

end GlobalTheory.RowAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMoveBack
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Jets


open TopologicalSpace in
theorem exists_gen_move_back : ∀ (Y Y' X₁ X₂ W : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂), L₁.IsLB → L₂.IsLB → ∀ (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → ∀ (K : Type) [Fintype K] (m : K → (Y' ⟶ Y)) (ε : K → ℤ) (φ₁ : K → (Y' ⟶ X₁)), (∀ k, φ₁ k = m k ≫ f₁) → ∀ (φ₂ : K → (W ⟶ X₂)) (h : Y' ⟶ W), (∀ k, h ≫ φ₂ k = m k ≫ f₂) → ∀ t : LB.Gen (LB.LinComb L₂ φ₂ ε), t.IsGen → ∃ a : LB.Gen (LB.LinComb L₁ φ₁ ε), a.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J₂ : (Z ⟶ X₂) → L₂.ι) (J₁ : (Z ⟶ X₁) → L₁.ι), Good L₂ z J₂ → Good L₁ z J₁ → val t (r ≫ h) z J₂ = (∏ k, isoVal w (r ≫ m k) z (J₂ ((r ≫ m k) ≫ f₂)) (J₁ ((r ≫ m k) ≫ f₁)) ^ ε k) * val a r z J₁ := by
  intro Y Y' X₁ X₂ W L₁ L₂ hL₁ hL₂ f₁ f₂ w hw K _ m ε φ₁ e₁ φ₂ h hc t ht
  classical
  obtain rfl : φ₁ = fun k => m k ≫ f₁ := funext e₁
  let O : (K → L₁.ι) → (K → L₂.ι) → Y'.Opens := fun q p =>
    LB.wchart L₁ (fun k => m k ≫ f₁) q ⊓ LB.wchart L₂ (fun k => m k ≫ f₂) p
  have pt : ∀ k y, φ₂ k (h y) = f₂ (m k y) := fun k y => congrArg (fun q : Y' ⟶ X₂ => q y) (hc k)
  have le1 : ∀ q p k, O q p ≤ m k ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => p k) ⊓ (L₁.pull f₁).U (fun _ => q k)) :=
    fun q p k y hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy.2 k), mem_pull.2 (Set.mem_iInter.1 hy.1 k)⟩
  have le2 : ∀ q p, O q p ≤ h ⁻¹ᵁ LB.wchart L₂ φ₂ p := fun q p y hy => Set.mem_iInter.2 fun k => by
    show φ₂ k (h y) ∈ L₂.U (p k)
    rw [pt]; exact Set.mem_iInter.1 hy.2 k
  let v : ∀ q p, Γ(Y', O q p)ˣ := fun q p =>
    (∏ k, res (le1 q p k) (pullU (m k) _ (w.s (fun _ => p k, fun _ => q k))) ^ ε k)⁻¹ *
      res (le2 q p) (pullU h _ (t.s p))
  have germ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (O q p) (v q p) =
        (∏ k, isoVal w (r ≫ m k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L₂ φ₂ p) (t.s p) := by
    intro Z r z q p hz
    have m2 := le2 q p hz
    show gm r z (O q p) ((∏ k, _)⁻¹ * _) = _
    rw [map_mul, map_inv, map_prod]
    refine congrArg₂ (· * ·) (congrArg (·⁻¹) (Finset.prod_congr rfl fun k _ => ?_))
      ((gm_res r z (le2 q p) hz _).trans (gm_pull r h z _ m2 _))
    have m1 := le1 q p k hz
    exact (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z (le1 q p k) hz _).trans
      (gm_pull r (m k) z _ m1 _)))
  have memO : ∀ q (y : Y'), y ∈ LB.wchart L₁ (fun k => m k ≫ f₁) q → ∃ p, y ∈ O q p := fun q y hy => by
    choose p hp using fun k => exists_chart hL₂ (f₂ (m k y))
    exact ⟨p, hy, Set.mem_iInter.2 fun k => hp k⟩
  have glue : ∀ q, ∃ s : Γ(Y', LB.wchart L₁ (fun k => m k ≫ f₁) q)ˣ,
      ∀ p, res (inf_le_left : O q p ≤ _) s = v q p := by
    intro q
    refine glue_unit _ (O q) (fun p => inf_le_left) (fun y hy => ?_) (v q) fun p p' y hy => ?_
    · obtain ⟨p, hp⟩ := memO q y hy
      exact Opens.mem_iSup.2 ⟨p, hp⟩
    · rw [germ _ _ y q p hy.1, germ _ _ y q p' hy.2]
      have hp : ∀ k, f₂ (m k y) ∈ L₂.U (p k) := fun k => Set.mem_iInter.1 hy.1.2 k
      have hp' : ∀ k, f₂ (m k y) ∈ L₂.U (p' k) := fun k => Set.mem_iInter.1 hy.2.2 k
      have hq : ∀ k, f₁ (m k y) ∈ L₁.U (q k) := fun k => Set.mem_iInter.1 hy.1.1 k
      have e1 : ∀ k, isoVal w (𝟙 Y' ≫ m k) y (p k) (q k) =
          gm (m k ≫ f₂) y _ (L₂.g (p k) (p' k)) * isoVal w (𝟙 Y' ≫ m k) y (p' k) (q k) := fun k => by
        rw [Category.id_comp, GlobalTheory.FieldBaseChange.isoVal_trans hw (m k) y (hp k) (hp' k) (hq k) (hq k),
          gm_self hL₁ (m k ≫ f₁) y (hq k), inv_one, _root_.mul_one]
      have e2 : trF φ₂ ε (𝟙 Y' ≫ h) y p p' = ∏ k, gm (m k ≫ f₂) y _ (L₂.g (p k) (p' k)) ^ ε k :=
        Finset.prod_congr rfl fun k _ => by rw [Category.id_comp, hc k]
      rw [gen_trans ht (𝟙 Y' ≫ h) y (le2 q p hy.1) (le2 q p' hy.2), e2]
      simp only [e1, mul_zpow, Finset.prod_mul_distrib, mul_inv_rev]
      rw [_root_.mul_assoc, inv_mul_cancel_left]
  choose s hs using glue
  have vals : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (LB.wchart L₁ (fun k => m k ≫ f₁) q) (s q) =
        (∏ k, isoVal w (r ≫ m k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L₂ φ₂ p) (t.s p) := by
    intro Z r z q p hz
    rw [← gm_res r z (inf_le_left : O q p ≤ _) hz, hs q p, germ Z r z q p hz]
  refine ⟨⟨s⟩, fun q q' => unit_ext fun y hy => ?_, fun Z r z J₂ J₁ hJ₂ hJ₁ => ?_⟩
  · have hq : ∀ k, f₁ (m k y) ∈ L₁.U (q k) := fun k => Set.mem_iInter.1 hy.1 k
    have hq' : ∀ k, f₁ (m k y) ∈ L₁.U (q' k) := fun k => Set.mem_iInter.1 hy.2 k
    choose p hp using fun k => exists_chart hL₂ (f₂ (m k y))
    have m0 : y ∈ O q p := ⟨hy.1, Set.mem_iInter.2 fun k => hp k⟩
    have m' : y ∈ O q' p := ⟨hy.2, Set.mem_iInter.2 fun k => hp k⟩
    rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy]
    show gm (𝟙 Y') y (LB.wchart L₁ (fun k => m k ≫ f₁) q) (s q) =
      gm (𝟙 Y') y (LB.wchart L₁ (fun k => m k ≫ f₁) q ⊓ LB.wchart L₁ (fun k => m k ≫ f₁) q')
      ((LB.LinComb L₁ (fun k => m k ≫ f₁) ε).g q q') * gm (𝟙 Y') y (LB.wchart L₁ (fun k => m k ≫ f₁) q') (s q')
    rw [gm_linComb L₁ (fun k => m k ≫ f₁) ε (𝟙 Y') y q q' hy.1 hy.2, vals _ _ y q p m0, vals _ _ y q' p m']
    have e3 : ∀ k, isoVal w (𝟙 Y' ≫ m k) y (p k) (q k) =
        (gm (𝟙 Y' ≫ m k ≫ f₁) y _ (L₁.g (q k) (q' k)))⁻¹ * isoVal w (𝟙 Y' ≫ m k) y (p k) (q' k) := fun k => by
      rw [Category.id_comp, Category.id_comp,
        GlobalTheory.FieldBaseChange.isoVal_trans hw (m k) y (hp k) (hp k) (hq k) (hq' k),
        gm_self hL₂ (m k ≫ f₂) y (hp k), _root_.one_mul]
    simp only [e3, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv_rev, inv_inv]
    exact (congrArg (· * _) (mul_comm _ _)).trans (_root_.mul_assoc _ _ _)
  · have m0 : r z ∈ O (fun k => J₁ ((r ≫ m k) ≫ f₁)) (fun k => J₂ ((r ≫ m k) ≫ f₂)) :=
      ⟨Set.mem_iInter.2 fun k => hJ₁ ((r ≫ m k) ≫ f₁), Set.mem_iInter.2 fun k => hJ₂ ((r ≫ m k) ≫ f₂)⟩
    rw [val_of t (r ≫ h) z J₂ (fun k => J₂ ((r ≫ m k) ≫ f₂))
        (fun k => by rw [Category.assoc, hc k, Category.assoc]),
      val_of _ r z J₁ (fun k => J₁ ((r ≫ m k) ≫ f₁)) (fun k => by rw [Category.assoc])]
    show _ = _ * gm r z (LB.wchart L₁ (fun k => m k ≫ f₁) _) (s _)
    rw [vals Z r z _ _ m0, mul_inv_cancel_left]

end GlobalTheory.Jets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedLatticeExponentEqRoundedDepthGoodPlaceStatement
section
open Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.onObj_exponent_eq_rounded_depth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) lv) (c : Coeff lv) [StarRing (𝓞 E)] (Dd : DepData E)
  (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ),
  (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) →
  (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O →
  ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J), ¬ (plc v ∈ O.sm ∨ plc v = O.q1 ∨ plc v = O.dd ∨ plc v = O.g1 ∨ plc v = O.g2) →
    O.e0 v j ≤ (Dd.Q.T : ℝ) * ((nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j)).toReal / (ramOverZ (placeBelow (K := c.F) v) : ℝ)) + 1 ∧
    (nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j) = 0 → O.e0 v j = 0) := by
  first | exact @GlobalTheory.GoodDepth.normalizedLattice_exponent_eq_roundedDepth_goodPlace | exact GlobalTheory.GoodDepth.normalizedLattice_exponent_eq_roundedDepth_goodPlace | (intros; apply GlobalTheory.GoodDepth.normalizedLattice_exponent_eq_roundedDepth_goodPlace <;> assumption)
end

