module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0066
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpValuationCentre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingFrac
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpLocRingFrac.proof (hiso : BlowUpLocRingIso.Statement.{u})
    (hfam : BlowUpOverLocFamilyFinite.Statement.{u}) (havoid : MultiHomogPrimeAvoid.Statement.{u}) :
    BlowUpLocRingFrac.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW' hW'rel hW'W
  have hW'p : W'.IsPrime := hW'.1.1
  have hbl : blowUpOf P u ≤ W' := le_trans le_sup_left hW'.1.2
  have hmh : IsMultiHomogIdeal W' :=
    MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  obtain ⟨e, L, hL, he, hLQ⟩ := havoid O (Option K) (extIdx ι J) _
    (hfam O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel) (fun Q hQ => ⟨hQ.1, hQ.2.1, hQ.2.2.1⟩)
  have hW'fam : W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W := ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := hiso O K ι J P u W' hbl

  have hne : ∀ (d : Option K → ℕ) (H : MRing (extIdx ι J) O), IsMultiHomog H d → H ∉ W' →
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u H) ≠ 0 := by
    intro d H hH hHW h0
    have h1 := hφ d H H hH hH hHW
    rw [h0, div_zero] at h1
    have h2 : (⟨_, Subring.subset_closure ⟨d, H, H, hH, hH, hHW, rfl⟩⟩ :
        homLocRing (blowUpOf P u) W') = 1 := by
      apply Subtype.ext
      show _ / _ = (1 : FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
      apply div_self
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => hHW (hbl h)
    rw [h2, map_one] at h1
    exact one_ne_zero h1

  have hgen : ∀ (b : Option K → ℕ) (F G : MRing (extIdx ι J) O), IsMultiHomog F b → IsMultiHomog G b →
      G ∉ W' → ∃ bb ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
        (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) * s = bb := by
    intro b F G hF hG hGW
    set k := ∑ o, b o with hk
    obtain ⟨M, hM, hMW⟩ := homLocRing_form_not_mem hW'p hW'rel (fun o => k * e o - b o)
    have hdeg : b + (fun o => k * e o - b o) = k • e := by
      funext o
      have : b o ≤ k * e o := le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ o)) (Nat.le_mul_of_pos_right _ (he o))
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      omega
    have hFM : IsMultiHomog (F * M) (k • e) := hdeg ▸ hF.mul hM
    have hGM : IsMultiHomog (G * M) (k • e) := hdeg ▸ hG.mul hM
    have hLk : IsMultiHomog (L ^ k) (k • e) := hL.pow k
    have hLkQ : ∀ Q : Ideal (MRing (extIdx ι J) O), Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
        blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W → L ^ k ∉ Q :=
      fun Q hQ h => hLQ Q hQ (hQ.1.mem_of_pow_mem k h)
    have hmemB : ∀ H, IsMultiHomog H (k • e) →
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u H) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (L ^ k)) ∈
          blowUpOverLoc P W u := fun H hH =>
      Subring.mem_iInf.mpr fun Q => Subring.mem_iInf.mpr fun hQ =>
        Subring.subset_closure ⟨k • e, H, L ^ k, hH, hLk, hLkQ Q hQ, rfl⟩
    have hGMW : G * M ∉ W' := fun h => (hW'p.mem_or_mem h).elim hGW hMW
    have hLkW : L ^ k ∉ W' := hLkQ W' hW'fam
    have hG0 := hne _ _ hG hGW
    have hGM0 := hne _ _ hGM hGMW
    have hLk0 := hne _ _ hLk hLkW
    refine ⟨_, hmemB _ hFM, _, hmemB _ hGM, ⟨_,
      Subring.subset_closure ⟨k • e, L ^ k, G * M, hLk, hGM, hGMW, rfl⟩, ?_⟩, ?_⟩
    · rw [div_mul_div_comm, mul_comm]
      exact div_self (mul_ne_zero hLk0 hGM0)
    · rw [map_mul, map_mul] at hGM0 ⊢
      rw [map_mul, map_mul]
      field_simp
  intro z hz
  induction hz using Subring.closure_induction with
  | mem z hz =>
    obtain ⟨b, F, G, hF, hG, hGW, rfl⟩ := hz
    exact hgen b F G hF hG hGW
  | zero => exact ⟨0, zero_mem _, 1, one_mem _, ⟨1, one_mem _, mul_one 1⟩, zero_mul 1⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, ⟨1, one_mem _, mul_one 1⟩, one_mul 1⟩
  | add x y _ _ h₁ h₂ =>
    obtain ⟨b₁, hb₁, s₁, hs₁, ⟨t₁, ht₁, hst₁⟩, hx₁⟩ := h₁
    obtain ⟨b₂, hb₂, s₂, hs₂, ⟨t₂, ht₂, hst₂⟩, hx₂⟩ := h₂
    refine ⟨b₁ * s₂ + b₂ * s₁, add_mem (mul_mem hb₁ hs₂) (mul_mem hb₂ hs₁), s₁ * s₂, mul_mem hs₁ hs₂,
      ⟨t₁ * t₂, mul_mem ht₁ ht₂, by rw [mul_mul_mul_comm, hst₁, hst₂, one_mul]⟩, ?_⟩
    rw [← hx₁, ← hx₂]
    ring
  | neg x _ h =>
    obtain ⟨b₁, hb₁, s₁, hs₁, ht, hx₁⟩ := h
    exact ⟨-b₁, neg_mem hb₁, s₁, hs₁, ht, by rw [← hx₁]; ring⟩
  | mul x y _ _ h₁ h₂ =>
    obtain ⟨b₁, hb₁, s₁, hs₁, ⟨t₁, ht₁, hst₁⟩, hx₁⟩ := h₁
    obtain ⟨b₂, hb₂, s₂, hs₂, ⟨t₂, ht₂, hst₂⟩, hx₂⟩ := h₂
    refine ⟨b₁ * b₂, mul_mem hb₁ hb₂, s₁ * s₂, mul_mem hs₁ hs₂,
      ⟨t₁ * t₂, mul_mem ht₁ ht₂, by rw [mul_mul_mul_comm, hst₁, hst₂, one_mul]⟩, ?_⟩
    rw [← hx₁, ← hx₂]
    ring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocCentreDom
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocCentreDom.proof : BlowUpOverLocCentreDom.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro 𝔫 h𝔫
  have hW : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  obtain ⟨V, hBV, hnV⟩ := Ideal.image_subset_nonunits_valuationSubring 𝔫 h𝔫.ne_top
  obtain ⟨W', hp, hh, hr, hb, hc, hloc⟩ := exists_blowUp_centre (J := J) P W hP.multiProj.multiHomog hW hPW
    hWrel N u hu hu' V ((homLocRing_le_blowUpOverLoc P W u).trans hBV)
  have h : blowUpOverLoc P W u ≤ blowUpLocRing P u W' := iInf₂_le W' ⟨hp, hh, hr, hb, hc⟩
  refine ⟨W', hp, hh, hr, hb, hc, h, fun y hy hunit => ?_⟩
  obtain ⟨w, hw⟩ := hunit
  obtain ⟨hyV, hymax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := V)).1
    (hnV ⟨y, hy, rfl⟩)
  have hinv : ((w⁻¹ : (blowUpLocRing P u W')ˣ) : FractionRing (MRing ι O ⧸ P)) ∈ V := hloc ((w⁻¹ : (blowUpLocRing P u W')ˣ) : blowUpLocRing P u W').2
  have hmul : (y : FractionRing (MRing ι O ⧸ P)) * ((w⁻¹ : (blowUpLocRing P u W')ˣ) : _) = 1 := by
    have h1 := congrArg Subtype.val w.mul_inv
    rw [hw] at h1
    exact h1
  exact (IsLocalRing.mem_maximalIdeal _).1 hymax (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext hmul))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocFibreMinimal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocFibreMinimal.proof (h₁ : BlowUpOverLocPointLoc.Statement.{u})
    (h₂ : BlowUpLocRingInj.Statement.{u}) : BlowUpOverLocFibreMinimal.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  have := hP.multiProj.isPrime
  have hxW : x ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  have hxW' : liftForm x ∈ W' := by
    rw [← Ideal.mem_comap, hW'c]
    exact hxW
  have hle : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ W' :=
    sup_le hW'le ((Ideal.span_singleton_le_iff_mem _).mpr hxW')
  refine ⟨⟨hW'p, hle⟩, fun Q hQ hQW' => ?_⟩
  have := hQ.1
  obtain ⟨Q₀, hQ₀min, hQ₀Q⟩ := Ideal.exists_minimalPrimes_le hQ.2
  have hQ₀W' : Q₀ ≤ W' := hQ₀Q.trans hQW'
  have hQ₀p : Q₀.IsPrime := hQ₀min.1.1
  have hQ₀h : IsMultiHomogIdeal Q₀ :=
    MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ Q₀
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hQ₀min
  have hQ₀r : IsRelevant Q₀ := fun k => by
    obtain ⟨i, hi⟩ := hW'r k
    exact ⟨i, fun h => hi (hQ₀W' h)⟩
  have hQ₀le : blowUpOf P u ≤ Q₀ := le_sup_left.trans hQ₀min.1.2
  have hQ₀c : Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) = W := by
    obtain ⟨hcp, hPc, -, -⟩ := comap_liftForm_facts hQ₀p hQ₀le hQ₀r
    have hxc : x ∈ Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) :=
      hQ₀min.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hcW : Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W := hW'c ▸ Ideal.comap_mono hQ₀W'
    exact le_antisymm hcW (hWmin.2 ⟨hcp, sup_le hPc ((Ideal.span_singleton_le_iff_mem _).mpr hxc)⟩ hcW)
  obtain ⟨h, 𝔫, h𝔫, hl⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  obtain ⟨h₀, 𝔮, h𝔮, hl₀⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel Q₀ hQ₀p hQ₀h hQ₀r hQ₀le hQ₀c
  have hsub : blowUpLocRing P u W' ≤ blowUpLocRing P u Q₀ := by
    refine Subring.closure_mono ?_
    rintro z ⟨b, F, G, hF, hG, hGW', hz⟩
    exact ⟨b, F, G, hF, hG, fun hGQ => hGW' (hQ₀W' hGQ), hz⟩
  let _ := (Subring.inclusion h).toAlgebra
  let _ := (Subring.inclusion h₀).toAlgebra
  have := h𝔫.isPrime
  have := h𝔮.isPrime
  have : IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫 := hl
  have : IsLocalization.AtPrime (blowUpLocRing P u Q₀) 𝔮 := hl₀
  have : IsLocalRing (blowUpLocRing P u Q₀) := IsLocalization.AtPrime.isLocalRing _ 𝔮
  have hq : 𝔮 ≤ 𝔫 := by
    intro s hs
    by_contra hsn
    have hu1 : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W') s) :=
      IsLocalization.map_units (M := 𝔫.primeCompl) _ ⟨s, hsn⟩
    have hu2 : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u Q₀) s) :=
      hu1.map (Subring.inclusion hsub)
    have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff (blowUpLocRing P u Q₀) 𝔮 s).mpr hs
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu2
  have hqn : 𝔮 = 𝔫 := h𝔮.eq_of_le h𝔫.ne_top hq
  have hsup : blowUpLocRing P u Q₀ ≤ blowUpLocRing P u W' := by
    intro z hz
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl
      (⟨z, hz⟩ : blowUpLocRing P u Q₀)
    replace hbs : IsLocalization.mk' (blowUpLocRing P u Q₀) b s = ⟨z, hz⟩ := hbs
    have hs : (s : blowUpOverLoc P W u) ∈ 𝔫.primeCompl := hqn ▸ s.2
    obtain ⟨v, hv⟩ : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W') s) :=
      IsLocalization.map_units (M := 𝔫.primeCompl) _ ⟨s, hs⟩
    have e1 : z * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) =
        ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) := by
      have := congrArg Subtype.val (IsLocalization.mk'_spec (blowUpLocRing P u Q₀) b s)
      rw [hbs] at this
      exact this
    have e2 : ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) *
        (((v⁻¹ : (blowUpLocRing P u W')ˣ) : blowUpLocRing P u W') : FractionRing (MRing ι O ⧸ P)) = 1 := by
      have := congrArg Subtype.val v.mul_inv
      rw [hv] at this
      exact this
    have e3 : z = ((algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W') b *
        ((v⁻¹ : (blowUpLocRing P u W')ˣ) : blowUpLocRing P u W') : blowUpLocRing P u W') :
          FractionRing (MRing ι O ⧸ P)) := by
      rw [Subring.coe_mul, ← mul_one z, ← e2, ← mul_assoc, e1]
      rfl
    rw [e3]
    exact Subtype.property _
  have heq : Q₀ = W' :=
    h₂ O K ι J P u Q₀ W' hQ₀p hQ₀h hQ₀r hQ₀le hW'p hW'h hW'r hW'le (le_antisymm hsup hsub)
  rw [← heq]
  exact hQ₀Q

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocMaxCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocMaxCentre.proof (h₁ : BlowUpOverLocCentreDom.Statement.{u})
    (h₂ : BlowUpOverLocLocalization.Statement.{u}) (h₃ : BlowUpOverLocFinite.Statement.{u})
    (h₄ : BlowUpLocRingIso.Statement.{u}) :
    BlowUpOverLocMaxCentre.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro 𝔫 h𝔫
  obtain ⟨W', hW'p, hW'h, hW'r, hW'le, hW'c, h, hdom⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫
  obtain ⟨h', 𝔭, h𝔭, hl⟩ :=
    h₂ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  let _ := (Subring.inclusion h).toAlgebra
  have hl' : IsLocalization.AtPrime (blowUpLocRing P u W') 𝔭 := hl
  have hn𝔭 : 𝔫 ≤ 𝔭 := fun b hb => by
    by_contra hb𝔭
    exact hdom b hb ((IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔭 b).2 hb𝔭)
  obtain rfl : 𝔫 = 𝔭 := h𝔫.eq_of_le h𝔭.ne_top hn𝔭
  refine ⟨W', hW'p, hW'h, hW'r, hW'le, le_antisymm hW'c ?_, h, hl'⟩
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_trans le_sup_left hWmin.1.2
  have hWmh : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.full O K ι _ W
      (SupSpanMultiHomog.full O K ι P x c hP.multiProj.multiHomog hx) hWmin
  obtain ⟨hAloc, hAunit⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW
  obtain ⟨hfin, -⟩ := h₃ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have : Algebra.IsIntegral (homLocRing P W) (blowUpOverLoc P W u) := Algebra.IsIntegral.of_finite _ _
  have hmax : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := homLocRing P W) 𝔫
  have hcomap : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) =
      IsLocalRing.maximalIdeal (homLocRing P W) := IsLocalRing.eq_maximalIdeal hmax
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := h₄ O K ι J P u W' hW'le
  obtain ⟨-, hBunit⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J)
    (blowUpOf P u) W' hW'p hW'le
  have key : ∀ (b : K → ℕ) (w : MRing ι O), IsMultiHomog w b → w ∈ W →
      liftForm (J := J) w ∈ W' := by
    intro b w hw hwW
    by_contra hwW'
    obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hWrel b
    have hg := isMultiHomog_powMonomial (R := O) b i
    have hgW' : liftForm (J := J) (powMonomial b i) ∉ W' := fun hg' => hi (hW'c hg')
    have hzA := Subring.subset_closure (s := {z | ∃ (b : K → ℕ) (f g : MRing ι O), IsMultiHomog f b ∧
      IsMultiHomog g b ∧ g ∉ W ∧
      z = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P f) /
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g)})
      ⟨b, w, powMonomial b i, hw, hg, hi, rfl⟩
    have hm : (⟨_, hzA⟩ : homLocRing P W) ∈
        𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) := by
      rw [hcomap]
      exact fun hu => (hAunit b w _ hw hg hi hzA).1 hu hwW
    have hzB : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
          (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
          (Ideal.Quotient.mk (blowUpOf P u) (liftForm w)) /
        algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
          (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
          (Ideal.Quotient.mk (blowUpOf P u) (liftForm (powMonomial b i))) ∈
        homLocRing (blowUpOf P u) W' := by
      unfold homLocRing
      exact Subring.subset_closure ⟨liftMDeg b, liftForm w, liftForm (powMonomial b i),
        isMultiHomog_liftForm hw, isMultiHomog_liftForm hg, hgW', rfl⟩
    have hU := ((hBunit (liftMDeg b) (liftForm w) (liftForm (powMonomial b i))
      (isMultiHomog_liftForm hw) (isMultiHomog_liftForm hg) hgW' hzB).2 hwW').map φ
    have hval : φ ⟨_, hzB⟩ =
        algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W')
          (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hzA⟩) := by
      apply Subtype.ext
      rw [hφ (liftMDeg b) _ _ (isMultiHomog_liftForm hw) (isMultiHomog_liftForm hg) hgW',
        blowUpEval_liftForm, blowUpEval_liftForm]
      rfl
    rw [hval, IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔫] at hU
    exact hU hm
  intro w hwW
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Ideal.mem_comap, ← sum_weightedHomogeneousComponent (w := blockWeight ι) w,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp _), map_sum]
  exact Ideal.sum_mem _ fun b _ =>
    key b _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (hWmh w hwW b)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultiHomogPrimeAvoid
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem MultiHomogPrimeAvoid.proof : MultiHomogPrimeAvoid.Statement.{u} := by
  intro R _ K _ _ ι S hfin hS
  obtain ⟨e, L, hL, he, hLS⟩ := exists_form_avoid_primes hfin.toFinset
    (fun W hW => hS W (hfin.mem_toFinset.mp hW)) (fun _ => 1)
  exact ⟨e, L, hL, fun k => he k, fun Q hQ => hLS Q (hfin.mem_toFinset.mpr hQ)⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GenericProjClosureDivisor

noncomputable section

namespace SegreFlagCutChart

theorem exists_pow_mul_mem_of_mem_sup_map {R S F : Type*} [CommRing R] [CommRing S] [FunLike F S R]
    [RingHomClass F S R] (f : F) (A I : Ideal R) (J : Ideal S) (v : R) (hI : I ≤ A)
    (hJ : ∀ q ∈ J, ∃ n : ℕ, v ^ n * f q ∈ A) : ∀ x ∈ I ⊔ J.map f, ∃ n : ℕ, v ^ n * x ∈ A := by
  let T : Ideal R :=
    { carrier := {x | ∃ n : ℕ, v ^ n * x ∈ A}
      add_mem' := by
        rintro a b ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : v ^ (m + n) * (a + b) = v ^ n * (v ^ m * a) + v ^ m * (v ^ n * b) := by ring
        rw [h]
        exact A.add_mem (A.mul_mem_left _ hm) (A.mul_mem_left _ hn)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : v ^ n * (c • x) = c * (v ^ n * x) := by rw [smul_eq_mul]; ring
        rw [h]
        exact A.mul_mem_left _ hn }
  have hle : I ⊔ J.map f ≤ T :=
    sup_le (fun x hx => ⟨0, by simpa using hI hx⟩) (Ideal.map_le_iff_le_comap.2 fun q hq => hJ q hq)
  exact fun x hx => hle hx

end SegreFlagCutChart


open SegreFlagCutChart in
theorem SegreFlagCutChart.proof (hCS : SegreFlagCutChartSection.Statement)
    (hPre : SegreFlagCutPreimage.Statement) : SegreFlagCutChart.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk W hW hWr hPW hϖW
  classical

  choose c hc using fun j : K => hWr (some (some j))
  have nz : ∀ j, y ⟨j, c j⟩ ≠ 0 := by
    intro j h0
    refine hc j (hPW (mem_of_homog (isWeightedHomogeneous_X O _ _) ?_))
    rw [aeval_X]
    show algebraMap Ω Φ (y ⟨j, c j⟩) = 0
    rw [h0, map_zero]
  have hcne : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => nz j
  have hvW : (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ∉ W := fun hm => by
    obtain ⟨j, -, hj⟩ := hW.prod_mem_iff.mp hm
    exact hc j hj
  obtain ⟨-, dl, dm, l, μ, m, hμ, hl, hμh, hdeg, hval, hsat⟩ :=
    hCS O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hcne
  have hμW : μ ∉ W := by
    rw [hμ]
    intro hm
    obtain ⟨j, -, hj⟩ := hW.prod_mem_iff.mp hm
    exact hc j (hW.mem_of_pow_mem _ hj)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  ·
    refine ⟨dl, dm, l, μ, _, hl, hμh, hdeg, hμW, hvW, hval, fun _ hlW => ?_, fun h => absurd h (lt_irrefl 0)⟩
    obtain ⟨j, hj⟩ := hWr none
    have hq : (X ⟨none, j⟩ : MvPolynomial (Σ o : Option K, bundleIdx (bundleIdx ι M) M' (secondFactorBlocks o)) O) ∈
        pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t 0) := by
      refine mem_of_homog (isWeightedHomogeneous_X O _ _) ?_
      rw [aeval_X]
      show flagClosurePt y w e φ φ' t 0 ⟨none, j⟩ = 0
      simp [flagClosurePt, pairProjCoord, flagCoord]
    obtain ⟨n, hn⟩ := hsat _ hq
    have h1 := sup_le hPW ((Ideal.span_singleton_le_iff_mem W).2 hlW) hn
    rw [rename_X] at h1
    rcases hW.mem_or_mem h1 with h2 | h2
    · exact hvW (hW.mem_of_pow_mem _ h2)
    · exact hj h2
  ·
    obtain ⟨u₀, hu₀W, hu₀⟩ := hPre O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
      Φ e t ht k hk W hW hWr hPW hϖW
    refine ⟨dl, dm, l, μ, u₀ * ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O), hl, hμh, hdeg,
      hμW, fun hm => ?_, hval, fun h => absurd h (Nat.pos_iff_ne_zero.mp hk0), fun _ q hq => ?_⟩
    · rcases hW.mem_or_mem hm with h | h
      · exact hu₀W h
      · exact hvW h
    · obtain ⟨n, hn⟩ := hu₀ q hq
      obtain ⟨m', hm'⟩ := exists_pow_mul_mem_of_mem_sup_map _ _ _ _ _ le_sup_left hsat _ hn
      refine ⟨n + m', ?_⟩
      have h : (u₀ * ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ (n + m') * q =
          u₀ ^ m' * (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ n *
            ((∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ m' * (u₀ ^ n * q)) := by
        ring
      rw [h]
      exact Ideal.mul_mem_left _ _ hm'

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

