module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarUnit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem ConeVarUnit.proof (hDZ : DegZeroLocQuot.Statement.{u})
    (hNum : ConeVarNumerator.Statement.{u}) : ConeVarUnit.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  intro p e he
  obtain ⟨b, g, h, hg, hgW, hh, hcoeff, himg⟩ := hNum F K ι P hP W hW hPW v hv p
  have hne : ∀ x : MRing ι F, x ∉ W →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P x) ≠ 0 :=
    fun x hx h0 => hx (hPW ((Ideal.Quotient.eq_zero_iff_mem).mp
      ((IsFractionRing.to_map_eq_zero_iff).mp h0)))

  have heW : h e ∉ W := by
    intro heW
    obtain ⟨y, hy⟩ := he.exists_right_inv
    obtain ⟨b', f', g', -, -, -, hg'W, hy'⟩ :=
      hDZ F K ι P {W} (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hW.isPrime) y y.2
    have h1 : ((p.coeff e : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) * y = 1 := by
      rw [← Subalgebra.coe_mul, hy, Subalgebra.coe_one]
    rw [hcoeff e, hy', div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hne g hgW)
      (hne g' (hg'W W rfl))), ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h1
    have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ h1)
    have h3 : g * g' ∈ W := by
      have := W.sub_mem (W.mul_mem_right f' heW) (hPW h2)
      rwa [sub_sub_cancel] at this
    rcases hW.isPrime.mem_or_mem h3 with h4 | h4
    exacts [hgW h4, hg'W W rfl h4]

  have hu : ∀ d : K →₀ ℕ, IsMultiHomog (∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k) (⇑d) := by
    intro d
    have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, v k⟩) (fun k _ => (isWeightedHomogeneous_X F _ _).pow _)
    have hdeg : (∑ k, d k • blockWeight ι ⟨k, v k⟩) = ⇑d := by
      ext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hdeg] at this
    exact this
  have huW : ∀ d : K →₀ ℕ, (∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k) ∉ W := by
    intro d hd
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp hd
    exact hv k (hW.isPrime.mem_of_pow_mem _ hk)

  set N := ∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k with hNdef
  have hcomp : weightedHomogeneousComponent (blockWeight ι) (b + ⇑e) N =
      h e * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ e k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hNdef, map_sum, Finset.sum_eq_single e]
    · exact ((hh e).mul (hu e)).weightedHomogeneousComponent_same
    · intro d _ hde
      refine weightedHomogeneousComponent_eq_zero' _ _ fun c hc hw => hde ?_
      rw [((hh d).mul (hu d)) (mem_support_iff.mp hc)] at hw
      exact DFunLike.coe_injective (add_left_cancel hw)
    · intro hes
      exact absurd (notMem_support_iff.mp hes) he.ne_zero
  have hNW : N ∉ W := fun hN => by
    have := hW.multiHomog N hN (b + ⇑e)
    rw [hcomp] at this
    rcases hW.isPrime.mem_or_mem this with h4 | h4
    exacts [heW h4, huW e h4]

  have hunit : ∀ x : MRing ι F, x ∉ W →
      IsUnit (algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P x)) :=
    fun x hx => IsLocalization.map_units (coneLocal P W hPW)
      (⟨_, Submonoid.mem_map_of_mem _ hx⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  have heq : coneVarMap P W hPW v p *
      algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P N) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, himg,
      div_mul_cancel₀ _ (hne g hgW)]
  exact isUnit_of_mul_isUnit_left (heq ▸ hunit N hNW)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]


omit [DecidableEq K] in
theorem finiteType_quotient_mRing (I : Ideal (MRing ι F)) : Algebra.FiniteType F (MRing ι F ⧸ I) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ_surjective F I)


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem chartMonomial_not_mem (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) (b : K → ℕ) : chartMonomial u b ∉ Q := by
  unfold chartMonomial
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hu k (Ideal.IsPrime.mem_of_pow_mem ‹_› _ hk)

theorem chart_ringKrullDim_add_card (h : MChartTrdeg.Statement.{u}) (Q : Ideal (MRing ι F)) [Q.IsPrime]
    (hQ : IsMultiHomogIdeal Q) (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) :
    ringKrullDim (MRing ι F ⧸ chartIdeal Q u) + Fintype.card K = ringKrullDim (MRing ι F ⧸ Q) := by
  have := finiteType_quotient_mRing (F := F) (chartIdeal Q u)
  have := finiteType_quotient_mRing (F := F) Q
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F,
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ Q), ← h F K ι Q hQ u hu,
    map_add, map_natCast]
  norm_cast

end

theorem DegZeroLocDim.proof (h₁ : MChartHomog.Statement.{u}) (h₂ : MChartTrdeg.Statement.{u})
    (h₃ : MChartLocDim.Statement.{u}) : DegZeroLocDim.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  choose u hu using hW.relevant
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k hk => hu k (hPW hk)
  have hle : chartIdeal P u ≤ chartIdeal W u := by
    intro p hp
    obtain ⟨b, h, -, hh⟩ := h₁ F K ι u p
    simp only [chartIdeal, RingHom.mem_ker] at hp ⊢
    rw [hh P huP, div_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff,
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.Quotient.eq_zero_iff_mem] at hp
    have hW' : h ∈ W := by
      rcases hp with hp | hp
      · exact hPW hp
      · exact absurd hp (chartMonomial_not_mem P u huP b)
    rw [hh W hu, IsFractionRing.to_map_eq_zero_iff.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hW'), zero_div]
  have : ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)
  have := finiteType_quotient_mRing (F := F) (chartIdeal P u)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F)
    ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u)))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hform
  show ringKrullDim (degZeroLoc P {W}) + ringKrullDim (MRing ι F ⧸ W) = ringKrullDim (MRing ι F ⧸ P)
  rw [h₃ F K ι P W hPW u hu, ← chart_ringKrullDim_add_card h₂ W hW.multiHomog u hu,
    ← chart_ringKrullDim_add_card h₂ P hP.multiHomog u huP, ← hform, add_assoc]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocalize
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocLocalize.proof : DegZeroLocLocalize.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro W hW y hy
  have hWp := h𝒲P W hW
  have : W.IsPrime := hWp.1.isPrime
  obtain ⟨c, f, g, hf, hg, hgP, hgW, rfl⟩ :=
    DegZeroLocQuot.proof F K ι P {W} (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact this)
      y hy
  have hgW' : g ∉ W := hgW W rfl
  obtain ⟨e, h, hh, hce, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W' hW' => by
      rcases Finset.mem_insert.mp hW' with rfl | hW'
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have h' := (h𝒲P W' (h𝒲.mem_toFinset.mp hW')).1
        exact ⟨h'.isPrime, h'.multiHomog, h'.relevant⟩) c
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W' ∈ 𝒲, h ∉ W' := fun W' hW' =>
    hhS W' (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW'))
  obtain ⟨m, hm, hmW⟩ := exists_form_not_mem_of_isRelevant (H := W) hWp.1.relevant (e - c)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hgm : IsMultiHomog (g * m) e := by
    have := IsWeightedHomogeneous.mul hg hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hgmW : g * m ∉ W := fun h' => (this.mem_or_mem h').elim hgW' hmW
  have hgmP : g * m ∉ P := fun h' => hgmW (hWp.2 h')
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, _, div_mem_degZeroLoc P 𝒲 hgm hh hhP hh𝒲,
    ⟨_, div_mem_degZeroLoc P {W} hh hgm hgmP (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hgmW),
      ?_⟩, ?_⟩
  · rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hq0 _ hhP) (hq0 _ hgmP))]
  · have h1 := hq0 _ hgP
    have h2 := hq0 _ hhP
    simp only [map_mul]
    field_simp

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocSeparate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocSeparate.proof : DegZeroLocSeparate.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro W₁ hW₁ W₂ hW₂ hle
  obtain ⟨hW₁p, hPW₁⟩ := h𝒲P W₁ hW₁
  obtain ⟨hW₂p, hPW₂⟩ := h𝒲P W₂ hW₂
  have : W₂.IsPrime := hW₂p.isPrime

  obtain ⟨f, c, hf, hfW₁, hfW₂⟩ := exists_form_mem_not_mem hW₁p.multiHomog hle

  obtain ⟨e, h, hh, hce, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W hW => by
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have hW' := (h𝒲P W (h𝒲.mem_toFinset.mp hW)).1
        exact ⟨hW'.isPrime, hW'.multiHomog, hW'.relevant⟩) c
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W ∈ 𝒲, h ∉ W := fun W hW =>
    hhS W (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW))

  obtain ⟨m, hm, hmW₂⟩ := exists_form_not_mem_of_isRelevant (H := W₂) hW₂p.relevant (e - c)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hfmW₂ : f * m ∉ W₂ := fun h' => (hW₂p.isPrime.mem_or_mem h').elim hfW₂ hmW₂
  have hfmP : f * m ∉ P := fun h' => hfmW₂ (hPW₂ h')
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, ?_, _,
    div_mem_degZeroLoc P {W₂} hh hfm hfmP
      (fun W hW => by rw [Set.mem_singleton_iff.mp hW]; exact hfmW₂), ?_⟩
  ·
    rintro ⟨y, hy, hxy⟩
    obtain ⟨b', f', g', -, -, hg'P, hg'W, hy'⟩ := DegZeroLocQuot.proof F K ι P {W₁}
      (fun W hW => by rw [Set.mem_singleton_iff.mp hW]; exact hW₁p.isPrime) y hy
    rw [hy', div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hq0 h hhP) (hq0 g' hg'P)),
      ← map_mul, ← map_mul, ← map_mul, ← map_mul] at hxy
    have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ hxy)
    have h3 : h * g' ∈ W₁ := by
      have := W₁.sub_mem (W₁.mul_mem_right f' (W₁.mul_mem_right m hfW₁)) (hPW₁ h2)
      rwa [sub_sub_cancel] at this
    rcases hW₁p.isPrime.mem_or_mem h3 with h4 | h4
    exacts [hh𝒲 W₁ hW₁ h4, hg'W W₁ (Set.mem_singleton W₁) h4]
  ·
    rw [div_mul_div_comm, mul_comm (algebraMap _ _ (Ideal.Quotient.mk P (f * m))),
      div_self (mul_ne_zero (hq0 h hhP) (hq0 _ hfmP))]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocUnits
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocUnits.proof : DegZeroLocUnits.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲ne h𝒲
  have := hP.isPrime
  have hne : ∀ g : MRing ι F, g ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  intro x hx
  constructor
  · rintro ⟨y, hy, hxy⟩ W hW
    exact ⟨y, degZeroLoc_anti P (Set.singleton_subset_iff.mpr hW) hy, hxy⟩
  · intro h
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hx'⟩ :=
      DegZeroLocQuot.proof F K ι P 𝒲 (fun W hW => (h𝒲 W hW).1.isPrime) x hx
    by_cases hfW : ∃ W ∈ 𝒲, f ∈ W
    ·
      exfalso
      obtain ⟨W, hW, hfW⟩ := hfW
      have hWp : W.IsPrime := (h𝒲 W hW).1.isPrime
      obtain ⟨y, hy, hxy⟩ := h W hW
      obtain ⟨b', f', g', -, -, hg'P, hg'W, hy'⟩ := DegZeroLocQuot.proof F K ι P {W}
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hWp) y hy
      rw [hx', hy', div_mul_div_comm,
        div_eq_one_iff_eq (mul_ne_zero (hne g hgP) (hne g' hg'P)), ← map_mul, ← map_mul,
        ← map_mul, ← map_mul] at hxy
      have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ hxy)
      have h3 : g * g' ∈ W := by
        have := W.sub_mem (W.mul_mem_right f' hfW) ((h𝒲 W hW).2 h2)
        rwa [sub_sub_cancel] at this
      rcases hWp.mem_or_mem h3 with h4 | h4
      exacts [hgW W hW h4, hg'W W (Set.mem_singleton W) h4]
    ·
      push Not at hfW
      obtain ⟨W₀, hW₀⟩ := h𝒲ne
      have hfP : f ∉ P := fun h' => hfW W₀ hW₀ ((h𝒲 W₀ hW₀).2 h')
      refine ⟨_, div_mem_degZeroLoc P 𝒲 hg hf hfP hfW, ?_⟩
      rw [hx', div_mul_div_comm, mul_comm (algebraMap _ _ _),
        div_self (mul_ne_zero (hne g hgP) (hne f hfP))]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreNonempty
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem FibreNonempty.proof (h1 : SemilocalFiniteRank.Statement.{u})
    (h2 : DegZeroLocalRing.Statement.{u}) : FibreNonempty.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hn hc W hW hWn hle
  have := hP'.isPrime
  by_contra hem
  rw [Set.not_nonempty_iff_eq_empty] at hem
  obtain ⟨hfin, -, -⟩ := h1 F K K' j ι' P' hP' n hn hc W hW hWn hle
  have := hfin
  have hnone : ∀ W' ∈ fibrePrimes j P' W, False := fun W' hW' => by
    rw [hem] at hW'
    exact hW'

  have hB : IsField (degZeroLoc P' (fibrePrimes j P' W)) := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro x hx
    obtain ⟨b, f, g, hf, hg, hgP, -, hxfg⟩ := DegZeroLocQuot.proof F K' ι' P' (fibrePrimes j P' W)
      (fun W' hW' => (hnone W' hW').elim) x.1 x.2
    have hfP : f ∉ P' := by
      intro hfP
      apply hx
      apply Subtype.ext
      rw [hxfg, Ideal.Quotient.eq_zero_iff_mem.mpr hfP, map_zero, zero_div]
      rfl
    refine ⟨⟨_, div_mem_degZeroLoc P' (fibrePrimes j P' W) hg hf hfP
      (fun W' hW' => (hnone W' hW').elim)⟩, ?_⟩
    have hne : ∀ a : MRing ι' F, a ∉ P' →
        algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' a) ≠ 0 :=
      fun a ha => by
        rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
        exact ha
    apply Subtype.ext
    change x.1 * _ = 1
    rw [hxfg, div_mul_div_comm, mul_comm (algebraMap _ _ (Ideal.Quotient.mk P' f))]
    exact div_self (mul_ne_zero (hne g hgP) (hne f hfP))

  have hinj : Function.Injective (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W))) := by
    intro x y hxy
    have := congrArg (fun z : degZeroLoc P' (fibrePrimes j P' W) =>
      (z : FractionRing (MRing ι' F ⧸ P'))) hxy
    simp only [degZeroLoc.algebraMap_contract_coe] at this
    exact Subtype.ext ((contractFracMap j P').toRingHom.injective this)
  have : Algebra.IsIntegral (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W)) := Algebra.IsIntegral.of_finite _ _
  have hA := isField_of_isIntegral_of_isField hinj hB
  have hdim := (h2 F K (fun k => ι' (j k)) (contractPrime j P')
    (isMultiProjPrime_contractPrime j ι' hP') W hW hle).2 n hc hWn
  rw [ringKrullDim_eq_zero_of_isField hA] at hdim
  exact zero_ne_one hdim

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

