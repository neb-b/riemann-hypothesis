module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem BlowUpHorizontalLift.full : BlowUpHorizontalLift.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime
  obtain ⟨hWp, hPW, hrelW⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have hWmin : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hxW : x ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  obtain ⟨j₀, hj₀⟩ := hloc W hWp hPW hrelW hϖW
  choose v w hvW hvw using hj₀

  have hu₀ : u j₀ ∉ P := by
    intro h0
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have h2 := P.add_mem (hvw j) (P.mul_mem_left (w j) h0)
      rwa [sub_add_cancel] at h2
    rcases hPp.mem_or_mem h1 with h2 | h2
    · exact hvW j (hPW h2)
    · exact hj h2

  set V : MRing ι O := ∏ j, v j with hV
  set a : J → MRing ι O := fun j => w j * ∏ i ∈ Finset.univ.erase j, v i with ha_def
  have hVW : V ∉ W := by
    intro h
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hvW j hj
  have ha : ∀ j, V * u j - u j₀ * a j ∈ P := by
    intro j
    have e : V * u j - u j₀ * a j = (∏ i ∈ Finset.univ.erase j, v i) * (v j * u j - w j * u j₀) := by
      simp only [hV, ha_def]
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]
      ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hVa : V - a j₀ ∈ P := by
    have h1 : (V - a j₀) * u j₀ ∈ P := by
      have h2 := ha j₀
      rwa [show V * u j₀ - u j₀ * a j₀ = (V - a j₀) * u j₀ by ring] at h2
    exact (hPp.mem_or_mem h1).resolve_right hu₀
  have haW : a j₀ ∉ W := fun h => hVW (by simpa using W.add_mem (hPW hVa) h)

  set Wt : Ideal (MRing (extIdx ι J) O) :=
    (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) W).comap
      (aeval (R := O) (chartSubst a)) with hWt
  have hWtp : Wt.IsPrime := Ideal.comap_isPrime _ _
  have hcomap : ∀ s, liftForm (J := J) s ∈ Wt ↔ s ∈ W := by
    intro s
    rw [hWt, Ideal.mem_comap, aeval_chartSubst_liftForm]
    constructor
    · intro h
      simpa using Ideal.mem_map_C_iff.mp h 0
    · intro h
      exact Ideal.mem_map_of_mem _ h
  have hBWt : blowUpOf P u ≤ Wt := fun F hF =>
    Ideal.map_mono hPW (aeval_chartSubst_mem_of_mem_blowUpOf hPp hu₀ ha hF)
  have hxWt : liftForm x ∈ Wt := (hcomap x).2 hxW
  have hrelWt : IsRelevant Wt := by
    rintro (_ | k)
    · refine ⟨j₀, fun h => haW ?_⟩
      rw [hWt, Ideal.mem_comap] at h
      simp only [aeval_X, chartSubst] at h
      simpa using Ideal.mem_map_C_iff.mp h 1
    · obtain ⟨i, hi⟩ := hrelW k
      refine ⟨i, fun h => hi ((hcomap _).1 ?_)⟩
      rw [liftForm_X]
      exact h

  have hmin : Wt ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    refine ⟨⟨hWtp, sup_le hBWt ((Ideal.span_singleton_le_iff_mem _).mpr hxWt)⟩, fun Q hQ hQWt => ?_⟩
    have hQp := hQ.1
    have hBQ : blowUpOf P u ≤ Q := le_sup_left.trans hQ.2
    have hxQ : liftForm x ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hle : Q.comap (liftForm (J := J)) ≤ W := fun s hs => (hcomap s).1 (hQWt hs)
    have hQ₀ : Q.comap (liftForm (J := J)) = W :=
      le_antisymm hle (hWmin.2 ⟨Ideal.comap_isPrime _ _,
        sup_le (fun p hp => hBQ (liftForm_mem_blowUpOf hp))
          ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩ hle)
    intro F hF
    refine mem_of_aeval_chartSubst_mem hQp hQ₀.ge j₀ (fun h => haW ?_) (fun j => hBQ ?_) hF
    · rw [← hQ₀]
      exact h
    · apply mem_blowUpOf_of_sub
      have e : u j * a j₀ - u j₀ * a j = (V * u j - u j₀ * a j) - u j * (V - a j₀) := by ring
      rw [e]
      exact P.sub_mem (ha j) (P.mul_mem_left _ hVa)
  refine ⟨Wt, ?_, fun h => hϖW ((hcomap _).1 (by rw [liftForm_C]; exact h)), ?_⟩
  ·
    unfold divCycle
    rw [dite_eq_left ⟨hmin, hrelWt⟩]
    have hne := length_localizedQuot_ne_top (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt hmin
    have hnz : multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt ≠ 0 := by
      unfold multAt
      rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
      intro hs
      obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
        Ideal.Quotient.eq_zero_iff_mem] at hr0
      exact hr (hmin.1.2 hr0)
    have htn : (multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt).toNat ≠ 0 :=
      fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
    exact_mod_cast htn
  · ext s
    rw [Ideal.mem_comap]
    exact hcomap s

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalMinimal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem BlowUpHorizontalMinimal.full : BlowUpHorizontalMinimal.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  obtain ⟨hWp, hBW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine ⟨⟨hW₀p, sup_le hPW₀ ((Ideal.span_singleton_le_iff_mem _).mpr hxW)⟩, fun P' hP' hP'W₀ => ?_⟩
  have := hP'.1
  have hxP' : x ∈ P' := hP'.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))

  let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P').comap
    (aeval (R := O) (chartSubst a))
  have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hBQ' : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ Q' := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono (le_sup_left.trans hP'.2)
        (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ hxP'
  have hQ'W : Q' ≤ W := fun G hG =>
    mem_of_aeval_chartSubst_mem hWp hP'W₀ j₀ ha₀ (fun j => hBW (hrelB j)) hG

  have hWQ' : W ≤ Q' := hmin.2 ⟨hQ'p, hBQ'⟩ hQ'W
  intro p hp
  have h5 : Polynomial.C p ∈ Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P' := by
    rw [← aeval_chartSubst_liftForm a p]
    exact hWQ' hp
  simpa using Ideal.mem_map_C_iff.mp h5 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalSat
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Saturation

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem exists_pow_mul_mem_of_aeval_chartSubst_mem {P : Ideal (MRing ι R)} {u a : J → MRing ι R}
    {W : Ideal (MRing ι R)} (j₀ : J)
    (hrel : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u)
    {F : MRing (extIdx ι J) R}
    (hF : aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) W) :
    ∃ n : ℕ, liftForm (a j₀ ^ n) * F ∈
      blowUpOf P u ⊔ Ideal.map (liftForm (J := J) : MRing ι R →ₐ[R] MRing (extIdx ι J) R) W := by
  set B' := blowUpOf P u ⊔ Ideal.map (liftForm (J := J) : MRing ι R →ₐ[R] MRing (extIdx ι J) R) W
  let π := Ideal.Quotient.mk B'
  let x₀ := π (liftForm (a j₀))
  let L := Localization.Away x₀
  let q : MRing (extIdx ι J) R →+* L := (algebraMap _ L).comp π
  let t : L := IsLocalization.Away.invSelf x₀
  have hinv : q (liftForm (a j₀)) * t = 1 := IsLocalization.Away.mul_invSelf x₀
  let ψ : Polynomial (MRing ι R) →+* L :=
    Polynomial.eval₂RingHom (q.comp (liftForm (J := J) : MRing ι R →ₐ[R] _).toRingHom) (q (newVar j₀) * t)
  have key : ψ.comp (aeval (R := R) (chartSubst a)).toRingHom = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ]
    · rintro ⟨_ | k, i⟩
      · change J at i
        have hm : π (newVar i * liftForm (a j₀) - newVar j₀ * liftForm (a i)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (hrel i))
        have h1 : q (newVar i * liftForm (a j₀) - newVar j₀ * liftForm (a i)) = 0 := by
          show algebraMap _ L (π _) = 0
          rw [hm, map_zero]
        rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
        simp only [ψ, chartSubst, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        change q (liftForm (a i)) * (q (newVar j₀) * t) = q (newVar i)
        linear_combination (-t) * h1 + q (newVar i) * hinv
      · simp [ψ, chartSubst, liftForm]
  have hle : Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) W ≤ RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simp only [ψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, q]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hp)), map_zero]
  have h2 := RingHom.mem_ker.mp (hle hF)
  have h3 := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3
  rw [h3] at h2
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers x₀) L (π F)).mp h2
  refine ⟨n, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_pow]
  exact hm

end Saturation

theorem BlowUpHorizontalSat.full : BlowUpHorizontalSat.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW F
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hWsupp : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hW (by rw [divCycle, dif_neg h])
  obtain ⟨hmin, hWrel⟩ := hWsupp
  have hWp : W.IsPrime := hmin.1.1
  have hBW : blowUpOf P u ≤ W := le_sup_left.trans hmin.1.2
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have := hW₀p
  let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) W₀).comap
    (aeval (R := O) (chartSubst a))
  have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hBQ' : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ Q' := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono hPW₀ (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ hxW
  have hQ'W : Q' ≤ W := fun G hG =>
    mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG
  have hWQ' : W ≤ Q' := hmin.2 ⟨hQ'p, hBQ'⟩ hQ'W
  constructor
  · intro hF
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_aeval_chartSubst_mem j₀ hrelB (hWQ' hF)
    exact ⟨a j₀ ^ m, fun h => ha₀ (hW₀p.mem_of_pow_mem _ h), hm⟩
  · rintro ⟨s, hs, hsF⟩
    have h1 : liftForm s * F ∈ W := sup_le hBW Ideal.map_comap_le hsF
    exact (hWp.mem_or_mem h1).resolve_left hs

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDvrConeDimTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace DvrConeDimTrdeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem proof : Statement := by
  intro O _ _ _ K _ _ ι _ P hP hPC
  classical
  let F := FractionRing O
  have hPp : P.IsPrime := hP.isPrime
  have hG : (genFib P).IsPrime := (GenericFibProps.full.{0} O K ι P hP hPC).1
  have hdim : ringKrullDim (MRing ι O ⧸ P) = ringKrullDim (MRing ι F ⧸ genFib P) + 1 :=
    le_antisymm (GenericDimGe.proof.{0} O K ι P hPp hPC) (GenericDimBound.full.{0} O K ι P hP hPC)

  have hB : ringKrullDim (MRing ι F ⧸ genFib P) =
      (Algebra.trdeg F (MRing ι F ⧸ genFib P)).toENat :=
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F

  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C : O →+* MRing ι O)
  have : IsLocalization M (MRing ι F) := MvPolynomial.isLocalization (nonZeroDivisors O) F
  have hdisj : Disjoint (M : Set (MRing ι O)) (P : Set (MRing ι O)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hPC] at this
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 this)
  have hcomap : (genFib P).comap (algebraMap (MRing ι O) (MRing ι F)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι F) hPp hdisj
  let φ : (MRing ι O ⧸ P) →+* (MRing ι F ⧸ genFib P) :=
    Ideal.quotientMap (genFib P) (algebraMap (MRing ι O) (MRing ι F)) hcomap.ge
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' hcomap.le
  let _ : Algebra (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) := φ.toAlgebra
  have : IsScalarTower O (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change _ = φ (Ideal.Quotient.mk P (C a))
      simp [φ, Ideal.quotientMap_mk]
      rfl
  have : FaithfulSMul (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : FaithfulSMul O (MRing ι O ⧸ P) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 ((injective_iff_map_eq_zero (algebraMap O (MRing ι O ⧸ P))).2 fun a ha => ?_)
    have h : (C a : MRing ι O) ∈ P :=
      Ideal.Quotient.eq_zero_iff_mem.1 (show Ideal.Quotient.mk P (C a) = 0 from ha)
    have : a ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hPC] at this
    exact (Submodule.mem_bot _).1 this
  have : FaithfulSMul O F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective O F)
  have : FaithfulSMul F (MRing ι F ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective F (MRing ι F ⧸ genFib P)).2 (algebraMap F _).injective
  have : Algebra.IsAlgebraic O F := IsLocalization.isAlgebraic F (nonZeroDivisors O)
  have : Algebra.IsAlgebraic (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) := by
    refine ⟨fun b => ?_⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective M g
    have hspec := IsLocalization.mk'_spec (MRing ι F) s m
    let y := algebraMap (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) (Ideal.Quotient.mk P (m : MRing ι O))
    have hy0 : y ≠ 0 := by
      refine (map_ne_zero_iff _ hφ).2 fun h => ?_
      exact Set.disjoint_left.1 hdisj m.2 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hy0) (isAlgebraic_algebraMap _) ?_
    have : y * Ideal.Quotient.mk (genFib P) (IsLocalization.mk' (MRing ι F) s m) =
        algebraMap (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) (Ideal.Quotient.mk P s) := by
      change φ _ * _ = φ _
      simp only [φ, Ideal.quotientMap_mk, ← map_mul]
      rw [mul_comm, hspec]
    rw [this]
    exact isAlgebraic_algebraMap _
  have h1 := trdeg_add_eq O F (A := MRing ι F ⧸ genFib P)
  have h2 := trdeg_add_eq O (MRing ι O ⧸ P) (A := MRing ι F ⧸ genFib P)
  rw [trdeg_eq_zero (R := O) (A := F), zero_add] at h1
  rw [trdeg_eq_zero (R := MRing ι O ⧸ P) (A := MRing ι F ⧸ genFib P), add_zero] at h2
  rw [hdim, hB, h1, ← h2]
  rfl

end DvrConeDimTrdeg

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

