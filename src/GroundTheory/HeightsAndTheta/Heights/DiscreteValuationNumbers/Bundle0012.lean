module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConservationOfNumberLE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      have h'' : m + 1 ≤ n := by exact_mod_cast h'
      exact_mod_cast (show m < n by omega)

private theorem special_dim_add_one_le {O : Type u} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} {ι : K → Type}
    (P : Ideal (MRing ι O)) [P.IsPrime] (hnt : P.comap (C : O →+* MRing ι O) = ⊥) :
    ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P) + 1 ≤
      ringKrullDim (MRing ι O ⧸ P) := by
  set φ : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφdef
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]

  set g : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.Quotient.mk (specialIdeal P)).comp φ with hgdef
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hgdef, ← RingHom.comap_ker, Ideal.mk_ker, specialIdeal, ← hφdef,
      Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot, hker]
  have e1 : MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) ≃+*
      MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)

  set r : MRing ι O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef
  have hspan : (Ideal.span {(C ϖ : MRing ι O)}).map (Ideal.Quotient.mk P) = Ideal.span {r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have e2 : (MRing ι O ⧸ P) ⧸ Ideal.span {r} ≃+* MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) :=
    (Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P _)

  have hr0 : r ≠ 0 := by
    intro h0
    rw [hrdef, Ideal.Quotient.eq_zero_iff_mem] at h0
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h0
    rw [hnt, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have hr : r ∈ nonZeroDivisors (MRing ι O ⧸ P) := mem_nonZeroDivisors_of_ne_zero hr0
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  rwa [ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1] at hle

theorem ConservationOfNumberLE.proof (h1 : IntNumAssoc.Statement.{u})
    (h2 : SpecialCycleEval.Statement.{u}) (h3 : SpecialPieceRank.Statement.{u})
    (h4 : GenericPieceRank.Statement.{u}) (h5 : SpecialIdealMultiHomog.Statement.{u}) :
    ConservationOfNumberLE.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP hnt hdim a

  have hPprime : P.IsPrime := hP.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hnt, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have htors : ∀ x, C ϖ * x ∈ P → x ∈ P := fun x hx =>
    (hPprime.mem_or_mem hx).resolve_left hϖP
  have hhom : IsMultiHomogIdeal P := hP.multiHomog

  have hhilb : hilbFn (genFib P) = hilbFn (specialIdeal P) := by
    funext m
    unfold hilbFn
    split_ifs
    · rw [h4 O K ι P hhom, h3 O ϖ hϖ K ι P hhom htors]
    · rfl
  have hg : gNum P a = intNum (IsLocalRing.ResidueField O) (specialIdeal P) a := by
    unfold gNum intNum
    rw [hhilb]

  have hsp : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P) <
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    lt_of_add_one_le_natCast ((special_dim_add_one_le hϖ P hnt).trans hdim)
  rw [hg, h1 (IsLocalRing.ResidueField O) K ι d (specialIdeal P) (h5 O K ι P hhom) hsp a]
  exact h2 O ϖ hϖ K ι P (fun V => intNum (IsLocalRing.ResidueField O) V a)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByEffectiveDivisor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem IsVerticalDivisor.uniformiser_pow_mul {K : Type*} [DecidableEq K] {ι : K → Type*}
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {H : Ideal (MRing ι O)}
    [hH : H.IsPrime] {ϖ : O} (hϖ : (C ϖ : MRing ι O) ∉ H) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor H ϖ b f g) (n : ℕ) :
    IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by
  obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
  refine IsVerticalDivisor.of_unit_off_special ⟨bf, bg, ?_, hg, hb⟩ ?_ hD.den_not_mem ?_
  · have h0 : IsMultiHomog (C ϖ ^ n : MRing ι O) 0 := by
      rw [← map_pow]
      exact isWeightedHomogeneous_C _ _
    have := h0.mul hf
    rwa [zero_add] at this
  · exact hH.mul_notMem (fun h => hϖ (hH.mem_of_pow_mem n h)) hD.num_not_mem
  · intro W hW hHW hrel hϖW
    obtain ⟨u, v, hu, hv, huv⟩ := hD.unit_off_special W hW hHW hrel hϖW
    refine ⟨u, C ϖ ^ n * v, hu, hW.mul_notMem (fun h => hϖW (hW.mem_of_pow_mem n h)) hv, ?_⟩
    have e : u * (C ϖ ^ n * f) - C ϖ ^ n * v * g = C ϖ ^ n * (u * f - v * g) := by ring
    rw [e]
    exact H.mul_mem_left _ huv

theorem CutByEffectiveDivisor.proof (h1 : EffectiveCase.Statement.{u})
    (h2 : UniformiserCase.Statement.{u}) (h3 : ShiftByUniformiser.Statement.{u})
    (h4 : EffectiveShift.Statement.{u}) : CutByEffectiveDivisor.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH L
  obtain ⟨n, hEff⟩ := h4 O ϖ hϖ K ι P (d + 1) hP b f g hD
  have hH' : ∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by
    intro H hsH hϖH
    have := (le_and_isRelevant_of_divCycle_ne_zero hsH).1
    exact (hH H hsH hϖH).uniformiser_pow_mul hϖH n
  have e1 := h1 O ϖ hϖ K ι P d hP b (C ϖ ^ n * f) g hEff c s hs hsP hH' L
  have e2 := h2 O ϖ hϖ K ι P d hP c s hs hsP L
  exact h3 O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH L n e1 e2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DivCycleFiniteSupport.proof : DivCycleFiniteSupport.Statement.{u} := by
  intro R _ _ K _ ι _ P f
  apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f}))
  intro W hW
  by_contra hmin
  apply hW
  unfold divCycle
  rw [dite_eq_right]
  exact fun h => hmin h.1

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section General

variable {A : Type*} [CommRing A]

theorem localizedQuot_subsingleton_of_not_le (Q W : Ideal A) [W.IsPrime] (h : ¬ Q ≤ W) :
    Subsingleton (LocalizedModule W.primeCompl (A ⧸ Q)) := by
  obtain ⟨q, hqQ, hqW⟩ := Set.not_subset.mp h
  rw [LocalizedModule.subsingleton_iff]
  intro m
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  refine ⟨q, hqW, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Q.mul_mem_right a hqQ

theorem length_localizedQuot_sup_span_mul (P W : Ideal A) [P.IsPrime] [W.IsPrime] {x : A} (y : A)
    (hx : x ∉ P) :
    Module.length (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {x * y}))) =
      Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {y}))) +
        Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {x}))) := by
  have hle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {x} :=
    sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))) P
  let g₁ : (A ⧸ (P ⊔ Ideal.span {y})) →ₗ[A] A ⧸ (P ⊔ Ideal.span {x * y}) :=
    Submodule.mapQ _ _ (LinearMap.mulLeft A x) (fun a ha => by
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      show x * (p + c * y) ∈ P ⊔ Ideal.span {x * y}
      have e : x * (p + c * y) = x * p + c * (x * y) := by ring
      rw [e]
      exact Submodule.add_mem_sup (P.mul_mem_left _ hp) (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))
  let g₂ : (A ⧸ (P ⊔ Ideal.span {x * y})) →ₗ[A] A ⧸ (P ⊔ Ideal.span {x}) :=
    Submodule.mapQ _ _ LinearMap.id (fun a ha => hle ha)
  have hinj : Function.Injective g₁ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    rw [LinearMap.mem_ker] at hz
    simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply,
      Submodule.Quotient.mk_eq_zero] at hz
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hm : x * (a - c * y) ∈ P := by
      have e : x * (a - c * y) = p := by linear_combination hpr.symm
      rw [e]; exact hp
    have ha : a - c * y ∈ P := (‹P.IsPrime›.mem_or_mem hm).resolve_left hx
    have e : a = (a - c * y) + c * y := by ring
    rw [e]
    exact Submodule.add_mem_sup ha (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)
  have hsurj : Function.Surjective g₂ := by
    intro z
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have hex : Function.Exact g₁ g₂ := by
    intro z
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    simp only [g₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro ha
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
      rw [Submodule.Quotient.eq]
      have e : x * c - (p + c * x) = -p := by ring
      rw [e]
      exact Submodule.mem_sup_left (P.neg_mem hp)
    · rintro ⟨z, hz⟩
      induction z using Submodule.Quotient.induction_on with | _ c => ?_
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply] at hz
      rw [Submodule.Quotient.eq] at hz
      have e : a = -(x * c - a) + c * x := by ring
      rw [e]
      exact Submodule.add_mem _ (Submodule.neg_mem _ (hle hz))
        (Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))
  exact Module.length_eq_add_of_exact (R := Localization.AtPrime W)
    (LocalizedModule.map W.primeCompl g₁) (LocalizedModule.map W.primeCompl g₂)
    (LocalizedModule.map_injective _ _ hinj) (LocalizedModule.map_surjective _ _ hsurj)
    (LocalizedModule.map_exact _ _ _ hex)

theorem length_localizedQuot_ne_top [IsNoetherianRing A] (J W : Ideal A) [W.IsPrime]
    (hW : W ∈ J.minimalPrimes) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) ≠ ⊤ := by
  have : IsNoetherianRing (Localization.AtPrime W) :=
    IsLocalization.isNoetherianRing W.primeCompl _ inferInstance
  have hI : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      (J.map (algebraMap A (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W) J,
      Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hW
  have : IsArtinianRing (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
  have : IsArtinian (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    isArtinian_of_surjective_algebraMap
      (Ideal.Quotient.mk_surjective (I := J.map (algebraMap A (Localization.AtPrime W))))
  have : IsNoetherian (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    isNoetherian_quotient _
  have := IsLocalization.linearMap_compatibleSMul W.primeCompl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    (J.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)))
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J))).restrictScalars (Localization.AtPrime W)
  rw [← e.length_eq, Ideal.localized'_eq_map]
  exact Module.length_ne_top

theorem mem_minimalPrimes_sup_span_mul [IsNoetherianRing A] {P W : Ideal A} [P.IsPrime] {x y : A}
    (hy : y ∉ P) (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) :
    W ∈ (P ⊔ Ideal.span {x * y}).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hxW : x ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr (W.mul_mem_right y hxW))⟩, ?_⟩
  rintro Q ⟨hQp, hQ⟩ hQW
  have hPQ : P ≤ Q := le_sup_left.trans hQ
  rcases hQp.mem_or_mem (hQ (Ideal.mem_sup_right (Ideal.subset_span rfl))) with hxQ | hyQ
  · exact hW.2 ⟨hQp, sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩ hQW
  by_contra hWQ
  have hlt : Q < W := lt_of_le_of_ne hQW (fun h => hWQ h.ge)
  have hPQlt : P < Q := lt_of_le_of_ne hPQ (fun h => hy (h ▸ hyQ))
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have hQ' : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker.le.trans hPQ)
  have hW' : (W.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker.le.trans hPW)
  have h0 : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have hcQ : (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      hker, sup_eq_left.mpr hPQ]
  have hcW : (W.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = W := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      hker, sup_eq_left.mpr hPW]
  have hcP : (⊥ : Ideal (A ⧸ P)).comap (Ideal.Quotient.mk P) = P := by
    rw [← RingHom.ker_eq_comap_bot, hker]
  have h1 : (⊥ : Ideal (A ⧸ P)) < Q.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne bot_le (fun h => hPQlt.ne
      (hcP.symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk P)) h).trans hcQ)))
  have h2 : Q.map (Ideal.Quotient.mk P) < W.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne (Ideal.map_mono hQW) (fun h => hlt.ne
      (hcQ.symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk P)) h).trans hcW)))
  have hb := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have hc := Ideal.height_add_one_le_of_lt_of_isPrime h2
  have hk := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have h2le : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal (A ⧸ P)).height + 1 + 1 := by gcongr; positivity
      _ ≤ (Q.map (Ideal.Quotient.mk P)).height + 1 := by gcongr
      _ ≤ 1 := hc.trans hk
  exact absurd h2le (by norm_num)

end General

section Forms

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem divCycle_eq_toNat_multAt {P : Ideal (MRing ι R)} (f g : MRing ι R)
    {W : Ideal (MRing ι R)} [W.IsPrime] (hW : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes)
    (hrel : IsRelevant W) (hle : P ⊔ Ideal.span {g} ≤ P ⊔ Ideal.span {f}) :
    divCycle P f W = ((multAt (P ⊔ Ideal.span {f}) W).toNat : ℤ) := by
  unfold divCycle
  by_cases hfW : P ⊔ Ideal.span {f} ≤ W
  · have hm : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes :=
      ⟨⟨hW.1.1, hfW⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, hle.trans hQ.2⟩ hQW⟩
    rw [dite_eq_left ⟨hm, hrel⟩]
  · rw [dite_eq_right (fun h => hfW h.1.1.2)]
    unfold multAt
    rw [Module.length_eq_zero_iff.mpr (localizedQuot_subsingleton_of_not_le _ W hfW)]
    rfl

end Forms

theorem DivCycleMul.proof : DivCycleMul.Statement := by
  intro R _ _ K _ ι _ P x y hP hx hy
  funext W
  have hxy : x * y ∉ P := fun h => (hP.mem_or_mem h).elim hx hy
  by_cases hrel : IsRelevant W
  swap
  · simp only [Pi.add_apply]
    unfold divCycle
    rw [dite_eq_right (fun h => hrel h.2), dite_eq_right (fun h => hrel h.2), dite_eq_right (fun h => hrel h.2),
      add_zero]
  by_cases hm : W ∈ (P ⊔ Ideal.span {x * y}).minimalPrimes
  · have hW : W.IsPrime := hm.1.1
    have hxle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {x} :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))) P
    have hyle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {y} :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_left _ x (Ideal.mem_span_singleton_self y))) P
    simp only [Pi.add_apply]
    rw [divCycle_eq_toNat_multAt (x * y) (x * y) hm hrel le_rfl,
      divCycle_eq_toNat_multAt x (x * y) hm hrel hxle,
      divCycle_eq_toNat_multAt y (x * y) hm hrel hyle]
    have htop := length_localizedQuot_ne_top _ W hm
    have hadd := length_localizedQuot_sup_span_mul P W y hx
    unfold multAt
    rw [hadd] at htop ⊢
    rw [ENat.toNat_add (WithTop.add_ne_top.mp htop).1 (WithTop.add_ne_top.mp htop).2]
    push_cast
    ring
  · simp only [Pi.add_apply]
    unfold divCycle
    have hnx : ¬ W ∈ (P ⊔ Ideal.span {x}).minimalPrimes :=
      fun h => hm (mem_minimalPrimes_sup_span_mul hy h)
    have hny : ¬ W ∈ (P ⊔ Ideal.span {y}).minimalPrimes :=
      fun h => hm (mul_comm y x ▸ mem_minimalPrimes_sup_span_mul hx h)
    rw [dite_eq_right (fun h => hm h.1), dite_eq_right (fun h => hnx h.1), dite_eq_right (fun h => hny h.1), add_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEffectiveShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem EffectiveShift.proof : EffectiveShift.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P e hP b f g hD
  classical
  have hPr : P.IsPrime := hP.multiProj.isPrime
  have hCP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  let J : Ideal (MRing ι O) :=
    { carrier := {u | ∃ v, u * f - v * g ∈ P}
      add_mem' := by
        rintro a c ⟨v, hv⟩ ⟨w, hw⟩
        exact ⟨v + w, by convert P.add_mem hv hw using 1; ring⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨v, hv⟩
        exact ⟨c * v, by convert P.mul_mem_left c hv using 1; simp only [smul_eq_mul]; ring⟩ }
  have hJ : ∀ u, u ∈ J ↔ ∃ v, u * f - v * g ∈ P := fun u => Iff.rfl
  have hPJ : P ≤ J := fun p hp => (hJ p).2 ⟨0, by simpa using P.mul_mem_right f hp⟩

  let 𝔞 : Ideal (MRing ι O) :=
    ∏ k : K, Ideal.span (Set.range fun i : ι k => (X ⟨k, i⟩ : MRing ι O))
  let I : Ideal (MRing ι O) := Ideal.span {(C ϖ : MRing ι O)} * 𝔞
  have hIJ : I ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun W hW => ?_
    obtain ⟨hJW, hWp⟩ := hW
    by_cases hϖW : (C ϖ : MRing ι O) ∈ W
    · exact Ideal.mul_le_left.trans ((Ideal.span_singleton_le_iff_mem W).2 hϖW)
    · have hrel : ¬ IsRelevant W := by
        intro hrel
        obtain ⟨u, v, hu, -, huv⟩ := hD.unit_off_special W hWp (hPJ.trans hJW) hrel hϖW
        exact hu (hJW ((hJ u).2 ⟨v, huv⟩))
      simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
      obtain ⟨k, hk⟩ := hrel
      refine Ideal.mul_le_right.trans
        (Ideal.prod_le_inf.trans ((Finset.inf_le (Finset.mem_univ k)).trans ?_))
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hk i
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ (IsNoetherian.noetherian I)
  have hCN : (C ϖ : MRing ι O) ^ N ∉ P := fun h => hCP (hPr.mem_of_pow_mem N h)
  refine ⟨N, ?_, ?_⟩
  · obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine IsVerticalDivisor.of_unit_off_special ⟨bf, bg, ?_, hg, hb⟩ ?_ hD.den_not_mem ?_
    · have h := (isWeightedHomogeneous_C (blockWeight ι) (ϖ ^ N)).mul hf
      rw [zero_add, map_pow] at h
      exact h
    · exact fun h => (hPr.mem_or_mem h).elim hCN hD.num_not_mem
    · intro W hW hPW hrel hϖW
      obtain ⟨u, v, hu, hv, huv⟩ := hD.unit_off_special W hW hPW hrel hϖW
      refine ⟨u, C ϖ ^ N * v, hu, ?_, ?_⟩
      · exact fun h => (hW.mem_or_mem h).elim (fun h' => hϖW (hW.mem_of_pow_mem N h')) hv
      · convert P.mul_mem_left (C ϖ ^ N) huv using 1; ring
  · intro W hW hPW hrel
    choose i hi using hrel
    have hz : (∏ k, (X ⟨k, i k⟩ : MRing ι O)) ∉ W := by
      rw [hW.prod_mem_iff]
      rintro ⟨k, -, hk⟩
      exact hi k hk
    have hz𝔞 : (∏ k, (X ⟨k, i k⟩ : MRing ι O)) ∈ 𝔞 :=
      Ideal.prod_mem_prod fun k _ => Ideal.subset_span ⟨i k, rfl⟩
    have hmem : (C ϖ * ∏ k, (X ⟨k, i k⟩ : MRing ι O)) ^ N ∈ J :=
      hN (Ideal.pow_mem_pow (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz𝔞) N)
    obtain ⟨v, hv⟩ := (hJ _).1 hmem
    refine ⟨(∏ k, (X ⟨k, i k⟩ : MRing ι O)) ^ N, v, fun h => hz (hW.mem_of_pow_mem N h), ?_⟩
    convert hv using 1
    ring

end GroundTheory.Heights₂.Heights.NumbersDVR
end

