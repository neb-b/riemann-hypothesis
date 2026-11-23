module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ResidualComparison.proof (hpieces : BlowUpDecomposition.Statement.{u})
    (hdisj : ResidualDisjoint.Statement.{u}) (hcontr : ResidualContraction.Statement.{u}) :
    ResidualComparison.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  obtain ⟨hP', -, hsP', -, hres, hexc, -, -⟩ :=
    hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  have hY₀G' := hdisj O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  have hcmp := hcontr O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  set G := G'.comap (liftForm (J := BlowUpIdx ι) (ι := ι) (R := O)) with hGdef
  have hP'prime : P'.IsPrime := hP'.multiProj.isPrime
  have hPprime : P.IsPrime := hP.multiProj.isPrime
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hmul₀ := DivCycleMul.proof O K ι P
  have nm : ∀ x y, x ∉ P' → y ∉ P' → x * y ∉ P' := fun x y hx hy h =>
    (hP'prime.mem_or_mem h).elim hx hy
  have hzero : ∀ x, x ∉ G' → divCycle P' x G' = 0 := fun x hx => by
    by_contra h; exact hx (form_mem_of_divCycle_ne_zero h)

  have hG'supp : G' ∈ (P' ⊔ Ideal.span {liftForm s}).minimalPrimes ∧ IsRelevant G' := by
    by_contra h
    unfold divCycle at hsG'
    rw [dite_eq_right h] at hsG'
    exact lt_irrefl _ hsG'
  have hG'prime : G'.IsPrime := hG'supp.1.1.1
  have hP'G' : P' ≤ G' := le_sup_left.trans hG'supp.1.1.2
  have hlift : ∀ p ∈ P, liftForm (J := BlowUpIdx ι) p ∈ P' := fun p hp => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm,
      Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have hGprime : G.IsPrime := Ideal.comap_isPrime _ _
  have hPG : P ≤ G := fun p hp => hP'G' (hlift p hp)
  have hGrel : IsRelevant G := fun k => by
    obtain ⟨i, hi⟩ := hG'supp.2 (some k)
    exact ⟨i, fun h => hi (by simpa [hGdef, liftForm] using h)⟩
  have hϖG : (C ϖ : MRing ι O) ∈ G := by
    rw [hGdef, Ideal.mem_comap, liftForm_const]; exact hϖG'

  obtain ⟨u, v, huG, huv⟩ := hD.2 G hGprime hPG hGrel
  have hfP := hD.1.num_not_mem
  have hgP := hD.1.den_not_mem
  have huP : u ∉ P := fun h => huG (hPG h)
  have hvP : v ∉ P := fun hv => by
    have h : u * f ∈ P := by
      rw [show u * f = (u * f - v * g) + v * g by ring]
      exact P.add_mem huv (P.mul_mem_right g hv)
    exact (hPprime.mem_or_mem h).elim huP hfP
  have hdown : ratDiv P f g G = divCycle P v G := by
    have h1 := congrFun (divCycle_congr_of_sub_mem huv) G
    rw [hmul₀ u f hPprime huP hfP, hmul₀ v g hPprime hvP hgP] at h1
    have hu0 : divCycle P u G = 0 := by
      by_contra h; exact huG (form_mem_of_divCycle_ne_zero h)
    simp only [Pi.add_apply] at h1
    unfold ratDiv; omega

  have hluP' : liftForm (J := BlowUpIdx ι) u ∉ P' := fun h => huG (hP'G' h)
  have hlfP' : liftForm (J := BlowUpIdx ι) f ∉ P' := fun h =>
    hexc.1.num_not_mem (by rw [map_mul]; exact P'.mul_mem_right _ h)
  have hlgP' : liftForm (J := BlowUpIdx ι) g ∉ P' := fun h => hexc.1.den_not_mem (P'.mul_mem_right _ h)
  have hluv : liftForm u * liftForm f - liftForm v * liftForm g ∈ P' := by
    rw [← map_mul, ← map_mul, ← map_sub]; exact hlift _ huv
  have hlvP' : liftForm (J := BlowUpIdx ι) v ∉ P' := fun hv => by
    have h : liftForm u * liftForm f ∈ P' := by
      rw [show liftForm u * liftForm f = (liftForm u * liftForm f - liftForm v * liftForm g) +
        liftForm v * liftForm g by ring]
      exact P'.add_mem hluv (P'.mul_mem_right _ hv)
    exact nm _ _ hluP' hlfP' h
  have hup : ratDiv P' (liftForm f) (liftForm g) G' = divCycle P' (liftForm v) G' := by
    have h1 := congrFun (divCycle_congr_of_sub_mem hluv) G'
    rw [hmul _ _ hP'prime hluP' hlfP', hmul _ _ hP'prime hlvP' hlgP'] at h1
    have hu0 := hzero _ huG
    simp only [Pi.add_apply] at h1
    unfold ratDiv; omega

  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := hres.1.num_not_mem
  have hlmP' : liftForm (J := BlowUpIdx ι) m ∉ P' := hres.1.den_not_mem
  have hY₀P' : (newVar none : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := fun h => hY₀G' (hP'G' h)
  have hrel := congrFun (divCycle_congr_of_sub_mem (blowUp_relation P s g f m e)) G'
  rw [map_mul, map_mul, hmul _ _ hP'prime (nm _ _ hsP' hlgP') hY₁P',
    hmul _ _ hP'prime (nm _ _ hlfP' hlmP') hY₀P', hmul _ _ hP'prime hsP' hlgP',
    hmul _ _ hP'prime hlfP' hlmP'] at hrel
  have hY₀0 := hzero _ hY₀G'
  simp only [Pi.add_apply] at hrel
  have hv := hcmp v hvP
  refine ⟨G, hϖG, hcmp s hsP, ?_⟩
  unfold ratDiv at hup hdown ⊢
  omega

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ResidualDisjoint.proof : ResidualDisjoint.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  have hPprime : P.IsPrime := hP.multiProj.isPrime
  have hP'prime : P'.IsPrime := RingHom.ker_isPrime _
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hlm : liftForm (J := BlowUpIdx ι) m ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact hmP h
  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker] at h
    simp only [newVar, aeval_X, blowUpSubst, blowUpGens, mul_eq_zero, Polynomial.X_ne_zero, or_false,
      Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h
    exact (hPprime.mem_or_mem h).elim hD.1.num_not_mem hmP
  have hnonneg : ∀ x W, 0 ≤ divCycle P' x W := fun x W => by
    unfold divCycle; split_ifs <;> simp
  have hzero : ∀ x, x ∉ G' → divCycle P' x G' = 0 := fun x hx => by
    by_contra h; exact hx (form_mem_of_divCycle_ne_zero h)
  have hG'supp : G' ∈ (P' ⊔ Ideal.span {liftForm s}).minimalPrimes ∧ IsRelevant G' := by
    by_contra h
    unfold divCycle at hsG'
    rw [dif_neg h] at hsG'
    exact (lt_irrefl 0) hsG'
  have hP'G' : P' ≤ G' := le_sup_left.trans hG'supp.1.1.2

  have hY₁G' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' := by
    apply form_mem_of_divCycle_ne_zero (P := P')
    have := hnonneg (liftForm m) G'
    unfold ratDiv at hresG'; omega

  have hYiG' : ∀ i : ∀ k, ι k, (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' := by
    intro i
    by_contra hYi
    have hrel : liftForm (powMonomial e i) * newVar (some none) -
        liftForm m * newVar (some (some i)) ∈ P' := by
      rw [hP'def, blowUpOf, RingHom.mem_ker]
      simp only [map_sub, map_mul, aeval_blowUpSubst_liftForm, newVar, aeval_X, blowUpSubst, blowUpGens]
      ring
    have hYiP' : (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := fun h => hYi (hP'G' h)
    by_cases hp : liftForm (J := BlowUpIdx ι) (powMonomial e i : MRing ι O) ∈ P'
    · have h := P'.sub_mem (P'.mul_mem_right (newVar (some none)) hp) hrel
      rw [sub_sub_cancel] at h
      exact (hP'prime.mem_or_mem h).elim hlm hYiP'
    · have h1 := congrFun (divCycle_congr_of_sub_mem hrel) G'
      rw [hmul _ _ hP'prime hp hY₁P', hmul _ _ hP'prime hlm hYiP'] at h1
      simp only [Pi.add_apply] at h1
      have h2 := hzero _ hYi
      have h3 := hnonneg (liftForm (powMonomial e i)) G'
      unfold ratDiv at hresG'; omega

  obtain ⟨j, hj⟩ := hG'supp.2 none
  change BlowUpIdx ι at j
  rcases j with _ | _ | i
  · exact hj
  · exact absurd hY₁G' hj
  · exact absurd (hYiG' i) hj

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DivCycleMul.full : DivCycleMul.Statement.{u} := DivCycleMul.proof

theorem DivCycleFiniteSupport.full : DivCycleFiniteSupport.Statement.{u} :=
  DivCycleFiniteSupport.proof

theorem SupSpanMultiHomog.full : SupSpanMultiHomog.Statement.{u} := SupSpanMultiHomog.proof

theorem MinimalPrimeMultiHomog.full : MinimalPrimeMultiHomog.Statement.{u} :=
  MinimalPrimeMultiHomog.proof

theorem SpecialQuotDim.full : SpecialQuotDim.Statement.{u} := SpecialQuotDim.proof

theorem MaximalIdealHeightFG.full : MaximalIdealHeightFG.Statement.{u} := MaximalIdealHeightFG.proof

theorem GenericDimBound.full : GenericDimBound.Statement.{u} :=
  GenericDimBound.proof MaximalIdealHeightFG.full

theorem GenericFibProps.full : GenericFibProps.Statement.{u} := GenericFibProps.proof

theorem GenericCycleCorresp.full : GenericCycleCorresp.Statement.{u} := GenericCycleCorresp.proof

theorem ConservationOfNumberLE.full : ConservationOfNumberLE.Statement.{u} :=
  ConservationOfNumberLE.proof IntNumAssoc.full SpecialCycleEval.full SpecialPieceRank.full
    GenericPieceRank.full SpecialIdealMultiHomog.full

theorem UniformiserCase.full : UniformiserCase.Statement.{u} :=
  UniformiserCase.proof ConservationOfNumberLE.full GenericDimBound.full GenericFibProps.full
    GenericCycleCorresp.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full DimStrictDrop.full
    CutByForm.full

theorem ShiftByUniformiser.full : ShiftByUniformiser.Statement.{u} :=
  ShiftByUniformiser.proof DivCycleMul.full DivCycleFiniteSupport.full

theorem EffectiveShift.full : EffectiveShift.Statement.{u} := EffectiveShift.proof

theorem Representative.full : Representative.Statement.{u} := Representative.proof DivCycleMul.full

theorem IntNumAddFirst.full : IntNumAddFirst.Statement.{u} :=
  IntNumAddFirst.proof FieldNumbers.IntNumAdd.full FieldNumbers.IntNumZeroSlot.full
    FieldNumbers.HilbDegreeBound.full

theorem EffectiveCase.of_steps (h₀ : NoCommonComponentCase.Statement.{u}) (h₁ : CommonFactorInduction.Statement.{u}) :
    EffectiveCase.Statement.{u} :=
  EffectiveCase.proof h₀ h₁

theorem CutByEffectiveDivisor.of_steps (h₀ : NoCommonComponentCase.Statement.{u})
    (h₁ : CommonFactorInduction.Statement.{u}) : CutByEffectiveDivisor.Statement.{u} :=
  CutByEffectiveDivisor.proof (EffectiveCase.of_steps h₀ h₁) UniformiserCase.full
    ShiftByUniformiser.full EffectiveShift.full

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalCorresp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem finsum_eq_finsum_mem_of_support_subset' {α : Type*} (f : α → ℤ) {s : Set α}
    (h : Function.support f ⊆ s) : ∑ᶠ i, f i = ∑ᶠ i ∈ s, f i := by
  rw [finsum_mem_def, Set.indicator_eq_self.2 h]

theorem BlowUpHorizontalCorresp.proof (hsat : BlowUpHorizontalSat.Statement.{u})
    (hmult : BlowUpHorizontalMult.Statement.{u}) (hlift : BlowUpHorizontalLift.Statement.{u})
    (hstrict : BlowUpHorizontalStrict.Statement.{u}) : BlowUpHorizontalCorresp.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP
  have sat := hsat O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have mult := hmult O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have lift := hlift O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have strict := hstrict O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have hC : ∀ W : Ideal (MRing (extIdx ι J) O),
      (C ϖ : MRing ι O) ∈ W.comap (liftForm (ι := ι) (J := J) (R := O)) ↔
        (C ϖ : MRing (extIdx ι J) O) ∈ W := by
    intro W
    rw [Ideal.mem_comap]
    simp [liftForm]
  refine ⟨fun h => ?_, fun W hW hϖW => ⟨by rw [mult W hW hϖW]; exact hW, strict W hW hϖW⟩⟩
  classical
  unfold cycEval
  let s : Set (Ideal (MRing (extIdx ι J) O)) :=
    {W | divCycle (blowUpOf P u) (liftForm x) W ≠ 0 ∧ (C ϖ : MRing (extIdx ι J) O) ∉ W}
  let t : Set (Ideal (MRing ι O)) := {W | divCycle P x W ≠ 0 ∧ (C ϖ : MRing ι O) ∉ W}
  rw [finsum_eq_finsum_mem_of_support_subset' _ (s := s) ?hs,
    finsum_eq_finsum_mem_of_support_subset' _ (s := t) ?ht]
  case hs =>
    intro W hW
    rw [Function.mem_support] at hW
    exact ⟨fun h0 => hW (by rw [h0, zero_mul]), fun hc => hW (by simp only [if_pos hc, mul_zero])⟩
  case ht =>
    intro W hW
    rw [Function.mem_support] at hW
    exact ⟨fun h0 => hW (by rw [h0, zero_mul]), fun hc => hW (by simp only [if_pos hc, mul_zero])⟩
  refine finsum_mem_eq_of_bijOn (fun W => W.comap (liftForm (ι := ι) (J := J) (R := O)))
    ⟨?_, ?_, ?_⟩ ?_
  · intro W hW
    exact ⟨by rw [mult W hW.1 hW.2]; exact hW.1, fun h => hW.2 ((hC W).1 h)⟩
  · intro W₁ h₁ W₂ h₂ he
    ext F
    rw [sat W₁ h₁.1 h₁.2 F, sat W₂ h₂.1 h₂.2 F]
    simp only at he
    rw [he]
  · intro W hW
    obtain ⟨W', h1, h2, h3⟩ := lift W hW.1 hW.2
    exact ⟨W', ⟨h1, h2⟩, h3⟩
  · intro W hW
    simp only
    rw [if_neg hW.2, if_neg (fun h => hW.2 ((hC W).1 h)), mult W hW.1 hW.2]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalStrict
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Helpers

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem blowUpOf_mono {P W : Ideal (MRing ι R)} (h : P ≤ W) (u : J → MRing ι R) :
    blowUpOf P u ≤ blowUpOf W u := by
  intro F hF
  let φ := Polynomial.mapRingHom (Ideal.Quotient.factor h)
  have key : φ.comp (aeval (R := R) (blowUpSubst P u)).toRingHom =
      (aeval (R := R) (blowUpSubst W u)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [φ]
      rfl
    · rintro ⟨_ | k, i⟩
      · simp [φ, blowUpSubst, Ideal.Quotient.factor_mk]
      · simp [φ, blowUpSubst, Ideal.Quotient.factor_mk]
  have e := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e
  rw [blowUpOf, RingHom.mem_ker] at hF ⊢
  rw [← e, hF, map_zero]

theorem blowUpOf_isPrime {W : Ideal (MRing ι R)} (hW : W.IsPrime) (u : J → MRing ι R) :
    (blowUpOf W u).IsPrime := by
  have := hW
  exact RingHom.ker_isPrime _

theorem blowUpOf_comap_le {P : Ideal (MRing ι R)} {u : J → MRing ι R} {H : Ideal (MRing (extIdx ι J) R)}
    (hH : H.IsPrime) (hPH : blowUpOf P u ≤ H) {j₀ : J}
    (hj₀ : u j₀ ∉ H.comap (liftForm (ι := ι) (J := J) (R := R))) :
    blowUpOf (H.comap (liftForm (ι := ι) (J := J) (R := R))) u ≤ H := by
  have := hH
  let L := FractionRing (MRing (extIdx ι J) R ⧸ H)
  let q : MRing (extIdx ι J) R →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk H)
  have hq : ∀ y, q y = 0 ↔ y ∈ H := by
    intro y
    simp only [q, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]
  have hu₀ : q (liftForm (u j₀)) ≠ 0 := fun h0 => hj₀ ((hq _).mp h0)
  let ψ : MRing ι R ⧸ H.comap (liftForm (ι := ι) (J := J) (R := R)) →+* L :=
    Ideal.Quotient.lift _ (q.comp (liftForm (ι := ι) (J := J) (R := R)).toRingHom) fun a ha => (hq _).mpr ha
  let ε : Polynomial (MRing ι R ⧸ H.comap (liftForm (ι := ι) (J := J) (R := R))) →+* L :=
    Polynomial.eval₂RingHom ψ (q (newVar j₀) / q (liftForm (u j₀)))
  have hψ : ∀ a : MRing ι R, ψ (Ideal.Quotient.mk _ a) = q (liftForm a) := fun a =>
    Ideal.Quotient.lift_mk _ _ _

  have hrelq : ∀ j : J, q (newVar j) * q (liftForm (u j₀)) = q (liftForm (u j)) * q (newVar j₀) := by
    intro j
    have hr : newVar j * liftForm (u j₀) - newVar j₀ * liftForm (u j) ∈ H :=
      hPH (mem_blowUpOf_of_sub (P := P) (u := u) (j := j) (j' := j₀) (a := u j₀) (a' := u j)
        (by rw [show u j * u j₀ - u j₀ * u j = 0 from by ring]; exact P.zero_mem))
    have h1 := (hq _).mpr hr
    rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
    rw [h1, mul_comm]
  have key : ε.comp (aeval (R := R) (blowUpSubst (H.comap (liftForm (ι := ι) (J := J) (R := R))) u)).toRingHom =
      q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C,
        Polynomial.algebraMap_apply, ← Ideal.Quotient.mk_algebraMap]
      simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [hψ, AlgHom.commutes]
      rfl
    · rintro ⟨_ | k, i⟩
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
        show ε (Polynomial.C (Ideal.Quotient.mk _ (u i)) * Polynomial.X) = q (newVar i)
        simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        rw [hψ, ← mul_div_assoc, div_eq_iff hu₀]
        exact (hrelq i).symm
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
        show ε (Polynomial.C (Ideal.Quotient.mk _ (X ⟨k, i⟩))) = q (X ⟨some k, i⟩)
        simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        rw [hψ, liftForm_X]
  intro F hF
  rw [blowUpOf, RingHom.mem_ker] at hF
  have h3 := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3
  rw [hF, map_zero] at h3
  exact (hq F).mp h3.symm

end Helpers

theorem BlowUpHorizontalStrict.full : BlowUpHorizontalStrict.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW hj
  obtain ⟨j₀, hj₀⟩ := hj
  obtain ⟨hWp, hBW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hPW₀ : P ≤ W.comap (liftForm (ι := ι) (J := J) (R := O)) := fun p hp => hBW (liftForm_mem_blowUpOf hp)
  have hle := blowUpOf_comap_le hWp hBW hj₀
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine le_antisymm (hmin.2 ⟨blowUpOf_isPrime (Ideal.comap_isPrime _ _) u,
    sup_le (blowUpOf_mono hPW₀ u) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hle) hle
  exact liftForm_mem_blowUpOf (P := W.comap (liftForm (ι := ι) (J := J) (R := O))) hxW

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelCommonModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord)

theorem FlagModelCommonModel.proof (hModel : JoinTwoModels.Statement)
    (hPull : JoinPullbackAlt.Statement) (hVert : JoinVerticalDivisor.Statement)
    (hLeft : FlagModelJoinLeftAlt.Statement) (hRight : FlagModelJoinRightAlt.Statement) :
    FlagModelCommonModel.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hW hE F₁ F₂
  obtain ⟨hZ, hfn⟩ := hModel O Ω K ι x d hW F₁.K' F₁.ι' F₁.z F₂.K' F₂.ι' F₂.z F₁.model F₁.birat
    F₂.model F₂.birat
  obtain ⟨EB, E'B, hp, hp', hsame⟩ :=
    hPull O Ω K ι x (F₁.K' ⊕ F₂.K') (Sum.elim F₁.ι' F₂.ι') (joinCoord F₁.z F₂.z) N V E E' hE
  obtain ⟨φ₁, h₁⟩ := hLeft O Ω K ι x d N V E E' hW hE F₁ F₂.K' F₂.ι' F₂.z hZ hfn EB E'B hp hp'
  obtain ⟨φ₂, h₂⟩ := hRight O Ω K ι x d N V E E' hW hE F₂ F₁.K' F₁.ι' F₁.z hZ hfn EB E'B hp hp'
  refine ⟨F₁.K' ⊕ F₂.K', inferInstance, Sum.elim F₁.ι' F₂.ι', inferInstance, joinCoord F₁.z F₂.z, EB, E'B,
    φ₁, φ₂, hZ, hfn, hp, hp', hsame, fun b f g hv => hVert O Ω K ι x _ _ _ b f g hv, ?_⟩
  intro I I₁ I₂ hI hI₁ hI₂ G r y y' f g hv c Q hc hG hQ
  exact ⟨h₁ I I₁ hI hI₁ G r y y' f g hv c Q hc hG hQ, h₂ I I₂ hI hI₂ G r y y' f g hv c Q hc hG hQ⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

