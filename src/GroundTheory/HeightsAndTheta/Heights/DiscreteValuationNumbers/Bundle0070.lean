module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutForms
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0066

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocPointLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem blowUpEval_ne_zero_of_not_mem {K : Type} [DecidableEq K] {ι : K → Type} {J : Type} {O : Type u}
    [CommRing O] {P : Ideal (MRing ι O)} [P.IsPrime] {u : J → MRing ι O} {F : MRing (extIdx ι J) O}
    {b : Option K → ℕ} (hF : IsMultiHomog F b) (hFb : F ∉ blowUpOf P u) :
    algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  intro h
  apply hFb
  show F ∈ RingHom.ker (aeval (blowUpSubst P u))
  rw [RingHom.mem_ker]
  show aeval (blowUpSubst P u) F = 0
  rw [aeval_blowUpSubst_of_isMultiHomog P u hF, h, map_zero, zero_mul]

theorem div_mul_div_mul_cancel_of_ne_zero {F : Type*} [Field F] (a b c w : F) (hb : b ≠ 0) :
    a / b * (b / c * w) = a / c * w := by
  rw [← mul_assoc, div_mul_div_comm, mul_comm a b, mul_div_mul_left _ _ hb]

theorem BlowUpOverLocPointLoc.proof (hfin : BlowUpOverLocFinite.Statement.{u})
    (hcen : BlowUpOverLocMaxCentre.Statement.{u}) (hinj : BlowUpLocRingInj.Statement.{u}) :
    BlowUpOverLocPointLoc.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW'p hmh hW'rel hbl hW'W
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' :=
    iInf₂_le W' ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := BlowUpLocRingIso.proof O K ι J P u W' hbl
  obtain ⟨hlocT, hunitT⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hWp : W.IsPrime := hWmin.1.1
  obtain ⟨hlocA, hunitA⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW
  let 𝔫 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)

  have hcomapA : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal (homLocRing P W) ≤
        𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) := by
      rintro ⟨z, hz⟩ ha
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
      obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := (HomLocRingMem.proof O K ι P W hWp hPW z).mp hz
      have hfW : f ∈ W := by
        by_contra hfW
        exact ha ((hunitA b f g hf hg hgW hz).mpr hfW)
      have hgW' : liftForm (J := J) g ∉ W' := fun h => hgW (by rw [← hW'W]; exact h)
      have hfW' : liftForm (J := J) f ∈ W' := by rw [← hW'W] at hfW; exact hfW
      have hlf := isMultiHomog_liftForm (J := J) hf
      have hlg := isMultiHomog_liftForm (J := J) hg
      have hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm f)) /
          algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g)) ∈
          homLocRing (blowUpOf P u) W' :=
        Subring.subset_closure ⟨liftMDeg b, _, _, hlf, hlg, hgW', rfl⟩
      have hnu : ¬ IsUnit (⟨_, hz'⟩ : homLocRing (blowUpOf P u) W') :=
        fun h => (hunitT _ _ _ hlf hlg hgW' hz').mp h hfW'
      have hφz : Subring.inclusion hBR (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩) =
          φ ⟨_, hz'⟩ := by
        apply Subtype.ext
        rw [hφ _ _ _ hlf hlg hgW', blowUpEval_liftForm, blowUpEval_liftForm]
        rfl
      rw [Ideal.mem_comap, Ideal.mem_comap, hφz, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_map_iff]
      exact hnu
    have hne : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) ≠ ⊤ :=
      Ideal.comap_ne_top _ (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    rw [le_antisymm (IsLocalRing.le_maximalIdeal hne) hle]
    infer_instance
  obtain ⟨hfinite, -⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have h𝔫 : 𝔫.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (Algebra.IsIntegral.isIntegral) 𝔫 hcomapA
  refine ⟨hBR, 𝔫, h𝔫, ?_⟩

  obtain ⟨W₁, hW₁p, hW₁h, hW₁r, hW₁b, -, h₁, hl₁⟩ :=
    hcen O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫
  let _ := (Subring.inclusion h₁).toAlgebra
  have := h𝔫.isPrime
  have hl : IsLocalization.AtPrime (blowUpLocRing P u W₁) 𝔫 := hl₁

  have hunitB : ∀ s : blowUpOverLoc P W u, s ∉ 𝔫 → IsUnit (Subring.inclusion hBR s) := by
    intro s hs
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)

  have h3 : blowUpLocRing P u W₁ ≤ blowUpLocRing P u W' := by
    intro z hz
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔫.primeCompl (⟨z, hz⟩ : blowUpLocRing P u W₁)
    obtain ⟨t, ht⟩ := (hunitB s s.2).exists_right_inv
    have e₁ : z * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) :=
      congrArg Subtype.val hbs
    have e₂ : ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * (t : FractionRing (MRing ι O ⧸ P)) = 1 := congrArg Subtype.val ht
    have hzt : z = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t := by
      calc z = z * (((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t) := by rw [e₂, mul_one]
        _ = (z * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P))) * t := by ring
        _ = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t := by rw [e₁]
    rw [hzt]
    exact (blowUpLocRing P u W').mul_mem (hBR b.2) t.2

  have hdom : ∀ (y : FractionRing (MRing ι O ⧸ P)) (hy₁ : y ∈ blowUpLocRing P u W₁) (hy' : y ∈ blowUpLocRing P u W'),
      IsUnit (⟨y, hy'⟩ : blowUpLocRing P u W') → IsUnit (⟨y, hy₁⟩ : blowUpLocRing P u W₁) := by
    intro y hy₁ hy' hyu
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔫.primeCompl (⟨y, hy₁⟩ : blowUpLocRing P u W₁)
    have e₁ : y * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) :=
      congrArg Subtype.val hbs
    have hb : b ∉ 𝔫 := by
      intro hb
      have hb' : Subring.inclusion hBR b ∈ IsLocalRing.maximalIdeal (blowUpLocRing P u W') := hb
      apply (IsLocalRing.mem_maximalIdeal _).mp hb'
      have hprod : Subring.inclusion hBR b = (⟨y, hy'⟩ : blowUpLocRing P u W') * Subring.inclusion hBR s :=
        Subtype.ext e₁.symm
      rw [hprod]
      exact hyu.mul (hunitB s s.2)
    have hbu : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W₁) b) :=
      IsLocalization.map_units (M := 𝔫.primeCompl) _ (⟨b, hb⟩ : 𝔫.primeCompl)
    rw [← hbs] at hbu
    exact isUnit_of_mul_isUnit_left hbu

  have h5 : blowUpLocRing P u W' ≤ blowUpLocRing P u W₁ := by
    refine Subring.closure_le.mpr ?_
    rintro z ⟨d, F, G, hF, hG, hGW', rfl⟩
    obtain ⟨i, hi⟩ := powMonomial_not_mem hW₁p hW₁r d
    have hH := isMultiHomog_powMonomial (R := O) d i
    have hσH : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ≠ 0 :=
      blowUpEval_ne_zero_of_not_mem hH (fun h => hi (hW₁b h))
    have hσG : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) ≠ 0 := blowUpEval_ne_zero_of_not_mem hG (fun h => hGW' (hbl h))
    have hy₁ : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ∈ blowUpLocRing P u W₁ :=
      Subring.subset_closure ⟨d, G, _, hG, hH, hi, rfl⟩
    have hFH : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ∈ blowUpLocRing P u W₁ :=
      Subring.subset_closure ⟨d, F, _, hF, hH, hi, rfl⟩
    have hinv : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) ∈ blowUpLocRing P u W' :=
      Subring.subset_closure ⟨d, _, G, hH, hG, hGW', rfl⟩
    have hyu : IsUnit (⟨_, h3 hy₁⟩ : blowUpLocRing P u W') := by
      refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : blowUpLocRing P u W') (Subtype.ext ?_)
      show algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) * (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G)) = 1
      field_simp
    obtain ⟨v, hv⟩ := hdom _ hy₁ (h3 hy₁) hyu
    have e : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
        (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) = 1 := by
      have := congrArg Subtype.val v.mul_inv
      rw [hv] at this
      exact this
    have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
        (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) := by
      calc algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G)
          = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) * (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
            (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P))) := by rw [e, mul_one]
        _ = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
            (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) :=
          div_mul_div_mul_cancel_of_ne_zero _ _ _ _ hσG
    rw [hz]
    exact (blowUpLocRing P u W₁).mul_mem hFH (Subtype.property _)
  have heq : W₁ = W' :=
    hinj O K ι J P u W₁ W' hW₁p hW₁h hW₁r hW₁b hW'p hmh hW'rel hbl (le_antisymm h3 h5)
  subst heq
  exact hl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChartSectionTools
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial GenericProjClosureDivisor

noncomputable section

set_option linter.unusedSectionVars false

namespace SegreFlagCutChartSection

section Component

variable {O : Type} [CommRing O] {Φ : Type} [Field Φ] [Algebra O Φ] {K : Type} [DecidableEq K] {ι : K → Type}

def coneWeight (K : Type) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1

theorem coneMap_monomial_isWeightedHomogeneous (z : (Σ k, ι k) → Φ) (d : (Σ k, ι k) →₀ ℕ) (a : O) :
    IsWeightedHomogeneous (coneWeight K) (pointConeMap O z (monomial d a))
      (Finsupp.weight (blockWeight ι) d) := by
  rw [pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod,
    Finsupp.sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
  exact ((isWeightedHomogeneous_X (R := Φ) (coneWeight K) p.1).C_mul (z p)).pow (d p)

theorem coneMap_component (z : (Σ k, ι k) → Φ) (b : K → ℕ) (f : MRing ι O) :
    weightedHomogeneousComponent (coneWeight K) b (pointConeMap O z f) =
      pointConeMap O z (weightedHomogeneousComponent (blockWeight ι) b f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 := coneMap_monomial_isWeightedHomogeneous (K := K) (O := O) z d a
    have h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι O)
        (Finsupp.weight (blockWeight ι) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : b = Finsupp.weight (blockWeight ι) d
    · subst h
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]

theorem isMultiHomogIdeal_pointIdeal (z : (Σ k, ι k) → Φ) : IsMultiHomogIdeal (pointIdeal O z) := by
  intro f hf b
  rw [pointIdeal, RingHom.mem_ker] at hf ⊢
  have := coneMap_component (O := O) z b f
  rw [show (pointConeMap O z) f = 0 from hf, map_zero] at this
  exact this.symm

end Component

section Subst

variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  {O : Type} [CommRing O]

theorem bind₁_isMultiHomog_of (Λ : (K₁ → ℕ) →+ (K₂ → ℕ)) (g : (Σ k, ι₁ k) → MRing ι₂ O)
    (hg : ∀ v, IsWeightedHomogeneous (blockWeight ι₂) (g v) (Λ (blockWeight ι₁ v))) {q : MRing ι₁ O}
    {d : K₁ → ℕ} (hq : IsMultiHomog q d) : IsMultiHomog (bind₁ g q) (Λ d) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← q.support_sum_monomial_coeff, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hmd : Finsupp.weight (blockWeight ι₁) m = d := hq (mem_support_iff.mp hm)
  rw [bind₁_monomial]
  have := (isWeightedHomogeneous_C (blockWeight ι₂) (AddMonoidAlgebra.coeff q m)).mul
    (IsWeightedHomogeneous.prod m.support (fun v => g v ^ m v) (fun v => m v • Λ (blockWeight ι₁ v))
      (fun v _ => (hg v).pow (m v)))
  rw [zero_add] at this
  have hΛ : Λ d = ∑ v ∈ m.support, m v • Λ (blockWeight ι₁ v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hmd, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp only [map_nsmul]
  rw [hΛ]
  exact this

theorem bind₁_scale_of (o₀ : K₁) (u : MRing ι₂ O) (h : (Σ k, ι₁ k) → MRing ι₂ O) {q : MRing ι₁ O}
    {d : K₁ → ℕ} (hq : IsMultiHomog q d) :
    bind₁ (fun v => u ^ blockWeight ι₁ v o₀ * h v) q = u ^ d o₀ * bind₁ h q := by
  conv_lhs => rw [← q.support_sum_monomial_coeff]
  conv_rhs => rw [← q.support_sum_monomial_coeff]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : Finsupp.weight (blockWeight ι₁) m = d := hq (mem_support_iff.mp hm)
  have hs : ∑ v ∈ m.support, blockWeight ι₁ v o₀ * m v = d o₀ := by
    rw [← hmd, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [mul_comm]
  rw [bind₁_monomial, bind₁_monomial]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, hs]
  ring

theorem rename_eq_bind₁ {σ τ R : Type*} [CommRing R] (f : σ → τ) (q : MvPolynomial σ R) :
    rename f q = bind₁ (fun p => X (f p)) q := by
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, rename_X, bind₁_X_right]

theorem bind₁_sub_mem_of {σ τ R : Type*} [CommRing R] (I : Ideal (MvPolynomial τ R))
    (g g' : σ → MvPolynomial τ R) (h : ∀ v, g' v - g v ∈ I) (q : MvPolynomial σ R) :
    bind₁ g' q - bind₁ g q ∈ I := by
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
    exact I.add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul, map_mul, bind₁_X_right, bind₁_X_right,
      show bind₁ g' p * g' v - bind₁ g p * g v =
        (bind₁ g' p - bind₁ g p) * g' v + bind₁ g p * (g' v - g v) by ring]
    exact I.add_mem (I.mul_mem_right _ hp) (I.mul_mem_left _ (h v))

end Subst

section Saturate

variable {K₁ K₂ : Type} [Fintype K₁] [DecidableEq K₁] [Fintype K₂] [DecidableEq K₂] {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι₂ k)] {O : Type} [CommRing O] {Φ : Type} [Field Φ] [Algebra O Φ]

theorem saturate (j : K₁ ↪ K₂) (o₀ : K₁) (pt : (Σ k, ι₂ k) → Φ) (lam u D : MRing ι₂ O) (nD : ℕ)
    (hD : u ∣ D ^ nD) (e : K₂ → ℕ) (g : (Σ k, ι₂ (j k)) → MRing ι₂ O)
    (hg₁ : ∀ p, p.1 ≠ o₀ → g p = X (FieldNumbers.blockIncl j ι₂ p))
    (hg₂ : ∀ p, p.1 = o₀ → IsWeightedHomogeneous (blockWeight ι₂) (g p) e ∧
      u * X (FieldNumbers.blockIncl j ι₂ p) - g p ∈ Ideal.span {lam})
    (I : Ideal (MRing (fun k => ι₂ (j k)) O)) (hI : IsMultiHomogIdeal I)
    (hvan : ∀ q ∈ I, aeval (fun p => aeval pt (g p)) q = 0) :
    ∀ q ∈ I, ∃ n : ℕ, D ^ n * rename (FieldNumbers.blockIncl j ι₂) q ∈ pointIdeal O pt ⊔ Ideal.span {lam} := by
  classical
  let Λ₁ : K₁ → K₂ → ℕ := fun k => if k = o₀ then e else Pi.single (j k) 1
  let Λ : (K₁ → ℕ) →+ (K₂ → ℕ) :=
    { toFun := fun d => ∑ k, d k • Λ₁ k
      map_zero' := by simp
      map_add' := fun d d' => by simp [add_smul, Finset.sum_add_distrib] }
  have hΛ : ∀ v : Σ k, ι₂ (j k), Λ (blockWeight (fun k => ι₂ (j k)) v) = Λ₁ v.1 := by
    intro v
    simp only [Λ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, blockWeight]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hgh : ∀ v, IsWeightedHomogeneous (blockWeight ι₂) (g v) (Λ (blockWeight _ v)) := by
    intro v
    rw [hΛ]
    by_cases hv : v.1 = o₀
    · simp only [Λ₁, if_pos hv]
      exact (hg₂ v hv).1
    · simp only [Λ₁, if_neg hv]
      rw [hg₁ v hv]
      exact isWeightedHomogeneous_X O (blockWeight ι₂) (FieldNumbers.blockIncl j ι₂ v)
  have hform : ∀ (d : K₁ → ℕ) (q : MRing (fun k => ι₂ (j k)) O), IsMultiHomog q d → q ∈ I →
      u ^ d o₀ * rename (FieldNumbers.blockIncl j ι₂) q ∈ pointIdeal O pt ⊔ Ideal.span {lam} := by
    intro d q hqd hqI
    have h1 : bind₁ g q ∈ pointIdeal O pt := by
      refine mem_of_homog (bind₁_isMultiHomog_of Λ g hgh hqd) ?_
      rw [aeval_bind₁]
      exact hvan q hqI
    have h2 : u ^ d o₀ * rename (FieldNumbers.blockIncl j ι₂) q - bind₁ g q ∈ Ideal.span {lam} := by
      have hr : rename (FieldNumbers.blockIncl j ι₂) q =
          bind₁ (fun p => X (FieldNumbers.blockIncl j ι₂ p)) q := rename_eq_bind₁ _ q
      rw [hr, ← bind₁_scale_of o₀ u _ hqd]
      refine bind₁_sub_mem_of _ g _ (fun v => ?_) q
      by_cases hv : v.1 = o₀
      · have : blockWeight (fun k => ι₂ (j k)) v o₀ = 1 := by simp [blockWeight, hv]
        rw [this, pow_one]
        exact (hg₂ v hv).2
      · have : blockWeight (fun k => ι₂ (j k)) v o₀ = 0 := by
          simp [blockWeight, Ne.symm hv]
        rw [this, pow_zero, one_mul, hg₁ v hv, sub_self]
        exact zero_mem _
    have h3 := Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
    rwa [add_sub_cancel] at h3
  intro q hq
  have hsat : ∀ d, ∃ n : ℕ, D ^ n * rename (FieldNumbers.blockIncl j ι₂)
      (weightedHomogeneousComponent (blockWeight (fun k => ι₂ (j k))) d q) ∈
      pointIdeal O pt ⊔ Ideal.span {lam} := by
    intro d
    have hqd := hform d _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (hI q hq d)
    obtain ⟨r, hr⟩ := hD
    refine ⟨nD * d o₀, ?_⟩
    rw [pow_mul, hr, mul_pow, mul_comm (u ^ d o₀) (r ^ d o₀), mul_assoc]
    exact Ideal.mul_mem_left _ _ hqd
  choose nn hnn using hsat
  obtain ⟨S, hS⟩ : ∃ S : Finset (K₁ → ℕ),
      q = ∑ d ∈ S, weightedHomogeneousComponent (blockWeight (fun k => ι₂ (j k))) d q := by
    have hfin := weightedHomogeneousComponent_finsupp (w := blockWeight (fun k => ι₂ (j k))) q
    refine ⟨hfin.toFinset, ?_⟩
    conv_lhs => rw [← sum_weightedHomogeneousComponent (blockWeight (fun k => ι₂ (j k))) q]
    exact finsum_eq_sum _ hfin
  refine ⟨∑ d ∈ S, nn d, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hS, map_sum, Finset.mul_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  rw [← Nat.sub_add_cancel (Finset.single_le_sum (f := nn) (fun _ _ => Nat.zero_le _) hd), pow_add,
    mul_assoc]
  exact Ideal.mul_mem_left _ _ (hnn d)

end Saturate

end SegreFlagCutChartSection

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocFamilyFiniteCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocFibreFinite.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      {Q : Ideal (MRing (extIdx ι J) O) | Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
        blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := O)) = W}.Finite

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

