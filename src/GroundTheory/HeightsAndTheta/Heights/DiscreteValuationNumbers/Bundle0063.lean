module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0060

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section BlowUpLocRingInj

variable {R : Type*} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type} {J : Type}

theorem blowUpSubst_eq_C_mul_X_pow (P : Ideal (MRing ι R)) (u : J → MRing ι R) (v : Σ o, extIdx ι J o) :
    blowUpSubst P u v =
      Polynomial.C (blowUpEval P u (X v)) * Polynomial.X ^ (blockWeight (extIdx ι J) v none) := by
  obtain ⟨(_ | k), i⟩ := v
  · simp [blowUpSubst, blowUpEval, blockWeight]
  · simp [blowUpSubst, blowUpEval, blockWeight]

theorem aeval_blowUpSubst_monomial (P : Ideal (MRing ι R)) (u : J → MRing ι R)
    (d : (Σ o, extIdx ι J o) →₀ ℕ) (c : R) :
    aeval (blowUpSubst P u) (monomial d c) =
      Polynomial.C (blowUpEval P u (monomial d c)) *
        Polynomial.X ^ (Finsupp.weight (blockWeight (extIdx ι J)) d none) := by
  have key : ∃ q, aeval (blowUpSubst P u) (monomial d c) =
      Polynomial.C q * Polynomial.X ^ (Finsupp.weight (blockWeight (extIdx ι J)) d none) := by
    refine ⟨algebraMap R _ c * ∏ v ∈ d.support, blowUpEval P u (X v) ^ d v, ?_⟩
    have hp : ∀ (y : MRing ι R ⧸ P) (e k : ℕ),
        (Polynomial.C y * Polynomial.X ^ e) ^ k = Polynomial.C (y ^ k) * Polynomial.X ^ (e * k) := by
      intro y e k
      rw [map_pow, pow_mul]
      ring
    rw [aeval_monomial, Polynomial.algebraMap_apply, Finsupp.prod]
    simp_rw [blowUpSubst_eq_C_mul_X_pow, hp]
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum, ← mul_assoc, ← map_mul]
    refine congrArg₂ (· * ·) rfl (congrArg _ ?_)
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [mul_comm]
  obtain ⟨q, hq⟩ := key
  rw [hq]
  congr 2
  change q = Polynomial.eval 1 (aeval (blowUpSubst P u) (monomial d c))
  rw [hq]
  simp

theorem aeval_blowUpSubst_eq_C_blowUpEval_mul_X_pow (P : Ideal (MRing ι R)) (u : J → MRing ι R)
    {G : MRing (extIdx ι J) R} {b : Option K → ℕ} (hG : IsMultiHomog G b) :
    aeval (blowUpSubst P u) G = Polynomial.C (blowUpEval P u G) * Polynomial.X ^ b none := by
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_blowUpSubst_monomial, hG (mem_support_iff.mp hd)]

theorem mem_blowUpOf_of_isMultiHomog {P : Ideal (MRing ι R)} {u : J → MRing ι R}
    {G : MRing (extIdx ι J) R} {b : Option K → ℕ} (hG : IsMultiHomog G b) (h : blowUpEval P u G = 0) :
    G ∈ blowUpOf P u := by
  rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_eq_C_blowUpEval_mul_X_pow P u hG, h, map_zero, zero_mul]

theorem algebraMap_blowUpEval_ne_zero {P : Ideal (MRing ι R)} [P.IsPrime] {u : J → MRing ι R}
    {Q : Ideal (MRing (extIdx ι J) R)} (hle : blowUpOf P u ≤ Q) {G : MRing (extIdx ι J) R}
    {b : Option K → ℕ} (hG : IsMultiHomog G b) (hGQ : G ∉ Q) :
    algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G) ≠ 0 := by
  intro h
  have hmap : algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G) =
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) 0 := by
    rw [map_zero]
    exact h
  have hzero : blowUpEval P u G = 0 :=
    IsFractionRing.injective (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) hmap
  exact hGQ (hle (mem_blowUpOf_of_isMultiHomog hG hzero))

theorem exists_eq_div_of_mem_blowUpLocRing {P : Ideal (MRing ι R)} [P.IsPrime] {u : J → MRing ι R}
    {Q : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime) (hle : blowUpOf P u ≤ Q)
    {z : FractionRing (MRing ι R ⧸ P)} (hz : z ∈ blowUpLocRing P u Q) :
    ∃ (b : Option K → ℕ) (F G : MRing (extIdx ι J) R), IsMultiHomog F b ∧ IsMultiHomog G b ∧ G ∉ Q ∧
      z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) /
        algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G) := by
  have h1 : (1 : MRing (extIdx ι J) R) ∉ Q := fun h => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
  induction hz using Subring.closure_induction with
  | mem x hx => exact hx
  | zero =>
    exact ⟨0, 0, 1, isWeightedHomogeneous_zero R _ _, isWeightedHomogeneous_one R _, h1, by simp⟩
  | one =>
    exact ⟨0, 1, 1, isWeightedHomogeneous_one R _, isWeightedHomogeneous_one R _, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b₁, F₁, G₁, hF₁, hG₁, hG₁Q, rfl⟩ := hx
    obtain ⟨b₂, F₂, G₂, hF₂, hG₂, hG₂Q, rfl⟩ := hy
    refine ⟨b₁ + b₂, F₁ * G₂ + G₁ * F₂, G₁ * G₂,
      IsWeightedHomogeneous.add (IsWeightedHomogeneous.mul hF₁ hG₂) (IsWeightedHomogeneous.mul hG₁ hF₂),
      IsWeightedHomogeneous.mul hG₁ hG₂, fun h => (hQ.mem_or_mem h).elim hG₁Q hG₂Q, ?_⟩
    rw [div_add_div _ _ (algebraMap_blowUpEval_ne_zero hle hG₁ hG₁Q)
      (algebraMap_blowUpEval_ne_zero hle hG₂ hG₂Q)]
    simp only [RingHom.map_add, RingHom.map_mul]
  | neg x _ hx =>
    obtain ⟨b, F, G, hF, hG, hGQ, rfl⟩ := hx
    refine ⟨b, -F, G, fun d hd => hF (by rwa [coeff_neg, neg_ne_zero] at hd), hG, hGQ, ?_⟩
    rw [RingHom.map_neg, RingHom.map_neg, neg_div]
  | mul x y _ _ hx hy =>
    obtain ⟨b₁, F₁, G₁, hF₁, hG₁, hG₁Q, rfl⟩ := hx
    obtain ⟨b₂, F₂, G₂, hF₂, hG₂, hG₂Q, rfl⟩ := hy
    refine ⟨b₁ + b₂, F₁ * F₂, G₁ * G₂, IsWeightedHomogeneous.mul hF₁ hF₂,
      IsWeightedHomogeneous.mul hG₁ hG₂, fun h => (hQ.mem_or_mem h).elim hG₁Q hG₂Q, ?_⟩
    rw [div_mul_div_comm]
    simp only [map_mul]

theorem exists_monomial_not_mem_of_isMultiHomog {Q : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime)
    (hrel : IsRelevant Q) {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b)
    (hF0 : F ≠ 0) : ∃ M : MRing (extIdx ι J) R, IsMultiHomog M b ∧ M ∉ Q := by
  classical
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hF0
  choose i hi using hrel
  let e := Finsupp.mapDomain (fun v : Σ o, extIdx ι J o => (⟨v.1, i v.1⟩ : Σ o, extIdx ι J o)) d
  refine ⟨monomial e 1, isWeightedHomogeneous_monomial _ _ _ ?_, fun hmem => ?_⟩
  · rw [← hF hd]
    change Finsupp.linearCombination ℕ _ e = Finsupp.linearCombination ℕ _ d
    rw [Finsupp.linearCombination_mapDomain]
    rfl
  · have hmon : (monomial e 1 : MRing (extIdx ι J) R) ∈ Q.primeCompl := by
      rw [monomial_eq, map_one, one_mul, Finsupp.prod]
      refine prod_mem fun v hv => pow_mem ?_ _
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv)
      exact hi w.1
    exact hmon hmem

theorem mem_of_blowUpLocRing_le {P : Ideal (MRing ι R)} [P.IsPrime] {u : J → MRing ι R}
    {Q Q' : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime) (hrel : IsRelevant Q)
    (hle : blowUpOf P u ≤ Q) (hle' : blowUpOf P u ≤ Q')
    (hsub : blowUpLocRing P u Q' ≤ blowUpLocRing P u Q) {F : MRing (extIdx ι J) R} {b : Option K → ℕ}
    (hF : IsMultiHomog F b) (hFQ : F ∈ Q) : F ∈ Q' := by
  by_contra hFQ'
  have hF0 : F ≠ 0 := fun h => hFQ' (h ▸ Q'.zero_mem)
  obtain ⟨M, hM, hMQ⟩ := exists_monomial_not_mem_of_isMultiHomog hQ hrel hF hF0
  have hz : algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u M) /
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) ∈
        blowUpLocRing P u Q :=
    hsub (Subring.subset_closure ⟨b, M, F, hM, hF, hFQ', rfl⟩)
  obtain ⟨b₁, F₁, G₁, hF₁, hG₁, hG₁Q, heq⟩ := exists_eq_div_of_mem_blowUpLocRing hQ hle hz
  rw [div_eq_div_iff (algebraMap_blowUpEval_ne_zero hle' hF hFQ')
    (algebraMap_blowUpEval_ne_zero hle hG₁ hG₁Q)] at heq
  have hinj : blowUpEval P u M * blowUpEval P u G₁ = blowUpEval P u F₁ * blowUpEval P u F :=
    IsFractionRing.injective (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (by
      rw [map_mul, map_mul]
      exact heq)
  have h0 : blowUpEval P u (M * G₁ - F * F₁) = 0 := by
    rw [map_sub, map_mul, map_mul, hinj]
    ring
  have hmem : M * G₁ - F * F₁ ∈ Q :=
    hle (mem_blowUpOf_of_isMultiHomog (IsWeightedHomogeneous.sub
      (IsWeightedHomogeneous.mul hM hG₁) (IsWeightedHomogeneous.mul hF hF₁)) h0)
  rw [Submodule.sub_mem_iff_left _ (Q.mul_mem_right F₁ hFQ)] at hmem
  exact (hQ.mem_or_mem hmem).elim hMQ hG₁Q

theorem le_of_blowUpLocRing_le {P : Ideal (MRing ι R)} [P.IsPrime] {u : J → MRing ι R}
    {Q Q' : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime) (hQh : IsMultiHomogIdeal Q)
    (hrel : IsRelevant Q) (hle : blowUpOf P u ≤ Q) (hle' : blowUpOf P u ≤ Q')
    (hsub : blowUpLocRing P u Q' ≤ blowUpLocRing P u Q) : Q ≤ Q' := by
  intro f hf
  rw [← sum_weightedHomogeneousComponent (blockWeight (extIdx ι J)) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  exact Q'.sum_mem fun b _ => mem_of_blowUpLocRing_le hQ hrel hle hle' hsub
    (weightedHomogeneousComponent_isWeightedHomogeneous (n := b) (φ := f)) (hQh f hf b)

theorem BlowUpLocRingInj.proof : BlowUpLocRingInj.Statement.{u} := by
  intro R _ K _ ι J P _ u Q Q' hQ hQh hQr hQle hQ' hQ'h hQ'r hQ'le heq
  exact le_antisymm (le_of_blowUpLocRing_le hQ hQh hQr hQle hQ'le heq.ge)
    (le_of_blowUpLocRing_le hQ' hQ'h hQ'r hQ'le hQle heq.le)

end BlowUpLocRingInj

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Algebra

variable {L : Type*} [Field L]

theorem exists_mul_mem_of_mem_blowUpColon (A : Subring L) (I : Ideal A) (hI : I ≠ ⊥) {g : L}
    (hg : g ∈ blowUpColon L I) : ∃ d : A, d ≠ 0 ∧ ∃ r : A, algebraMap A L d * g = algebraMap A L r := by
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine Submodule.iSup_induction _ (motive := fun g => ∃ d : A, d ≠ 0 ∧ ∃ r : A,
    algebraMap A L d * g = algebraMap A L r) hg ?_ ⟨1, one_ne_zero, 0, by simp⟩ ?_
  · intro m g hg
    have hy : algebraMap A L y ^ m ∈ (Submodule.map (Algebra.linearMap A L) I) ^ m :=
      Submodule.pow_mem_pow _ (Submodule.mem_map_of_mem hyI) m
    have hgy := (Submodule.mem_div_iff_forall_mul_mem.mp hg) _ hy
    have h1 : Submodule.map (Algebra.linearMap A L) I ≤ 1 := by
      rw [Submodule.one_eq_range]
      exact LinearMap.map_le_range
    have hone : ∀ k : ℕ, (Submodule.map (Algebra.linearMap A L) I) ^ k ≤ 1 := by
      intro k
      induction k with
      | zero => exact (pow_zero _).le
      | succ k ih =>
        rw [pow_succ]
        exact (mul_le_mul' ih h1).trans (mul_one _).le
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hone m hgy)
    refine ⟨y ^ m, pow_ne_zero _ hy0, r, ?_⟩
    rw [map_pow, hr, mul_comm]
  · rintro g₁ g₂ ⟨d₁, hd₁, r₁, h₁⟩ ⟨d₂, hd₂, r₂, h₂⟩
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, d₂ * r₁ + d₁ * r₂, ?_⟩
    simp only [map_mul, map_add (f := _), ← h₁, ← h₂]
    ring

theorem finite_finrank_one_of_le_blowUpColon (A B : Subring L) [IsNoetherianRing A] (hAB : A ≤ B)
    (I : Ideal A) (hI : I ≠ ⊥) (hfg : (blowUpColon L I).FG) (hle : ∀ f ∈ B, f ∈ blowUpColon L I) :
    letI := (Subring.inclusion hAB).toAlgebra
    Module.Finite A B ∧ Module.finrank A B = 1 := by
  classical
  let _ := (Subring.inclusion hAB).toAlgebra

  let Bs : Submodule A L :=
    { carrier := B
      add_mem' := fun h₁ h₂ => add_mem h₁ h₂
      zero_mem' := zero_mem _
      smul_mem' := fun r f hf => by
        rw [Algebra.smul_def]
        exact mul_mem (hAB r.2) hf }
  obtain ⟨s, hs⟩ : Bs.FG := hfg.of_le fun f hf => hle f hf

  have hsB : ∀ g ∈ s, ∃ d : A, d ≠ 0 ∧ ∃ r : A, algebraMap A L d * g = algebraMap A L r := fun g hg =>
    exists_mul_mem_of_mem_blowUpColon A I hI (hle g (show g ∈ Bs from hs ▸ Submodule.subset_span hg))
  choose! dg hdg0 rg hrg using hsB
  have hd0 : (∏ g ∈ s, dg g) ≠ 0 := Finset.prod_ne_zero_iff.mpr hdg0
  let T : Submodule A L :=
    { carrier := {g | ∃ r : A, algebraMap A L (∏ g ∈ s, dg g) * g = algebraMap A L r}
      add_mem' := fun ⟨r₁, h₁⟩ ⟨r₂, h₂⟩ => ⟨r₁ + r₂, by rw [map_add (f := _), ← h₁, ← h₂, mul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := fun c g ⟨r, hr⟩ => ⟨c * r, by
        rw [Algebra.smul_def, map_mul, ← hr]
        ring⟩ }
  have hBT : Bs ≤ T := by
    rw [← hs, Submodule.span_le]
    intro g hg
    refine ⟨(∏ g' ∈ s.erase g, dg g') * rg g, ?_⟩
    rw [map_mul, ← hrg g hg, ← Finset.prod_erase_mul s dg hg, map_mul]
    ring

  let φ : Bs →ₗ[A] L := (LinearMap.mulLeft A (algebraMap A L (∏ g ∈ s, dg g))).comp Bs.subtype
  have hφ : Function.Injective φ := fun f₁ f₂ h => Subtype.ext
    (mul_left_cancel₀ (fun h0 => hd0 (Subtype.ext h0)) h)
  have hφr : LinearMap.range φ ≤ LinearMap.range (Algebra.linearMap A L) := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨r, hr⟩ := hBT f.2
    exact ⟨r, hr.symm⟩
  have hinj : Function.Injective (Algebra.linearMap A L) := fun _ _ h => Subtype.ext h
  have hle1 : Module.rank A Bs ≤ 1 := by
    rw [← rank_range_of_injective φ hφ, ← Module.rank_self A,
      ← rank_range_of_injective _ hinj]
    exact Submodule.rank_mono hφr
  let ψ : A →ₗ[A] Bs := (Algebra.linearMap A L).codRestrict Bs fun r => hAB r.2
  have hge1 : 1 ≤ Module.rank A Bs := by
    rw [← Module.rank_self A]
    exact LinearMap.rank_le_of_injective ψ fun x y h =>
      hinj (show Algebra.linearMap A L x = Algebra.linearMap A L y from congrArg (fun z : Bs => (z : L)) h)

  let e : Bs ≃ₗ[A] B :=
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f.1, f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Module.Finite A Bs := Module.Finite.iff_fg.mpr ⟨s, hs⟩
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq]
  exact Module.finrank_eq_of_rank_eq (le_antisymm hle1 (by exact_mod_cast hge1))

end Algebra

theorem BlowUpOverLocFinite.proof (hloc : HomLocRingLocal.Statement.{u})
    (hchart : BlowUpOverLocInChart.Statement.{u}) (hcolon : ChartsInColon.Statement.{u})
    (hfin : BlowUpColonFinite.Statement.{u}) : BlowUpOverLocFinite.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu ⟨j₀, hj₀⟩ c x hx hxP W hW hWrel
  have := hP.multiProj.isPrime
  obtain ⟨hL, hN, hD⟩ := hloc O K ι P hP.multiProj c x hx hxP W hW hWrel
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have he : ∀ f, f ∉ P → algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
      (Ideal.Quotient.mk P f) ≠ 0 := fun f hf h0 => hf (by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P)) (h0.trans (map_zero _).symm))
  have he0 : ∀ f, f ∈ P → algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
      (Ideal.Quotient.mk P f) = 0 := fun f hf => by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hWrel N
  have hh0 := he (powMonomial N i) fun hm => hi (hPW hm)
  let a : J → homLocRing P W := fun k =>
    ⟨algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)) /
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (powMonomial N i)),
      Subring.subset_closure ⟨N, u k, powMonomial N i, hu k, isMultiHomog_powMonomial N i, hi, rfl⟩⟩
  have hI : Ideal.span (Set.range a) ≠ ⊥ := by
    intro hb
    have h1 : a j₀ ∈ Ideal.span (Set.range a) := Ideal.subset_span ⟨j₀, rfl⟩
    rw [hb, Ideal.mem_bot] at h1
    exact div_ne_zero (he _ hj₀) hh0 (congrArg Subtype.val h1)

  have hle : ∀ f ∈ blowUpOverLoc P W u, f ∈ blowUpColon (FractionRing (MRing ι O ⧸ P)) (Ideal.span (Set.range a)) := by
    intro f hf
    refine hcolon (homLocRing P W) _ J a f fun k hk => ?_
    have huk : u k ∉ P := fun hm => hk (by
      show algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)) / _ = 0
      rw [he0 _ hm, zero_div])
    refine (Subring.closure_le (t := (Algebra.adjoin (homLocRing P W) _).toSubring)).mpr
      (Set.union_subset ?_ ?_) (hchart O K ι J P W hP.multiProj.multiHomog hWp hPW hWrel N u hu k huk hf)
    · intro z hz
      exact Subalgebra.algebraMap_mem _ (⟨z, hz⟩ : homLocRing P W)
    · rintro _ ⟨l, rfl⟩
      refine Algebra.subset_adjoin ⟨l, ?_⟩
      exact div_div_div_cancel_right₀ hh0
        (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u l)))
        (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)))
  have := hN
  exact finite_finrank_one_of_le_blowUpColon (homLocRing P W) (blowUpOverLoc P W u)
    (homLocRing_le_blowUpOverLoc P W u) _ hI
    (hfin (homLocRing P W) _ (fun _ _ h => Subtype.ext h) hD _ hI) hle

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PChartsInColon
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

open scoped Pointwise

section

variable {A : Type*} [CommRing A] {L : Type*} [Field L] [Algebra A L]

theorem ChartsInColon.prod_mem_pow {ι : Type*} (M : Submodule A L) (s : Finset ι) (x : ι → L)
    (hx : ∀ i ∈ s, x i ∈ M) : ∏ i ∈ s, x i ∈ M ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Submodule.one_le.mp (le_refl (1 : Submodule A L))
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ']
    exact Submodule.mul_mem_mul (hx i (Finset.mem_insert_self i s))
      (ih fun k hk => hx k (Finset.mem_insert_of_mem hk))

theorem ChartsInColon.exists_mul_pow_mem {J : Type*} (a : J → A) (j : J) (hj : algebraMap A L (a j) ≠ 0)
    {g : L} (hg : g ∈ Algebra.adjoin A (Set.range fun k => algebraMap A L (a k) / algebraMap A L (a j))) :
    ∃ m : ℕ, g * algebraMap A L (a j) ^ m ∈
      (Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a))) ^ m := by
  set I := Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a)) with hI
  have hmem : ∀ k, algebraMap A L (a k) ∈ I := fun k =>
    Submodule.mem_map_of_mem (f := Algebra.linearMap A L) (Ideal.subset_span ⟨k, rfl⟩)
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine ⟨1, ?_⟩
    simpa only [pow_one, div_mul_cancel₀ _ hj] using hmem k
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, pow_zero, mul_one]; exact Submodule.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h1 := Submodule.mul_mem_mul hm (Submodule.pow_mem_pow I (hmem j) n)
    have h2 := Submodule.mul_mem_mul hn (Submodule.pow_mem_pow I (hmem j) m)
    rw [← pow_add] at h1 h2
    rw [add_comm n m] at h2
    convert add_mem h1 h2 using 1
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h := Submodule.mul_mem_mul hm hn
    rw [← pow_add] at h
    convert h using 1
    ring

end

theorem ChartsInColon.proof : ChartsInColon.Statement.{u} := by
  classical
  intro A _ L _ _ J _ a f hf
  unfold blowUpColon
  set b : J → L := fun k => algebraMap A L (a k) with hb
  set I := Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a)) with hI
  have hIspan : I = Submodule.span A (Set.range b) := by
    rw [hI, Ideal.span, Submodule.map_span, ← Set.range_comp]
    rfl
  have hmem : ∀ k, b k ∈ I := fun k =>
    Submodule.mem_map_of_mem (f := Algebra.linearMap A L) (Ideal.subset_span ⟨k, rfl⟩)
  have hex : ∀ j, ∃ m : ℕ, b j ≠ 0 → f * b j ^ m ∈ I ^ m := by
    intro j
    by_cases hj : b j = 0
    · exact ⟨0, fun h => (h hj).elim⟩
    · obtain ⟨m, hm⟩ := ChartsInColon.exists_mul_pow_mem a j hj (hf j hj)
      exact ⟨m, fun _ => hm⟩
  choose m hm using hex
  set M := ∑ j, m j with hM
  refine Submodule.mem_iSup_of_mem (Fintype.card J * M + 1) ?_
  rw [Submodule.mem_div_iff_forall_mul_mem]
  intro y hy
  rw [hIspan, Submodule.span_pow] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := Set.mem_pow.mp hx
    choose k hk using fun i => (g i).2
    have hx' : (List.ofFn fun i => (g i : L)).prod = ∏ i, b (k i) := by
      rw [List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => (hk i).symm
    rw [hx']
    obtain ⟨j, hj⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := k) (n := M)
      (by rw [Fintype.card_fin]; omega)
    set s := Finset.univ.filter fun i => k i = j with hs
    set t := Finset.univ.filter fun i => ¬ k i = j with ht
    have hsplit : ∏ i, b (k i) = b j ^ s.card * ∏ i ∈ t, b (k i) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => k i = j), ← Finset.prod_const]
      congr 1
      exact Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
    have hcard : s.card + t.card = Fintype.card J * M + 1 := by
      rw [hs, ht, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
    have ht' : ∏ i ∈ t, b (k i) ∈ I ^ t.card :=
      ChartsInColon.prod_mem_pow I t _ fun i _ => hmem (k i)
    rw [hsplit]
    by_cases hbj : b j = 0
    · rw [hbj, zero_pow (by omega), zero_mul, mul_zero]
      exact zero_mem _
    · have hmj : m j ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have h1 := Submodule.mul_mem_mul
        (Submodule.mul_mem_mul (hm j hbj) (Submodule.pow_mem_pow I (hmem j) (s.card - m j))) ht'
      rw [← pow_add, ← pow_add, Nat.add_sub_cancel' (by omega), hcard] at h1
      convert h1 using 1
      have hc : s.card - m j + m j = s.card := Nat.sub_add_cancel (by omega)
      conv_lhs => rw [← hc, pow_add]
      ring
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivFibreVariety
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalDivisorFibreVariety.proof : VerticalDivisorFibreVariety.Statement := by
  intro O _ _ _ K _ ι _ P d hP b f g hV W hW
  exact VerticalDivisorSupportFibre.proof O K ι P d hP b f g hV W (Finsupp.mem_support_iff.mp hW)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

