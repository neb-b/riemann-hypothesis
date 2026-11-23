module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CorestrictionCyclotomicShapiroNormalisedTrace
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateModularFamilyAlongSeparatingFamily
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem conj_family_sep : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → (∀ i j, t i = t j → F i = F j) → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  intro g ι _ act act' m k N t t' F hN hA hA' ht ht' hF htF hc hq
  classical

  have key : ∀ i j, t i = t j ↔ t' i = t' j := by
    intro i j
    obtain ⟨a, ha, ha'⟩ := hc i
    obtain ⟨b, hb, hb'⟩ := hc j
    constructor
    · intro h
      have hab : a = b := HasQ.coeff_unique hN ha (h ▸ hb)
      subst hab
      exact HasQ.fun_unique ha' hb'
    · intro h
      have hab : (fun n => g (a n)) = fun n => g (b n) := HasQ.coeff_unique hN ha' (h ▸ hb')
      have : a = b := funext fun n => g.injective (congrFun hab n)
      subst this
      exact HasQ.fun_unique ha hb
  let s : Setoid ι := Setoid.ker t
  let κ := Quotient s
  have hs : ∀ i j, (Quotient.mk s i = Quotient.mk s j) ↔ t i = t j := fun i j =>
    ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  haveI : Fintype κ := Fintype.ofFinite κ
  let actκ : κ → SL(2, ℤ) → κ := fun c γ =>
    Quotient.lift (fun i => Quotient.mk s (act i γ)) (fun i j (h : t i = t j) => by
      apply (hs _ _).2
      rw [← ht i γ, ← ht j γ, h]) c
  let actκ' : κ → SL(2, ℤ) → κ := fun c γ =>
    Quotient.lift (fun i => Quotient.mk s (act' i γ)) (fun i j (h : t i = t j) => by
      apply (hs _ _).2
      rw [key, ← ht' i γ, ← ht' j γ, (key i j).1 h]) c
  let tκ : κ → ℍ → ℂ := fun c => Quotient.lift t (fun i j (h : t i = t j) => h) c
  let tκ' : κ → ℍ → ℂ := fun c => Quotient.lift t' (fun i j (h : t i = t j) => (key i j).1 h) c
  let Fκ : κ → ℍ → ℂ := fun c => Quotient.lift F (fun i j (h : t i = t j) => htF i j h) c
  have bij : ∀ (a : ι → SL(2, ℤ) → ι) (aκ : κ → SL(2, ℤ) → κ), ActBij a →
      (∀ i γ, aκ (Quotient.mk s i) γ = Quotient.mk s (a i γ)) → ActBij aκ := by
    intro a aκ hB hcomp γ
    rw [← Finite.surjective_iff_bijective]
    intro c
    induction c using Quotient.inductionOn with
    | h i =>
      obtain ⟨j, hj⟩ := (hB γ).2 i
      exact ⟨Quotient.mk s j, by simp only [hcomp, hj]⟩
  have hAκ : ActBij actκ := bij act actκ hA (fun _ _ => rfl)
  have hAκ' : ActBij actκ' := bij act' actκ' hA' (fun _ _ => rfl)
  have htκ : IsFam actκ m tκ := by
    intro c γ
    induction c using Quotient.inductionOn with
    | h i => exact ht i γ
  have htκ' : IsFam actκ' m tκ' := by
    intro c γ
    induction c using Quotient.inductionOn with
    | h i => exact ht' i γ
  have hFκ : IsFam actκ k Fκ := by
    intro c γ
    induction c using Quotient.inductionOn with
    | h i => exact hF i γ
  have hinj : Function.Injective tκ := by
    intro c d h
    induction c using Quotient.inductionOn with
    | h i =>
      induction d using Quotient.inductionOn with
      | h j => exact (hs i j).2 h
  have hcκ : ∀ c, QConj g N (tκ c) (tκ' c) := by
    intro c
    induction c using Quotient.inductionOn with
    | h i => exact hc i
  have hqκ : ∀ c, ∃ a, HasQ N (Fκ c) a := by
    intro c
    induction c using Quotient.inductionOn with
    | h i => exact hq i
  obtain ⟨G, hG, hGc⟩ := _root_.GlobalTheory.FN.Lag.conj_family_of_injective g κ actκ actκ' m k N tκ tκ' Fκ hN hAκ hAκ' htκ htκ' hFκ hinj hcκ hqκ
  refine ⟨fun i => G (Quotient.mk s i), ?_, fun i => hGc (Quotient.mk s i)⟩
  intro i γ
  exact hG (Quotient.mk s i) γ

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CorestrictionCyclotomicShapiroNormalisedTraceStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corestriction_cyclotomic_shapiro_normalisedTrace : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits →
  ∀ (L n m : ℕ), 1 ≤ m → m ≤ n → n ≤ L → ∀ χ : (Ω ≃ₐ[ℚ] Ω) → (ZMod (p ^ L))ˣ, (∀ s, s (zt ε p L) = zt ε p L ^ (χ s : ZMod (p ^ L)).val) →
  ∀ z : (Ω ≃ₐ[ℚ] Ω) → (ZMod (p ^ L))ˣ → ℚ → Ω, (∀ s x r, z s x r ∈ A) →
  (∀ s t, Stab A s → Stab A t → ∀ x r, CgA A p n (z (s * t) x r) (z s x r + s (z t (x * (χ s)⁻¹) r))) →
  ∀ ξ F : ℚ → Ω, (∀ r, ξ r ∈ A ∧ InZl ε p L (F r)) →
  (∀ s, Stab A s → (∀ x ∈ A, A.valuation (s x - x) < 1) → χ s = 1 → ∀ tt : ZMod (p ^ n), s (zt ε p (L + n)) = zt ε p n ^ tt.val * zt ε p (L + n) →
    ∀ r, CgA A p n (z s 1 r) (s (ξ r) - ξ r + F r * (tt.val : Ω))) →
  ∀ F' : ℚ → Ω, (∀ r, IsNT ε p L m (F r) (F' r)) →
  ∃ ξ' : ℚ → Ω, (∀ r, ξ' r ∈ A) ∧ ∀ s, Stab A s → (∀ x ∈ A, A.valuation (s x - x) < 1) → s (zt ε p m) = zt ε p m → ∀ tt : ZMod (p ^ n), IsLamG ε p n m s tt →
    ∀ r, CgA A p n ((p : Ω) ^ c * ∑ x ∈ Finset.univ.filter (fun x : (ZMod (p ^ L))ˣ => (x : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), z s x r)
      (s (ξ' r) - ξ' r + (p : Ω) ^ c * (F' r * (tt.val : Ω))) := by
  first | (exact @GlobalTheory.Glue.CorShap.cores_law) | (exact GlobalTheory.Glue.CorShap.cores_law) | (intros; apply GlobalTheory.Glue.CorShap.cores_law  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffConjOfQExpansionConj
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exp_conj : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω →+* Ω) (g : ℂ ≃+* ℂ) (N w : ℕ) (f f' : ℍ → ℂ)
    (h h' : HahnSeries ℚ Ω), (∀ x, g (ε x) = ε (s x)) → 0 < N →
    QAll (· ∈ ε.range) N (fun τ => DD τ ^ w * f τ) →
    QConj g N (fun τ => DD τ ^ w * f τ) (fun τ => DD τ ^ w * f' τ) →
    IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s g N w f f' h h' hg hN hA hC hf hf' r
  obtain ⟨a, ha, haE⟩ := hA
  obtain ⟨c, hc, hc'⟩ := hC
  have hac : a = c := HasQ.coeff_unique hN ha hc
  subst hac
  choose b hb using fun n => RingHom.mem_range.mp (haE n)
  have ha' : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (b n)) := by
    have e : (fun n => ε (b n)) = a := funext hb
    rw [e]; exact ha
  have hc2 : HasQ N (fun τ => DD τ ^ w * f' τ) (fun n => ε (s (b n))) := by
    have e : (fun n => ε (s (b n))) = fun n => g (a n) := funext fun n => by rw [← hg, hb]
    rw [e]; exact hc'
  obtain ⟨H, hH, hHk, hH0⟩ := _root_.GlobalTheory.fn_hahnSeries_of_hasQ Ω ε N _ b hN ha'
  obtain ⟨H', hH', hHk', hH0'⟩ := _root_.GlobalTheory.fn_hahnSeries_of_hasQ Ω ε N _ (fun n => s (b n)) hN hc2
  obtain ⟨hD, hDe, hD0, -, hDZ⟩ := _root_.GlobalTheory.FNExpD.expD Ω ε
  obtain ⟨hops, huniq, -, -, -⟩ := _root_.GlobalTheory.FNExp.exp_props Ω ε
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.FNTwist.exists_scale_twist_ringHom Ω Ω s 1 (fun _ => 1) one_pos rfl (fun _ _ => (one_mul 1).symm)
  have hΦc : ∀ x r, (Φ x).coeff r = s (x.coeff r) := fun x r => by simpa using hΦ x r
  have hpow : ∀ (u : ℍ → ℂ) (k : HahnSeries ℚ Ω), IsExp ε u k → ∀ m : ℕ,
      IsExp ε (fun τ => DD τ ^ m * u τ) (hD ^ m * k) := by
    intro u k hu m
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      have hm := (hops _ _ _ _ hDe ih).2.2
      have e1 : (fun τ => DD τ ^ (m + 1) * u τ) = DD * fun τ => DD τ ^ m * u τ := by
        funext τ; simp only [Pi.mul_apply, pow_succ]; ring
      have e2 : hD ^ (m + 1) * k = hD * (hD ^ m * k) := by ring
      rw [e1, e2]; exact hm
  have e1 : hD ^ w * h = H := huniq _ _ _ (hpow f h hf w) hH
  have e2 : hD ^ w * h' = H' := huniq _ _ _ (hpow f' h' hf' w) hH'
  have hΦD : Φ hD = hD := by
    ext r; rw [hΦc]; obtain ⟨n, hn⟩ := hDZ r; rw [hn, map_intCast]
  have hΦH : Φ H = H' := by
    ext r; rw [hΦc]
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr; rw [hHk, hHk']
    · push_neg at hr; rw [hH0 r hr, hH0' r hr, map_zero]
  have key : hD ^ w * Φ h = hD ^ w * h' := by
    rw [e2, ← hΦH, ← e1, map_mul, map_pow, hΦD]
  have hne : hD ^ w ≠ 0 := pow_ne_zero _ hD0
  have hh := mul_left_cancel₀ hne key
  rw [← hh, hΦc]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffMemFinitelyGeneratedSubring
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem coeff_fg : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ) (h : HahnSeries ℚ Ω),
    InR ε.range f → IsExp ε f h → ∃ S : Finset Ω, ∀ r, h.coeff r ∈ Subring.closure (S : Set Ω) := by
  intro Ω _ ε f h hf hh
  obtain ⟨N, w, hN, hLv⟩ := hf
  obtain ⟨b, hb, hbE⟩ := hLv.2 1
  have hb' : HasQ N (fun τ => DD τ ^ w * f τ) b := by
    simpa only [one_smul] using hb
  choose a ha using fun n => (hbE n : b n ∈ ε.range)
  have hb'' : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (a n)) := by
    have : (fun n => ε (a n)) = b := funext ha
    rw [this]; exact hb'
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.FN.qcoeff_finitelyGenerated Ω ε N w f a hN hLv hb''
  obtain ⟨H, hH, hHa, hH0⟩ := _root_.GlobalTheory.fn_hahnSeries_of_hasQ Ω ε N (fun τ => DD τ ^ w * f τ) a hN hb''
  obtain ⟨hD, hDe, hD0, hDl, hDz⟩ := _root_.GlobalTheory.FNExpD.expD Ω ε
  obtain ⟨hops, huniq, hC, -, -⟩ := _root_.GlobalTheory.FNExp.exp_props Ω ε
  obtain ⟨hmul, hinv⟩ := _root_.GlobalTheory.HahnSub.coeff_mul_inv_mem Ω (Subring.closure (S : Set Ω))
  set A := Subring.closure (S : Set Ω)

  have hpow : ∀ k : ℕ, IsExp ε (fun τ => DD τ ^ k) (hD ^ k) := by
    intro k
    induction k with
    | zero =>
      have := hC 1
      simpa [map_one] using this
    | succ k ih =>
      have e : (fun τ => DD τ ^ (k + 1)) = (fun τ => DD τ ^ k) * DD := by
        funext τ; simp [pow_succ]
      rw [e, pow_succ]
      exact (hops _ _ _ _ ih hDe).2.2
  have hprod : IsExp ε (fun τ => DD τ ^ w * f τ) (hD ^ w * h) := (hops _ _ _ _ (hpow w) hh).2.2
  have hEq : hD ^ w * h = H := huniq _ _ _ hprod hH
  have hDw0 : hD ^ w ≠ 0 := pow_ne_zero _ hD0
  have hEq' : h = H * (hD⁻¹) ^ w := by
    rw [← hEq, inv_pow, mul_comm (hD ^ w) h, mul_assoc, mul_inv_cancel₀ hDw0, mul_one]

  have hHA : ∀ r, H.coeff r ∈ A := by
    intro r
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr
      rw [hHa k]; exact hS k
    · push_neg at hr
      rw [hH0 r hr]; exact A.zero_mem
  have hDA : ∀ r, hD.coeff r ∈ A := by
    intro r
    obtain ⟨n, hn⟩ := hDz r
    rw [hn]; exact intCast_mem A n
  have hDiA : ∀ r, (hD⁻¹).coeff r ∈ A := hinv hD hDA (by rw [hDl, inv_one]; exact A.one_mem)
  have hpA : ∀ k : ℕ, ∀ r, ((hD⁻¹) ^ k).coeff r ∈ A := by
    intro k
    induction k with
    | zero =>
      intro r
      rw [pow_zero]
      by_cases hr : r = 0
      · subst hr; simpa using A.one_mem
      · simpa [hr] using A.zero_mem
    | succ k ih =>
      intro r
      rw [pow_succ]
      exact hmul _ _ ih hDiA r
  refine ⟨S, fun r => ?_⟩
  rw [hEq']
  exact hmul _ _ hHA (hpA w) r

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionAtInfinityOfSomeLevel
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_isExp : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ), InR ε.range f →
    ∃ h : HahnSeries ℚ Ω, IsExp ε f h := by
  intro Ω _ ε f hf
  obtain ⟨N, w, hN, -, hq⟩ := hf
  obtain ⟨a, ha, hmem⟩ := hq 1
  choose b hb using fun n => (hmem n : a n ∈ ε.range)
  have hg : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (b n)) := by
    intro τ
    have := ha τ
    simp only [one_smul] at this
    simpa only [hb] using this
  obtain ⟨hg', hexg, -, -⟩ := _root_.GlobalTheory.fn_hahnSeries_of_hasQ Ω ε N _ b hN hg
  obtain ⟨hD, hexD, hD0, -, -⟩ := _root_.GlobalTheory.FNExpD.expD Ω ε
  obtain ⟨hring, -, hconst, -, hinv⟩ := _root_.GlobalTheory.FNExp.exp_props Ω ε
  have hDi := hinv DD hD hD0 hexD
  have hpow : ∀ k : ℕ, IsExp ε (DD⁻¹ ^ k) (hD⁻¹ ^ k) := by
    intro k
    induction k with
    | zero =>
      have := hconst 1
      simp only [map_one, HahnSeries.C_one] at this
      rw [pow_zero, pow_zero]
      exact this
    | succ k ih =>
      simpa [pow_succ] using (hring _ _ _ _ ih hDi).2.2
  have hprod := (hring _ _ _ _ hexg (hpow w)).2.2
  refine ⟨hg' * hD⁻¹ ^ w, ?_⟩
  convert hprod using 1
  funext τ
  have := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply]
  rw [inv_pow, mul_comm (DD τ ^ w), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ this), mul_one]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJInvariantInModularFunctionFractionField
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem j_in_frac : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), ∃ a : GlobalTheory.FN.ring ε.range, (a : ℍ → ℂ) = jT ∧ (∀ γ : SL(2, ℤ), T.sl (ofSL γ) (T.io a) = T.io a) ∧ (T.exp (T.io a)).coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → (T.exp (T.io a)).coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, (T.exp (T.io a)).coeff r = n := by
  intro Ω _ _ _ ε T
  have hlv := (_root_.GlobalTheory.FN.jT_level_one ε.range).1
  let a : GlobalTheory.FN.ring ε.range := ⟨jT, mem_ring_of_inR ⟨1, 1, one_pos, hlv⟩⟩
  have ha : (a : ℍ → ℂ) = jT := rfl
  obtain ⟨h, hexp, h1, h2, h3⟩ := _root_.GlobalTheory.FNExpJ.expansion_j Ω ε
  have heq : T.exp (T.io a) = h :=
    (_root_.GlobalTheory.FNExp.exp_props Ω ε).2.1 jT _ _ (T.exp_io a) hexp
  refine ⟨a, ha, fun γ => ?_, ?_, ?_, ?_⟩
  · apply T.sl_io
    rw [ha, (_root_.GlobalTheory.FN.cmp_props).2.2.1 γ jT]
    funext τ
    exact ((_root_.GlobalTheory.FN.jT_level_one ε.range).2 γ τ).symm
  · rw [heq]; exact h1
  · rw [heq]; exact h2
  · rw [heq]; exact h3

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCompGLTwoPosRatFun
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem cmp_mem_ring (E : Subring ℂ) (g : GQ)
    (hE : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) {f : ℍ → ℂ} (hf : f ∈ ring E) :
    cmp g f ∈ ring E :=
  ((_root_.GlobalTheory.FN.mem_ring_iff_inR E).1 _).2 (_root_.GlobalTheory.FN.inR_cmp E g f hE (((_root_.GlobalTheory.FN.mem_ring_iff_inR E).1 f).1 hf))

noncomputable def cmpHom (E : Subring ℂ) (g : GQ)
    (hE : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) : ring E →+* ring E where
  toFun a := ⟨cmp g a, cmp_mem_ring E g hE a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem cmp_cmp_inv (g : GQ) (f : ℍ → ℂ) : cmp g (cmp g⁻¹ f) = f := by
  rw [← _root_.GlobalTheory.FN.cmp_props.2.1, inv_mul_cancel, _root_.GlobalTheory.FN.cmp_props.1]

theorem cmp_inv_cmp (g : GQ) (f : ℍ → ℂ) : cmp g⁻¹ (cmp g f) = f := by
  rw [← _root_.GlobalTheory.FN.cmp_props.2.1, mul_inv_cancel, _root_.GlobalTheory.FN.cmp_props.1]

theorem cmp_ringEquiv : ∀ (E : Subring ℂ) (g : GQ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) →
    ∃ σ : GlobalTheory.FN.ring E ≃+* GlobalTheory.FN.ring E, ∀ a, ((σ a : GlobalTheory.FN.ring E) : ℍ → ℂ) = GlobalTheory.FN.cmp g a := by
  intro E g hE
  refine ⟨{ cmpHom E g hE with
    invFun := cmpHom E g⁻¹ hE
    left_inv := fun a => Subtype.ext (cmp_inv_cmp g a)
    right_inv := fun a => Subtype.ext (cmp_cmp_inv g a) }, fun a => rfl⟩

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationAlmostEtaleTowerFixerStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_almostEtale_towerFixer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω), ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ GlobalTheory.K5.IsInt (p := p) x) ∧ (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 ∧ ∀ S : Finset Ω, ∃ U : Subgroup ↥(⨅ n, Gn T n), U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix Ω U) ∧ AlmostSep v U := by
  first | exact @GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep | exact GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep | (intros; apply GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExistsGammaLevel
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem sl_ofSL_io_of_gamma {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Frac Ω ε) (a : ring ε.range) (M : ℕ)
    (ha : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, (a : ℍ → ℂ) (γ • τ) = (a : ℍ → ℂ) τ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma M) : T.sl (ofSL γ) (T.io a) = T.io a := by
  apply T.sl_io
  rw [_root_.GlobalTheory.FN.cmp_props.2.2.1 γ a]
  funext τ
  exact (ha γ hγ τ).symm

theorem frac_exists_level (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K) :
    ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f := by
  obtain ⟨a, b, hb, hf⟩ := T.io_surj f
  obtain ⟨N₁, w₁, hN₁, h₁⟩ := ((_root_.GlobalTheory.FN.mem_ring_iff_inR ε.range).1 a).1 a.2
  obtain ⟨N₂, w₂, hN₂, h₂⟩ := ((_root_.GlobalTheory.FN.mem_ring_iff_inR ε.range).1 b).1 b.2
  have hM : 0 < N₁ * N₂ := Nat.mul_pos hN₁ hN₂
  have h₁' := _root_.GlobalTheory.FN.lv_mono ε.range N₁ (N₁ * N₂) w₁ w₁ a hM (dvd_mul_right _ _) le_rfl h₁
  have h₂' := _root_.GlobalTheory.FN.lv_mono ε.range N₂ (N₁ * N₂) w₂ w₂ b hM (dvd_mul_left _ _) le_rfl h₂
  refine ⟨N₁ * N₂, hM, fun γ hγ => ?_⟩
  have ea := sl_ofSL_io_of_gamma T a _ h₁'.1 γ hγ
  have eb := sl_ofSL_io_of_gamma T b _ h₂'.1 γ hγ
  have hib : T.io b ≠ 0 := by
    intro h
    apply hb
    apply T.io_inj
    rw [h, map_zero]
  have key : T.sl (ofSL γ) f * T.io b = f * T.io b := by
    have := congrArg (T.sl (ofSL γ)) hf
    rw [map_mul, eb, ea] at this
    rw [this, hf]
  exact mul_right_cancel₀ hib key

end GlobalTheory.FN
end

