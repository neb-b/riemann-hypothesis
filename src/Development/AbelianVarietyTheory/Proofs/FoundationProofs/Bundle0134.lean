module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0129
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassNotRootsAvoidLe
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem avoid_pow_natDegree_minpoly {g : ℕ} [Fact g.Prime] {x : AlgebraicClosure (ZMod g)} (hx : x ≠ 0) :
    x ^ (g ^ (minpoly (ZMod g) x).natDegree - 1) = 1 := by
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hi
  haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  haveI : Fintype (IntermediateField.adjoin (ZMod g) {x}) := Fintype.ofFinite _
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one y hy
  rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hi] at h1
  simpa [y] using congrArg Subtype.val h1

theorem avoid_card_irreducible_le {g : ℕ} [Fact g.Prime] (c : (ZMod g)ˣ) (d : ℕ) (hd : 1 ≤ d) (h2 : 2 ∣ g - 1) :
    d * ((sqSet g d).filter fun P => Irreducible P ∧ ¬ RootsAvoid g c P).card ≤
      ∑ l ∈ (g ^ d - 1).primeFactors, l ^ padicValNat l (g ^ d - 1) := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hn : 0 < g ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hg)
  have hdv : g - 1 ∣ g ^ d - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 d
  set n := g ^ d - 1 with hndef
  set c' : AlgebraicClosure (ZMod g) := algebraMap (ZMod g) (AlgebraicClosure (ZMod g)) (c : ZMod g) with hc'
  have hc0 : c' ≠ 0 := by simp [hc']
  have hcn : c' ^ n = 1 := by
    obtain ⟨k, hk⟩ := hdv
    rw [hk, pow_mul, hc', ← map_pow, ZMod.pow_card_sub_one_eq_one c.ne_zero, map_one, one_pow]
  have hS := fun l (hl : l ∈ n.primeFactors) =>
    (GlobalTheory.BadShare.samePart_roots_finite_ncard (AlgebraicClosure (ZMod g)) n l hn (Nat.prime_of_mem_primeFactors hl)).2 c'
  let T : Finset (AlgebraicClosure (ZMod g)) :=
    n.primeFactors.attach.biUnion fun l => (hS l.1 l.2).1.toFinset
  have hT : T.card ≤ ∑ l ∈ n.primeFactors, l ^ padicValNat l n := by
    refine Finset.card_biUnion_le.trans ?_
    rw [← Finset.sum_attach n.primeFactors]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Set.ncard_eq_toFinset_card _ (hS l.1 l.2).1]
    exact (hS l.1 l.2).2
  refine le_trans ?_ hT
  set B := (sqSet g d).filter fun P => Irreducible P ∧ ¬ RootsAvoid g c P with hB
  have h1 : ∑ P ∈ B, (T.filter fun x => minpoly (ZMod g) x = P).card ≤ T.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_filter_le _ _
  refine le_trans ?_ h1
  rw [mul_comm, ← smul_eq_mul]
  refine Finset.card_nsmul_le_sum _ _ _ fun P hP => ?_
  obtain ⟨hP1, hirr, hbad⟩ := Finset.mem_filter.1 hP
  obtain ⟨hm, hdeg, -, h0⟩ := mem_sqSet.1 hP1
  rw [rootsAvoid_iff h0] at hbad
  push Not at hbad
  obtain ⟨l, hl, -, x, hx, a, ha⟩ := hbad
  have hmin : ∀ y ∈ P.aroots (AlgebraicClosure (ZMod g)), minpoly (ZMod g) y = P := fun y hy =>
    (minpoly.eq_of_irreducible_of_monic hirr (mem_aroots.1 hy).2 hm).symm
  have hdvd : P ∣ X ^ (l ^ a) - C ((c : ZMod g) ^ (l ^ a)) := by
    rw [← hmin x hx, minpoly.dvd_iff]
    simp [ha, hc']
  have hcard : (P.aroots (AlgebraicClosure (ZMod g))).toFinset.card = d := by
    have hsep : P.Separable := PerfectField.separable_of_irreducible hirr
    have := Polynomial.card_rootSet_eq_natDegree (K := AlgebraicClosure (ZMod g)) hsep (IsAlgClosed.splits _)
    rw [← hdeg, ← this]
    simp only [rootSet, Finset.coe_sort_coe]
    convert (Fintype.card_coe _).symm
  rw [← hcard]
  refine Finset.card_le_card fun y hy => ?_
  rw [Multiset.mem_toFinset] at hy
  have hy0 := root_ne_zero h0 hy
  have hyn : y ^ n = 1 := by
    have := avoid_pow_natDegree_minpoly hy0
    rwa [hmin y hy, hdeg] at this
  have hya : y ^ (l ^ a) = c' ^ (l ^ a) := by
    have h3 : minpoly (ZMod g) y ∣ X ^ (l ^ a) - C ((c : ZMod g) ^ (l ^ a)) := by rwa [hmin y hy]
    rw [minpoly.dvd_iff] at h3
    simpa [sub_eq_zero, hc'] using h3
  refine Finset.mem_filter.2 ⟨?_, hmin y hy⟩
  simp only [T, Finset.mem_biUnion, Finset.mem_attach, true_and, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  by_cases hln : l ∣ n
  · exact ⟨⟨l, Nat.mem_primeFactors.2 ⟨hl, hln, hn.ne'⟩⟩, hyn, (samePart_iff_of_ne_zero hl hy0 hc0).2 ⟨a, hya⟩⟩
  · have : y = c' := eq_of_pow_eq ((hl.coprime_iff_not_dvd.2 hln).symm) hyn hcn hn.ne' hya
    refine ⟨⟨2, Nat.mem_primeFactors.2 ⟨Nat.prime_two, h2.trans hdv, hn.ne'⟩⟩, hyn, ?_⟩
    rw [this]; rfl

theorem avoid_sum_le (g : ℝ) (hg : 2 ≤ g) (N : ℕ) :
    ∑ d ∈ Finset.Icc 2 (N + 1), ((g - 1) / (g ^ d - 1) + 1 / (d * (g - 1))) ≤
      (1 - 1 / g ^ N + Real.log ((N + 1 : ℕ) : ℝ)) / (g - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hg1 : 0 < g - 1 := by linarith
    have hp : 1 ≤ g ^ N := one_le_pow₀ (by linarith)
    have hq : 0 < g ^ (N + 1 + 1) - 1 := by
      have : g ^ (N + 1 + 1) = g ^ N * g * g := by ring
      have h5 : 2 ≤ g ^ N * g := by nlinarith
      rw [this]; nlinarith
    have e1 : (g - 1) / (g ^ (N + 1 + 1) - 1) ≤ 1 / g ^ (N + 1) := by
      rw [div_le_div_iff₀ hq (by positivity)]
      have : g ^ (N + 1 + 1) = g ^ N * g * g := by ring
      rw [this, pow_succ]; nlinarith
    have e2 : 1 / ((N + 1 + 1 : ℕ) : ℝ) ≤ Real.log ((N + 1 + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / ((N + 1 + 1 : ℕ) : ℝ)) (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have h' : ((N + 1 : ℕ) : ℝ) / ((N + 1 + 1 : ℕ) : ℝ) - 1 = - (1 / ((N + 1 + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp; ring
      linarith
    have e3 : 1 / (((N + 1 + 1 : ℕ) : ℝ) * (g - 1)) ≤
        (Real.log ((N + 1 + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ)) / (g - 1) := by
      rw [← div_div]
      exact div_le_div_of_nonneg_right e2 hg1.le
    have e4 : (1 - 1 / g ^ (N + 1) + Real.log ((N + 1 + 1 : ℕ) : ℝ)) / (g - 1) =
        (1 - 1 / g ^ N + Real.log ((N + 1 : ℕ) : ℝ)) / (g - 1) + 1 / g ^ (N + 1) +
        (Real.log ((N + 1 + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ)) / (g - 1) := by
      have : g ≠ 0 := by linarith
      field_simp; ring
    rw [e4]; linarith

theorem avoid_mass_le_sum {g : ℕ} [Fact g.Prime] (c : (ZMod g)ˣ) (N : ℕ) (h2 : 2 ∣ g - 1) :
    (mass g N fun f => ¬ RootsAvoid g c f) ≤ ∑ d ∈ Finset.Icc 1 N,
      (∑ l ∈ (g ^ d - 1).primeFactors, ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) / (d * ((g : ℝ) ^ d - 1)) := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  let B : ℕ → Finset (ZMod g)[X] := fun d => (sqSet g d).filter fun P => Irreducible P ∧ ¬ RootsAvoid g c P
  have hU := (GlobalTheory.BadShare.mass_union_bounds g N).2.2.1
  refine (hU ℕ (Finset.Icc 1 N) _ (fun d f => ∃ P ∈ B d, P ∣ f) ?_).trans (Finset.sum_le_sum fun d hd => ?_)
  · intro f hf hbad
    obtain ⟨hm, hdeg, -, h0⟩ := mem_sqSet.1 hf
    unfold RootsAvoid at hbad
    push Not at hbad
    obtain ⟨l, hl, hlg, x, hx, hs⟩ := hbad
    have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
    have hdvd : minpoly (ZMod g) x ∣ f := minpoly.dvd _ _ (mem_aroots.1 hx).2
    refine ⟨(minpoly (ZMod g) x).natDegree, Finset.mem_Icc.2 ⟨minpoly.natDegree_pos hi,
      hdeg ▸ natDegree_le_of_dvd hdvd hm.ne_zero⟩, minpoly (ZMod g) x, Finset.mem_filter.2 ⟨mem_sqSet.2
        ⟨minpoly.monic hi, rfl, (minpoly.irreducible hi).squarefree,
          minpoly.coeff_zero_ne_zero hi (root_ne_zero h0 hx)⟩, minpoly.irreducible hi, fun h => ?_⟩, hdvd⟩
    exact h l hl hlg x (mem_aroots.2 ⟨minpoly.ne_zero hi, minpoly.aeval _ _⟩) hs
  · have hd1 := (Finset.mem_Icc.1 hd).1
    have hpow : 1 < g ^ d := Nat.one_lt_pow (by omega) hg
    have hq : (0 : ℝ) < (g : ℝ) ^ d - 1 := by
      have : (1 : ℝ) < (g : ℝ) ^ d := by exact_mod_cast hpow
      linarith
    refine (hU _ (B d) _ (fun P f => P ∣ f) fun f _ h => h).trans ?_
    have h3 : ∑ P ∈ B d, mass g N (fun f => P ∣ f) ≤ (B d).card • ((g : ℝ) ^ d - 1)⁻¹ := by
      refine Finset.sum_le_card_nsmul _ _ _ fun P hP => ?_
      obtain ⟨hP1, hirr, -⟩ := Finset.mem_filter.1 hP
      refine ((GlobalTheory.BadShare.divisor_bound g).2 N d P hP1).trans_eq ?_
      rw [torusCard_irreducible hirr, (mem_sqSet.1 hP1).2.1, Nat.cast_sub hpow.le]
      simp
    refine h3.trans ?_
    have h4 : (d : ℝ) * (B d).card ≤ ∑ l ∈ (g ^ d - 1).primeFactors, ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ) := by
      exact_mod_cast avoid_card_irreducible_le c d hd1 h2
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    rw [nsmul_eq_mul, le_div_iff₀ (by positivity)]
    refine le_trans (le_of_eq ?_) h4
    field_simp

theorem mass_not_rootsAvoid_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N q d : ℕ) (c : (ZMod g)ˣ), (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → (mass g N fun f => ¬ RootsAvoid g c f) ≤ 1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1) := by
  rintro g _ N q d c ⟨hq, hd, hq2, hd2, hqd, hmax, hdvd⟩
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have h4 : 4 ∣ g - 1 := Dvd.dvd.trans ⟨4 * q * d, by ring⟩ hdvd
  refine (avoid_mass_le_sum c N (Dvd.dvd.trans (by norm_num) h4)).trans ?_
  cases N with
  | zero => simp only [Nat.cast_zero, Real.log_zero]; simp; positivity
  | succ N =>
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega), Finset.sum_insert (by simp)]
    refine add_le_add ?_ ?_
    · have h := GlobalTheory.BadShare.sum_primePowerParts_le (g - 1) q d (by omega) hq hd hq2 hd2 hqd hmax hdvd
      rw [Nat.cast_sub (by omega)] at h
      simp only [pow_one, Nat.cast_one, one_mul] at h ⊢
      rw [div_le_iff₀ hg1]
      refine h.trans_eq ?_
      ring
    · refine le_trans (Finset.sum_le_sum fun e he => ?_) ((avoid_sum_le g hgR N).trans ?_)
      · have he2 : 2 ≤ e := (Finset.mem_Icc.1 he).1
        have he0 : (0 : ℝ) < e := by exact_mod_cast (by omega : 0 < e)
        have hq : (0 : ℝ) < (g : ℝ) ^ e - 1 := by
          have : (1 : ℝ) < (g : ℝ) ^ e := one_lt_pow₀ (by linarith) (by omega)
          linarith
        rw [div_le_iff₀ (by positivity)]
        refine (GlobalTheory.BadShare.sum_primePowerPart_pow_sub_one_le g e hg h4 he2).trans_eq ?_
        field_simp
      · refine div_le_div_of_nonneg_right ?_ hg1.le
        have : (0 : ℝ) ≤ 1 / (g : ℝ) ^ N := by positivity
        linarith

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionFractionFieldOfQExpansions
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_of_qexp : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) → (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs, HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) → ∃ f : T.K, T.an f = (a : Mero) := by
  intro Ω _ _ _ ε T a M hM _ hinv hexp
  have hHs : ∀ τ : ℍ, (τ : ℂ) ∈ Hs := _root_.GlobalTheory.FN.germ_ringHom_and_restrict.2.2.2.2
  have hmob : ∀ (γ : SL(2, ℤ)) (τ : ℍ), mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := _root_.GlobalTheory.FN.mob_props.2.2.2.1
  set f : ℍ → ℂ := fun τ => a τ with hf
  have hinvf : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ := by
    intro γ hγ τ
    simp only [hf]
    rw [← hmob γ τ]
    exact hinv γ hγ τ (hHs τ)
  have hw : ∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ ε.range) M fun τ => DD τ ^ w * f (γ • τ) := by
    intro γ
    obtain ⟨c, n0, hc0, hs⟩ := hexp γ
    refine (_root_.GlobalTheory.FN.laurent_iff ε.range M (fun τ => f (γ • τ)) hM).2 ⟨fun n => ε (c n), n0, fun n => ⟨c n, rfl⟩, ?_, ?_⟩
    · intro n hn
      simp [hc0 n hn]
    · intro τ
      have := hs τ (hHs τ)
      simp only [hf]
      rw [← hmob γ τ]
      exact this
  obtain ⟨w, hLv⟩ := _root_.GlobalTheory.FN.uniform_pole_order ε.range M f hM hinvf hw
  have hmem : f ∈ ring ε.range := mem_ring_of_inR ⟨M, w, hM, hLv⟩
  refine ⟨T.io ⟨f, hmem⟩, ?_⟩
  rw [T.an_io]
  exact _root_.GlobalTheory.FN.germ_ringHom_and_restrict.2.2.2.1 a

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOver
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.RingMem

theorem inR_const (E : Subring ℂ) (c : ℂ) (hc : c ∈ E) : InR E fun _ => c := by
  refine ⟨1, 0, one_pos, fun _ _ _ => rfl, fun γ => ?_⟩
  have h := GlobalTheory.QFam.QAllSubring.const (R := E) (N := 1) hc
  simpa only [pow_zero, one_mul] using h

theorem lv_lift {E : Subring ℂ} {f : ℍ → ℂ} {N w : ℕ} (N₂ : ℕ) (hN₂ : 0 < N₂) (w' : ℕ) (hw : w ≤ w')
    (hN : 0 < N) (h : Lv E N w f) : Lv E (N * N₂) w' f :=
  _root_.GlobalTheory.FN.lv_mono E N (N * N₂) w w' f (Nat.mul_pos hN hN₂) (dvd_mul_right N N₂) hw h

theorem lv_lift' {E : Subring ℂ} {f : ℍ → ℂ} {N w : ℕ} (N₁ : ℕ) (hN₁ : 0 < N₁) (w' : ℕ) (hw : w ≤ w')
    (hN : 0 < N) (h : Lv E N w f) : Lv E (N₁ * N) w' f :=
  _root_.GlobalTheory.FN.lv_mono E N (N₁ * N) w w' f (Nat.mul_pos hN₁ hN) (dvd_mul_left N N₁) hw h

theorem inR_add {E : Subring ℂ} {f g : ℍ → ℂ} (hf : InR E f) (hg : InR E g) : InR E (f + g) := by
  obtain ⟨N₁, w₁, hN₁, hf⟩ := hf
  obtain ⟨N₂, w₂, hN₂, hg⟩ := hg
  have hf' := lv_lift N₂ hN₂ (max w₁ w₂) (le_max_left _ _) hN₁ hf
  have hg' := lv_lift' N₁ hN₁ (max w₁ w₂) (le_max_right _ _) hN₂ hg
  refine ⟨N₁ * N₂, max w₁ w₂, Nat.mul_pos hN₁ hN₂, fun γ hγ τ => ?_, fun γ => ?_⟩
  · simp only [Pi.add_apply, hf'.1 γ hγ τ, hg'.1 γ hγ τ]
  · have h := GlobalTheory.QFam.QAllSubring.add (hf'.2 γ) (hg'.2 γ)
    refine (congrArg (QAll (· ∈ E) (N₁ * N₂)) (funext fun τ => ?_)).mp h
    simp only [Pi.add_apply]; ring

theorem inR_mul {E : Subring ℂ} {f g : ℍ → ℂ} (hf : InR E f) (hg : InR E g) : InR E (f * g) := by
  obtain ⟨N₁, w₁, hN₁, hf⟩ := hf
  obtain ⟨N₂, w₂, hN₂, hg⟩ := hg
  have hf' := lv_lift N₂ hN₂ w₁ le_rfl hN₁ hf
  have hg' := lv_lift' N₁ hN₁ w₂ le_rfl hN₂ hg
  refine ⟨N₁ * N₂, w₁ + w₂, Nat.mul_pos hN₁ hN₂, fun γ hγ τ => ?_, fun γ => ?_⟩
  · simp only [Pi.mul_apply, hf'.1 γ hγ τ, hg'.1 γ hγ τ]
  · have h := GlobalTheory.QFam.QAllSubring.mul (hf'.2 γ) (hg'.2 γ)
    refine (congrArg (QAll (· ∈ E) (N₁ * N₂)) (funext fun τ => ?_)).mp h
    simp only [Pi.mul_apply]; ring

theorem inR_neg {E : Subring ℂ} {f : ℍ → ℂ} (hf : InR E f) : InR E (-f) := by
  obtain ⟨N, w, hN, hf⟩ := hf
  refine ⟨N, w, hN, fun γ hγ τ => ?_, fun γ => ?_⟩
  · simp only [Pi.neg_apply, hf.1 γ hγ τ]
  · have h := GlobalTheory.QFam.QAllSubring.sub (GlobalTheory.QFam.QAllSubring.const (R := E) (N := N) E.zero_mem) (hf.2 γ)
    refine (congrArg (QAll (· ∈ E) N) (funext fun τ => ?_)).mp h
    simp only [Pi.neg_apply]; ring

def inRSubring (E : Subring ℂ) : Subring (ℍ → ℂ) where
  carrier := {f | InR E f}
  mul_mem' := inR_mul
  one_mem' := inR_const E 1 E.one_mem
  add_mem' := inR_add
  zero_mem' := inR_const E 0 E.zero_mem
  neg_mem' := inR_neg

end GlobalTheory.FN.RingMem

theorem GlobalTheory.FN.mem_ring_iff_inR :
    ∀ E : Subring ℂ, (∀ f : ℍ → ℂ, f ∈ GlobalTheory.FN.ring E ↔ InR E f) ∧ ∀ c ∈ E, InR E fun _ => c := by
  intro E
  refine ⟨fun f => ⟨fun h => ?_, mem_ring_of_inR⟩, fun c hc => GlobalTheory.FN.RingMem.inR_const E c hc⟩
  have hle : GlobalTheory.FN.ring E ≤ GlobalTheory.FN.RingMem.inRSubring E :=
    (Subring.closure_le).mpr fun g hg => hg
  exact hle h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSubfieldOfFixedByGeometricTowerGaloisStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_subfield_of_fixed_by_geometric_tower_galois : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (F : Subfield Ω), (∀ c : O0 p, algebraMap (O0 p) Ω c ∈ F) → (∀ x : Ω, IsAlgZp (p := p) x → x ∈ F) → T.qq n ∈ F → ∀ o : Ω, (∀ g ∈ Ggeo (p := p) Ω ⊓ Gn T n, g o = o) → o ∈ F := by
  intro p hp Ω _ _ hc T n F hO hA hq o ho
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have : IsAlgClosed Ω := hc.clo
  let f : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hO
  let : Algebra (O0 p) F := f.toAlgebra
  have : IsScalarTower (O0 p) F Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hf : Function.Injective (algebraMap (O0 p) F) :=
    fun _ _ h => hc.inj (congrArg Subtype.val h)
  have : Algebra.IsAlgebraic (O0 p) Ω := hc.alg
  have : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.extendScalars (R := O0 p) hf
  have : IsAlgClosure F Ω := ⟨hc.clo, inferInstance⟩
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hζ : IsAlgZp (p := p) (T.ζ n) := by
    refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow_sub_C (1 : ℤ_[p]) (pow_ne_zero _ hp.out.ne_zero)).ne_zero
    · simp [(T.prim n).pow_eq_one]
  have ho' : o ∈ Set.range (algebraMap F Ω) := by
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed o).2 fun σ => ?_
    let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun c => σ.commutes (f c)
    have hg : g ∈ Ggeo (p := p) Ω ⊓ Gn T n := by
      refine ⟨fun x hx => σ.commutes ⟨x, hA x hx⟩, ?_, ?_⟩
      · show g • T.ζ n = T.ζ n
        exact σ.commutes ⟨T.ζ n, hA _ hζ⟩
      · show g • T.qq n = T.qq n
        exact σ.commutes ⟨T.qq n, hq⟩
    exact ho g hg
  obtain ⟨x, rfl⟩ := ho'
  exact x.2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelModularSTransform
section
open Complex
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

noncomputable section

namespace GlobalTheory.Sieg.ThInv

open GlobalTheory.ThetaWeberRoad GlobalTheory.ThetaWeberRoad.OddDeriv

theorem exp_pi_I_half : cexp (π * I / 2) = I := by
  rw [show (π : ℂ) * I / 2 = π / 2 * I by ring, Complex.exp_pi_div_two_mul_I]

theorem oddTheta_eq (τ : ℍ) (z : ℂ) : oddTheta τ z = I * ModularForm.eta (τ : ℂ) * th z τ := by
  have hB := hasProd_tailProd τ (cexp (2 * π * I * z))
  have hC := hasProd_tailProd τ (cexp (-(2 * π * I * z)))
  have hP : ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹) =
      tailProd τ (cexp (2 * π * I * z)) * tailProd τ (cexp (-(2 * π * I * z))) := by
    rw [← (hB.mul hC).tprod_eq]
    refine tprod_congr fun n => ?_
    rw [ModularForm.eta_q_eq_pow, Complex.exp_neg]
    rfl
  have hT1 : tailProd τ 1 = ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) := by
    simp [tailProd]
  have h1 : cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) =
      I * Function.Periodic.qParam 24 (τ : ℂ) * ee ((τ : ℂ) / 12) * ee (z / 2) := by
    rw [Function.Periodic.qParam, ee, ee]
    conv_rhs => rw [← exp_pi_I_half]
    rw [exp_pi_I_half]
    nth_rewrite 3 [← exp_pi_I_half]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  have h2 : ee (-z / 2) = ee (z / 2) * cexp (-(2 * π * I * z)) := by
    rw [ee, ee, ← Complex.exp_add]
    congr 1; ring
  rw [oddTheta, jacobiTheta₂_shift GlobalTheory.JacobiTriple.tripleProduct, th, hP, ModularForm.eta, ← hT1, h1, h2]
  ring

theorem sqrt_eq (τ : ℍ) : (Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h0 : -I * (τ : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ
  have hre : 0 < (-I * (τ : ℂ)).re := by simpa using τ.im_pos
  have ha := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre))
  have hl : log (I * (-I * (τ : ℂ))) = log I + log (-I * (τ : ℂ)) := by
    rw [Complex.log_mul_eq_add_log_iff I_ne_zero h0, Complex.arg_I]
    constructor <;> linarith [ha.1, ha.2, Real.pi_pos]
  rw [show I * (-I * (τ : ℂ)) = τ by linear_combination (-(τ : ℂ)) * I_sq] at hl
  rw [Complex.sqrt, Complex.sqrt, Complex.cpow_def_of_ne_zero I_ne_zero, Complex.cpow_def_of_ne_zero hτ,
    Complex.cpow_def_of_ne_zero h0, hl,
    ← Complex.exp_neg, ← Complex.exp_add]
  congr 1; ring

theorem eta_S (τ : ℍ) :
    ModularForm.eta (-1 / (τ : ℂ)) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ModularForm.eta (τ : ℂ) := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv τ.2
  rw [← sqrt_eq, mul_assoc]
  simpa using h

theorem coe_S_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul]
  simp [neg_div]

theorem oddTheta_S (τ : ℍ) (z : ℂ) :
    oddTheta (ModularGroup.S • τ) (z / (τ : ℂ)) =
      -I * (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ee (z ^ 2 / (2 * (τ : ℂ))) * oddTheta τ z := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h0 : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ h.1
  have hI : -I = cexp (-(π * I / 2)) := by
    rw [Complex.exp_neg, exp_pi_I_half, Complex.inv_I]
  rw [oddTheta, oddTheta, coe_S_smul, jacobiTheta₂_functional_equation (z + ((τ : ℂ) + 1) / 2) τ,
    show z / (τ : ℂ) + (-1 / (τ : ℂ) + 1) / 2 = (z + ((τ : ℂ) + 1) / 2) / τ + -1 / (τ : ℂ) by
      field_simp; ring, jacobiTheta₂_add_left']
  generalize jacobiTheta₂ ((z + ((τ : ℂ) + 1) / 2) / τ) (-1 / (τ : ℂ)) = J
  generalize (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) = s at h0 ⊢
  have hE : ∀ A B C D : ℂ, cexp A * s * cexp B * (cexp C * (1 / s * cexp D * J)) =
      cexp (A + B + C + D) * J := by
    intro A B C D
    simp only [Complex.exp_add]
    field_simp
  rw [ee]
  conv_rhs => rw [hI]
  rw [hE, ← mul_assoc, ← Complex.exp_add]
  congr 2
  field_simp
  ring

theorem th_S : ∀ (τ : ℍ) (z : ℂ), th (z / (τ : ℂ)) (ModularGroup.S • τ) =
    -Complex.I * ee (z ^ 2 / (2 * (τ : ℂ))) * th z τ := by
  intro τ z
  have h := oddTheta_S τ z
  rw [oddTheta_eq, oddTheta_eq] at h
  have hne : I * ModularForm.eta ((ModularGroup.S • τ : ℍ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (ModularForm.eta_ne_zero (ModularGroup.S • τ).2)
  refine mul_left_cancel₀ hne ?_
  rw [h, coe_S_smul, eta_S]
  ring

end GlobalTheory.Sieg.ThInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntTorsionFreeOfCardQuotientPowStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_eq_zero_of_pow_smul_of_card_quotient : ∀ (l : ℕ) [Fact l.Prime] (C : Type) [AddCommGroup C] [Module ℤ_[l] C] [Module.Finite ℤ_[l] C], (∀ r : ℕ, 0 < r → Nat.card (C ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] C ((l : ℤ_[l]) ^ r))) = l ^ r) → ∀ (r : ℕ) (c : C), (l : ℤ_[l]) ^ r • c = 0 → c = 0 := by
  first | exact @GlobalTheory.padicInt_torsionFree_of_card_quotient_pow | exact GlobalTheory.padicInt_torsionFree_of_card_quotient_pow | (intros; apply GlobalTheory.padicInt_torsionFree_of_card_quotient_pow <;> assumption)
end

