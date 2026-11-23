module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.PlaceOfLetterInjective
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordLargeSizeNumericalBounds
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem alternatingWord_numerical_bounds :
    ∀ (l : ℕ) (B η S M b : ℝ), 11 ≤ l → 100 ≤ B → 0 ≤ η → 0 ≤ S → 2 * η + S ≤ B / 10 →
      |M - B| ≤ η → |b - B| ≤ η → (M + S) / 2 ≤ b ∧
      2 * ((M + S + η) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + (Real.logb l (2 * (M + S + η)) + 1))
        + η + 1 ≤ b := by
  intro l B η S M b hl hB hη hS hBS hM hb
  have hl' : (11:ℝ) ≤ l := by exact_mod_cast hl
  rw [abs_le] at hM hb
  obtain ⟨hM1, hM2⟩ := hM
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨by linarith, ?_⟩
  have hx1 : M + S + η ≤ 11/10 * B := by linarith
  have hx0 : 100 ≤ M + S + η := by linarith
  have hfrac : (2 * (l:ℝ) - 1) / ((l:ℝ) - 1) ^ 2 ≤ 21/100 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have hfrac0 : 0 ≤ (2 * (l:ℝ) - 1) / ((l:ℝ) - 1) ^ 2 :=
    div_nonneg (by linarith) (sq_nonneg _)
  have h1 : (M + S + η) * (2 * (l:ℝ) - 1) / ((l:ℝ) - 1) ^ 2 ≤ 231/1000 * B := by
    rw [mul_div_assoc]
    nlinarith [mul_le_mul_of_nonneg_left hfrac (show 0 ≤ M + S + η by linarith),
      mul_le_mul_of_nonneg_right hx1 hfrac0]
  have hlogl : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlog100 : Real.log 100 < 5 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have he : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc (100:ℝ) < 2.7182818283 ^ 5 := by norm_num
      _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h.le 5
  have hlogy : Real.log (2 * (M + S + η)) ≤ 2 * (M + S + η) / 100 - 1 + Real.log 100 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 * (M + S + η) / 100 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at this
    linarith
  have hlogb : Real.logb l (2 * (M + S + η)) ≤ 2 * (M + S + η) / 100 + 4 := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    have : 0 ≤ Real.log (2 * (M + S + η)) := Real.log_nonneg (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hlogl (show 0 ≤ 2 * (M + S + η) / 100 + 4 by linarith)]
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostOneThickShortOrbit
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem short_orbit_one_thick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG),
    orderOf φ.2 ≤ 4 * H.Lw → ∀ a b : ZMod (orderOf φ), Thick H (letter τ φ a) →
      Thick H (letter τ φ b) → plc (letter τ φ a) = plc (letter τ φ b) := by
  intro R H τ φ hord a b ha hb
  have key : ∀ g : R.GG, Thick H g → ∃ s ∈ H.T2, R.tau2 (R.dig s + H.u0) = plc g := by
    intro g hg
    unfold Thick Host.thickPlaces at hg
    simpa [Finset.mem_image] using hg
  exact UpperTheory.KStar.Words.thick_one_place H.T2 H.second_set_range H.u0 τ φ
    ((Nat.le_of_dvd (orderOf_pos _) (R.toFrame.orderOf_hH_dvd φ.2)).trans hord) a.val b.val (key _ ha) (key _ hb)

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostTwoThickInWindowLongOrbit
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.LongWindow

theorem thick_inTranslate {R : Ranks} (H : Host R) (g : R.GG) (hg : Thick H g) :
    R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv g.2) := by
  unfold Thick Host.thickPlaces at hg
  obtain ⟨s, hs, e⟩ : ∃ s ∈ H.T2, R.tau2 (R.dig s + H.u0) = plc g := by
    simpa [Finset.mem_image] using hg
  refine ⟨s, hs, ?_⟩
  have e2 : (plc g).2 = g.2 := UpperTheory.KStar.Words.placeOf_snd g
  rw [← e2, ← e]
  rfl

theorem letter_snd {fr : Formalism.HC.Frame} (τ φ : fr.GG) (i : ZMod (orderOf φ)) (k : ℕ) :
    fr.iotaInv (letter τ φ (i + k)).2 = fr.iotaInv τ.2 + (((i.val + k : ℕ) : ℤ)) • fr.iotaInv φ.2 := by
  unfold letter
  rw [UpperTheory.KStar.Words.pow_val_add, natCast_zsmul]
  rfl

open Classical in
theorem main : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 4 * H.Lw < orderOf φ.2 →
    WindowTwo (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) H.Lw := by
  intro R H τ φ hord i a b c hab hbc hcL ⟨ha, hb, hc⟩
  have hO := ((R.toFrame.hostThickOrbit H.T2 H.second_set_range H.second_set_no_relation H.u0 (R.iotaInv τ.2) (R.iotaInv φ.2)).1
    (by rw [R.toFrame.addOrderOf_iotaInv]; exact hord) (i.val : ℤ))
  have mem : ∀ k : ℕ, k < H.Lw → Thick H (letter τ φ (i + k)) →
      ((i.val + k : ℕ) : ℤ) ∈ (Finset.Ico (i.val : ℤ) (i.val + H.Lw)).filter
        (fun j : ℤ => R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv τ.2 + j • R.iotaInv φ.2)) := by
    intro k hk ht
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by push_cast; omega, by push_cast; omega⟩, ?_⟩
    rw [← letter_snd]
    exact thick_inTranslate H _ ht
  have hsub : ({((i.val + a : ℕ) : ℤ), ((i.val + b : ℕ) : ℤ), ((i.val + c : ℕ) : ℤ)} : Finset ℤ) ⊆
      (Finset.Ico (i.val : ℤ) (i.val + H.Lw)).filter
        (fun j : ℤ => R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv τ.2 + j • R.iotaInv φ.2)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem a (by omega) ha
    · exact mem b (by omega) hb
    · exact mem c hcL hc
  have h3 : ({((i.val + a : ℕ) : ℤ), ((i.val + b : ℕ) : ℤ), ((i.val + c : ℕ) : ℤ)} : Finset ℤ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · push_cast; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; push_cast; omega
  have := Finset.card_le_card hsub
  omega

end GlobalTheory.HTW.LongWindow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardDecompositionGroupEqLocalDegree
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.DecompCard

theorem card_stabilizer_eq_locDeg : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (v w : HeightOneSpectrum (𝓞 E)), v ∈ placesOver E l → w ∈ placesOver E l →
    Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) = locDeg E w := by
  intro l _ E _ _ _ v w hv hw
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).2 hpz
  have := v.isPrime
  have := w.isPrime
  have hover : ∀ R : HeightOneSpectrum (𝓞 E), R ∈ placesOver E l →
      R.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := fun R hR =>
    (Ideal.liesOver_span_iff R.isPrime.ne_top hpz).mpr (by simpa [placesOver] using hR)
  have := hover v hv
  have := hover w hw
  rw [Ideal.card_stabilizer_eq (G := E ≃ₐ[ℚ] E) (Ideal.span {(l : ℤ)}) v.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) w.asIdeal (E ≃ₐ[ℚ] E),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(l : ℤ)}) w.asIdeal (E ≃ₐ[ℚ] E), locDeg]

end GlobalTheory.DecompCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardSmallTwistedDualJumpsEqRank
section
noncomputable section

namespace GlobalTheory.HTW

open Formalism.BasicNotions Formalism.FrobeniusOrbits

section Count

variable {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool)

def twistedJump (y : ℤ) : ℤ :=
  if s then -(⌊P.e j⌋ + y + ((R.t : ℤ) + 1) / 2) else ⌊P.e j⌋ + y - ((R.t : ℤ) + 1) / 2

theorem twistedDualJumps_eq_hodgeTateJump_images : jT2 P j s =
    (Finset.univ : Finset (Fin (R.k - 1))).val.map (fun i => twistedJump P j s ⌊P.v i⌋) +
      (Finset.univ : Finset (Fin R.m)).val.map (fun i => twistedJump P j s (-⌊P.b i⌋)) := by
  obtain ⟨q, hq⟩ := R.t_odd
  cases s <;>
    simp only [jT2, jW, cloud, lows, twistedJump, Multiset.map_add (f := _), Multiset.map_map,
      Function.comp_def, ↓reduceIte, Bool.false_eq_true] <;>
    congr 1 <;>
    refine Multiset.map_congr rfl fun i _ => ?_ <;>
    omega

theorem twistedJump_low_small (η : ℝ) (h : ∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) (i : Fin R.m) :
    |twistedJump P j s (-⌊P.b i⌋)| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  obtain ⟨zb, hzb⟩ := P.b_int i
  obtain ⟨ze, hze⟩ := P.e_int j
  obtain ⟨q, hq⟩ := R.t_odd
  have hb : ⌊P.b i⌋ = zb := by rw [hzb]; exact Int.floor_intCast zb
  have he : ⌊P.e j⌋ = ze := by rw [hze]; exact Int.floor_intCast ze
  have hr : (((zb - ze : ℤ) : ℝ)) = (((P.b i - P.e j : ℚ) : ℝ)) := by
    rw [hzb, hze]; push_cast; ring
  have hn : (zb - ze).natAbs ≤ ⌊η⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_natAbs, Int.cast_abs, hr]
    exact h i
  have habs : |zb - ze| ≤ (⌊η⌋₊ : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hn
  rw [abs_le] at habs ⊢
  unfold twistedJump
  rw [hb, he]
  cases s <;> simp only [↓reduceIte, Bool.false_eq_true] <;> push_cast <;> constructor <;> omega

theorem twistedJump_cloud_large (n : ℕ) (hv : ∀ i, 0 ≤ P.v i) (h : (n : ℤ) < szT P j s)
    (i : Fin (R.k - 1)) : ¬ |twistedJump P j s ⌊P.v i⌋| ≤ (n : ℤ) := by
  obtain ⟨q, hq⟩ := R.t_odd
  have hV : 0 ≤ ⌊P.v i⌋ := Int.floor_nonneg.mpr (hv i)
  unfold twistedJump
  unfold szT at h
  rw [abs_le]
  cases s <;> simp only [↓reduceIte, Bool.false_eq_true] at h ⊢ <;> omega

end Count

theorem card_small_twistedDualJumps_eq_rank {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (η : ℝ)
    (hv : ∀ i, 0 ≤ P.v i) (hb : ∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η)
    (hs : ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) < szT P j s) :
    ((jT2 P j s).filter fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)).card = R.m := by
  rw [twistedDualJumps_eq_hodgeTateJump_images, Multiset.filter_add, Multiset.card_add]
  have hc : ((Finset.univ : Finset (Fin (R.k - 1))).val.map
      (fun i => twistedJump P j s ⌊P.v i⌋)).filter
        (fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro u hu
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hu
    exact twistedJump_cloud_large P j s _ hv hs i
  have hl : ((Finset.univ : Finset (Fin R.m)).val.map
      (fun i => twistedJump P j s (-⌊P.b i⌋))).filter
        (fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)) =
      (Finset.univ : Finset (Fin R.m)).val.map (fun i => twistedJump P j s (-⌊P.b i⌋)) := by
    rw [Multiset.filter_eq_self]
    intro u hu
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hu
    exact twistedJump_low_small P j s η hb i
  rw [hc, hl]
  simp

end GlobalTheory.HTW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CloudLowJumpsReflectAndCard
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem block_map_reflect (R : Ranks) :
    (block R).map (fun u => (R.t : ℤ) - 1 - u) = block R := by
  have hnd : (block R).Nodup := by
    unfold block
    exact (Multiset.nodup_range R.t).map (fun a b h => by exact_mod_cast h)
  have hmem : ∀ x : ℤ, x ∈ block R ↔ 0 ≤ x ∧ x < R.t := by
    intro x
    unfold block
    simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by positivity, by exact_mod_cast hc⟩
    · rintro ⟨h0, h1⟩
      exact ⟨x.toNat, by omega, by omega⟩
  refine (Multiset.Nodup.ext (hnd.map (fun a b h => by simpa using h)) hnd).2 ?_
  · intro x
    rw [Multiset.mem_map, hmem]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hmem] at hy
      omega
    · rintro ⟨h0, h1⟩
      exact ⟨(R.t : ℤ) - 1 - x, by rw [hmem]; omega, by ring⟩

theorem jR_symm_card {R : Ranks} (P : HCParam R) (j : Fin R.m) :
    jR P j false = (jR P j true).map (fun u => (R.t : ℤ) - 1 - u) ∧ ∀ s, (jW P j s).card = R.r ∧
      (jR P j s).card = R.nV ∧ (jT2 P j s).card = R.r ∧ jT2 P j s ≤ jT1 P j s := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  have hW : ∀ s, (jW P j s).card = R.r := by
    intro s
    have h : (cloud P j + lows P j).card = R.r := by
      simp only [Multiset.card_add, cloud, lows, Multiset.card_map, Finset.card_val,
        Finset.card_univ, Fintype.card_fin, Ranks.r]
      omega
    cases s
    · simp only [jW, Bool.false_eq_true, if_false, Multiset.card_map, h]
    · simp only [jW, if_true, h]
  refine ⟨?_, fun s => ?_⟩
  · simp only [jR, jW, if_true, Bool.false_eq_true, if_false, Multiset.map_add (f := _), block_map_reflect]
  · have hR : (jR P j s).card = R.nV := by
      simp only [jR, Multiset.card_add, hW s, block, Multiset.card_map, Multiset.card_range, Ranks.nV]
    refine ⟨hW s, hR, ?_, ?_⟩
    · simp only [jT2, Multiset.card_map, hW s]
    · unfold jT2 jT1 jR
      exact Multiset.map_le_map (Multiset.le_add_right _ _)

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexConjugationOrbitOneRealPlace
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.ConjWord

theorem cc_comm {fr : Formalism.HC.Frame} (g : fr.GG) : g * fr.cc = fr.cc * g := mul_comm _ _

theorem plc_cc_mul {fr : Formalism.HC.Frame} (g : fr.GG) : plc (fr.cc * g) = plc g := UpperTheory.KStar.Words.placeOf_cc_mul g

theorem conj_word_one_place {fr : Formalism.HC.Frame} (τ : fr.GG) :
    orderOf fr.cc = 2 ∧ ∀ i : ZMod (orderOf fr.cc), plc (letter τ fr.cc i) = plc τ := by
  refine ⟨fr.orderOf_cc, fun i => ?_⟩
  unfold letter
  generalize i.val = k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ fr.cc k, ← mul_assoc, cc_comm, plc_cc_mul, ih]

end GlobalTheory.HTW.ConjWord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersOfAtMostTwoInWindow
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem winClusters_exists_step {n : ℕ} (th : ZMod n → Prop) (j : ℕ) (x : ZMod n) :
    ∃ s : ℕ, s ≤ j ∧ (s = 0 → ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x + q)) ∧ (0 < s → th (x + s)) ∧
      ∀ q : ℕ, 0 < q → q < s → ¬ th (x + q) := by
  classical
  by_cases h : ∃ q : ℕ, 1 ≤ q ∧ q ≤ j ∧ th (x + q)
  · obtain ⟨h1, h2, h3⟩ := Nat.find_spec h
    refine ⟨Nat.find h, h2, fun h0 => absurd h0 (by omega), fun _ => h3, ?_⟩
    intro q hq hqs hth
    exact Nat.find_min h hqs ⟨hq, by omega, hth⟩
  · push_neg at h
    refine ⟨0, Nat.zero_le _, fun _ q hq hqj hth => absurd hth (h q hq hqj), fun h0 => absurd h0 (lt_irrefl 0),
      fun q hq hq0 => absurd hq0 (by omega)⟩

theorem winClusters : ∀ {n : ℕ} (th : ZMod n → Prop) (L j : ℕ), 1 ≤ j → 2 * j + 1 ≤ L → 2 * j < n →
    WindowTwo th L → Clusters th j := by
  intro n th L j _ hL hn hW
  choose sp hsp using winClusters_exists_step th j
  set F : Set (ZMod n) := {x | th x ∧ ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x - q)} with hFdef
  have key : ∀ x1 x2 : ZMod n, x1 ∈ F → x2 ∈ F → ∀ s1 s2 : ℕ, s1 ≤ s2 → s2 ≤ j →
      x1 + s1 = x2 + s2 → x1 = x2 := by
    intro x1 x2 hx1 hx2 s1 s2 hs hs2 he
    rcases Nat.lt_or_ge s1 s2 with hlt | hge
    · exfalso
      apply hx1.2 (s2 - s1) (by omega) (by omega)
      have : x1 - ((s2 - s1 : ℕ) : ZMod n) = x2 := by
        rw [Nat.cast_sub hs]
        linear_combination he
      rw [this]; exact hx2.1
    · have : s1 = s2 := le_antisymm hs hge
      subst this
      exact add_right_cancel he
  have ofCl : ∀ x y : ZMod n, (y = x ∨ y = x + (sp x : ZMod n)) → ∃ s : ℕ, s ≤ j ∧ y = x + s := by
    intro x y h
    rcases h with h | h
    · exact ⟨0, Nat.zero_le _, by simp [h]⟩
    · exact ⟨sp x, (hsp x).1, h⟩
  refine ⟨F, sp, ?_, ?_⟩
  · rintro x ⟨hx, hxF⟩
    obtain ⟨h1, _, h3, h4⟩ := hsp x
    refine ⟨hx, h1, by omega, ?_, h4, hxF⟩
    rcases Nat.eq_zero_or_pos (sp x) with h | h
    · rw [h]; simpa using hx
    · exact h3 h
  · intro y hy
    have ex : ∃ x, x ∈ F ∧ (y = x ∨ y = x + (sp x : ZMod n)) := by
      by_cases hyF : ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (y - q)
      · exact ⟨y, ⟨hy, hyF⟩, Or.inl rfl⟩
      · push_neg at hyF
        obtain ⟨q, hq1, hqj, hq⟩ := hyF
        have hxF : y - (q : ZMod n) ∈ F := by
          refine ⟨hq, ?_⟩
          intro q' hq'1 hq'j hth
          apply hW (y - q - q') 0 q' (q' + q) (by omega) (by omega) (by omega)
          refine ⟨by simpa using hth, ?_, ?_⟩
          · have : y - (q : ZMod n) - q' + (q' : ℕ) = y - q := by ring
            rw [this]; exact hq
          · have : y - (q : ZMod n) - q' + ((q' + q : ℕ) : ZMod n) = y := by push_cast; ring
            rw [this]; exact hy
        have hyx : y - (q : ZMod n) + (q : ZMod n) = y := by ring
        obtain ⟨h1, h2, h3, h4⟩ := hsp (y - q)
        have hspq : sp (y - q) = q := by
          rcases Nat.eq_zero_or_pos (sp (y - q)) with h0 | hpos
          · exact absurd (by rw [hyx]; exact hy) (h2 h0 q hq1 hqj)
          rcases lt_trichotomy (sp (y - q)) q with hlt | heq | hgt
          · exfalso
            apply hW (y - q) 0 (sp (y - q)) q hpos hlt (by omega)
            refine ⟨by simpa using hq, h3 hpos, ?_⟩
            rw [hyx]; exact hy
          · exact heq
          · exact absurd (by rw [hyx]; exact hy) (h4 q (by omega) hgt)
        refine ⟨y - q, hxF, Or.inr ?_⟩
        rw [hspq, hyx]
    obtain ⟨x, hxF, hx⟩ := ex
    refine ⟨x, ⟨hxF, hx⟩, ?_⟩
    rintro z ⟨hzF, hz⟩
    obtain ⟨s1, hs1, e1⟩ := ofCl z y hz
    obtain ⟨s2, hs2, e2⟩ := ofCl x y hx
    rcases le_total s1 s2 with h | h
    · exact key z x hzF hxF s1 s2 h hs2 (e1.symm.trans e2)
    · exact (key x z hxF hzF s2 s1 h hs1 (e2.symm.trans e1)).symm

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostOne
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem noThree_of_atMostOne : ∀ {n : ℕ} (th : ZMod n → Prop), 2 ≤ n → (∀ a b, th a → th b → a = b) → NoThree th ∧ ∃ i, ¬ th i := by
  intro n th hn hone
  have h10 : (1 : ZMod n) ≠ 0 := by
    have : Fact (1 < n) := ⟨by omega⟩
    exact one_ne_zero
  have key : ∀ i : ZMod n, ¬ (th i ∧ th (i + 1)) := by
    rintro i ⟨ha, hb⟩
    exact h10 (by linear_combination (hone _ _ ha hb).symm)
  refine ⟨fun i h => key i ⟨h.1, h.2.1⟩, ?_⟩
  by_cases h0 : th 0
  · exact ⟨0 + 1, fun h1 => key 0 ⟨h0, h1⟩⟩
  · exact ⟨0, h0⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChangeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_param_of_thetaLift_baseChange : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm3 D → SumRepresentations.ArchimedeanSignatureMatching D → SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), thetaOf D.nd D.naut i σ P → IsBCV D.nd D.naut i P Pa → (⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa → ∃ Sig, HasParamW D.nd D.naut i σ Sig ∧ IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) := by
  first | exact @GlobalTheory.RowThetaParam.param_of_theta | exact GlobalTheory.RowThetaParam.param_of_theta | (intros; apply GlobalTheory.RowThetaParam.param_of_theta <;> assumption)
end

