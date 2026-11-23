module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Formalism.LocalToGlobal.HermitianColumns.Bundle0004
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdHstar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistCharacterRamifiedAtConductorTrivialAboveL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.WtComb

theorem orderEmb_add_le {n : ℕ} (e : Fin n ↪o ℤ) :
    ∀ (k : ℕ) (a b : Fin n), (b : ℕ) = (a : ℕ) + k → e a + (k : ℤ) ≤ e b := by
  intro k
  induction k with
  | zero =>
    intro a b hb
    have : a = b := Fin.ext (by omega)
    subst this; simp
  | succ k ih =>
    intro a b hb
    have hk : (a : ℕ) + k < n := by have := b.2; omega
    have h1 := ih a ⟨(a : ℕ) + k, hk⟩ rfl
    have h2 : e ⟨(a : ℕ) + k, hk⟩ < e b := e.lt_iff_lt.2 (by rw [Fin.lt_def]; simp; omega)
    push_cast; linarith

theorem exists_domWeight_infOf (n : ℕ) (S : Multiset ℂ) (hc : Multiset.card S = n) (hd : S.Nodup)
    (hm : ∀ x ∈ S, ∃ z : ℤ, x = (z : ℂ) + ((n : ℂ) - 1) / 2) :
    ∃ lam : DomWeight n, NG.infOf lam.w = S := by
  classical
  set c : ℂ := ((n : ℂ) - 1) / 2 with hcdef
  let g : ℂ → ℤ := fun x => if h : ∃ z : ℤ, x = (z : ℂ) + c then h.choose else 0
  have hg : ∀ x ∈ S, x = (g x : ℂ) + c := fun x hx => by
    simp only [g, dif_pos (hm x hx)]; exact (hm x hx).choose_spec
  let M : Multiset ℤ := S.map (fun x => -g x)
  have hMd : M.Nodup := hd.map_on (fun x hx y hy hxy => by
    rw [hg x hx, hg y hy]; simp only [neg_inj] at hxy; rw [hxy])
  let T : Finset ℤ := ⟨M, hMd⟩
  have hT : T.card = n := by simp [T, M, hc]
  let e := T.orderEmbOfFin hT
  refine ⟨⟨fun a => -e a + (a : ℕ), ?_⟩, ?_⟩
  · intro a b hab
    have := orderEmb_add_le e ((b : ℕ) - (a : ℕ)) a b (by rw [Fin.le_def] at hab; omega)
    show -e b + ((b : ℕ) : ℤ) ≤ -e a + ((a : ℕ) : ℤ)
    rw [Fin.le_def] at hab
    push_cast [Nat.cast_sub hab] at this
    linarith
  · unfold NG.infOf
    have h1 : (Finset.univ.map e.toEmbedding) = T := Finset.map_orderEmbOfFin_univ T hT
    calc (Finset.univ.val.map fun a : Fin n => ((-e a + ((a : ℕ) : ℤ) : ℤ) : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ))
        = (Finset.univ.val.map fun a : Fin n => e a).map (fun y : ℤ => -(y : ℂ) + c) := by
          rw [Multiset.map_map]
          refine Multiset.map_congr rfl fun a _ => ?_
          simp only [Function.comp, hcdef]; push_cast; ring
      _ = T.val.map (fun y : ℤ => -(y : ℂ) + c) := by rw [← h1]; rfl
      _ = S := by
          show M.map _ = S
          rw [Multiset.map_map]
          conv_rhs => rw [← Multiset.map_id S]
          refine Multiset.map_congr rfl fun x hx => ?_
          simp only [Function.comp, id]
          have h := hg x hx
          push_cast
          linear_combination -1 * h

end GlobalTheory.WtComb

namespace GlobalTheory.WtComb

theorem chain_lt (f : ℕ → ℚ) (N : ℕ) (hs : ∀ i, i + 1 < N → f (i + 1) < f i) :
    ∀ i i', i < i' → i' < N → f i' < f i := by
  intro i i' h
  induction i' with
  | zero => omega
  | succ i' ih =>
    intro hN
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · exact lt_trans (hs i' hN) (ih h' (by omega))
    · subst h'; exact hs i hN

theorem chain_le (f : ℕ → ℚ) (N : ℕ) (hs : ∀ i, i + 1 < N → f (i + 1) < f i) :
    ∀ i i', i ≤ i' → i' < N → f i' ≤ f i := by
  intro i i' h hN
  rcases Nat.lt_or_eq_of_le h with h' | h'
  · exact (chain_lt f N hs i i' h' hN).le
  · rw [h']

def qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : Multiset ℚ :=
  (Finset.univ.val.map fun i : Fin (R.k - 1) => h.v i) + (Finset.univ.val.map fun i : Fin R.m => -h.b i) +
  ((Multiset.range R.t).map fun c : ℕ => -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2)

theorem paramV_eq (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ) :
    NG.paramV R h j sh = (qv R h j).map (fun q : ℚ => (q : ℂ) - sh) := by
  unfold NG.paramV qv
  simp only [Multiset.map_add (f := _), Multiset.map_map]
  congr 1
  · congr 1
    all_goals refine Multiset.map_congr rfl fun i _ => ?_
    all_goals simp only [Function.comp]; push_cast; try ring
  · refine Multiset.map_congr rfl fun c _ => ?_
    simp only [Function.comp]; push_cast; try ring

theorem card_qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : Multiset.card (qv R h j) = R.nV := by
  have := R.m_add_three_le_k
  simp [qv, Ranks.nV, Ranks.r]
  omega

end GlobalTheory.WtComb

namespace GlobalTheory.WtComb

theorem nodup_qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : (qv R h j).Nodup := by
  classical
  have hk := R.m_add_three_le_k
  have hm2 := R.two_le_m
  have ht0 : (0 : ℚ) ≤ R.t := by positivity
  let U : ℕ → ℚ := fun i => if hi : i < R.k then h.u ⟨i, hi⟩ else 0
  let V : ℕ → ℚ := fun i => if hi : i < R.k - 1 then h.v ⟨i, hi⟩ else 0
  let B : ℕ → ℚ := fun i => if hi : i < R.m then -h.b ⟨i, hi⟩ else 0
  have hU : ∀ i, i + 1 < R.k → U (i + 1) < U i := by
    intro i hi
    have h1 := h.u_gt_v ⟨i, by omega⟩
    have h2 := h.v_gt_u ⟨i, by omega⟩
    simp only [U, dif_pos hi, dif_pos (show i < R.k by omega)]
    exact lt_trans h2 h1
  have hV : ∀ i, i + 1 < R.k - 1 → V (i + 1) < V i := by
    intro i hi
    have h1 := h.u_gt_v ⟨i + 1, hi⟩
    have h2 := h.v_gt_u ⟨i, by omega⟩
    simp only [V, dif_pos hi, dif_pos (show i < R.k - 1 by omega)]
    exact lt_trans h1 h2
  have hB : ∀ i, i + 1 < R.m → B (i + 1) < B i := by
    intro i hi
    have h1 := h.gap_be ⟨i, by omega⟩
    have h2 := h.gap_eb ⟨i, by omega⟩ hi
    simp only [B, dif_pos hi, dif_pos (show i < R.m by omega)]
    linarith
  have bmono : ∀ i i' : Fin R.m, i.1 ≤ i'.1 → -h.b i' ≤ -h.b i := by
    intro i i' hii
    have := chain_le B R.m hB i.1 i'.1 hii i'.2
    simpa only [B, dif_pos i.2, dif_pos i'.2] using this
  have vgt : ∀ (i : Fin (R.k - 1)) (i' : Fin R.m), -h.b i' < h.v i := by
    intro i i'
    have a1 := h.v_gt_u i
    have a2 := chain_le U R.k hU (i.1 + 1) (R.k - 1) (by omega) (by omega)
    have a3 := h.u_last_gt (by omega) (by omega)
    have a4 := bmono ⟨0, by omega⟩ i' (Nat.zero_le _)
    simp only [U, dif_pos (show R.k - 1 < R.k by omega), dif_pos (show i.1 + 1 < R.k by omega)] at a2
    linarith
  have top : ∀ c : ℕ, -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 < -h.b j := by
    intro c
    have := h.gap_be j
    have hc : (0 : ℚ) ≤ c := by positivity
    linarith
  have bne : ∀ (i : Fin R.m) (c : ℕ), c < R.t → -h.b i ≠ -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 := by
    intro i c hc
    by_cases hij : i.1 ≤ j.1
    · have := bmono i j hij
      have := top c
      intro heq; linarith
    · have hj1 : j.1 + 1 < R.m := by have := i.2; omega
      have a1 := h.gap_eb j hj1
      have a2 := bmono ⟨j.1 + 1, hj1⟩ i (show j.1 + 1 ≤ i.1 by omega)
      have hc' : (c : ℚ) + 1 ≤ R.t := by exact_mod_cast hc
      intro heq; linarith
  have vne : ∀ (i : Fin (R.k - 1)) (c : ℕ), h.v i ≠ -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 := by
    intro i c heq
    have := vgt i j
    have := top c
    linarith
  have vinj : Function.Injective h.v := by
    refine StrictAnti.injective fun a b hab => ?_
    have := chain_lt V (R.k - 1) hV a.1 b.1 hab b.2
    simpa only [V, dif_pos a.2, dif_pos b.2] using this
  have binj : Function.Injective fun i : Fin R.m => -h.b i := by
    refine StrictAnti.injective fun a b hab => ?_
    have := chain_lt B R.m hB a.1 b.1 hab b.2
    simpa only [B, dif_pos a.2, dif_pos b.2] using this
  have rinj : Function.Injective fun c : ℕ => -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 := by
    intro c c' hcc
    have : (c : ℚ) = c' := by simp only at hcc; linarith
    exact_mod_cast this
  unfold qv
  refine Multiset.nodup_add.2 ⟨Multiset.nodup_add.2 ⟨Finset.univ.nodup.map vinj, Finset.univ.nodup.map binj, ?_⟩,
    (Multiset.nodup_range _).map rinj, ?_⟩
  · refine Multiset.disjoint_left.2 fun ha hb => ?_
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha
    obtain ⟨i', -, hi'⟩ := Multiset.mem_map.1 hb
    have := vgt i i'
    linarith
  · refine Multiset.disjoint_left.2 fun ha hb => ?_
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [Multiset.mem_range] at hc
    rcases Multiset.mem_add.1 ha with ha | ha
    · obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 ha
      exact vne i c hi
    · obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 ha
      exact bne i c hc hi

theorem int_qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : ∀ q ∈ qv R h j, ∃ z : ℤ, q = z := by
  intro q hq
  unfold qv at hq
  rcases Multiset.mem_add.1 hq with hq | hq
  · rcases Multiset.mem_add.1 hq with hq | hq
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hq
      exact h.v_int i
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hq
      obtain ⟨z, hz⟩ := h.b_int i
      exact ⟨-z, by rw [hz]; push_cast; ring⟩
  · obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hq
    obtain ⟨z, hz⟩ := h.e_int j
    obtain ⟨s, hs⟩ := R.t_odd
    refine ⟨-z + s - c, ?_⟩
    rw [hz, hs]; push_cast; ring

theorem paramV_eq_infOf : ∀ (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ), (∃ z : ℤ, sh = (z : ℂ) + 1 / 2) →
    ∃ lam : DomWeight R.nV, NG.infOf lam.w = NG.paramV R h j sh := by
  intro R h j sh ⟨z', hz'⟩
  rw [paramV_eq]
  apply exists_domWeight_infOf
  · rw [Multiset.card_map, card_qv]
  · exact (nodup_qv R h j).map (fun a b hab => by simpa using hab)
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨w, rfl⟩ := int_qv R h j q hq
    obtain ⟨a, ha⟩ := R.k_even
    obtain ⟨b, hb⟩ := R.m_even
    obtain ⟨s, hs⟩ := R.t_odd
    have hk := R.m_add_three_le_k
    have hp : R.nV = 2 * (a + b + s) := by simp only [Ranks.nV, Ranks.r]; omega
    refine ⟨w - z' - (a + b + s), ?_⟩
    rw [hz', hp]; push_cast; ring

end GlobalTheory.WtComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NoRamifiedNorm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.ErrTies

theorem trace_rat {R : Ranks} (H : Host R) (x : H.E) (hx : x ∈ H.K) :
    ∃ r : ℚ, (r : H.E) = x + H.conj x := by
  have h1 := Formalism.MainNotions.UnusedSlot33.HK.norm_K H ⟨x, hx⟩
  have h2 := Formalism.MainNotions.UnusedSlot33.HK.norm_K H ⟨x + 1, add_mem hx (one_mem _)⟩
  refine ⟨Algebra.norm ℚ (⟨x + 1, add_mem hx (one_mem _)⟩ : H.K) -
    Algebra.norm ℚ (⟨x, hx⟩ : H.K) - 1, ?_⟩
  rw [eq_ratCast] at h1 h2
  push_cast
  rw [h1, h2]
  simp only [map_add (f := _), map_one]
  ring

theorem no_ramified_norm {T d : ℕ} (hT : T.Prime) (hd : d.Prime) (h2 : T ≠ 2) (hTd : T ≠ d)
    (a : ℤ) (s : ℚ) (h : ((T : ℚ) * a) ^ 2 - 4 * T = -d * s ^ 2) : False := by
  have hTZ : Prime (T : ℤ) := Nat.prime_iff_prime_int.1 hT
  have hq : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  have hs : s * s.den = s.num := Rat.mul_den_eq_num s
  have hZ : (T : ℤ) * ((T * a ^ 2 - 4) * (s.den : ℤ) ^ 2) = -d * s.num ^ 2 := by
    have : (T : ℚ) * ((T * a ^ 2 - 4) * (s.den : ℚ) ^ 2) = -d * (s.num : ℚ) ^ 2 := by
      rw [← hs]
      linear_combination (s.den : ℚ) ^ 2 * h
    exact_mod_cast this
  have hnd : ¬ (T : ℤ) ∣ -(d : ℤ) := by
    rw [dvd_neg, Int.natCast_dvd_natCast]
    exact fun h => hTd ((Nat.prime_dvd_prime_iff_eq hT hd).1 h)
  have hp : (T : ℤ) ∣ s.num :=
    hTZ.dvd_of_dvd_pow ((hTZ.dvd_or_dvd ⟨_, hZ.symm⟩).resolve_left hnd)
  obtain ⟨p, hp'⟩ := hp
  have hT0 : (T : ℤ) ≠ 0 := hTZ.ne_zero
  have hZ2 : (T * a ^ 2 - 4) * (s.den : ℤ) ^ 2 = T * (-d * p ^ 2) := by
    apply mul_left_cancel₀ hT0
    rw [hZ, hp']; ring
  have h4 : (T : ℤ) ∣ 2 ^ 2 * (s.den : ℤ) ^ 2 :=
    ⟨a ^ 2 * (s.den : ℤ) ^ 2 + d * p ^ 2, by linear_combination -hZ2⟩
  rcases hTZ.dvd_or_dvd h4 with h5 | h5
  · have h6 : (T : ℤ) ∣ ((2 : ℕ) : ℤ) := hTZ.dvd_of_dvd_pow h5
    rw [Int.natCast_dvd_natCast] at h6
    exact h2 ((Nat.prime_dvd_prime_iff_eq hT Nat.prime_two).1 h6)
  · have h6 : T ∣ s.den := Int.natCast_dvd_natCast.1 (hTZ.dvd_of_dvd_pow h5)
    have h7 : T ∣ s.num.natAbs := Int.natCast_dvd.1 ⟨p, hp'⟩
    have h8 := Nat.dvd_gcd h7 h6
    rw [s.reduced] at h8
    exact hT.one_lt.ne' (Nat.dvd_one.1 h8)

theorem not_both_mem {R : Ranks} (H : Host R) {T : ℕ} (hT : T.Prime) (π π' : 𝓞 H.E)
    (hK : (π : H.E) ∈ H.K) (hc : (π' : H.E) = H.conj π) (hN : (π : H.E) * H.conj π = T)
    (M : ℕ) (hM : 2 * H.d ∣ M) (hcong : π - 1 ∈ Ideal.span {(M : 𝓞 H.E)})
    (P : Ideal (𝓞 H.E)) (hP : P ≠ ⊤) (h1 : π ∈ P) (h2 : π' ∈ P) : False := by
  have hTe : π * π' = (T : 𝓞 H.E) := by
    apply RingOfIntegers.ext
    push_cast
    rw [← hN, ← hc]
  have hTP : (T : 𝓞 H.E) ∈ P := hTe ▸ P.mul_mem_right _ h1
  have hTM : ¬ T ∣ M := by
    rintro ⟨k, hk⟩
    apply hP
    rw [Ideal.eq_top_iff_one]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hcong
    have : (1 : 𝓞 H.E) = π - c * k * T := by
      rw [hk] at hc
      push_cast at hc
      linear_combination hc
    rw [this]
    exact P.sub_mem h1 (P.mul_mem_left _ hTP)
  have hT2 : T ≠ 2 := fun h => hTM (h ▸ (Dvd.intro _ rfl).trans hM)
  have hTd : T ≠ H.d := fun h => hTM (h ▸ (Dvd.intro_left _ rfl).trans hM)
  obtain ⟨r, hr⟩ := trace_rat H π hK
  have hint : IsIntegral ℤ r := by
    have : IsIntegral ℤ (algebraMap ℚ H.E r) := by
      rw [eq_ratCast, hr, ← hc]
      exact π.isIntegral_coe.add π'.isIntegral_coe
    exact (isIntegral_algebraMap_iff ).1 this
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [eq_intCast] at ha
  have haE : (a : 𝓞 H.E) = π + π' := by
    apply RingOfIntegers.ext
    push_cast
    rw [← ha] at hr
    push_cast at hr
    rw [← hc] at hr
    exact (map_intCast (algebraMap (𝓞 H.E) H.E) a).trans hr
  have hTa : (T : ℤ) ∣ a := by
    by_contra hn
    have hcop : IsCoprime (T : ℤ) a :=
      ((Nat.prime_iff_prime_int.1 hT).irreducible.coprime_iff_not_dvd).2 hn
    obtain ⟨x, y, hxy⟩ := hcop
    apply hP
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 H.E) = x * T + y * (π + π') := by
      rw [← haE]
      exact_mod_cast (congrArg (fun z : ℤ => (z : 𝓞 H.E)) hxy).symm
    rw [this]
    exact P.add_mem (P.mul_mem_left _ hTP) (P.mul_mem_left _ (P.add_mem h1 h2))
  obtain ⟨a', rfl⟩ := hTa
  set b := H.sqd with hb
  have hb0 : b ≠ 0 := Formalism.MainNotions.UnusedSlot33.HK.b_ne_zero H
  have hb2 : b ^ 2 = -(H.d : H.E) := Examples₂.bE_sq H
  have hbc : H.conj b = -b := Examples₂.conj_bE H
  obtain ⟨s, hs⟩ := trace_rat H ((π : H.E) / b) (div_mem hK (Formalism.MainNotions.UnusedSlot33.HK.bE_mem H))
  rw [map_div₀, hbc] at hs
  have hs' : (s : H.E) * b = π - H.conj π := by
    rw [hs]; field_simp; ring
  refine no_ramified_norm hT H.hyp.2.1 hT2 hTd a' s ?_
  have hE : (((T : ℚ) * a') ^ 2 - 4 * T : ℚ) = ((-(H.d : ℚ) * s ^ 2 : ℚ) : H.E) := by
    rw [← ha] at hr
    push_cast at hr ⊢
    rw [hr, ← hN, ← hb2]
    linear_combination (-((s : H.E) * b) - (π - H.conj π)) * hs'
  exact_mod_cast hE

theorem embLL_tauLL (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    D.what₂.embLL (tauLL D τ x) = D.host.emb (D.eTau τ).1 x := by
  rw [tauLL, Host.emb, ← D.embE_φ₀]
  rfl

def errOfTies (D : D7) (H : Formalism.L2.Herm.ColsHermS D) : ErrX D where
  piG := (H.levelZeroCompatibility D.u₀).piG
  piG_K := (H.levelZeroCompatibility D.u₀).piG_K
  piG_norm i := by rw [← Examples₂.star_eq_conj]; exact (H.levelZeroCompatibility D.u₀).piG_norm i
  piT u := (H.atT u).piU
  piT_K u := (H.atT u).piU_K
  piT_norm u := (H.atT u).piU_norm
  piT_cong u := (H.atT u).piU_cong
  vPl u v := (H.base.vT u v).1
  vPl_inj u := fun _ _ h => (H.base.vT u).injective (Subtype.ext h)
  norm_mem_place_ideal u v := (H.base.vT u v).2

theorem seenDef (D : D7) (H : Formalism.L2.Herm.ColsHermS D) : SeenDef D (errOfTies D H) := by
  intro u w hw
  obtain ⟨v⟩ : Nonempty (D.mem u).A.vT := by
    letI := (D.mem u).A.vTFin
    rw [← Fintype.card_pos_iff, (D.mem u).A.card_vT]
    unfold Ranks.f Ranks.n
    exact Nat.mul_pos (by decide) D.R.toFrame.ord_pos
  have hτ : ∀ τ, tauLL D τ ((H.atT u).piU : D.host.E) = D.embE ((H.atT u).piU : D.host.E) := by
    intro τ
    rw [tauLL, Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K D.host _ (D.eTau τ).2 _ (H.atT u).piU_K]
  have key := (H.atT u).seen w hw v (H.atT u).piU _ (embLL_tauLL D _ _)
  rw [hτ] at key
  change _ ↔ ∀ τ, 0 < D.what₂.places.val w (tauLL D τ ((H.atT u).piU : D.host.E))
  simp only [hτ]
  constructor
  · intro hs _
    rw [if_pos hs] at key
    exact key.2 ((H.atT u).Pv_pi v)
  · intro h
    by_contra hs
    rw [if_neg hs, Formalism.L2.Col.mem_conjIdeal] at key
    refine not_both_mem D.host (D.mem u).A.T_prime (H.atT u).piU _ (H.atT u).piU_K ?_
      (H.atT u).piU_norm _ ?_ (H.atT u).piU_cong _ ((H.atT u).Pv_max v).ne_top
      ((H.atT u).Pv_pi v) (key.1 (h ((D.fm u).tauOf w v)))
    · exact Examples₂.star_eq_conj D.host _
    · obtain ⟨c, hc⟩ := D.host.two_dvd_QS
      refine ⟨c * D.host.q * (D.host.g 0 * D.host.g 1) ^ 2, ?_⟩
      trans D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2
      · ring
      · rw [hc]
        ring

theorem tauOfDef (D : D7) (H : Formalism.L2.Herm.ColsHermS D) : TauOfDef D (errOfTies D H) := by
  intro u w hw v x
  have key := (H.atT u).seen w hw v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) _ (embLL_tauLL D _ _)
  have hx : x ∈ (H.base.vT u v).1.asIdeal ↔
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ (H.atT u).Pv v := by
    rw [← (H.atT u).Pv_over v, Ideal.mem_comap]
  have hc : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) =
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    apply RingOfIntegers.ext
    exact (Examples₂.star_eq_conj D.host _).trans ((Examples₂.conj_eq_self_iff D.host _).2 (x : D.host.F).2)
  refine hx.trans (Iff.trans ?_ key.symm)
  split_ifs
  · rfl
  · rw [Formalism.L2.Col.mem_conjIdeal, hc]

theorem exists_errX : ∀ (D : D7) (H : Formalism.L2.Herm.ColsHermS D), ∃ eX : ErrX D, eX.piG = (H.levelZeroCompatibility D.u₀).piG ∧ (∀ u, eX.piT u = (H.atT u).piU) ∧ (∀ u v, eX.vPl u v = (H.base.vT u v).1) ∧ PiGLevel D H.base.lev0 eX ∧ PiTLevel D H.base.lev0 eX ∧ SeenDef D eX ∧ TauOfDef D eX := by
  intro D H
  refine ⟨errOfTies D H, rfl, fun _ => rfl, fun _ _ => rfl, ?_, ?_, seenDef D H, tauOfDef D H⟩
  · intro u i v h
    have := (H.levelZeroCompatibility u).splitG_pi i v h
    rw [H.piG u D.u₀, Examples₂.star_eq_conj] at this
    exact this
  · intro u v z hz y
    exact (H.levelZeroCompatibility u).fM_pi _ _ z hz y

end GlobalTheory.Mem.ErrTies
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPointMovesAdelicThetaByDetCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_point_moves_adelic_theta_by_det_character : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∃ η, IsEtaTilde D η) → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ a ∈ GinfC T, ∀ y : (AE D)ˣ, IsDetRoot T a y → ∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → ∀ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f → Zak ψ θ hr eT bas idx (frOf hr eT (mvZ θ a Z)) (((χS y : Circle) : ℂ) • φ) (om (1, a) f) := by
  first | exact @GlobalTheory.OneMapRef.RealMove.zak_om_real | exact GlobalTheory.OneMapRef.RealMove.zak_om_real | (intros; apply GlobalTheory.OneMapRef.RealMove.zak_om_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOneMemOfIsRayFieldIn
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.RayRoots

theorem rootOne_mem_of_isRayFieldIn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ)
    (N n : ℕ) (M : IntermediateField ℚ ℂ), N ≠ 0 → n ∣ N → IsRayFieldIn φ (natIdeal E N) M → rootOne n ∈ M :=
  fun _ _ _ _ φ _ _ _ hN hn hM => GlobalTheory.Mem.FieldsEx.rootOne_mem_ray φ hN hn hM

end GlobalTheory.Mem.RayRoots
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistCharacterRamifiedAtConductorTrivialAboveLStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistCharacter_ramified_at_conductor_trivial_above_l : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (w : D.what₂.places.Pl), GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.RowTie.ChebSplit D.nd → PsiChoiceCompatible D cf C tp → TwistedAt D w → (tp.psi w).ValuesIn 0 D.what₂.embLL → NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) → (∀ v ∈ C.Q w, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ σ ∈ Ine (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ ≠ 1) ∧ (∀ v ∈ placesOver D.host.E (D.what₂.places.resChar w), ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Dec (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ = 1) := by
  first | exact @GlobalTheory.TwistRamLoc.twist_ram_and_trivial_at_l | exact GlobalTheory.TwistRamLoc.twist_ram_and_trivial_at_l | (intros; apply GlobalTheory.TwistRamLoc.twist_ram_and_trivial_at_l <;> assumption)
end

