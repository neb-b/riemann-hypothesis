module

public import Formalism.SuccessiveMinima.DefsMink

@[expose] public section

-- bundled from Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MinkCore
section
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN

theorem partialBoxVolumeTopLeOne : GjTop := by
  intro n A
  unfold Gj
  calc volume (boxJ n n ∩ (A + latJ n n)) ≤ volume (boxJ n n) :=
        measure_mono Set.inter_subset_left
    _ ≤ volume (Set.univ.pi fun _ : Fin n => Set.Ico (0 : ℝ) 1) := by
        apply measure_mono
        intro u hu i _
        exact hu i i.2
    _ = 1 := by
        rw [Real.volume_pi_Ico]
        simp

theorem gjZero (n : ℕ) (A : Set (Fin n → ℝ)) : Gj n 0 A = volume A := by
  unfold Gj
  have h1 : boxJ n 0 = Set.univ := by
    ext u
    simp [boxJ]
  have h2 : latJ n 0 = {0} := by
    ext k
    simp only [latJ, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, hk⟩
      funext i
      exact hk i (Nat.zero_le _)
    · rintro rfl
      exact ⟨fun _ => ⟨0, by simp⟩, fun _ _ => rfl⟩
  rw [h1, h2, Set.univ_inter]
  simp

theorem minkCore_of (h3 : GjLevel) (h4 : GjScale) : MinkCore := by
  intro n C lam hCo hCc hCs hCb hpos hmono hsep
  have hsmulC : ∀ k : Fin n, IsOpen (lam k • C) := fun k => hCo.smul₀ (hpos k).ne'
  have hlev : ∀ k : Fin n, Gj n k (lam k • C) ≤ Gj n (k + 1) (lam k • C) := by
    intro k
    apply h3 n k (lam k • C) k.2 (hsmulC k)
    intro x hx y hy hxy i hi
    exact hsep k x hx y hy hxy i (Fin.le_def.mpr hi)
  have hbase : ∀ hk : 0 < n, ENNReal.ofReal (∏ i, min (lam i) (lam ⟨0, hk⟩)) * volume C
      ≤ Gj n 0 (lam ⟨0, hk⟩ • C) := by
    intro hk
    rw [gjZero, Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_pos (pow_pos (hpos _) n)]
    have e : ∏ i, min (lam i) (lam ⟨0, hk⟩) = lam ⟨0, hk⟩ ^ n := by
      rw [Finset.prod_congr rfl
        (fun i _ => min_eq_right (hmono (show (⟨0, hk⟩ : Fin n) ≤ i from
          Fin.le_def.mpr (Nat.zero_le (i : ℕ)))))]
      simp
    rw [e]
  have hstep : ∀ k (hk0 : k < n) (hk : k + 1 < n),
      ∏ i, min (lam i) (lam ⟨k + 1, hk⟩) =
        (lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1)) * ∏ i, min (lam i) (lam ⟨k, hk0⟩) := by
    intro k hk0 hk
    have hab : lam ⟨k, hk0⟩ ≤ lam ⟨k + 1, hk⟩ := hmono (Fin.mk_le_mk.mpr (by omega))
    have ha0 : 0 < lam ⟨k, hk0⟩ := hpos _
    have hfac : ∀ i : Fin n, min (lam i) (lam ⟨k + 1, hk⟩) =
        (if k < (i : ℕ) then lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩ else 1) * min (lam i) (lam ⟨k, hk0⟩) := by
      intro i
      split_ifs with h
      · have h1 : lam ⟨k + 1, hk⟩ ≤ lam i := hmono (Fin.le_def.mpr (show k + 1 ≤ (i : ℕ) by omega))
        rw [min_eq_right h1, min_eq_right (hab.trans h1), div_mul_cancel₀ _ ha0.ne']
      · have h1 : lam i ≤ lam ⟨k, hk0⟩ := hmono (Fin.le_def.mpr (show (i : ℕ) ≤ k by omega))
        rw [min_eq_left (h1.trans hab), min_eq_left h1, one_mul]
    have hcard : (Finset.univ.filter fun i : Fin n => k < (i : ℕ)).card = n - (k + 1) := by
      have e : (Finset.univ.filter fun i : Fin n => k < (i : ℕ)) = Finset.Ioi ⟨k, hk0⟩ := by
        ext i
        simp [Fin.lt_def]
      rw [e, Fin.card_Ioi]
      simp only
      omega
    rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib, Finset.prod_ite,
      Finset.prod_const, Finset.prod_const_one, mul_one, hcard]
  have claim : ∀ k (hk : k < n), ENNReal.ofReal (∏ i, min (lam i) (lam ⟨k, hk⟩)) * volume C
      ≤ Gj n k (lam ⟨k, hk⟩ • C) := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih =>
      intro hk
      have hk0 : k < n := by omega
      have hr : 0 ≤ (lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1)) := by
        have := hpos ⟨k + 1, hk⟩
        have := hpos ⟨k, hk0⟩
        positivity
      rw [hstep k hk0 hk, ENNReal.ofReal_mul hr, mul_assoc]
      calc ENNReal.ofReal ((lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1))) *
            (ENNReal.ofReal (∏ i, min (lam i) (lam ⟨k, hk0⟩)) * volume C)
          ≤ ENNReal.ofReal ((lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1))) *
            Gj n (k + 1) (lam ⟨k, hk0⟩ • C) := by
            gcongr
            exact (ih hk0).trans (hlev ⟨k, hk0⟩)
        _ ≤ Gj n (k + 1) (lam ⟨k + 1, hk⟩ • C) :=
            h4 n (k + 1) C (lam ⟨k, hk0⟩) (lam ⟨k + 1, hk⟩) hk.le hCo hCc hCs hCb (hpos _)
              (hmono (Fin.mk_le_mk.mpr (by omega)))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 := partialBoxVolumeTopLeOne 0 C
    rw [gjZero] at h0
    simp only [Fin.prod_univ_zero, mul_one]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h0)
  · have hn1 : n - 1 < n := by omega
    have hlast := (claim (n - 1) hn1).trans (hlev ⟨n - 1, hn1⟩)
    have htop := partialBoxVolumeTopLeOne n (lam ⟨n - 1, hn1⟩ • C)
    have e : ((⟨n - 1, hn1⟩ : Fin n) : ℕ) + 1 = n := by
      show n - 1 + 1 = n
      omega
    rw [e] at hlast
    have hprod : ∏ i, min (lam i) (lam ⟨n - 1, hn1⟩) = ∏ i, lam i :=
      Finset.prod_congr rfl fun i _ =>
        min_eq_left (hmono (Fin.le_def.mpr (show (i : ℕ) ≤ n - 1 by omega)))
    rw [hprod] at hlast
    have hP : 0 ≤ ∏ i, lam i := Finset.prod_nonneg fun i _ => (hpos i).le
    have hfin : ENNReal.ofReal (∏ i, lam i) * volume C ≤ 1 := hlast.trans htop
    rw [mul_comm, ← ENNReal.toReal_ofReal hP, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hfin)

end Formalism.FN
end
end

-- bundled from Formalism.SuccessiveMinima.SuccessiveMinimaProofs.SuccMin
section
open MeasureTheory Module Metric Set
open scoped Pointwise

noncomputable section

namespace Formalism.FN.SuccessiveMinima

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem mem_smul_iff_gauge {K : Set E} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hK0 : (0 : E) ∈ interior K) {t : ℝ} (ht : 0 ≤ t) (u : E) :
    u ∈ t • K ↔ gauge K u ≤ t := by
  have hK : K ∈ nhds (0 : E) := mem_interior_iff_mem_nhds.mp hK0
  have hKabs : Absorbent ℝ K := absorbent_nhds_zero hK
  rcases ht.eq_or_lt with rfl | htpos
  ·
    have hne : K.Nonempty := ⟨0, interior_subset hK0⟩
    rw [Set.zero_smul_set hne, Set.mem_zero]
    constructor
    · rintro rfl
      simp
    · intro hg
      by_contra hu
      have := (gauge_pos hKabs ((NormedSpace.isVonNBounded_iff ℝ).mpr hKc.isBounded)).mpr hu
      linarith
  · have h1 : t⁻¹ • u ∈ K ↔ gauge K (t⁻¹ • u) ≤ 1 := by
      rw [gauge_le_one_iff_mem_closure hKv hK, hKc.isClosed.closure_eq]
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ htpos.ne', h1,
      gauge_smul_of_nonneg (inv_nonneg.mpr htpos.le), smul_eq_mul, inv_mul_le_iff₀ htpos, mul_one]

theorem finite_lat_inter (L : Submodule ℤ E) [DiscreteTopology L] {s : Set E}
    (hs : Bornology.IsBounded s) : ((L : Set E) ∩ s).Finite := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hcl : IsClosed (L : Set E) := L.toAddSubgroup.isClosed_of_discrete
  have hd : IsDiscrete (L : Set E) := by
    first
      | exact ⟨‹DiscreteTopology L›⟩
      | exact isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology L›
  rw [Set.inter_comm]
  exact Metric.finite_isBounded_inter_isClosed hd hs hcl

theorem exists_gap {α : Type*} (f : α → ℝ) {B : Set α} (hB : B.Finite) {c T : ℝ} (hcT : c < T)
    (h : ∀ u ∈ B, c < f u) : ∃ m, c < m ∧ m ≤ T ∧ ∀ u ∈ B, m ≤ f u := by
  obtain ⟨m, hmS, hmin⟩ := Set.exists_min_image (insert T (f '' B)) id
    ((hB.image f).insert T) ⟨T, Set.mem_insert _ _⟩
  refine ⟨m, ?_, hmin T (Set.mem_insert _ _), fun u hu => hmin (f u) (Set.mem_insert_of_mem _ ⟨u, hu, rfl⟩)⟩
  rcases hmS with rfl | ⟨u, hu, rfl⟩
  · exact hcT
  · exact h u hu

variable (L : Submodule ℤ E) [DiscreteTopology L] {K : Set E}

theorem succMin_mem (hKc : IsCompact K) (hKv : Convex ℝ K) (hK0 : (0 : E) ∈ interior K)
    {i : ℕ} {T : ℝ}
    (hT : 0 ≤ T ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ T • K))) :
    0 ≤ succMin L K i ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ succMin L K i • K)) := by
  classical
  set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ t • K))}
    with hS
  have hSne : S.Nonempty := ⟨T, hT⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  have hs0 : 0 ≤ sInf S := le_csInf hSne fun t ht => ht.1
  have hsT : sInf S ≤ T := csInf_le hSbdd hT
  show 0 ≤ sInf S ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ sInf S • K))
  refine ⟨hs0, ?_⟩
  rcases hsT.eq_or_lt with hsT | hsT
  · rw [hsT]; exact hT.2

  set B : Set E := {u | u ∈ (L : Set E) ∩ T • K ∧ sInf S < gauge K u} with hB
  have hBfin : B.Finite :=
    (finite_lat_inter L ((hKc.smul T).isBounded)).subset fun u hu => hu.1
  obtain ⟨m, hsm, hmT, hmB⟩ := exists_gap (gauge K) hBfin hsT fun u hu => hu.2
  obtain ⟨t, htS, htm⟩ := exists_lt_of_csInf_lt hSne hsm
  have hst : sInf S ≤ t := csInf_le hSbdd htS
  refine htS.2.trans (Submodule.finrank_mono (Submodule.span_mono ?_))
  rintro u ⟨huL, hut⟩
  have hgt : gauge K u ≤ t := (mem_smul_iff_gauge hKc hKv hK0 htS.1 u).mp hut
  refine ⟨huL, (mem_smul_iff_gauge hKc hKv hK0 hs0 u).mpr ?_⟩
  by_contra hlt
  push_neg at hlt
  have huT : u ∈ T • K :=
    (mem_smul_iff_gauge hKc hKv hK0 (hs0.trans hsT.le) u).mpr (by linarith)
  have := hmB u ⟨⟨huL, huT⟩, hlt⟩
  linarith

theorem exists_pos_bot (hKc : IsCompact K) (hKv : Convex ℝ K) (hK0 : (0 : E) ∈ interior K) :
    ∃ m : ℝ, 0 < m ∧ ∀ t, 0 ≤ t → t < m →
      Submodule.span ℝ ((L : Set E) ∩ t • K) = ⊥ := by
  have hK : K ∈ nhds (0 : E) := mem_interior_iff_mem_nhds.mp hK0
  have hKabs : Absorbent ℝ K := absorbent_nhds_zero hK
  set B : Set E := {u | u ∈ (L : Set E) ∩ K ∧ u ≠ 0} with hB
  have hBfin : B.Finite := (finite_lat_inter L hKc.isBounded).subset fun u hu => hu.1
  obtain ⟨m, hm0, hm1, hmB⟩ := exists_gap (gauge K) hBfin zero_lt_one
    fun u hu => (gauge_pos hKabs ((NormedSpace.isVonNBounded_iff ℝ).mpr hKc.isBounded)).mpr hu.2
  refine ⟨m, hm0, fun t ht htm => Submodule.span_eq_bot.mpr ?_⟩
  rintro u ⟨huL, hut⟩
  have hgt : gauge K u ≤ t := (mem_smul_iff_gauge hKc hKv hK0 ht u).mp hut
  by_contra hu
  have huK : u ∈ K := by
    have := (mem_smul_iff_gauge hKc hKv hK0 zero_le_one u).mpr (by linarith)
    rwa [one_smul] at this
  have := hmB u ⟨⟨huL, huK⟩, hu⟩
  linarith

theorem exists_span_top [IsZLattice ℝ L] (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hK0 : (0 : E) ∈ interior K) :
    ∃ T : ℝ, 0 ≤ T ∧ Submodule.span ℝ ((L : Set E) ∩ T • K) = ⊤ := by

  obtain ⟨b, hbL, hbspan, hbli⟩ := exists_linearIndependent ℝ (L : Set E)
  have hbfin : b.Finite := hbli.setFinite
  obtain ⟨M, hM⟩ := (hbfin.image (gauge K)).bddAbove
  refine ⟨max M 0, le_max_right _ _, eq_top_iff.mpr ?_⟩
  have hLtop : Submodule.span ℝ (L : Set E) = ⊤ := IsZLattice.span_top
  rw [← hLtop, ← hbspan]
  refine Submodule.span_mono fun x hx => ⟨hbL hx, ?_⟩
  refine (mem_smul_iff_gauge hKc hKv hK0 (le_max_right _ _) x).mpr ?_
  exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)

end Formalism.FN.SuccessiveMinima

open Formalism.FN.SuccessiveMinima in
theorem Formalism.FN.existsSuccessiveMinimaVectors : Formalism.FN.SuccMinFacts := by
  classical
  intro E _ _ _ L _ _ K hKc hKv _ hK0
  have hmemK : ∀ {t : ℝ}, 0 ≤ t → ∀ u, u ∈ t • K ↔ gauge K u ≤ t :=
    fun ht u => mem_smul_iff_gauge hKc hKv hK0 ht u
  obtain ⟨T, hT0, hTtop⟩ := exists_span_top L hKc hKv hK0
  have hTfin : finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ T • K)) = finrank ℝ E := by
    rw [hTtop, finrank_top]
  have hmem : ∀ j, j ≤ finrank ℝ E → 0 ≤ succMin L K j ∧
      j ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ succMin L K j • K)) :=
    fun j hj => succMin_mem L hKc hKv hK0 ⟨hT0, by rw [hTfin]; exact hj⟩
  have hsub : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → (L : Set E) ∩ s • K ⊆ (L : Set E) ∩ t • K :=
    fun hs hst u hu => ⟨hu.1, (hmemK (hs.trans hst) u).mpr (((hmemK hs u).mp hu.2).trans hst)⟩
  have hle : ∀ {j : ℕ} {t : ℝ}, 0 ≤ t →
      j ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ t • K)) → succMin L K j ≤ t :=
    fun ht h => csInf_le ⟨0, fun x hx => hx.1⟩ ⟨ht, h⟩
  obtain ⟨m, hm0, hmbot⟩ := exists_pos_bot L hKc hKv hK0
  have hpos : ∀ j, 1 ≤ j → j ≤ finrank ℝ E → 0 < succMin L K j := by
    intro j hj1 hjn
    obtain ⟨h0, hj⟩ := hmem j hjn
    by_contra hneg
    push_neg at hneg
    rw [hmbot _ h0 (lt_of_le_of_lt hneg hm0), finrank_bot] at hj
    omega

  have build : ∀ k, k ≤ finrank ℝ E → ∃ w : Fin k → E, LinearIndependent ℝ w ∧
      ∀ j : Fin k, w j ∈ L ∧ w j ∈ succMin L K ((j : ℕ) + 1) • K := by
    intro k
    induction k with
    | zero => intro _; exact ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨w, hw, hwm⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨_, hdim⟩ := hmem (k + 1) hk
      have hex : ∃ x ∈ (L : Set E) ∩ succMin L K (k + 1) • K,
          x ∉ Submodule.span ℝ (Set.range w) := by
        by_contra hno
        push_neg at hno
        have h1 := Submodule.finrank_mono (Submodule.span_le.mpr hno)
        rw [finrank_span_eq_card hw, Fintype.card_fin] at h1
        omega
      obtain ⟨x, ⟨hxL, hxK⟩, hxw⟩ := hex
      refine ⟨Fin.snoc w x, linearIndependent_finSnoc.mpr ⟨hw, hxw⟩, fun j => ?_⟩
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.snoc_last, Fin.val_last]
        exact ⟨hxL, hxK⟩
      · simp only [Fin.snoc_castSucc, Fin.coe_castSucc]
        exact hwm i
  obtain ⟨v, hv, hvm⟩ := build (finrank ℝ E) le_rfl
  refine ⟨v, hv, fun i => (hvm i).1, fun i => (hvm i).2,
    fun i => hpos _ (by omega) (Nat.succ_le_of_lt i.isLt), ?_, ?_⟩
  · intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    obtain ⟨h0, hj⟩ := hmem ((j : ℕ) + 1) (Nat.succ_le_of_lt j.isLt)
    exact hle h0 (le_trans (by omega) hj)
  · intro i u huL huint
    have hlam : 0 < succMin L K ((i : ℕ) + 1) := hpos _ (by omega) (Nat.succ_le_of_lt i.isLt)

    have hg : gauge K u < succMin L K ((i : ℕ) + 1) := by
      obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp huint
      rw [gauge_smul_of_nonneg hlam.le, smul_eq_mul]
      exact mul_lt_of_lt_one_right hlam (interior_subset_gauge_lt_one K hy)
    have hg0 : 0 ≤ gauge K u := gauge_nonneg u
    set W := Submodule.span ℝ ((L : Set E) ∩ gauge K u • K) with hW
    have huW : u ∈ W := Submodule.subset_span ⟨huL, (hmemK hg0 u).mpr le_rfl⟩
    have hdn : finrank ℝ W ≤ finrank ℝ E := Submodule.finrank_le W
    have hdi : finrank ℝ W ≤ (i : ℕ) := by
      by_contra hcon
      push_neg at hcon
      have := hle hg0 (show (i : ℕ) + 1 ≤ finrank ℝ W by omega)
      linarith

    have hdW : succMin L K (finrank ℝ W) ≤ gauge K u := hle hg0 le_rfl
    have hvW : ∀ k : Fin (finrank ℝ E), (k : ℕ) < finrank ℝ W → v k ∈ W := by
      intro k hk
      obtain ⟨hd0, hd⟩ := hmem (finrank ℝ W) hdn
      have hk1 : succMin L K ((k : ℕ) + 1) ≤ gauge K u :=
        (hle hd0 (le_trans (by omega) hd)).trans hdW
      exact Submodule.subset_span
        (hsub (hmem _ (Nat.succ_le_of_lt k.isLt)).1 hk1 ⟨(hvm k).1, (hvm k).2⟩)
    have himg : v '' {k | (k : ℕ) < finrank ℝ W} =
        Set.range (fun j : Fin (finrank ℝ W) => v (Fin.castLE hdn j)) := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, congrArg v (Fin.ext rfl)⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Fin.castLE hdn j, by simp, rfl⟩
    have hUW : Submodule.span ℝ (v '' {k | (k : ℕ) < finrank ℝ W}) = W := by
      refine Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.mpr ?_) ?_
      · rintro x ⟨k, hk, rfl⟩
        exact hvW k hk
      · rw [himg]
        exact (finrank_span_eq_card (hv.comp _ (Fin.castLE_injective hdn))).trans
          (Fintype.card_fin _)
    rw [← hUW] at huW
    refine Submodule.span_mono (Set.image_mono fun k hk => ?_) huW
    show k < i
    exact Fin.lt_iff_val_lt_val.mpr (lt_of_lt_of_le hk hdi)
end
end

