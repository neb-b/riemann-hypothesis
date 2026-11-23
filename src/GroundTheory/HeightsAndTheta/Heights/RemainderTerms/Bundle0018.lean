module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombDetDescFactorial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Comb Equiv

theorem CombDetDescFactorial.proof : CombDetDescFactorial.Statement := by
  intro m l
  rw [vandermondeOf_eq_det]

  set v : Fin m → ℚ := fun i => (l i : ℚ)
  have hA : (Matrix.of fun i j : Fin m => ((l i).descFactorial (stair m j) : ℚ)) =
      (Matrix.of fun i j : Fin m => (descPochhammer ℚ (j : ℕ)).eval (v i)).submatrix
        id Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply, v,
      descPochhammer_eval_eq_descFactorial, stair]
    rw [Fin.val_rev]
    congr 2
    omega
  have hB : (Matrix.of fun i j : Fin m => v i ^ (m - 1 - (j : ℕ))) =
      (Matrix.vandermonde v).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply, Fin.val_rev,
      Matrix.vandermonde_apply]
    congr 1
    omega
  rw [hA, hB, Matrix.det_permute', Matrix.det_permute',
    Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v
      (fun j => descPochhammer ℚ (j : ℕ))
      (fun j => descPochhammer_natDegree ℚ _)
      (fun j => monic_descPochhammer ℚ _)]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombExtendWord
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

noncomputable section

open scoped Classical

namespace CombExtendWord

theorem snoc_mem {m n : ℕ} (lam : Fin m → ℕ) (hlam : Antitone lam) (k : Fin m) (hk : 1 ≤ lam k)
    (v : Fin n → Fin m) (hv : v ∈ latticeWords n (Function.update lam k (lam k - 1))) :
    (Fin.snoc v k : Fin (n + 1) → Fin m) ∈ latticeWords (n + 1) lam := by
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hv ⊢
  obtain ⟨hlat, hcont⟩ := hv
  refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
  · rcases Nat.lt_or_ge t (n + 1) with htn | htn
    · rw [pcnt_castSucc_snoc _ _ _ (by omega), pcnt_castSucc_snoc _ _ _ (by omega)]
      exact hlat t (by omega) i j hij
    · have ht' : t = n + 1 := by omega
      subst ht'
      rw [pcnt_snoc_last, pcnt_snoc_last, hcont, hcont, update_pred_sub lam k i hk,
        update_pred_sub lam k j hk]
      exact hlam hij
  · rw [pcnt_snoc_last, hcont, update_pred_sub lam k i hk]

theorem exists_word {m : ℕ} (h1 : CombPcntAppend.Statement) (μ : Fin m → ℕ) (hμ : Antitone μ) :
    ∀ (q : ℕ) (lam : Fin m → ℕ), Antitone lam → (∀ i, μ i ≤ lam i) →
      ∑ i, lam i = ∑ i, μ i + q →
        ∃ s : Fin q → Fin m, ∀ n, ∀ w ∈ latticeWords n μ,
          Fin.append w s ∈ latticeWords (n + q) lam := by
  intro q
  induction q with
  | zero =>
    intro lam _ hle hsum
    have heq : ∀ i, μ i = lam i := by
      have := (Finset.sum_eq_sum_iff_of_le (s := univ) (fun i _ => hle i)).mp (by simpa using hsum.symm)
      exact fun i => this i (mem_univ i)
    refine ⟨Fin.elim0, fun n w hw => ?_⟩
    simp only [latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
    have hp : ∀ t i, pcnt (Fin.append w (Fin.elim0 : Fin 0 → Fin m)) t i = pcnt w t i := by
      intro t i
      rw [h1]
      have : pcnt (Fin.elim0 : Fin 0 → Fin m) (t - n) i = 0 := by unfold pcnt; simp
      omega
    refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
    · rw [hp, hp]; exact hw.1 t ht i j hij
    · rw [hp, Nat.add_zero, hw.2 i, heq i]
  | succ q ih =>
    intro lam hlam hle hsum
    have hne : (univ.filter (fun i => μ i < lam i)).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
      have : ∑ i, lam i ≤ ∑ i, μ i :=
        Finset.sum_le_sum fun i _ => not_lt.mp (hemp (mem_univ i))
      omega
    obtain ⟨k, hk, hkmax⟩ : ∃ k, μ k < lam k ∧ ∀ j, μ j < lam j → j ≤ k :=
      ⟨_, (mem_filter.mp (max'_mem _ hne)).2,
        fun j hj => le_max' _ j (mem_filter.mpr ⟨mem_univ j, hj⟩)⟩
    have hgt : ∀ j, k < j → lam j = μ j := by
      intro j hj
      by_contra hne'
      exact absurd (hkmax j (lt_of_le_of_ne (hle j) (Ne.symm hne'))) (not_le.mpr hj)
    have hanti : Antitone (Function.update lam k (lam k - 1)) := by
      intro i j hij
      by_cases hik : i = k <;> by_cases hjk : j = k
      · rw [hik, hjk]
      · rw [hik, Function.update_self, Function.update_of_ne hjk]
        have hkj : k < j := lt_of_le_of_ne (hik ▸ hij) (Ne.symm hjk)
        rw [hgt j hkj]
        have := hμ (hik ▸ hij)
        omega
      · rw [hjk, Function.update_self, Function.update_of_ne hik]
        have := hlam (hjk ▸ hij)
        omega
      · rw [Function.update_of_ne hik, Function.update_of_ne hjk]
        exact hlam hij
    have hle' : ∀ i, μ i ≤ Function.update lam k (lam k - 1) i := by
      intro i
      by_cases hik : i = k
      · rw [hik, Function.update_self]; omega
      · rw [Function.update_of_ne hik]; exact hle i
    have hsum' : ∑ i, Function.update lam k (lam k - 1) i = ∑ i, μ i + q := by
      have h2 : ∀ i, Function.update lam k (lam k - 1) i + (if k = i then 1 else 0) = lam i :=
        fun i => update_pred_sub lam k i (by omega)
      have : ∑ i, lam i = ∑ i, Function.update lam k (lam k - 1) i + 1 := by
        rw [← Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_add_distrib, Finset.sum_ite_eq]
        simp
      omega
    obtain ⟨s', hs'⟩ := ih _ hanti hle' hsum'
    refine ⟨Fin.snoc s' k, fun n w hw => ?_⟩
    rw [Fin.append_snoc]
    exact snoc_mem lam hlam k (by omega) _ (hs' n w hw)

theorem proof (h1 : CombPcntAppend.Statement) : CombExtendWord.Statement := by
  intro m n q μ lam hμ hlam hle hsum
  obtain ⟨s, hs⟩ := exists_word h1 μ hμ q lam hlam hle hsum
  exact ⟨s, hs n⟩

end CombExtendWord

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombPcntAppend
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

open scoped Classical

open Comb

theorem CombPcntAppend.proof : CombPcntAppend.Statement := by
  intro m n q w s t i
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.append_left, Fin.val_castAdd]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.append_right, Fin.val_natAdd]
    have h : (n + (k : ℕ) < t) ↔ ((k : ℕ) < t - n) := by omega
    simp only [h]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Equiv

theorem CombSortLe.proof : CombSortLe.Statement := by
  intro m u l σ hl hul hu k
  obtain ⟨j, hjk, hkj⟩ : ∃ j : Fin m, j ≤ k ∧ k ≤ σ j := by
    by_contra h
    push Not at h
    have hcard : (Iic k).card ≤ (Iio k).card := by
      refine card_le_card_of_injOn σ ?_ σ.injective.injOn
      intro j hj
      simp only [coe_Iic, coe_Iio, Set.mem_Iic, Set.mem_Iio] at hj ⊢
      exact h j hj
    rw [Fin.card_Iic, Fin.card_Iio] at hcard
    omega
  calc u (σ k) ≤ u (σ j) := hu hjk
    _ ≤ l (σ j) := hul _
    _ ≤ l k := hl hkj

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Equiv

namespace Comb

theorem add_index_le_of_strictAnti {m : ℕ} {f : Fin m → ℕ} (hf : StrictAnti f) (a b : Fin m)
    (hab : a ≤ b) : f b + (b : ℕ) ≤ f a + (a : ℕ) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have h1 := ih (by omega)
    have h2 : f ⟨n + 1, hb⟩ < f ⟨n, by omega⟩ := hf (by simp [Fin.lt_def])
    simp only at h1 ⊢
    omega

theorem CombSortShift.proof (h1 : CombSortLe.Statement) : CombSortShift.Statement := by
  intro m lam hlam q i hq hinj
  set u := Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) with hu
  obtain ⟨σ, hσ⟩ := exists_perm_strictAnti hinj
  have hge : ∀ k : Fin m, stair m k ≤ u (σ k) := by
    intro k
    have hk := add_index_le_of_strictAnti hσ k ⟨m - 1, by have := k.isLt; omega⟩ (by rw [Fin.le_def]; exact Nat.le_sub_one_of_lt k.isLt)
    simp only [Function.comp_apply] at hk
    simp only [stair]
    omega
  refine ⟨σ, fun k => u (σ k) - stair m k, ?_, ?_, ?_⟩
  · intro a b hab
    have h := add_index_le_of_strictAnti hσ a b hab
    have ha := hge a
    have hb := hge b
    simp only [Function.comp_apply, stair] at h ha hb ⊢
    omega
  · intro k
    have hl : Antitone (fun j => lam j + stair m j) := by
      intro a b hab
      have := hlam hab
      simp only [stair]
      have : (a : ℕ) ≤ b := hab
      omega
    have hul : ∀ j, u j ≤ lam j + stair m j := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [hu]
      · simp [hu, Function.update_of_ne hj]
    have := h1 m u (fun j => lam j + stair m j) σ hl hul hσ.antitone k
    show u (σ k) - stair m k ≤ lam k
    omega
  · intro k
    have := hge k
    show u (σ k) = u (σ k) - stair m k + stair m k
    omega

end Comb

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortShiftDistinct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Equiv

theorem CombSortShiftDistinct.proof : CombSortShiftDistinct.Statement := by
  intro m l hl q hq i j hij hqi hqj σ τ heq
  have hr := congrArg Set.range heq
  rw [σ.surjective.range_comp, τ.surjective.range_comp] at hr
  have hmem : l i ∈ Set.range (Function.update l j (l j - q)) :=
    ⟨i, by rw [Function.update_of_ne hij]⟩
  rw [← hr] at hmem
  obtain ⟨k, hk⟩ := hmem
  by_cases hki : k = i
  · subst hki
    rw [Function.update_self] at hk
    omega
  · rw [Function.update_of_ne hki] at hk
    exact hki (hl hk)

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombStripSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

theorem CombStripSum.proof (h1 : CombCfAtStair.Statement) (h2 : CombSortShift.Statement)
    (h3 : CombSortShiftDistinct.Statement) (h4 : CombExtendWord.Statement) :
    CombStripSum.Statement := by
  classical
  intro m n q lam hlam hq
  set l : Fin m → ℕ := fun j => lam j + stair m j with hl
  have hAlt : IsAlt (alternantPsum m (List.replicate n 1)) := isAlt_vandermonde_mul_prod _
  have hl_inj : Function.Injective l := by
    intro a b hab
    simp only [hl, stair] at hab
    have ha := a.isLt
    have hb := b.isLt
    rcases lt_trichotomy a b with h | h | h
    · have h' := hlam h.le
      have : (a : ℕ) < b := h
      omega
    · exact h
    · have h' := hlam h.le
      have : (b : ℕ) < a := h
      omega

  have key : ∀ i : Fin m, q ≤ l i → Function.Injective (Function.update l i (l i - q)) →
      ∃ μ : Fin m → ℕ, ∃ s : Fin q → Fin m,
        (∃ σ : Perm (Fin m), ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k) ∧
        |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| =
          ((latticeWords n μ).card : ℚ) ∧
        ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam := by
    intro i hqi hinj
    obtain ⟨σ, μ, hμ, hμle, hσ0⟩ := h2 m lam hlam q i hqi hinj
    have hσ : ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k := hσ0
    have hsum : ∑ k, lam k = ∑ k, μ k + q := by
      have e1 : ∑ k, (μ k + stair m k) = ∑ k, Function.update l i (l i - q) k := by
        rw [← Equiv.sum_comp σ (Function.update l i (l i - q))]
        exact Finset.sum_congr rfl fun k _ => (hσ k).symm
      have e4 : ∑ k, l k = ∑ k, lam k + ∑ k, stair m k := Finset.sum_add_distrib
      have e3 : ∀ k, l k = Function.update l i (l i - q) k + if k = i then q else 0 := by
        intro k
        by_cases hk : k = i
        · subst hk; simp only [Function.update_self, if_true]; omega
        · simp [hk]
      have e2 : ∑ k, l k = ∑ k, Function.update l i (l i - q) k + q := by
        rw [Finset.sum_congr rfl (fun k _ => e3 k), Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
      rw [Finset.sum_add_distrib] at e1
      omega
    obtain ⟨s, hs⟩ := h4 m n q μ lam hμ hlam hμle hsum
    refine ⟨μ, s, ⟨σ, hσ⟩, ?_, hs⟩
    have hu : Function.update l i (l i - q) = (fun k => μ k + stair m k) ∘ σ.symm := by
      funext k
      rw [Function.comp_apply, ← hσ (σ.symm k), Equiv.apply_symm_apply]
    rw [hu, cf_perm hAlt, abs_mul, h1 m n μ hμ]
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]
  have key' : ∀ i : Fin m, ∃ μ : Fin m → ℕ, ∃ s : Fin q → Fin m,
      (q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))) →
        (∃ σ : Perm (Fin m), ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k) ∧
        |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| =
          ((latticeWords n μ).card : ℚ) ∧
        ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam := by
    intro i
    by_cases h : q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))
    · obtain ⟨μ, s, hs⟩ := key i h.1 h.2
      exact ⟨μ, s, fun _ => hs⟩
    · exact ⟨fun _ => 0, fun _ => i, fun h' => absurd h' h⟩
  choose μ s hμs using key'
  set S := univ.filter
    (fun i : Fin m => q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))) with hS
  change ∑ i : Fin m, (if q ≤ l i then
      |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| else 0) ≤ _
  have hsum_eq : ∑ i : Fin m, (if q ≤ l i then
      |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| else 0) =
      ∑ i ∈ S, ((latticeWords n (μ i)).card : ℚ) := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hqi : q ≤ l i
    · by_cases hinj : Function.Injective (Function.update l i (l i - q))
      · rw [if_pos hqi, if_pos ⟨hqi, hinj⟩, (hμs i ⟨hqi, hinj⟩).2.1]
      · rw [if_pos hqi, if_neg (fun h => hinj h.2)]
        simp only [Function.Injective, not_forall] at hinj
        obtain ⟨a, b, hab, hne⟩ := hinj
        rw [cf_eq_zero_of_eq hAlt hne hab, abs_zero]
    · rw [if_neg hqi, if_neg (fun h => hqi h.1)]
  rw [hsum_eq]
  have hcard : ∑ i ∈ S, (latticeWords n (μ i)).card ≤ (latticeWords (n + q) lam).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn (fun x => Fin.append x.2 (s x.1)) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_sigma] at hx
      exact (hμs x.1 (Finset.mem_filter.mp hx.1).2).2.2 x.2 hx.2
    · rintro ⟨i, w⟩ hx ⟨j, w'⟩ hy hxy
      rw [Finset.mem_coe, Finset.mem_sigma] at hx hy
      simp only at hxy hx hy
      have hw : w = w' := by
        funext k
        have := congrFun hxy (Fin.castAdd q k)
        simpa only [Fin.append_left] using this
      subst hw
      have hμij : μ i = μ j := by
        funext k
        have a1 := (Finset.mem_filter.mp hx.2).2.2 k
        have a2 := (Finset.mem_filter.mp hy.2).2.2 k
        rw [← a1, ← a2]
      have hSi := (Finset.mem_filter.mp hx.1).2
      have hSj := (Finset.mem_filter.mp hy.1).2
      have hij : i = j := by
        by_contra hij
        obtain ⟨σ, hσ⟩ := (hμs i hSi).1
        obtain ⟨τ, hτ⟩ := (hμs j hSj).1
        refine h3 m l hl_inj q hq i j hij hSi.1 hSj.1 σ τ ?_
        funext k
        rw [Function.comp_apply, Function.comp_apply, hσ k, hτ k, hμij]
      subst hij
      rfl
  exact_mod_cast hcard

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauOfWord
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauOfWord.proof (h1 : CombCellOfWordMem.Statement)
    (h2 : CombCellOfWordInj.Statement) (h3 : CombCellOfWordMono.Statement) :
    CombTableauOfWord.Statement := by
  intro m lam _hlam w hw
  have hL : IsLattice w := by
    simp only [latticeWords, mem_filter] at hw
    exact hw.2.1
  let f : Fin (youngCells lam).card → youngCells lam := fun t => ⟨cellOfWord w t, h1 m lam w hw t⟩
  have hinj : Function.Injective f := by
    intro s t hst
    exact h2 m _ w (congrArg Subtype.val hst)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp⟩
  let T : youngCells lam ≃ Fin (youngCells lam).card := (Equiv.ofBijective f hbij).symm
  have hT : ∀ p : youngCells lam, cellOfWord w (T p) = p.1 := by
    intro p
    have : f (T p) = p := (Equiv.ofBijective f hbij).apply_symm_apply p
    exact congrArg Subtype.val this
  refine ⟨T, ?_, ?_⟩
  · intro p q hpq1 hpq2
    apply h3 m _ w hL
    · rw [hT p, hT q]; exact hpq1
    · rw [hT p, hT q]; exact hpq2
  · funext t
    show (T.symm t).1.1 = w t
    rfl

end GroundTheory.Heights₂.Heights.RestTerms
end

