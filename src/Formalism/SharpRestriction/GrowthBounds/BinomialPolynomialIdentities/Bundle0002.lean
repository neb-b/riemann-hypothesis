module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.IndexOffRange
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem hstrip_iff {n : ℕ} (nu mu : Fin n → ℤ) (b : ℕ) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip mu nu b ↔ Formalism.MainNotions.G.HStrip nu mu b := by
  unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip Formalism.MainNotions.G.HStrip
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h a ha
      exact h a ⟨a.1 + 1, ha⟩ rfl
    · intro h m m' hm
      have hlt : m.1 + 1 < n := by rw [hm]; exact m'.2
      have : m' = ⟨m.1 + 1, hlt⟩ := Fin.ext hm.symm
      rw [this]; exact h m hlt
  · rw [Finset.sum_sub_distrib]

theorem ext_of_lt {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) {i : ℕ} (h : i < N + 1) : ext mu i = mu ⟨i, h⟩ := by
  unfold ext; rw [dite_eq_left h]

theorem isV_of_lt {N : ℕ} (LL : Letters (Fin N)) {i : ℕ} (h : i < N) : isV LL i = LL.vec ⟨i, h⟩ := by
  unfold isV; rw [dite_eq_left h]

theorem Bn_of_lt {N : ℕ} (B : Fin N → ℕ) {i : ℕ} (h : i < N) : Bn B i = B ⟨i, h⟩ := by
  unfold Bn; rw [dite_eq_left h]

theorem restPathTo : RestPathTo := by
  intro n N LL B P
  refine ⟨?_, ?_, ?_⟩
  · rw [ext_of_lt _ (Nat.succ_pos N)]; exact P.zero
  · intro i hi
    rw [ext_of_lt _ (Nat.lt_succ_of_le hi)]; exact P.dom _
  · intro i hi
    have hs := P.step ⟨i, hi⟩
    rw [isV_of_lt LL hi, Bn_of_lt B hi, ext_of_lt P.mu (show i < N + 1 by omega),
      ext_of_lt P.mu (show i + 1 < N + 1 by omega)]
    have e1 : (⟨i, hi⟩ : Fin N).castSucc = ⟨i, by omega⟩ := rfl
    have e2 : (⟨i, hi⟩ : Fin N).succ = ⟨i + 1, by omega⟩ := rfl
    rw [e1, e2] at hs
    split_ifs at hs ⊢ with hv
    · exact (hstrip_iff _ _ _).2 hs
    · exact (hstrip_iff _ _ _).2 hs

theorem restPathFrom : RestPathFrom := by
  intro n N LL B μ hμ
  obtain ⟨h0, hd, hs⟩ := hμ
  refine ⟨⟨res N μ, ?_, ?_, ?_⟩, rfl⟩
  · exact h0
  · intro i
    exact hd i.val (Nat.le_of_lt_succ i.2)
  · intro i
    have h := hs i.val i.2
    rw [isV_of_lt LL i.2, Bn_of_lt B i.2] at h
    have e1 : res N μ i.castSucc = μ i.val := rfl
    have e2 : res N μ i.succ = μ (i.val + 1) := rfl
    rw [e1, e2]
    have e3 : (⟨i.val, i.2⟩ : Fin N) = i := rfl
    rw [e3] at h
    split_ifs at h ⊢ with hv
    · exact (hstrip_iff _ _ _).1 h
    · exact (hstrip_iff _ _ _).1 h

theorem tabCol_eq {n : ℕ} (I : ℤ → Finset (Fin n)) (c : ℤ) : tabCol I c = Formalism.InvariantFactorPaths.GelfandTsetlinBases.hatIdx I c := by
  unfold tabCol Formalism.InvariantFactorPaths.GelfandTsetlinBases.hatIdx
  split_ifs
  · rfl
  · exact (Finset.compl_eq_univ_sdiff _).symm

theorem cnt_succ {n : ℕ} (A : Finset (Fin n)) (t : Fin n) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt A (t.val + 1) = (A.filter (· ≤ t)).card := by
  unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt
  congr 1

theorem dom_iff_le {n : ℕ} (A B : Finset (Fin n)) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.Dom A B ↔ ∀ t : Fin n, (B.filter (· ≤ t)).card ≤ (A.filter (· ≤ t)).card := by
  constructor
  · intro h t
    rw [← cnt_succ, ← cnt_succ]; exact h _
  · intro h x
    rcases x with _ | y
    · simp [Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt]
    · by_cases hy : y < n
      · have := h ⟨y, hy⟩
        rw [← cnt_succ, ← cnt_succ] at this
        exact this
      · have hn : n ≤ y + 1 := by omega
        rw [Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le A hn, Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le B hn]
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          have : B = ∅ := by ext a; exact a.elim0
          rw [this]; simp
        · have := h ⟨n - 1, by omega⟩
          rw [← cnt_succ, ← cnt_succ] at this
          have e : n - 1 + 1 = n := by omega
          simp only [e] at this
          rwa [Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le A le_rfl, Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le B le_rfl] at this

theorem index_off_range {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n))
    (h : ∀ c, (I c).card = if 1 ≤ c then colH (pEnd mu) c else n - colH (pEnd mu) c) (c : ℤ)
    (hc : c ∉ colRange mu) : I c = ∅ := by
  rw [← Finset.card_eq_zero, h c]
  have hT : ∀ m, |pEnd mu m| ≤ ∑ i, ∑ m, |mu i m| := fun m => Formalism.MainNotions.LemmaBAlt.abs_entry_le_total mu (Fin.last N) m
  have hT0 : (0 : ℤ) ≤ ∑ i, ∑ m, |mu i m| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  simp only [colRange, Finset.mem_Icc, not_and_or, not_le] at hc
  rcases hc with hc | hc
  · rw [if_neg (by omega)]
    have : colH (pEnd mu) c = n := by
      unfold colH
      rw [Finset.filter_true_of_mem]
      · simp
      · intro m _
        have := neg_abs_le (pEnd mu m)
        have := hT m
        omega
    omega
  · rw [if_pos (by omega)]
    unfold colH
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _
    have := le_abs_self (pEnd mu m)
    have := hT m
    omega

theorem restStd : RestStd := by
  intro n N mu I
  unfold IsSt Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsStd
  constructor
  · rintro ⟨_, h2, h3⟩
    refine ⟨h2, fun c => ?_⟩
    rw [Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.dom_iff, dom_iff_le]
    intro t
    rw [← tabCol_eq, ← tabCol_eq]
    exact h3 c t
  · rintro ⟨h2, h3⟩
    refine ⟨index_off_range mu I h2, h2, fun c t => ?_⟩
    have := (dom_iff_le _ _).1 ((Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.dom_iff _ _).1 (h3 c)) t
    rw [← tabCol_eq, ← tabCol_eq] at this
    exact this

end Formalism.MainNotions.G.ColumnFamilies
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.KcolEqPathWord
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt

theorem wedgeR_eq_wedgeF {n : ℕ} {P : Type*} [CommRing P] (x : Fin n → P) (K : Finset (Fin n) → P) :
    wedgeR x K = Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF K x := by
  funext J
  unfold wedgeR Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

theorem contrR_eq_contrF {n : ℕ} {P : Type*} [CommRing P] (x : Fin n → P) (K : Finset (Fin n) → P) :
    contrR x K = Formalism.InvariantFactorPaths.GelfandTsetlinBases.contrF K x := by
  funext J
  unfold contrR Formalism.InvariantFactorPaths.GelfandTsetlinBases.contrF Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg
  rw [Finset.compl_eq_univ_sdiff]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

theorem colHeight_eq {n : ℕ} (mu : Fin n → ℤ) (c : ℤ) : Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight mu c = colH mu c := rfl

theorem ext_apply {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (j : ℕ) (h : j < N + 1) : ext mu j = mu ⟨j, h⟩ := by
  unfold ext; rw [dite_eq_left h]

theorem colH_step {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (P : PPath n N LL B) (c : ℤ) (j : ℕ) (h : j < N) :
    if LL.vec ⟨j, h⟩ then colH (P.mu ⟨j, by omega⟩) c ≤ colH (P.mu ⟨j + 1, by omega⟩) c
    else colH (P.mu ⟨j + 1, by omega⟩) c ≤ colH (P.mu ⟨j, by omega⟩) c := by
  have hs := P.step ⟨j, h⟩
  have e1 : (Fin.castSucc (⟨j, h⟩ : Fin N)) = ⟨j, by omega⟩ := rfl
  have e2 : (Fin.succ (⟨j, h⟩ : Fin N)) = ⟨j + 1, by omega⟩ := rfl
  rw [e1, e2] at hs
  split_ifs with hv
  · rw [if_pos hv] at hs
    exact column_height_mono hs.1 c
  · rw [if_neg hv] at hs
    exact column_height_mono hs.1 c

theorem Kcol_eq_pathWord (R : Type*) [CommRing R] {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ}
    (P : PPath n N LL B) (c : ℤ) (j : ℕ) (hj : j ≤ N) (J : Finset (Fin n)) :
    rename (iv N n) (Kcol R P.mu c j J) =
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord (isV LL) (ext P.mu) c
        (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) j J := by
  induction j generalizing J with
  | zero =>
    simp only [Kcol, Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord]
    exact map_exterior_one (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom J
  | succ j ih =>
    have h : j < N := hj
    have ih' := ih (by omega)
    simp only [Kcol, Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord]
    rw [dite_eq_left h]
    have hm := map_column_operator (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom c
      (colH (P.mu ⟨j, by omega⟩) c) (colH (P.mu ⟨j + 1, by omega⟩) c) (letVec R ⟨j, h⟩) (Kcol R P.mu c j) J
    have h1 : (fun m => (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom
        (letVec R (⟨j, h⟩ : Fin N) m)) = fun a => (X (j, a) : MvPolynomial (ℕ × Fin n) R) := by
      funext m; simp [letVec, iv]
    have h2 : (fun J => (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom
        (Kcol R P.mu c j J)) = Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord (isV LL) (ext P.mu) c
        (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) j := funext ih'
    rw [h1, h2] at hm
    have hm' : rename (iv N n) (colStep c (colH (P.mu ⟨j, by omega⟩) c) (colH (P.mu ⟨j + 1, by omega⟩) c)
        (letVec R ⟨j, h⟩) (Kcol R P.mu c j) J) = _ := hm
    rw [hm', colHeight_eq, colHeight_eq, ext_apply P.mu j (by omega), ext_apply P.mu (j + 1) (by omega)]
    have hst := colH_step P c j h
    have hV : isV LL j = LL.vec ⟨j, h⟩ := by unfold isV; rw [dite_eq_left h]
    rw [hV]
    unfold colStep Formalism.InvariantFactorPaths.GelfandTsetlinBases.stepF
    by_cases hv : LL.vec ⟨j, h⟩ = true
    · rw [if_pos hv] at hst
      rw [hv]
      by_cases he : colH (P.mu ⟨j + 1, by omega⟩) c = colH (P.mu ⟨j, by omega⟩) c
      · rw [if_pos he, if_neg (by omega), if_neg (by omega)]
      · rw [if_neg he, if_pos (by omega)]
        by_cases hc : 1 ≤ c
        · simp [hc, wedgeR_eq_wedgeF]
        · simp [hc, contrR_eq_contrF]
    · rw [if_neg hv] at hst
      have hv' : LL.vec ⟨j, h⟩ = false := by simpa using hv
      rw [hv']
      by_cases he : colH (P.mu ⟨j + 1, by omega⟩) c = colH (P.mu ⟨j, by omega⟩) c
      · rw [if_pos he, if_neg (by omega), if_neg (by omega)]
      · rw [if_neg he, if_neg (by omega), if_pos (by omega)]
        by_cases hc : 1 ≤ c
        · simp [hc, contrR_eq_contrF]
        · simp [hc, wedgeR_eq_wedgeF]

theorem colH_off {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) {c : ℤ} (hc : c ∉ colRange mu) (i : Fin (N + 1)) :
    colH (mu i) c = if 1 ≤ c then 0 else n := by
  have hT : ∀ m, |mu i m| ≤ ∑ i, ∑ m, |mu i m| := fun m => abs_entry_le_total mu i m
  have hT0 : (0 : ℤ) ≤ ∑ i, ∑ m, |mu i m| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  simp only [colRange, Finset.mem_Icc, not_and_or, not_le] at hc
  unfold colH
  rcases hc with hc | hc
  · rw [if_neg (by omega)]
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro m _
    have := abs_le.mp (hT m)
    omega
  · rw [if_pos (by omega)]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _
    have := abs_le.mp (hT m)
    omega

theorem pathWord_off (R : Type*) [CommRing R] {n N : ℕ} (isVec : ℕ → Bool) (mu : Fin (N + 1) → Fin n → ℤ) {c : ℤ}
    (hc : c ∉ colRange mu) (Xr : ℕ → Fin n → R) (j : ℕ) (hj : j ≤ N) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec (ext mu) c Xr j = Formalism.InvariantFactorPaths.GelfandTsetlinBases.oneF := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord]
    rw [colHeight_eq, colHeight_eq, ext_apply mu j (by omega), ext_apply mu (j + 1) (by omega),
      colH_off mu hc, colH_off mu hc, if_pos rfl]
    exact ih (by omega)

theorem restPsi : RestPsi := by
  intro R _ n N LL B P I hI
  unfold Psi Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath
  rw [map_prod]
  rw [finprod_eq_prod_of_mulSupport_subset (s := colRange P.mu)]
  · exact Finset.prod_congr rfl fun c _ => Kcol_eq_pathWord R P c N le_rfl (I c)
  · intro c hc
    by_contra hcn
    apply hc
    have hcn' : c ∉ colRange P.mu := hcn
    show Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord (isV LL) (ext P.mu) c _ N (I c) = 1
    rw [pathWord_off _ _ _ hcn' _ N le_rfl]
    have hcard := hI c
    rw [colHeight_eq] at hcard
    have h0 : colH (pEnd P.mu) c = if 1 ≤ c then 0 else n := colH_off P.mu hcn' (Fin.last N)
    have : (I c).card = 0 := by
      rw [hcard, h0]
      split_ifs <;> simp
    rw [Finset.card_eq_zero] at this
    rw [this]
    simp [Formalism.InvariantFactorPaths.GelfandTsetlinBases.oneF]

end Formalism.MainNotions.G.ColumnFamilies
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.PeBnOfLt
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem iv_inj (N n : ℕ) : Function.Injective (iv N n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [iv, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) h.2

theorem pe_Bn_of_lt {N : ℕ} (B : Fin N → ℕ) {i : ℕ} (h : i < N) : Bn B i = B ⟨i, h⟩ := by simp [Bn, h]

theorem expSet_eq (n N : ℕ) (B : Fin N → ℕ) :
    (fun m : Fin N × Fin n →₀ ℕ => m.mapDomain (iv N n)) '' {m | ∀ i, multideg m i = B i} =
      {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then Bn B i else 0} := by
  ext e
  constructor
  · rintro ⟨m, hm, rfl⟩ i
    by_cases h : i < N
    · rw [if_pos h, pe_Bn_of_lt B h, ← hm ⟨i, h⟩]
      unfold multideg
      refine Finset.sum_congr rfl fun a _ => ?_
      have : ((i, a) : ℕ × Fin n) = iv N n (⟨i, h⟩, a) := rfl
      rw [this, Finsupp.mapDomain_apply_of_injective (iv_inj N n)]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun a _ => ?_
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨⟨x, y⟩, hxy⟩
      simp only [iv, Prod.mk.injEq] at hxy
      exact h (hxy.1 ▸ x.2)
  · intro he
    have hsupp : (↑e.support : Set (ℕ × Fin n)) ⊆ Set.range (iv N n) := by
      rintro ⟨i, a⟩ hia
      by_cases h : i < N
      · exact ⟨(⟨i, h⟩, a), rfl⟩
      · exfalso
        have h0 := he i
        rw [if_neg h] at h0
        have := (Finset.sum_eq_zero_iff.mp h0) a (Finset.mem_univ a)
        simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hia
        exact hia this
    refine ⟨e.comapDomain (iv N n) (iv_inj N n).injOn, ?_, Finsupp.mapDomain_comapDomain _ (iv_inj N n) e hsupp⟩
    intro i
    have h0 := he i.val
    rw [if_pos i.2, pe_Bn_of_lt B i.2] at h0
    rw [← h0]
    unfold multideg
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.comapDomain_apply]
    rfl

theorem restPol : RestPol := by
  intro R _ n N B
  rw [(Formalism.InvariantFactorPaths.GelfandTsetlinBases.polynomial_b_rank n N (Bn B)).2.2 R, ← expSet_eq, Pol, MvPolynomial.restrictSupport_eq_span,
    Submodule.map_span, Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro m _
  simp [rename_monomial]

end Formalism.MainNotions.G.ColumnFamilies
end
end

