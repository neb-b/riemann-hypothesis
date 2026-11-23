module

public import Formalism.GradedWeylDivisibility.Bundle0001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0004
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0005
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0001

@[expose] public section

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelDegBound
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem aeval_eq_self_of_eq_X_on_vars {τ B : Type*} [CommRing B] (g : τ → MvPolynomial τ B)
    (p : MvPolynomial τ B) (h : ∀ i ∈ p.vars, g i = X i) : aeval g p = p := by
  have key := hom_congr_vars (f₁ := (aeval g : MvPolynomial τ B →ₐ[B] MvPolynomial τ B).toRingHom)
    (f₂ := RingHom.id _) (p₁ := p) (p₂ := p) (RingHom.ext fun b => by simp [algebraMap_eq])
    (fun i hi _ => by simpa using h i hi) rfl
  simpa using key

private theorem degreeOf_eq_zero_of_not_mem_vars {τ B : Type*} [CommRing B] (i : τ)
    (p : MvPolynomial τ B) (h : i ∉ p.vars) : degreeOf i p = 0 := by
  refine Nat.le_zero.1 (degreeOf_le_iff.2 fun m hm => ?_)
  by_contra hne
  exact h ((MvPolynomial.mem_vars_iff_mem_support i).2 ⟨m, hm, Finsupp.mem_support_iff.2 (by omega)⟩)

private theorem not_mem_vars_of_degreeOf_eq_zero {τ B : Type*} [CommRing B] (i : τ)
    (p : MvPolynomial τ B) (h : degreeOf i p = 0) : i ∉ p.vars := by
  intro hi
  obtain ⟨m, hm, hmi⟩ := (MvPolynomial.mem_vars_iff_mem_support i).1 hi
  have h1 := degreeOf_le_iff.1 h.le m hm
  exact Finsupp.mem_support_iff.1 hmi (by omega)

private theorem le_and_degreeOf_top_le_of_degreeOf_sum_le {B τ : Type} [CommRing B] [IsDomain B] [DecidableEq τ]
    (hE : EvalDeg) (x y c : τ) (hxy : x ≠ y) (hxc : x ≠ c) (hyc : y ≠ c) (K e s : ℕ)
    (W : ℕ → MvPolynomial τ B) (hW : ∀ k, ∀ i ∈ (W k).vars, i ≠ x ∧ i ≠ y) (hWK : W K ≠ 0)
    (hs : degreeOf c ((X y + X c * X x) ^ e *
      ∑ k ∈ Finset.range (K + 1), X x ^ k * (X y + X c * X x) ^ (K - k) * W k) ≤ s) :
    e ≤ s ∧ degreeOf c (W K) ≤ s - e + K := by
  obtain ⟨Y, hY⟩ : ∃ Y : MvPolynomial τ B, Y = X y + X c * X x := ⟨_, rfl⟩
  rw [← hY] at hs
  obtain ⟨Q, hQ⟩ : ∃ Q : MvPolynomial τ B,
      Q = ∑ k ∈ Finset.range (K + 1), X x ^ k * Y ^ (K - k) * W k := ⟨_, rfl⟩
  rw [← hQ] at hs
  have hX : ∀ v : τ, (X v : MvPolynomial τ B) ≠ 0 := by
    intro v hv
    have h1 : degreeOf v (0 : MvPolynomial τ B) ≤ 0 := degreeOf_le_iff.2 fun m hm => by simp at hm
    rw [← hv, degreeOf_X] at h1
    simp at h1
  have hYσ : aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c else X v)
      Y = 0 := by
    rw [hY]; simp [hxy.symm, hxc.symm, hyc.symm]
  have hWσ : ∀ k, aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c
      else X v) (W k) = W k := by
    intro k
    refine aeval_eq_self_of_eq_X_on_vars _ _ fun i hi => ?_
    simp [(hW k i hi).1, (hW k i hi).2]
  have hsum : aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c
      else X v) Q = W K := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hQ, map_sum, Finset.sum_eq_single K]
    · rw [Nat.sub_self, pow_zero, mul_one, map_mul, map_pow, hWσ, aeval_X]
      simp
    · intro k hk hkK
      have hk' : K - k ≠ 0 := by
        rw [Finset.mem_range] at hk; omega
      simp only [map_mul, map_pow, hYσ, zero_pow hk', mul_zero, zero_mul]
    · intro h; exact absurd (Finset.self_mem_range_succ K) h
  have hQ0 : Q ≠ 0 := by
    intro h; rw [h, map_zero] at hsum; exact hWK hsum.symm
  have hcY : 1 ≤ degreeOf c Y := by
    by_contra hlt
    have h0 : degreeOf c Y = 0 := by omega
    have hfix : aeval (fun v : τ => if v = c then (0 : MvPolynomial τ B) else X v) Y = Y := by
      refine aeval_eq_self_of_eq_X_on_vars _ _ fun i hi => ?_
      have hic : i ≠ c := fun h => not_mem_vars_of_degreeOf_eq_zero c Y h0 (by rwa [h] at hi)
      simp [hic]
    have h2 : (X c : MvPolynomial τ B) * X x = 0 := by
      have h3 : aeval (fun v : τ => if v = c then (0 : MvPolynomial τ B) else X v)
          (X y + X c * X x : MvPolynomial τ B) = X y := by
        simp [hyc, hxc]
      rw [← hY, hfix, hY] at h3
      linear_combination h3
    exact mul_ne_zero (hX c) (hX x) h2
  have hY0 : Y ≠ 0 := by
    rintro rfl
    have h1 : degreeOf c (0 : MvPolynomial τ B) ≤ 0 := degreeOf_le_iff.2 fun m hm => by simp at hm
    omega
  have hyQ : degreeOf y Q ≤ K := by
    rw [hQ]
    refine Finset.sum_induction _ (fun q => degreeOf y q ≤ K)
      (fun a b ha hb => (degreeOf_add_le y a b).trans (max_le ha hb))
      (degreeOf_le_iff.2 fun m hm => by simp at hm) ?_
    intro k _
    show degreeOf y (X x ^ k * Y ^ (K - k) * W k) ≤ K
    have h1 := degreeOf_mul_le y (X x ^ k * Y ^ (K - k)) (W k)
    have h2 := degreeOf_mul_le y (X x ^ k) (Y ^ (K - k))
    have h3 := degreeOf_pow_le y (X x : MvPolynomial τ B) k
    have h4 := degreeOf_pow_le y Y (K - k)
    have h5 : degreeOf y (X x : MvPolynomial τ B) = 0 := by
      rw [degreeOf_X]; simp [hxy.symm]
    have h6 : degreeOf y Y ≤ 1 := by
      rw [hY]
      refine (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
      · rw [degreeOf_X]; split_ifs <;> omega
      · refine (degreeOf_mul_le _ _ _).trans ?_
        rw [degreeOf_X, degreeOf_X]
        simp [hyc, hxy.symm]
    have h7 : degreeOf y (W k) = 0 :=
      degreeOf_eq_zero_of_not_mem_vars y (W k) fun hi => (hW k y hi).2 rfl
    rw [h5, mul_zero] at h3
    have h8 : (K - k) * degreeOf y Y ≤ K - k := by
      simpa using Nat.mul_le_mul_left (K - k) h6
    generalize (K - k) * degreeOf y Y = t at h4 h8
    omega
  have key : degreeOf c (W K) ≤ degreeOf c Q + degreeOf y Q := by
    convert hE B τ x y c hxy hxc hyc Q using 2
    exact hsum.symm
  rw [degreeOf_mul_eq (pow_ne_zero _ hY0) hQ0, degreeOf_pow_eq c Y e hY0] at hs
  have he : e ≤ e * degreeOf c Y := by simpa using Nat.mul_le_mul_left e hcY
  generalize e * degreeOf c Y = t at hs he
  constructor <;> omega

theorem peelDegBound_of (hE : EvalDeg) : PeelDegBound := by
  intro B _ _ r n l j hlj a0 K e s w hw hK hs
  have hφX : ∀ v : Fin r × Fin n, colAddGen B l j (X v : MvPolynomial (Fin r × Fin n) B) =
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) := by
    intro v; simp only [colAddGen, aeval_X]
  have hinj : ∀ f : MvPolynomial (Fin r × Fin n) B, colAddGen B l j f = 0 → f = 0 := by
    intro f hf
    have hl : (aeval (fun v : Option (Fin r × Fin n) => v.elim (0 : MvPolynomial (Fin r × Fin n) B) X)).comp
        (colAddGen B l j) = AlgHom.id B _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [AlgHom.comp_apply, AlgHom.id_apply, hφX]
      split_ifs <;> simp
    have h1 := congrArg (aeval (fun v : Option (Fin r × Fin n) =>
      v.elim (0 : MvPolynomial (Fin r × Fin n) B) X)) hf
    rw [map_zero, ← AlgHom.comp_apply, hl, AlgHom.id_apply] at h1
    exact h1
  have hvars : ∀ k, ∀ i ∈ (colAddGen B l j (w k)).vars,
      i ≠ some (a0, l) ∧ i ≠ some (a0, j) := by
    intro k i hi
    have hi2 : i ∈ ((bind₁ fun v : Fin r × Fin n => if v.2 = j then
        (X (some v) + X none * X (some (v.1, l)) : MvPolynomial (Option (Fin r × Fin n)) B)
        else X (some v)) (w k)).vars := by
      rw [← aeval_eq_bind₁]; exact hi
    have hi3 := vars_bind₁ _ _ hi2
    rw [Finset.mem_biUnion] at hi3
    obtain ⟨v, hv, hiv⟩ := hi3
    obtain ⟨m, hm, hmv⟩ := (MvPolynomial.mem_vars_iff_mem_support v).1 hv
    have hvl : v ≠ (a0, l) := by
      rintro rfl; exact (Finsupp.mem_support_iff.1 hmv) (hw k m hm).1
    have hvj : v ≠ (a0, j) := by
      rintro rfl; exact (Finsupp.mem_support_iff.1 hmv) (hw k m hm).2
    split_ifs at hiv with hv2
    · rcases Finset.mem_union.1 (vars_add_subset _ _ hiv) with h1 | h1
      · rw [vars_X, Finset.mem_singleton] at h1
        subst h1; simp [hvl, hvj]
      · rcases Finset.mem_union.1 (vars_mul _ _ h1) with h2 | h2
        · rw [vars_X, Finset.mem_singleton] at h2
          subst h2; simp
        · rw [vars_X, Finset.mem_singleton] at h2
          subst h2
          refine ⟨fun h => ?_, by simp [hlj]⟩
          simp only [Option.some.injEq, Prod.mk.injEq, and_true] at h
          exact hvj (Prod.ext h hv2)
    · rw [vars_X, Finset.mem_singleton] at hiv
      subst hiv; simp [hvl, hvj]
  have e1 : colAddGen B l j (X (a0, l) : MvPolynomial (Fin r × Fin n) B) = X (some (a0, l)) := by
    rw [hφX]; simp [hlj]
  have e2 : colAddGen B l j (X (a0, j) : MvPolynomial (Fin r × Fin n) B) =
      X (some (a0, j)) + X none * X (some (a0, l)) := by
    rw [hφX]; simp
  have hQ : colAddGen B l j
      (∑ k ∈ Finset.range (K + 1), X (a0, l) ^ k * X (a0, j) ^ (e + (K - k)) * w k) =
      (X (some (a0, j)) + X none * X (some (a0, l))) ^ e * ∑ k ∈ Finset.range (K + 1),
        X (some (a0, l)) ^ k * (X (some (a0, j)) + X none * X (some (a0, l))) ^ (K - k) *
          colAddGen B l j (w k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, e1, e2, pow_add]
    ring
  rw [hQ] at hs
  exact le_and_degreeOf_top_le_of_degreeOf_sum_le hE (some (a0, l)) (some (a0, j)) none (by simp [hlj]) (by simp) (by simp)
    K e s (fun k => colAddGen B l j (w k)) hvars (fun h => hK (hinj _ h)) hs

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelLead
section
open MvPolynomial
open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem toLex_lt_of_eq_of_lt_at {N : ℕ} {a b : Fin N →₀ ℕ} (i : Fin N)
    (h1 : ∀ i', i' < i → a i' = b i') (h2 : a i < b i) : toLex a < toLex b := by
  exact Finsupp.lex_def.2 ⟨i, h1, h2⟩

private theorem domCongr_cmIdx_apply_eq {r n : ℕ} (m : Fin r × Fin n →₀ ℕ)
    (x : Fin r × Fin n) :
    Finsupp.domCongr (cmIdx r n) m (cmIdx r n x) = m x := by
  simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]

private theorem toSyn_le_toSyn_degree_of_mem_support {σ R : Type*} [CommSemiring R] (M : MonomialOrder σ)
    {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    M.toSyn d ≤ M.toSyn (M.degree f) := by
  exact M.le_degree hd

theorem sliceLeading : PeelLead := by
  unfold PeelLead
  intro B _ _ r n l j hlj a0 ω g K hg hω hK htop
  have hlj' : l ≠ j := ne_of_lt hlj
  have hd : (colLex r n).degree (peel l j a0 K g) ∈
      (peel l j a0 K g).support :=
    (colLex r n).degree_mem_support hK
  obtain ⟨m0, hm0, hm0K, hd_eq⟩ := lcplead_mem_support_peel a0 K hd
  have hm0_eq := lcplead_recon hlj' a0 hg hm0
  rw [hm0K, ← hd_eq] at hm0_eq
  rw [← hm0_eq]
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hm0
  have hup : ∀ m ∈ g.support, (colLex r n).toSyn m ≤ (colLex r n).toSyn m0 := by
    intro m hm
    rcases lt_trichotomy (m (a0, l)) K with hlt | heq | hgt
    · apply le_of_lt
      apply colLex_lt_iff.2
      refine toLex_lt_of_eq_of_lt_at (cmIdx r n (a0, l)) ?_ ?_
      · intro i' hi'
        obtain ⟨⟨b, t⟩, rfl⟩ := (cmIdx r n).surjective i'
        rw [domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq]
        rcases lcplead_cmIdx_lt hi' with ht | ⟨ht, hb⟩
        · have htl : t ≠ l := ne_of_lt ht
          have htj : t ≠ j := ne_of_lt (lt_trans ht hlj)
          rw [lcplead_hom_off hlj' hg hm b t htl htj,
            lcplead_hom_off hlj' hg hm0 b t htl htj]
        · rw [ht]
          have h1 := lcplead_hom_row hlj' hg hm b
          have h2 := lcplead_hom_row hlj' hg hm0 b
          have h3 := hω b hb
          omega
      · rw [domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq, hm0K]
        exact hlt
    · have hc := lcplead_coeff_peel hlj' a0 hg hm
      rw [heq] at hc
      have he : (m.erase (a0, l)).erase (a0, j) ∈ (peel l j a0 K g).support := by
        rw [mem_support_iff, hc]
        exact mem_support_iff.1 hm
      have hle := toSyn_le_toSyn_degree_of_mem_support (colLex r n) he
      have hm_eq := lcplead_recon hlj' a0 hg hm
      rw [heq] at hm_eq
      rw [hm_eq, hm0_eq]
      simp only [map_add (f := _)]
      exact add_le_add le_rfl hle
    · exfalso
      have hc := lcplead_coeff_peel hlj' a0 hg hm
      simp only [htop _ hgt, AddMonoidAlgebra.coeff_zero] at hc
      exact mem_support_iff.1 hm hc.symm
  exact (colLex r n).toSyn.injective
    (le_antisymm (hup _ ((colLex r n).degree_mem_support hg0))
      (toSyn_le_toSyn_degree_of_mem_support (colLex r n) hm0))

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSYTExists
section
open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem exists_tableau_of_sum_eq_lemma (hP : SSYTPeel) (r n : ℕ) :
    ∀ (N : ℕ) (ν : Fin n → ℕ) (m : Fin r × Fin n →₀ ℕ), ∑ t, ν t = N →
      (∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t) → Interlaced m →
      ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
        shapeDeg sz = ν ∧ (∀ k, StrictMono (I k)) ∧ bidetExp sz hsz I = m := by
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih ν m hN hcol hint_r
  by_cases hm : m = 0
  · subst hm
    have hν : ν = 0 := by
      funext t
      rw [← hcol t]
      simp
    subst hν
    refine ⟨0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, ?_, fun k => k.elim0, ?_⟩
    · funext t
      simp [shapeDeg]
    · simp [bidetExp]
  · obtain ⟨h, hh, c, hc, hν, hle, hint', hcol'⟩ := hP r n ν m hcol hint_r hm
    obtain ⟨⟨a0, t0⟩, hne⟩ : ∃ x, m x ≠ 0 := by
      by_contra H
      push_neg at H
      exact hm (Finsupp.ext H)
    have hpos : 0 < ν t0 := by
      rw [← hcol t0]
      exact lt_of_lt_of_le (Nat.pos_of_ne_zero hne)
        (Finset.single_le_sum (f := fun a => m (a, t0)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a0))
    have hlt : ∑ t, (ν t - if t.val < h then 1 else 0) < N := by
      rw [← hN]
      apply Finset.sum_lt_sum
      · intro t _
        exact Nat.sub_le _ _
      · refine ⟨t0, Finset.mem_univ _, ?_⟩
        rw [if_pos ((hν t0).2 hpos)]
        omega
    obtain ⟨K, sz, hsz, I, hshape, hI, hexp⟩ :=
      ih _ hlt (fun t => ν t - if t.val < h then 1 else 0) (m - colExp c hh) rfl hcol' hint'
    refine ⟨K + 1, Fin.cons h sz, lcssyt_consSz hh sz hsz, lcssyt_consI sz c I, ?_,
      lcssyt_consI_strictMono sz c I hc hI, ?_⟩
    · funext t
      rw [lcssyt_shapeDeg_cons, congrFun hshape t]
      by_cases ht : t.val < h
      · have h1 := (hν t).1 ht
        simp only [if_pos ht]
        omega
      · simp only [if_neg ht]
        omega
    · rw [lcssyt_bidetExp_cons hh c sz hsz I, hexp]
      exact add_tsub_cancel_of_le hle

theorem sSYTExists_of (hP : SSYTPeel) : SSYTExists :=
  fun r n ν m hcol hint_r => exists_tableau_of_sum_eq_lemma hP r n _ ν m rfl hcol hint_r

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem sum_Ico_tsub_telescope (g : ℕ → ℕ) (n : ℕ) (hg : ∀ i, g (i + 1) ≤ g i)
    (hn : ∀ i, n ≤ i → g i = 0) :
    ∀ d k, n - k = d → ∑ i ∈ Finset.Ico k n, (g i - g (i + 1)) = g k := by
  intro d
  induction d with
  | zero =>
    intro k hk
    have hnk : n ≤ k := by omega
    rw [Finset.Ico_eq_empty_of_le hnk, Finset.sum_empty, hn k hnk]
  | succ d ih =>
    intro k hk
    have hkn : k < n := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot hkn, ih (k + 1) (by omega)]
    exact Nat.sub_add_cancel (hg k)

def extNu {n : ℕ} (ν : Fin n → ℕ) (k : ℕ) : ℕ := if h : k < n then ν ⟨k, h⟩ else 0

theorem hw_weight_eq {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    (∑ s : Fin n, (ν s - nuNext ν s) • initW n (s.val + 1)) = ν := by
  have hg : ∀ i, extNu ν (i + 1) ≤ extNu ν i := by
    intro i
    unfold extNu
    by_cases h1 : i + 1 < n
    · have h0 : i < n := by omega
      rw [dite_eq_left h1, dite_eq_left h0]
      exact hν (show (⟨i, h0⟩ : Fin n) ≤ ⟨i + 1, h1⟩ from Fin.mk_le_mk.mpr (Nat.le_succ i))
    · rw [dite_eq_right h1]
      exact Nat.zero_le _
  have hz : ∀ i, n ≤ i → extNu ν i = 0 := by
    intro i hi
    have h0 : ¬ i < n := by omega
    unfold extNu
    rw [dite_eq_right h0]
  funext t
  have key : ∀ s : Fin n, (ν s - nuNext ν s) * initW n (s.val + 1) t =
      (if t.val ≤ s.val then extNu ν s.val - extNu ν (s.val + 1) else 0) := by
    intro s
    have h1 : ν s = extNu ν s.val := by
      unfold extNu
      rw [dite_eq_left s.isLt]
    have h2 : nuNext ν s = extNu ν (s.val + 1) := rfl
    unfold initW
    rw [h1, h2]
    by_cases hts : t.val ≤ s.val
    · have h3 : t.val < s.val + 1 := by omega
      simp only [hts, h3, if_true, mul_one]
    · have h3 : ¬ t.val < s.val + 1 := by omega
      simp only [hts, h3, if_false, mul_zero]
  have hsum : ∑ s : Fin n, (ν s - nuNext ν s) * initW n (s.val + 1) t
      = ∑ i ∈ Finset.range n,
          (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun s _ => key s)
  calc (∑ s : Fin n, (ν s - nuNext ν s) • initW n (s.val + 1)) t
      = ∑ s : Fin n, (ν s - nuNext ν s) * initW n (s.val + 1) t := by
        rw [Finset.sum_apply]
        rfl
    _ = ∑ i ∈ Finset.range n,
          (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) := hsum
    _ = ∑ i ∈ Finset.range t.val,
          (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) +
        ∑ i ∈ Finset.Ico t.val n,
          (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) :=
        (Finset.sum_range_add_sum_Ico
          (fun i => if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0)
          (le_of_lt t.isLt)).symm
    _ = 0 + ∑ i ∈ Finset.Ico t.val n, (extNu ν i - extNu ν (i + 1)) := by
        congr 1
        · refine Finset.sum_eq_zero (fun i hi => ?_)
          rw [Finset.mem_range] at hi
          have h0 : ¬ t.val ≤ i := by omega
          exact if_neg h0
        · exact Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_Ico.mp hi).1)
    _ = extNu ν t.val := by
        rw [zero_add]
        exact sum_Ico_tsub_telescope _ n hg hz (n - t.val) t.val rfl
    _ = ν t := by
        unfold extNu
        rw [dite_eq_left t.isLt]

theorem lpMinor_mem {R : Type*} [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    lpMinor R s hr hn ∈ dualWeyl R r n (initW n s) := by
  have h : lpMinor R s hr hn = initMinor R (Fin.castLE hr) hn := rfl
  rw [h]
  exact initMinor_mem (Fin.castLE hr) hn

theorem highestWeightVectorMem : HWMem := by
  unfold HWMem
  intro R _ r n hn ν hν
  unfold hw
  refine dualWeyl_of_eq ?_ (hw_weight_eq ν hν)
  exact dualWeyl_prod Finset.univ
    (fun s : Fin n => (ν s - nuNext ν s) • initW n (s.val + 1))
    (fun s : Fin n =>
      lpMinor R (s.val + 1) (by omega) (by omega) ^ (ν s - nuNext ν s))
    (fun s _ => dualWeyl_pow (lpMinor_mem _ _ _) _)

end Formalism.GradedWeylDivisibility
end
end

