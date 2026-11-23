module

public import Mathlib
public import Formalism.PieriBlockIdeals.Bundle0001

@[expose] public section

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.ContentLinkageHolds
section
noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

open Classical

theorem comb_roots_prod {K : Type} [Field K] {N : ℕ} (f : Fin N → K) :
    (∏ a, (X + C (f a))).roots = Multiset.map (fun a => -f a) Finset.univ.val := by
  have h : (∏ a, (X + C (f a))) =
      ((Multiset.map (fun a => -f a) Finset.univ.val).map fun x => X - C x).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp [sub_eq_add_neg]
  rw [h, Polynomial.roots_multiset_prod_X_sub_C]

theorem contentLinkage_holds : Linkage := by
  intro l K _ _ N U U' c hl hprod
  haveI : Fact l.Prime := ⟨hl⟩
  have hr := congrArg Polynomial.roots hprod
  have hU := comb_roots_prod (fun a => (((U a + c : ℤ)) : K))
  have hU' := comb_roots_prod (fun a => (((U' a + c : ℤ)) : K))
  rw [hU, hU'] at hr
  let ψ : ZMod l →+* K := ZMod.castHom (dvd_refl l) K
  have hψ : Function.Injective ψ := ψ.injective
  have key : ∀ V : Fin N → ℤ, Multiset.map (fun a => -(((V a + c : ℤ)) : K)) Finset.univ.val =
      Multiset.map ψ (Multiset.map (fun a => -(((V a + c : ℤ)) : ZMod l)) Finset.univ.val) := by
    intro V
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro a _
    simp [ψ, map_intCast]
  rw [key U, key U'] at hr
  have h2 := Multiset.map_injective hψ hr
  have h3 := congrArg (Multiset.map fun z : ZMod l => -z - (c : ZMod l)) h2
  simp only [Multiset.map_map] at h3
  convert h3 using 2 <;> (try simp only [Function.comp_apply]; push_cast; ring)

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.SharperSizeNeedsMleKFalse
section
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

lemma sums_harmonic_real (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ≤ 1 + Real.log n := by
  have h1 := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at h1
  push_cast at h1
  simpa [one_div] using h1

lemma leastCongruentPos_mem_le (l D : ℕ) (hD : 1 ≤ D) :
    1 ≤ d0 l (D : ℤ) ∧ (l : ℤ) ∣ (D : ℤ) - (d0 l (D : ℤ) : ℤ) ∧ d0 l (D : ℤ) ≤ D := by
  have hmem : D ∈ {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ (D : ℤ) - (d : ℤ)} := ⟨hD, by simp⟩
  have hs := Nat.sInf_mem (⟨D, hmem⟩ : ({d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ (D : ℤ) - (d : ℤ)}).Nonempty)
  unfold d0
  exact ⟨hs.1, hs.2, Nat.sInf_le hmem⟩

lemma sums_le_of_gate (l D : ℕ) (hD : 1 ≤ D) (hg : ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)) :
    (l : ℤ) ≤ (D : ℤ) - (d0 l (D : ℤ) : ℤ) := by
  obtain ⟨_, hdvd, _⟩ := leastCongruentPos_mem_le l D hD
  exact Int.le_of_dvd (by omega) hdvd

lemma sums_inj (D h : ℕ) (L : ℝ) (hD : 1 ≤ D) (hDh : D ≤ h) (hh : (h : ℝ) < L ^ 2)
    (hL : 1 ≤ L) (l l' : ℕ) (hl : l.Prime) (hl' : l'.Prime) (hLl : L < (l : ℝ))
    (hLl' : L < (l' : ℝ)) (hg : ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))
    (heq : d0 l (D : ℤ) = d0 l' (D : ℤ)) : l = l' := by
  by_contra hne
  obtain ⟨_, hdvd, _⟩ := leastCongruentPos_mem_le l D hD
  obtain ⟨_, hdvd', _⟩ := leastCongruentPos_mem_le l' D hD
  rw [← heq] at hdvd'
  have hcop : IsCoprime (l : ℤ) (l' : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes hl hl').2 hne
  have hprod := hcop.mul_dvd hdvd hdvd'
  have hpos : (0 : ℤ) < (D : ℤ) - (d0 l (D : ℤ) : ℤ) := by omega
  have hle2 := Int.le_of_dvd hpos hprod
  have hZ : (l : ℤ) * (l' : ℤ) ≤ (h : ℤ) := by
    have : (D : ℤ) ≤ h := by exact_mod_cast hDh
    have : (0 : ℤ) ≤ (d0 l (D : ℤ) : ℤ) := by positivity
    linarith
  have hR : (l : ℝ) * (l' : ℝ) ≤ (h : ℝ) := by exact_mod_cast hZ
  have hL0 : 0 ≤ L := by linarith
  have : L ^ 2 < (l : ℝ) * (l' : ℝ) := by
    rw [sq]; exact mul_lt_mul'' hLl hLl' hL0 hL0
  linarith

theorem gatedPrimeSum_holds : GatedSum := by
  intro D h L A k P hD hDh hA hk hh hL hP
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast le_trans hD hDh
  have hlogh : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg hh1
  have step1 : ∑ l ∈ P, (if ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ) then
        min k (A / (d0 l (D : ℤ) : ℝ)) else 0) * Real.log (l : ℝ) ≤
      ∑ l ∈ P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)),
        (A / (d0 l (D : ℤ) : ℝ)) * Real.log (h : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro l hl
    obtain ⟨hlp, _⟩ := hP l hl
    split_ifs with hgl
    · have hsub := sums_le_of_gate l D hD hgl
      have hlh : (l : ℝ) ≤ (h : ℝ) := by
        have h1 : (l : ℤ) ≤ (h : ℤ) := by
          have : (D : ℤ) ≤ (h : ℤ) := by exact_mod_cast hDh
          have : (0 : ℤ) ≤ ((d0 l (D : ℤ) : ℕ) : ℤ) := by positivity
          linarith
        exact_mod_cast h1
      have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hlp.one_lt.le
      exact mul_le_mul (min_le_right _ _) (Real.log_le_log (by linarith) hlh)
        (Real.log_nonneg hl1) (div_nonneg hA (Nat.cast_nonneg _))
    · simp
  have hinj : ∀ x ∈ P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)),
      ∀ y ∈ P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)),
      d0 x (D : ℤ) = d0 y (D : ℤ) → x = y := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.1 hx
    have hy' := Finset.mem_filter.1 hy
    obtain ⟨hxp, hLx⟩ := hP x hx'.1
    obtain ⟨hyp, hLy⟩ := hP y hy'.1
    exact sums_inj D h L hD hDh hh hL x y hxp hyp hLx hLy hx'.2 hxy
  have step2 : ∑ l ∈ P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)),
        (A / (d0 l (D : ℤ) : ℝ)) * Real.log (h : ℝ) =
      ∑ x ∈ (P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))).image
        (fun l => d0 l (D : ℤ)), (A / (x : ℝ)) * Real.log (h : ℝ) := by
    rw [Finset.sum_image hinj]
  have hsub : (P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))).image
      (fun l => d0 l (D : ℤ)) ⊆ Finset.Icc 1 h := by
    intro x hx
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h1, _, h2⟩ := leastCongruentPos_mem_le l D hD
    exact Finset.mem_Icc.2 ⟨h1, le_trans h2 hDh⟩
  have step3 : ∑ x ∈ (P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))).image
        (fun l => d0 l (D : ℤ)), (A / (x : ℝ)) * Real.log (h : ℝ) ≤
      ∑ x ∈ Finset.Icc 1 h, (A / (x : ℝ)) * Real.log (h : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => mul_nonneg (div_nonneg hA (Nat.cast_nonneg _)) hlogh)
  have step4 : ∑ x ∈ Finset.Icc 1 h, (A / (x : ℝ)) * Real.log (h : ℝ) =
      A * Real.log (h : ℝ) * ∑ x ∈ Finset.Icc 1 h, (1 : ℝ) / (x : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hH := sums_harmonic_real h
  have hAl : 0 ≤ A * Real.log (h : ℝ) := mul_nonneg hA hlogh
  refine le_trans step1 ?_
  rw [step2]
  refine le_trans step3 ?_
  rw [step4]
  calc A * Real.log (h : ℝ) * ∑ x ∈ Finset.Icc 1 h, (1 : ℝ) / (x : ℝ)
      ≤ A * Real.log (h : ℝ) * (1 + Real.log h) := mul_le_mul_of_nonneg_left hH hAl
    _ = A * (1 + Real.log (h : ℝ)) * Real.log (h : ℝ) := by ring

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.WeightExchangeBoundHolds
section
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

theorem we_msum (Y A Bm X : Multiset ℤ) (lo hi : ℤ) (hYA : Y ≤ A) (hA : A = Bm + X)
    (hc : Multiset.card Y = Multiset.card Bm) (hin : ∀ a ∈ A, lo ≤ a ∧ a ≤ hi) :
    |Bm.sum - Y.sum| ≤ (Multiset.card X : ℤ) * (hi - lo) := by
  subst hA
  have noMem : hi < lo → ∀ S : Multiset ℤ, (∀ a ∈ S, lo ≤ a ∧ a ≤ hi) → Multiset.card S = 0 := by
    intro hlt S hS
    by_contra hne
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero hne)
    have := hS a ha
    omega
  have hP : Y - Bm ≤ X := Multiset.sub_le_iff_le_add.2 (by rw [add_comm]; exact hYA)
  have hYs : Y.sum = (Y - Bm).sum + (Y ∩ Bm).sum := by
    conv_lhs => rw [← Multiset.sub_add_inter Y Bm]
    rw [Multiset.sum_add]
  have hBs : Bm.sum = (Bm - Y).sum + (Y ∩ Bm).sum := by
    conv_lhs => rw [← Multiset.sub_add_inter Bm Y]
    rw [Multiset.sum_add, Multiset.inter_comm]
  have hYc : Multiset.card Y = Multiset.card (Y - Bm) + Multiset.card (Y ∩ Bm) := by
    conv_lhs => rw [← Multiset.sub_add_inter Y Bm]
    rw [Multiset.card_add]
  have hBc : Multiset.card Bm = Multiset.card (Bm - Y) + Multiset.card (Y ∩ Bm) := by
    conv_lhs => rw [← Multiset.sub_add_inter Bm Y]
    rw [Multiset.card_add, Multiset.inter_comm]
  have hPQ : Multiset.card (Y - Bm) = Multiset.card (Bm - Y) := by omega
  have memP : ∀ a ∈ Y - Bm, lo ≤ a ∧ a ≤ hi := fun a ha =>
    hin a (Multiset.mem_of_le hYA (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha))
  have memQ : ∀ a ∈ Bm - Y, lo ≤ a ∧ a ≤ hi := fun a ha =>
    hin a (Multiset.mem_add.2 (Or.inl (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)))
  have memX : ∀ a ∈ X, lo ≤ a ∧ a ≤ hi := fun a ha => hin a (Multiset.mem_add.2 (Or.inr ha))
  have P1 := Multiset.sum_le_card_nsmul (Y - Bm) hi (fun a ha => (memP a ha).2)
  have P2 : Multiset.card (Y - Bm) • lo ≤ (Y - Bm).sum :=
    Multiset.card_nsmul_le_sum (fun a ha => (memP a ha).1)
  have Q1 := Multiset.sum_le_card_nsmul (Bm - Y) hi (fun a ha => (memQ a ha).2)
  have Q2 : Multiset.card (Bm - Y) • lo ≤ (Bm - Y).sum :=
    Multiset.card_nsmul_le_sum (fun a ha => (memQ a ha).1)
  rw [hPQ] at P1 P2
  simp only [nsmul_eq_mul] at P1 P2 Q1 Q2
  have hm : (Multiset.card (Bm - Y) : ℤ) * (hi - lo) ≤ (Multiset.card X : ℤ) * (hi - lo) := by
    by_cases h : lo ≤ hi
    · apply mul_le_mul_of_nonneg_right _ (by linarith)
      have := Multiset.card_le_card hP
      rw [hPQ] at this
      exact_mod_cast this
    · push_neg at h
      rw [noMem h _ memQ, noMem h X memX]
  rw [hYs, hBs, abs_le]
  constructor <;> linarith

theorem shiftSumBound_holds : KapSum := by
  intro l b t κ U kap hl htl hU hkap hle
  have : NeZero l := ⟨by omega⟩
  have hlpos : (0 : ℤ) < (l : ℤ) := by exact_mod_cast hl
  obtain ⟨lo, hlo⟩ : ∃ lo : ℤ, lo = b - (κ : ℤ) := ⟨_, rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi : ℤ, hi = b + (t : ℤ) - 1 + (κ : ℤ) := ⟨_, rfl⟩
  have hwin : hi < lo + l := by omega
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℤ, ∀ u, g u = lo + (u - lo) % (l : ℤ) := ⟨_, fun _ => rfl⟩
  have g_ge : ∀ u, lo ≤ g u := fun u => by
    rw [hg]
    have := Int.emod_nonneg (u - lo) hlpos.ne'
    linarith
  have g_fix : ∀ v, lo ≤ v → v ≤ hi → g v = v := fun v h1 h2 => by
    rw [hg, Int.emod_eq_of_lt (by linarith) (by linarith)]
    ring
  have g_mod : ∀ u, g u ≡ u [ZMOD (l : ℤ)] := fun u => by
    have h := (Int.mod_modEq (u - lo) (l : ℤ)).add_left lo
    rw [hg]
    rwa [show lo + (u - lo) = u by ring] at h
  have g_cong : ∀ u v, u ≡ v [ZMOD (l : ℤ)] → g u = g v := fun u v h => by
    have e : (u - lo) % (l : ℤ) = (v - lo) % (l : ℤ) := Int.ModEq.sub_right lo h
    rw [hg, hg, e]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ZMod l → ℤ, ∀ u : ℤ, ρ (u : ZMod l) = g u :=
    ⟨fun z => lo + ((z - (lo : ZMod l)).val : ℤ), fun u => by
      show lo + ((((u : ZMod l) - (lo : ZMod l))).val : ℤ) = g u
      rw [← Int.cast_sub, ZMod.val_intCast, hg]⟩
  have hvW : ∀ s : Fin t, lo ≤ b + ((s : ℕ) : ℤ) - kap s ∧ b + ((s : ℕ) : ℤ) - kap s ≤ hi :=
    fun s => by
      have h1 := s.isLt
      have h2 := abs_le.1 (hkap s)
      omega
  have hY : Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val ≤
      Multiset.map g U.val := by
    have h1 := Multiset.map_le_map (f := ρ) hle
    rw [Multiset.map_map, Multiset.map_map] at h1
    refine Eq.trans_le (Multiset.map_congr rfl fun s _ => ?_)
      (h1.trans_eq (Multiset.map_congr rfl fun u _ => ?_))
    · simp only [Function.comp_apply]
      rw [hρ, g_fix _ (hvW s).1 (hvW s).2]
    · simp only [Function.comp_apply]
      rw [hρ]
  have hYA : Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val ≤
      Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) := by
    have hself : Multiset.filter (fun x => x ≤ hi)
        (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val) =
        Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val :=
      Multiset.filter_eq_self.2 (fun a ha => by
        rw [Multiset.mem_map] at ha
        obtain ⟨s, -, rfl⟩ := ha
        exact (hvW s).2)
    rw [← hself]
    exact Multiset.filter_le_filter (p := fun x => x ≤ hi) hY
  have hin : ∀ a ∈ Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val), lo ≤ a ∧ a ≤ hi := by
    intro a ha
    rw [Multiset.mem_filter, Multiset.mem_map] at ha
    obtain ⟨⟨u, -, rfl⟩, h⟩ := ha
    exact ⟨g_ge u, h⟩
  have hF : Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) =
      Multiset.map g (Multiset.filter (fun u => g u ≤ hi) U.val) := by
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map g) (Multiset.filter_congr fun _ _ => Iff.rfl)
  have hfirst : Multiset.filter (fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1))
      (Multiset.filter (fun u => g u ≤ hi) U.val) =
      Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val := by
    have hinj : Function.Injective (fun s : Fin t => b + ((s : ℕ) : ℤ)) := by
      intro s1 s2 h
      have h' : b + ((s1 : ℕ) : ℤ) = b + ((s2 : ℕ) : ℤ) := h
      exact Fin.ext (by omega)
    have hnd1 : (Multiset.filter (fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1))
        (Multiset.filter (fun u => g u ≤ hi) U.val)).Nodup := by
      apply Multiset.Nodup.filter
      apply Multiset.Nodup.filter
      exact U.nodup
    rw [Multiset.Nodup.ext hnd1 (Multiset.Nodup.map hinj (Finset.nodup _))]
    intro a
    simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_Icc, Multiset.mem_map,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨-, -⟩, h1, h2⟩
      have hn := Int.toNat_of_nonneg (show 0 ≤ a - b by omega)
      refine ⟨⟨(a - b).toNat, by omega⟩, ?_⟩
      show b + (((a - b).toNat : ℕ) : ℤ) = a
      omega
    · rintro ⟨s, rfl⟩
      have hs := s.isLt
      refine ⟨⟨hU s, ?_⟩, by omega, by omega⟩
      rw [g_fix _ (by omega) (by omega)]
      omega
  have hA : Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) =
      Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val +
      Multiset.map g (Multiset.filter (fun u => u ∉ Finset.Icc b (b + (t : ℤ) - 1))
        (Multiset.filter (fun u => g u ≤ hi) U.val)) := by
    rw [hF]
    conv_lhs => rw [← Multiset.filter_add_not (p := fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1))
      (s := Multiset.filter (fun u => g u ≤ hi) U.val)]
    rw [Multiset.map_add (f := _), hfirst, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun s _ => by
      have hs := s.isLt
      simp only [Function.comp_apply]
      exact g_fix _ (by omega) (by omega)
  have hR : ∀ u, (∃ x ∈ Finset.Icc (b - (κ : ℤ)) (b + (t : ℤ) - 1 + (κ : ℤ)),
      x ≡ u [ZMOD (l : ℤ)]) ↔ g u ≤ hi := by
    intro u
    constructor
    · rintro ⟨x, hx, hxu⟩
      rw [Finset.mem_Icc] at hx
      rw [← g_cong x u hxu, g_fix x (by omega) (by omega)]
      omega
    · intro hu
      exact ⟨g u, Finset.mem_Icc.2 ⟨by have := g_ge u; omega, by omega⟩, g_mod u⟩
  have hcard : Multiset.card (Multiset.filter (fun u => u ∉ Finset.Icc b (b + (t : ℤ) - 1))
      (Multiset.filter (fun u => g u ≤ hi) U.val)) = mwCount l b t κ U := by
    unfold mwCount
    rw [← Finset.card_val, Finset.filter_val, Finset.filter_val,
      Multiset.filter_filter, Multiset.filter_filter]
    congr 1
    have e : Multiset.filter (fun a => a ∉ Finset.Icc b (b + (t : ℤ) - 1) ∧ g a ≤ hi) U.val =
        Multiset.filter (fun a => (∃ x ∈ Finset.Icc (b - (κ : ℤ)) (b + (t : ℤ) - 1 + (κ : ℤ)),
          x ≡ a [ZMOD (l : ℤ)]) ∧ a ∉ Finset.Icc b (b + (t : ℤ) - 1)) U.val :=
      Multiset.filter_congr (fun u _ => by rw [hR u]; exact and_comm)
    convert e using 2
  have key := we_msum _ _ _ _ lo hi hYA hA
    (by rw [Multiset.card_map, Multiset.card_map]) hin
  rw [Multiset.card_map, hcard] at key
  have hBs : (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val).sum =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ)) := (Finset.sum_eq_multiset_sum _ _).symm
  have hYs : (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val).sum =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ) - kap s) := (Finset.sum_eq_multiset_sum _ _).symm
  rw [hBs, hYs, Finset.sum_sub_distrib, sub_sub_cancel] at key
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  omega

theorem weightExchangeBound_holds : WEArith := by
  intro k j t q l h κ mw mwp U U' kc kp _ _ hU0 hU'h hsum htop hkc hkp
  have hlkp : (l : ℤ) * kp ≤ (l : ℤ) * ((mwp : ℤ) * ((t : ℤ) + 2 * κ)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self kp).trans hkp) (by positivity)
  have hkc' : -kc ≤ (mw : ℤ) * ((t : ℤ) + 2 * κ) := (neg_le_abs kc).trans hkc
  have hq : ∑ a ∈ Finset.univ.filter
      (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q), (h : ℤ) ≤
      (q : ℤ) * h := by
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hc : (Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q)).card ≤ q := by
      refine le_trans (Finset.card_le_card_of_injOn (fun a => (a : ℕ) - (k + j)) ?_ ?_)
        (Finset.card_range q).le
      · intro a ha
        simp at ha ⊢
        omega
      · intro a ha a' ha' hab
        simp at ha ha'
        have hab' : (a : ℕ) - (k + j) = (a' : ℕ) - (k + j) := hab
        exact Fin.ext (by omega)
    exact_mod_cast hc
  rw [Finset.sum_filter] at hq
  have hpt : ∀ a ∈ (Finset.univ : Finset (Fin (k + j + t + q))),
      (if (a : ℕ) < k + j then U a - U' a else 0) +
        (if k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t then U a else 0) ≤
      (if k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q then (h : ℤ) else 0) +
        (if k + j + q ≤ (a : ℕ) then U' a else 0) + (U a - U' a) := by
    intro a _
    have h1 := hU0 a
    have h2 := hU'h a
    split_ifs <;> omega
  have hsumle := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsumle
  simp only [Finset.sum_filter] at htop ⊢
  nlinarith

end Formalism.CohomologicalDescent
end
end

