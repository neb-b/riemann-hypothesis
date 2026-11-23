module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PSysBasic
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma lft_uni' (hU : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β)
    (L : Finset κ) : lft (uni b L) = b := by
  exact (hU β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.1

private lemma rgt_uni' (hU : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β)
    (L : Finset κ) : rgt (uni b L) = L := by
  exact (hU β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.2.1

private lemma card_uni' (hU : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β)
    (L : Finset κ) : (uni b L).card = b.card + L.card := by
  exact (hU β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.2.2.1

private lemma uni_lr' (hU : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ]
    (s : Finset (β ⊕ₗ κ)) : uni (lft s) (rgt s) = s := by
  exact (hU β κ ℂ (fun _ => 0) (fun _ => 0) ∅ ∅).2.2.2.2 s

private lemma mem_acxC {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E) :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥) := by
  show c ∈ Submodule.pi Set.univ _ ↔ _
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]

private lemma wd_eq_zero {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (w : σ → Module.End ℂ E) (f : Finset σ → E) (t : Finset σ)
    (h : ∀ i ∈ t, f (t.erase i) = 0) : wd w f t = 0 := by
  simp only [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  exact Finset.sum_eq_zero fun i hi => by rw [h i hi]; simp

section
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
  (T : Sys d S E) {κ : Type} [LinearOrder κ]

private lemma col_iff (n : κ → ℕ × ℕ) (z : κ → S) (I J : Finset (Fin (d + 1))) (m : ℤ)
    (x : Finset κ → E) : x ∈ (T.colCx n z I J).C m ↔ ∀ L, x L ∈ (if (L.card : ℤ) = m then
      (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) else ⊥) :=
  mem_acxC _ _ _ _

private lemma cx_iff (hU : WdUni) (n : κ → ℕ × ℕ) (z : κ → S) (N : ℤ)
    (c : Finset (Two d ⊕ₗ κ) → E) : c ∈ (T.cx n z).C N ↔ ∀ I J L, c (uni (uni I J) L) ∈
      (if I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card + L.card : ℕ) : ℤ) = N then
        (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) else ⊥) := by
  have key : ∀ (I J : Finset (Fin (d + 1))) (L : Finset κ),
      (if (((uni (uni I J) L).card : ℕ) : ℤ) = N then
        mixF (fun I' J' => Submodule.map (T.act ((∏ l ∈ rgt (uni (uni I J) L),
          T.u n (pk I') (pk J') l : Sˣ) : S)) (T.M I' J')) (lft (uni (uni I J) L)) else ⊥) =
      (if I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card + L.card : ℕ) : ℤ) = N then
        (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) else ⊥) := by
    intro I J L
    simp only [lft_uni' hU, rgt_uni' hU, card_uni' hU, mixF]
    split_ifs <;> first | rfl | (exfalso; tauto)
  refine (mem_acxC _ _ N c).trans ?_
  constructor
  · intro h I J L
    rw [← key]
    exact h _
  · intro h s
    obtain ⟨I, J, L, rfl⟩ : ∃ I J L, s = uni (uni I J) L :=
      ⟨_, _, _, by rw [uni_lr' hU, uni_lr' hU]⟩
    rw [key]
    exact h I J L

private lemma top_C (hU : WdUni) (n : κ → ℕ × ℕ) (z : κ → S) (N : ℤ)
    (c : Finset (Two d ⊕ₗ κ) → E) (hc : c ∈ (T.cx n z).C N) : top c ∈ T.mix.C N := by
  refine (mem_acxC _ _ N _).mpr ?_
  intro b
  obtain ⟨I, J, rfl⟩ : ∃ I J, b = uni I J := ⟨lft b, rgt b, (uni_lr' hU b).symm⟩
  have h1 := (cx_iff T hU n z N c).mp hc I J ∅
  simp only [top, mixF, lft_uni' hU, rgt_uni' hU, card_uni' hU, Finset.prod_empty,
    Finset.card_empty, add_zero, Units.val_one, map_one] at h1 ⊢
  rw [Module.End.one_eq_id, Submodule.map_id] at h1
  split_ifs at h1 ⊢ <;> first | exact h1 | (exfalso; tauto) | simp_all

private lemma top_D (hU : WdUni) (z : κ → S) (c : Finset (Two d ⊕ₗ κ) → E) :
    top (wd (T.wt z) c) = wd (fun _ : Two d => (1 : Module.End ℂ E)) (top c) := by
  funext b
  simp only [top]
  rw [(hU _ _ _ (T.wt z) c b ∅).1]
  have h0 : wd (fun l => T.wt z (inrE l)) (fun L' => c (uni b L')) ∅ = 0 := by
    simp [wd]
  rw [h0, smul_zero, add_zero]
  have hw : (fun i => T.wt z (inlE i)) = fun _ : Two d => (1 : Module.End ℂ E) := by
    funext i
    simp [Sys.wt, inlE]
  rw [hw]
  rfl

end

private theorem wd_wt_resK_eq_zero_of_wd_eq_zero (hU : WdUni) (hB : WdBasic) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) {κ : Type} [LinearOrder κ] [Fintype κ]
    (z : κ → S) {κ' : Type} [LinearOrder κ'] (e : κ' ↪o κ) (c : Finset (Two d ⊕ₗ κ) → E)
    (hD : wd (T.wt z) c = 0) : wd (T.wt fun l => z (e l)) (resK e c) = 0 := by
  have hwl : ∀ {κ₀ : Type} [LinearOrder κ₀] (z₀ : κ₀ → S) (i : Two d), T.wt z₀ (inlE i) = 1 := by
    intro κ₀ _ z₀ i
    simp [Sys.wt, inlE]
  have hwr : ∀ {κ₀ : Type} [LinearOrder κ₀] (z₀ : κ₀ → S) (l : κ₀), T.wt z₀ (inrE l) = T.act (z₀ l) := by
    intro κ₀ _ z₀ l
    simp [Sys.wt, inrE]
  funext s
  obtain ⟨b, L, rfl⟩ : ∃ b L, s = uni b L := ⟨lft s, rgt s, (uni_lr' hU s).symm⟩
  rw [(hU _ _ _ _ (resK e c) b L).1]
  have hres : ∀ b' L', resK e c (uni b' L') = c (uni b' (L'.map e.toEmbedding)) := by
    intro b' L'
    simp only [resK, lft_uni' hU, rgt_uni' hU]
  have hmap : wd (fun l => T.act (z (e l))) (fun L' => c (uni b (L'.map e.toEmbedding))) L =
      wd (fun l => T.act (z l)) (fun L' => c (uni b L')) (L.map e.toEmbedding) :=
    (hB κ E (fun _ => ⊥) (fun l => T.act (z l))).2.2.2.2.2 κ' e (fun L' => c (uni b L')) L
  have e2 := (hU _ _ _ (T.wt z) c b (L.map e.toEmbedding)).1
  rw [hD] at e2
  simp only [hres, hwl, hwr]
  rw [hmap]
  simp only [hwl, hwr] at e2
  rw [← e2]
  rfl

theorem UpperTheory.Gal.productCup_of_system.sysBasic_of :
    WdUni → WdBasic → SysBasic := by
  intro hU hB d S E _ _ _ _ T κ _ _ n z N
  have hmem : ∀ c, c ∈ (T.cx n z).C N → ∀ (I J : Finset (Fin (d + 1))) (L : Finset κ),
      ¬ (I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card + L.card : ℕ) : ℤ) = N) →
      c (uni (uni I J) L) = 0 := by
    intro c hc I J L h
    have := (cx_iff T hU n z N c).mp hc I J L
    rw [if_neg h] at this
    exact (Submodule.mem_bot ℂ).mp this
  have h2 : ∀ c : Finset (Two d ⊕ₗ κ) → E, c ∈ (T.cx n z).C N ↔
      ∀ (I J : Finset (Fin (d + 1))), col c (uni I J) ∈
        (if I.Nonempty ∧ J.Nonempty then (T.colCx n z I J).C (N - I.card - J.card) else ⊥) := by
    intro c
    rw [cx_iff T hU]
    refine forall_congr' fun I => forall_congr' fun J => ?_
    by_cases hIJ : I.Nonempty ∧ J.Nonempty
    · rw [if_pos hIJ, col_iff]
      refine forall_congr' fun L => ?_
      simp only [col]
      by_cases hL : (L.card : ℤ) = N - I.card - J.card
      · rw [if_pos hL, if_pos ⟨hIJ.1, hIJ.2, by push_cast; omega⟩]
      · rw [if_neg hL, if_neg (fun h => hL (by have := h.2.2; push_cast at this; omega))]
    · rw [if_neg hIJ, Submodule.mem_bot, funext_iff]
      refine forall_congr' fun L => ?_
      rw [if_neg (fun h => hIJ ⟨h.1, h.2.1⟩), Submodule.mem_bot]
      rfl
  have hwr : ∀ {κ₀ : Type} [LinearOrder κ₀] (z₀ : κ₀ → S) (l : κ₀), T.wt z₀ (inrE l) = T.act (z₀ l) := by
    intro κ₀ _ z₀ l
    simp [Sys.wt, inrE]
  refine ⟨?_, h2, ?_, ?_, ?_, ?_⟩
  · intro c hc I J L h
    apply hmem c hc I J L
    rintro ⟨hI, hJ, hN⟩
    rcases h with h | h | h
    · subst h; exact Finset.not_nonempty_empty hI
    · subst h; exact Finset.not_nonempty_empty hJ
    · exact h hN
  · intro c hc
    obtain ⟨hC, hD⟩ := Submodule.mem_inf.mp hc
    refine Submodule.mem_inf.mpr ⟨top_C T hU n z N c hC, ?_⟩
    rw [LinearMap.mem_ker] at hD ⊢
    change wd (fun _ : Two d => (1 : Module.End ℂ E)) (top c) = 0
    rw [← top_D T hU z c]
    change wd (T.wt z) c = 0 at hD
    rw [hD]
    rfl
  · intro c hc
    obtain ⟨c', hc', rfl⟩ := Submodule.mem_map.mp hc
    exact Submodule.mem_map.mpr ⟨top c', top_C T hU n z (N - 1) c' hc', (top_D T hU z c').symm⟩
  · intro c hc I J hI hJ hlow
    obtain ⟨hC, hD⟩ := Submodule.mem_inf.mp hc
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · have := (h2 c).mp hC I J
      rwa [if_pos ⟨hI, hJ⟩] at this
    · rw [LinearMap.mem_ker] at hD ⊢
      change wd (fun l => T.act (z l)) (col c (uni I J)) = 0
      change wd (T.wt z) c = 0 at hD
      funext L
      have e1 := (hU _ _ _ (T.wt z) c (uni I J) L).1
      rw [hD] at e1
      have key : ∀ t : Finset (Two d), t.card < (uni I J).card → c (uni t L) = 0 := by
        intro t ht
        rw [← uni_lr' hU t]
        apply hlow
        have h3 := card_uni' hU (lft t) (rgt t)
        rw [uni_lr' hU] at h3
        rw [card_uni' hU] at ht
        omega
      have hz1 : wd (fun b => T.wt z (inlE b)) (fun b' => c (uni b' L)) (uni I J) = 0 := by
        apply wd_eq_zero
        intro i hi
        exact key _ (Finset.card_erase_lt_of_mem hi)
      rw [hz1, zero_add] at e1
      simp only [hwr, Pi.zero_apply] at e1 ⊢
      rcases neg_one_pow_eq_or ℤ (uni I J).card with h | h <;> rw [h] at e1 <;> simp at e1 <;>
        first | exact e1.symm | exact e1 | exact neg_eq_zero.mp e1.symm
  · intro κ' _ _ e c hc
    obtain ⟨hC, hD⟩ := Submodule.mem_inf.mp hc
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [cx_iff T hU]
      intro I J L
      have := (cx_iff T hU n z N c).mp hC I J (L.map e.toEmbedding)
      simp only [resK, lft_uni' hU, rgt_uni' hU]
      rw [Finset.card_map, Finset.prod_map] at this
      exact this
    · rw [LinearMap.mem_ker] at hD ⊢
      exact wd_wt_resK_eq_zero_of_wd_eq_zero hU hB T z e c hD
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PSysOk
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section SlopeTestRemainingChoices

private lemma mem_lft' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (s : Finset (ι ⊕ₗ κ)) (a : ι) :
    a ∈ lft s ↔ toLex (Sum.inl a) ∈ s := by
  simp [lft, Finset.mem_toLeft]

private lemma mem_rgt' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (s : Finset (ι ⊕ₗ κ)) (a : κ) :
    a ∈ rgt s ↔ toLex (Sum.inr a) ∈ s := by
  simp [rgt, Finset.mem_toRight]

private lemma lft_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s s' : Finset (ι ⊕ₗ κ)} (h : s ⊆ s') :
    lft s ⊆ lft s' := fun a ha => (mem_lft' _ _).2 (h ((mem_lft' _ _).1 ha))

private lemma rgt_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s s' : Finset (ι ⊕ₗ κ)} (h : s ⊆ s') :
    rgt s ⊆ rgt s' := fun a ha => (mem_rgt' _ _).2 (h ((mem_rgt' _ _).1 ha))

private lemma pk_mem' {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  unfold pk
  rw [dite_eq_left h]
  exact Finset.min'_mem _ _

variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
  {κ : Type} [LinearOrder κ]

private lemma u_quot (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha' : a' ∈ I) (hb' : b' ∈ J) (l : κ) :
    ((T.u n a b l * (T.u n a' b' l)⁻¹ : Sˣ) : S) ∈ T.R I J := by
  have e : T.u n a b l * (T.u n a' b' l)⁻¹ =
      (T.X a * (T.X a')⁻¹) ^ (n l).1 * (T.Y b * (T.Y b')⁻¹) ^ (n l).2 := by
    simp only [Sys.u, mul_inv, mul_pow, inv_pow]
    ac_rfl
  rw [e, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  exact mul_mem (pow_mem (hT.memX I J hJ a' ha' a) _) (pow_mem (hT.memY I J hI b' hb' b) _)

private lemma prod_quot (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha' : a' ∈ I) (hb' : b' ∈ J) (L : Finset κ) :
    (((∏ l ∈ L, T.u n a b l) * (∏ l ∈ L, T.u n a' b' l)⁻¹ : Sˣ) : S) ∈ T.R I J := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Units.coe_prod]
  exact Subalgebra.prod_mem _ (fun l _ => u_quot T hT n hI hJ ha' hb' l)

private lemma lat_le (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha' : a' ∈ I) (hb' : b' ∈ J) (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.u n a b l : Sˣ) : S)) ≤
      (T.M I J).map (T.act ((∏ l ∈ L, T.u n a' b' l : Sˣ) : S)) := by
  rintro y ⟨m, hm, rfl⟩
  have hr := prod_quot T hT n hI hJ (a := a) (b := b) ha' hb' L
  refine ⟨T.act (((∏ l ∈ L, T.u n a b l) * (∏ l ∈ L, T.u n a' b' l)⁻¹ : Sˣ) : S) m,
    hT.stab I J hI hJ _ hr m hm, ?_⟩
  rw [← Module.End.mul_apply, ← map_mul, ← Units.val_mul, mul_comm (∏ l ∈ L, T.u n a b l),
    mul_inv_cancel_left]

private lemma lat_eq (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha : a ∈ I) (ha' : a' ∈ I) (hb : b ∈ J) (hb' : b' ∈ J) (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.u n a b l : Sˣ) : S)) =
      (T.M I J).map (T.act ((∏ l ∈ L, T.u n a' b' l : Sˣ) : S)) :=
  le_antisymm (lat_le T hT n hI hJ ha' hb' L) (lat_le T hT n hI hJ ha hb L)

private lemma lat_mono (hT : T.Good) (n : κ → ℕ × ℕ) {I I' J J' : Finset (Fin (d + 1))} (hI : I.Nonempty)
    (hJ : J.Nonempty) (hII : I ⊆ I') (hJJ : J ⊆ J') (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) ≤
      (T.M I' J').map (T.act ((∏ l ∈ L, T.u n (pk I') (pk J') l : Sˣ) : S)) := by
  have hI' := Finset.Nonempty.mono hII hI
  have hJ' := Finset.Nonempty.mono hJJ hJ
  calc (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))
      ≤ (T.M I' J').map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) :=
        Submodule.map_mono (hT.monoM I I' J J' hI hJ hII hJJ)
    _ = _ := lat_eq T hT n hI' hJ' (hII (pk_mem' hI)) (pk_mem' hI') (hJJ (pk_mem' hJ)) (pk_mem' hJ') L

private lemma r_mem (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S) (hA : T.admitted n z) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) (l : κ) : T.r n z i j l ∈ T.R I J :=
  hT.monoR {i} I {j} J (Finset.singleton_nonempty i) (Finset.singleton_nonempty j)
    (Finset.singleton_subset_iff.2 hi) (Finset.singleton_subset_iff.2 hj) (hA i j l)

private lemma col_eq (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) :
    T.colCx n z I J = kosT T.act (T.M I J) (T.u n i j) z := by
  unfold Sys.colCx kosT
  congr 1
  funext L
  exact lat_eq T hT n ⟨i, hi⟩ ⟨j, hj⟩ (pk_mem' ⟨i, hi⟩) hi (pk_mem' ⟨j, hj⟩) hj L

private lemma mix_mono (hT : T.Good) (n : κ → ℕ × ℕ) (L : Finset κ) {s s' : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1))}
    (hs : s ⊆ s') {m : E}
    (hm : m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))) s) :
    m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))) s' := by
  unfold mixF at hm ⊢
  by_cases h : (lft s).Nonempty ∧ (rgt s).Nonempty
  · have h' : (lft s').Nonempty ∧ (rgt s').Nonempty :=
      ⟨Finset.Nonempty.mono (lft_mono' hs) h.1, Finset.Nonempty.mono (rgt_mono' hs) h.2⟩
    rw [if_pos h] at hm
    rw [if_pos h']
    exact lat_mono T hT n h.1 h.2 (lft_mono' hs) (rgt_mono' hs) L hm
  · rw [if_neg h, Submodule.mem_bot] at hm
    subst hm
    exact zero_mem _

private lemma mix_step (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S) (hA : T.admitted n z) (L : Finset κ) {l : κ} (hl : l ∉ L)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1))) {m : E}
    (hm : m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))) s) :
    T.act (z l) m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ insert l L, T.u n (pk I) (pk J) l : Sˣ) : S))) s := by
  unfold mixF at hm ⊢
  by_cases h : (lft s).Nonempty ∧ (rgt s).Nonempty
  · rw [if_pos h] at hm ⊢
    rw [Submodule.mem_map] at hm ⊢
    obtain ⟨m0, hm0, rfl⟩ := hm
    refine ⟨T.act (T.r n z (pk (lft s)) (pk (rgt s)) l) m0,
      hT.stab _ _ h.1 h.2 _ (r_mem T hT n z hA (pk_mem' h.1) (pk_mem' h.2) l) m0 hm0, ?_⟩
    have e : ((∏ k ∈ insert l L, T.u n (pk (lft s)) (pk (rgt s)) k : Sˣ) : S) *
        T.r n z (pk (lft s)) (pk (rgt s)) l =
        z l * ((∏ k ∈ L, T.u n (pk (lft s)) (pk (rgt s)) k : Sˣ) : S) := by
      have hu := Units.mul_inv (T.u n (pk (lft s)) (pk (rgt s)) l)
      rw [Finset.prod_insert hl, Units.val_mul]
      simp only [Sys.r]
      linear_combination (z l * ((∏ k ∈ L, T.u n (pk (lft s)) (pk (rgt s)) k : Sˣ) : S)) * hu
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
  · rw [if_neg h, Submodule.mem_bot] at hm
    rw [if_neg h, hm, map_zero]
    exact zero_mem _

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.productCup_of_system.sysOk_of :
    WdUni → SysOk := by
  intro _
  unfold SysOk
  intro d S E _ _ _ _ T κ _ _ n z hT hA
  refine ⟨⟨?_, ?_⟩, fun I J i hi j hj => ⟨fun l => r_mem T hT n z hA hi hj l, col_eq T hT n z hi hj⟩, ?_⟩
  · intro i j
    unfold Sys.wt
    rcases ofLex i with a | a <;> rcases ofLex j with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact Commute.one_left _
    · exact Commute.one_left _
    · exact Commute.one_right _
    · exact (Commute.all (z a) (z b)).map T.act
  · intro s t ht m hm
    obtain ⟨x, rfl⟩ : ∃ x : Two d ⊕ κ, toLex x = t := ⟨ofLex t, rfl⟩
    beta_reduce at hm ⊢
    rcases x with a | l
    · have hw : T.wt z (toLex (Sum.inl a)) = 1 := rfl
      rw [hw, Module.End.one_apply]
      have gen : ∀ s1 : Finset (Two d ⊕ₗ κ), lft s ⊆ lft s1 → rgt s1 = rgt s →
          m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ rgt s1, T.u n (pk I) (pk J) l : Sˣ) : S)))
            (lft s1) := by
        intro s1 h1 h2
        rw [h2]
        exact mix_mono T hT n (rgt s) h1 hm
      refine gen _ ?_ ?_
      · intro b hb
        rw [mem_lft'] at hb ⊢
        simp [hb]
      · ext b
        simp [mem_rgt']
    · have hl : l ∉ rgt s := fun h => ht ((mem_rgt' s l).1 h)
      have key := mix_step T hT n z hA (rgt s) hl (lft s) hm
      have hw : T.wt z (toLex (Sum.inr l)) = T.act (z l) := rfl
      rw [hw]
      have gen : ∀ s1 : Finset (Two d ⊕ₗ κ), lft s1 = lft s → rgt s1 = insert l (rgt s) →
          T.act (z l) m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ rgt s1, T.u n (pk I) (pk J) l : Sˣ) : S)))
            (lft s1) := by
        intro s1 h1 h2
        rw [h1, h2]
        exact key
      refine gen _ ?_ ?_
      · ext b
        simp [mem_lft']
      · ext b
        simp [mem_rgt']
  · intro I I' J J' hI hJ hII hJJ m x hx
    simp only [Cx.Z, Sys.colCx, kosT, acx, Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ,
      true_implies] at hx ⊢
    refine ⟨fun L => ?_, hx.2⟩
    have hxL := hx.1 L
    split_ifs at hxL ⊢
    · exact lat_mono T hT n hI hJ hII hJJ L hxL
    · exact hxL
end

