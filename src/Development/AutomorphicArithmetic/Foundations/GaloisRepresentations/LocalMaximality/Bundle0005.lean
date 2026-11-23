module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.MemUniInr
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private def phiT {d : ℕ} : Fin (d + 1) ⊕ₗ Fin d → Fin (d + 1) := fun t => Sum.elim id Fin.succ (ofLex t)

private def cT {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E) :
    Fin (d + 1) ⊕ₗ Fin d → S :=
  app (fun _ => 1) (fun l : Fin d => (T.X l.succ : S))

private lemma rowT_eq {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (t : Fin (d + 1) ⊕ₗ Fin d) : T.rowT t = Pi.single (phiT t) (cT T t) := by
  rcases t with i | l <;> rfl

private lemma det_single {S : Type} [CommRing S] {n : ℕ} (g : Fin n → Fin n) (v : Fin n → S) :
    (Matrix.of fun a b => (Pi.single (g a) (v a) : Fin n → S) b).det = 0 ∨
      (Function.Bijective g ∧ ∃ ε : ℤˣ,
        (Matrix.of fun a b => (Pi.single (g a) (v a) : Fin n → S) b).det = ε • ∏ a, v a) := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply, Pi.single_apply]
  rw [Finset.sum_congr rfl fun σ _ => by rw [Fintype.prod_ite_zero]]
  by_cases hg : Function.Bijective g
  · right
    refine ⟨hg, Equiv.Perm.sign (Equiv.ofBijective g hg), ?_⟩
    rw [Finset.sum_eq_single (Equiv.ofBijective g hg)]
    · rw [if_pos (show ∀ i, (Equiv.ofBijective g hg) i = g i from fun i => rfl)]
    · intro σ _ hσ
      rw [if_neg, smul_zero]
      intro h
      exact hσ (Equiv.ext fun i => h i)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · left
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [if_neg, smul_zero]
    intro h
    have hgσ : g = σ := funext fun i => (h i).symm
    exact hg (hgσ ▸ σ.bijective)

private lemma detC_eq {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin d)) (h : s.card = d + 1) :
    detC T.rowT s = (Matrix.of fun a b => (Pi.single (phiT (s.orderEmbOfFin h a)) (cT T (s.orderEmbOfFin h a)) :
      Fin (d + 1) → S) b).det := by
  simp only [detC, dif_pos h, rowT_eq]

private lemma detC_id {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin d)) (h : s.card = d + 1) (f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Fin d)
    (hfs : ∀ a, f a ∈ s) (hf : StrictMono f) (hφ : ∀ a, phiT (f a) = a) :
    detC T.rowT s = ∏ a, cT T (f a) := by
  have hf' : ∀ a, s.orderEmbOfFin h a = f a := fun a =>
    (congrFun (Finset.orderEmbOfFin_unique h hfs hf) a).symm
  rw [detC_eq T s h]
  simp only [hf', hφ]
  rw [show (Matrix.of fun a b => (Pi.single a (cT T (f a)) : Fin (d + 1) → S) b) =
      Matrix.diagonal (fun a => cT T (f a)) from ?_]
  · exact Matrix.det_diagonal
  · ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [Matrix.diagonal_apply_ne _ hab, Pi.single_apply, Ne.symm hab]

private lemma mem_uni_inl {d : ℕ} (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) (i : Fin (d + 1)) :
    toLex (Sum.inl i) ∈ uni I L ↔ i ∈ I := by
  simp [uni]

private lemma mem_uni_inr {d : ℕ} (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) (l : Fin d) :
    toLex (Sum.inr l) ∈ uni I L ↔ l ∈ L := by
  simp [uni]

private lemma card_uni' {d : ℕ} (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) :
    (uni I L).card = I.card + L.card := by
  simp [uni]

private lemma prod_uni' {d : ℕ} {S : Type} [CommMonoid S] (I : Finset (Fin (d + 1))) (L : Finset (Fin d))
    (c : Fin (d + 1) ⊕ₗ Fin d → S) :
    ∏ t ∈ uni I L, c t = (∏ i ∈ I, c (toLex (Sum.inl i))) * ∏ l ∈ L, c (toLex (Sum.inr l)) := by
  rw [uni, Finset.prod_map, Finset.prod_disjSum]
  rfl

private lemma prod_emb {α M : Type} [LinearOrder α] [CommMonoid M] (s : Finset α) {k : ℕ} (h : s.card = k) (c : α → M) :
    ∏ a, c (s.orderEmbOfFin h a) = ∏ t ∈ s, c t := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ s h]
  rw [Finset.prod_map]
  rfl

private theorem wd_lmul_app_detC_eq_zero_of_det (hD : Det) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E]
    [Module ℂ E] (T : Sys d S E) :
    (wd fun t => (Algebra.lmul ℂ S) (app (fun _ => (1 : S)) (fun l : Fin d => (T.X l.succ : S)) t))
      (detC T.rowT) = 0 := by
  have key := hD S S (Algebra.lmul ℂ S) (Fin (d + 1) ⊕ₗ Fin d) (d + 1) T.rowT (fun _ => 1) 1
  have h1 : (fun l => Algebra.lmul ℂ S (∑ b, T.rowT l b * 1)) =
      fun t => Algebra.lmul ℂ S (app (fun _ => (1 : S)) (fun l : Fin d => (T.X l.succ : S)) t) := by
    funext t
    rw [show (∑ b, T.rowT t b * 1) = cT T t by simp [rowT_eq]]
    rfl
  have h2 : (fun s => Algebra.lmul ℂ S (detC T.rowT s) 1) = detC T.rowT := by
    funext s
    simp
  rw [h1, h2] at key
  exact key

private theorem detC_uni_univ_empty {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) : detC T.rowT (uni Finset.univ ∅) = 1 := by
  rw [detC_id T (uni Finset.univ ∅) (by simp [card_uni']) (fun a => toLex (Sum.inl a))
    (fun a => (mem_uni_inl _ _ a).2 (Finset.mem_univ a)) Sum.Lex.inl_strictMono (fun a => rfl)]
  simp [cT, app]

private theorem detC_uni_singleton_zero_univ {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) : detC T.rowT (uni {0} Finset.univ) = ∏ l : Fin d, (T.X l.succ : S) := by
  let f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Fin d := fun a =>
    Fin.cases (motive := fun _ => Fin (d + 1) ⊕ₗ Fin d) (toLex (Sum.inl 0)) (fun l => toLex (Sum.inr l)) a
  have hfs : ∀ a, f a ∈ uni {0} Finset.univ := by
    intro a
    cases a using Fin.cases with
    | zero => exact (mem_uni_inl _ _ 0).2 (Finset.mem_singleton_self 0)
    | succ l => exact (mem_uni_inr _ _ l).2 (Finset.mem_univ l)
  have hf : StrictMono f := by
    intro a b hab
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact absurd hab (lt_irrefl _)
      | succ l => exact Sum.Lex.inl_lt_inr _ _
    | succ i =>
      cases b using Fin.cases with
      | zero => exact absurd hab (Fin.not_lt_zero _)
      | succ l => exact Sum.Lex.inr_strictMono (Fin.succ_lt_succ_iff.1 hab)
  have hφ : ∀ a, phiT (f a) = a := by
    intro a
    cases a using Fin.cases <;> rfl
  have hcard : (uni ({0} : Finset (Fin (d + 1))) (Finset.univ : Finset (Fin d))).card = d + 1 := by
    rw [card_uni', Finset.card_singleton, Finset.card_univ, Fintype.card_fin, add_comm]
  rw [detC_id T _ hcard f hfs hf hφ, Fin.prod_univ_succ]
  simp [f, cT, app]

private theorem detC_uni_eq_zero_or_eq_unit_smul_prod_compl {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) :
    detC T.rowT (uni I L) = 0 ∨
      0 ∈ I ∧ I.card + L.card = d + 1 ∧ ∃ ε : ℤˣ, detC T.rowT (uni I L) = ε • ∏ m ∈ Iᶜ, (T.X m : S) := by
  by_cases hc : (uni I L).card = d + 1
  swap
  · left
    simp only [detC, dif_neg hc]
  rcases det_single (fun a => phiT ((uni I L).orderEmbOfFin hc a))
      (fun a => cT T ((uni I L).orderEmbOfFin hc a)) with h0 | ⟨hbij, ε, hε⟩
  · left
    rw [detC_eq T _ hc]
    exact h0
  · right
    have hdet := (detC_eq T _ hc).trans hε
    have hmem : ∀ t, t ∈ uni I L ↔ ∃ a, (uni I L).orderEmbOfFin hc a = t := by
      intro t
      rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (uni I L) hc, Set.mem_range]
    have h0I : 0 ∈ I := by
      obtain ⟨a, ha⟩ := hbij.2 0
      replace ha : phiT ((uni I L).orderEmbOfFin hc a) = 0 := ha
      have hA : (uni I L).orderEmbOfFin hc a ∈ uni I L := Finset.orderEmbOfFin_mem _ hc a
      generalize (uni I L).orderEmbOfFin hc a = t at ha hA
      rcases t with i | l
      · change i = 0 at ha
        subst ha
        exact (mem_uni_inl I L _).1 hA
      · exact absurd ha (Fin.succ_ne_zero l)
    have hcard : I.card + L.card = d + 1 := by
      rw [← card_uni']
      exact hc
    have hcompl : Iᶜ = L.map (Fin.succEmb d) := by
      ext m
      simp only [Finset.mem_compl, Finset.mem_map, Fin.coe_succEmb]
      constructor
      · intro hm
        obtain ⟨a, ha⟩ := hbij.2 m
        replace ha : phiT ((uni I L).orderEmbOfFin hc a) = m := ha
        have hA : (uni I L).orderEmbOfFin hc a ∈ uni I L := Finset.orderEmbOfFin_mem _ hc a
        generalize (uni I L).orderEmbOfFin hc a = t at ha hA
        rcases t with i | l
        · change i = m at ha
          subst ha
          exact absurd ((mem_uni_inl I L _).1 hA) hm
        · exact ⟨l, (mem_uni_inr I L l).1 hA, ha⟩
      · rintro ⟨l, hl, rfl⟩ hI
        obtain ⟨a, ha⟩ := (hmem (toLex (Sum.inl l.succ))).1 ((mem_uni_inl I L _).2 hI)
        obtain ⟨b, hb⟩ := (hmem (toLex (Sum.inr l))).1 ((mem_uni_inr I L _).2 hl)
        have hab : a = b := hbij.1 (by
          show phiT ((uni I L).orderEmbOfFin hc a) = phiT ((uni I L).orderEmbOfFin hc b)
          rw [ha, hb]
          rfl)
        rw [hab, hb] at ha
        exact Sum.inl_ne_inr (toLex.injective ha.symm)
    refine ⟨h0I, hcard, ε, ?_⟩
    rw [hdet, prod_emb (uni I L) hc (cT T), prod_uni', hcompl, Finset.prod_map]
    simp [cT, app]

theorem UpperTheory.Gal.productCup_of_system.thT_of :
    Det → ThT := by
  intro hD d S E _ _ _ _ T
  exact ⟨wd_lmul_app_detC_eq_zero_of_det hD T, detC_uni_univ_empty T, detC_uni_singleton_zero_univ T, detC_uni_eq_zero_or_eq_unit_smul_prod_compl T⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PColQEx
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma wd_zero' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (x : Finset ι → E) (t : Finset ι) : wd (fun _ : ι => (0 : Module.End ℂ E)) x t = 0 := by
  simp [wd]

private theorem uni_inter_map_inrE {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ]
    (b : Finset β) (L : Finset κ) :
    uni b L ∩ Finset.map (inrE (β := β)).toEmbedding Finset.univ = L.map (inrE (β := β)).toEmbedding := by
  ext x
  simp [GlobalTheory.WH.uni, inrE]
  constructor
  · rintro ⟨h, a, rfl⟩
    exact ⟨a, by simpa using h, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨by simpa using ha, a, rfl⟩

theorem UpperTheory.Gal.productCup_of_system.colQEx_of :
    WdUni → ColQEx := by
  intro hU β κ E _ _ _ _ _ _ A w d hK n m hm c hc hlev hcz
  set Q := Finset.map (inrE (β := β) (κ := κ)).toEmbedding Finset.univ with hQ
  have hQc : ∀ (b : Finset β) (L : Finset κ), (uni b L ∩ Q).card = L.card := by
    intro b L
    rw [hQ, uni_inter_map_inrE]
    simp
  have hl : (fun i : β => wOn Q w (inlE i)) = fun _ => 0 := by
    funext i
    have : inlE (κ := κ) i ∉ Q := by
      simp [hQ, inlE, inrE]
    simp [wOn, this]
  have hr : (fun l : κ => wOn Q w (inrE l)) = fun l => w (inrE l) := by
    funext l
    have : inrE (β := β) l ∈ Q := by
      simp [hQ]
    simp [wOn, this]
  have hdec : ∀ (x : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ),
      wd (wOn Q w) x (uni b L) =
        (-1 : ℤ) ^ b.card • wd (fun l => w (inrE l)) (fun L' => x (uni b L')) L := by
    intro x b L
    rw [(hU β κ E (wOn Q w) x b L).1, hl, hr, wd_zero', zero_add]
  have hmem : ∀ s, c s ∈ (if ((s.card : ℕ) : ℤ) = n then A s else ⊥) := by
    intro s
    have := hc
    simp only [acx, Submodule.mem_pi, Set.mem_univ, true_implies] at this
    exact this s
  have hY : ∀ b : Finset β, ∃ Y ∈ (colA A w b).C (m - 1),
      wd (fun l => w (inrE l)) Y = fun L => c (uni b L) := by
    intro b
    have hz : (fun L => c (uni b L)) ∈ (colA A w b).Z m := by
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [colA, acx, Submodule.mem_pi]
        intro L _
        show c (uni b L) ∈ (if ((L.card : ℕ) : ℤ) = m then A (uni b L) else ⊥)
        by_cases hL : ((L.card : ℕ) : ℤ) = m
        · rw [if_pos hL]
          have h1 := hmem (uni b L)
          split_ifs at h1 with h2
          · exact h1
          · rw [Submodule.mem_bot] at h1
            rw [h1]
            exact Submodule.zero_mem _
        · rw [if_neg hL, Submodule.mem_bot]
          apply hlev
          show ¬ (((uni b L ∩ Q).card : ℕ) : ℤ) = m
          rwa [show (uni b L ∩ Q).card = L.card by convert hQc b L]
      · rw [LinearMap.mem_ker]
        change wd (fun l => w (inrE l)) (fun L => c (uni b L)) = 0
        funext L
        have h1 : (wd (wOn Q w)) c (uni b L) = 0 := by
          exact congrFun hcz (uni b L)
        rw [hdec] at h1
        simp only [Pi.zero_apply]
        have h2 := congrArg (fun v => (-1 : ℤ) ^ b.card • v) h1
        simp only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, smul_zero] at h2
        exact h2
    obtain ⟨Y, hY1, hY2⟩ := hK b m hm hz
    exact ⟨Y, hY1, hY2⟩
  choose Y hYC hYD using hY
  have hYmem : ∀ b L, Y b L ∈ (if ((L.card : ℕ) : ℤ) = m - 1 then A (uni b L) else ⊥) := by
    intro b L
    have := hYC b
    rw [colA, acx, Submodule.mem_pi] at this
    exact this L (Set.mem_univ _)
  have hU2 := fun s => (hU β κ E w c (lft s) (rgt s)).2.2.2.2 s
  have hQs : ∀ s, (s ∩ Q).card = (rgt s).card := by
    intro s
    have := hQc (lft s) (rgt s)
    rw [hU2 s] at this
    exact this
  obtain ⟨y, hy⟩ : ∃ y : Finset (β ⊕ₗ κ) → E, ∀ s, y s = if (((lft s).card : ℕ) : ℤ) = n - m then
      (-1 : ℤ) ^ (lft s).card • Y (lft s) (rgt s) else 0 := ⟨_, fun s => rfl⟩
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [acx, Submodule.mem_pi]
    intro s _
    show y s ∈ (if ((s.card : ℕ) : ℤ) = n - 1 then A s else ⊥)
    rw [hy]
    have hs := hYmem (lft s) (rgt s)
    rw [hU2 s] at hs
    have hcard := (hU β κ E w c (lft s) (rgt s)).2.2.2.1
    rw [hU2 s] at hcard
    by_cases h1 : (((lft s).card : ℕ) : ℤ) = n - m
    · rw [if_pos h1]
      by_cases h2 : ((s.card : ℕ) : ℤ) = n - 1
      · rw [if_pos h2]
        by_cases h3 : (((rgt s).card : ℕ) : ℤ) = m - 1
        · rw [if_pos h3] at hs
          exact zsmul_mem hs _
        · rw [if_neg h3, Submodule.mem_bot] at hs
          rw [hs, smul_zero]
          exact Submodule.zero_mem _
      · rw [if_neg h2, Submodule.mem_bot]
        rw [if_neg, Submodule.mem_bot] at hs
        · rw [hs, smul_zero]
        · intro h3
          apply h2
          rw [hcard]
          push_cast
          omega
    · rw [if_neg h1]
      exact Submodule.zero_mem _
  · intro s hs
    rw [hy]
    split_ifs with h1
    · have hY0 := hYmem (lft s) (rgt s)
      rw [if_neg] at hY0
      · rw [Submodule.mem_bot] at hY0
        rw [hY0, smul_zero]
      · intro h3
        apply hs
        show (((s ∩ Q).card : ℕ) : ℤ) = m - 1
        rw [hQs s]
        exact h3
    · rfl
  · funext t
    obtain ⟨b, L, rfl⟩ : ∃ b L, t = uni b L := ⟨lft t, rgt t, (hU2 t).symm⟩
    refine Eq.trans (b := (-1 : ℤ) ^ b.card • wd (fun l => w (inrE l)) (fun L' => y (uni b L')) L) ?_ ?_
    · convert hdec y b L
    have hb2 := hU β κ E w c b
    have hfun : (fun L' => y (uni b L')) =
        if (((b.card : ℕ) : ℤ) = n - m) then (-1 : ℤ) ^ b.card • Y b else 0 := by
      funext L'
      rw [hy, (hb2 L').2.1, (hb2 L').2.2.1]
      split_ifs <;> rfl
    rw [hfun]
    by_cases hb : (((b.card : ℕ) : ℤ) = n - m)
    · rw [if_pos hb, map_zsmul, Pi.smul_apply, hYD, smul_smul, ← mul_pow]
      simp
    · rw [if_neg hb, map_zero, Pi.zero_apply, smul_zero]
      symm
      by_cases hL : ((L.card : ℕ) : ℤ) = m
      · have h5 := hmem (uni b L)
        rw [if_neg] at h5
        · exact (Submodule.mem_bot _).1 h5
        · intro hn
          apply hb
          rw [(hb2 L).2.2.2.1] at hn
          push_cast at hn
          omega
      · apply hlev
        show ¬ ((((uni b L ∩ Q).card : ℕ) : ℤ) = m)
        rwa [show (uni b L ∩ Q).card = L.card by convert hQc b L]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PWdUni
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {β κ : Type} [LinearOrder β] [LinearOrder κ]

private theorem lex_cases (t : β ⊕ₗ κ) : (∃ i, t = inlE i) ∨ ∃ l, t = inrE l := by
  rcases t with i | l
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨l, rfl⟩

private theorem mem_uni_l (b : Finset β) (L : Finset κ) (i : β) :
    (inlE i : β ⊕ₗ κ) ∈ uni b L ↔ i ∈ b := by
  simp [uni, inlE]

private theorem mem_uni_r (b : Finset β) (L : Finset κ) (l : κ) :
    (inrE l : β ⊕ₗ κ) ∈ uni b L ↔ l ∈ L := by
  simp [uni, inrE]

private theorem mem_lft (s : Finset (β ⊕ₗ κ)) (i : β) : i ∈ lft s ↔ (inlE i : β ⊕ₗ κ) ∈ s := by
  simp [lft, inlE]

private theorem mem_rgt (s : Finset (β ⊕ₗ κ)) (l : κ) : l ∈ rgt s ↔ (inrE l : β ⊕ₗ κ) ∈ s := by
  simp [rgt, inrE]

private theorem l_lt_r (i : β) (l : κ) : (inlE i : β ⊕ₗ κ) < inrE l := Sum.Lex.inl_lt_inr i l

private theorem not_r_lt_l (i : β) (l : κ) : ¬ (inrE l : β ⊕ₗ κ) < inlE i := Sum.Lex.not_inr_lt_inl

private theorem card_uni (b : Finset β) (L : Finset κ) : (uni b L).card = b.card + L.card := by
  simp [uni]

private theorem sum_uni {M : Type} [AddCommMonoid M] (b : Finset β) (L : Finset κ) (f : β ⊕ₗ κ → M) :
    ∑ t ∈ uni b L, f t = ∑ i ∈ b, f (inlE i) + ∑ l ∈ L, f (inrE l) := by
  rw [uni, Finset.sum_map, Finset.sum_disjSum]
  rfl

private theorem erase_l [DecidableEq (β ⊕ₗ κ)] (b : Finset β) (L : Finset κ) (i : β) :
    (uni b L).erase (inlE i) = uni (b.erase i) L := by
  ext t
  rcases lex_cases t with ⟨j, rfl⟩ | ⟨m, rfl⟩
  · rw [Finset.mem_erase, mem_uni_l, mem_uni_l, Finset.mem_erase, inlE.injective.ne_iff]
  · rw [Finset.mem_erase, mem_uni_r, mem_uni_r]
    exact and_iff_right (l_lt_r i m).ne'

private theorem erase_r [DecidableEq (β ⊕ₗ κ)] (b : Finset β) (L : Finset κ) (l : κ) :
    (uni b L).erase (inrE l) = uni b (L.erase l) := by
  ext t
  rcases lex_cases t with ⟨j, rfl⟩ | ⟨m, rfl⟩
  · rw [Finset.mem_erase, mem_uni_l, mem_uni_l]
    exact and_iff_right (l_lt_r j l).ne
  · rw [Finset.mem_erase, mem_uni_r, mem_uni_r, Finset.mem_erase, inrE.injective.ne_iff]

private theorem sign_l (b : Finset β) (L : Finset κ) (i : β) :
    GlobalTheory.cubeSign (uni b L) (inlE i) = GlobalTheory.cubeSign b i := by
  unfold GlobalTheory.cubeSign
  congr 1
  rw [Finset.card_filter, Finset.card_filter, sum_uni]
  simp [not_r_lt_l]

private theorem sign_r (b : Finset β) (L : Finset κ) (l : κ) :
    GlobalTheory.cubeSign (uni b L) (inrE l) = (-1 : ℤ) ^ b.card * GlobalTheory.cubeSign L l := by
  unfold GlobalTheory.cubeSign
  rw [← pow_add]
  congr 1
  rw [Finset.card_filter, Finset.card_filter, sum_uni]
  simp [l_lt_r]

private theorem wd_app {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

end

theorem UpperTheory.Gal.productCup_of_system.wdUni_of :
    WdUni := by
  intro β κ E _ _ _ _ w c b L
  refine ⟨?_, ?_, ?_, card_uni b L, ?_⟩
  · rw [wd_app, wd_app, wd_app, sum_uni, Finset.smul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by rw [sign_l, erase_l]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [sign_r, erase_r, mul_smul]
  · ext i
    rw [mem_lft, mem_uni_l]
  · ext l
    rw [mem_rgt, mem_uni_r]
  · intro s
    ext t
    rcases lex_cases t with ⟨j, rfl⟩ | ⟨l, rfl⟩
    · rw [mem_uni_l, mem_lft]
    · rw [mem_uni_r, mem_rgt]
end

