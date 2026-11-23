module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0008
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RatioConditionOfSegFacts
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0009
public import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfValuationBound
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M

section Hyp

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

theorem hypU_proved (hB : G.BlockOK) : Formalism.InvariantFactorPaths.KP.LL.HypU p (r := r) G := by
  have hpol : ∀ (LL LL' : M.Letters N) (a : Fin N) (c : Fin r), LL'.deg a = LL.deg a - 1 →
      (∀ i, i ≠ a → LL'.deg i = LL.deg i) →
      ∀ y ∈ M.Pol p r LL, pderiv (a, c) y ∈ M.Pol p r LL' := by
    intro LL LL' a c hda hdo y hy
    unfold M.Pol at hy ⊢
    rw [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Submodule.mem_comap, Finsupp.mem_supported] at hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [y.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [MvPolynomial.pderiv_monomial]
    by_cases h0 : m (a, c) = 0
    · rw [h0, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]
      exact zero_mem _
    · have hmd : M.MultiDeg LL m := hy (Finset.mem_coe.mpr hm)
      rw [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Submodule.mem_comap, Finsupp.mem_supported]
      refine (Finset.coe_subset.mpr MvPolynomial.support_monomial_subset).trans ?_
      rw [Finset.coe_singleton, Set.singleton_subset_iff]
      show M.MultiDeg LL' (m - Finsupp.single (a, c) 1)
      intro i
      by_cases hi : i = a
      · subst hi
        have key : ∀ c', ((m - Finsupp.single (i, c) 1 : (Fin N × Fin r) →₀ ℕ) (i, c')) + (if c' = c then 1 else 0) =
            m (i, c') := by
          intro c'
          rw [Finsupp.tsub_apply, Finsupp.single_apply]
          by_cases hc : c' = c
          · subst hc
            rw [if_pos rfl, if_pos rfl]
            omega
          · have hne : ¬ (i, c) = (i, c') := fun h => hc (congrArg Prod.snd h).symm
            rw [if_neg hne, if_neg hc]
            simp
        have hs : ∑ c', (((m - Finsupp.single (i, c) 1 : (Fin N × Fin r) →₀ ℕ) (i, c')) + (if c' = c then 1 else 0)) =
            ∑ c', m (i, c') := Finset.sum_congr rfl fun c' _ => key c'
        have h1 : ∑ c' : Fin r, (if c' = c then 1 else 0 : ℕ) = 1 := by simp
        rw [Finset.sum_add_distrib, h1] at hs
        rw [hda, ← hmd i]
        omega
      · rw [hdo i hi, ← hmd i]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finsupp.tsub_apply, Finsupp.single_apply,
          if_neg (fun h => hi (congrArg Prod.fst h).symm), Nat.sub_zero]
  intro j jp c y hy
  simp only [M.Y, Submodule.mem_inf, Submodule.mem_iInf] at hy ⊢
  refine ⟨hpol _ _ G.uPos c ?_ ?_ y hy.1, fun k => ?_⟩
  · simp only [M.BlockData.lettersAt, eq_self_iff_true, if_true]
    omega
  · intro i hi
    simp only [M.BlockData.lettersAt, if_neg hi]
  · rw [ycond_vec (p := p) (r := r) (G.lettersAt j (jp + 1)) (G.lettersAt j jp) rfl]
    exact pderiv_ycond (p := p) _ _ _ G.uPos (fun _ => hB.2.2.1) c y (hy.2 k)

theorem sum_update_ite {t : ℕ} (P : Fin t → Prop) [DecidablePred P] (j : Fin t → ℕ) (i : Fin t) :
    ∑ i', (if P i' then Function.update j i (j i + 1) i' else 0) =
      ∑ i', (if P i' then j i' else 0) + (if P i then 1 else 0) := by
  have h : ∀ i', (if P i' then Function.update j i (j i + 1) i' else 0) =
      (if P i' then j i' else 0) + (if i' = i then (if P i then 1 else 0) else 0) := by
    intro i'
    by_cases hi : i' = i
    · subst hi
      rw [Function.update_self]
      split_ifs <;> simp_all
    · rw [Function.update_of_ne hi, if_neg hi, add_zero]
  rw [Finset.sum_congr rfl fun i' _ => h i', Finset.sum_add_distrib]
  simp

theorem hypTie_proved (hB : G.BlockOK) : Formalism.InvariantFactorPaths.KP.LL.HypJoin p (r := r) G := by
  have hpol : ∀ (LL LL' : M.Letters N) (a : Fin N) (c : Fin r), LL'.deg a = LL.deg a - 1 →
      (∀ i, i ≠ a → LL'.deg i = LL.deg i) →
      ∀ y ∈ M.Pol p r LL, pderiv (a, c) y ∈ M.Pol p r LL' := by
    intro LL LL' a c hda hdo y hy
    unfold M.Pol at hy ⊢
    rw [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Submodule.mem_comap, Finsupp.mem_supported] at hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [y.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [MvPolynomial.pderiv_monomial]
    by_cases h0 : m (a, c) = 0
    · rw [h0, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]
      exact zero_mem _
    · have hmd : M.MultiDeg LL m := hy (Finset.mem_coe.mpr hm)
      rw [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Submodule.mem_comap, Finsupp.mem_supported]
      refine (Finset.coe_subset.mpr MvPolynomial.support_monomial_subset).trans ?_
      rw [Finset.coe_singleton, Set.singleton_subset_iff]
      show M.MultiDeg LL' (m - Finsupp.single (a, c) 1)
      intro i
      by_cases hi : i = a
      · subst hi
        have key : ∀ c', ((m - Finsupp.single (i, c) 1 : (Fin N × Fin r) →₀ ℕ) (i, c')) + (if c' = c then 1 else 0) =
            m (i, c') := by
          intro c'
          rw [Finsupp.tsub_apply, Finsupp.single_apply]
          by_cases hc : c' = c
          · subst hc
            rw [if_pos rfl, if_pos rfl]
            omega
          · have hne : ¬ (i, c) = (i, c') := fun h => hc (congrArg Prod.snd h).symm
            rw [if_neg hne, if_neg hc]
            simp
        have hs : ∑ c', (((m - Finsupp.single (i, c) 1 : (Fin N × Fin r) →₀ ℕ) (i, c')) + (if c' = c then 1 else 0)) =
            ∑ c', m (i, c') := Finset.sum_congr rfl fun c' _ => key c'
        have h1 : ∑ c' : Fin r, (if c' = c then 1 else 0 : ℕ) = 1 := by simp
        rw [Finset.sum_add_distrib, h1] at hs
        rw [hda, ← hmd i]
        omega
      · rw [hdo i hi, ← hmd i]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finsupp.tsub_apply, Finsupp.single_apply,
          if_neg (fun h => hi (congrArg Prod.fst h).symm), Nat.sub_zero]
  intro j jp i y hy
  obtain ⟨hlt, hvW, hvE⟩ := hB.1.2.1 i
  set W := G.letterAt (G.T.pos i) with hWdef
  set E := G.letterAt (G.T.pos i + 1) with hEdef
  have hWv : (W : ℕ) = G.T.pos i := by
    simp only [hWdef, M.BlockData.letterAt]
    omega
  have hEv : (E : ℕ) = G.T.pos i + 1 := by
    simp only [hEdef, M.BlockData.letterAt]
    omega
  have hWE : W ≠ E := fun h => by
    have := congrArg Fin.val h
    omega
  have hvW' : G.LL.vec W = true := by
    rwa [show W = ⟨G.T.pos i, by omega⟩ from Fin.ext hWv]
  have hvE' : G.LL.vec E = false := by
    rwa [show E = ⟨G.T.pos i + 1, hlt⟩ from Fin.ext hEv]

  have hdeg : ∀ x : Fin N, (G.lettersAt (Function.update j i (j i + 1)) jp).deg x =
      (G.lettersAt j jp).deg x -
        (if ((x : ℕ) = G.T.pos i ∨ (x : ℕ) = G.T.pos i + 1) then 1 else 0) := by
    intro x
    simp only [M.BlockData.lettersAt]
    change G.LL.deg x - (∑ k : Fin G.T.t, if (x : ℕ) = G.T.pos k ∨
      (x : ℕ) = G.T.pos k + 1 then Function.update j i (j i + 1) k else 0) -
      (if x = G.uPos then jp else 0) =
      (G.LL.deg x - (∑ k : Fin G.T.t, if (x : ℕ) = G.T.pos k ∨
        (x : ℕ) = G.T.pos k + 1 then j k else 0) -
        (if x = G.uPos then jp else 0)) - _
    rw [sum_update_ite]
    omega
  have htie : ∀ x : MvPolynomial (Fin N × Fin r) ℚ_[p],
      Formalism.GM.tieF (fun c => (W, c)) (fun c => (E, c)) x =
      ∑ c, pderiv (W, c) (pderiv (E, c) x) := by
    intro x
    simp [Formalism.GM.tieF]
  simp only [M.Y, Submodule.mem_inf, Submodule.mem_iInf] at hy ⊢
  refine ⟨?_, fun k => ?_⟩
  · rw [htie]
    refine Submodule.sum_mem _ fun c _ => ?_
    let L1 : M.Letters N := ⟨G.LL.vec, fun x =>
      if x = E then (G.lettersAt j jp).deg x - 1 else (G.lettersAt j jp).deg x⟩
    have h1 := hpol (G.lettersAt j jp) L1 E c (by show (if E = E then _ else _) = _; rw [if_pos rfl])
      (fun x hx => by show (if x = E then _ else _) = _; rw [if_neg hx]) y hy.1
    refine hpol L1 _ W c ?_ ?_ _ h1
    · rw [hdeg W, if_pos (Or.inl hWv)]
      show _ = (if W = E then _ else _) - 1
      rw [if_neg hWE]
    · intro x hx
      rw [hdeg x]
      show _ = (if x = E then _ else _)
      by_cases hxE : x = E
      · have hxv : (x : ℕ) = G.T.pos i + 1 := by rw [hxE]; exact hEv
        rw [if_pos hxE, if_pos (Or.inr hxv)]
      · rw [if_neg hxE, if_neg, Nat.sub_zero]
        rintro (h | h)
        · exact hx (Fin.ext (h.trans hWv.symm))
        · exact hxE (Fin.ext (h.trans hEv.symm))
  · rw [ycond_vec (p := p) (r := r) (G.lettersAt (Function.update j i (j i + 1)) jp)
      (G.lettersAt j jp) rfl]
    have hx := hy.2 k
    by_cases hE : (E : ℕ) < G.T.J k
    · exact tieF_ycond (p := p) (G.lettersAt j jp) (G.T.J k) (G.T.thr k) W E (by omega) hE hvW' hvE' y hx
    · rw [htie]
      exact Submodule.sum_mem _ fun c _ => pderiv_ycond (p := p) _ _ _ W (fun _ => hvW') c _
        (pderiv_ycond (p := p) _ _ _ E (fun h => absurd h hE) c y hx)

end Hyp

section Inst

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem restLL_proved {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : RestLL C0 CE1 CE2 X :=
  restLL_of C0 CE1 CE2 X hCYb hCE1 hCE2 hH fun aTop aPlus b =>
    ⟨hypTie_proved X.p _ (gB_blockOK C0 CE1 CE2 X aTop aPlus b),
      hypU_proved X.p _ (gB_blockOK C0 CE1 CE2 X aTop aPlus b)⟩

theorem block_valuation_Zp_of_valuation_bound {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (hV : RestVal C0 CE1 CE2 X) : BlockBoundIntegers C0 CE1 CE2 X :=
  block_valuation_Zp_of_lattice_inclusion C0 CE1 CE2 X (Nat.one_le_iff_ne_zero.mpr X.hm)
    (restLL_proved C0 CE1 CE2 X hCYb hCE1 hCE2 hH) hV

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfOpenConditions
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem thr_mono_seg {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cc, 2 ≤ CYb → 0 ≤ CD → 1 ≤ Cb → 0 ≤ CE1 → 0 ≤ CE2 →
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cc → Q C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : TransportedAlt P) : TransportedAlt Q := by
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hP Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 a1 a2 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 a1 a2
  refine ⟨max T2 2, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => ?_⟩
  have m1 := le_max_left T2 2
  have m2 := le_max_right T2 2
  exact h _ _ _ _ _ _ _ _ _ (m2.trans b1) (by linarith) (by linarith) (by linarith) (by linarith)
    (h2 CYb Cde Ck CD Cb (m1.trans b1) (m1.trans b2) (m1.trans b3) (m1.trans b4) (m1.trans b5))

def RestOpen (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    BlockBoundUniformiser C0 CE1 CE2 X ∧ RestPlus C0 CE1 CE2 X CM ∧ RestTM C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X

def RestOpenE (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ CM : ℝ, 0 ≤ CM ∧
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restAllE_of_open (D : Formalism.BasicNotions.D7) (h : RestOpenE D) : RestAllE D :=
  thr_mono_seg (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hY hD hb h1 h2 hP Ckap Cs => by
    obtain ⟨CM, hCM, hX⟩ := hP Ckap Cs
    have he : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
    refine ⟨CM, max (2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3) (18 * (1 + CM) + 20), hCM,
      le_max_of_le_right (by linarith), le_max_left _ _, fun X hA hH => ?_⟩
    obtain ⟨a, b, c, d⟩ := hX X hA hH
    have hS := segFacts hY hb hD h1 h2 hH
    exact ⟨a, b, c, d, restFree_proved hS, ratioCondition_of_segFacts hS,
      restDepth_proved CM _ (by linarith) hCM (le_max_right _ _) hH⟩) h

theorem closed_of_open_conditions (D : Formalism.BasicNotions.D7) (h : RestOpenE D) : IntegralityFromMetricForLargeConstants D :=
  theorem_A_closed_of_all_remaining_bounds D (restAllE_of_open D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MfacMapDomainAdd
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Disj

variable {k σ τ : Type} [Field k] [DecidableEq σ] [DecidableEq τ]

theorem mapDomain_add_inj (e : τ → σ) (he : Function.Injective e) (a b : τ →₀ ℕ) (β β' : σ →₀ ℕ)
    (hβ : ∀ x, β (e x) = 0) (hβ' : ∀ x, β' (e x) = 0)
    (h : Finsupp.mapDomain e a + β = Finsupp.mapDomain e b + β') : a = b ∧ β = β' := by
  have ha : a = b := by
    ext x
    have h1 := DFunLike.congr_fun h (e x)
    simpa [Finsupp.mapDomain_apply_of_injective he, hβ, hβ'] using h1
  subst ha
  exact ⟨rfl, add_left_cancel h⟩

theorem mfac_mapDomain_add (e : τ → σ) (he : Function.Injective e) (a : τ →₀ ℕ) (β : σ →₀ ℕ)
    (hβ : ∀ x, β (e x) = 0) : (mfac (Finsupp.mapDomain e a + β) : k) = mfac a * mfac β := by
  unfold mfac
  have hd : Disjoint (Finsupp.mapDomain e a).support β.support := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    exact (Finsupp.mem_support_iff.1 hx') (hβ y)
  rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_mapDomain_index_inj he]

theorem fockK_rename_mul (e : τ → σ) (he : Function.Injective e) (A B : MvPolynomial τ k) (β β' : σ →₀ ℕ) (c : k)
    (hβ : ∀ x, β (e x) = 0) (hβ' : ∀ x, β' (e x) = 0) :
    Formalism.GM.M.fockK (rename e A * monomial β 1) (rename e B * monomial β' c) =
      if β = β' then c * mfac β * Formalism.GM.M.fockK A B else 0 := by
  classical
  set F := rename e A * monomial β (1 : k) with hF
  set G := rename e B * monomial β' c with hG
  have hcF : ∀ m, F.coeff (Finsupp.mapDomain e m + β) = A.coeff m := by
    intro m
    rw [hF, MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain e he, mul_one]
  have hcF0 : ∀ n, F.coeff n ≠ 0 → ∃ m, n = Finsupp.mapDomain e m + β ∧ A.coeff m ≠ 0 := by
    intro n hn
    rw [hF, MvPolynomial.coeff_mul_monomial'] at hn
    split_ifs at hn with hle
    · rw [mul_one] at hn
      obtain ⟨u, hu, hu0⟩ := MvPolynomial.coeff_rename_ne_zero e A (n - β) hn
      refine ⟨u, ?_, hu0⟩
      rw [hu]
      exact (tsub_add_cancel_of_le hle).symm
    · exact absurd rfl hn
  have hcG : ∀ m, G.coeff (Finsupp.mapDomain e m + β) = if β = β' then B.coeff m * c else 0 := by
    intro m
    split_ifs with hb
    · subst hb
      rw [hG, MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain e he]
    · by_contra hne
      rw [hG, MvPolynomial.coeff_mul_monomial'] at hne
      split_ifs at hne with hle
      · have h1 : (rename e B).coeff (Finsupp.mapDomain e m + β - β') ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
        obtain ⟨u, hu, -⟩ := MvPolynomial.coeff_rename_ne_zero e B _ h1
        have h2 : Finsupp.mapDomain e m + β = Finsupp.mapDomain e u + β' := by
          rw [hu]
          exact (tsub_add_cancel_of_le hle).symm
        exact hb (mapDomain_add_inj e he m u β β' hβ hβ' h2).2
      · exact hne rfl
  have hmf : ∀ m : τ →₀ ℕ, ((Finsupp.mapDomain e m + β).prod fun _ j => (j.factorial : k)) =
      (m.prod fun _ j => (j.factorial : k)) * (β.prod fun _ j => (j.factorial : k)) :=
    fun m => mfac_mapDomain_add e he m β hβ
  unfold Formalism.GM.M.fockK
  have hsub : F.support ⊆ A.support.image (fun m => Finsupp.mapDomain e m + β) := by
    intro n hn
    obtain ⟨m, rfl, hm⟩ := hcF0 n (MvPolynomial.mem_support_iff.1 hn)
    exact Finset.mem_image.2 ⟨m, MvPolynomial.mem_support_iff.2 hm, rfl⟩
  rw [Finset.sum_subset hsub (fun n _ hn => by
    rw [MvPolynomial.mem_support_iff, not_not] at hn
    rw [hn]
    ring)]
  have hinj : Set.InjOn (fun m => Finsupp.mapDomain e m + β) A.support :=
    fun a _ b _ hab => (mapDomain_add_inj e he a b β β hβ hβ hab).1
  rw [Finset.sum_image hinj]
  simp only [hcF, hcG, hmf]
  split_ifs with hb
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    unfold mfac
    ring
  · simp

end Disj

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDimBCProved
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem restDimBC_proved : RestDimBC C0 CE1 CE2 X := by
  intro aTop _ aPlus _ b _
  set Dd := blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b with hDd
  set V0 := Submodule.span ℚ_[X.p]
    (((gmB Dd).SSZ X.p (r := X.r) : Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :
      Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) with hV0
  set W := Submodule.span (KK X.O) ((Dd.SSZ X.O (r := X.r) : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) :
      Set (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) with hW
  show Module.finrank ℚ_[X.p] V0 ≤ Module.finrank (KK X.O) W
  have : FiniteDimensional (KK X.O) W := span_SSZ_finite Dd
  by_cases hfin : FiniteDimensional ℚ_[X.p] V0
  swap
  · rw [Module.finrank_of_not_finite hfin]
    exact Nat.zero_le _

  have hmemW : ∀ x ∈ V0, MvPolynomial.map (iotaX X) x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact map_SSZ (ι := iotaX X) (iotaX_int X) Dd x hx
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul_Q]; exact W.smul_mem _ hx
  set bs := Module.finBasis ℚ_[X.p] V0
  have hli : LinearIndependent ℚ_[X.p] (fun i => (bs i : MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :=
    bs.linearIndependent.map' V0.subtype (Submodule.ker_subtype V0)
  have hli2 := li_map (iotaX X) _ hli
  let w : Fin (Module.finrank ℚ_[X.p] V0) → W := fun i => ⟨MvPolynomial.map (iotaX X) (bs i).1, hmemW _ (bs i).2⟩
  have hli3 : LinearIndependent (KK X.O) w := LinearIndependent.of_comp W.subtype hli2
  have h := hli3.fintype_card_le_finrank
  rw [Fintype.card_fin] at h
  exact h

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestSumSpan
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestLvlDim : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b → ∀ x ∈ lv C0 CE1 CE2 X aTop b,
      rL C0 CE1 CE2 X aTop b x ≤
        Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r := X.r) x.1 x.2))

def RestSumSpan : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∑ x ∈ lv C0 CE1 CE2 X aTop b,
          Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r := X.r) x.1 x.2)) ≤
        Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p]
          (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
            Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
              Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])))

variable {C0 CE1 CE2 X}

theorem restDirQ_of (h1 : RestLvlDim C0 CE1 CE2 X) (h2 : RestSumSpan C0 CE1 CE2 X) : RestDirQ C0 CE1 CE2 X :=
  fun aTop hT aPlus hP b hk =>
    (Finset.sum_le_sum fun x hx => h1 aTop hT aPlus hP b hk x hx).trans (h2 aTop hT aPlus hP b hk)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

