module

public import Formalism.HarderNarasimhan.DegSupermodZ
public import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0002

@[expose] public section

-- bundled from Formalism.HarderNarasimhan.HarderNarasimhanProofs.RatioMax
section
open Module Submodule

noncomputable section

namespace Formalism.HN

theorem le_of_imageLattice_le {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) (L N₁ N₂ : Submodule R V)
    (hinj : Set.InjOn ρ (L : Set V)) (h₁ : N₁ ≤ L) (h₂ : N₂ ≤ L) (h : zl ρ N₁ ≤ zl ρ N₂) :
    N₁ ≤ N₂ := by
  intro x hx
  have hx' : ρ x ∈ zl ρ N₂ :=
    h ((satR_mem_zl ρ N₁ (ρ x)).2 ⟨x, hx, rfl⟩)
  obtain ⟨y, hy, hyx⟩ := (satR_mem_zl ρ N₂ (ρ x)).1 hx'
  have hxy : y = x := hinj (h₂ hy) (h₁ hx) hyx
  rw [← hxy]
  exact hy

universe u v w in
theorem ratioMax_of (h1 : SatR.{u, v, w}) (h2 : SatBasic.{u, v, w}) : RatioMax.{u, v, w} := by
  unfold RatioMax
  intro R V E _ _ _ _ _ _ ρ L S hL hS hSL
  obtain ⟨hsub, hmono, hsat, -, -, -, hLsat, -⟩ := h2 R V E ρ L hL
  have hinj : Set.InjOn ρ (L : Set V) := hL.1
  have hdL : DiscreteTopology (zl ρ L) := hL.2
  have hSle : S ≤ L := hS.1
  have hSL' : S < L := lt_of_le_of_ne hSle hSL
  have hgap : ∀ N : Submodule R V, S < N → N ≤ L → (rk ρ S : ℝ) < rk ρ N := by
    intro N hSN hNL
    have hle := (hmono S N hSN.le hNL).1
    have hne : rk ρ N ≠ rk ρ S := fun he => hSN.ne (hsat S N hS hSN.le hNL he).symm
    exact_mod_cast lt_of_le_of_ne hle (Ne.symm hne)
  obtain ⟨f, hf⟩ : ∃ f : Submodule R V → ℝ, ∀ N, f N =
      (deg ρ N - deg ρ S) / ((rk ρ N : ℝ) - rk ρ S) := ⟨_, fun _ => rfl⟩
  have hdeg : ∀ N : Submodule R V, S < N → N ≤ L → f L ≤ f N →
      deg ρ S - |f L| * (rk ρ L : ℝ) ≤ deg ρ N := by
    intro N hSN hNL hc
    have hpos : 0 < (rk ρ N : ℝ) - rk ρ S := sub_pos.2 (hgap N hSN hNL)
    have hrN : (rk ρ N : ℝ) - rk ρ S ≤ rk ρ L := by
      have h3 : (rk ρ N : ℝ) ≤ rk ρ L := by exact_mod_cast (hmono N L hNL le_rfl).1
      have h4 : (0 : ℝ) ≤ rk ρ S := Nat.cast_nonneg _
      linarith
    rw [hf N, le_div_iff₀ hpos] at hc
    have h3 : -|f L| * (rk ρ L : ℝ) ≤ f L * ((rk ρ N : ℝ) - rk ρ S) := by
      calc -|f L| * (rk ρ L : ℝ) ≤ -|f L| * ((rk ρ N : ℝ) - rk ρ S) :=
            mul_le_mul_of_nonpos_left hrN (neg_nonpos.2 (abs_nonneg _))
        _ ≤ f L * ((rk ρ N : ℝ) - rk ρ S) :=
            mul_le_mul_of_nonneg_right (neg_abs_le _) hpos.le
    linarith
  obtain ⟨T, hTdef⟩ : ∃ T : Set (Submodule R V),
      T = {N | IsSat ρ L N ∧ S < N ∧ f L ≤ f N} := ⟨_, rfl⟩
  have hmemT : ∀ N, N ∈ T ↔ IsSat ρ L N ∧ S < N ∧ f L ≤ f N := by
    intro N
    subst hTdef
    exact Iff.rfl
  have hfinE := Formalism.F.finiteSaturated E (zl ρ L) hdL
      (Real.exp (-(deg ρ S - |f L| * (rk ρ L : ℝ))))
  have hT : T.Finite := by
    refine Set.Finite.of_finite_image (f := zl ρ) (hfinE.subset ?_) ?_
    · rintro _ ⟨N, hN, rfl⟩
      obtain ⟨hNs, hSN, hc⟩ := (hmemT N).1 hN
      show _ ∧ _
      refine ⟨hNs.2, ?_⟩
      have hlat := hsub N hNs.1
      have : DiscreteTopology (zl ρ N) := hlat.2
      have hcpos : 0 < Formalism.F.covol (zl ρ N) :=
        Formalism.F.covol_pos _
      have hd := hdeg N hSN hNs.1 hc
      have hdN : deg ρ N = -Real.log (Formalism.F.covol (zl ρ N)) := rfl
      rw [← Real.log_le_iff_le_exp hcpos]
      linarith
    · intro A hA B hB hAB
      have hA' := ((hmemT A).1 hA).1.1
      have hB' := ((hmemT B).1 hB).1.1
      exact le_antisymm
        (le_of_imageLattice_le ρ L A B hinj hA' hB' hAB.le)
        (le_of_imageLattice_le ρ L B A hinj hB' hA' hAB.ge)
  have hLT : L ∈ T := (hmemT L).2 ⟨hLsat, hSL', le_rfl⟩
  obtain ⟨N, hNT, hNmax⟩ := Set.exists_max_image T f hT ⟨L, hLT⟩
  obtain ⟨hNsat, hSN, -⟩ := (hmemT N).1 hNT
  refine ⟨N, hSN, hNsat, ?_⟩
  intro N' hSN' hN'L
  have hpos' : 0 < (rk ρ N' : ℝ) - rk ρ S := sub_pos.2 (hgap N' hSN' hN'L)
  have hposN : 0 < (rk ρ N : ℝ) - rk ρ S := sub_pos.2 (hgap N hSN hNsat.1)
  have key : f N' ≤ f N := by
    by_cases hc : f L ≤ f N'
    · obtain ⟨N'', hle, hN''L, himg⟩ := h1 R V E ρ L N' hL hN'L
      have hmon : zl ρ N' ≤ zl ρ L := satBasic_zl_mono ρ hN'L
      have hsp := Formalism.F.saturProps E (zl ρ L) (zl ρ N')
        hdL hmon
      have hsat'' : IsSat ρ L N'' := by
        refine And.intro hN''L ?_
        rw [himg]
        exact hsp.1
      have hrk : rk ρ N'' = rk ρ N' := by
        show Formalism.F.rk (zl ρ N'') = Formalism.F.rk (zl ρ N')
        rw [himg]
        exact hsp.2.2
      have hdg : deg ρ N' ≤ deg ρ N'' := (hmono N' N'' hle hN''L).2 hrk.symm
      have hff : f N' ≤ f N'' := by
        rw [hf N', hf N'', hrk, div_le_div_iff₀ hpos' hpos']
        exact mul_le_mul_of_nonneg_right (by linarith) hpos'.le
      have hN''T : N'' ∈ T := (hmemT N'').2 ⟨hsat'', lt_of_lt_of_le hSN' hle, hc.trans hff⟩
      exact hff.trans (hNmax N'' hN''T)
    · have hlt : f N' < f L := not_le.1 hc
      exact hlt.le.trans ((hmemT N).1 hNT).2.2
  rw [hf N', hf N, div_le_div_iff₀ hpos' hposN] at key
  exact key

theorem maximal_slope_ratio : RatioMax :=
  ratioMax_of real_saturation_property saturation_basic_properties

end Formalism.HN
end
end

-- bundled from Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
section
open Module Submodule

noncomputable section

namespace Formalism.HN

universe u v w w₂

theorem shiftInv_zl_mono {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) {A B : Submodule R V}
    (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  exact satBasic_zl_mono ρ h

theorem shiftInv_isSat_iff {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    {L : Submodule R V} (hL : IsLat ρ L) (N : Submodule R V) :
    IsSat ρ L N ↔
      N ≤ L ∧ ∀ N' : Submodule R V, N ≤ N' → N' ≤ L → rk ρ N' = rk ρ N → N' = N := by
  have hB := saturation_basic_properties R V E ρ L hL
  constructor
  · intro hN
    exact ⟨hN.1, fun N' h₁ h₂ h₃ => hB.2.2.1 N N' hN h₁ h₂ h₃⟩
  · rintro ⟨hNL, hmax⟩
    obtain ⟨N', hNN', hN'L, himg⟩ := real_saturation_property R V E ρ L N hL hNL
    have hsat := Formalism.F.saturProps E (zl ρ L) (zl ρ N) hL.2
      (shiftInv_zl_mono ρ hNL)
    have hrk : rk ρ N' = rk ρ N := by
      show Formalism.F.rk (zl ρ N') = Formalism.F.rk (zl ρ N)
      rw [himg]
      exact hsat.2.2
    have heq : N' = N := hmax N' hNN' hN'L hrk
    refine ⟨hNL, ?_⟩
    rw [← heq, himg]
    exact hsat.1

theorem shiftInv_mu {R : Type u} {V : Type v} {E : Type w} {E₂ : Type w₂} [Ring R]
    [AddCommGroup V] [Module R V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    [FiniteDimensional ℝ E₂] (h1 : MuChar.{u, v, w}) (h1' : MuChar.{u, v, w₂})
    (ρ : V →+ E) (ρ₂ : V →+ E₂) (L : Submodule R V) (c : ℝ) (hL : IsLat ρ L)
    (hL₂ : IsLat ρ₂ L)
    (hsh : ∀ N : Submodule R V, N ≤ L → rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N + c * rk ρ N)
    (hL0 : L ≠ ⊥) : muMax ρ₂ L = muMax ρ L + c ∧ muMin ρ₂ L = muMin ρ L + c := by
  obtain ⟨hmax, hmin, -, -, -⟩ := h1 R V E ρ L hL hL0
  obtain ⟨hmax₂, hmin₂, -, -, -⟩ := h1' R V E₂ ρ₂ L hL₂ hL0
  have hrL := (hsh L le_rfl).1
  have hdL := (hsh L le_rfl).2
  constructor
  · apply le_antisymm
    · rw [hmax₂]
      intro N hN
      rw [(hsh N hN).1, (hsh N hN).2]
      have := (hmax (muMax ρ L)).1 le_rfl N hN
      linarith
    · have key : muMax ρ L ≤ muMax ρ₂ L - c := by
        rw [hmax]
        intro N hN
        have := (hmax₂ (muMax ρ₂ L)).1 le_rfl N hN
        rw [(hsh N hN).1, (hsh N hN).2] at this
        linarith
      linarith
  · apply le_antisymm
    · have key : muMin ρ₂ L - c ≤ muMin ρ L := by
        rw [hmin]
        intro N hN
        have := (hmin₂ (muMin ρ₂ L)).1 le_rfl N hN
        rw [hrL, (hsh N hN).1, hdL, (hsh N hN).2] at this
        linarith
      linarith
    · rw [hmin₂]
      intro N hN
      rw [hrL, (hsh N hN).1, hdL, (hsh N hN).2]
      have := (hmin (muMin ρ L)).1 le_rfl N hN
      linarith

theorem shiftInv_count (c : ℝ) (k m : ℕ) :
    (∑ i ∈ Finset.range m, if i < k then c else 0) = c * ((min k m : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : m < k
    · rw [if_pos h, min_eq_right h.le, min_eq_right (show m + 1 ≤ k by omega)]
      push_cast
      ring
    · rw [if_neg h]
      replace h := not_lt.mp h
      rw [min_eq_left h, min_eq_left (show k ≤ m + 1 by omega)]
      ring

private theorem sum_fin_ite_lt_const_eq_mul_min (c : ℝ) (k n : ℕ) :
    (∑ j : Fin n, if (j : ℕ) < k then c else 0) = c * ((min k n : ℕ) : ℝ) :=
  (Fin.sum_univ_eq_sum_range (fun i => if i < k then c else 0) n).trans (shiftInv_count c k n)

theorem shiftInv_sum {n m : ℕ} (h : m = n) (f : Fin n → ℝ) (g : Fin m → ℝ) (c : ℝ) (k : ℕ)
    (hfg : ∀ (j : ℕ) (h1 : j < m) (h2 : j < n), g ⟨j, h1⟩ = f ⟨j, h2⟩ + c) :
    (∑ j : Fin m, if (j : ℕ) < k then g j else 0) =
      (∑ j : Fin n, if (j : ℕ) < k then f j else 0) + c * ((min k n : ℕ) : ℝ) := by
  subst h
  rw [← sum_fin_ite_lt_const_eq_mul_min c k, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact hfg j.1 j.2 j.2
  · simp

private theorem lt_card_filter_le_iff_of_antitone {n : ℕ} {s : Fin n → ℝ} (hs : Antitone s) (j : Fin n) (θ : ℝ) :
    (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ s i)).card ↔ θ ≤ s j := by
  constructor
  · intro h
    by_contra hlt
    replace hlt := not_le.mp hlt
    have h2 : Finset.univ.filter (fun i => θ ≤ s i) ⊆ Finset.Iio j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_Iio]
      by_contra hji
      replace hji := not_lt.mp hji
      have := hs hji
      linarith
    have c2 := Finset.card_le_card h2
    rw [Fin.card_Iio] at c2
    omega
  · intro h
    have h1 : Finset.Iic j ⊆ Finset.univ.filter (fun i => θ ≤ s i) := by
      intro i hi
      simp only [Finset.mem_Iic] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.trans (hs hi)
    have c1 := Finset.card_le_card h1
    rw [Fin.card_Iic] at c1
    omega

theorem shiftInvariance_of (h1 : MuChar.{u, v, w}) (h1' : MuChar.{u, v, w₂})
    (h4 : HNSlopes.{u, v, w}) : ShiftInvariance.{u, v, w, w₂} := by
  intro R V E E₂ _ _ _ _ _ _ _ _ _ ρ ρ₂ L c hL hL₂ hsh
  have hBL := saturation_basic_properties R V E ρ L hL
  have hBL₂ := saturation_basic_properties R V E₂ ρ₂ L hL₂
  have hfilt : ∀ θ : ℝ, hnStep ρ₂ L (θ + c) = hnStep ρ L θ := by
    intro θ
    unfold hnStep
    congr 1
    ext N
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hNL, hN0, hθ⟩
      have hm := (shiftInv_mu h1 h1' ρ ρ₂ N c (hBL.1 N hNL) (hBL₂.1 N hNL)
        (fun N' hN' => hsh N' (hN'.trans hNL)) hN0).2
      exact ⟨hNL, hN0, by linarith⟩
    · rintro ⟨hNL, hN0, hθ⟩
      have hm := (shiftInv_mu h1 h1' ρ ρ₂ N c (hBL.1 N hNL) (hBL₂.1 N hNL)
        (fun N' hN' => hsh N' (hN'.trans hNL)) hN0).2
      exact ⟨hNL, hN0, by linarith⟩
  have hfiltle : ∀ θ : ℝ, hnStep ρ L θ ≤ L := fun θ => sSup_le fun N hN => hN.1
  have hS := h4 R V E ρ L hL
  have hslope : ∀ (j : ℕ) (hj₂ : j < rk ρ₂ L) (hj : j < rk ρ L),
      slopeList ρ₂ L ⟨j, hj₂⟩ = slopeList ρ L ⟨j, hj⟩ + c := by
    intro j hj₂ hj
    have hset : {θ : ℝ | j < rk ρ₂ (hnStep ρ₂ L θ)} = Set.Iic (slopeList ρ L ⟨j, hj⟩ + c) := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_Iic]
      have hf : hnStep ρ₂ L θ = hnStep ρ L (θ - c) := by
        have := hfilt (θ - c)
        rwa [sub_add_cancel] at this
      rw [hf, (hsh _ (hfiltle (θ - c))).1, ← hS.2.1 (θ - c)]
      refine (lt_card_filter_le_iff_of_antitone hS.1 ⟨j, hj⟩ (θ - c)).trans ?_
      constructor <;> intro h <;> linarith
    show sSup {θ : ℝ | j < rk ρ₂ (hnStep ρ₂ L θ)} = slopeList ρ L ⟨j, hj⟩ + c
    rw [hset, csSup_Iic]
  refine ⟨fun N => ?_, fun hL0 => shiftInv_mu h1 h1' ρ ρ₂ L c hL hL₂ hsh hL0,
    hfilt, fun k => ?_⟩
  · rw [shiftInv_isSat_iff ρ₂ hL₂, shiftInv_isSat_iff ρ hL]
    constructor
    · rintro ⟨hNL, hm⟩
      refine ⟨hNL, fun N' hNN' hN'L hr => hm N' hNN' hN'L ?_⟩
      rwa [(hsh N' hN'L).1, (hsh N hNL).1]
    · rintro ⟨hNL, hm⟩
      refine ⟨hNL, fun N' hNN' hN'L hr => hm N' hNN' hN'L ?_⟩
      rwa [(hsh N' hN'L).1, (hsh N hNL).1] at hr
  · exact shiftInv_sum (hsh L le_rfl).1 (slopeList ρ L) (slopeList ρ₂ L) c k hslope

end Formalism.HN
end
end

