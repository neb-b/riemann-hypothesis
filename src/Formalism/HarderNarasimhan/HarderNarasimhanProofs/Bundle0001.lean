module

public import Formalism.HarderNarasimhan.DegSupermodZ
public import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
public import Formalism.LatticeSlopes.LatticeSlopesProofs.Bundle0001

@[expose] public section

-- bundled from Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
section
open Module Submodule

noncomputable section

namespace Formalism.HN

theorem exists_smul_mem_of_finrank_eq {E : Type*} [AddCommGroup E] (S N : Submodule ℤ E) [Module.Finite ℤ S]
    (hNS : N ≤ S) (hrk : finrank ℤ S = finrank ℤ N) :
    ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ a • x ∈ N := by
  intro x hx
  set P : Submodule ℤ S := N.comap S.subtype with hP
  have hPr : finrank ℤ P = finrank ℤ N :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hNS)
  have h := P.finrank_quotient_add_finrank
  have h0 : finrank ℤ (S ⧸ P) = 0 := by omega
  obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff.1 h0) (Submodule.Quotient.mk ⟨x, hx⟩)
  refine ⟨a, ha, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  exact hax

theorem satR_mem_zl {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E) (N : Submodule R V) (y : E) :
    y ∈ zl ρ N ↔ ∃ x ∈ N, ρ x = y := Iff.rfl

theorem real_saturation_property : SatR := by
  intro R V E _ _ _ _ _ _ ρ L N hL hNL
  obtain ⟨hinj, hdisc⟩ := hL
  have : DiscreteTopology (zl ρ L) := hdisc
  have hNL' : zl ρ N ≤ zl ρ L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (satR_mem_zl ρ N y).1 hy
    exact (satR_mem_zl ρ L _).2 ⟨x, hNL hx, rfl⟩
  obtain ⟨-, hNS, hrk⟩ := Formalism.F.saturProps E (zl ρ L) (zl ρ N) hdisc hNL'
  set S := Formalism.F.satur (zl ρ L) (zl ρ N) with hSdef
  have : DiscreteTopology S :=
    Formalism.F.discreteTopology_of_le (L := zl ρ L) inf_le_left
  have htor := exists_smul_mem_of_finrank_eq S (zl ρ N) hNS hrk
  have hspan : ∀ y : E, y ∈ S ↔ y ∈ zl ρ L ∧ y ∈ span ℝ ((zl ρ N : Submodule ℤ E) : Set E) :=
    fun y => Submodule.mem_inf
  refine ⟨{ carrier := {x | x ∈ L ∧ ρ x ∈ S}
            add_mem' := ?_
            zero_mem' := ?_
            smul_mem' := ?_ }, ?_, ?_, ?_⟩
  · rintro x y ⟨hxL, hxS⟩ ⟨hyL, hyS⟩
    refine ⟨L.add_mem hxL hyL, ?_⟩
    rw [map_add (f := _)]
    exact S.add_mem hxS hyS
  · refine ⟨L.zero_mem, ?_⟩
    rw [map_zero]
    exact S.zero_mem
  · rintro c x ⟨hxL, hxS⟩
    have hcxL : c • x ∈ L := L.smul_mem c hxL
    refine ⟨hcxL, (hspan _).2 ⟨(satR_mem_zl ρ L _).2 ⟨c • x, hcxL, rfl⟩, ?_⟩⟩
    obtain ⟨a, ha, hax⟩ := htor (ρ x) hxS
    obtain ⟨n, hnN, hn⟩ := (satR_mem_zl ρ N _).1 hax
    have haxL : a • x ∈ L := L.toAddSubgroup.zsmul_mem hxL a
    have hn' : n = a • x := by
      apply hinj (hNL hnN) haxL
      rw [hn, map_zsmul]
    have haxN : a • x ∈ N := hn' ▸ hnN
    have h1 : a • (c • x) ∈ N := by
      rw [smul_comm]
      exact N.smul_mem c haxN
    have h2 : a • ρ (c • x) ∈ zl ρ N := by
      rw [← map_zsmul]
      exact (satR_mem_zl ρ N _).2 ⟨_, h1, rfl⟩
    have h3 : (a : ℝ) • ρ (c • x) ∈ span ℝ ((zl ρ N : Submodule ℤ E) : Set E) := by
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.subset_span h2
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have h4 := (span ℝ ((zl ρ N : Submodule ℤ E) : Set E)).smul_mem (a : ℝ)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ ha', one_smul] at h4
  · intro x hx
    exact ⟨hNL hx, hNS ((satR_mem_zl ρ N _).2 ⟨x, hx, rfl⟩)⟩
  · intro x hx
    exact hx.1
  · ext y
    rw [satR_mem_zl]
    constructor
    · rintro ⟨x, ⟨-, hxS⟩, rfl⟩
      exact hxS
    · intro hy
      obtain ⟨x, hxL, rfl⟩ := (satR_mem_zl ρ L _).1 ((hspan y).1 hy).1
      exact ⟨x, ⟨hxL, hy⟩, rfl⟩

end Formalism.HN
end
end

-- bundled from Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNStep
section
open Module Submodule

noncomputable section

namespace Formalism.HN

theorem imageLattice_mono {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) {A B : Submodule R V}
    (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hx
  exact AddSubgroup.mem_map.mpr ⟨y, h hy, rfl⟩

universe u v w in
theorem hnStep_of (h1 : DegSupermod.{u, v, w}) (h2 : MuChar.{u, v, w}) (h3 : RatioMax.{u, v, w})
    (h4 : FinSup.{u, v, w}) (h5 : SatR.{u, v, w}) (h6 : SatBasic.{u, v, w}) :
    HNStep.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L hL θ
  obtain ⟨hsub, hmono, hsat_eq, -, -, hbot, -, -⟩ := h6 R V E ρ L hL
  obtain ⟨g, hg⟩ : ∃ g : Submodule R V → ℝ, ∀ N, g N = deg ρ N - θ * (rk ρ N : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have sm : ∀ A B : Submodule R V, A ≤ L → B ≤ L → g A + g B ≤ g (A ⊔ B) + g (A ⊓ B) := by
    intro A B hA hB
    obtain ⟨hr, hd⟩ := h1 R V E ρ L A B hL hA hB
    have hr' : (rk ρ (A ⊔ B) : ℝ) + rk ρ (A ⊓ B) = rk ρ A + rk ρ B := by
      exact_mod_cast hr
    have hθ : θ * (rk ρ (A ⊔ B) : ℝ) + θ * rk ρ (A ⊓ B) = θ * rk ρ A + θ * rk ρ B := by
      rw [← mul_add, ← mul_add, hr']
    simp only [hg]
    linarith
  have charP : ∀ M : Submodule R V, M ≤ L → M ≠ ⊥ →
      (θ ≤ muMin ρ M ↔ ∀ N ≤ M, g N ≤ g M) := by
    intro M hM hM0
    rw [(h2 R V E ρ M (hsub M hM) hM0).2.1 θ]
    refine forall_congr' fun N => imp_congr_right fun _ => ?_
    simp only [hg, mul_sub]
    constructor <;> intro h <;> linarith
  have supP : ∀ A B : Submodule R V, A ≤ L → B ≤ L → (∀ N ≤ A, g N ≤ g A) →
      (∀ N ≤ B, g N ≤ g B) → ∀ N ≤ A ⊔ B, g N ≤ g (A ⊔ B) := by
    intro A B hA hB pA pB N hN
    have hNL : N ≤ L := hN.trans (sup_le hA hB)
    have e1 := sm N A hNL hA
    have e2 := pA (N ⊓ A) inf_le_right
    have e3 := sm (N ⊔ A) B (sup_le hNL hA) hB
    have e4 := pB ((N ⊔ A) ⊓ B) inf_le_right
    have e5 : N ⊔ A ⊔ B = A ⊔ B := by
      rw [sup_assoc]; exact sup_eq_right.mpr hN
    rw [e5] at e3
    linarith
  obtain ⟨t, htS, htF⟩ := h4 R V E ρ L {N | N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N} hL
    (fun N hN => hN.1)
  have hFdef : hnStep ρ L θ = t.sup id := htF
  have memS : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → θ ≤ muMin ρ N →
      N ≤ hnStep ρ L θ := fun N a b c =>
    le_sSup (s := {N | N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N})
      (show N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N from ⟨a, b, c⟩)
  have PF : t.sup id ≤ L ∧ ∀ N ≤ t.sup id, g N ≤ g (t.sup id) := by
    refine Finset.sup_induction (p := fun M => M ≤ L ∧ ∀ N ≤ M, g N ≤ g M) ?_ ?_ ?_
    · refine ⟨bot_le, fun N hN => ?_⟩
      rw [le_bot_iff.mp hN]
    · rintro A ⟨hA, pA⟩ B ⟨hB, pB⟩
      exact ⟨sup_le hA hB, supP A B hA hB pA pB⟩
    · intro M hM
      have hM' : M ≤ L ∧ M ≠ ⊥ ∧ θ ≤ muMin ρ M := htS (Finset.mem_coe.mpr hM)
      exact ⟨hM'.1, (charP M hM'.1 hM'.2.1).mp hM'.2.2⟩
  rw [← hFdef] at PF
  obtain ⟨FL, PF⟩ := PF
  clear hFdef htF htS
  set F := hnStep ρ L θ with hFset
  clear_value F
  have rkpos_of : IsSat ρ L F → ∀ X : Submodule R V, F < X → X ≤ L →
      rk ρ F < rk ρ X := by
    intro hs X hX hXL
    rcases (hmono F X hX.le hXL).1.lt_or_eq with h | h
    · exact h
    · exact absurd (hsat_eq F X hs hX.le hXL h.symm) hX.ne'
  have Fsat : IsSat ρ L F := by
    obtain ⟨F', hFF', hF'L, himg⟩ := h5 R V E ρ L F hL FL
    obtain ⟨hsatimg, -, hrkimg⟩ := Formalism.F.saturProps E (zl ρ L)
      (zl ρ F) hL.2 (imageLattice_mono ρ FL)
    have hF'sat : IsSat ρ L F' := by
      unfold IsSat
      rw [himg]
      exact ⟨hF'L, hsatimg⟩
    have hrk : rk ρ F' = rk ρ F := by
      show Formalism.F.rk (zl ρ F') = Formalism.F.rk (zl ρ F)
      rw [himg]
      exact hrkimg
    by_cases hF'0 : F' = ⊥
    · have hF0 : F = ⊥ := by
        rw [eq_bot_iff, ← hF'0]
        exact hFF'
      rw [hF0]
      exact hbot
    · have PF' : ∀ N ≤ F', g N ≤ g F' := by
        intro M hM
        have hML : M ≤ L := hM.trans hF'L
        have e1 := sm M F hML FL
        have e2 := PF (M ⊓ F) inf_le_right
        have hX : M ⊔ F ≤ F' := sup_le hM hFF'
        have r1 := (hmono F (M ⊔ F) le_sup_right (hX.trans hF'L)).1
        have r2 := (hmono (M ⊔ F) F' hX hF'L).1
        have hreq : rk ρ (M ⊔ F) = rk ρ F' := by omega
        have d := (hmono (M ⊔ F) F' hX hF'L).2 hreq
        have e3 : g (M ⊔ F) ≤ g F' := by
          simp only [hg, hreq]
          linarith
        linarith
      have hmem := memS F' hF'L hF'0 ((charP F' hF'L hF'0).mpr PF')
      rw [le_antisymm hmem hFF'] at hF'sat
      exact hF'sat
  refine ⟨Fsat, fun hF0 => (charP F FL hF0).mpr PF, memS, ?_⟩
  intro N hFN hNL
  refine not_le.mp fun hcon => ?_
  have rkpos := rkpos_of Fsat
  have hFL : F ≠ L := (lt_of_lt_of_le hFN hNL).ne
  obtain ⟨N₀, hFN₀, hN₀sat, hmax⟩ := h3 R V E ρ L F hL Fsat hFL
  have hN₀L : N₀ ≤ L := by
    unfold IsSat at hN₀sat
    exact hN₀sat.1
  have hr₀ : (rk ρ F : ℝ) < rk ρ N₀ := by exact_mod_cast rkpos N₀ hFN₀ hN₀L
  have hr : (rk ρ F : ℝ) < rk ρ N := by exact_mod_cast rkpos N hFN hNL
  have key := hmax N hFN hNL
  have hμ : θ * ((rk ρ N₀ : ℝ) - rk ρ F) ≤ deg ρ N₀ - deg ρ F := by
    refine not_lt.mp fun hlt => ?_
    have a1 := mul_lt_mul_of_pos_right hlt (sub_pos.mpr hr)
    have a2 := mul_le_mul_of_nonneg_right hcon (sub_pos.mpr hr₀).le
    nlinarith
  have PN₀ : ∀ M ≤ N₀, g M ≤ g N₀ := by
    intro M hM
    have hML : M ≤ L := hM.trans hN₀L
    have e1 := sm M F hML FL
    have e2 := PF (M ⊓ F) inf_le_right
    have hX : M ⊔ F ≤ N₀ := sup_le hM hFN₀.le
    have hXN₀ : g (M ⊔ F) ≤ g N₀ := by
      rcases (le_sup_right : F ≤ M ⊔ F).lt_or_eq with hlt | heq
      · have hrX₀ : (rk ρ (M ⊔ F) : ℝ) ≤ rk ρ N₀ := by
          exact_mod_cast (hmono _ _ hX hN₀L).1
        have k2 := hmax (M ⊔ F) hlt (hX.trans hN₀L)
        have hpos : 0 < (rk ρ N₀ : ℝ) - rk ρ F := sub_pos.mpr hr₀
        have hm : ((rk ρ N₀ : ℝ) - rk ρ F) * g (M ⊔ F) ≤
            ((rk ρ N₀ : ℝ) - rk ρ F) * g N₀ := by
          simp only [hg]
          nlinarith [mul_nonneg (sub_nonneg.mpr hμ) (sub_nonneg.mpr hrX₀)]
        exact le_of_mul_le_mul_left hm hpos
      · rw [← heq]
        simp only [hg]
        linarith [mul_sub θ (rk ρ N₀ : ℝ) (rk ρ F)]
    linarith
  have hN₀0 : N₀ ≠ ⊥ := ne_bot_of_gt hFN₀
  have hle := memS N₀ hN₀L hN₀0 ((charP N₀ hN₀L hN₀0).mpr PN₀)
  exact absurd (le_antisymm hle hFN₀.le) hFN₀.ne'

end Formalism.HN
end
end

