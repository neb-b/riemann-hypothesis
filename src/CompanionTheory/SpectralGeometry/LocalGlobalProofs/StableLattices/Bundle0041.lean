module

public import Mathlib
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.VNormSqRenum
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgFarRen

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight qdet qminor Tm sgn)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (LocFin)
open PI.UpqRep (vNormSq rhoC nsq)

variable {n : ℕ}

theorem glRel_renum {A : Type*} [Ring A] {E : Fin n → Fin n → A} (hE : GlRel E) (s : Equiv.Perm (Fin n)) :
    GlRel (fun a b => E (s a) (s b)) := by
  intro a b c d
  have h := hE (s a) (s b) (s c) (s d)
  simpa only [Equiv.apply_eq_iff_eq] using h

theorem tm_renum {A : Type*} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) (s : Equiv.Perm (Fin n)) (u : ℂ)
    (a b : Fin n) : Tm (fun a b => E (s a) (s b)) u a b = Tm E u (s a) (s b) := by
  simp only [Formalism.REAL.Tm, Equiv.apply_eq_iff_eq]

theorem qminor_renum {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin n → Fin n → A) (s : Equiv.Perm (Fin n))
    (a b : Fin t → Fin n) (u : ℂ) :
    qminor (fun a b => E (s a) (s b)) a b u = qminor E (s ∘ a) (s ∘ b) u := by
  unfold Formalism.REAL.qminor
  simp only [tm_renum, Function.comp_apply]

theorem qdet_renum {A : Type} [Ring A] [Algebra ℂ A] {E : Fin n → Fin n → A} (hE : GlRel E)
    (s : Equiv.Perm (Fin n)) (u : ℂ) : qdet (fun a b => E (s a) (s b)) u = qdet E u := by
  have h1 : qdet (fun a b => E (s a) (s b)) u = qminor E (id ∘ ⇑s) (id ∘ ⇑s) u := by
    unfold Formalism.REAL.qdet
    rw [qminor_renum]
    rfl
  have hsq : ((Equiv.Perm.sign s : ℤ) : A) * ((Equiv.Perm.sign s : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [h1, Formalism.REAL.quantumMinorRowSkew_holds, Formalism.REAL.quantumMinorColSkew_holds A n n E hE, ← mul_assoc, hsq, one_mul]
  rfl

theorem symm_lt {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    s.symm a < s.symm b := by
  rcases lt_trichotomy (s.symm a) (s.symm b) with h | h | h
  · exact h
  · exact absurd (s.symm.injective h) (ne_of_lt hab)
  · have h' := hs (s.symm b) (s.symm a) h (by simp [he])
    simp only [Equiv.apply_symm_apply] at h'
    exact absurd h' (lt_asymm hab)

theorem kHighest_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    (E : Fin n → Fin n → Module.End ℂ V) {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (γ : Fin n → ℝ) (u : V) :
    KHighest ε E γ u ↔ KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (γ ∘ s) u := by
  unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
  constructor
  · rintro ⟨hw, hz⟩
    exact ⟨fun a => hw (s a), fun a b hab he => hz (s a) (s b) (hs a b hab he) he⟩
  · rintro ⟨hw, hz⟩
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · simpa using hw (s.symm a)
    · have h := hz (s.symm a) (s.symm b) (symm_lt hs hab he) (by simpa using he)
      simpa using h

theorem rhoC_renum {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) : rhoC (ε ∘ s) = rhoC ε ∘ s := by
  funext a
  have h1 : (Finset.univ.filter (fun b => a < b ∧ ε (s b) = ε (s a))).card =
      (Finset.univ.filter (fun b => s a < b ∧ ε b = ε (s a))).card := by
    refine Finset.card_nbij' s s.symm ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hb ⊢
      exact ⟨hs a b hb.1 hb.2.symm, hb.2⟩
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, Equiv.apply_symm_apply] at hc ⊢
      refine ⟨?_, hc.2⟩
      have h' := symm_lt hs hc.1 hc.2.symm
      simpa using h'
    · intro b _
      simp
    · intro c _
      simp
  have h2 : (Finset.univ.filter (fun b => b < a ∧ ε (s b) = ε (s a))).card =
      (Finset.univ.filter (fun b => b < s a ∧ ε b = ε (s a))).card := by
    refine Finset.card_nbij' s s.symm ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hb ⊢
      exact ⟨hs b a hb.1 hb.2, hb.2⟩
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, Equiv.apply_symm_apply] at hc ⊢
      refine ⟨?_, hc.2⟩
      have h' := symm_lt hs hc.1 hc.2
      simpa using h'
    · intro b _
      simp
    · intro c _
      simp
  simp only [PI.UpqRep.rhoC, Function.comp_apply, h1, h2]

theorem vNormSq_renum {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (γ : Fin n → ℝ) :
    vNormSq (ε ∘ s) (γ ∘ s) = vNormSq ε γ := by
  unfold PI.UpqRep.vNormSq PI.UpqRep.nsq PI.UpqRep.dot
  rw [rhoC_renum hs]
  exact Fintype.sum_equiv s _ _ (fun a => by simp)

theorem isMinG_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    (E : Fin n → Fin n → Module.End ℂ V) {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (γ : Fin n → ℝ) :
    IsMinG ε E γ ↔ IsMinG (ε ∘ s) (fun a b => E (s a) (s b)) (γ ∘ s) := by
  unfold CompanionTheory.RgExh.U.IsMinG
  constructor
  · intro h μ x hx hk
    have hμ : μ = (μ ∘ s.symm) ∘ s := by
      funext a
      simp
    rw [hμ] at hk ⊢
    rw [vNormSq_renum hs, vNormSq_renum hs]
    exact h _ x hx ((kHighest_iff E hs _ x).mpr hk)
  · intro h μ x hx hk
    have h' := h (μ ∘ s) x hx ((kHighest_iff E hs μ x).mp hk)
    rwa [vNormSq_renum hs, vNormSq_renum hs] at h'

theorem renumber : CompanionTheory.RgExh.U.Renumber := by
  intro n ε V _ _ E hE s hs
  refine ⟨glRel_renum hE s, fun hU a b x y => hU (s a) (s b) x y, ?_, ?_,
    fun γ u => kHighest_iff E hs γ u, fun γ => isMinG_iff E hs γ, rhoC_renum hs⟩
  · intro hL x
    obtain ⟨S, hS, hK, hx⟩ := hL x
    exact ⟨S, hS, fun a b hab v hv => hK (s a) (s b) hab v hv, hx⟩
  · intro χ hχ Y
    exact (qdet_renum hE s _).trans (hχ Y)

end GlobalTheory.CompanionTheory.RgFarRen
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.VanKGOf
section
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhVanKG

open CompanionTheory.D.LK
open CompanionTheory.D.LK.Car
open CompanionTheory.RgExh.U
open Formalism.REAL (GlRel KHighest IsWeight CasK)
open PI.UpqRep (rhoC nsq)
open CompanionTheory.D.DSIC (KRel KUnit KStab)

theorem vanKG_of (hN : NumKG) : VanKG := by
  have hC : COK := cok_of hGenCO
  have hP : WtProj := GlobalTheory.CompanionTheory.LKWtProj.wtProj
  have hM : WtMajor := GlobalTheory.CompanionTheory.KWeightMajor.wtMajor_of CompanionTheory.D.DSIC.hLowSpan
  intro n ε γ lev V _ _ E hg hE hU hF hmin B j z hB hBU hz hwt hb
  set τ := xv ε γ with hτ
  have hzw : ∀ A, IsWeight E (τ - wt A) (z A) := fun A c => by
    have := congrFun (hwt c) A
    rw [Ft_apply, filter_all, Pi.smul_apply] at this
    rw [eq_sub_of_add_eq this, Pi.sub_apply, Complex.ofReal_sub, sub_smul]
  obtain ⟨w, hw, e⟩ := hC n ε V E hE B j (τ - wt B) z hz (fun c => funext fun A => by
    by_cases h : z A = 0
    · simp [Ft_apply, h]
    · rw [Ft_apply, hzw A c, Pi.smul_apply, ← add_smul, Pi.sub_apply, Pi.sub_apply, wt_split (ε := ε) A, (hz A h).1]
      congr 1; push_cast; ring) hb
  choose S hS hSt hmem using hF
  let W : Submodule ℂ V := ⨆ A, S (z A)
  haveI : ∀ A, FiniteDimensional ℂ (S (z A)) := fun A => hS _
  have hWs : KStab ε E W := fun a b h v hv =>
    (iSup_le fun A y hy => Submodule.mem_iSup_of_mem A (hSt _ a b h y hy) : W ≤ W.comap (E a b)) hv
  obtain ⟨q, hq⟩ := exists_poly (CasK ε E) (fun x y => by
      simp only [CasK, LinearMap.sum_apply, sum_inner, inner_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h
      · rw [Module.End.mul_apply, Module.End.mul_apply, hU a b h, hU b a h.symm]
      · simp) W (fun x hx => by
      simp only [CasK, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      split_ifs with h
      · exact hWs a b h _ (hWs b a h.symm _ hx)
      · simp) (nsq (τ - wt B - rhoC ε) - nsq (rhoC ε))
  have hcq : ∀ c d, ε c = ε d → ∀ x, Polynomial.aeval (CasK ε E) q (E c d x) = E c d (Polynomial.aeval (CasK ε E) q x) :=
    fun c d h x => by
      have : Commute (E c d) (Polynomial.aeval (CasK ε E) q) := by
        rw [Polynomial.aeval_eq_sum_range]
        exact Commute.sum_right _ _ _ fun k _ => ((casK_comm hE h).pow_right k).smul_right _
      exact (LinearMap.congr_fun this.eq x).symm
  have h0 : z + lift n (Polynomial.aeval (CasK ε E) q) (bd ε E w) = 0 := by
    funext A
    by_contra hne
    rw [← e] at hne
    have hA : z A ≠ 0 := fun h => hne (by simp [h])
    obtain ⟨ν, y, hy0, hy, hs, hd, hc⟩ := hM n ε V E hE hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (τ - wt A) _ _ hne
      (fun c => by
        simp only [Pi.add_apply, lift_apply, Pi.sub_apply, Pi.smul_apply]
        rw [map_add (f := _), ← hcq c c rfl, map_sub, map_smul, ← Module.End.mul_apply, (casK_comm hE rfl).eq,
          Module.End.mul_apply, hzw A c]
        simp only [map_smul, map_sub, smul_add, smul_sub, Pi.sub_apply, smul_comm ((τ c - wt A c : ℝ) : ℂ)])
      (hq (z A) (Submodule.mem_iSup_of_mem A (hmem _)) _ rfl)
    have hA1 := (hz A hA).1
    refine absurd (hmin ν y hy0 hy) (not_le.2 (hN n ε γ lev ν B (A.filter (cpt ε)) hg hB
      (fun i hi => ⟨(mem_filter.1 (hA1.symm ▸ hi :)).2, hBU i hi⟩) (fun i hi => (mem_filter.1 hi).2) hd (fun w hw' => ?_) ?_))
    · convert hc w hw' using 2
      funext c
      simp only [Pi.sub_apply, wt_split (ε := ε) A, hA1, hτ]
      ring
    · have h1 : nsq (τ - wt B - rhoC ε) = nsq (ν + rhoC ε) := by
        have := Complex.ofReal_injective hs
        linarith
      rw [← h1]
      congr 1
      abel
  have h1 : bd ε E (-lift n (Polynomial.aeval (CasK ε E) q) w) = z := by
    rw [map_neg, ← lift_bd _ E E fun i hi x => hcq _ _ hi x]
    exact (eq_neg_of_add_eq_zero_left h0).symm
  obtain ⟨t, ht1, ht2, ht3⟩ := hP n (allT n) ε V E hE hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (bd ε E)
    (differential_commutes_weight_operator n _ ε V E (fun _ _ _ => rfl) hE) τ _ (h1.symm ▸ hwt)
  exact ⟨t, sup_of_supp hw fun A h => ht3 A (by simp [h]), ht1, ht2.trans h1⟩

end GlobalTheory.CompanionTheory.RgExhVanKG
end
end

