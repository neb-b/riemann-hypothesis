module

public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle0001
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityExactSequence
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityInSection

@[expose] public section

-- bundled from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerRuleProductZero
section
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter


open E7 in
theorem euler_char_product_eventually_add (hE1 : EulerAdditivityExactSequence) (hGr : RuleGr) {k : ℕ} (X : HidaSetting k)
    (ts : List (Deg k × X.R)) (F : X.Mod) (d d' : Deg k) (s s' : X.R)
    (hV : Valid X.𝒜 ((d, s) :: (d', s') :: ts)) (hF : F.IsGr X.𝒜)
    (hA : admitted X.𝒜 ((d + d', s * s') :: ts) F.Ann) :
    ∀ᶠ m in atTop, chi ((d + d', s * s') :: ts) F m =
      chi ((d, s) :: ts) F m + chi ((d', s') :: ts) (F.shift d) m := by
  have hs : 0 ≤ d ∧ s ∈ X.𝒜 d := hV (d, s) List.mem_cons_self
  have hs' : 0 ≤ d' ∧ s' ∈ X.𝒜 d' := hV (d', s') (List.mem_cons_of_mem _ List.mem_cons_self)
  have hVt : Valid X.𝒜 ts :=
    fun p hp => hV p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
  have hss : s * s' ∈ X.𝒜 (d + d') := SetLike.mul_mem_graded hs.2 hs'.2
  have hFd := (hGr k X F hF).2.1 d
  have hP14 := (hGr k X _ hFd).2.2 d' s' hs'.2
  have hP25 := (hGr k X F hF).2.2 (d + d') (s * s') hss
  have hP36 := (hGr k X F hF).2.2 d s hs.2
  have g2 := product_kernel_to_kernel_isGraded X.𝒜 F s s' d d' hF hs'.2
  have g3 := kernel_to_shift_quotient_isGraded F s s' d
  have g4 := quotient_to_product_quotient_isGraded X.𝒜 F s s' d hF hs.2
  have hI2 := ((hGr k X _ hP36.2).1 _ (g2.range_hom hP25.2.internal)).1
  have hI3 := ((hGr k X _ hP14.1).1 _ (g3.range_hom hP36.2.internal)).1
  have hI4 := ((hGr k X _ hP25.1).1 _ (g4.range_hom hP14.1.internal)).1
  have a2 : admitted X.𝒜 ts (F.ann (s * s') (d + d')).Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_sub F _) (mul_mem_annihilator_product_kernel F s s' d d')
  have a3 : admitted X.𝒜 ts (F.ann s d).Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_sub F _) (mul_mem_annihilator_kernel F s s' d)
  have a4 : admitted X.𝒜 ts ((F.shift d).quot s').Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_quo (F.shift d) _) (mul_mem_annihilator_shift_quotient F s s' d)
  have a5 : admitted X.𝒜 ts (F.quot (s * s')).Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_quo F _) (mul_mem_annihilator_product_quotient F s s')
  have e2 := hE1 k X ts _ _ _ hVt hP14.2 hP25.2 hI2
    (sesOfExact (phi1 F s s' d d') (phi2 F s s' d d') (kernel_inclusion_product_injective F s s' d d')
      (kernel_inclusion_product_exact F s s' d d') (kernel_inclusion_grading_comap F s s' d d') g2 hP25.2.internal hP36.2.internal) a2
  have e3 := hE1 k X ts _ _ _ hVt hI2 hP36.2 hI3
    (sesOfKer _ (phi3 F s s' d) (ker3 F s s' d d') g3 hP36.2.internal hP14.1.internal) a3
  have e4 := hE1 k X ts _ _ _ hVt hI3 hP14.1 hI4
    (sesOfKer _ (phi4 F s s' d) (ker4 F s s' d) g4 hP14.1.internal hP25.1.internal) a4
  have e5 := hE1 k X ts _ _ _ hVt hI4 hP25.1 hP36.1 (ses5 F s s' d) a5
  filter_upwards [e2, e3, e4, e5] with m h2 h3 h4 h5
  show chi ts (F.quot (s * s')) m - chi ts (F.ann (s * s') (d + d')) m =
    (chi ts (F.quot s) m - chi ts (F.ann s d) m) +
      (chi ts ((F.shift d).quot s') m - chi ts ((F.shift d).ann s' d') m)
  linarith

theorem euler_rule_product_zero : EulerAdditivityDegreeZero := by
  intro k X ts F d s s' hV hF hA
  have hA' : admitted X.𝒜 ((0 + d, s * s') :: ts) F.Ann := by rwa [zero_add]
  have h := euler_char_product_eventually_add (euler_additivity_of_rules ruleGr ruleFin ruleIso) ruleGr X ts F 0 d s s' hV hF hA'
  rw [zero_add] at h
  filter_upwards [h] with m hm
  rw [hm, chi_shift, sub_zero]

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

-- bundled from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleCong
section
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

namespace Cong

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem lsmul_eq (F : GMod B R k) {s s' : R} (h : s - s' ∈ F.Ann) :
    LinearMap.lsmul R F.M s = LinearMap.lsmul R F.M s' := by
  ext x
  have hx : (s - s') • x = 0 := Module.mem_annihilator.1 h x
  rw [sub_smul, sub_eq_zero] at hx
  exact hx

theorem quot_eq (F : GMod B R k) {s s' : R} (h : s - s' ∈ F.Ann) : F.quot s = F.quot s' := by
  unfold GMod.quot
  rw [lsmul_eq F h]

theorem ann_eq (F : GMod B R k) {s s' : R} (d : Deg k) (h : s - s' ∈ F.Ann) :
    F.ann s d = F.ann s' d := by
  unfold GMod.ann
  rw [lsmul_eq F h]

theorem ann_le_quot (F : GMod B R k) (s : R) : F.Ann ≤ (F.quot s).Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at *
  intro y
  obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ_surjective y
  exact (map_smul (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ a x).symm.trans
    ((congrArg _ (ha x)).trans (map_zero _))

theorem ann_le_ann (F : GMod B R k) (s : R) (d : Deg k) : F.Ann ≤ (F.ann s d).Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at *
  intro x
  exact Subtype.ext (ha x.1)

theorem chi_cong {ts ts' : List (Deg k × R)} : ∀ (F : GMod B R k),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2 - q.2 ∈ F.Ann) ts ts' →
      ∀ m, chi ts F m = chi ts' F m := by
  induction ts generalizing ts' with
  | nil =>
    intro F h m
    cases h
    rfl
  | cons p ts ih =>
    intro F h m
    cases h with
    | @cons _ q _ ts'' hpq hrest =>
      obtain ⟨d, s⟩ := p
      obtain ⟨d', s'⟩ := q
      obtain ⟨hd, hs⟩ := hpq
      have hd' : d = d' := hd
      subst hd'
      have hs' : s - s' ∈ F.Ann := hs
      show chi ts (F.quot s) m - chi ts (F.ann s d) m =
        chi ts'' (F.quot s') m - chi ts'' (F.ann s' d) m
      rw [← quot_eq F hs', ← ann_eq F d hs',
        ih (F.quot s) (hrest.imp fun _ _ h => ⟨h.1, ann_le_quot F s h.2⟩) m,
        ih (F.ann s d) (hrest.imp fun _ _ h => ⟨h.1, ann_le_ann F s d h.2⟩) m]

end Cong

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

-- bundled from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIrr
section
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

theorem ruleIrr : RuleIrr := by
  rintro k X F hF ⟨N, hN⟩
  filter_upwards [hF.eventually_gr_le X.std X.iSup_eq_top N] with m hm
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  refine Submodule.smul_induction_on (hm y hy) ?_ ?_
  · intro a ha z _
    exact Module.mem_annihilator.1 (hN ha) z
  · intro x y hx hy
    rw [hx, hy, add_zero]

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

-- bundled from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.SumPowersetFinSucc
section
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open Finset

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem sum_powerset_fin_succ {n : ℕ} (f : Finset (Fin (n + 1)) → ℤ) :
    ∑ I ∈ (univ : Finset (Fin (n + 1))).powerset, f I =
      ∑ J ∈ (univ : Finset (Fin n)).powerset, f (J.image Fin.succ) +
        ∑ J ∈ (univ : Finset (Fin n)).powerset, f (insert 0 (J.image Fin.succ)) := by
  have hu : (univ : Finset (Fin (n + 1))) = insert 0 ((univ : Finset (Fin n)).image Fin.succ) := by
    ext i
    simp only [mem_univ, mem_insert, mem_image, true_and, true_iff]
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, h.symm⟩
  have h0 : (0 : Fin (n + 1)) ∉ (univ : Finset (Fin n)).image Fin.succ := by
    simp only [mem_image, mem_univ, true_and, not_exists]
    exact fun j => Fin.succ_ne_zero j
  have hinj : Function.Injective (fun J : Finset (Fin n) => J.image Fin.succ) :=
    Finset.image_injective (Fin.succ_injective n)
  rw [hu, Finset.sum_powerset_insert h0, Finset.powerset_image,
    Finset.sum_image (fun a _ b _ hab => hinj hab), Finset.sum_image (fun a _ b _ hab => hinj hab)]

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

