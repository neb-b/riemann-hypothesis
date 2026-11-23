module

public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleMono
section
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter


open E4 in
theorem ruleMono : RuleMono := by
  intro k X ts F' F F'' hv hF' hF hF'' S hA
  have hle : F.Ann ≤ F'.Ann := by
    intro a ha
    refine Module.mem_annihilator.mpr fun x => S.inj ?_
    rw [map_smul, map_zero]
    exact Module.mem_annihilator.mp ha _
  have h1 := Pos.e1 k X ts F' F F'' hv hF' hF hF'' S hA
  have h2 := rulePos k X ts F' hv hF' (admissible_mono_ideal X.𝒜 hle hA)
  filter_upwards [h1, h2] with m a b
  rw [a]
  linarith

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

-- bundled from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleUB
section
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

theorem UB.ann_sup_le_ann {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (F : GMod B R k) (s : R) (d : Deg k) : F.Ann ⊔ Ideal.span {s} ≤ (F.ann s d).Ann := by
  refine sup_le ?_ ?_
  · intro a ha
    refine Module.mem_annihilator.mpr fun x => ?_
    have hx : ∀ x : LinearMap.ker (LinearMap.lsmul R F.M s), a • x = 0 :=
      fun x => Subtype.ext (Module.mem_annihilator.mp ha x.1)
    exact hx x
  · rw [Ideal.span_singleton_le_iff_mem]
    refine Module.mem_annihilator.mpr fun x => ?_
    have hx : ∀ x : LinearMap.ker (LinearMap.lsmul R F.M s), s • x = 0 :=
      fun x => Subtype.ext x.2
    exact hx x


open E4 in
theorem ruleUB : RuleUB := by
  intro k X ts us
  induction ts with
  | nil =>
    intro F _ _ _
    exact Eventually.of_forall fun m => le_rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F hv hF hA
    have hv' : Valid X.𝒜 (ts ++ us) := fun p hp => hv p (List.mem_cons_of_mem _ hp)
    have hs : s ∈ X.𝒜 d := (hv (d, s) List.mem_cons_self).2
    have hA' : admitted X.𝒜 (ts ++ us) (F.Ann ⊔ Ideal.span {s}) := admissible_tail_of_cons_mem X.𝒜 hA
    obtain ⟨g1, g2⟩ := (ruleGr k X F hF).2.2 d s hs
    have h1 := ih (F.quot s) hv' g1 (admissible_mono_ideal X.𝒜 (ann_sup_le_quot F s) hA')
    have h2 := rulePos k X (ts ++ us) (F.ann s d) hv' g2 (admissible_mono_ideal X.𝒜 (UB.ann_sup_le_ann F s d) hA')
    filter_upwards [h1, h2] with m a b
    show chi (ts ++ us) (F.quot s) m - chi (ts ++ us) (F.ann s d) m ≤ chi us ((F.quot s).quots ts) m
    linarith

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

