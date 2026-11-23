module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.SiegelWeilStdLt

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.FieldOf
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem eisValue_of (hBL : EisBL) (hSec : SecK) (d : SD σ) {r' s' : ℕ}
    (hY : d.Y.IsHerm σ d.B r' s' ∨ d.Y.IsSkew σ d.B r' s') (c : ℂ) (hM : MainC c d) (Φ : d.Fn) (hK : d.KFin Φ) :
    EisValueAt (flat d.a (d.sec0 Φ) (s0 d.m d.n)) (s0 d.m d.n) (fun x => c * d.I Φ x) := by
  obtain ⟨Ê, ⟨t, hsum, -⟩, hw⟩ := hBL F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.χ d.ok.hecke d.m d.ok.res d.b d.K d.a
    d.ok.frame d.ok.stdK d.ok.hgt (s0 d.m d.n) (d.sec0 Φ) (hSec F E σ d Φ hK)
  intro x
  have hfl : ∀ z, (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ y) = flat d.a (d.sec0 Φ) (s0 d.m d.n) z :=
    fun z => funext fun y => by
      simp only [SD.Ht, flat]
      rw [Real.coe_toNNReal _ (Khead.hgt_nonneg d.ok.hgt y)]
  have Heisenberg₂ : ∀ z : ℂ, t < z.re → d.eis (d.sec0 Φ) (s0 d.m d.n) z x = Ê z x := fun z hz => by
    simp only [SD.eis]
    rw [hfl z]
    exact (hsum z hz x).tsum_eq
  have hmer := Khead.meromorphicOn_of_weak hw x
  have hext : IsExtAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (Ê · x) :=
    ⟨Set.univ, trivial, isRightDomain_univ, hmer, t, fun z hz => (Heisenberg₂ z hz).symm⟩
  obtain ⟨H', hext', han, hval⟩ := hM Φ hK x
  have hev := hext'.eventuallyEq hext
  have hloc : Function.update (Ê · x) (s0 d.m d.n) (c * d.I Φ x) =ᶠ[𝓝 (s0 d.m d.n)] H' := by
    filter_upwards [eventually_nhdsWithin_iff.1 hev] with z hz
    by_cases e : z = s0 d.m d.n
    · subst e; rw [Function.update_self]; exact hval.symm
    · rw [Function.update_of_ne e]; exact (hz e).symm
  refine ⟨Function.update (Ê · x) (s0 d.m d.n) (c * d.I Φ x), fun z _ => (hmer z trivial).update _ _,
    ⟨max t (s0 d.m d.n).re, fun z hz => ?_⟩, han.congr hloc.symm, Function.update_self _ _ _⟩
  have hz1 : t < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have hz2 : z ≠ s0 d.m d.n := fun e => by subst e; exact lt_irrefl _ (lt_of_le_of_lt (le_max_right _ _) hz)
  rw [Function.update_of_ne hz2]
  exact hsum z hz1 x

end PositivityTheory.SiegelWeilFormula.Atop

namespace PositivityTheory.SiegelWeilFormula

theorem Atop.fieldOf : FieldOf := by
  intro hBL hSec hLt hLe F E _ _ _ _ _ σ B m n A Y r s r' s' h1 h2 h3 h4 h5 χ h6 h7 κ _ dd om S l h8 b K a h9 h10 h11 μ D
    h12 h13 Φ h14 h15
  by_cases hlt : n < m
  · exact Khead.siegelWeilStd_lt hLt F E σ B m n A Y r s r' s' hlt h1 h2 h3 h4 h5 χ h6 h7 κ dd om S l h8 b K a h9 h10 h11
      μ D h12 h13 Φ h14 h15
  · simp only [if_neg hlt]
    let d : SD σ :=
      { B := B, m := m, n := n, A := A, Y := Y, r := r, s := s, χ := χ, κ := κ, dd := dd, om := om, S := S, l := l, b := b,
        K := K, a := a, μ := μ, D := D, bs := Khead.basis2 h1,
        ok := ⟨h1, h2, h3, h4, h5.imp (fun h => ⟨h.1, h.2.skew⟩) (fun h => ⟨h.1, h.2.herm⟩), h6, h7, h8, h9, h10, h11, h12,
          h13⟩ }
    have hY : d.Y.IsHerm σ d.B r' s' ∨ d.Y.IsSkew σ d.B r' s' := h5.elim (fun h => .inr h.2) (fun h => .inl h.2)
    exact Atop.eisValue_of hBL hSec d hY 2 (hLe F E σ d (not_lt.mp hlt)) Φ ⟨h14, h15⟩

end PositivityTheory.SiegelWeilFormula

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainLe
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem LD.n_succ {d : SD σ} (L : LD d) : L.n + 1 = d.n := by
  have e : Fin L.n ≃ {i : Fin d.n // ¬ i = L.i₀} :=
    Equiv.ofBijective (fun a => ⟨L.em a, (L.rng _).2 ⟨a, rfl⟩⟩)
      ⟨fun a b h => L.inj (congrArg Subtype.val h), fun i => by
        obtain ⟨a, ha⟩ := (L.rng i.1).1 i.2
        exact ⟨a, Subtype.ext ha⟩⟩
  have h := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq] at h
  have := L.i₀.pos
  omega

theorem rank_difference_induction (hRD : RDEx) (hLD : LDEx) (hVK : VacK) (hPK : PolyKFin) (hEq : MainEq) (hStep : Step)
    (hVA : VacAll) (k : ℕ) : ∀ d : SD σ, d.m ≤ d.n → d.n - d.m = k → MainC 2 d := by
  have hCV : ∀ (d : SD σ) (R : RD d) (c : ℂ), MainC c d → MainV c R := by
    intro d R c hC Φ hΦ hv x
    exact hC Φ (hPK F E σ d R Φ hΦ ((hVK F E σ d R).2.1 hv)) x
  have key : ∀ k' : ℕ, ∀ d : SD σ, d.m ≤ d.n → d.n - d.m = k' → ∀ R : RD d, MainV 2 R := by
    intro k'
    induction k' with
    | zero =>
      intro d h1 h2 R
      exact hCV d R 2 (hEq F E σ d (by omega))
    | succ k' ih =>
      intro d h1 h2 R
      have hm := d.ok.hm
      obtain ⟨L⟩ := hLD F E σ d (by omega)
      obtain ⟨R'⟩ := hRD F E σ L.sd
      have hn := LD.n_succ L
      refine hStep F E σ d R L R' (by omega) (ih L.sd ?_ ?_ R')
      · show d.m ≤ L.n
        omega
      · show L.n - d.m = k'
        omega
  intro d h1 h2
  obtain ⟨R⟩ := hRD F E σ d
  exact hVA F E σ d R 2 (key k d h1 h2 R)

end PositivityTheory.SiegelWeilFormula.Atop

namespace PositivityTheory.SiegelWeilFormula

theorem Atop.mainLeOf : MainLeOf := by
  intro hRD hLD hVK hPK hEq hStep hVA F E _ _ _ _ _ σ d h
  exact Atop.rank_difference_induction hRD hLD hVK hPK hEq hStep hVA _ d h rfl

end PositivityTheory.SiegelWeilFormula

end
end

