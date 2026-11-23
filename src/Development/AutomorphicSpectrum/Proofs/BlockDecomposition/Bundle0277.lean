module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0274
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0267
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.WeightSumAsFiniteDifferences
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0018
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineCocycleClosed
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactExhaustionStatement
section
noncomputable section

open Finset MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.WordFam

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem eword_smooth (hP : IsPsiFor ε lam T Ψ) (v : T.V) :
    ∀ w : List (Fin n × Fin n), IsSmoothL2 ε (Formalism.REAL.Eword ε w (jfun Ψ T.w v))
  | [] => datumFunction_isSmoothL2 hP T.w v
  | p :: w => (eword_smooth hP v w).Eab p.1 p.2

def cD (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) (v : T.V) : smD ε (rreg ε) :=
  ⟨toL2 ε (Formalism.REAL.Eword ε w (jfun Ψ T.w v)), toL2_mem_smD_of_isSmoothL2 (eword_smooth hP v w)⟩

theorem cD_cons (hP : IsPsiFor ε lam T Ψ) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (v : T.V) :
    cD hP (p :: w) v = smE ε (rreg ε) p.1 p.2 (cD hP w v) :=
  Subtype.ext (rightDerivative_toL2 (eword_smooth hP v w) p.1 p.2).symm

theorem cD_add (hP : IsPsiFor ε lam T Ψ) (u v : T.V) :
    ∀ w : List (Fin n × Fin n), cD hP w (u + v) = cD hP w u + cD hP w v
  | [] => Subtype.ext (datumEmbedding_add hP T.w u v)
  | p :: w => by rw [cD_cons, cD_cons, cD_cons, cD_add hP u v w, map_add (f := _)]

theorem cD_smul (hP : IsPsiFor ε lam T Ψ) (c : ℂ) (v : T.V) :
    ∀ w : List (Fin n × Fin n), cD hP w (c • v) = c • cD hP w v
  | [] => Subtype.ext (datumEmbedding_smul hP T.w c v)
  | p :: w => by rw [cD_cons, cD_cons, cD_smul hP c v w, map_smul]

theorem cD_zero (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) : cD hP w (0 : T.V) = 0 := by
  simpa using cD_smul hP (0 : ℂ) (0 : T.V) w

theorem actL_eq (hP : IsPsiFor ε lam T Ψ) {m : ℕ} (a : AS T m) :
    actL T Ψ a = ∑ x, (cD hP (ofW x) (a x) : L2 ε) := by
  have h := toL2_finset_sum_of_memLp (ε := ε) univ
    (fun x : Wd n m => Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (a x)))
    (fun x => (eword_smooth hP (a x) (ofW x)).2 [])
  have e : actF T Ψ a = fun g => ∑ x : Wd n m, Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (a x)) g := by
    funext g
    exact Finset.sum_apply _ _ _
  unfold actL
  rw [e]
  exact h

theorem ofW_inj {m : ℕ} {x y : Wd n m} (h : ofW x = ofW y) : x = y := by
  obtain ⟨⟨l, hl⟩, w⟩ := x
  obtain ⟨⟨l', hl'⟩, w'⟩ := y
  have hlen : l = l' := by simpa [ofW] using congrArg List.length h
  subst hlen
  have : w = w' := List.ofFn_injective h
  subst this
  rfl


open Classical in
def sgl (m : ℕ) (w : List (Fin n × Fin n)) (v : T.V) : AS T m := fun y => if ofW y = w then v else 0

theorem actL_sgl (hP : IsPsiFor ε lam T Ψ) {m : ℕ} {w : List (Fin n × Fin n)} (h : w.length ≤ m) (v : T.V) :
    actL T Ψ (sgl m w v) = (cD hP w v : L2 ε) := by
  have hx0 : ofW (⟨⟨w.length, Nat.lt_succ_of_le h⟩, w.get⟩ : Wd n m) = w := List.ofFn_get w
  rw [actL_eq hP, Finset.sum_eq_single (⟨⟨w.length, Nat.lt_succ_of_le h⟩, w.get⟩ : Wd n m)]
  · simp only [sgl, hx0, if_true]
  · intro y _ hy
    have hne : ofW y ≠ w := fun e => hy (ofW_inj (e.trans hx0.symm))
    simp only [sgl, if_neg hne, cD_zero]
    rfl
  · intro hn
    exact absurd (Finset.mem_univ _) hn

def actLin (hP : IsPsiFor ε lam T Ψ) (m : ℕ) : AS T m →ₗ[ℂ] L2 ε where
  toFun := actL T Ψ
  map_add' a b := by
    simp only [actL_eq hP, Pi.add_apply, cD_add, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [actL_eq hP, Pi.smul_apply, cD_smul, Submodule.coe_smul, Finset.smul_sum, RingHom.id_apply]

theorem actLin_apply (hP : IsPsiFor ε lam T Ψ) {m : ℕ} (a : AS T m) : actLin hP m a = actL T Ψ a := rfl

theorem pad (hP : IsPsiFor ε lam T Ψ) {m m' : ℕ} (h : m ≤ m') (a : AS T m) :
    ∃ a' : AS T m', actL T Ψ a' = actL T Ψ a := by
  refine ⟨∑ x : Wd n m, sgl m' (ofW x) (a x), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← actLin_apply hP, map_sum, actL_eq hP a]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [actLin_apply, actL_sgl hP]
  have : (ofW x).length = x.1 := by simp [ofW]
  have h2 := x.1.2
  omega

def exS (hP : IsPsiFor ε lam T Ψ) : Submodule ℂ (smD ε (rreg ε)) where
  carrier := {x | ∃ (m : ℕ) (a : AS T m), (x : L2 ε) = actL T Ψ a}
  add_mem' := by
    rintro x y ⟨m, a, ha⟩ ⟨m', b, hb⟩
    obtain ⟨a', ea⟩ := pad hP (le_max_left m m') a
    obtain ⟨b', eb⟩ := pad hP (le_max_right m m') b
    refine ⟨_, a' + b', ?_⟩
    rw [Submodule.coe_add, ha, hb, ← ea, ← eb]
    exact ((actLin hP _).map_add a' b').symm
  zero_mem' := ⟨0, 0, ((actLin hP 0).map_zero).symm⟩
  smul_mem' := by
    rintro c x ⟨m, a, ha⟩
    refine ⟨m, c • a, ?_⟩
    rw [Submodule.coe_smul, ha]
    exact ((actLin hP m).map_smul c a).symm

theorem cD_mem_exS (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) (v : T.V) : cD hP w v ∈ exS hP :=
  ⟨w.length, sgl _ w v, (actL_sgl hP le_rfl v).symm⟩

theorem eq_sum (hP : IsPsiFor ε lam T Ψ) {x : smD ε (rreg ε)} {m : ℕ} {a : AS T m}
    (h : (x : L2 ε) = actL T Ψ a) : x = ∑ y, cD hP (ofW y) (a y) :=
  Subtype.ext (by rw [h, actL_eq hP, Submodule.coe_sum])

theorem genSub_le_exS (hP : IsPsiFor ε lam T Ψ) :
    genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) ≤ exS hP := by
  refine sInf_le ⟨fun x hx => ?_, fun a b x hx => ?_⟩
  · obtain ⟨v, hv⟩ := (mem_datumV_iff hP T.w x).1 hx
    have : x = cD hP [] v := Subtype.ext hv
    rw [this]
    exact cD_mem_exS hP [] v
  · obtain ⟨m, f, hf⟩ := hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum hP hf, map_sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    have := cD_cons hP (a, b) (ofW y) (f y)
    simp only at this
    rw [← this]
    exact cD_mem_exS hP _ _

theorem cD_mem_genSub (hP : IsPsiFor ε lam T Ψ) (v : T.V) (w : List (Fin n × Fin n)) :
    cD hP w v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) := by
  refine (Submodule.mem_sInf).2 fun N hN => ?_
  induction w with
  | nil => exact hN.1 ((mem_datumV_iff hP T.w _).2 ⟨v, rfl⟩)
  | cons p w ih =>
    rw [cD_cons]
    exact hN.2 _ _ _ ih

theorem exhaust : Exhaust := by
  intro n ε lam T Ψ hP
  refine ⟨fun x hx => genSub_le_exS hP hx, fun m m' h a => pad hP h a, fun m a => ?_⟩
  refine ⟨∑ x, cD hP (ofW x) (a x),
    Submodule.sum_mem _ fun x _ => cD_mem_genSub hP _ _, ?_⟩
  rw [actL_eq hP]
  simp only [Submodule.subtype_apply, Submodule.coe_sum]

end GlobalTheory.CompanionTheory.WordFam
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeZetaSpecialValueDenominatorBound
section
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem eq_at_neg_of_eq_right (k p : ℕ) (hp : p < k) (T G : ℂ → ℂ)
    (hT : DifferentiableOn ℂ T {1}ᶜ) (hG : DifferentiableOn ℂ G {s | -(k : ℝ) < s.re})
    (h : ∀ s : ℂ, 1 < s.re → T s = G s) : T (-(p : ℂ)) = G (-(p : ℂ)) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le p) hp)
  have hpk : (p : ℝ) < k := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  set C₁ : Set ℂ := {s | -(k : ℝ) < s.re} ∩ {s | 0 < s.im} with hC₁
  set C₂ : Set ℂ := {s | -(k : ℝ) < s.re} ∩ {s | s.re < 1} with hC₂
  have hO₁ : IsOpen C₁ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hO₂ : IsOpen C₂ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hV₁ : Convex ℝ C₁ := (convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)
  have hV₂ : Convex ℝ C₂ := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  have hs₁ : C₁ ⊆ {1}ᶜ := by
    intro s hs h1
    have : s = 1 := h1
    have h2 := hs.2
    simp [this] at h2
  have hs₂ : C₂ ⊆ {1}ᶜ := by
    intro s hs h1
    have : s = 1 := h1
    have h2 := hs.2
    simp [this] at h2
  have hAT₁ : AnalyticOnNhd ℂ T C₁ := (hT.mono hs₁).analyticOnNhd hO₁
  have hAG₁ : AnalyticOnNhd ℂ G C₁ :=
    (hG.mono (show C₁ ⊆ {s | -(k : ℝ) < s.re} from fun _ hs => hs.1)).analyticOnNhd hO₁
  have hAT₂ : AnalyticOnNhd ℂ T C₂ := (hT.mono hs₂).analyticOnNhd hO₂
  have hAG₂ : AnalyticOnNhd ℂ G C₂ :=
    (hG.mono (show C₂ ⊆ {s | -(k : ℝ) < s.re} from fun _ hs => hs.1)).analyticOnNhd hO₂
  have hz₁ : (2 + Complex.I : ℂ) ∈ C₁ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hev₁ : T =ᶠ[nhds (2 + Complex.I : ℂ)] G := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (2 + Complex.I : ℂ) ∈ {s : ℂ | 1 < s.re})] with s hs
    exact h s hs
  have hE₁ : Set.EqOn T G C₁ :=
    hAT₁.eqOn_of_preconnected_of_eventuallyEq hAG₁ hV₁.isPreconnected hz₁ hev₁
  have hz₂ : (Complex.I : ℂ) ∈ C₂ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hz₂' : (Complex.I : ℂ) ∈ C₁ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hev₂ : T =ᶠ[nhds (Complex.I : ℂ)] G := by
    filter_upwards [hO₁.mem_nhds hz₂'] with s hs
    exact hE₁ hs
  have hE₂ : Set.EqOn T G C₂ :=
    hAT₂.eqOn_of_preconnected_of_eventuallyEq hAG₂ hV₂.isPreconnected hz₂ hev₂
  refine hE₂ ?_
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re]
    linarith
  · simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re]
    linarith

theorem abelValue_mem_zInv (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ)
    (w : (Fin r → ℕ) → ℚ) (hr : r ≤ Fintype.card ι) (hl : 0 < l) (ha : ∀ j i, 0 < a j i)
    (hb : ∀ j, 0 < b j) (hw : GoodWeight l w) (hz : ∀ m, ∃ z : ℤ, w m = z) (T : ℂ → ℂ)
    (hT : DifferentiableOn ℂ T {1}ᶜ)
    (hS : ∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) (p : ℕ)
    (hp : ∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) :
    ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  obtain ⟨Q, _, cs, u, K, hu, hc, hK, hid⟩ :=
    _root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int r l (Fintype.card ι * (p + 1) + 2) w hl hw hz
  set G : ℂ → ℂ := fun s => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m with hGdef
  have hG : DifferentiableOn ℂ G {s | -((p + 1 : ℕ) : ℝ) < s.re} := by
    refine DifferentiableOn.fun_sum fun q _ => ?_
    exact _root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.differentiableOn_tsum_weighted_DL_halfplane ι r a b ha hb (p + 1) _ (cs q) (u q) le_rfl (hu q) (hc q)
  have hTG : ∀ s : ℂ, 1 < s.re → T s = G s := by
    intro s hs
    rw [← (hS s hs).tsum_eq]
    exact hid _ (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable ι r a b hr ha hb s hs)
  have hval := eq_at_neg_of_eq_right (p + 1) p (Nat.lt_succ_self p) T G hT hG hTG
  choose ρ ζ hρ hζ using fun q => _root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.value_neg_nat_mem ι r a b (u q) (cs q) p K l hl (hK q) hp
  refine ⟨∑ q, ρ q, K, ∑ q, ζ q, ?_, ?_⟩
  · rw [hval, hGdef]
    push_cast
    exact Finset.sum_congr rfl fun q _ => hρ q
  · rw [Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun q _ => hζ q

theorem abelValue_mem_zInv' : ∀ (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ), r ≤ Fintype.card ι → 0 < l → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) → ∀ p : ℕ, (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  intro ι _ r l a b w hr hl ha hb hw hz T hT hS p hp
  exact abelValue_mem_zInv ι r l a b w hr hl ha hb hw hz T hT hS p hp

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTranslateNeZero
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def IsFix (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (v : π.V) : Prop :=
  ∀ k ∈ KGL w (n := a), π.locRep w k v = v

def sphSpan (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Submodule ℂ (Sm E a) :=
  Submodule.span ℂ {φ | ∃ (g : GL (Fin a) (w.adicCompletion E)) (v : π.V), IsFix π w v ∧ φ = (π.locRep w g v).1}

theorem locRep_val (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) (v : π.V) :
    (π.locRep w g v).1 = finRep E a (locGL E a w g) v.1 := rfl

theorem mem_sphSpan (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) {v : π.V}
    (hv : IsFix π w v) : (π.locRep w g v).1 ∈ sphSpan π w :=
  Submodule.subset_span ⟨g, v, hv, rfl⟩

theorem isFix_op (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : Op E a)
    (hc : ∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) {v : π.V} (hv : IsFix π w v) :
    IsFix π w (π.op o v) := fun k hk => by
  refine Subtype.ext ?_
  rw [locRep_val, CuspSub.op_val]
  have e := LinearMap.congr_fun (hc k) v.1
  simp only [Module.End.mul_apply] at e
  rw [← e, ← locRep_val, hv k hk]

theorem act_translate (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : Op E a)
    (hc : ∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o)
    (g : GL (Fin a) (w.adicCompletion E)) {v : π.V} (hv : IsFix π w v) :
    act o (π.locRep w g v).1 ∈ sphSpan π w := by
  have e := LinearMap.congr_fun (hc g) v.1
  simp only [Module.End.mul_apply] at e
  rw [locRep_val, e]
  exact mem_sphSpan π w g (isFix_op π w o hc hv)

theorem cpt_comm (y : Kinf E a) (k : GL (Fin a) (Af E)) :
    act (.cpt y : Op E a) * finRep E a k = finRep E a k * act (.cpt y : Op E a) := by
  change rt E a _ * rt E a _ = rt E a _ * rt E a _
  rw [← map_mul, ← map_mul]
  exact congrArg (rt E a) (infGL_comm _ _)

theorem lie_comm' (X : Lie E a) (k : GL (Fin a) (Af E)) :
    act (.lie X : Op E a) * finRep E a k = finRep E a k * act (.lie X : Op E a) :=
  lie_rt_fin X k

theorem fin_translate (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E))
    (g : GL (Fin a) (w.adicCompletion E)) {v : π.V} (hv : IsFix π w v) :
    finRep E a k (π.locRep w g v).1 ∈ sphSpan π w := by
  obtain ⟨h, gw, e, hc⟩ := _root_.GlobalTheory.CuspGeneric.exists_split_loc E a w (finGL E a (k * locGL E a w g))
  obtain ⟨h', hh'⟩ : ∃ h' : GL (Fin a) (Af E), h' = k * locGL E a w g * (locGL E a w gw)⁻¹ := ⟨_, rfl⟩
  have hh : h = finGL E a h' := by
    rw [hh', map_mul, map_inv, e, mul_inv_cancel_right]
  have hcomm : ∀ u, finRep E a h' * finRep E a (locGL E a w u) = finRep E a (locGL E a w u) * finRep E a h' := fun u => by
    have h2 := congrArg (rt E a) (hc u)
    rw [hh, map_mul, map_mul] at h2
    exact h2
  have hfix : IsFix π w (π.op (.fin h') v) := isFix_op π w (.fin h') (fun u => hcomm u) hv
  have e2 : finRep E a k (π.locRep w g v).1 = (π.locRep w gw (π.op (.fin h') v)).1 := by
    rw [locRep_val, locRep_val, CuspSub.op_val]
    change (finRep E a k * finRep E a (locGL E a w g)) v.1 = (finRep E a (locGL E a w gw) * finRep E a h') v.1
    rw [← hcomm, ← map_mul, ← map_mul, hh', inv_mul_cancel_right]
  rw [e2]
  exact mem_sphSpan π w gw hfix

theorem isStable_sphSpan (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : _root_.GlobalTheory.CuspRep.IsStable (sphSpan π w) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, v, hv, rfl⟩ := hx
    cases o with
    | fin k => exact fin_translate π w k g hv
    | cpt y => exact act_translate π w _ (fun u => cpt_comm y _) g hv
    | lie X => exact act_translate π w _ (fun u => lie_comm' X _) g hv
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem sphSpan_le (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : sphSpan π w ≤ π.V :=
  Submodule.span_le.2 fun _ ⟨g, v, _, e⟩ => e ▸ (π.locRep w g v).2

theorem exists_translate_ne_zero : G2 := by
  intro E _ _ _ a π w B hB l hl
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hx⟩ := hB.exists_vec
  have hfix : ∀ v : π.V, IsFix π w v → v ≠ 0 → IsSatVecGL w (π.locRep w) v B := fun v hv h0 =>
    hB.2 v (GlobalTheory.LGrp.mem_fixed.2 hv) h0
  have hxf : IsFix π w x := GlobalTheory.LGrp.mem_fixed.1 hx.2.1
  have hker : sphSpan π w ≤ (LinearMap.ker l).map π.V.subtype := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, v, hv, rfl⟩
    refine ⟨π.locRep w g v, ?_, rfl⟩
    by_cases h0 : v = 0
    · simp [h0]
    · exact hcon v g (hfix v hv h0)
  rcases π.irred _ (sphSpan_le π w) (isStable_sphSpan π w) with h | h
  · have h1 := mem_sphSpan π w 1 hxf
    rw [h, Submodule.mem_bot] at h1
    exact hx.1 (Subtype.ext (by simpa using h1))
  · refine hl (LinearMap.ext fun u => ?_)
    have h1 : u.1 ∈ sphSpan π w := by rw [h]; exact u.2
    obtain ⟨y, hy, e⟩ := hker h1
    rw [LinearMap.zero_apply, ← Subtype.ext (a1 := y) (a2 := u) e]
    exact hy

end GlobalTheory.CompanionTheory.SatakeBound

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueIsFirstChernTorsionFree
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrystallineFirstChernTorsionFree

section Core

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I}

def precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick ((B.schFn q).cr b ht κ)} {D : E.LineData X}
    (Λ₀ : B.CLift g D) (h : C' ⥤ C) : B.CLift (h ⋙ g) D where
  p c := Λ₀.p (h.obj c)
  hp c := Λ₀.hp (h.obj c)
  w φ := Λ₀.w (h.map φ)
  hw φ hh := Λ₀.hw (h.map φ) hh

end Core

section Main

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} {γ : DividedPowers I} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {l s : ℕ}

theorem dpow_vanish {T : Thick (nlFun γ 0 X q (κA O I))} (hT : TF l s T) (k : ℕ) (hk : s ≤ k) (x : T.B) (hx : x ∈ T.J) :
    (k.factorial : T.B) * T.δ.dpow (k + 1) x = 0 := by
  have h1 : T.δ.dpow (k + 1) x ∈ T.pdPow s := by
    rw [pdPow_eq]
    refine Ideal.subset_span ⟨[(k + 1, x)], ?_, ?_, ?_⟩
    · intro z hz
      rw [List.mem_singleton] at hz
      rw [hz]
      exact hx
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    · simp
  rw [hT.1] at h1
  rw [(Ideal.mem_bot.1 h1), mul_zero]

theorem lifts_of_mem (D : E.LineData X) (T : Thick (nlFun γ 0 X q (κA O I))) (h : ∃ V ∈ 𝒱D D, InU V T) :
    ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = pt T := by
  obtain ⟨V, ⟨σ, hσ⟩, hV⟩ := h
  have hr : Set.range (pt T) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
  refine ⟨IsOpenImmersion.lift V.ι (pt T) hr ≫ σ, ?_⟩
  rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]

end Main

theorem existsUnique_isFirstChernTorsionFree : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (D : E.LineData X), sSup (𝒱D D) = ⊤ → ∃! z, IsFirstChernThickening (TS γ q l s {⊤}) D s z := by
  intro O A _ _ _ I γ X q l s D hD
  have hle : St (TF l s) (𝒱D D) ≤ TS γ q l s {⊤} := fun T h => ⟨h.1, ⊤, rfl, fun _ _ => trivial⟩
  have hU : Used (TF l s : ObjectProperty (Thick (nlFun γ 0 X q (κA O I)))) := Or.inl ⟨rfl, l, s, rfl⟩
  have hb := (_root_.GlobalTheory.CompanionTheory.NlZar.zariski_descent (TF l s) hU (𝒱D D) {⊤} hle (by rintro W rfl; rw [hD]) 2).2.2
  let Q : ObjectProperty (Thick (nlFun γ 0 X q (κA O I))) := TS γ q l s {⊤}
  let Q' : ObjectProperty (Thick (nlFun γ 0 X q (κA O I))) := St (TF l s) (𝒱D D)
  let G₀ : Q'.FullSubcategory ⥤ Thick ((B.schFn q).cr (nlBase A I γ 0) rfl (κA O I)) := Q'.ι
  obtain ⟨Λ₀⟩ := _root_.GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) G₀ D
    (fun T => lifts_of_mem D T.obj T.property.2)
  have hz₀ := (_root_.GlobalTheory.CompanionTheory.CocCls.coc_cls G₀ D (RingHom.id A) s (fun T k hk x hx => dpow_vanish T.property.1 k hk x hx)).1 Λ₀
  obtain ⟨x, hx⟩ := hb.2 ((CH.cx _).cls _ hz₀)
  refine ⟨x, ?_, ?_⟩
  · intro C _ G hG Λ₁
    let G₁ : C ⥤ Thick ((B.schFn q).cr (nlBase A I γ 0) rfl (κA O I)) := G ⋙ Q.ι
    have hcl := _root_.GlobalTheory.CompanionTheory.CocCls.coc_cls G₁ D (RingHom.id A) s
      (fun T k hk x hx => dpow_vanish (G.obj T).property.1 k hk x hx)
    let G' : C ⥤ Q'.FullSubcategory := Q'.lift (G ⋙ Q.ι) fun T => ⟨(G.obj T).property.1, hG T⟩
    let Λ' : B.CLift G₁ D := precomp Λ₀ G'
    refine ⟨hcl.1 Λ₁, ?_⟩
    refine (hcl.2 Λ₁ Λ' (hcl.1 Λ₁) (hcl.1 Λ')).trans ?_
    have e1 : (CH.Mor.restrict (CH.modF (sP Q).A) G).pull 2 x =
        (CH.Mor.restrict (CH.modF (sP Q').A) G').pull 2 ((incl hle).o.pull 2 x) := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    rw [e1, hx]
    rfl
  · intro y hy
    apply hb.1
    obtain ⟨h1, h2⟩ := hy _ (ObjectProperty.ιOfLE hle) (fun T => T.property.2) Λ₀
    have e : (incl hle).o.pull 2 y = (CH.Mor.restrict (CH.modF (sP Q).A) (ObjectProperty.ιOfLE hle)).pull 2 y := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl
    rw [hx, e]
    exact h2.symm

end GlobalTheory.CompanionTheory.CrystallineFirstChernTorsionFree
end

