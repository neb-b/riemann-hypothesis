module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmodule
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesUnionTwistPlacesSplitDisjoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

open Classical

namespace GlobalTheory.TwistTypePlaces

private theorem isConjPl_lev_of_isConjPl_div {D : D7} {PP PP' : Pl D.host.E} (h : Formalism.L2.DIV.IsConjPl PP PP') :
    Formalism.IndefR.Lev.IsConjPl PP PP' := by
  intro c hc
  exact ⟨Formalism.DivisionValues.cO D.host.E c, (h c (Formalism.DivisionValues.cO D.host.E c) rfl).1 hc, rfl⟩

private theorem conjPl_ne_and_under_eq_of_ncard_primesOver_two {D : D7} (P : Pl D.host.E)
    (h2 : (Ideal.primesOver (P.under (𝓞 D.host.F)).asIdeal (𝓞 D.host.E)).ncard = 2) :
    Formalism.DivisionValues.conjPl P ≠ P ∧ (Formalism.DivisionValues.conjPl P).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := by
  rw [GlobalTheory.QuadSignLocal.ncard_primesOver] at h2
  have hsub : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)} ⊆
      {P, Formalism.DivisionValues.conjPl P} := by
    intro u hu
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with hq | hq
    · exact Or.inl hq
    · exact Or.inr hq
  have hle : ({P, Formalism.DivisionValues.conjPl P} : Set (HeightOneSpectrum (𝓞 D.host.E))).ncard ≤
      {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)}.ncard := by
    rw [h2]
    calc ({P, Formalism.DivisionValues.conjPl P} : Set (HeightOneSpectrum (𝓞 D.host.E))).ncard
        ≤ ({Formalism.DivisionValues.conjPl P} : Set (HeightOneSpectrum (𝓞 D.host.E))).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hS := Set.eq_of_subset_of_ncard_le hsub hle
  refine ⟨fun hc => ?_, ?_⟩
  · rw [hS, hc, Set.pair_eq_singleton, Set.ncard_singleton] at h2
    exact absurd h2 (by decide)
  · have hmem : Formalism.DivisionValues.conjPl P ∈
        {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)} := by
      rw [hS]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact hmem

theorem isSplitSet_union : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Formalism.L2.DIV.IsSplitSet (R.Pg ∪ R.Q t) ∧ Disjoint R.Pg (R.Q t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t
  obtain ⟨hdisj, hinj, hcard⟩ := GlobalTheory.TwistTypePlaces.places_split R F hC t
  refine ⟨?_, hdisj⟩
  unfold Formalism.L2.DIV.IsSplitSet
  intro PP hPP PP' hPP' hc

  have hPP' : PP' = Formalism.DivisionValues.conjPl PP := GlobalTheory.GoodPrimes.isConjPl_iff.mp (isConjPl_lev_of_isConjPl_div hc)
  obtain ⟨hne, hund⟩ := conjPl_ne_and_under_eq_of_ncard_primesOver_two PP (hcard PP hPP).1
  have hsame : PP' = PP :=
    hinj (Finset.mem_coe.mpr (hPP' ▸ ‹PP' ∈ R.Pg ∪ R.Q t›)) (Finset.mem_coe.mpr hPP) (by rw [hPP']; exact hund)
  exact hne (hPP' ▸ hsame)

end GlobalTheory.TwistTypePlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.FrameConj

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem conj_mem_iff {G : Type} [Group G] (H : Subgroup G) {T : G} (hT : T ∈ H) (x : G) :
    T * x * T⁻¹ ∈ H ↔ x ∈ H := by
  rw [Subgroup.mul_mem_cancel_right H (H.inv_mem hT), Subgroup.mul_mem_cancel_left H hT]

theorem frGL_mul_left (T β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y) :
    frGL (T * β) y = T * frGL β y * T⁻¹ := by
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem conj_mem_St_iff (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    T * x * T⁻¹ ∈ St (T * β) ↔ x ∈ St β := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [frGL_mul_left] at hy
    exact mul_left_cancel (mul_right_cancel hy)
  · rintro ⟨y, rfl⟩
    exact ⟨y, frGL_mul_left T β y⟩

theorem redFn_conj (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) :
    redFn (T * β) PP (T * x * T⁻¹) = redFn β PP x := by
  by_cases hx : x ∈ St β
  · obtain ⟨y, rfl⟩ := hx
    rw [← frGL_mul_left, redFn_frGL, redFn_frGL]
  · have h' : T * x * T⁻¹ ∉ St (T * β) := fun h => hx ((conj_mem_St_iff T β x).1 h)
    unfold redFn ext1
    rw [dite_eq_right hx, dite_eq_right h']

variable {LL : Type} [CommRing LL]

theorem rTup_conj (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) :
    rTup (T * β) L (T * x * T⁻¹) = rTup β L x := by
  funext PP
  show upperLeftBlock L.hr (redFn (T * β) PP.1 (T * x * T⁻¹)) = upperLeftBlock L.hr (redFn β PP.1 x)
  rw [redFn_conj]

theorem levFn_conj (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) :
    levFn (T * β) L (T * x * T⁻¹) = levFn β L x := by
  unfold levFn
  simp only [rTup_conj, redFn_conj]

theorem conj_mem_lev_iff [StarRing E] {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E}
    {T : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hT : T ∈ UA hc J) (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (L : LevDat E LL n) : T * x * T⁻¹ ∈ lev hc J (T * β) L ↔ x ∈ lev hc J β L := by
  rw [mem_lev, mem_lev, mem_parLev, mem_parLev, conj_mem_iff _ hT, conj_mem_St_iff, rTup_conj]
  simp only [redFn_conj]

end Gen

theorem levS_conj_frame : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) (t : GA D V),
    t ∈ GfC V → ∀ k : GA D V, (k ∈ levS V β L ↔ t * k * t⁻¹ ∈ levS V (finE V t * β) L) ∧
      levChi V (finE V t * β) L (t * k * t⁻¹) = levChi V β L k := by
  intro D V β L t ht k
  have hfin : finE V (t * k * t⁻¹) = finE V t * finE V k * (finE V t)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  refine ⟨?_, ?_⟩
  · show k ∈ levG V β L ↔ t * k * t⁻¹ ∈ levG V (finE V t * β) L
    simp only [levG, levA, Subgroup.mem_inf, Subgroup.mem_comap]
    rw [conj_mem_iff _ ht, hfin, conj_mem_lev_iff (GlobalTheory.LevSplit.finE_mem_UA V t)]
  · unfold levChi
    rw [hfin, levFn_conj]

end GlobalTheory.FrameConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeil
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.SiegelSet.ConeConv

theorem lintegral_Ici_rpow {b p : ℝ} (hb : 0 < b) (hp : p < 0) :
    ∫⁻ x, (Set.Ici b).indicator (fun x => ENNReal.ofReal (x ^ (p - 1))) x = ENNReal.ofReal (b ^ p / (-p)) := by
  rw [lintegral_indicator measurableSet_Ici, setLIntegral_congr Ioi_ae_eq_Ici.symm]
  have hlt : p - 1 < -1 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hlt hb)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x (hx : b < x) =>
      Real.rpow_nonneg (le_of_lt (lt_trans hb hx)) _)), integral_Ioi_rpow_of_lt hlt hb]
  congr 1
  have : p - 1 + 1 = p := by ring
  rw [this, div_neg, neg_div]

theorem mem_cone_cons {m : ℕ} {c x : ℝ} (y : Fin (m + 1) → ℝ) :
    (Fin.cons x y : Fin (m + 2) → ℝ) ∈ GlobalTheory.SiegelSet.cone (m + 2) c ↔
      (0 < x ∧ c * y 0 ≤ x) ∧ y ∈ GlobalTheory.SiegelSet.cone (m + 1) c := by
  simp only [GlobalTheory.SiegelSet.cone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hpos, hstep, hlast⟩
    refine ⟨⟨by simpa using hpos 0, by simpa using hstep 0 1 (by simp)⟩, fun i => by simpa using hpos i.succ,
      fun i j hij => by simpa using hstep i.succ j.succ (by simp [hij]),
      fun i hi => by simpa using hlast i.succ (by simp; omega)⟩
  · rintro ⟨⟨h0, h01⟩, hpos, hstep, hlast⟩
    refine ⟨fun i => Fin.cases (by simpa using h0) (fun i => by simpa using hpos i) i, fun i j hij => ?_,
      fun i hi => ?_⟩
    · induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        induction i using Fin.cases with
        | zero =>
          have : j = 0 := Fin.ext (by simpa using hij)
          subst this; simpa using h01
        | succ i => simpa using hstep i j (by simpa using hij)
    · induction i using Fin.cases with
      | zero => simp at hi
      | succ i => simpa using hlast i (by simpa using hi)

theorem mem_cone_one {c x : ℝ} (hc : 0 < c) :
    (fun _ => x : Fin 1 → ℝ) ∈ GlobalTheory.SiegelSet.cone 1 c ↔ c ≤ x := by
  simp only [GlobalTheory.SiegelSet.cone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, _, hlast⟩
    exact hlast 0 rfl
  · intro h
    refine ⟨fun _ => lt_of_lt_of_le hc h, fun i j hij => ?_, fun _ _ => h⟩
    exact absurd hij (by omega)

theorem lintegral_cone_lt_top {c : ℝ} (hc : 0 < c) : ∀ (m : ℕ) (a : ℕ → ℝ),
    (∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a i < 0) →
    ∫⁻ t, (GlobalTheory.SiegelSet.cone (m + 1) c).indicator
      (fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) t < ⊤ := by
  intro m
  induction m with
  | zero =>
    intro a ha
    have ha0 : a 0 < 0 := by simpa using ha 0 le_rfl
    change ∫⁻ t : Fin 1 → ℝ, (GlobalTheory.SiegelSet.cone 1 c).indicator
      (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.val - 1))) t < ⊤
    have key := (MeasurePreserving.symm _ (volume_preserving_funUnique (Fin 1) ℝ)).lintegral_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
      (fun t : Fin 1 → ℝ => (GlobalTheory.SiegelSet.cone 1 c).indicator
        (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.val - 1))) t)
    refine lt_of_eq_of_lt key.symm ?_
    have : ∀ x : ℝ, (GlobalTheory.SiegelSet.cone 1 c).indicator
        (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.val - 1))) ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm x)
        = (Set.Ici c).indicator (fun x => ENNReal.ofReal (x ^ (a 0 - 1))) x := by
      intro x
      have hx : (MeasurableEquiv.funUnique (Fin 1) ℝ).symm x = fun _ => x := by
        funext i; simp [MeasurableEquiv.funUnique_symm_apply]
      rw [hx]
      by_cases h : c ≤ x
      · rw [Set.indicator_of_mem ((mem_cone_one hc).2 h), Set.indicator_of_mem (Set.mem_Ici.2 h)]
        simp
      · rw [Set.indicator_of_notMem (fun h' => h ((mem_cone_one hc).1 h')),
          Set.indicator_of_notMem (fun h' => h (Set.mem_Ici.1 h'))]
    simp_rw [this]
    rw [lintegral_Ici_rpow hc ha0]
    exact ENNReal.ofReal_lt_top
  | succ m ih =>
    intro a ha
    have ha0 : a 0 < 0 := by simpa using ha 0 (Nat.zero_le _)
    set a' : ℕ → ℝ := fun i => if i = 0 then a 0 + a 1 else a (i + 1) with ha'
    have hsum : ∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a' i < 0 := by
      intro k hk
      have h := ha (k + 1) (by omega)
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
      rw [Finset.sum_range_succ']
      simp only [ha', if_pos, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false] at *
      linarith
    set K : ℝ≥0∞ := ENNReal.ofReal (c ^ a 0 / (-a 0))
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0
    rw [← (MeasurePreserving.symm _ (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0)).lintegral_comp_emb
      e.symm.measurableEmbedding, Measure.volume_eq_prod, ← lintegral_prod_swap]
    refine lt_of_le_of_lt (lintegral_prod_le _) ?_
    have hpt : ∀ y : Fin (m + 1) → ℝ, ∫⁻ x, (GlobalTheory.SiegelSet.cone (m + 1 + 1) c).indicator
        (fun t => ∏ i : Fin (m + 1 + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) (e.symm (Prod.swap (y, x)))
        ≤ K * (GlobalTheory.SiegelSet.cone (m + 1) c).indicator
          (fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a' i.val - 1))) y := by
      intro y
      have he : ∀ x, e.symm (Prod.swap (y, x)) = Fin.cons x y := by
        intro x; simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero'] <;> rfl
      simp_rw [he]
      by_cases hy : y ∈ GlobalTheory.SiegelSet.cone (m + 1) c
      · have hy0 : 0 < y 0 := hy.1 0
        have hb : 0 < c * y 0 := mul_pos hc hy0
        set T : ℝ≥0∞ := ∏ i : Fin (m + 1), ENNReal.ofReal (y i ^ (a (i.val + 1) - 1))
        have hfun : ∀ x, (GlobalTheory.SiegelSet.cone (m + 1 + 1) c).indicator
            (fun t => ∏ i : Fin (m + 1 + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) (Fin.cons x y)
            = (Set.Ici (c * y 0)).indicator (fun x => ENNReal.ofReal (x ^ (a 0 - 1))) x * T := by
          intro x
          by_cases hx : c * y 0 ≤ x
          · rw [Set.indicator_of_mem ((mem_cone_cons y).2 ⟨⟨lt_of_lt_of_le hb hx, hx⟩, hy⟩),
              Set.indicator_of_mem (Set.mem_Ici.2 hx), Fin.prod_univ_succ]
            simp [T, Fin.val_succ]
          · rw [Set.indicator_of_notMem (fun h' => hx ((mem_cone_cons y).1 h').1.2),
              Set.indicator_of_notMem (fun h' => hx (Set.mem_Ici.1 h')), zero_mul]
        simp_rw [hfun]
        rw [lintegral_mul_const' _ _ (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top),
          lintegral_Ici_rpow hb ha0, Set.indicator_of_mem hy]
        apply le_of_eq
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
        have hrest : ∏ j : Fin m, ENNReal.ofReal (y j.succ ^ (a (j.succ.val + 1) - 1))
            = ∏ j : Fin m, ENNReal.ofReal (y j.succ ^ (a' j.succ.val - 1)) :=
          Finset.prod_congr rfl fun j _ => by simp [ha', Fin.val_succ]
        have h1 : 0 ≤ (c * y 0) ^ a 0 / (-a 0) := div_nonneg (Real.rpow_nonneg hb.le _) (by linarith)
        have h2 : 0 ≤ c ^ a 0 / (-a 0) := div_nonneg (Real.rpow_nonneg hc.le _) (by linarith)
        have h0 : ENNReal.ofReal ((c * y 0) ^ a 0 / (-a 0)) * ENNReal.ofReal (y 0 ^ (a ((0 : Fin (m + 1)).val + 1) - 1))
            = K * ENNReal.ofReal (y 0 ^ (a' (0 : Fin (m + 1)).val - 1)) := by
          simp only [K, ha', Fin.val_zero, zero_add, if_true]
          rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2]
          congr 1
          rw [Real.mul_rpow hc.le hy0.le, show a 0 + a 1 - 1 = (a 1 - 1) + a 0 by ring, Real.rpow_add hy0]
          ring
        rw [hrest, ← mul_assoc, ← mul_assoc, h0]
      · have hz : ∀ x, (GlobalTheory.SiegelSet.cone (m + 1 + 1) c).indicator
            (fun t => ∏ i : Fin (m + 1 + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) (Fin.cons x y) = 0 :=
          fun x => Set.indicator_of_notMem (fun h' => hy ((mem_cone_cons y).1 h').2) _
        simp_rw [hz, lintegral_zero]
        exact bot_le
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ih a' hsum)

theorem measurableSet_cone (r : ℕ) (c : ℝ) : MeasurableSet (GlobalTheory.SiegelSet.cone r c) := by
  simp only [GlobalTheory.SiegelSet.cone, Set.setOf_and, Set.setOf_forall]
  exact (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_const.mul (measurable_pi_apply j)) (measurable_pi_apply i)).inter
     (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurableSet_le measurable_const (measurable_pi_apply i)))

end GlobalTheory.SiegelSet.ConeConv


open GlobalTheory.SiegelSet.ConeConv in
theorem GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top : ∀ (F : Type) [Field F] [NumberField F] (n r d : ℕ) {c : ℝ}, 0 < c →
    d < 2 * (n - r) → ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n r d c hc hd
  have hf : (0 : ℝ) < (Module.finrank ℚ F : ℝ) := by exact_mod_cast Module.finrank_pos
  cases r with
  | zero =>
    simp only [GlobalTheory.SiegelSet.modulus, Finset.univ_eq_empty, Finset.prod_empty, mul_one, inv_one, ENNReal.ofReal_one,
      lintegral_const, one_mul]
    rw [Measure.restrict_apply MeasurableSet.univ]
    change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) _ < ⊤
    rw [Measure.pi_of_empty]
    simp only [Set.univ_inter]
    exact measure_lt_top _ _
  | succ m =>
    set f := Module.finrank ℚ F with hfdef
    set a : ℕ → ℝ := fun i => (f : ℝ) * d - 2 * f * ((n : ℝ) - 2 * i - 1) with hadef
    have closed : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), a i = f * (k + 1) * (d - 2 * n + 2 * (k + 1)) := by
      intro k
      induction k with
      | zero => rw [Finset.sum_range_one]; simp only [hadef]; push_cast; ring
      | succ k ih => rw [Finset.sum_range_succ, ih]; simp only [hadef]; push_cast; ring
    have hsum : ∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a i < 0 := by
      intro k hk
      rw [closed]
      have h1 : d + 2 * (k + 1) < 2 * n := by omega
      have h2 : (d : ℝ) + 2 * (k + 1) < 2 * n := by exact_mod_cast h1
      exact mul_neg_of_pos_of_neg (mul_pos hf (by positivity)) (by linarith)
    have hmeas := measurableSet_cone (m + 1) c
    rw [setLIntegral_congr_fun hmeas (g := fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) ?_,
      ← lintegral_indicator hmeas]
    · exact lintegral_cone_lt_top hc m a hsum
    intro t ht
    have hpos : ∀ i, 0 < t i := ht.1
    dsimp only
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => pow_nonneg (hpos i).le _),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hpos i).le _)]
    congr 1
    unfold GlobalTheory.SiegelSet.modulus
    rw [← hfdef]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hti := hpos i
    rw [← Real.rpow_natCast, ← Real.rpow_intCast,
      show a i.val - 1 = ((f * d : ℕ) : ℝ) - ((2 * (f : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1 by
        simp only [hadef]; push_cast; ring,
      Real.rpow_sub hti, Real.rpow_sub hti, Real.rpow_one]
    field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactSpanHighestWeightLine
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.KSpanHighest

theorem kset_mul {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.REAL.Kset ε)
    (hb : b ∈ Formalism.REAL.Kset ε) : a * b ∈ Formalism.REAL.Kset ε := by
  rw [(Formalism.REAL.kFacts n ε).2.2.2.2] at ha hb ⊢
  exact ⟨GlobalTheory.KTypeExists.inUJ_mul ha.1 hb.1, Submonoid.mul_mem _ ha.2 hb.2⟩

theorem kset_of_mul {n : ℕ} {ε : Fin n → Bool} {k x : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε)
    (hx : Formalism.REAL.inUJ ε x) (hkx : k * x ∈ Formalism.REAL.Kset ε) : x ∈ Formalism.REAL.Kset ε := by
  rw [(Formalism.REAL.kFacts n ε).2.2.2.2] at hk hkx ⊢
  refine ⟨hx, ?_⟩
  have e : x = star k * (k * x) := by
    rw [← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hk.2, Matrix.one_mul]
  rw [e]
  exact Submonoid.mul_mem _ (Unitary.star_mem hk.2) hkx.2

theorem kspan_highest : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → (∀ v, ContinuousOn (fun g => ρ g v) (Formalism.MainNotions.S.UJset ε)) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε ρ S → ∀ (Λ : Fin n → ℝ) (w : H), w ∈ S → w ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ Λ w → (∀ a b : Fin n, a < b → ε a = ε b → ∀ x ∈ S, Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ (Λ + Formalism.REAL.root a b) x → x = 0) → (∀ (μ : Fin n → ℝ) (x : H), x ∈ Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε) → x ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ x → Formalism.MainNotions.S.CDom ε μ Λ) ∧ (∀ x ∈ Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ Λ x → ∃ c : ℂ, x = c • w) := by
  intro n ε H _ _ ρ hρ hcont hiso S hfd hS Λ w hw _ hΛ hkill
  classical
  have hKU : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ Formalism.MainNotions.S.UJset ε := fun g hg => (Formalism.REAL.kFacts n ε).1 g hg
  let πS : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] S) := fun g =>
    if hg : g ∈ Formalism.REAL.Kset ε then
      LinearMap.toContinuousLinearMap ((ρ g).toLinearMap.restrict (p := S) (q := S) (fun v hv => hS g hg v hv))
    else 0
  have hπ : ∀ g ∈ Formalism.REAL.Kset ε, ∀ v : S, ((πS g v : S) : H) = ρ g v := by
    intro g hg v
    simp [πS, hg]
  have hπ0 : ∀ g, g ∉ Formalism.REAL.Kset ε → πS g = 0 := fun g hg => by simp [πS, hg]
  have h1K : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε := by
    rw [(Formalism.REAL.kFacts n ε).2.2.2.2]
    exact ⟨by simp [Formalism.REAL.inUJ], Submonoid.one_mem _⟩
  have h1 : πS 1 = 1 := by
    ext v
    rw [hπ 1 h1K v, hρ.1]
    rfl
  have hmulK : ∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, πS (a * b) = (πS a).comp (πS b) := by
    intro a ha b hb
    ext v
    rw [hπ _ (kset_mul ha hb), ContinuousLinearMap.comp_apply, hπ a ha, hπ b hb, hρ.2 a (hKU a ha) b (hKU b hb)]
    rfl
  have hK : ∀ k ∈ Formalism.REAL.Kset ε, ∀ x, Formalism.REAL.inUJ ε x → πS (k * x) = πS k * πS x := by
    intro k hk x hx
    by_cases hxK : x ∈ Formalism.REAL.Kset ε
    · exact hmulK k hk x hxK
    · have : k * x ∉ Formalism.REAL.Kset ε := fun h => hxK (kset_of_mul hk hx h)
      rw [hπ0 _ this, hπ0 _ hxK, mul_zero]
  have hU : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.Kset ε) πS := by
    refine ⟨⟨h1, hmulK⟩, ?_, ?_⟩
    · intro g hg v
      rw [← Submodule.norm_coe, hπ g hg v, hiso g hg, Submodule.norm_coe]
    · intro v
      have hc : ContinuousOn (fun g => ((πS g v : S) : H)) (Formalism.REAL.Kset ε) :=
        ((hcont (v : H)).mono hKU).congr fun g hg => hπ g hg v
      exact (Topology.IsInducing.subtypeVal.continuousOn_iff).2 hc
  obtain ⟨E, hR, hUn, hder, -⟩ := ReciprocityTheory.ChartRestriction.DS.HW.uRepCompRed n ε S πS hU
  have hE : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inK ε Z → ∀ v : S,
      HasDerivAt (fun t : ℝ => πS (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0 := by
    intro Z hZ v
    have := hder Z hZ v
    simpa [ReciprocityTheory.ChartRestriction.DS.actM, LinearMap.sum_apply, LinearMap.smul_apply] using this
  have hwt : ∀ (μ : Fin n → ℝ) (v : S), IsWtOn (Formalism.REAL.Kset ε) πS μ v ↔ IsWtOn (Formalism.REAL.Kset ε) ρ μ (v : H) :=
    fun μ v => forall₂_congr fun θ hθ => by rw [← hπ _ hθ, ← Submodule.coe_smul, Subtype.coe_inj]
  set w' : S := ⟨w, hw⟩ with hw'
  have hwE : IsWeight E Λ w' := GlobalTheory.KTypeExists.isWeight_of_isWtOnK E hE Λ w' ((hwt Λ w').2 hΛ)
  have hhi : KHighest ε E Λ w' := by
    refine ⟨hwE, fun a b hab he => ?_⟩
    have h2 := GlobalTheory.KTypeExists.isWtOn_of_isWeightK h1 hK E hE _ _ (compact_weight_shift hR hwE he)
    have h3 : Λ + Pi.single a 1 - Pi.single b 1 = Λ + Formalism.REAL.root a b := by
      simp [Formalism.REAL.root, add_sub_assoc]
    rw [h3, hwt] at h2
    exact Subtype.ext (hkill a b hab he _ (E a b w').2 h2)
  have hst := GlobalTheory.KTypeExists.stable_of_derivedK h1 hK E hE _ (compact_span_stable (ε := ε) (F := E) w')
  have hspan : Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε) ≤ (kSpan ε E w').map S.subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨πS g w', hst g hg w' (mem_compact_span_self w'), hπ g hg w'⟩
  refine ⟨?_, ?_⟩
  · intro μ x hx hx0 hxw
    obtain ⟨y, hy, rfl⟩ := hspan hx
    exact GlobalTheory.KTypeExists.cdom_of_mem_kSpan E Λ μ w' y hR hUn hhi hy
      (fun h => hx0 (by rw [h]; rfl)) (GlobalTheory.KTypeExists.isWeight_of_isWtOnK E hE μ y ((hwt μ y).2 hxw))
  · intro x hx hxw
    obtain ⟨y, hy, rfl⟩ := hspan hx
    obtain ⟨heq, hline⟩ := compact_lowering_holds S n ε E Λ w' hR hhi
    obtain ⟨c, hc⟩ := hline y (heq ▸ hy) (GlobalTheory.KTypeExists.isWeight_of_isWtOnK E hE Λ y ((hwt Λ y).2 hxw))
    exact ⟨c, by rw [hc]; rfl⟩

end GlobalTheory.KSpanHighest
end

