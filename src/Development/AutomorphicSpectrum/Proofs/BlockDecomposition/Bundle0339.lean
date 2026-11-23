module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0224
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.StringsTwo
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaplacianPowerCasimirBound
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.LapSec

open GlobalTheory.CompanionTheory.FcSmooth (Lap)
open GlobalTheory.CompanionTheory.SobSecK (Rw_congr Rw_smooth)
open GlobalTheory.CompanionTheory.SobOpsPf (Rw_add Rw_post sob_congr sob_smul sob_sum sob_bs sob_Om sob_post Om_smooth)

variable {n : ℕ}

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Lap_eq (f : Mat n → V) (g : Mat n) : Lap f g = -∑ p, Rw [p, p] f g := rfl

theorem Lap_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Lap f) (GLs n) := by
  have h : ContDiffOn ℝ ∞ (fun g => ∑ p, Rw [p, p] f g) (GLs n) :=
    ContDiffOn.sum fun p _ => Rw_smooth [p, p] hf
  exact h.neg

theorem Lap_congr {f f' : Mat n → V} (e : Set.EqOn f f' (GLs n)) : Set.EqOn (Lap f) (Lap f') (GLs n) := by
  intro g hg
  simp only [Lap_eq]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun p _ => Rw_congr [p, p] e hg)

theorem Lap_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Lap (f + f')) (Lap f + Lap f') (GLs n) := by
  intro g hg
  simp only [Lap_eq, Pi.add_apply]
  rw [← neg_add, ← Finset.sum_add_distrib]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun p _ => Rw_add [p, p] hf hf' hg)

theorem Lap_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Lap fun y => A (f y)) (fun y => A (Lap f y)) (GLs n) := by
  intro g hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Lap_eq, map_neg, map_sum]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun p _ => Rw_post [p, p] A hf hg)

theorem iter_congr (j : ℕ) {f f' : Mat n → V} (e : Set.EqOn f f' (GLs n)) :
    Set.EqOn (Lap^[j] f) (Lap^[j] f') (GLs n) := by
  induction j generalizing f f' with
  | zero => exact e
  | succ j ih => exact ih (Lap_congr e)

theorem iter_add (j : ℕ) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Lap^[j] (f + f')) (Lap^[j] f + Lap^[j] f') (GLs n) := by
  induction j generalizing f f' with
  | zero => intro x _; rfl
  | succ j ih =>
    intro x hx
    exact (iter_congr j (Lap_add hf hf') hx).trans (ih (Lap_smooth hf) (Lap_smooth hf') hx)

end Words

section Sob

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem sob_Lap {f : Mat n → V} (hf : Sob μ f) : Sob μ (Lap f) :=
  sob_congr (f := (-1 : ℂ) • ∑ p, Rd (bs p) (Rd (bs p) f))
    (sob_smul _ (sob_sum _ hf fun p => sob_bs p (sob_bs p hf))) fun g _ => by
      simp [Lap]

theorem sob_iter (j : ℕ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Lap^[j] f) := by
  induction j generalizing f with
  | zero => exact hf
  | succ j ih => exact ih (sob_Lap hf)

theorem cls_add {F F' : Mat n → V} (h : MemLp (fun y : G n => F y.val) 2 μ)
    (h' : MemLp (fun y : G n => F' y.val) 2 μ) : cls μ (F + F') = cls μ F + cls μ F' := by
  rw [GlobalTheory.CompanionTheory.SecBd.cls_eq μ h, GlobalTheory.CompanionTheory.SecBd.cls_eq μ h', GlobalTheory.CompanionTheory.SecBd.cls_eq μ (f := F + F') (h.add h')]
  exact MemLp.toLp_add h h'

end Sob

theorem om_mem (hR : RCalc) (E : KMod n) {f : Mat n → E.V} (hf : f ∈ CE E) : Om f ∈ CE E := by
  have h1 := (hR n).2.1 E f hf true 2
  have h2 := (hR n).2.1 E f hf false 2
  refine ⟨Om_smooth hf.1, fun g hg k => ?_⟩
  simp only [Om, Pi.smul_apply, Pi.add_apply, h1.2 g hg k, h2.2 g hg k, map_add (f := _), map_smul]

theorem strong [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (Q : E.V →L[ℂ] E.V) (hR : RCalc)
    (hL : ∀ f ∈ CE E, ∀ g ∈ GLs n, Lap f g = -Om f g + Q (f g)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Mat n → E.V, Sob μ f → IsSec E f → ∀ B : E.V →L[ℂ] E.V,
      ‖cls μ (Lap^[j] fun y => B (f y))‖ ≤ C * ‖B‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ := by
  induction j with
  | zero =>
    refine ⟨1, zero_le_one, fun f hS _ B => ?_⟩
    have hm : MemLp (fun y : G n => B (f y.val)) 2 μ := (sob_post B hS).2 []
    have h := GlobalTheory.CompanionTheory.SecBd.norm_le_of_ae μ (f := f) (hS.2 []) (cls μ fun y => B (f y)) B
      (GlobalTheory.CompanionTheory.SecBd.cls_ae μ hm)
    simpa using h
  | succ j ih =>
    obtain ⟨C, hC, ih⟩ := ih
    refine ⟨C * (1 + ‖Q‖), by positivity, fun f hS hsec B => ?_⟩
    have hCE : f ∈ CE E := ⟨hS.1, hsec⟩
    have hOS := sob_Om hS
    have hOC := om_mem hR E hCE
    let a : Mat n → E.V := fun y => (-B) (Om f y)
    let b : Mat n → E.V := fun y => (B * Q) (f y)
    have ha : Sob μ a := sob_post _ hOS
    have hb : Sob μ b := sob_post _ hS
    have e1 : Set.EqOn (Lap fun y => B (f y)) (a + b) (GLs n) := fun g hg => by
      refine (Lap_post B hS.1 hg).trans ?_
      show B (Lap f g) = (-B) (Om f g) + (B * Q) (f g)
      rw [hL f hCE g hg]
      simp
    have e2 : Set.EqOn (Lap^[j + 1] fun y => B (f y)) (Lap^[j] a + Lap^[j] b) (GLs n) := fun g hg =>
      (iter_congr j e1 hg).trans (iter_add j ha.1 hb.1 hg)
    have mA : MemLp (fun y : G n => (Lap^[j] a) y.val) 2 μ := (sob_iter j ha).2 []
    have mB : MemLp (fun y : G n => (Lap^[j] b) y.val) 2 μ := (sob_iter j hb).2 []
    have e3 : cls μ (Lap^[j + 1] fun y => B (f y)) = cls μ (Lap^[j] a) + cls μ (Lap^[j] b) := by
      rw [← cls_add mA mB]
      exact (GlobalTheory.CompanionTheory.SecBd.cls_congr μ (f := Lap^[j] a + Lap^[j] b) (mA.add mB)
        fun g hg => (e2 hg).symm).symm
    have b1 : ‖cls μ (Lap^[j] a)‖ ≤ C * ‖-B‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] (Om f))‖ :=
      ih (Om f) hOS hOC.2 (-B)
    have b2 : ‖cls μ (Lap^[j] b)‖ ≤ C * ‖B * Q‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ :=
      ih f hS hsec (B * Q)
    set S := ∑ i ∈ range (j + 1 + 1), ‖cls μ (Om^[i] f)‖ with hSdef
    have s1 : ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] (Om f))‖ ≤ S := by
      have e := Finset.sum_range_succ' (fun i => ‖cls μ (Om^[i] f)‖) (j + 1)
      rw [hSdef, e]
      exact le_add_of_nonneg_right (norm_nonneg _)
    have s2 : ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ ≤ S := by
      rw [hSdef, Finset.sum_range_succ _ (j + 1)]
      exact le_add_of_nonneg_right (norm_nonneg _)
    have hBQ : ‖B * Q‖ ≤ ‖B‖ * ‖Q‖ := norm_mul_le _ _
    have c1 : C * ‖-B‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] (Om f))‖ ≤ C * ‖B‖ * S := by
      rw [norm_neg]
      exact mul_le_mul_of_nonneg_left s1 (by positivity)
    have c2 : C * ‖B * Q‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ ≤ C * (‖B‖ * ‖Q‖) * S := by
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
      exact mul_le_mul (mul_le_mul_of_nonneg_left hBQ hC) s2
        (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)
    rw [e3]
    calc _ ≤ ‖cls μ (Lap^[j] a)‖ + ‖cls μ (Lap^[j] b)‖ := norm_add_le _ _
      _ ≤ C * ‖B‖ * S + C * (‖B‖ * ‖Q‖) * S := add_le_add (b1.trans c1) (b2.trans c2)
      _ = C * (1 + ‖Q‖) * ‖B‖ * S := by ring

theorem sectionBound : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (Q : E.V →L[ℂ] E.V), LgFacts → Unimod → RCalc → ClsFacts →
    (∀ f ∈ CE E, ∀ g ∈ GLs n, GlobalTheory.CompanionTheory.FcSmooth.Lap f g = -Om f g + Q (f g)) →
    ∀ j : ℕ, ∃ C : ℝ, ∀ f : Mat n → E.V, Sob μ f → IsSec E f →
      ‖cls μ (GlobalTheory.CompanionTheory.FcSmooth.Lap^[j] f)‖ ≤ C * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ := by
  intro n _ _ μ _ E Q _ _ hR _ hL j
  obtain ⟨C, -, h⟩ := strong μ E Q hR hL j
  refine ⟨C * ‖(1 : E.V →L[ℂ] E.V)‖, fun f hS hs => ?_⟩
  simpa only [ContinuousLinearMap.one_apply] using h f hS hs 1

end GlobalTheory.CompanionTheory.LapSec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetOfStringsDeterminesPointsDegrees
section
open GlobalTheory.DiscSpec

namespace GlobalTheory.CompanionTheory.Rigid


open Classical in
theorem card_spehExp_eq (d m : ℕ) (hm : 1 ≤ m) :
    ((Finset.univ : Finset (Fin d)).filter (fun k => ((m : ℝ) - 1) / 2 = spehExp d k)).card =
      if m ≤ d ∧ Even (d - m) then 1 else 0 := by
  split_ifs with h
  · obtain ⟨hle, t, ht⟩ := h
    have hd : d = m + 2 * t := by omega
    have hdR : (d : ℝ) = m + 2 * t := by exact_mod_cast hd
    have htd : t < d := by omega
    rw [Finset.card_eq_one]
    refine ⟨⟨t, htd⟩, ?_⟩
    ext k
    rw [Finset.mem_filter, Finset.mem_singleton]
    simp only [Finset.mem_univ, true_and, spehExp]
    constructor
    · intro hk
      apply Fin.ext
      have : ((k : ℕ) : ℝ) = t := by linarith
      exact_mod_cast this
    · rintro rfl
      show ((m : ℝ) - 1) / 2 = ((d : ℝ) - 1) / 2 - (t : ℝ)
      linarith
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _ hk
    apply h
    simp only [spehExp] at hk
    have h1 : (d : ℝ) = m + 2 * ((k : ℕ) : ℝ) := by linarith
    have h2 : d = m + 2 * (k : ℕ) := by exact_mod_cast h1
    exact ⟨by omega, (k : ℕ), by omega⟩


open Classical in
theorem count_strings {X ι : Type} [Fintype ι] (p : ι → X) (d : ι → ℕ) (x : X) (m : ℕ) (hm : 1 ≤ m) :
    (GlobalTheory.Rigid.strings p d).count (x, ((m : ℝ) - 1) / 2) =
      (Finset.univ.filter fun i => p i = x ∧ m ≤ d i ∧ Even (d i - m)).card := by
  unfold GlobalTheory.Rigid.strings
  rw [Multiset.count_sum', Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Multiset.count_map]
  by_cases hx : p i = x
  · have h := card_spehExp_eq (d i) m hm
    simp only [hx, true_and, Prod.mk.injEq]
    rw [← h]
    rfl
  · have hx' : ¬ x = p i := fun e => hx e.symm
    simp [hx, hx']


open Classical in
theorem card_fibre_add {ι : Type} {X : Type} [Fintype ι] (p : ι → X) (d : ι → ℕ) (x : X) (m : ℕ) :
    (Finset.univ.filter fun i => p i = x ∧ d i = m).card +
        (Finset.univ.filter fun i => p i = x ∧ m + 2 ≤ d i ∧ Even (d i - (m + 2))).card =
      (Finset.univ.filter fun i => p i = x ∧ m ≤ d i ∧ Even (d i - m)).card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hx : p i = x
  · simp only [hx, true_and, Nat.even_iff]
    split_ifs <;> omega
  · simp [hx]


open Classical in
theorem card_fibre_eq {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X)
    (d' : κ → ℕ) (hd : ∀ i, 1 ≤ d i) (hd' : ∀ j, 1 ≤ d' j)
    (h : GlobalTheory.Rigid.strings p d = GlobalTheory.Rigid.strings p' d') (x : X) (m : ℕ) :
    (Finset.univ.filter fun i => p i = x ∧ d i = m).card =
      (Finset.univ.filter fun j => p' j = x ∧ d' j = m).card := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 : (Finset.univ.filter fun i => p i = x ∧ d i = 0) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun i _ hi => by have := hd i; omega
    have h2 : (Finset.univ.filter fun j => p' j = x ∧ d' j = 0) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun j _ hj => by have := hd' j; omega
    rw [h1, h2, Finset.card_empty, Finset.card_empty]
  · have a1 := card_fibre_add p d x m
    have a2 := card_fibre_add p' d' x m
    have c1 := count_strings p d x m hm
    have c2 := count_strings p' d' x m hm
    have e1 := count_strings p d x (m + 2) (by omega)
    have e2 := count_strings p' d' x (m + 2) (by omega)
    rw [h] at c1 e1
    omega

theorem strings_rigid {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X)
    (d' : κ → ℕ) (hd : ∀ i, 1 ≤ d i) (hd' : ∀ j, 1 ≤ d' j)
    (h : GlobalTheory.Rigid.strings p d = GlobalTheory.Rigid.strings p' d') :
    ∃ s : ι ≃ κ, ∀ i, p i = p' (s i) ∧ d i = d' (s i) := by
  classical
  have hc : ∀ c : X × ℕ, Fintype.card {i // (p i, d i) = c} = Fintype.card {j // (p' j, d' j) = c} := by
    rintro ⟨x, m⟩
    have := card_fibre_eq p d p' d' hd hd' h x m
    simp only [Fintype.card_subtype, Prod.mk.injEq]
    convert this
  let e : ∀ c : X × ℕ, {i // (p i, d i) = c} ≃ {j // (p' j, d' j) = c} :=
    fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv e, fun i => ?_⟩
  have := Equiv.ofFiberEquiv_map e i
  exact ⟨(congrArg Prod.fst this).symm, (congrArg Prod.snd this).symm⟩

end GlobalTheory.CompanionTheory.Rigid
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLtOneOfPowTendstoZero
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
open MeasureTheory ValuativeRel

noncomputable section
namespace GlobalTheory.CompanionTheory.NabsContract

theorem valuation_lt_one_of_tendsto_pow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ)
    (ht : Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0)) : valuation k (t : k) < 1 := by
  by_contra H
  rw [not_lt] at H
  have hs : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun x hx => by simpa using hx⟩
  obtain ⟨n, hn⟩ := (ht.eventually hs).exists
  have hn' : valuation k ((t : k) ^ n) < 1 := hn
  rw [map_pow] at hn'
  exact (not_lt.mpr (one_le_pow₀ H)) hn'

theorem nabs_lt_one_of_tendsto_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ),
    Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) → nabs k t < 1 := by
  intro k _ _ _ _ t ht
  have hv := GlobalTheory.CompanionTheory.NabsContract.valuation_lt_one_of_tendsto_pow t ht
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.t2Space k
  set ν : Measure k := Measure.addHaar with hν
  set O : Set k := ((valuation k).integer : Set k) with hO_def
  set B : Set k := GlobalTheory.SplitWeil.cball t with hB_def
  have hO : IsOpen O := GlobalTheory.SplitWeil.isOpen_int k
  have hBO : B ⊆ O := fun x hx =>
    (Valuation.mem_integer_iff _ _).mpr
      (le_trans (show valuation k x ≤ valuation k (t : k) from hx) hv.le)
  have hO1 : O ⊆ GlobalTheory.SplitWeil.cball (1 : kˣ) := fun x hx => by
    have hx' := (Valuation.mem_integer_iff _ _).mp hx
    show valuation k x ≤ valuation k ((1 : kˣ) : k)
    rw [Units.val_one, map_one]
    exact hx'
  have hOfin : ν O ≠ ⊤ :=
    measure_ne_top_of_subset hO1 (GlobalTheory.SplitWeil.isCompact_cball (1 : kˣ)).measure_lt_top.ne
  have hBfin : ν B ≠ ⊤ := measure_ne_top_of_subset hBO hOfin
  have h1 : (1 : k) ∈ O \ B := by
    refine ⟨(Valuation.mem_integer_iff _ _).mpr (map_one _).le, fun h => ?_⟩
    have h' : valuation k (1 : k) ≤ valuation k (t : k) := h
    rw [map_one] at h'
    exact not_lt.mpr h' hv
  have hdiff : 0 < ν (O \ B) :=
    (hO.sdiff (GlobalTheory.SplitWeil.isCompact_cball t).isClosed).measure_pos ν ⟨1, h1⟩
  rw [measure_sdiff hBO (GlobalTheory.SplitWeil.isOpen_cball t).measurableSet.nullMeasurableSet
    hBfin, tsub_pos_iff_lt] at hdiff
  have hlt : ν.real B < ν.real O := (ENNReal.toReal_lt_toReal hBfin hOfin).mpr hdiff
  have hOpos : 0 < ν.real O :=
    ENNReal.toReal_pos (hO.measure_pos ν ⟨0, (Valuation.mem_integer_iff _ _).mpr (by simp)⟩).ne'
      hOfin
  have hmeas : ν.real B = GlobalTheory.SplitWeil.nabs k t * ν.real O :=
    GlobalTheory.SplitWeil.measureReal_cball ν t
  rw [hmeas] at hlt
  exact lt_of_mul_lt_mul_right (by rwa [one_mul]) hOpos.le

end GlobalTheory.CompanionTheory.NabsContract
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicInductionCentralCharacterProd
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ZCentre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem scalar_apply {R : Type} [Field R] {n : Type} [Fintype n] [DecidableEq n] (t : Rˣ) (i j : n) :
    ((Matrix.GeneralLinearGroup.scalar n t : GL n R) : Matrix n n R) i j = if i = j then (t : R) else 0 := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem det_scalar {R : Type} [Field R] {n : Type} [Fintype n] [DecidableEq n] (t : Rˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar n t : GL n R) = t ^ Fintype.card n := by
  ext; simp [Matrix.GeneralLinearGroup.scalar]

theorem scalar_comm {R : Type} [Field R] {n : Type} [Fintype n] [DecidableEq n] (t : Rˣ) (g : GL n R) :
    g * Matrix.GeneralLinearGroup.scalar n t = Matrix.GeneralLinearGroup.scalar n t * g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

theorem sum_card_mul_modExp : ∑ a, (Fintype.card (m a) : ℤ) * modExp m a = 0 := by
  simp only [modExp, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp [mul_comm]


variable (k) in
theorem deltaHalf_scalar (t : kˣ) :
    deltaHalf k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) = 1 := by
  have h1 : modulus k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) = 1 := by
    have h2 : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (m a) t : GL (m a) k)) ^ modExp m a =
        nabs k t ^ ((Fintype.card (m a) : ℤ) * modExp m a) := fun a => by
      rw [det_scalar, zpow_mul, zpow_natCast]
      congr 1
      simp [nabs]
    simp only [modulus, h2]
    have h3 : ∀ (s : Finset α) (f : α → ℤ), ∏ a ∈ s, nabs k t ^ f a = nabs k t ^ ∑ a ∈ s, f a := fun s f => by
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ (nabs_pos' k t).ne', ih]
    rw [h3, sum_card_mul_modExp, zpow_zero]
  refine Units.ext ?_
  rw [val_deltaHalf, h1]
  simp

theorem piTensor_scalar {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (h : ∀ a v, ρ a (g a) v = c a • v) (w : PiTensorProduct ℂ X) :
    piTensor ρ g w = (∏ a, c a) • w := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    simp only [h]
    exact MultilinearMap.map_smul_univ _ _ _
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]

theorem scalar_mem_parab (e : (Σ a, m a) ≃ n) (t : kˣ) :
    Matrix.GeneralLinearGroup.scalar n t ∈ parab k e := by
  refine mem_parab.2 fun i j hij => ?_
  rw [scalar_apply, if_neg]
  rintro rfl
  exact lt_irrefl _ hij

theorem leviProj_scalar (e : (Σ a, m a) ≃ n) (t : kˣ) :
    leviProj k e ⟨_, scalar_mem_parab e t⟩ = fun a => Matrix.GeneralLinearGroup.scalar (m a) t := by
  funext a
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [leviProj_apply, scalar_apply, scalar_apply]
  simp

theorem parInd_scalar {W : Type} [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n)
    (ρ : Representation ℂ (Levi k m) W) (t : kˣ) (c : ℂ)
    (h : ∀ w, ρ (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) w = c • w) (f : IndSp e ρ) :
    parInd e ρ (Matrix.GeneralLinearGroup.scalar n t) f = c • f := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  have h1 := parInd_law e ρ f ⟨_, scalar_mem_parab e t⟩ g
  rw [leviProj_scalar, deltaHalf_scalar, h] at h1
  rw [parInd_apply, scalar_comm]
  simpa using h1

theorem prodIrr_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (t : kˣ) (c : Fin h → ℂ),
    (∀ a, Zl.ScalarBy (x a) t (c a)) →
      ∀ v, prodIrr x hd (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = (∏ a, c a) • v := by
  intro k _ _ _ _ h N x hd t c hc v
  exact parInd_scalar _ _ t _ (fun w => piTensor_scalar _ _ c (fun a v => hc a v) w) v

end GlobalTheory.CompanionTheory.ZCentre

end
end

