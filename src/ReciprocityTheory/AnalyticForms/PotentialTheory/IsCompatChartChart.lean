module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ProjectiveLineZeroFormHolds

@[expose] public section

namespace ReciprocityTheory.AnForm.M.PLAux

open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt densV PoincareLelongData log_norm_integral_formula_snc)
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]

theorem isCompatChart_chart (A : FinHolAtlas e X) (j : Fin A.n) : IsCompatChart A (A.chart j) :=
  fun k => ⟨A.holo k j, A.holo j k⟩

theorem pl_chart (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ)
    (hL : IsPotential A L) (hs : IsSection A L s)
    (hℓ : ∀ Φ' : Fin (e + 1) → LocPot X, (∀ i, IsPotential A (Φ' i)) →
      MIntegrable A Φ' (logNormSec L s))
    (Φ : Fin e → LocPot X) (hΦ : ∀ k, IsPotential A (Φ k)) (x : X)
    (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) (hψ : IsCompatChart A ψ)
    (hψL : ψ.source ⊆ L.U x) (u : X → ℂ) (hu : A.HoloOn ψ.source u)
    (hu0 : ∀ p ∈ ψ.source, u p ≠ 0) (M : Fin (e + 1) → ℤ)
    (hsu : ∀ p ∈ ψ.source, s x p = u p * ∏ i, ψ p i ^ M i) {V : Set X} (hV : IsOpen V)
    (hVψ : V ⊆ ψ.source) (hVΦ : ∀ k, V ⊆ (Φ k).U x) {v : X → ℝ} (hv : A.Smooth v)
    (hvV : tsupport v ⊆ V) :
    mInt A (Fin.cons (LocPot.ofFun v) Φ) (logNormSec L s) =
      ∑ i, (M i : ℝ) * (∫ w, chartExt ψ v (hypInclAt i w) *
        densHypAt i (fun k => (Φ k).φ x ∘ ψ.symm) w) - mInt A (Fin.cons L Φ) v := by
  classical
  have mInt_congr {B : FinHolAtlas (e + 1) X} {P Q : Fin (e + 1) → LocPot X}
      {g g' : X → ℝ}
      (h : ∀ j, ∀ y ∈ (B.chart j).target,
        g ((B.chart j).symm y) * locDens B P j y =
          g' ((B.chart j).symm y) * locDens B Q j y) : mInt B P g = mInt B Q g' := by
    unfold mInt
    split_ifs
    · unfold integralWith
      refine Finset.sum_congr rfl fun j _ => ?_
      refine setIntegral_congr_fun (B.chart j).open_target.measurableSet fun y hy => ?_
      simp only [mul_assoc]
      rw [h j y hy]
    · rfl

  have hcomp : ∀ i, IsCompatChart A
      ((Fin.cons ψ A.chart : Fin (A.n + 1) → OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hψ
    · simpa using isCompatChart_chart A j
  obtain ⟨A', hAA', hin, -⟩ := atlasOfCompat A _ hcomp
    (fun p => ⟨(A.cover p).choose.succ, by simpa using (A.cover p).choose_spec⟩)
  have mIntAtlasIndep (P : Fin (e + 1) → LocPot X) (hP : ∀ i, IsPotential A (P i))
      (g : X → ℝ) (hg : MIntegrable A P g) :
      MIntegrable A' P g ∧ mInt A P g = mInt A' P g := by
    have hg' := mIntegrable_of_compatible hAA' P hP hg
    refine ⟨hg', ?_⟩
    have hU := compatible_unionAtlas_left A A' hAA'
    have hPU := fun i => isPotential_of_compatible hU (hP i)
    have hgU := mIntegrable_of_compatible hU P hP hg
    have hP' := fun i => isPotential_of_compatible hAA' (hP i)
    obtain ⟨R⟩ := existsPartition A
    obtain ⟨R'⟩ := existsPartition A'
    rw [mIntEq A R P hP g hg, mIntEq A' R' P hP' g hg',
      ← integralWith_extendLeft hAA' R P g, ← integralWith_extendRight hAA' R' P g]
    exact integralWithIndep _ _ _ P hPU g hgU
  obtain ⟨j0, hj0⟩ := hin 0
  simp only [Fin.cons_zero] at hj0
  set Φv : Fin (e + 1) → LocPot X := Fin.cons (LocPot.ofFun v) Φ with hΦvd
  have hΦv : ∀ i, IsPotential A (Φv i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact isPotential_ofFun A v hv
    · exact hΦ k
  have hΦv' : ∀ i, IsPotential A' (Φv i) := fun i => isPotential_of_compatible hAA' (hΦv i)
  set ℓ := logNormSec L s with hℓd
  obtain ⟨hℓ', hAA'eq⟩ := mIntAtlasIndep Φv hΦv ℓ (hℓ Φv hΦv)
  have hne : Nonempty (ChartPartition A') := existsPartition A'

  have hvs : tsupport v ⊆ ψ.source := hvV.trans hVψ
  obtain ⟨hv'C, hKc, hv'K⟩ := contDiff_chartExt hψ hv hvs
  have hU' : IsOpen (ψ '' V) := ψ.isOpen_image_of_subset_source hV hVψ
  have hKU : ψ '' tsupport v ⊆ ψ '' V := Set.image_mono hvV
  have hU'T : ψ '' V ⊆ ψ.target := by rintro _ ⟨p, hp, rfl⟩; exact ψ.map_source (hVψ hp)
  have hKT : ψ '' tsupport v ⊆ ψ.target := hKU.trans hU'T
  obtain ⟨ρt, hρC, hρc, hρU, O, hO, hKO, hO1⟩ := exists_cutoff hKc hU' hKU
  have hφL : ContDiffOn ℝ ∞ (L.φ x ∘ ψ.symm) ψ.target :=
    (contDiffOn_compat hψ (L.isOpen_U x) (hL.1 x)).mono fun y hy => ⟨hy, hψL (ψ.map_target hy)⟩
  have hFwC : ContDiff ℝ ∞ (fun y => ρt y * (L.φ x ∘ ψ.symm) y) :=
    contDiff_mul_of_tsupport ψ.open_target hρC (hρU.trans hU'T) hφL
  have hFwt : tsupport (fun y => ρt y * (L.φ x ∘ ψ.symm) y) ⊆ tsupport ρt :=
    tsupport_mul_subset_left
  have hFwc : IsCompact (tsupport (fun y => ρt y * (L.φ x ∘ ψ.symm) y)) :=
    hρc.of_isClosed_subset (isClosed_tsupport _) hFwt
  set ρ := chartPush ψ ρt with hρd
  set w := chartPush ψ (fun y => ρt y * (L.φ x ∘ ψ.symm) y) with hwd
  have hρs : A.Smooth ρ := smooth_chartPush hψ hρC hρc (hρU.trans hU'T)
  have hws : A.Smooth w := smooth_chartPush hψ hFwC hFwc (hFwt.trans (hρU.trans hU'T))
  have hwsupp : tsupport w ⊆ ψ.source :=
    tsupport_chartPush_source ψ hFwc (hFwt.trans (hρU.trans hU'T))
  have hρsupp : tsupport ρ ⊆ ψ.source := tsupport_chartPush_source ψ hρc (hρU.trans hU'T)
  have hρ1 : ∀ p ∈ tsupport v, ρ p = 1 := fun p hp => by
    simp only [hρd, chartPush, Set.indicator_of_mem (hvs hp), Function.comp_apply]
    exact hO1 _ (hKO ⟨p, hp, rfl⟩)
  have hwL : ∀ p ∈ ψ.source, ψ p ∈ O → w p = L.φ x p := fun p hp hpO => by
    simp only [hwd, chartPush, Set.indicator_of_mem hp, Function.comp_apply, hO1 _ hpO, one_mul,
      ψ.left_inv hp]

  have hD0 : ∀ y ∈ ψ.target, ψ.symm y ∉ tsupport v → locDens A' Φv j0 y = 0 := by
    intro y hy hp
    exact locDens_cons_ofFun_eq_zero (A := A') v Φ j0 (by rw [hj0]; exact hy) (by rw [hj0]; exact hp)
  have hDK : ∀ y ∈ ψ.target, y ∉ ψ '' tsupport v → locDens A' Φv j0 y = 0 := by
    intro y hy hyK
    exact hD0 y hy fun hp => hyK ⟨_, hp, ψ.right_inv hy⟩

  have hb : mInt A' Φv ℓ = mInt A' Φv (fun p => ρ p * ℓ p) := by
    apply mInt_congr
    intro j y hy
    by_cases hp : (A'.chart j).symm y ∈ tsupport v
    · rw [hρ1 _ hp, one_mul]
    · have h0 : locDens A' Φv j y = 0 := locDens_cons_ofFun_eq_zero v Φ j hy hp
      rw [h0, mul_zero, mul_zero]
  have hmiρ : MIntegrable A' Φv (fun p => ρ p * ℓ p) :=
    mIntegrableMul A' Φv ℓ ρ hℓ' (smooth_continuous hρs)
  have hc : mInt A' Φv (fun p => ρ p * ℓ p) =
      ∫ y in ψ.target, ρ (ψ.symm y) * ℓ (ψ.symm y) * locDens A' Φv j0 y := by
    unfold mInt
    rw [dite_eq_left hne, mIntLocalize A' hne.some Φv hΦv' j0 (fun p => ρ p * ℓ p)
      (by rw [hj0]; exact tsupport_mul_subset_left.trans hρsupp) hmiρ, hj0]

  have hG1 : IntegrableOn (fun y => ρ (ψ.symm y) * ℓ (ψ.symm y) * locDens A' Φv j0 y) ψ.target := by
    have h := hmiρ j0 _ (by rw [hj0]; exact hKT) hKc
    rw [hj0] at h
    refine h.of_forall_sdiff_eq_zero ψ.open_target.measurableSet ?_
    rintro y ⟨hy, hyK⟩
    show ρ (ψ.symm y) * ℓ (ψ.symm y) * locDens A' Φv j0 y = 0
    rw [hDK y hy hyK, mul_zero]
  have hmiw : MIntegrable A' Φv w := mIntegrableCont A' Φv hΦv' w (smooth_continuous hws)
  have hG2 : IntegrableOn (fun y => w (ψ.symm y) * locDens A' Φv j0 y) ψ.target := by
    have h := hmiw j0 _ (by rw [hj0]; exact hKT) hKc
    rw [hj0] at h
    refine h.of_forall_sdiff_eq_zero ψ.open_target.measurableSet ?_
    rintro y ⟨hy, hyK⟩
    show w (ψ.symm y) * locDens A' Φv j0 y = 0
    rw [hDK y hy hyK, mul_zero]

  have hae : ∀ᵐ y ∂(volume.restrict ψ.target),
      Real.log ‖u (ψ.symm y) * ∏ i, y i ^ M i‖ * locDens A' Φv j0 y =
        ρ (ψ.symm y) * ℓ (ψ.symm y) * locDens A' Φv j0 y + w (ψ.symm y) * locDens A' Φv j0 y := by
    filter_upwards [ae_restrict_mem ψ.open_target.measurableSet,
      ae_restrict_of_ae ae_coord_ne_zero] with y hy hy0
    by_cases hp : ψ.symm y ∈ tsupport v
    · have hps : ψ.symm y ∈ ψ.source := hvs hp
      have hψp : ψ (ψ.symm y) = y := ψ.right_inv hy
      have hprod : ∏ i, y i ^ M i ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hy0 i)
      have hsx : s x (ψ.symm y) = u (ψ.symm y) * ∏ i, y i ^ M i := by rw [hsu _ hps, hψp]
      have hsx0 : s x (ψ.symm y) ≠ 0 := by rw [hsx]; exact mul_ne_zero (hu0 _ hps) hprod
      have hℓp : ℓ (ψ.symm y) = Real.log ‖s x (ψ.symm y)‖ - L.φ x (ψ.symm y) :=
        logNormSecLocal A L s x _ hs (hψL hps) hsx0
      have hwp : w (ψ.symm y) = L.φ x (ψ.symm y) :=
        hwL _ hps (by rw [hψp]; exact hKO ⟨_, hp, hψp⟩)
      rw [hρ1 _ hp, hℓp, hwp, hsx]
      ring
    · rw [hD0 y hy hp]
      ring
  have hsplit : ∫ y in ψ.target, ρ (ψ.symm y) * ℓ (ψ.symm y) * locDens A' Φv j0 y =
      (∫ y in ψ.target, Real.log ‖u (ψ.symm y) * ∏ i, y i ^ M i‖ * locDens A' Φv j0 y) -
        ∫ y in ψ.target, w (ψ.symm y) * locDens A' Φv j0 y := by
    have h := integral_congr_ae hae
    rw [integral_add hG1 hG2] at h
    rw [h]
    ring

  have hφ' : ∀ k, ContDiffOn ℝ ∞ ((Φ k).φ x ∘ ψ.symm) (ψ '' V) := by
    intro k
    refine (contDiffOn_compat hψ ((Φ k).isOpen_U x) ((hΦ k).1 x)).mono ?_
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨ψ.map_source (hVψ hp), by simpa [ψ.left_inv (hVψ hp)] using hVΦ k hp⟩
  have hu' : DifferentiableOn ℂ (u ∘ ψ.symm) (ψ '' V) := fun y hy =>
    (analyticAt_compat_fun hψ hu (hU'T hy) (ψ.map_target (hU'T hy))).differentiableAt.differentiableWithinAt
  have hu'0 : ∀ y ∈ ψ '' V, (u ∘ ψ.symm) y ≠ 0 := fun y hy => hu0 _ (ψ.map_target (hU'T hy))
  have hyp : PoincareLelongData (ψ '' V) (chartExt ψ v) (fun k => (Φ k).φ x ∘ ψ.symm) :=
    ⟨hU', hv'C.of_le (WithTop.coe_le_coe.2 le_top),
      hKc.of_isClosed_subset (isClosed_tsupport _) hv'K, hv'K.trans hKU, hφ'⟩
  obtain ⟨-, hPL⟩ := log_norm_integral_formula_snc e M (ψ '' V) (chartExt ψ v) _ (u ∘ ψ.symm) hyp hu' hu'0
  have hdens0 : ∀ y, y ∉ ψ '' tsupport v →
      densV (chartExt ψ v) (fun k => (Φ k).φ x ∘ ψ.symm) y = 0 := by
    intro y hy
    apply maDens_cons_eq_zero
    filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hy] with y' hy'
    exact image_eq_zero_of_notMem_tsupport fun h => hy' (hv'K h)
  have hDeq : ∀ y ∈ ψ.target,
      locDens A' Φv j0 y = densV (chartExt ψ v) (fun k => (Φ k).φ x ∘ ψ.symm) y := by
    intro y hy
    by_cases hyK : y ∈ ψ '' tsupport v
    · obtain ⟨p, hp, hpy⟩ := hyK
      have hps : p ∈ ψ.source := hvs hp
      have hsy : ψ.symm y = p := by rw [← hpy, ψ.left_inv hps]
      rw [locDensBase A' Φv hΦv' j0 y (by rw [hj0]; exact hy)
        (Fin.cons p (fun _ => x)) ?_]
      · unfold densV
        apply maDens_congr_germ
        intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · filter_upwards [ψ.open_target.mem_nhds hy] with y' hy'
          simp [hΦvd, hj0, chartExt, Set.indicator_of_mem hy', LocPot.ofFun]
        · filter_upwards with y'
          simp [hΦvd, hj0]
      · intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp [hΦvd, LocPot.ofFun]
        · simpa [hΦvd, hj0, hsy] using hVΦ k (hvV hp)
    · rw [hDK y hy hyK, hdens0 y hyK]
  have he : ∫ y in ψ.target, Real.log ‖u (ψ.symm y) * ∏ i, y i ^ M i‖ * locDens A' Φv j0 y =
      ∑ i, (M i : ℝ) * ∫ w, chartExt ψ v (hypInclAt i w) *
        densHypAt i (fun k => (Φ k).φ x ∘ ψ.symm) w := by
    rw [← hPL]
    calc _ = ∫ y in ψ.target, Real.log ‖(u ∘ ψ.symm) y * ∏ i, y i ^ M i‖ *
          densV (chartExt ψ v) (fun k => (Φ k).φ x ∘ ψ.symm) y :=
          setIntegral_congr_fun ψ.open_target.measurableSet (fun y hy => by
            simp only [Function.comp_apply]; rw [hDeq y hy])
      _ = _ := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
        have hyK : y ∉ ψ '' tsupport v := fun h => hy (hKT h)
        rw [hdens0 y hyK, mul_zero]

  have hΦw : ∀ i, IsPotential A ((Fin.cons (LocPot.ofFun w) Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact isPotential_ofFun A w hws
    · exact hΦ k
  have hΦL : ∀ i, IsPotential A ((Fin.cons L Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hL
    · exact hΦ k
  have hf1 : ∫ y in ψ.target, w (ψ.symm y) * locDens A' Φv j0 y = mInt A' Φv w := by
    unfold mInt
    rw [dite_eq_left hne, mIntLocalize A' hne.some Φv hΦv' j0 w (by rw [hj0]; exact hwsupp) hmiw, hj0]
  have hf2 : mInt A' Φv w = mInt A' (Fin.cons (LocPot.ofFun w) Φ) v := by
    let Φw : Fin (e + 1) → LocPot X := Fin.cons (LocPot.ofFun w) Φ
    let φ : Fin e → (Fin (e + 1) → ℂ) → ℝ := fun k => (Φ k).φ x ∘ ψ.symm
    have hv' := smoothOn_of_compatible hAA' isOpen_univ hv
    have hΦw' : ∀ i, IsPotential A' (Φw i) :=
      fun i => isPotential_of_compatible hAA' (hΦw i)
    have hmi := mIntegrableCont A' Φw hΦw' v (smooth_continuous hv')
    have hloc : mInt A' Φw v = ∫ y in ψ.target, v (ψ.symm y) * locDens A' Φw j0 y := by
      rw [mIntEq A' hne.some Φw hΦw' v hmi,
        mIntLocalize A' hne.some Φw hΦw' j0 v (by rw [hj0]; exact hvs) hmi, hj0]
    have hparts : ReciprocityTheory.AnForm.A.PartsHyp φ (chartExt ψ v) (w ∘ ψ.symm) (ψ '' V) :=
      ⟨hU', hyp.2.1.contDiffOn, hyp.2.2.1, hyp.2.2.2.1,
        ((contDiffOn_compat hψ isOpen_univ hws).mono fun y hy => ⟨hU'T hy, Set.mem_univ _⟩).of_le
          (WithTop.coe_le_coe.2 le_top),
        fun k => (hφ' k).of_le (WithTop.coe_le_coe.2 le_top)⟩
    have hsymm := (ReciprocityTheory.AnForm.A.parts_thm e φ (chartExt ψ v) (w ∘ ψ.symm)
      (ψ '' V) hparts).2.2.2.2
    rw [← hf1, show Fin.cons (LocPot.ofFun w) Φ = Φw from rfl, hloc]
    calc
      _ = ∫ y in ψ '' V, w (ψ.symm y) * locDens A' Φv j0 y := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero ψ.open_target.measurableSet hU'T ?_
        rintro y ⟨hy, hyV⟩
        rw [hDK y hy (fun hyK => hyV (hKU hyK)), mul_zero]
      _ = maInt (Fin.cons (chartExt ψ v) φ) (w ∘ ψ.symm) (ψ '' V) := by
        unfold maInt
        refine setIntegral_congr_fun hU'.measurableSet fun y hy => ?_
        exact congrArg (fun d => w (ψ.symm y) * d) (hDeq y (hU'T hy))
      _ = maInt (Fin.cons (w ∘ ψ.symm) φ) (chartExt ψ v) (ψ '' V) := hsymm
      _ = ∫ y in ψ '' V, v (ψ.symm y) * locDens A' Φw j0 y := by
        unfold maInt
        refine setIntegral_congr_fun hU'.measurableSet fun y hy => ?_
        have hyV : ψ.symm y ∈ V := by
          obtain ⟨p, hp, rfl⟩ := hy
          simpa only [ψ.left_inv (hVψ hp)] using hp
        have hbase : ∀ i, (A'.chart j0).symm y ∈ (Φw i).U x := by
          rw [hj0]
          intro i
          refine Fin.cases ?_ (fun k => ?_) i
          · exact Set.mem_univ _
          · exact hVΦ k hyV
        have hd := locDensBase A' Φw hΦw' j0 y (by rw [hj0]; exact hU'T hy) (fun _ => x) hbase
        rw [hj0] at hd
        have hφw : (fun i z => (Φw i).φ x (ψ.symm z)) = Fin.cons (w ∘ ψ.symm) φ := by
          funext i z
          refine Fin.cases ?_ (fun k => ?_) i <;> rfl
        simp only [chartExt, Set.indicator_of_mem (hU'T hy), Function.comp_apply]
        exact congrArg (fun d => v (ψ.symm y) * d)
          (hd.trans (congrArg (fun f => maDens f y) hφw)).symm
      _ = _ := by
        symm
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero ψ.open_target.measurableSet hU'T ?_
        rintro y ⟨hy, hyV⟩
        have h0 : v (ψ.symm y) = 0 := image_eq_zero_of_notMem_tsupport fun hp =>
          hyV ⟨_, hvV hp, ψ.right_inv hy⟩
        rw [h0, zero_mul]
  have hf3 : mInt A' (Fin.cons (LocPot.ofFun w) Φ) v = mInt A (Fin.cons (LocPot.ofFun w) Φ) v :=
    ((mIntAtlasIndep _ hΦw v (mIntegrableCont A _ hΦw v (smooth_continuous hv))).2).symm
  have hf4 : mInt A (Fin.cons (LocPot.ofFun w) Φ) v = mInt A (Fin.cons L Φ) v := by
    apply mInt_congr
    intro j y hy
    by_cases hp : v ((A.chart j).symm y) = 0
    · rw [hp, zero_mul, zero_mul]
    · apply congrArg (fun d : ℝ => v ((A.chart j).symm y) * d)
      have hpt : (A.chart j).symm y ∈ tsupport v := subset_tsupport _ hp
      have hps := hvs hpt
      let base : Fin (e + 1) → X := Fin.cons x (fun _ => (A.chart j).symm y)
      have hbase : ∀ i, (A.chart j).symm y ∈
          ((Fin.cons L Φ : Fin (e + 1) → LocPot X) i).U (base i) := by
        intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · exact hψL hps
        · exact (Φ k).mem_U _
      refine Eq.trans ?_ (locDensBase A (Fin.cons L Φ) hΦL j y hy base hbase).symm
      unfold locDens
      apply maDens_congr_germ
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · have hN : IsOpen (ψ.source ∩ ψ ⁻¹' O) :=
          ψ.continuousOn.isOpen_inter_preimage ψ.open_source hO
        have hpN : (A.chart j).symm y ∈ ψ.source ∩ ψ ⁻¹' O := ⟨hps, hKO ⟨_, hpt, rfl⟩⟩
        filter_upwards [((A.chart j).continuousOn_symm.isOpen_inter_preimage
          (A.chart j).open_target hN).mem_nhds ⟨hy, hpN⟩] with y' hy'
        exact hwL _ hy'.2.1 hy'.2.2
      · exact Eventually.of_forall fun _ => rfl
  rw [hAA'eq, hb, hc, hsplit, he, hf1, hf2, hf3, hf4]

end

end ReciprocityTheory.AnForm.M.PLAux
