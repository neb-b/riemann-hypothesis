module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameInnerDifferByRationalUnipotent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SlabMeasureSqueeze
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem slab_measure_squeeze : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε (maxK ε ∩ flagM ε W) E → (∀ i, (E i)ᴴ = -E i) → ∀ ν : Measure (Formalism.REAL.UJ ε), ν (maxK ε ∩ flagM ε W)ᶜ = 0 → (∀ l ∈ maxK ε ∩ flagM ε W, ν.map (fun g => g * l) = ν) → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η → ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, u * m * k ∈ hsBall ε r → ν (hsBall ε (r / (1 + η))) ≤ ν {l | l * k ∈ slab ε E ρ r} ∧ ν {l | l * k ∈ slab ε E ρ r} ≤ ν (hsBall ε ((1 + η) * r)) := by
  intro n ε a j W hW d E hcut hskew ν hν hinv ρ η hρ hρ8 hη
  set S := maxK ε ∩ flagM ε W with hS
  obtain ⟨t, ht, hsq⟩ := _root_.GlobalTheory.IwConst.slab_squeeze n ε S d E hcut ρ η hρ hρ8 hη
  obtain ⟨r0, hr0, hnear⟩ := _root_.GlobalTheory.IwConst.CloseLevi.close_levi n ε a j W hW t ht
  have hmem : Set.Iio (min t r0) ∈ nhds (0 : ℝ) := Iio_mem_nhds (lt_min ht hr0)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with r hr hr' u hu m hm k hk hball
  have hrpos : (0 : ℝ) < r := hr
  have hrlt : r < min t r0 := hr'
  have hrt : r < t := lt_of_lt_of_le hrlt (min_le_left _ _)
  have hrr0 : r < r0 := lt_of_lt_of_le hrlt (min_le_right _ _)

  have hb : nrm (uMat (u * m * k) - 1) ≤ r := hball
  obtain ⟨l0, hl0S, hl0⟩ := hnear u hu m hm k hk (le_trans hb hrr0.le)

  obtain ⟨l1, hl1S, hcrd, hmin⟩ := _root_.GlobalTheory.IwConstMin.exists_nearest n ε S d E hcut (fun x hx => hx.1) hskew k hk
  have hnrm : nrm (uMat (l1 * k) - 1) < t := lt_of_le_of_lt (hmin l0 hl0S) hl0
  have key := fun l (hl : l ∈ S) => hsq r hrpos hrt (l1 * k) hnrm hcrd l hl

  have hA : ν {l | l * k ∈ slab ε E ρ r} = ν {l | l * (l1 * k) ∈ slab ε E ρ r} := by
    calc ν {l | l * k ∈ slab ε E ρ r}
        = (ν.map (fun g => g * l1)) {l | l * k ∈ slab ε E ρ r} := by rw [hinv l1 hl1S]
      _ = ν ((fun g => g * l1) ⁻¹' {l | l * k ∈ slab ε E ρ r}) :=
          (Homeomorph.mulRight l1).toMeasurableEquiv.map_apply _
      _ = ν {l | l * (l1 * k) ∈ slab ε E ρ r} := by
          congr 1
          ext l
          simp only [Set.mem_preimage, Set.mem_setOf_eq, mul_assoc]
  rw [hA]
  constructor
  · calc ν (hsBall ε (r / (1 + η)))
        ≤ ν (hsBall ε (r / (1 + η)) ∩ S ∪ Sᶜ) := by
          apply measure_mono
          intro l hl
          by_cases h : l ∈ S
          · exact Or.inl ⟨hl, h⟩
          · exact Or.inr h
      _ ≤ ν (hsBall ε (r / (1 + η)) ∩ S) + ν Sᶜ := measure_union_le _ _
      _ = ν (hsBall ε (r / (1 + η)) ∩ S) := by rw [hν, add_zero]
      _ ≤ ν {l | l * (l1 * k) ∈ slab ε E ρ r} :=
          measure_mono (fun l hl => (key l hl.2).1 hl.1)
  · calc ν {l | l * (l1 * k) ∈ slab ε E ρ r}
        ≤ ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S ∪ Sᶜ) := by
          apply measure_mono
          intro l hl
          by_cases h : l ∈ S
          · exact Or.inl ⟨hl, h⟩
          · exact Or.inr h
      _ ≤ ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S) + ν Sᶜ := measure_union_le _ _
      _ = ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S) := by rw [hν, add_zero]
      _ ≤ ν (hsBall ε ((1 + η) * r)) :=
          measure_mono (fun l hl => (key l hl.2).2 hl.1)

end GlobalTheory.IwConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepBound
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DeepStep

theorem step_bound (B : RowsAut) (b ρ M : ℝ) (P : ℕ) (D : ℕ)
    (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA)
    (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (hg : 1 ≤ B.g) (hW : B.I.IsIsot W)
    (hcov : ∀ ν : B.I.Ginf, ((ν, 1) : B.I.GA) ∈ B.I.NA W → ∃ γ ∈ B.I.GFset, ∃ k ∈ B.I.Kg B.g,
      ∃ y ∈ omega B.I x W ρ, ((ν, 1) : B.I.GA) * x = γ * y * (1, k))
    (hS : StepBoundAt B b P) (hR : ∀ i, IsReps B (T i) (Fr i))
    (hC : ∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) (hM : 0 ≤ M)
    (hb : ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B (P + 1), ‖vv B Fr u y‖ ≤ M * ‖u‖) :
    ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P,
      ‖vv B Fr u y‖ ≤ 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
  intro y hy u hu
  have hvv : ∀ z : B.I.GA, ‖vv B Fr u z‖ = Real.sqrt (∑ i, ‖Fr i u z‖ ^ 2) := by
    intro z
    simp [vv, EuclideanSpace.norm_eq]
  have hvvs : ∀ z : B.I.GA, ‖vv B Fr u z - vv B Fr u x‖ = Real.sqrt (∑ i, ‖Fr i u z - Fr i u x‖ ^ 2) := by
    intro z
    simp [vv, EuclideanSpace.norm_eq]
  have hnear := _root_.GlobalTheory.PathVar.path_variation B b ρ M P D T Fr x W hS hR hM hb
  have hcusp := _root_.GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  obtain ⟨L, hL, -, -, hLf⟩ := hcusp
  have hrep : ∀ i, GlobalTheory.Dec.IsContRep B (T i u) (Fr i u) := fun i => (hR i P u hu).1
  have hx : ‖vv B Fr u x‖ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
    rw [hvv]
    refine GlobalTheory.MeanZero.norm_le_of_cusp B.I B.μf B.g W D (fun i => Fr i u) x (fun i => Fr i u x) _ hg hW ?_ ?_
    · intro i
      obtain ⟨hc, hl, hae⟩ := hrep i
      refine ⟨hc, hl, (hR i P u hu).2.1, ?_⟩
      have h1 := ((_root_.GlobalTheory.ContRepUniq.contRep_unique_linear B).2.2.2 _ _ (hrep i)).1
      exact (hLf (T i u) (Fr i u) hl hc h1).1 ((hL _).2 (hC i u))
    · intro ν hν
      obtain ⟨γ, hγ, k, hk, z, hz, he⟩ := hcov ν hν
      have hval : ∀ i, Fr i u (((ν, 1) : B.I.GA) * x) = Fr i u z := by
        intro i
        rw [he, (hR i P u hu).2.1 k hk, (hrep i).2.1 γ hγ]
      simp only [hval]
      rw [← hvvs]
      exact hnear z hz u hu
  calc ‖vv B Fr u y‖ = ‖(vv B Fr u y - vv B Fr u x) + vv B Fr u x‖ := by rw [sub_add_cancel]
    _ ≤ ‖vv B Fr u y - vv B Fr u x‖ + ‖vv B Fr u x‖ := norm_add_le _ _
    _ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ + ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ :=
        add_le_add (hnear y hy u hu) hx
    _ = 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by ring

end GlobalTheory.DeepStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdGaugeMeasuresGaugeBody
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConstBox

theorem local_vag {n d : ℕ} {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (h : IsCut ε S E) (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub S d μ) :
    SigmaFinite μ ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      IsFiniteMeasure (μ.restrict {g | nrm (uMat g - 1) < t}) ∧
      Vag (μ.restrict {g | nrm (uMat g - 1) < t}) (fun g => crd E (uMat g - 1)) volume d := by
  obtain ⟨A, hA, hON, hspan, rfl⟩ := h
  obtain ⟨hσ, hcpt, -, r₀, hr₀, hlim⟩ := GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hON hspan μ hμ
  refine ⟨hσ, Real.sqrt r₀, Real.sqrt_pos.2 hr₀, fun t ht htt => ⟨?_, ?_⟩⟩
  ·
    refine isFiniteMeasure_restrict.2 (ne_of_lt ?_)
    refine lt_of_le_of_lt (measure_mono ?_) (isCompact_hsBall ε t).measure_lt_top
    intro g hg
    exact (show nrm (uMat g - 1) < t from hg).le
  ·
    intro φ hφ hsupp
    have hset : {g : Formalism.REAL.UJ ε | nrm (uMat g - 1) < t} =
        {g | Formalism.REAL.hs (uMat g - 1) < t ^ 2} := by
      ext g
      exact Real.sqrt_lt' ht
    have h1 : 0 < t ^ 2 := by positivity
    have h2 : t ^ 2 ≤ r₀ := by
      calc t ^ 2 ≤ Real.sqrt r₀ ^ 2 := pow_le_pow_left₀ ht.le htt 2
        _ = r₀ := Real.sq_sqrt hr₀.le
    rw [hset]
    refine (hlim (t ^ 2) h1 h2 φ hφ hsupp).congr (fun r => ?_)
    congr 2
    funext g
    congr 1
    ext i
    simp [crd, div_eq_mul_inv, mul_comm]

theorem prod_gauge_body : ∀ (n : ℕ) (ε : Fin n → Bool) (SN SM MainNotions : Set (Formalism.REAL.UJ ε)), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε SN EN → IsCut ε SM EM → IsCut ε MainNotions EK → (∀ v, gau EN EM EK EL v = 0 → v = 0) → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub SN dN μN → IsGaugeSub SM dM μM → IsGaugeSub MainNotions dK μK → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → Filter.Tendsto (fun r : ℝ => (μN.prod (μM.prod μK)) {x | (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧ gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ r} / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  intro n ε SN SM MainNotions dN dM dK dL EN EM EK EL hN hM hK hgau μN μM μK hμN hμM hμK
  obtain ⟨hσN, tN, htN, hN'⟩ := local_vag hN μN hμN
  obtain ⟨hσM, tM, htM, hM'⟩ := local_vag hM μM hμM
  obtain ⟨hσK, tK, htK, hK'⟩ := local_vag hK μK hμK
  refine ⟨min tN (min tM tK), lt_min htN (lt_min htM htK), fun t ht htt => ?_⟩
  obtain ⟨fN, vN⟩ := hN' t ht (htt.trans (min_le_left _ _))
  obtain ⟨fM, vM⟩ := hM' t ht (htt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨fK, vK⟩ := hK' t ht (htt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  set s : Set (Formalism.REAL.UJ ε) := {g | nrm (uMat g - 1) < t} with hs
  have hsm : MeasurableSet s := (continuous_nrm_uMat ε).measurable measurableSet_Iio
  have mc : ∀ {e : ℕ} (E : Fin e → Matrix (Fin n) (Fin n) ℂ),
      Measurable fun g : Formalism.REAL.UJ ε => crd E (uMat g - 1) :=
    fun E => (continuous_crd_uMat ε E).measurable

  have vMK := GlobalTheory.T.vague_limit_rescaled_measures_prod _ _ _ _ (μM.restrict s) (μK.restrict s) (fun g => crd EM (uMat g - 1))
    (fun g => crd EK (uMat g - 1)) volume volume dM dK (mc EM) (mc EK) vM vK
  have vNMK := GlobalTheory.T.vague_limit_rescaled_measures_prod _ _ _ _ (μN.restrict s) ((μM.restrict s).prod (μK.restrict s))
    (fun g => crd EN (uMat g - 1)) (Prod.map (fun g => crd EM (uMat g - 1)) (fun g => crd EK (uMat g - 1)))
    volume (volume.prod volume) dN (dM + dK) (mc EN) (Measurable.prodMap (mc EM) (mc EK)) vN vMK
  have h2 : (volume.prod volume : Measure ((Fin dM → ℝ) × (Fin dK → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have h3 : (volume.prod (volume.prod volume) :
      Measure ((Fin dN → ℝ) × (Fin dM → ℝ) × (Fin dK → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have key := _root_.GlobalTheory.IwConst.VagBody.tendsto_body _ _ ((μN.restrict s).prod ((μM.restrict s).prod (μK.restrict s)))
    (Prod.map (fun g => crd EN (uMat g - 1))
      (Prod.map (fun g => crd EM (uMat g - 1)) (fun g => crd EK (uMat g - 1))))
    (volume.prod (volume.prod volume)) (dN + (dM + dK)) (gau EN EM EK EL)
    (Measurable.prodMap (mc EN) (Measurable.prodMap (mc EM) (mc EK))) (continuous_gau EN EM EK EL)
    (gau_nonneg EN EM EK EL) (fun c hc v => gau_smul EN EM EK EL c hc v) hgau vNMK
  refine key.congr (fun r => ?_)
  congr 1
  rw [Measure.prod_restrict, Measure.prod_restrict,
    Measure.restrict_apply' (hsm.prod (hsm.prod hsm))]
  congr 1
  ext ⟨a, b, c⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod, Prod.map_apply, hs]
  tauto

end GlobalTheory.IwConstBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsSameRationalInnerClassAreTranslates
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.CntC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gmap_mul (a b : GV D) (M : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem gmap_one (M : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) M = M := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem gmap_inv_of {a : GV D} {M N : LV D} (h : Formalism.HermitianLatticesTheory.gmap a M = N) : Formalism.HermitianLatticesTheory.gmap a⁻¹ N = M := by
  rw [← h, ← gmap_mul, inv_mul_cancel, gmap_one]

theorem adapt_mul {T : D.host.E} {F G H : LFlag (D.sp.Y 0) D.R.rS T} {g g' : GV D} (hg : Adapt g F G)
    (hg' : Adapt g' G H) : Adapt (g' * g) F H := by
  refine ⟨mul_mem hg'.1 hg.1, fun a => ?_⟩
  have hmap := (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D T G H g' hg').1 a.val
  have h1 : g' (g (frame F a) - frame G a) ∈ Xflag H a.val := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem (hg.2 a)
  have h2 := hg'.2 a
  have e : (g' * g) (frame F a) - frame H a =
      g' (g (frame F a) - frame G a) + (g' (frame G a) - frame H a) := by
    rw [map_sub, LinearEquiv.mul_apply]
    abel
  rw [e]
  exact add_mem h1 h2

theorem adapt_fix {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {h : GV D} (hi : h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hf : ∀ a, h (frame F a) = frame F a) : Adapt h F F := by
  refine ⟨hi, fun a => ?_⟩
  rw [hf a, sub_self]
  exact zero_mem _

theorem frame_mapLF {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {γ : GV D} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (a : Fin (D.R.rS + 1)) : frame (mapLF γ F) a = γ (frame F a) := by
  simp only [frame, mapLF, dif_pos hγ, Formalism.MainNotions.S.FlagG.fvec]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Fin.snoc_last]
    rfl
  · simp only [Fin.snoc_castSucc]
    rfl

theorem xsp_mapLF {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {γ : GV D} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    Xsp (mapLF γ F) = (Xsp F).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  simp only [Xsp, mapLF, dif_pos hγ, Formalism.MainNotions.S.FlagG.X, Submodule.map_span, ← Set.range_comp]
  rfl

theorem adapt_mapLF {T : D.host.E} {F G : LFlag (D.sp.Y 0) D.R.rS T} {γ g : GV D}
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) : Adapt g (mapLF γ F) G ↔ Adapt (g * γ) F G := by
  simp only [Adapt, frame_mapLF F hγ, LinearEquiv.mul_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨mul_mem h1 hγ, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := mul_mem h1 (inv_mem hγ)
    rwa [mul_inv_cancel_right] at this

end GlobalTheory.Unfold.CntC

namespace GlobalTheory.Unfold.CntC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem translates : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ t : TauC Y u u') (Λ₀ Λ₁ : LV D), TG F F' t₀ Λ₀ → TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → t.lam = t₀.lam ∧ t.lam' = t₀.lam' ∧ ∃ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam, ∃ a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam', KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t₀.lam (a * t₀.lin * a'⁻¹) t.lin := by
  intro D X Y u u' F F' w _ _ t₀ t Λ₀ Λ₁ h₀ h₁ hR
  obtain ⟨g₀, hg₀a, hg₀b, rfl⟩ := h₀
  obtain ⟨ψ₁, hψ₁a, hψ₁b, rfl⟩ := h₁
  obtain ⟨h, ⟨hhi, hhF, hhF'⟩, hgd⟩ := hR
  rw [← gmap_mul] at hgd
  set ψ₀ := h * g₀ with hψ₀
  have hψ₀a : Adapt ψ₀ (lf D (X.Fu u)) F := adapt_mul hg₀a (adapt_fix hhi hhF)
  have hψ₀b : Adapt ψ₀ t₀.frame F' := adapt_mul hg₀b (adapt_fix hhi hhF')
  have li₀ : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have lg₀ : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have li : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have lg : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have e1 : Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam) F = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ t.lam) F := congrArg Prod.fst hgd
  have e2 : Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam) F' = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ t.lam) F' :=
    congrArg (fun x => x.2.1) hgd
  have e3 : (gdat F F' (Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam)).2.2 = (gdat F F' (Formalism.HermitianLatticesTheory.gmap ψ₁ t.lam)).2.2 :=
    congrArg (fun x => x.2.2) hgd
  obtain ⟨hlam, n, hn, hA⟩ := _root_.GlobalTheory.Unfold.SideEq.side D X Y u F ψ₀ ψ₁ t₀.lam t.lam t₀.mem t.mem hψ₀a hψ₁a e1
  have hψ₀b' : Adapt (ψ₀ * t₀.lin) (lf D (X.Fu u')) F' :=
    (adapt_mapLF (F := lf D (X.Fu u')) (G := F') (g := ψ₀) li₀).1 hψ₀b
  have hψ₁b' : Adapt (ψ₁ * t.lin) (lf D (X.Fu u')) F' :=
    (adapt_mapLF (F := lf D (X.Fu u')) (G := F') (g := ψ₁) li).1 hψ₁b
  have q₀ : Formalism.HermitianLatticesTheory.gmap (ψ₀ * t₀.lin) t₀.lam' = Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam :=
    (gmap_mul ψ₀ t₀.lin t₀.lam').trans (congrArg (Formalism.HermitianLatticesTheory.gmap ψ₀) lg₀)
  have q₁ : Formalism.HermitianLatticesTheory.gmap (ψ₁ * t.lin) t.lam' = Formalism.HermitianLatticesTheory.gmap ψ₁ t.lam :=
    (gmap_mul ψ₁ t.lin t.lam').trans (congrArg (Formalism.HermitianLatticesTheory.gmap ψ₁) lg)
  have e2' : Lsub (Formalism.HermitianLatticesTheory.gmap (ψ₀ * t₀.lin) t₀.lam') F' = Lsub (Formalism.HermitianLatticesTheory.gmap (ψ₁ * t.lin) t.lam') F' := by
    rw [q₀, q₁]
    exact e2
  obtain ⟨hlam', n', hn', hA'⟩ :=
    _root_.GlobalTheory.Unfold.SideEq.side D X Y u' F' (ψ₀ * t₀.lin) (ψ₁ * t.lin) t₀.lam' t.lam' t₀.mem' t.mem' hψ₀b' hψ₁b' e2'
  refine ⟨hlam, hlam', n * (ψ₁⁻¹ * ψ₀), hA, n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin)), hA', ?_⟩
  have hA2 : Formalism.HermitianLatticesTheory.gmap (n * (ψ₁⁻¹ * ψ₀)) t₀.lam = t₀.lam := hA.2
  have hA'2 : Formalism.HermitianLatticesTheory.gmap (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) t₀.lam' = t₀.lam' := hA'.2
  have hγ : n * (ψ₁⁻¹ * ψ₀) * t₀.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin)))⁻¹ = n * t.lin * n'⁻¹ := by
    group
  have hβ : t.lin * (n * t.lin * n'⁻¹)⁻¹ =
      t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹ * (n * (ψ₁⁻¹ * ψ₀))⁻¹ := by
    group
  rw [hγ]
  have hnN := _root_.GlobalTheory.NRatInv.adapt_and_inv_mem D _ _ n hn
  have hn'N := _root_.GlobalTheory.NRatInv.adapt_and_inv_mem D _ _ n' hn'
  have hn'iN := _root_.GlobalTheory.NRatInv.adapt_and_inv_mem D _ _ n'⁻¹ hn'N.2
  have hni : n⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hnN.2.1
  have hn'i : n'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn'N.2.1
  have hni' : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn.1
  have hγi : n * t.lin * n'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (mul_mem hni' li) hn'i
  unfold KeyEq
  refine ⟨⟨n⁻¹, hnN.2, n', hn', by group⟩, ?_⟩
  have hΨ₀a : Adapt (ψ₁ * n⁻¹) (lf D (X.Fu u)) F := adapt_mul (_root_.GlobalTheory.NRatInv.adapt_and_inv_mem D _ _ n⁻¹ hnN.2).1 hψ₁a
  have hΨ₀b : Adapt (ψ₁ * n⁻¹) (mapLF (n * t.lin * n'⁻¹) (lf D (X.Fu u'))) F' := by
    refine (adapt_mapLF (F := lf D (X.Fu u')) (G := F') (g := ψ₁ * n⁻¹) hγi).2 ?_
    have : ψ₁ * n⁻¹ * (n * t.lin * n'⁻¹) = ψ₁ * t.lin * n'⁻¹ := by group
    have key := adapt_mul hn'iN.1 hψ₁b'
    rw [← this] at key
    exact key
  have hg1 : Formalism.HermitianLatticesTheory.gmap (ψ₁ * n⁻¹) t₀.lam = Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam := by
    have : ψ₁ * n⁻¹ = ψ₀ * (n * (ψ₁⁻¹ * ψ₀))⁻¹ := by group
    rw [this, gmap_mul, gmap_inv_of hA2]
  refine _root_.GlobalTheory.iotaCompat_of_graph_eq D _ _ (lf D (X.Fu u)) F (mapLF (n * t.lin * n'⁻¹) (lf D (X.Fu u')))
    (mapLF t.lin (lf D (X.Fu u'))) F' t₀.lam (ψ₁ * n⁻¹) ψ₁ (t.lin * (n * t.lin * n'⁻¹)⁻¹)
    (mul_mem hψ₁a.1 hni) hψ₁a.1 (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D _ _ _ _ hΨ₀a).2 (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D _ _ _ _ hψ₁a).2
    (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D _ _ _ _ hΨ₀b).2 (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D _ (mapLF t.lin (lf D (X.Fu u'))) F' ψ₁ hψ₁b).2
    ?_ (mul_mem li (inv_mem hγi)) ?_ ?_ ?_ ?_
  · exact (congrArg (fun Λ => (gdat F F' Λ).2.2) hg1).trans
      (e3.trans (congrArg (fun Λ => (gdat F F' (Formalism.HermitianLatticesTheory.gmap ψ₁ Λ)).2.2) hlam))
  · calc Formalism.HermitianLatticesTheory.gmap (t.lin * (n * t.lin * n'⁻¹)⁻¹) t₀.lam
          = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹ * (n * (ψ₁⁻¹ * ψ₀))⁻¹) t₀.lam :=
            congrArg (fun g => Formalism.HermitianLatticesTheory.gmap g t₀.lam) hβ
      _ = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹) (Formalism.HermitianLatticesTheory.gmap (n * (ψ₁⁻¹ * ψ₀))⁻¹ t₀.lam) := gmap_mul _ _ _
      _ = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹) t₀.lam :=
            congrArg (Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹)) (gmap_inv_of hA2)
      _ = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin)))) (Formalism.HermitianLatticesTheory.gmap t₀.lin⁻¹ t₀.lam) := gmap_mul _ _ _
      _ = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin)))) t₀.lam' :=
            congrArg (Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))))) (gmap_inv_of lg₀)
      _ = Formalism.HermitianLatticesTheory.gmap t.lin (Formalism.HermitianLatticesTheory.gmap (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) t₀.lam') := gmap_mul _ _ _
      _ = Formalism.HermitianLatticesTheory.gmap t.lin t₀.lam' := congrArg (Formalism.HermitianLatticesTheory.gmap t.lin) hA'2
      _ = t₀.lam := (congrArg (Formalism.HermitianLatticesTheory.gmap t.lin) hlam'.symm).trans (lg.trans hlam)
  · rw [xsp_mapLF _ hγi, xsp_mapLF _ li, ← Submodule.map_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    exact congrArg (fun g : GV D => g x) (inv_mul_cancel_right t.lin (n * t.lin * n'⁻¹))
  · intro l hl
    have : ψ₁⁻¹ * (ψ₁ * n⁻¹) = n⁻¹ := by group
    have key := hnN.2.2.2 l (Submodule.mem_inf.mp hl).2
    rw [← this] at key
    exact key
  · intro x' hx'
    have : ψ₁⁻¹ * (ψ₁ * n⁻¹) = n⁻¹ := by group
    have key := _root_.GlobalTheory.UnipRight.unip_right D _ (lf D (X.Fu u')) (n * t.lin * n'⁻¹) t.lin n⁻¹ n' hγi hni hn' (by group) x'
      (Submodule.mem_inf.mp hx').2
    rw [← this] at key
    exact key

end GlobalTheory.Unfold.CntC
end
end

