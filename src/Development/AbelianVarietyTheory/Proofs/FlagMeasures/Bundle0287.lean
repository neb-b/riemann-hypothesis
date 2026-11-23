module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LsubGmapOfMapXspEq
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

private theorem orth_map_isom_eq_map_orth (D : D7) (φ : GV D) (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (U : Submodule D.host.E (VS D).V) :
    Formalism.MainNotions.S.Lat.orth (VS D) (U.map (φ : (VS D).V →ₗ[D.host.E] (VS D).V)) =
      (Formalism.MainNotions.S.Lat.orth (VS D) U).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  have hi : ∀ x y, (VS D).hT (φ x) (φ y) = (VS D).hT x y := hφ
  ext v
  simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hv
    refine (Submodule.mem_map).2 ⟨φ.symm v, ?_, by simp⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    have h1 := hv (φ x) (Submodule.mem_map_of_mem hx)
    rw [← hi x (φ.symm v)]
    simpa using h1
  · intro hv x hx
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_map).1 hv
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_map).1 hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hw
    simp only [LinearEquiv.coe_coe]
    rw [hi]
    exact hw y hy

private theorem toO_map_eq_toO_map (D : D7) (φ : GV D) (U : Submodule D.host.E (VS D).V) :
    (Formalism.MainNotions.S.Lat.toO (VS D) U).map
              ((φ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) =
      Formalism.MainNotions.S.Lat.toO (VS D) (U.map (φ : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
  ext v
  simp only [Formalism.MainNotions.S.Lat.toO, Submodule.mem_map, Submodule.restrictScalars_mem,
    LinearMap.coe_restrictScalars]

theorem lsub_gmap_of_map_Xsp_eq :
    ∀ (D : D7) (T : D.host.E) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T) (φ : GV D) (M : LV D),
      φ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (Xsp F₁).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F₂ →
      Lsub (Formalism.HermitianLatticesTheory.gmap φ M) F₂ = Formalism.HermitianLatticesTheory.gmap φ (Lsub M F₁) := by
  intro D T F₁ F₂ φ M hφ hX
  have hinj : Function.Injective
      ((φ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) := φ.injective
  unfold Formalism.MainNotions.S.Lat.Lsub Formalism.MainNotions.S.Lat.Lrep Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_inf _ hinj, Submodule.map_sup, Submodule.map_inf _ hinj,
    toO_map_eq_toO_map, toO_map_eq_toO_map, ← orth_map_isom_eq_map_orth D φ hφ, hX]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypes
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomProdPart

theorem product_moment_first : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (m : ℕ) (hm : m ≤ r + 1) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (lb ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin m, lenA k r z (Matrix.of x) (Fin.castLE hm a) ^ 2) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ m) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS m hm ν hν hnz
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  obtain ⟨Q, hQ⟩ := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).1 hk
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hDS := hFam ν hν0
  obtain ⟨w, hw1, -, hwK, hwF⟩ := GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries hK k r _ _ (R ν) hDS Q (E ν) hQ (hE ν hν0).1
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hk hDS Q (E ν) hQ (hE ν hν0).1
  have hLev := GlobalTheory.lev_zero_of_kHighest _ _ _ (E ν) _ w hMod.1 hMod.2.1 hwK hwF
  have hw1' : ‖(w : (R ν).H)‖ = 1 := hw1
  have hwsm : (w : (R ν).H) ∈ (R ν).sm := w.2
  refine ⟨(w : (R ν).H), hwsm, hw1', ?_⟩
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  obtain ⟨⟨hb1, hb2, -, -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hq2 : ∀ q ≤ (r + 1) ^ 2, 0 + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 := by
    intro q hq
    have : (r + 1) ^ 2 ≤ (2 * r + k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hb : (1 : ℝ) ≤ b := by linarith
  have hA : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have : 0 ≤ bv := by linarith
    positivity
  have hmain := _root_.GlobalTheory.MomentHolder.initial_product_moment_le (Formalism.QuantumDeterminants.Mt k r) νq r m hm (fun a x => lenA k r z (Matrix.of x) a)
    (fun x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)
    (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2)
    hlen
    (fun a => hG.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.1 a)
    (((hmeas (l ν) hBeL.1 w hwsm).norm.aemeasurable.pow_const 2).const_mul _)
    (fun x => mul_nonneg hdg.le (by positivity))
    (by
      have := ((GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν0).2 hnz).2 w hwsm
      simpa only [one_mul, hw1', one_pow, ENNReal.ofReal_one] using this)
    hA (one_le_pow₀ hb)
    (fun q hq => by
      have := GlobalTheory.T.family_setup_cayley_recursion hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q ν
        (by omega) 0 (hq2 q hq) w hLev
      simpa only [hw1, one_pow, mul_one] using this)
    (fun a q hq => by
      have := GlobalTheory.T.family_setup_cayley_bound hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν0
        0 q (hq2 q hq) a w hLev
      simpa only [hw1, one_pow, mul_one] using this)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  exact pow_le_pow_left₀ (mul_nonneg hA (by positivity))
    (_root_.GlobalTheory.MomNum.mom_num k r lam u b bv ga h q0 _ hNum hT) _

end GlobalTheory.MomProdPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassLowTypesFirst
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowTypeMass

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

variable {k r : ℕ}


open scoped Classical in
theorem lintegral_rmul_of_measurable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hS : SideG k r z π u μW μN μG νq) (F : Mx k r → ℝ≥0∞)
    (hF : Measurable ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}.piecewise
      (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)))
    (hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x)
    {g : Mx k r} (hg : g ∈ GG k r) :
    ∫⁻ x, F (Matrix.of x * g) ∂νq = ∫⁻ x, F (Matrix.of x) ∂νq := by
  classical
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x = F (Matrix.of x) :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ hF (fun s hs x hx => by
    rw [hval x hx]
    exact (hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)).trans (hinv s hs _ hx)) g hg
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => hval x hx)))
  exact (hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)).symm

theorem norm_sq_sqrt_scaled {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {t d : ℝ} (ht : 0 ≤ t)
    (hd : 0 ≤ d) (v : Wp) : ‖((Real.sqrt t * Real.sqrt d : ℝ) : ℂ) • v‖ ^ 2 = t * (d * ‖v‖ ^ 2) := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hd]
  ring


open scoped Classical in
theorem measurable_piecewise_mass {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (φ : (Fin (r + 1) → ℝ) → ℝ) (hφm : Measurable φ) (d : ℝ) (B : Mx k r → Wp) (hB : ContinuousOn B (GG k r)) :
    Measurable ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}.piecewise
      (fun x : Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
        ENNReal.ofReal (d * ‖B (Matrix.of x)‖ ^ 2)) (fun _ => 0)) := by
  classical
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    convert this using 1
    ext x
    simp [hA]
  have hL : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) A :=
    continuousOn_pi.2 fun a => GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a
  have hLm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a)
      (fun _ => (0 : Fin (r + 1) → ℝ))) :=
    hL.measurable_piecewise continuousOn_const hAm
  have hBc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) A :=
    continuousOn_const.mul (hB.norm.pow 2)
  have hBm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) (fun _ => (0 : ℝ))) :=
    hBc.measurable_piecewise continuousOn_const hAm
  have heq : A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
        ENNReal.ofReal (d * ‖B (Matrix.of x)‖ ^ 2)) (fun _ => 0) =
      A.indicator (fun x => ENNReal.ofReal (φ (A.piecewise
        (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) (fun _ => (0 : Fin (r + 1) → ℝ)) x)) *
        ENNReal.ofReal (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) (fun _ => (0 : ℝ)) x)) := by
    funext x
    by_cases hx : x ∈ A
    · simp [Set.piecewise, Set.indicator, hx]
    · simp [Set.piecewise, Set.indicator, hx]
  rw [heq]
  exact ((ENNReal.measurable_ofReal.comp (hφm.comp hLm)).mul (ENNReal.measurable_ofReal.comp hBm)).indicator hAm

end prelim

section main

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

end main

end GlobalTheory.LowTypeMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetTransportedRealPointsImage
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom

theorem measPolish_UJ (n : ℕ) (ε : Fin n → Bool) : PolishSpace (Formalism.REAL.UJ ε) := by
  haveI : PolishSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (PolishSpace (Fin n → Fin n → ℂ))
  exact (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.polishSpace

variable {D : D7}

theorem measCont_trX (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) : Continuous (trX X C) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun x : X.B.I.Ginf => C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  exact (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply _)

theorem measInj_trX (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) : Function.Injective (trX X C) := by
  intro x y h
  funext v
  obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, by simp [vOf]⟩
  have h2 : C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ =
      C.Qi τ * Formalism.MainNotions.S.uMat (y (vOf X τ)) * C.Q τ := congrFun h τ
  obtain ⟨-, h1, -⟩ := C.isT τ
  have h3 := congrArg (fun M => C.Q τ * M * C.Qi τ) h2
  simp only [Matrix.mul_assoc, h1, Matrix.mul_one] at h3
  simp only [← Matrix.mul_assoc, h1, Matrix.one_mul] at h3
  exact Subtype.ext (Units.ext h3)

theorem measTauOf_mk (D : D7) (τ : D.what₂.Tau) : tauOf D (InfinitePlace.mk (embS D τ)) = τ :=
  (GlobalTheory.RealPlaces.existsUnique_place D _).unique
    (GlobalTheory.RealPlaces.existsUnique_place D _).exists.choose_spec rfl

theorem measInj_cjw (D : D7) (w : InfinitePlace D.host.E) : Function.Injective (cjw D w) := by
  intro M N h
  by_cases hw : Direct D w
  · simpa [cjw, hw] using h
  · simp only [cjw, hw, if_false] at h
    funext i j
    simpa using congrArg star (congrFun (congrFun h i) j)

theorem measCont_Gm (D : D7) : Continuous (Gm D) := by
  refine continuous_pi fun w => ?_
  by_cases hw : Direct D w
  · simp only [Gm, cjw, hw, if_true]
    exact continuous_apply _
  · simp only [Gm, cjw, hw, if_false]
    exact continuous_pi fun i => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply j).comp ((continuous_apply i).comp (continuous_apply _)))

theorem measInj_Gm (D : D7) : Function.Injective (Gm D) := by
  intro y z h
  funext τ
  have := congrFun h (InfinitePlace.mk (embS D τ))
  simp only [Gm, measTauOf_mk] at this
  exact measInj_cjw D _ this

theorem measurableSet_Gm_trX_image : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (S : Set X.B.I.Ginf),
    MeasurableSet S → MeasurableSet (Gm D '' (trX X C '' S)) := by
  intro D X θ C S hS
  haveI : ∀ v, PolishSpace (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => measPolish_UJ _ _
  rw [Set.image_image]
  exact hS.image_of_continuousOn_injOn ((measCont_Gm D).comp (measCont_trX X C)).continuousOn
    ((measInj_Gm D).comp (measInj_trX X C)).injOn

end GlobalTheory.CovDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureEqOfStrictFundamentalSetsPlacewise
section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FundEq

open GlobalTheory.DegVol

theorem measurable_mulP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) :
    Measurable (fun x : ι → Formalism.QuantumDeterminants.Mt k r => mulP m x) :=
  Measurable.of_eval fun v => (GlobalTheory.DegVol.Cov.continuous_lmulM _).measurable.comp (measurable_pi_apply v)

theorem measure_eq_tsum {ι : Type} {k r : ℕ} (μ : Measure (ι → Formalism.QuantumDeterminants.Mt k r))
    (R Γ Ω S : Set (ι → Formalism.QuantumDeterminants.Mt k r)) [Countable Γ] (hR : μ Rᶜ = 0)
    (hΩ : MeasurableSet Ω) (hS : MeasurableSet S) (h : ∀ x ∈ R, ∃! m, m ∈ Γ ∧ mulP m x ∈ Ω) :
    μ S = ∑' a : Γ, μ ((fun x => mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω ∩ S) := by
  rw [← measure_iUnion₀]
  · apply measure_congr
    have : ∀ᵐ x ∂μ, x ∈ R := hR
    filter_upwards [this] with x hx
    obtain ⟨s, hs, -⟩ := h x hx
    constructor
    · intro hxS
      exact Set.mem_iUnion.2 ⟨⟨s, hs.1⟩, hs.2, hxS⟩
    · intro hxS
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hxS
      exact ha.2
  · intro a b hab
    refine measure_mono_null ?_ hR
    rintro x ⟨ha, hb⟩ hx
    exact hab (Subtype.ext ((h x hx).unique ⟨a.2, ha.1⟩ ⟨b.2, hb.1⟩))
  · intro a
    exact ((measurable_mulP _ hΩ).inter hS).nullMeasurableSet

def invP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) : ι → Formalism.QuantumDeterminants.Mt k r :=
  fun v => Matrix.of.symm (Matrix.of (m v))⁻¹

theorem mulP_invP_mulP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) (hm : ∀ v, IsUnit (Matrix.of (m v)).det)
    (x : ι → Formalism.QuantumDeterminants.Mt k r) : mulP (invP m) (mulP m x) = x := by
  funext v
  show (Matrix.of (m v))⁻¹ * (Matrix.of (m v) * Matrix.of (x v)) = x v
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hm v), Matrix.one_mul]
  rfl

theorem pointwiseInv_pointwiseInv {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) (hm : ∀ v, IsUnit (Matrix.of (m v)).det) :
    invP (invP m) = m := by
  funext v
  show ((Matrix.of (m v))⁻¹)⁻¹ = m v
  rw [Matrix.nonsing_inv_nonsing_inv _ (hm v)]
  rfl

theorem measure_le {ι : Type} [Fintype ι] {k r : ℕ} (μ : Measure (ι → Formalism.QuantumDeterminants.Mt k r))
    (R Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)) (hΓ : Γ.Countable) (hR : μ Rᶜ = 0)
    (hinv : ∀ m ∈ Γ, invP m ∈ Γ) (hu : ∀ m ∈ Γ, ∀ v, IsUnit (Matrix.of (m v)).det)
    (hpres : ∀ m ∈ Γ, μ.map (fun x => mulP m x) = μ)
    (h₁ : IsFund Γ R Ω₁) (h₂ : IsFund Γ R Ω₂) : μ Ω₁ ≤ μ Ω₂ := by
  haveI : Countable Γ := hΓ.to_subtype
  have e1 := measure_eq_tsum μ R Γ Ω₂ Ω₁ hR h₂.1 h₁.1 h₂.2
  have e2 := measure_eq_tsum μ R Γ Ω₁ Ω₂ hR h₁.1 h₂.1 h₁.2
  have hterm : ∀ a : Γ, μ ((fun x => mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω₂ ∩ Ω₁) =
      μ ((fun x => mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) x) ⁻¹' Ω₁ ∩ Ω₂) := by
    intro a
    have hs : MeasurableSet ((fun x => mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) x) ⁻¹' Ω₁ ∩ Ω₂) :=
      (measurable_mulP _ h₁.1).inter h₂.1
    conv_rhs => rw [← hpres a a.2, Measure.map_apply (measurable_mulP _) hs]
    congr 1
    ext x
    show (mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x ∈ Ω₂ ∧ x ∈ Ω₁) ↔
      (mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) (mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ∈ Ω₁ ∧ mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x ∈ Ω₂)
    rw [mulP_invP_mulP _ (hu a a.2)]
    exact And.comm
  let f : Γ → Γ := fun a => ⟨invP a, hinv a a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h' : invP (a : ι → Formalism.QuantumDeterminants.Mt k r) = invP b := congrArg Subtype.val hab
    apply Subtype.ext
    rw [← pointwiseInv_pointwiseInv _ (hu a a.2), ← pointwiseInv_pointwiseInv _ (hu b b.2), h']
  rw [e1, e2, tsum_congr hterm]
  exact ENNReal.tsum_comp_le_tsum_of_injective hf
    (fun b : Γ => μ ((fun x => mulP (b : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω₁ ∩ Ω₂))

theorem measure_eq : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)),
    Γ.Countable → (fun _ => Matrix.of.symm 1) ∈ Γ → (∀ m ∈ Γ, ∀ m' ∈ Γ, GlobalTheory.DegVol.mulP m m' ∈ Γ) →
    (∀ m ∈ Γ, (fun v => Matrix.of.symm (Matrix.of (m v))⁻¹) ∈ Γ) →
    (∀ m ∈ Γ, ∀ v, Matrix.of (m v) ∈ Formalism.QuantumDeterminants.Nset k r) →
    GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₁ → GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₂ →
    Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₁ = Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₂ := by
  intro ι _ k r Γ Ω₁ Ω₂ hΓ _ _ hinv hN h₁ h₂
  have hH := GlobalTheory.Amp.NHaar.isHaarOn_lebN k r
  haveI : SigmaFinite (GlobalTheory.Amp.lebN k r) := hH.1
  have hu : ∀ m ∈ Γ, ∀ v, IsUnit (Matrix.of (m v)).det := fun m hm v =>
    GlobalTheory.DegVol.RealMat.isUnit_det (hN m hm v).1
  have hnull : Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) (GlobalTheory.DegVol.RP k r (fun _ => 1))ᶜ = 0 := by
    refine measure_mono_null (t := ⋃ v : ι, Function.eval v ⁻¹' {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) ?_
      (measure_iUnion_null fun v => Measure.pi_eval_preimage_null _ hH.2.2.1)
    intro x hx
    simp only [RP, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨v, hv'⟩ := hx
    refine Set.mem_iUnion.2 ⟨v, ?_⟩
    intro hxN
    apply hv'
    refine ⟨hxN, ?_⟩
    simpa using hxN
  have hpres : ∀ m ∈ Γ, (Measure.pi fun _ : ι => GlobalTheory.Amp.lebN k r).map (fun x => mulP m x) =
      Measure.pi fun _ : ι => GlobalTheory.Amp.lebN k r := fun m hm => by
    have e : ∀ v, (GlobalTheory.Amp.lebN k r).map (Formalism.QuantumDeterminants.lmulM (Matrix.of (m v))) = GlobalTheory.Amp.lebN k r :=
      fun v => hH.2.2.2 _ (hN m hm v)
    haveI : ∀ v, SigmaFinite ((GlobalTheory.Amp.lebN k r).map (Formalism.QuantumDeterminants.lmulM (Matrix.of (m v)))) := fun v => by
      rw [e]; infer_instance
    have := Measure.pi_map_pi (μ := fun _ : ι => GlobalTheory.Amp.lebN k r)
      (f := fun v => Formalism.QuantumDeterminants.lmulM (Matrix.of (m v))) fun v => (GlobalTheory.DegVol.Cov.continuous_lmulM _).measurable.aemeasurable
    simp only [e] at this
    exact this
  exact le_antisymm
    (measure_le _ _ Γ Ω₁ Ω₂ hΓ hnull hinv hu hpres h₁ h₂)
    (measure_le _ _ Γ Ω₂ Ω₁ hΓ hnull hinv hu hpres h₂ h₁)

end GlobalTheory.FundEq
end
end

