module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0478
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0472
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallHeightVectorIsotropic
section
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.Bridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hermValue_inclR (v : Fin n → E) :
    hermValue F J F (fun i => inclR (F := F) F (v i)) =
      inclR (F := F) F (hE (conj F E).toAlgHom J v v) := by
  have hc : ∀ e : E, conjBase F E F (inclR (F := F) F e) = inclR (F := F) F (conj F E e) := fun e => rfl
  have hb : baseMatrix F J F = J.map (inclR (F := F) F) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermValue, hc, hb, hE, Formalism.UG.hform, dotProduct, mulVec, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.map_apply, mul_assoc]

theorem ofResVec_cvec (v : Fin n → E) :
    ofResVec (ι := Fin n) (Module.finBasis F E) F (cvec F v) = fun i => inclR (F := F) F (v i) := by
  apply resVec_injective (ι := Fin n) (Module.finBasis F E) F
  rw [resVec_ofResVec]
  funext p
  simp only [cvec, resVec, Function.comp_apply, coordsVec, coords, inclR]
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem hermCoords_cvec_ne_zero {v : Fin n → E} (h : hE (conj F E).toAlgHom J v v ≠ 0) :
    hermCoords J (Module.finBasis F E) F (cvec F v) ≠ 0 := by
  intro h0
  apply h
  have h1 : hermValue F J F (ofResVec (ι := Fin n) (Module.finBasis F E) F (cvec F v)) = 0 := by
    apply (coords (Module.finBasis F E) F).injective
    rw [map_zero]
    exact h0
  rw [ofResVec_cvec, hermValue_inclR] at h1
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F F).injective (h1.trans (map_zero _).symm)

theorem matHom_mem_unitaryPoints (g : GAd (conj F E).toAlgHom J) :
    matHom (AF F) (conj F E).toAlgHom J g ∈ unitaryPoints F E J (AF F) := by
  rw [← CompanionTheory.SWFin.HR_eq]
  exact g.2

theorem exists_pos_isotropic_of_hgt_lt :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd (conj F E).toAlgHom J) (v : Fin n → E), v ≠ 0 →
      hgt (conj F E).toAlgHom J g v < ε → hE (conj F E).toAlgHom J v v = 0 := by
  obtain ⟨C, hC, hCb⟩ := exists_adelicNorm_aeval_le (K := F) (d := 2) two_pos
    (hermPoly J (Module.finBasis F E))
    (fun v t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
    (fun w t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
  refine ⟨min 1 C⁻¹, lt_min one_pos (inv_pos.2 hC), fun g v hv hlt => ?_⟩
  by_contra hne
  rw [hgt_eq] at hlt
  have hx : cvec F v ≠ 0 := cvec_ne_zero hv
  have hz := hermCoords_cvec_ne_zero J hne
  have hy := Reduction.hasFiniteContent_height (trG (conj F E).toAlgHom J g) hx
  have he : (fun k => MvPolynomial.aeval
      (Reduction.ratVec (cvec F v) ᵥ* ((trG (conj F E).toAlgHom J g : GL _ (AF F)) : Matrix _ _ (AF F)))
      (hermPoly J (Module.finBasis F E) k)) =
      Reduction.ratVec (hermCoords J (Module.finBasis F E) F (cvec F v)) := by
    funext k
    rw [aeval_hermPoly]
    exact congrFun (hermCoords_vecMul_trHom J (Module.finBasis F E) (cvec F v)
      ⟨_, matHom_mem_unitaryPoints J g⟩) k
  have hfz := Reduction.hasFiniteContent_ratVec hz
  rw [← he] at hfz
  have h1 := Reduction.one_le_adelicNorm_ratVec hz
  rw [← he] at h1
  have h2 : 1 ≤ C * Reduction.height (trG (conj F E).toAlgHom J g) (cvec F v) ^ 2 :=
    h1.trans (hCb _ hy hfz)
  have h0 := Reduction.height_nonneg (trG (conj F E).toAlgHom J g) (cvec F v)
  set t := Reduction.height (trG (conj F E).toAlgHom J g) (cvec F v)
  have ht1 : t < 1 := hlt.trans_le (min_le_left _ _)
  have htC : t < C⁻¹ := hlt.trans_le (min_le_right _ _)
  have h3 : C * t < 1 := by
    have := mul_lt_mul_of_pos_left htC hC
    rwa [mul_inv_cancel₀ hC.ne'] at this
  have h4 : C * t ^ 2 ≤ C * t := by
    nlinarith [mul_nonneg (mul_nonneg hC.le h0) (sub_nonneg.2 ht1.le)]
  linarith

end GlobalTheory.CompanionTheory.RedCov.Bridge

namespace GlobalTheory.CompanionTheory.RedCov

theorem isotropic_of_hgt_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd σ J) (v : Fin n → E), v ≠ 0 → hgt σ J g v < ε → hE σ J v v = 0 := by
  intro F E _ _ _ _ _ σ h n J _
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  haveI : IsTotallyReal F := h.1
  haveI : IsTotallyComplex E := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((h.2.2.2 τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  exact Bridge.exists_pos_isotropic_of_hgt_lt J

end GlobalTheory.CompanionTheory.RedCov

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCutoffTranslateContDiff
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CutOff

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem contDiff_lastEnt : ContDiff ℝ ∞ (lastEnt : (Fin k → Cinf E) → Cinf E) := by
  unfold lastEnt
  refine ContDiff.sum fun c _ => ?_
  by_cases h : (c : ℕ) + 1 = k
  · simp only [if_pos h]
    exact contDiff_apply ℝ (fun _ : Fin k => Cinf E) c
  · simp only [if_neg h]
    exact contDiff_const

theorem isOpen_lastEnt_unit : IsOpen {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
  (Units.isOpen (R := Cinf E)).preimage (contDiff_lastEnt (E := E)).continuous

theorem contDiffOn_inverse_lastEnt :
    ContDiffOn ℝ ∞ (fun x : Fin k → Cinf E => Ring.inverse (lastEnt x))
      {x | IsUnit (lastEnt x)} := by
  intro x hx
  obtain ⟨u, hu⟩ := hx
  have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Cinf E → Cinf E) (lastEnt x) := by
    rw [← hu]; exact contDiffAt_ringInverse ℝ u
  exact (h1.comp x (contDiff_lastEnt (E := E)).contDiffAt).contDiffWithinAt

def tauM (x : Fin k → Cinf E) : LieI (InfinitePlace E) k := Matrix.of.symm (rowM (rowI x))

theorem contDiffOn_tauM :
    ContDiffOn ℝ ∞ (tauM : (Fin k → Cinf E) → LieI (InfinitePlace E) k)
      {x | IsUnit (lastEnt x)} := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun c => ?_
  have hinv := contDiffOn_inverse_lastEnt (E := E) (k := k)
  by_cases hi : (i : ℕ) + 1 = k
  · have e : ∀ x : Fin k → Cinf E, tauM x i c = rowI x c := fun x => rowM_apply_last _ i c hi
    simp only [e]
    by_cases hc : (c : ℕ) + 1 = k
    · simp only [rowI, if_pos hc]
      exact hinv
    · simp only [rowI, if_neg hc]
      exact ((contDiff_apply ℝ (fun _ : Fin k => Cinf E) c).contDiffOn.mul hinv).neg
  · have e : ∀ x : Fin k → Cinf E, tauM x i c = (1 : Matrix (Fin k) (Fin k) (Cinf E)) i c :=
      fun x => rowM_apply_ne _ i c hi
    simp only [e]
    exact contDiffOn_const

theorem tauM_isUnit {x : Fin k → Cinf E} (h : IsUnit (lastEnt x)) :
    IsUnit (Matrix.of (tauM x)) := by
  have e : Matrix.of (tauM x) = (((rowGL x)⁻¹ : GL (Fin k) (Cinf E)) : Matrix (Fin k) (Fin k) (Cinf E)) :=
    (rowGL_inv_val h).symm
  rw [e]
  exact Units.isUnit _

theorem rt_inv_eq_orb (φ : XB E k) {x : Fin k → Cinf E} (h : IsUnit (lastEnt x)) :
    Rt E k (infGL E k (rowGL x))⁻¹ φ = orb (repI E k) φ (tauM x) := by
  have hu := tauM_isUnit h
  have e : hu.unit = (rowGL x)⁻¹ := Units.ext (by
    rw [IsUnit.unit_spec]; exact (rowGL_inv_val h).symm)
  rw [orb, dite_eq_left hu, e]
  change _ = Rt E k (infGL E k (rowGL x)⁻¹) φ
  rw [map_inv (infGL E k)]

theorem contDiff_cut_orbit {φ : XB E k} (hφ : SmV (repI E k) φ) {b : (Fin k → Cinf E) → ℝ}
    (hb : ContDiff ℝ ∞ b) (hs : ∀ x ∈ tsupport b, IsUnit (lastEnt x)) :
    ContDiff ℝ ∞ fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ := by
  have hO := isOpen_lastEnt_unit (E := E) (k := k)
  have hbc : ContDiff ℝ ∞ fun x => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp hb
  have horb : ContDiffOn ℝ ∞ (fun x => orb (repI E k) φ (tauM x)) {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
    ContDiffOn.comp hφ contDiffOn_tauM fun x hx => tauM_isUnit hx
  have hF : ContDiffOn ℝ ∞ (fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ)
      {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
    (hbc.contDiffOn.smul horb).congr fun x hx => by
      rw [rt_inv_eq_orb φ hx]
      rfl
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ tsupport b
  · exact hF.contDiffAt (hO.mem_nhds (hs x hx))
  · have e : (fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq e

end GlobalTheory.CompanionTheory.CutOff

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVecCompleteOfUnitary
section
noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix MeasureTheory GlobalTheory.SmoothGlob Filter
open GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped Topology

namespace GlobalTheory.CompanionTheory.SobComplete

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Dw_sub_of_sm {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H} (hx : Sm ε σ x) (hy : Sm ε σ y) :
    Dw σ l (x - y) = Dw σ l x - Dw σ l y := by
  have hxy : Sm ε σ (x - y) := sm_iff.2 (Submodule.sub_mem _ (sm_iff.1 hx) (sm_iff.1 hy))
  have h := Dw_add hσ hl hxy hy
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem tendsto_sobNorm_zero {σ : Mx n → (H →L[ℂ] H)} {u : ℕ → H} (S : List (List (Mx n)))
    (h : ∀ l ∈ S, Tendsto (fun k => ‖l.foldr (dRep σ) (u k)‖) atTop (𝓝 0)) :
    Tendsto (fun k => sobNorm σ S (u k)) atTop (𝓝 0) := by
  induction S with
  | nil => simpa [sobNorm] using tendsto_const_nhds
  | cons l S ih =>
    have h1 := h l List.mem_cons_self
    have h2 := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr fun k => ?_
    simp [sobNorm]

theorem smoothVec_complete_of_unitary (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : IsURepOn (UJset ε) σ) (w : ℕ → H) (hw : ∀ k, SmoothVec (lieSet ε) σ (w k))
    (hC : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∀ δ > 0,
      ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ) :
    ∃ w₀, SmoothVec (lieSet ε) σ w₀ ∧ ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)),
      (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → Tendsto (fun k => sobNorm σ S (w k - w₀)) atTop (𝓝 0) := by
  have hρ : ModRep ε σ := GlobalTheory.FamSmooth.modRep_of_isURepOn hσ
  have hmem : ∀ l : List (lie (Jm ε)), ∀ X ∈ l.map Subtype.val, X ∈ lieSet ε := fun l X hX => by
    obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hX
    exact Y.2
  let U : ℕ → List (lie (Jm ε)) → H := fun k l => Dw σ (l.map Subtype.val) (w k)
  have hU : ∀ k, U k ∈ Fam ε σ := fun k => GlobalTheory.SobUnif.smooth_fam hσ (hw k)
  have hcau : ∀ l, CauchySeq fun k => U k l := fun l => by
    refine Metric.cauchySeq_iff.2 fun δ hδ => ?_
    obtain ⟨K, hK⟩ := hC [l.map Subtype.val] (by simpa using hmem l) δ hδ
    refine ⟨K, fun k hk m hm => ?_⟩
    rw [dist_eq_norm]
    show ‖Dw σ (l.map Subtype.val) (w k) - Dw σ (l.map Subtype.val) (w m)‖ < δ
    rw [← Dw_sub_of_sm hσ (hmem l) (hw k) (hw m)]
    exact (norm_Dw_le_sobNorm σ List.mem_cons_self _).trans_lt (hK k hk m hm)
  choose v hv using fun l => cauchySeq_tendsto_of_complete (hcau l)
  have hvF : v ∈ Fam ε σ :=
    (GlobalTheory.T.isClosed_derivativeFamilies_moderateGrowth n ε H σ hρ).mem_of_tendsto (tendsto_pi_nhds.2 hv) (Eventually.of_forall hU)
  obtain ⟨hs, hd⟩ := GlobalTheory.SobUnif.fam_smooth hσ hvF
  refine ⟨v [], hs, fun S hS => tendsto_sobNorm_zero S fun l hl => ?_⟩
  obtain ⟨l', rfl⟩ := GlobalTheory.SobUnif.exists_lift l (hS l hl)
  have h1 : Tendsto (fun k => U k l' - v l') atTop (𝓝 0) := by
    simpa using (hv l').sub_const (v l')
  have h2 := h1.norm
  rw [norm_zero] at h2
  refine h2.congr fun k => ?_
  show ‖Dw σ (l'.map Subtype.val) (w k) - v l'‖ = ‖Dw σ (l'.map Subtype.val) (w k - v [])‖
  rw [Dw_sub_of_sm hσ (hmem l') (hw k) hs, hd l']

theorem smoothVec_complete : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ w : ℕ → H, (∀ k, SmoothVec (lieSet ε) σ (w k)) → (∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∀ δ > 0, ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ) → ∃ w₀, SmoothVec (lieSet ε) σ w₀ ∧ ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → Filter.Tendsto (fun k => sobNorm σ S (w k - w₀)) Filter.atTop (nhds 0) :=
  fun n ε H _ _ _ σ hσ _ w hw hC => smoothVec_complete_of_unitary n ε H σ hσ w hw hC

end GlobalTheory.CompanionTheory.SobComplete

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusConjugateUnipotentBounded
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem torus_contracts_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Q : Set (GAd σ J)) (c : ℝ), IsCompact Q → 0 < c → ∀ s : Fin r, ∃ M : ℝ, 0 ≤ M ∧ ∀ m ∈ Q, m ∈ unipRad σ J (pre X s) → ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n), ‖(archMat σ J τ (projArch σ J w (a⁻¹ * m * a)) - 1) i j‖ ≤ M / ratio t s := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW Q c hQ hc s
  obtain ⟨K, hK0, hK⟩ := _root_.GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio r c hc
  have hb : ∀ q : (Σ w : InfinitePlace F, EmbOver E w) × FrameIx r × FrameIx r × Fin n × Fin n, ∃ B : ℝ, ∀ g ∈ Q,
      ‖((frameIdem (σ : E →+* E) J X Y q.2.1).map q.1.2.1 * (archMat σ J q.1.2 (projArch σ J q.1.1 g) - 1) *
        (frameIdem (σ : E →+* E) J X Y q.2.2.1).map q.1.2.1) q.2.2.2.1 q.2.2.2.2‖ ≤ B := fun q => by
    have hcont : Continuous fun g : GAd σ J => archMat σ J q.1.2 (projArch σ J q.1.1 g) :=
      (GlobalTheory.Orb.continuous_archMat σ J q.1.2).comp (continuous_projArch σ J q.1.1)
    refine hQ.exists_bound_of_continuousOn (Continuous.continuousOn ?_)
    exact ((continuous_const.matrix_mul (hcont.sub continuous_const)).matrix_mul continuous_const).matrix_elem _ _
  choose B hB using hb
  set Bt : ℝ := ∑ q, |B q| with hBt
  have hBt0 : 0 ≤ Bt := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(Fintype.card (FrameIx r) : ℝ) * ((Fintype.card (FrameIx r) : ℝ) * (K * Bt)), by positivity, ?_⟩
  intro m hm hmU t ht a ha w τ i j
  have hr : 0 < ratio t s := ratio_pos ht s
  have hd : ∀ α, 0 < frameWt t α := frameWt_pos ht.1
  set A := archMat σ J τ (projArch σ J w a) with hAdef
  set A' := archMat σ J τ (projArch σ J w a⁻¹) with hA'def
  set M₁ := archMat σ J τ (projArch σ J w m) - 1 with hM₁
  set P : FrameIx r → Matrix (Fin n) (Fin n) ℂ := fun α => (frameIdem (σ : E →+* E) J X Y α).map τ.1 with hPdef
  have hAA : A' * A = 1 := by
    rw [hAdef, hA'def, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have e2 : archMat σ J τ (projArch σ J w (a⁻¹ * m * a)) - 1 = A' * M₁ * A := by
    rw [map_mul, map_mul, map_mul, map_mul, ← hAdef, ← hA'def, hM₁, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAA]
  have hP : ∑ α, P α = 1 := by
    have : ∑ α, P α = (τ.1.mapMatrix) (∑ α, frameIdem (σ : E →+* E) J X Y α) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; rfl
    rw [this, sum_frameIdem, map_one]
  have hTor : ∀ β, A * P β = ((frameWt t β : ℝ) : ℂ) • P β := fun β =>
    _root_.GlobalTheory.CompanionTheory.RapidDecay.torus_mul_frameIdem F E σ h n J hJ r X Y hW t a ha ht.1 w τ β
  have hA : A = ∑ β, ((frameWt t β : ℝ) : ℂ) • P β := by
    calc A = A * ∑ β, P β := by rw [hP, Matrix.mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun β _ => hTor β
  have hTor' : ∀ α, A' * P α = ((frameWt t α : ℝ) : ℂ)⁻¹ • P α := fun α => by
    have hne : ((frameWt t α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hd α).ne'
    rw [eq_inv_smul_iff₀ hne, ← Matrix.mul_smul, ← hTor α, ← Matrix.mul_assoc, hAA, Matrix.one_mul]
  have hA' : A' = ∑ α, ((frameWt t α : ℝ) : ℂ)⁻¹ • P α := by
    calc A' = A' * ∑ α, P α := by rw [hP, Matrix.mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun α _ => hTor' α
  have e3 : A' * M₁ * A = ∑ α, ∑ β, (((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)) • (P α * M₁ * P β) := by
    conv_lhs => rw [hA', hA]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, Matrix.mul_smul, smul_smul]
  have term : ∀ α β, ‖((((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)) • (P α * M₁ * P β)) i j‖ ≤ K * Bt / ratio t s := fun α β => by
    by_cases hl : frameLev s α ≤ frameLev s β
    · have h0 : P α * M₁ * P β = 0 := GlobalTheory.T.unipotent_frame_level_triangular F E σ h n J hJ r X Y hW s m hmU w τ α β hl
      rw [h0, smul_zero]
      simpa using div_nonneg (mul_nonneg hK0 hBt0) hr.le
    · have h1 := hK s t ht α β (not_le.1 hl)
      have h2 : ‖(P α * M₁ * P β) i j‖ ≤ Bt :=
        ((hB (⟨w, τ⟩, α, β, i, j) m hm).trans (le_abs_self _)).trans
          (Finset.single_le_sum (f := fun q => |B q|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _))
      have h3 : ‖((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)‖ = frameWt t β / frameWt t α := by
        rw [norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hd α).le,
          Real.norm_of_nonneg (hd β).le, div_eq_inv_mul]
      rw [Matrix.smul_apply, norm_smul, h3]
      calc _ ≤ K / ratio t s * Bt := mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg hK0 hr.le)
        _ = _ := by ring
  rw [e2, e3, Matrix.sum_apply]
  calc _ ≤ ∑ α : FrameIx r, ‖(∑ β, (((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)) • (P α * M₁ * P β)) i j‖ := norm_sum_le _ _
    _ ≤ ∑ α : FrameIx r, ∑ β : FrameIx r, K * Bt / ratio t s := Finset.sum_le_sum fun α _ => by
        rw [Matrix.sum_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => term α β)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelSupDistributesSubreps
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.PRep.WhitSup

theorem mem_sup_of_mem_twKer_sup {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (X Y : Subrepresentation ρ) (H : Subgroup G) (χ : H →* ℂˣ)
    {w : (X ⊔ Y).toSubmodule} (hw : w ∈ twKer (X ⊔ Y).toRepresentation H χ) :
    (w : V) ∈ X.toSubmodule ⊓ twKer ρ H χ ⊔ Y.toSubmodule ⊓ twKer ρ H χ := by
  unfold GlobalTheory.PRep.twKer at hw ⊢
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨h, u, rfl⟩ := hz
    have hu : (u : V) ∈ X.toSubmodule ⊔ Y.toSubmodule := by
      rw [← Subrepresentation.toSubmodule_sup]
      exact u.2
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hu
    have hρu : ((X ⊔ Y).toRepresentation h u : V) = ρ h u := rfl
    have hcoe : (((X ⊔ Y).toRepresentation h u - (χ h : ℂ) • u : (X ⊔ Y).toSubmodule) : V) =
        (ρ h x - (χ h : ℂ) • x) + (ρ h y - (χ h : ℂ) • y) := by
      rw [Submodule.coe_sub, Submodule.coe_smul, hρu, ← hxy, map_add (f := _), smul_add]
      abel
    rw [hcoe]
    apply Submodule.add_mem_sup
    · exact Submodule.mem_inf.2
        ⟨X.toSubmodule.sub_mem (X.apply_mem_toSubmodule h hx) (X.toSubmodule.smul_mem _ hx),
          Submodule.subset_span ⟨h, x, rfl⟩⟩
    · exact Submodule.mem_inf.2
        ⟨Y.toSubmodule.sub_mem (Y.apply_mem_toSubmodule h hy) (Y.toSubmodule.smul_mem _ hy),
          Submodule.subset_span ⟨h, y, rfl⟩⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Submodule.coe_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem _ c ha

theorem sup_inf_twKer_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ X Y : Subrepresentation ρ, (X ⊔ Y).toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ≤ X.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ⊔ Y.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
  intro k _ _ _ _ ψ hψ N V _ _ ρ hρ X Y w hw
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hw
  have hW : GlobalTheory.PRep.IsSmooth (X ⊔ Y).toRepresentation := by
    unfold GlobalTheory.PRep.IsSmooth at hρ ⊢
    intro v
    have hset : {g | (X ⊔ Y).toRepresentation g v = v} = {g | ρ g v = v} := by
      ext g
      exact Subtype.ext_iff
    rw [hset]
    exact hρ v
  have hw' : (⟨w, hw1⟩ : (X ⊔ Y).toSubmodule) ∈ GlobalTheory.PRep.twKer
      (X ⊔ Y).toRepresentation (GlobalTheory.SmGL.unipB k (Fin N))
      (GlobalTheory.LocGL.whitChar ψ N) :=
    GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N (X ⊔ Y).toRepresentation ρ
      hW hρ (X ⊔ Y).toSubmodule.subtype Subtype.val_injective (fun _ _ => rfl) _ hw2
  exact GlobalTheory.CompanionTheory.PRep.WhitSup.mem_sup_of_mem_twKer_sup X Y _ _ hw'

end GlobalTheory.CompanionTheory.PRep.WhitSup

end
end

