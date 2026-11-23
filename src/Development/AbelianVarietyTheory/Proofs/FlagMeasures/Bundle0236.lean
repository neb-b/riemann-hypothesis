module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0235
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0231
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIndependentOfQuotientMeasure
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SnMass.AmpUniq

theorem isQuotMeas_smul {k r : ℕ} {μG μR ν : Measure (Mt k r)} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : IsQuotMeas μG (c • μR) ν) : IsQuotMeas μG μR (c • ν) := by
  intro f hf
  rw [h f hf]
  simp only [lintegral_smul_measure, smul_eq_mul]
  exact lintegral_const_mul' _ _ hc

theorem equiv_N {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat k r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {Φ : Mat k r → Wp}
    (hπ : IsURepOn (UWset k r z) π) (hΦ : IsSPsiEquiv z ψ π Φ) {n : Mat k r} (hn : n ∈ Nset k r)
    {x : Mat k r} (hx : x ∈ GG k r) : Φ (n * x) = ψ n • Φ x := by
  have h1 : (1 : Mat k r) ∈ UWset k r z := (isClosedSub_UWset (k := k) (r := r) z).2.2.1
  have e := hΦ 1 h1 n hn x hx
  rw [hπ.1.1, one_mul, ContinuousLinearMap.one_apply] at e
  exact e

theorem amp_uniq : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (ψ ψ' : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (cN : ℝ), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsURepOn (UWset k r z) π → IsURepOn (UWset k r z') π' → (∀ n ∈ Nset k r, ‖ψ n‖ = 1 ∧ ‖ψ' n‖ = 1) → IsSPsiEquiv z ψ π Φ → IsSPsiEquiv z' ψ' π' Φ' → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → ∀ (γ : Mat k r) (μG μR ν ν' : Measure (Mt k r)) (t : ℝ), γ ∈ GG k r → (∀ ρ ∈ Rset k r γ, ψ (γ * ρ * γ⁻¹) = ψ' ρ) → IsHaarOn (GG k r) μG → IsHaarOn (Rset k r γ) μR → 0 < t → IsQuotMeas μG μR ν → IsQuotMeas μG (ENNReal.ofReal t • μR) ν' → ampJ ν cN Φ Φ' γ = (t : ℂ) • ampJ ν' cN Φ Φ' γ := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ z z' ψ ψ' π π' Φ Φ' cN _ _ _ _ hπ hπ' hψ hΦ hΦ' hc hc' γ μG μR ν ν' t hγ
    hψγ hG hR ht hν hν'
  obtain ⟨hRc, hRu⟩ := _root_.GlobalTheory.UnipUnimod.rset_unimodular k r γ hγ
  have hν₂ : IsQuotMeas μG μR (ENNReal.ofReal t • ν') := isQuotMeas_smul ENNReal.ofReal_ne_top hν'
  have hGm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := (isClosedSub_GG (k := k) (r := r)).2.2.2.1
  let F : Mat k r → (Wq →L[ℂ] Wp) := fun g => (innerSL ℂ (Φ' g)).smulRight (Φ (γ * g))
  have hFc : ContinuousOn F (GG k r) := by
    have h1 : ContinuousOn (fun g => innerSL ℂ (Φ' g)) (GG k r) :=
      (innerSL ℂ).continuous.comp_continuousOn hc'
    have h2 : ContinuousOn (fun g => Φ (γ * g)) (GG k r) :=
      hc.comp (continuous_const.mul continuous_id).continuousOn fun g hg => hGm γ hγ g hg
    exact (ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous₂.comp_continuousOn (h1.prodMk h2)
  have hFi : ∀ ρ ∈ Rset k r γ, ∀ x ∈ GG k r, F (ρ * x) = F x := by
    intro ρ hρ x hx
    have hρN : ρ ∈ Nset k r := hρ.1
    have hρc : γ * ρ * γ⁻¹ ∈ Nset k r := hρ.2
    have e1 : Φ' (ρ * x) = ψ' ρ • Φ' x := equiv_N hπ' hΦ' hρN hx
    have e2 : γ * (ρ * x) = γ * ρ * γ⁻¹ * (γ * x) := by
      rw [show γ * ρ * γ⁻¹ * (γ * x) = γ * ρ * (γ⁻¹ * γ) * x by simp only [Matrix.mul_assoc],
        Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_GG hγ), Matrix.mul_one, Matrix.mul_assoc]
    have e3 : Φ (γ * (ρ * x)) = ψ' ρ • Φ (γ * x) := by
      rw [e2, equiv_N hπ hΦ hρc (hGm γ hγ x hx), hψγ ρ hρ]
    have hn : ‖ψ' ρ‖ = 1 := (hψ ρ hρN).2
    ext w
    simp only [F, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, e1, e3, inner_smul_left,
      smul_smul]
    congr 1
    calc (starRingEnd ℂ) (ψ' ρ) * inner ℂ (Φ' x) w * ψ' ρ
        = ((starRingEnd ℂ) (ψ' ρ) * ψ' ρ) * inner ℂ (Φ' x) w := by ring
      _ = inner ℂ (Φ' x) w := by rw [Complex.conj_mul', hn]; simp
  have key := (_root_.GlobalTheory.SnMass.QuotUniq.quot_uniq k r (Rset k r γ) μG μR ν (ENNReal.ofReal t • ν') hRc hG hR (hRu μR hR) hν hν₂
    (Wq →L[ℂ] Wp) F hFc hFi).2
  rw [integral_smul_measure, ENNReal.toReal_ofReal ht.le] at key
  change (cN : ℂ)⁻¹ • ∫ x, F (Matrix.of x) ∂ν = (t : ℂ) • ((cN : ℂ)⁻¹ • ∫ x, F (Matrix.of x) ∂ν')
  rw [key, Complex.coe_smul, smul_comm]

end GlobalTheory.SnMass.AmpUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt
section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace GlobalTheory.Tube

def Hd (k : ℕ) (η : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1

def blk {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun i j => Fin.lastCases (motive := fun _ => ℂ) (Fin.lastCases (motive := fun _ => ℂ) d r j)
    (fun i' => Fin.lastCases (motive := fun _ => ℂ) (b i') (A i') j) i

@[simp] theorem blk_ll {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) :
    blk A b r d (Fin.last k) (Fin.last k) = d := by simp [blk]

@[simp] theorem blk_lc {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) (j : Fin k) :
    blk A b r d (Fin.last k) j.castSucc = r j := by simp [blk]

@[simp] theorem blk_cl {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) (i : Fin k) :
    blk A b r d i.castSucc (Fin.last k) = b i := by simp [blk]

@[simp] theorem blk_cc {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) (i j : Fin k) :
    blk A b r d i.castSucc j.castSucc = A i j := by simp [blk]

theorem blk_ext {k : ℕ} {M N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h1 : ∀ i j : Fin k, M i.castSucc j.castSucc = N i.castSucc j.castSucc)
    (h2 : ∀ i : Fin k, M i.castSucc (Fin.last k) = N i.castSucc (Fin.last k))
    (h3 : ∀ j : Fin k, M (Fin.last k) j.castSucc = N (Fin.last k) j.castSucc)
    (h4 : M (Fin.last k) (Fin.last k) = N (Fin.last k) (Fin.last k)) : M = N := by
  first
  | exact @_root_.GlobalTheory.MatrixExtLast.matrix_ext_last
  | exact _root_.GlobalTheory.MatrixExtLast.matrix_ext_last
  | (apply _root_.GlobalTheory.MatrixExtLast.matrix_ext_last <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixExtLast.matrix_ext_last <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixExtLast.matrix_ext_last <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixExtLast.matrix_ext_last ..)

theorem Hd_eq (k : ℕ) (η : ℝ) : Hd k η = blk 1 0 0 (η : ℂ) := by
  refine blk_ext (fun i j => ?_) (fun i => ?_) (fun j => ?_) ?_
  · simp [Hd, Matrix.diagonal_apply, Matrix.one_apply, Fin.castSucc_ne_last]
  · simp [Hd, Matrix.diagonal_apply, Fin.castSucc_ne_last]
  · simp [Hd, Matrix.diagonal_apply, (Fin.castSucc_ne_last _).symm]
  · simp [Hd]

theorem Hd_sq (k : ℕ) {η : ℝ} (hη : η = 1 ∨ η = -1) : Hd k η * Hd k η = 1 := by
  refine GlobalTheory.GramExp.diag_sq fun i => ?_
  split_ifs
  · rcases hη with h | h <;> simp [h]
  · simp

def nsq {k : ℕ} (β : Fin k → ℂ) : ℝ := ∑ j, ‖β j‖ ^ 2

def dd {k : ℕ} (η : ℝ) (β : Fin k → ℂ) : ℝ := Real.sqrt (1 - η * nsq β)

def sec {k : ℕ} (η : ℝ) (β : Fin k → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  blk (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j - ((η / (1 + dd η β) : ℝ) : ℂ) * (conj (β i) * β j))
    (fun i => -(η : ℂ) * conj (β i)) β (dd η β : ℂ)

def kap {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (u : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := blk A 0 0 u

def row {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin k → ℂ := fun j => g (Fin.last k) j.castSucc

def ph {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℂ :=
  g (Fin.last k) (Fin.last k) / (‖g (Fin.last k) (Fin.last k)‖ : ℂ)

def bet {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin k → ℂ := fun j => conj (ph g) * row g j

def top {k : ℕ} (η : ℝ) (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => (g * sec η (-bet g)) i.castSucc j.castSucc

abbrev Par (k : ℕ) : Type := lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) × ℝ × EuclideanSpace ℂ (Fin k)

def hv {k : ℕ} (w : EuclideanSpace ℂ (Fin k)) : Fin k → ℂ := fun j => w j / (Real.sqrt 2 : ℂ)

def chart {k : ℕ} (η : ℝ) (x : Par k) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  kap (NormedSpace.exp (unrealify (x.1 : EuclideanSpace ℝ _))) (Complex.exp (x.2.1 * Complex.I)) * sec η (hv x.2.2)

def tang {k : ℕ} (η : ℝ) (x : Par k) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  blk (unrealify (x.1 : EuclideanSpace ℝ _)) (fun i => -(η : ℂ) * conj (hv x.2.2 i)) (hv x.2.2) (x.2.1 * Complex.I)

def tubeO (k : ℕ) (η t : ℝ) : Set (PI.MtM (k + 1)) :=
  {g | Matrix.of g ∈ UH (Hd k η) ∧ nsq (row (Matrix.of g)) < t}

end GlobalTheory.Tube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowDivLattice
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

theorem hasDom_ideLat_dInv_div : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * (dInv E t')⁻¹) c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  intro F E _ _ _ _ _ σ hσ hu t t' c hc
  have hE : IsTotallyComplex E := hσ.2.1
  have hdE : (discr E : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero E
  have hdF : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have hd : |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
    have h1 := congrArg (Nat.cast : ℕ → ℤ) (FrameDual.natAbs_discr_sq (F := F) (E := E) hσ.2.2.1)
    rw [Nat.cast_pow, Int.natCast_natAbs, Int.natCast_natAbs] at h1
    rw [sq_abs]
    have h2 : ((|discr E| : ℤ) : ℝ) = ((|discr F| ^ 2 : ℤ) : ℝ) := by rw [h1]
    push_cast at h2
    rw [h2, sq_abs]
  set I := dInv E t * (dInv E t')⁻¹ with hIdef
  have hNI : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = (|(discr E : ℝ)|⁻¹ ^ t) * (|(discr E : ℝ)|⁻¹ ^ t')⁻¹ := by
    rw [hIdef, map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, FrameDual.absNorm_dInv, FrameDual.absNorm_dInv]
  have hI : I ≠ 0 := by
    intro h0
    have h1 : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = 0 := by rw [h0, map_zero, Rat.cast_zero]
    rw [hNI] at h1
    have : |(discr E : ℝ)| ≠ 0 := abs_ne_zero.2 hdE
    simp_all
  obtain ⟨L₀, hL₀, hcov⟩ := HomCovolume.exists_idealLat E hE I hI
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let f : (InfinitePlace E → ℂ) →ₗ[ℝ] (InfinitePlace E → ℂ) :=
    LinearMap.pi fun w => (Algebra.lmul ℝ ℂ ((c : ℂ))⁻¹).comp (LinearMap.proj w)
  have hf : ∀ z w, f z w = ((c : ℂ))⁻¹ * z w := fun _ _ => rfl
  have hdet : LinearMap.det f = (∏ _w : InfinitePlace E, ‖(c : ℂ)‖ ^ 2)⁻¹ := by
    rw [LinearMap.det_pi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]
  have hpos : 0 < ∏ _w : InfinitePlace E, ‖(c : ℂ)‖ ^ 2 :=
    Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 hc0) _
  let L : Submodule ℤ (InfinitePlace E → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HomCovolume.HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ z ∈ (ideLat I c : Set (InfinitePlace E → ℂ)) := by
    intro z
    change f z ∈ L₀ ↔ ∃ y ∈ I, ∀ w, z w = (c : ℂ) * w.embedding y
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩
    · rw [← h w, hf, mul_inv_cancel_left₀ hc0]
    · rw [hf, h w, inv_mul_cancel_left₀ hc0]
  refine ⟨latticeDomain L, measurableSet_latticeDomain L, fun a => ?_, ?_⟩
  · obtain ⟨z, hz, hu'⟩ := existsUnique_add_mem_latticeDomain L a
    refine ⟨z, ⟨(hL z).1 z.2, hz⟩, ?_⟩
    rintro l ⟨hl, hl'⟩
    exact congrArg Subtype.val (hu' ⟨l, (hL l).2 hl⟩ hl')
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet, abs_of_pos (inv_pos.2 hpos),
      div_inv_eq_mul] at h
    have hfin : volume (latticeDomain L) ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]
    congr 1
    have hn : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have hDpos : 0 < |(discr F : ℝ)| := abs_pos.2 hdF
    have hr : |(discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) =
        |(discr F : ℝ)| ^ (1 + 2 * t') / |(discr F : ℝ)| ^ (2 * t) := by
      rw [show (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) = ((1 + 2 * t' : ℕ) : ℝ) - ((2 * t : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_sub hDpos, Real.rpow_natCast, Real.rpow_natCast]
    rw [hNI, HomCovolume.vInv_pow E hE, hn, hd, Real.sqrt_sq hDpos.le, hr, Finset.prod_const, Finset.card_univ,
      Complex.norm_real, Real.norm_of_nonneg hc.le]
    generalize |(discr F : ℝ)| = D at hDpos
    generalize Fintype.card (InfinitePlace E) = n
    rw [inv_pow, inv_pow, inv_inv, ← pow_mul, ← pow_mul, ← pow_mul, pow_add, pow_one, div_eq_mul_inv]
    ring

end GlobalTheory.SnMass.VolN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowMulLattice
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.CovMul

open GlobalTheory.HomCovolume GlobalTheory.SnMass.FrameDual

theorem hasDom_ideLat {E : Type} [Field E] [NumberField E] (hE : IsTotallyComplex E)
    (a : FractionalIdeal (𝓞 E)⁰ E) (ha : a ≠ 0) {c : ℝ} (hc : 0 < c) :
    HasDom volume (ideLat a c : Set (InfinitePlace E → ℂ))
      (ENNReal.ofReal ((FractionalIdeal.absNorm a : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E *
        c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  obtain ⟨L₀, hL₀, hcov⟩ := exists_idealLat E hE a ha
  let f : (InfinitePlace E → ℂ) →ₗ[ℝ] (InfinitePlace E → ℂ) := c⁻¹ • LinearMap.id
  have hf : ∀ z, f z = c⁻¹ • z := fun _ => rfl
  have hrank : Module.finrank ℝ (InfinitePlace E → ℂ) = 2 * Fintype.card (InfinitePlace E) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hdet : LinearMap.det f = (c ^ (2 * Fintype.card (InfinitePlace E)))⁻¹ := by
    change LinearMap.det (c⁻¹ • LinearMap.id) = _
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, hrank, inv_pow]
  have hpos : 0 < c ^ (2 * Fintype.card (InfinitePlace E)) := pow_pos hc _
  let L : Submodule ℤ (InfinitePlace E → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ z ∈ ideLat a c := by
    intro z
    change f z ∈ L₀ ↔ _
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩
    · have h1 := h w
      rw [hf, Pi.smul_apply, Complex.real_smul] at h1
      rw [← h1, Complex.ofReal_inv, mul_inv_cancel_left₀ (by exact_mod_cast hc.ne')]
    · rw [hf, Pi.smul_apply, Complex.real_smul, h w, Complex.ofReal_inv,
        inv_mul_cancel_left₀ (by exact_mod_cast hc.ne')]
  refine ⟨GlobalTheory.latticeDomain L, GlobalTheory.measurableSet_latticeDomain L, fun v => ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := GlobalTheory.existsUnique_add_mem_latticeDomain L v
    refine ⟨z, ⟨(hL _).1 z.2, hz⟩, ?_⟩
    rintro l ⟨hl, hlD⟩
    exact congrArg Subtype.val (hu ⟨l, (hL l).2 hl⟩ hlD)
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (GlobalTheory.isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet,
      abs_of_pos (inv_pos.2 hpos), div_inv_eq_mul] at h
    have hfin : volume (GlobalTheory.latticeDomain L) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]

theorem value_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    [Algebra.FormallyUnramified (𝓞 F) (𝓞 E)] (t t' : ℕ) :
    ((FractionalIdeal.absNorm (dInv E t * dInv E t') : ℚ) : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E =
      (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) *
        |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) := by
  have hD : 0 < |(NumberField.discr F : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F))
  have hdisc : |(discr E : ℝ)| = |(NumberField.discr F : ℝ)| ^ 2 := by
    have h1 := congrArg (Nat.cast : ℕ → ℝ) (natAbs_discr_sq (F := F) (E := E) h2)
    simpa [Nat.cast_natAbs] using h1
  have hcard : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hexp : |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) =
      ((|(NumberField.discr F : ℝ)| ^ 2)⁻¹ ^ t * (|(NumberField.discr F : ℝ)| ^ 2)⁻¹ ^ t') *
        |(NumberField.discr F : ℝ)| := by
    have e1 : (2 * (t : ℝ)) = ((2 * t : ℕ) : ℝ) := by push_cast; ring
    have e2 : (2 * (t' : ℝ)) = ((2 * t' : ℕ) : ℝ) := by push_cast; ring
    rw [Real.rpow_sub hD, Real.rpow_sub hD, Real.rpow_one, e1, e2, Real.rpow_natCast,
      Real.rpow_natCast, pow_mul, pow_mul, inv_pow, inv_pow]
    field_simp
  rw [map_mul, Rat.cast_mul, absNorm_dInv, absNorm_dInv, vInv_pow E hE, hdisc,
    Real.sqrt_sq hD.le, hcard, hexp]
  ring

theorem hasDom_ideLat_dInv_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * dInv E t') c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  intro F E _ _ _ _ _ σ hσ hU t t' c hc
  have h := hasDom_ideLat hσ.2.1 (dInv E t * dInv E t')
    (mul_ne_zero (dInv_ne_zero t) (dInv_ne_zero t')) hc
  rwa [value_eq hσ.2.1 hσ.2.2.1 t t'] at h

end GlobalTheory.SnMass.VolN.CovMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DelSqIrreducibleUnitary
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.WeylUnitary

theorem delSq_irreducible_unitary :
    ∀ (n : ℕ) (lam : DomWeight n), FiniteDimensional ℂ (delSq ℂ n lam) ∧ delSq ℂ n lam = nablaSq ℂ n lam ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ delSq ℂ n lam, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam) ∧ ∀ U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ), U ≤ delSq ℂ n lam → (∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ p ∈ U, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ U) → U = ⊥ ∨ U = delSq ℂ n lam := by
  intro n lam
  rw [← Formalism.L2.Col.nablaSq_eq_delSq ℂ lam]
  have ha : Antitone lam.natW := fun i j hij => by
    have := lam.anti hij
    simp only [DomWeight.natW]
    omega
  refine ⟨GlobalTheory.Branching.finite_nablaSq ℂ n lam, rfl,
    fun g p hp => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ g p hp, fun U hle hU => ?_⟩
  rw [or_iff_not_imp_left]
  intro hne
  exact le_antisymm hle (GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl _ ha U hle
    (GlobalTheory.Branching.rowDivClosed_of_rowAct_stable U (GlobalTheory.Branching.rowAct_mem_of_unitary_stable U hU)) hne)

end GlobalTheory.WeylUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInnerLatticeVectorAnisotropicStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inner_lattice_vector_anisotropic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)), Fr.IsInner L → ∃ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L ∧ H.h (Fr.f (Fin.last r)) (y : V) = 1 ∧ ∀ a, H.h (y : V) (Fr.es a) = 0 := by
  first | exact @GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic' | exact GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic' | (intros; apply GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueLayeredStrictFundamentalDomain
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem existsUnique_layered_fundamentalDomain :
    ∀ {G X B : Type} [Group G] [Finite B] {V : B → Type} [∀ β, AddCommGroup (V β)] (ρ : G → X → X) (NN : Set X) (o : X) (deg : B → ℕ) (c : ∀ β, X → V β) (L D : ∀ β, Set (V β)), o ∈ NN → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ β, (0 : V β) ∈ L β) → (∀ β v, ∃! l, l ∈ L β ∧ v + l ∈ D β) → (∀ β, c β o = 0) → (∀ (d : ℕ) (g : G), (∀ β, deg β < d → c β (ρ g o) = 0) → ∀ x ∈ NN, ∀ β, deg β ≤ d → c β (ρ g x) = c β x + c β (ρ g o)) → (∀ (g : G) (β : B), (∀ β', deg β' < deg β → c β' (ρ g o) = 0) → c β (ρ g o) ∈ L β) → (∀ β, ∀ l ∈ L β, ∃ g : G, c β (ρ g o) = l ∧ ∀ β', β' ≠ β → deg β' ≤ deg β → c β' (ρ g o) = 0) → (∀ g : G, (∀ β, c β (ρ g o) = 0) → g = 1) → ∀ x ∈ NN, ∃! g : G, ∀ β, c β (ρ g x) ∈ D β := by
  intro G X B _ _ V _ ρ NN o deg c L D ho h1 hmul hst hL0 hD hco htr hL hon hinj x hx
  classical
  haveI := Fintype.ofFinite B
  have hgx : ∀ (g : G) (y : X), y ∈ NN → ρ g y ∈ NN := fun g y hy => hst g y hy

  have step : ∀ (d : ℕ) (T : Finset B), (∀ β ∈ T, deg β = d) →
      (∃ g : G, ∀ β, deg β < d → c β (ρ g x) ∈ D β) →
      ∃ g : G, ∀ β, (deg β < d ∨ β ∈ T) → c β (ρ g x) ∈ D β := by
    intro d T
    induction T using Finset.induction_on with
    | empty =>
      intro _ ⟨g, hg⟩
      refine ⟨g, fun β hβ => ?_⟩
      rcases hβ with hβ | hβ
      · exact hg β hβ
      · simp at hβ
    | insert b T hb ih =>
      intro hT h0
      obtain ⟨g, hg⟩ := ih (fun β hβ => hT β (Finset.mem_insert_of_mem hβ)) h0
      have hbd : deg b = d := hT b (Finset.mem_insert_self b T)
      obtain ⟨l, ⟨hlL, hlD⟩, -⟩ := hD b (c b (ρ g x))
      obtain ⟨h, hhl, hh0⟩ := hon b l hlL
      have hlow : ∀ β, deg β < d → c β (ρ h o) = 0 := fun β hβ =>
        hh0 β (fun e => by subst e; omega) (by omega)
      have htrans := htr d h hlow (ρ g x) (hgx g x hx)
      refine ⟨h * g, fun β hβ => ?_⟩
      rw [hmul]
      by_cases hβb : β = b
      · subst hβb
        rw [htrans β (by omega), hhl]
        exact hlD
      · have hle : deg β ≤ d := by
          rcases hβ with hβ | hβ
          · omega
          · exact (hT β hβ).le
        have hold : deg β < d ∨ β ∈ T := by
          rcases hβ with hβ | hβ
          · exact Or.inl hβ
          · exact Or.inr ((Finset.mem_insert.mp hβ).resolve_left hβb)
        rw [htrans β hle, hh0 β hβb (by omega), add_zero]
        exact hg β hold
  have exD : ∀ d : ℕ, ∃ g : G, ∀ β, deg β < d → c β (ρ g x) ∈ D β := by
    intro d
    induction d with
    | zero => exact ⟨1, fun β hβ => absurd hβ (Nat.not_lt_zero _)⟩
    | succ d ih =>
      obtain ⟨g, hg⟩ := step d (Finset.univ.filter (fun β => deg β = d))
        (fun β hβ => (Finset.mem_filter.mp hβ).2) ih
      refine ⟨g, fun β hβ => hg β ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hβ with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  obtain ⟨M, hM⟩ := (Set.finite_range deg).bddAbove
  obtain ⟨g₀, hg₀⟩ := exD (M + 1)
  refine ⟨g₀, fun β => hg₀ β (Nat.lt_succ_of_le (hM ⟨β, rfl⟩)), ?_⟩

  intro g₂ hg₂
  have hg₁ : ∀ β, c β (ρ g₀ x) ∈ D β := fun β => hg₀ β (Nat.lt_succ_of_le (hM ⟨β, rfl⟩))
  have hy : ρ g₀ x ∈ NN := hgx g₀ x hx
  have hδy : ρ (g₂ * g₀⁻¹) (ρ g₀ x) = ρ g₂ x := by
    rw [← hmul, inv_mul_cancel_right]
  have vanish : ∀ d : ℕ, ∀ β, deg β < d → c β (ρ (g₂ * g₀⁻¹) o) = 0 := by
    intro d
    induction d with
    | zero => exact fun β hβ => absurd hβ (Nat.not_lt_zero _)
    | succ d ih =>
      intro β hβ
      rcases Nat.lt_succ_iff_lt_or_eq.mp hβ with h | h
      · exact ih β h
      · have hin : c β (ρ (g₂ * g₀⁻¹) o) ∈ L β := hL _ β (fun β' hβ' => ih β' (by omega))
        have hadd := htr d (g₂ * g₀⁻¹) ih (ρ g₀ x) hy β h.le
        rw [hδy] at hadd
        have hmem : c β (ρ g₀ x) + c β (ρ (g₂ * g₀⁻¹) o) ∈ D β := hadd ▸ hg₂ β
        have hzero : c β (ρ g₀ x) + 0 ∈ D β := by simpa using hg₁ β
        exact (hD β (c β (ρ g₀ x))).unique ⟨hin, hmem⟩ ⟨hL0 β, hzero⟩
  have hone : g₂ * g₀⁻¹ = 1 :=
    hinj _ (fun β => vanish (M + 1) β (Nat.lt_succ_of_le (hM ⟨β, rfl⟩)))
  exact mul_inv_eq_one.mp hone

end GlobalTheory.SnMass.VolN
end

