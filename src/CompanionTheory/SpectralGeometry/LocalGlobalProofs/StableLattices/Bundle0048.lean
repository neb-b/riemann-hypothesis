module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0358
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0045
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0046
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DualClassInvolutiveImports
section

end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlagFacts
section
open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.GradFlag

open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S

variable {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}

def pM (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A - A)

def qM (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A + A)

theorem J_mul (h : IsGrad ε A) : Formalism.REAL.Jm ε * A = -(A * Formalism.REAL.Jm ε) := by
  obtain ⟨hg, hH, -, -⟩ := h
  have h0 : Aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * A = 0 := hg
  rw [hH] at h0
  exact eq_neg_of_add_eq_zero_right h0

theorem A4 (h : A * A * A = A) : A * A * A * A = A * A := by rw [h]

theorem pM_idem (h : A * A * A = A) : pM A * pM A = pM A := by
  have h4 := A4 h
  unfold pM
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub, ← mul_assoc, h4, h]
  module

theorem pM_mul_qM (h : A * A * A = A) : pM A * qM A = 0 := by
  have h4 := A4 h
  unfold pM qM
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_add, add_mul, mul_sub, ← mul_assoc, h4, h]
  module

theorem J_mul_pM (h : IsGrad ε A) : Formalism.REAL.Jm ε * pM A = qM A * Formalism.REAL.Jm ε := by
  have hJ := J_mul h
  have h2 : Formalism.REAL.Jm ε * (A * A) = A * A * Formalism.REAL.Jm ε := by
    rw [← mul_assoc, hJ, neg_mul, mul_assoc, hJ, mul_neg, neg_neg, mul_assoc]
  unfold pM qM
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, add_mul, h2, hJ, sub_neg_eq_add]

theorem trace_qM (h : IsGrad ε A) : Matrix.trace (qM A) = Matrix.trace (pM A) := by
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have : qM A = Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε := by
    rw [J_mul_pM h, mul_assoc, hJJ, mul_one]
  rw [this, Matrix.trace_mul_comm, ← mul_assoc, hJJ, one_mul]

theorem pM_conjTranspose (h : Aᴴ = A) : (pM A)ᴴ = pM A := by
  unfold pM
  simp [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, h]

theorem isProj (h : A * A * A = A) : LinearMap.IsProj (Vm A) (Matrix.toLin' (pM A)) := by
  refine ⟨fun x => ⟨x, rfl⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  change Matrix.toLin' (pM A) (Matrix.toLin' (pM A) y) = Matrix.toLin' (pM A) y
  rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, pM_idem h]

theorem trace_pM (h : A * A * A = A) : Matrix.trace (pM A) = (rk A : ℂ) := by
  have := (isProj h).trace
  rw [Matrix.trace_toLin'_eq] at this
  exact this

theorem one_le_rk (h : IsGrad ε A) : 1 ≤ rk A := by
  obtain ⟨-, -, h3, hA⟩ := id h
  by_contra hc
  have h0 : rk A = 0 := by omega
  have hb : Vm A = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hP : pM A = 0 := by
    have : Matrix.toLin' (pM A) = 0 := LinearMap.range_eq_bot.mp hb
    simpa using this
  have hQ : qM A = 0 := by
    have hJJ := Formalism.REAL.Jm_mul_self ε
    have : qM A = Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε := by
      rw [J_mul_pM h, mul_assoc, hJJ, mul_one]
    rw [this, hP]; simp
  apply hA
  have : A = qM A - pM A := by unfold pM qM; module
  rw [this, hP, hQ, sub_zero]

theorem isotropic (h : IsGrad ε A) {x y : Fin n → ℂ} (hx : x ∈ Vm A) (hy : y ∈ Vm A) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  obtain ⟨-, hH, h3, -⟩ := id h
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  change star (pM A *ᵥ u) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (pM A *ᵥ v)) = 0
  have hz : pM A * (Formalism.REAL.Jm ε * pM A) = 0 := by
    rw [J_mul_pM h, ← mul_assoc, pM_mul_qM h3, zero_mul]
  rw [star_mulVec, pM_conjTranspose hH, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, hz]
  simp

theorem flagFacts : FlagFacts := by
  intro n ε A h
  obtain ⟨-, -, h3, -⟩ := id h
  refine ⟨one_le_rk h, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [W]
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h0 : W A 0 = ⊥ := rfl
    have h1 : W A 1 = Vm A := rfl
    change Module.finrank ℂ (W A 1) = Module.finrank ℂ (W A 0) + rk A
    rw [h0, h1, finrank_bot, zero_add]
    rfl
  · intro x hx y hy
    exact isotropic h hx hy
  · have hj : (Matrix.trace ((1 / 2 : ℂ) • (A * A + A))).re = (rk A : ℝ) := by
      change (Matrix.trace (qM A)).re = _
      rw [trace_qM h, trace_pM h3]
      simp
    unfold rhoA
    simp only [hj]

end GlobalTheory.CompanionTheory.GradFlag
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FreeAlgebraActionOnSubquotientStatement
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_algebra_action_on_subquotient : ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (L : Type) (l : L → Module.End ℂ C)
    (Z B : Submodule ℂ C), (∀ k, ∀ z ∈ Z, l k z ∈ Z) → (∀ k, ∀ z ∈ B, l k z ∈ B) →
    ∃ ρ : FreeAlgebra ℂ L →ₐ[ℂ] Module.End ℂ (Z ⧸ B.comap Z.subtype),
      ∀ (y : FreeAlgebra ℂ L) (z : Z), ∃ hz : FreeAlgebra.lift ℂ l y (z : C) ∈ Z,
        ρ y (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨FreeAlgebra.lift ℂ l y (z : C), hz⟩ := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.QuotAction.descends | exact GlobalTheory.CompanionTheory.RgCOBlock.QuotAction.descends | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.QuotAction.descends <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InitialStatement
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.RgStart

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S ReciprocityTheory.ChartRestriction.DS GlobalTheory.FlagMeas Formalism.MainNotions.S GlobalTheory.Count

variable {n : ℕ} {ε : Fin n → Bool}

theorem measurable_modA (A : Matrix (Fin n) (Fin n) ℂ) : Measurable (modA (ε := ε) A) := by
  unfold modA
  have h1 : Measurable fun τ : Fin 1 → ℝ => layerProd n 1 (fun _ : Fin 1 => rk A) τ id := by
    unfold layerProd
    simp only [id]
    fun_prop
  exact (h1.comp (Measurable.of_eval fun i =>
    measurable_locSize_uMat n ε 1 (fun _ : Fin 1 => rk A) (W A) i)).ennreal_ofReal

theorem detOn_pos_of_left_inv {f g : Matrix (Fin n) (Fin n) ℂ} (hgf : g * f = 1) (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ y ∈ V, f *ᵥ y ∈ V) : 0 < detOn f V := by
  classical
  have h : ∀ y ∈ V, Matrix.toLin' f y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]
    exact hV y hy
  unfold detOn
  rw [dite_eq_left h]
  refine norm_pos_iff.mpr fun h0 => ?_
  obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt (LinearMap.bot_lt_ker_of_det_eq_zero h0)
  have h1 : f *ᵥ (x : Fin n → ℂ) = 0 := by
    have := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    simpa [Matrix.toLin'_apply] using this
  have h2 : (x : Fin n → ℂ) = 0 := by
    have := congrArg (g *ᵥ ·) h1
    simpa [Matrix.mulVec_mulVec, hgf] using this
  exact hx0 (by simpa using Subtype.ext h2)

theorem modA_ne_zero (A : Matrix (Fin n) (Fin n) ℂ) {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) :
    modA A m ≠ 0 := by
  have hinv : (((m : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      uMat m = 1 := Units.inv_mul _
  have hd : ∀ i, 0 < detOn (uMat m) (W A i) := fun i =>
    detOn_pos_of_left_inv hinv _ fun y hy => (hm i y hy).1
  have hτ : ∀ i : Fin 1, 0 < locSize (fun _ : Fin 1 => rk A) (W A) (uMat m) i := fun i =>
    Real.rpow_pos_of_pos (div_pos (hd _) (hd _)) _
  have hp : 0 < layerProd n 1 (fun _ : Fin 1 => rk A) (locSize (fun _ : Fin 1 => rk A) (W A) (uMat m)) id := by
    unfold layerProd
    simp only [id]
    exact mul_pos (prod_pos fun i _ => prod_pos fun k _ =>
        mul_pos (pow_pos (div_pos (hτ i) (hτ k)) _) (pow_pos (mul_pos (hτ i) (hτ k)) _))
      (prod_pos fun i _ => mul_pos (pow_pos (hτ i) _) (pow_pos (pow_pos (hτ i) _) _))
  unfold modA
  exact (ENNReal.ofReal_pos.mpr hp).ne'

theorem startOf : StartOf := by
  intro _ _ hLine hSlab hFub hKMaj n ε H _ _ _ σ D E hK hU hL2 A μ hA hμ u ξ
  obtain ⟨F, hFm, hFK, hFint, hFle⟩ := hKMaj n ε H σ D E hK hU hL2 u ξ
  obtain ⟨μN, μM, hN, hM, hMS, hMinv, ⟨κ, hκ0, hκt, hκ⟩, hnull⟩ := hFub n ε A hA
  obtain ⟨a, τ, ha, hτ, haM, hadd, haS, hcent, hmod, htime⟩ := hLine n ε A hA
  haveI := hN
  haveI := hM
  obtain ⟨⟨Msub, eM⟩, hS, -⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε 1 (W A)
  have hfin : (∫⁻ v, ∫⁻ m, modA A m * F (v * m) ∂μM ∂μN) < ⊤ := by
    have h := hFint
    rw [hκ F hFm hFK] at h
    exact ENNReal.lt_top_of_mul_ne_top_right h.ne hκ0
  have h1N : (1 : Formalism.REAL.UJ ε) ∈ flagN ε (W A) := by
    refine ⟨fun i y _ => ?_, fun y _ => ?_⟩ <;>
      · rw [GlobalTheory.FlagLeviGroup.uMat_one, Matrix.one_mulVec, sub_self]
        exact Submodule.zero_mem _
  have hsl := hSlab (Formalism.REAL.UJ ε) μN μM (flagM ε (W A)) a (modA A) τ (rhoA A) hS.measurableSet hMS ha.measurable
    (measurable_modA A) hτ hadd
    (fun m hm t => by
      have : m * a t ∈ Msub := Msub.mul_mem (by rw [← SetLike.mem_coe, eM]; exact hm)
        (by rw [← SetLike.mem_coe, eM]; exact haS t)
      rw [← eM]; exact this)
    (fun t => hMinv (a t) (haS t) (hcent t)) hmod
    (fun m hm t => by simpa using htime 1 h1N m hm t)
    (fun m hm => modA_ne_zero A hm) F hFm hfin
  let I : Formalism.REAL.UJ ε → ℝ≥0∞ := fun x =>
    ∫⁻ t in Set.Ioi (0 : ℝ), F (x * a t) * ENNReal.ofReal (Real.exp (2 * rhoA A * t))
  have hI : Measurable I := Measurable.lintegral_prod_right'
    (f := fun p : Formalism.REAL.UJ ε × ℝ => F (p.1 * a p.2) * ENNReal.ofReal (Real.exp (2 * rhoA A * p.2)))
    ((hFm.comp (measurable_fst.mul (ha.measurable.comp measurable_snd))).mul (by fun_prop))
  have hE : MeasurableSet (I ⁻¹' {⊤}) := hI (measurableSet_singleton ⊤)
  have h0 : (μN.prod μM) {p | p.1 * p.2 ∈ I ⁻¹' {⊤}} = 0 := by
    refine measure_mono_null (fun p hp => ?_) (ae_iff.mp hsl)
    have hp' : I (p.1 * p.2) = ⊤ := hp
    show ¬ I (p.1 * p.2) < ⊤
    rw [hp']
    exact lt_irrefl _
  have hμE : μ (I ⁻¹' {⊤}) = 0 := hnull μ hμ _ hE h0
  have hae : ∀ᵐ x ∂μ, I x ≠ ⊤ := by
    refine ae_iff.mpr (measure_mono_null (fun x hx => ?_) hμE)
    exact not_not.mp hx
  have hle : ∀ y : Formalism.REAL.UJ ε, lineInt ε (baseCoef σ D ξ u) A (-rhoA A) y ≤ I y := by
    intro y
    unfold lineInt
    refine lintegral_mono fun t => ?_
    have e1 : S7.toM y * NormedSpace.exp ((t : ℂ) • A) = uMat (y * a t) := by
      rw [← haM t]
      rfl
    have e2 : Real.exp (-2 * (-rhoA A) * t) = Real.exp (2 * rhoA A * t) := by
      congr 1
      ring
    rw [e1, e2]
    exact mul_le_mul' (hFle _) le_rfl
  filter_upwards [hae] with x hx
  exact lt_of_le_of_lt (hle x) (lt_top_iff_ne_top.mpr hx)

end GlobalTheory.CompanionTheory.RgStart
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionPreservesSupportDegreeStatement
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_action_preserves_support_degree : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → ∀ (x : Cn n V), SuppIn (inU lev) x → ∀ p q, lev p = lev q → SuppIn (inU lev) (lF E p q x) ∧ ∀ j, Deg j x → Deg j (lF E p q x) := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.lF_suppIn_deg | exact GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.lF_suppIn_deg | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.lF_suppIn_deg <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MaximalCompactStatement
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.RgKMaj

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_riesz (l : E →ₗ[ℂ] ℂ) : ∃ η : E, ∀ x, l x = ⟪η, x⟫_ℂ := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  refine ⟨(InnerProductSpace.toDual ℂ E).symm (LinearMap.toContinuousLinearMap l), fun x => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem sum_sq_eq_of_basis {ι κ : Type*} [Fintype ι] [Fintype κ] (l : E →ₗ[ℂ] ℂ)
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ E) :
    ∑ i, ‖l (b i)‖ ^ 2 = ∑ j, ‖l (c j)‖ ^ 2 := by
  obtain ⟨η, hη⟩ := exists_riesz l
  simp only [hη]
  rw [b.sum_sq_norm_inner_left, c.sum_sq_norm_inner_left]

theorem sq_le_of_basis {ι : Type*} [Fintype ι] (l : E →ₗ[ℂ] ℂ)
    (b : OrthonormalBasis ι ℂ E) (x : E) :
    ‖l x‖ ^ 2 ≤ ‖x‖ ^ 2 * ∑ i, ‖l (b i)‖ ^ 2 := by
  obtain ⟨η, hη⟩ := exists_riesz l
  simp only [hη]
  rw [b.sum_sq_norm_inner_left, ← mul_pow, mul_comm ‖x‖]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm η x) 2

end Abstract

theorem sum_enorm_sq {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ∑ i, ‖z i‖ₑ ^ 2 = ENNReal.ofReal (∑ i, ‖z i‖ ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem lintegral_enorm_sq_lt_top {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (h : MemLp f 2 μ) : (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) < ⊤ := by
  have h1 := h.eLpNorm_lt_top
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) two_ne_zero h.aestronglyMeasurable
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at h2
  rw [← h2]
  exact ENNReal.pow_lt_top h1

variable {n : ℕ} {ε : Fin n → Bool}

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_coef {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (ξ v : H) :
    Continuous (fun g : Formalism.REAL.UJ ε => ⟪ξ, σ (Formalism.MainNotions.S.umat g) v⟫_ℂ) := by
  have h : Continuous (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g) v) :=
    (hU.2.2 v).comp_continuous continuous_uMat (fun g => g.2)
  exact continuous_const.inner h

theorem sum_sq_translate {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hst : Formalism.MainNotions.S.IsKStableOn ε σ S)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ S) (ξ : H) (g k : Formalism.REAL.UJ ε)
    (hk : k ∈ Formalism.REAL.KG ε) :
    ∑ i, ‖⟪ξ, σ (Formalism.MainNotions.S.umat (g * k)) (b i : H)⟫_ℂ‖ ^ 2 =
      ∑ i, ‖⟪ξ, σ (Formalism.MainNotions.S.umat g) (b i : H)⟫_ℂ‖ ^ 2 := by
  have hkK : Formalism.MainNotions.S.umat k ∈ Formalism.REAL.Kset ε := hk
  let T : S →ₗᵢ[ℂ] S :=
    { toLinearMap := ((σ (Formalism.MainNotions.S.umat k) : H →ₗ[ℂ] H).comp S.subtype).codRestrict S
        (fun x => hst _ hkK _ x.2)
      norm_map' := fun x => hU.2.1 _ k.2 _ }
  let Te : S ≃ₗᵢ[ℂ] S := T.toLinearIsometryEquiv rfl
  let l : S →ₗ[ℂ] ℂ :=
    { toFun := fun x => ⟪ξ, σ (Formalism.MainNotions.S.umat g) (x : H)⟫_ℂ
      map_add' := fun x y => by simp [inner_add_right]
      map_smul' := fun c x => by simp [inner_smul_right] }
  have hmul : ∀ x : H, σ (Formalism.MainNotions.S.umat (g * k)) x = σ (Formalism.MainNotions.S.umat g) (σ (Formalism.MainNotions.S.umat k) x) := by
    intro x
    have : Formalism.MainNotions.S.umat (g * k) = Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat k := rfl
    rw [this, hU.1.2 _ g.2 _ k.2]
    rfl
  have h := sum_sq_eq_of_basis l (b.map Te) b
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
  rw [hmul, OrthonormalBasis.map_apply]
  rfl

theorem kMaj : CompanionTheory.RgExh.Dec.N.S.KMaj := by
  intro n ε H _ _ _ σ D E hK hU hS u ξ
  obtain ⟨S, hfd, huS, hst⟩ := (hK.mem u).1 u.2
  haveI := hfd
  let b := stdOrthonormalBasis ℂ S
  let c : Formalism.REAL.UJ ε → Fin (Module.finrank ℂ S) → ℂ := fun g i => ⟪ξ, σ (Formalism.MainNotions.S.umat g) (b i : H)⟫_ℂ
  have hcm : ∀ i, Measurable fun g => ‖c g i‖ₑ ^ 2 := fun i =>
    (continuous_coef hU ξ (b i : H)).measurable.enorm.pow_const 2
  refine ⟨fun g => ENNReal.ofReal (‖(u : H)‖ ^ 2) * ∑ i, ‖c g i‖ₑ ^ 2, ?_, ?_, ?_, ?_⟩
  · exact (Finset.measurable_sum _ fun i _ => hcm i).const_mul _
  · intro g k hk
    simp only [sum_enorm_sq]
    congr 2
    exact sum_sq_translate hU hst b ξ g k hk
  · rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hcm i),
      lintegral_finsetSum _ fun i _ => hcm i]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun i _ => ?_)
    exact lintegral_enorm_sq_lt_top (hS (b i : H) ξ)
  · intro g
    let l : S →ₗ[ℂ] ℂ :=
      { toFun := fun x => ⟪ξ, σ (Formalism.MainNotions.S.umat g) (x : H)⟫_ℂ
        map_add' := fun x y => by simp [inner_add_right]
        map_smul' := fun c x => by simp [inner_smul_right] }
    have h := sq_le_of_basis l b ⟨(u : H), huS⟩
    show ‖l ⟨(u : H), huS⟩‖ₑ ^ 2 ≤ ENNReal.ofReal (‖(u : H)‖ ^ 2) * ∑ i, ‖l (b i)‖ₑ ^ 2
    rw [sum_enorm_sq, ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal h

end GlobalTheory.CompanionTheory.RgKMaj
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordOccursOfSubquotientImports
section

end

