module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0142
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeOnPuncturedDisc
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0141
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0134
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormSqEqAdaptedFrameSum
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetCoverOfArithmeticVariety
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0143

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicEigenProjectionOnBall
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem perExt_differentiableOn {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ}
    {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)
    (y : Ψ → Fin (j + j') → ℂ) :
    DifferentiableOn ℂ (fun t => C.perExt (F.R t) y) (ballDom F.q) := by
  have h : (fun t => C.perExt (F.R t) y) =
      fun t => ∑ k, C.bas.equivFun y k • (F.R t).P (C.lam k) := by
    funext t
    exact Module.Basis.constr_apply_fintype ℝ C.bas _ y
  rw [h]
  refine DifferentiableOn.fun_sum fun k _ => ?_
  exact (F.hol.2 (C.lam k)).const_smul (C.bas.equivFun y k)

theorem pPart_differentiableOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (τ : Ψ) (y : Fin (j + j') → ℂ), DifferentiableOn ℂ (fun t => C.pPart (F.R t) τ y) (ballDom F.q) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C τ y
  classical
  unfold LatEmb.pPart
  exact ((perExt_differentiableOn C _).sub
    ((perExt_differentiableOn C _).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeFamilyLocalSections
section
open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_logPeriods_of_local_markings : ∀ (n a g : ℕ) (_h : a ≤ n) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : LinearMap.BilinForm ℤ Λ) (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Hf : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (U : Set (Fin n → ℂ)) (Γ₀ : Submodule ℤ (Fin g → ℂ)) (S : Γ₀ → (Fin n → ℂ) → (Fin g → ℂ)), U = {z | z ∈ ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0} → Module.finrank ℤ Λ = 2 * g → (∀ x, E x x = 0) → Function.Bijective E → (∀ z ∈ U, (Hf z).IsHermitian ∧ ∀ x : Fin g → ℂ, x ≠ 0 → 0 < (x ⬝ᵥ Hf z *ᵥ star x).re) → (∀ z₀ ∈ U, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ U ∧ ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun z => P z x) N) ∧ ∀ z ∈ N, Function.Injective (P z) ∧ (P z).range = Γ z ∧ ∀ x y, (P z x ⬝ᵥ Hf z *ᵥ star (P z y)).im = E x y) → (∀ x, DifferentiableOn ℂ (S x) (ball 0 1) ∧ S x 0 = x ∧ ∀ z ∈ U, S x z ∈ Γ z) → (∀ x y z, S (x + y) z = S x z + S y z) → (∀ s : (Fin n → ℂ) → (Fin g → ℂ), ContinuousAt s 0 → (∀ z ∈ U, s z ∈ Γ z) → s 0 ∈ Γ₀) → Submodule.span ℂ (Γ₀ : Set (Fin g → ℂ)) = ⊤ → (∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → ∀ z ∈ U, ∃ k : ℤ, (S x z ⬝ᵥ Hf z *ᵥ star (S y z)).im = N * k) → ∃ L : LogPeriods n a g Λ, L.H = Hf := by
  intro n a g h Λ _ _ _ E Γ Hf U Γ₀ S hU hr hE hEb hH hloc hS hadd hlim hspan hcount
  obtain ⟨L, hL, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_range_eq n a g h Λ E Γ Hf U Γ₀ S hU hr hE hEb hH hloc hS hadd hlim
    hspan hcount
  exact ⟨L, hL⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeStabilizerEquivAutomorphismsStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stabilizer_equiv_automorphisms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), ∃ α : latticeStab C.h C.e.range ≃* autGrp (E := E) F.form, ∀ γ x, C.e ((α γ).1 x) = ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.exists_alpha | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.exists_alpha | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.exists_alpha <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentOfGramDetUnit
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem linearIndependent_of_isUnit_gram_det :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
      [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (d : Fin m → Fin g → ℂ),
      IsUnit (R.gram d).det → LinearIndependent ℂ d := by
  intro E _ _ _ g Λ _ _ R m d hdet
  rw [Fintype.linearIndependent_iff]
  intro x hx
  have hmul : (R.gram d) *ᵥ x = 0 := by
    funext a
    have hsum : (∑ b, x b • d b) ⬝ᵥ (R.Hm *ᵥ star (d a)) = 0 := by
      rw [hx, zero_dotProduct]
    rw [sum_dotProduct] at hsum
    simp only [smul_dotProduct, smul_eq_mul] at hsum
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hsum ⊢
    rw [← hsum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mulVec, dotProduct]
    rw [mul_comm]
  have hx0 : x = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet.ne_zero hmul
  intro i
  rw [hx0, Pi.zero_apply]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetChange
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.PointLog

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem gram_change (R : RiemLat E g Λ) {m : ℕ} (bb d : Fin m → Fin g → ℂ) (Y : Matrix (Fin m) (Fin m) ℂ)
    (hd : ∀ b, d b = ∑ c, Y c b • bb c) : R.gram d = Yᴴ * R.gram bb * Y := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RiemLat.gram, Matrix.of_apply, RiemLat.ip, hd,
    star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem log_det_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (bb d : Fin m → Fin g → ℂ) (Y M : Matrix (Fin m) (Fin m) ℂ) (κ : ℝ), 0 < κ → (∀ b, d b = ∑ c, Y c b • bb c) → R.gram d * M = (κ : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) → M.PosDef → Y.det ≠ 0 ∧ -Real.log M.det.re = 2 * Real.log ‖Y.det‖ + Real.log (R.gram bb).det.re - m * Real.log κ := by
  intro E _ _ _ g Λ _ _ R m bb d Y M κ hκ hd hM hpos
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, gram_change R bb d Y hd, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hMp : 0 < M.det := hpos.det_pos
  obtain ⟨hr, hi⟩ := Complex.pos_iff.mp hMp
  set r := M.det.re with hrdef
  have hMr : M.det = (r : ℂ) := by
    apply Complex.ext <;> simp [hrdef, ← hi]
  set y := Y.det with hy
  set G := (R.gram bb).det with hG
  have hyy : star y * y = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.conj_mul' y
  have hκm : 0 < κ ^ m := pow_pos hκ m
  have e1 : ((‖y‖ ^ 2 : ℝ) : ℂ) * G * (r : ℂ) = ((κ ^ m : ℝ) : ℂ) := by
    rw [← hyy, ← hMr]
    push_cast
    linear_combination hdet
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at e1
    have : ((κ ^ m : ℝ) : ℂ) = 0 := by simpa using e1.symm
    exact hκm.ne' (by exact_mod_cast this)
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hGr : G = ((κ ^ m / (‖y‖ ^ 2 * r) : ℝ) : ℂ) := by
    have h2 : ((‖y‖ ^ 2 * r : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (pow_pos hn 2) hr).ne'
    push_cast at h2 e1 ⊢
    field_simp
    linear_combination e1
  refine ⟨hy0, ?_⟩
  rw [hGr, Complex.ofReal_re, Real.log_div hκm.ne' (mul_pos (pow_pos hn 2) hr).ne',
    Real.log_mul (pow_pos hn 2).ne' hr.ne', Real.log_pow, Real.log_pow]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.PointLog
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEqBallPotentialStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_eq_ball_potential : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (R : RiemLat E g Λ), t ∈ ballDom q → R.Hm = (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹ → R.logDet (fun τ (i : Fin j') => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = ballPot q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodExtensionImaginaryForm
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.im_perExt_eq_Fm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ), R.form = F.form → ∀ y y', (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im = C.Fm y y' := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R hR y y'
  exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen.form_ext C R hR y y'
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetCoverOfArithmeticVarietyStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheet_cover_of_arithmetic_variety : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n nc : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : Fin nc → GroundTheory.Heights₂.Heights.LowerBoundFree.SncChart P n Bd) (V B : ℕ → Set (Fin n → ℂ)) (γ : ℕ → (Fin n → ℂ) → (Σ k, J k) → ℂ) (A : HermLine J) (G : ((Σ k, J k) → ℂ) → ℝ), IsArithVar P (n + 1) → (∀ z ∈ mcPts P, ∃ a, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ z ∈ torusSat {(χ a).γ t}) → IsSheetCover χ V B γ → (∀ m, ContDiffOn ℝ 2 (fun t => Real.log (A.h (γ m t))) (V m)) → (∀ w ∈ mcPts P \ Bd, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, IntegrableOn (fun t => G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t) (B m)) → Summable (fun m => ∫ t in B m, |G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t|) → ptsIntegral (e := n) P (fun _ z => Real.log (A.h z)) G = ∑' m, ∫ t in B m, G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets | exact GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelNormalFormOfHermitianStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_normal_form_of_hermitian : ∀ {I : Type} [Fintype I] [DecidableEq I] (L : (I → ℂ) →ₗ[ℝ] (I → ℂ)) (H : Matrix I I ℂ), H.IsHermitian → (∀ z : I → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H *ᵥ star z).re) → (∀ z w : I → ℂ, (L z ⬝ᵥ H *ᵥ star (L w)).im = (z ⬝ᵥ star w).im) → ∃ (A : (I → ℂ) ≃ₗ[ℂ] (I → ℂ)) (Z : Matrix I I ℂ), Zᵀ = Z ∧ (1 - Zᴴ * Z).PosDef ∧ ∀ z, L z = A (tz Z z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord.exists_linearEquiv_tz | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord.exists_linearEquiv_tz | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord.exists_linearEquiv_tz <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformSymplecticImaginaryStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_transform_symplectic_imaginary : ∀ {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ), Zᵀ = Z → (1 - Zᴴ * Z).PosDef → ∀ z w : I → ℂ, (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SignatureUnitaryBlocksInvertible
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.SgBlocks

variable {j j' : ℕ}

theorem blocks_eqs (u : Matrix (Sg j j') (Sg j j') ℂ) (h : IsSgU u) :
    u.toBlocks₁₁ᴴ * u.toBlocks₁₁ - u.toBlocks₂₁ᴴ * u.toBlocks₂₁ = 1 ∧
    u.toBlocks₁₂ᴴ * u.toBlocks₁₂ - u.toBlocks₂₂ᴴ * u.toBlocks₂₂ = -1 ∧
    u.toBlocks₁₁ᴴ * u.toBlocks₁₂ - u.toBlocks₂₁ᴴ * u.toBlocks₂₂ = 0 := by
  have hu : u = fromBlocks u.toBlocks₁₁ u.toBlocks₁₂ u.toBlocks₂₁ u.toBlocks₂₂ :=
    (fromBlocks_toBlocks u).symm
  generalize u.toBlocks₁₁ = a at hu ⊢
  generalize u.toBlocks₁₂ = b at hu ⊢
  generalize u.toBlocks₂₁ = c at hu ⊢
  generalize u.toBlocks₂₂ = d at hu ⊢
  subst hu
  unfold IsSgU sgI at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_⟩
  · simpa [sub_eq_add_neg] using h1
  · simpa [sub_eq_add_neg] using h4
  · simpa [sub_eq_add_neg] using h2

theorem det_unit_of_eq {m k : ℕ} {x : Matrix (Fin m) (Fin m) ℂ} {y : Matrix (Fin k) (Fin m) ℂ}
    (e : xᴴ * x = 1 + yᴴ * y) : IsUnit x.det := by
  have pd : (xᴴ * x).PosDef := by
    rw [e]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self y)
  have hu : IsUnit (xᴴ * x).det := (Matrix.isUnit_iff_isUnit_det _).1 pd.isUnit
  rw [Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

theorem moebW_zero (u : Matrix (Sg j j') (Sg j j') ℂ) :
    moebW u 0 = u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ := by
  simp [moebW]

theorem one_sub_mul_eq {a : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {c : Matrix (Fin j') (Fin j) ℂ} {d : Matrix (Fin j') (Fin j') ℂ}
    (ha : IsUnit a.det) (hd : IsUnit d.det) (h2 : bᴴ * b - dᴴ * d = -1)
    (h3 : aᴴ * b - cᴴ * d = 0) :
    (1 - (c * a⁻¹) * (c * a⁻¹)ᴴ) * (d * dᴴ) = 1 := by
  have hab : aᴴ * b = cᴴ * d := sub_eq_zero.1 h3
  have haH : IsUnit aᴴ.det := by
    rw [det_conjTranspose]; exact ha.star
  have hdH : IsUnit dᴴ.det := by
    rw [det_conjTranspose]; exact hd.star

  have hWH : (c * a⁻¹)ᴴ * d = b := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, ← hab,
      Matrix.nonsing_inv_mul_cancel_left _ _ haH]
  have hWH' : dᴴ * (c * a⁻¹) = bᴴ := by
    have := congrArg conjTranspose hWH
    simpa [conjTranspose_mul] using this
  have hdd : dᴴ * d = 1 + bᴴ * b := by
    rw [← sub_eq_zero]
    have : bᴴ * b - dᴴ * d + 1 = 0 := by rw [h2]; abel
    rw [← neg_eq_zero, ← this]; abel

  have key : dᴴ * ((1 - (c * a⁻¹) * (c * a⁻¹)ᴴ) * (d * dᴴ)) = dᴴ * 1 := by
    calc dᴴ * ((1 - (c * a⁻¹) * (c * a⁻¹)ᴴ) * (d * dᴴ))
        = (dᴴ * d - (dᴴ * (c * a⁻¹)) * ((c * a⁻¹)ᴴ * d)) * dᴴ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = dᴴ * 1 := by
          rw [hWH, hWH', hdd]; simp
  have := congrArg (fun x => (dᴴ)⁻¹ * x) key
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hdH] using this

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.SgBlocks


open GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.SgBlocks in
theorem GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.sgU_blocks : ∀ (j j' : ℕ) (u : Matrix (Sg j j') (Sg j j') ℂ), IsSgU u → IsUnit u.toBlocks₁₁.det ∧ IsUnit u.toBlocks₂₂.det ∧ (1 - moebW u 0 * (moebW u 0)ᴴ) * (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) = 1 ∧ (1 - moebW u 0 * (moebW u 0)ᴴ).PosDef := by
  open GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.SgBlocks in
  intro j j' u hu
  obtain ⟨h1, h2, h3⟩ := blocks_eqs u hu
  have ha : IsUnit u.toBlocks₁₁.det := by
    refine det_unit_of_eq (y := u.toBlocks₂₁) ?_
    rw [← h1]; abel
  have hd : IsUnit u.toBlocks₂₂.det := by
    refine det_unit_of_eq (y := u.toBlocks₁₂) ?_
    rw [← sub_eq_zero]
    have : u.toBlocks₁₂ᴴ * u.toBlocks₁₂ - u.toBlocks₂₂ᴴ * u.toBlocks₂₂ + 1 = 0 := by rw [h2]; abel
    rw [← neg_eq_zero, ← this]; abel
  have hm : (1 - moebW u 0 * (moebW u 0)ᴴ) * (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) = 1 := by
    rw [moebW_zero]
    exact one_sub_mul_eq ha hd h2 h3
  refine ⟨ha, hd, hm, ?_⟩
  have hpd : (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ).PosDef := by
    have h := Matrix.PosDef.one.mul_mul_conjTranspose_same (B := u.toBlocks₂₂)
      (Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hd))
    simpa using h
  have he : 1 - moebW u 0 * (moebW u 0)ᴴ = (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ)⁻¹ :=
    (Matrix.inv_eq_left_inv hm).symm
  rw [he]
  exact hpd.inv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymmetricMatrixInBallImageStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_pattern_matrix_mem_range_bigZe : ∀ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : Matrix (Fin g) (Fin g) ℂ), Zᵀ = Z → (∀ i k, Z i k ≠ 0 → (e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft) → ∃ t, bigZe e q t = Z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.exists_bigZe_eq | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.exists_bigZe_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.exists_bigZe_eq <;> assumption)
end

