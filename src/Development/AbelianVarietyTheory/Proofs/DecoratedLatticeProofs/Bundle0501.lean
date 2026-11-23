module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqIntegralFactorQuotient
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartLevelStandardBasePointEqMember
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfEqOfEqOnRational
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem GlobalTheory.RatHalfDense.tmul_split {F E A : Type} [Field F] [CommRing E] [Algebra F E] [CommRing A] [Algebra F A]
    (a : E) (α ι : A) (u : F) (N d : ℕ)
    (h : α = ((N * d : ℕ) : F) • algebraMap F A u + ((N * d : ℕ) : F) • ι) :
    a ⊗ₜ[F] α = (algebraMap F E (((N * d : ℕ) : F) * u) * a) ⊗ₜ[F] (1 : A) + N • (((d : E) * a) ⊗ₜ[F] ι) := by
  rw [h, TensorProduct.tmul_add]
  congr 1
  · rw [Algebra.algebraMap_eq_smul_one (A := A) u, smul_smul, ← Algebra.smul_def, TensorProduct.smul_tmul]
  · have hd' : (d : E) * a = (d : F) • a := by rw [Algebra.smul_def, map_natCast]
    rw [TensorProduct.tmul_smul, hd', ← TensorProduct.smul_tmul', ← Nat.cast_smul_eq_nsmul F, smul_smul, Nat.cast_mul]

namespace GlobalTheory.RatHalfDense

variable {D : D7}

theorem coe_stdLat (n : ℕ) :
    ((Formalism.L2.Pj.stdLat D.host.E n : Submodule _ _) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, GlobalTheory.LocM.Unim.mem_stdLat, intVec, Set.mem_setOf_eq]
  constructor
  · intro h k
    obtain ⟨c, hc⟩ := h k
    rw [← hc]
    exact c.isIntegral_coe
  · intro h k
    exact ⟨⟨x k, h k⟩, rfl⟩

theorem exists_nsmul_mem_stdHom (S T : HSp D) : ∃ K : ℕ, 0 < K ∧ ∀ t : WO S T, t.map (infPart D) = 0 →
    (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → K • t ∈ stdHom S T := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (GlobalTheory.LocM.Unim.isLattice_stdLat S.rank) (GlobalTheory.LocM.Unim.isLattice_stdLat T.rank)
  refine ⟨K, hK, fun t h1 h2 => ?_⟩
  have := h t h1 h2
  rw [coe_stdLat, coe_stdLat] at this
  exact this

theorem mul_eq_zero_of_parts {e z : AE D} (he : infPart D e = 0) (hz : finPart D z = 0) : e * z = 0 := by
  rw [Formalism.IndefR.Eqv.infPart_eq_zero_iff_smul] at he
  rw [Formalism.IndefR.Eqv.finPart_eq_zero_iff_smul] at hz
  rw [← he, ← hz, smul_mul_smul_comm]
  have : Formalism.IndefR.Eqv.eFin D * Formalism.IndefR.Eqv.eInf D = 0 := by
    simp only [Formalism.IndefR.Eqv.eFin, Formalism.IndefR.Eqv.eInf, pairA]
    exact Prod.ext (show (0 : Ainf D.host.F) * 1 = 0 from zero_mul _) (show (1 : Af D.host.F) * 0 = 0 from mul_zero _)
  rw [this, zero_smul]

theorem exists_nat_mul_isIntegral (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * z) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, h⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', Int.cast_neg, neg_mul]; exact h.neg

theorem exists_rat_add_nsmul (z : EAf D) (N : ℕ) (hN : 0 < N) :
    ∃ γ : D.host.E, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, z = eToEAf D γ + N • w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | tmul a α =>
    obtain ⟨d, hd, hda⟩ := exists_nat_mul_isIntegral a
    have hc : ((N * d : ℕ) : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_pos hN hd).ne'
    obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_adele
      (R := NumberField.RingOfIntegers D.host.F) (K := D.host.F) (((N * d : ℕ) : D.host.F)⁻¹ • α)
    have hα : α = ((N * d : ℕ) : D.host.F) • algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u
        + ((N * d : ℕ) : D.host.F) • (((N * d : ℕ) : D.host.F)⁻¹ • α - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
    refine ⟨algebraMap D.host.F D.host.E (((N * d : ℕ) : D.host.F) * u) * a,
      ((d : D.host.E) * a) ⊗ₜ (((N * d : ℕ) : D.host.F)⁻¹ • α - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u), ?_, ?_⟩
    · have h1 : ((d : D.host.E) * a) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inl ⟨⟨(d : D.host.E) * a, ⟨⟨(d : D.host.E) * a, hda⟩, rfl⟩⟩, rfl⟩)
      have h2 : (1 : D.host.E) ⊗ₜ[D.host.F] (((N * d : ℕ) : D.host.F)⁻¹ • α
          - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inr ⟨⟨_, hu⟩, rfl⟩)
      have := mul_mem h1 h2
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
    · exact tmul_split a α _ u N d hα
  | add x y hx hy =>
    obtain ⟨γ₁, w₁, hw₁, h₁⟩ := hx
    obtain ⟨γ₂, w₂, hw₂, h₂⟩ := hy
    refine ⟨γ₁ + γ₂, w₁ + w₂, add_mem hw₁ hw₂, ?_⟩
    rw [h₁, h₂, map_add (f := _), smul_add]
    abel

theorem exists_half_approx {S T : HSp D} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {E₂ : AE D} (hE : IsIdemSum E₂ Q)
    (K : ℕ) (hK : 0 < K) (t : WO S T) (ht : IsHalf E₂ t) :
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ u ∈ stdHom S T, IsHalf E₂ u ∧
      t = γ.map (fun a => E₂ * incA D a) + K • u := by
  obtain ⟨c, hc, hlat⟩ := exists_nsmul_mem_stdHom S T
  have hap : ∀ i j, ∃ γ : D.host.E, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      toEAf D (t i j) = eToEAf D γ + (K * c) • w := fun i j => exists_rat_add_nsmul _ (K * c) (Nat.mul_pos hK hc)
  choose γ w hw heq using hap
  choose y hy using fun i j => GlobalTheory.LocMod.exists_toEAf_lift (w i j)
  have hidem := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum hE
  let m : WO S T := Matrix.of fun i j => E₂ * y i j
  refine ⟨Matrix.of γ, c • m, hlat m ?_ ?_, ?_, ?_⟩
  · ext i j
    simp only [m, Matrix.map_apply, Matrix.of_apply, map_mul, hinf, zero_mul, Matrix.zero_apply]
  · intro i j
    simp only [m, Matrix.of_apply, map_mul, hy]
    exact mul_mem (GlobalTheory.ExportSeries.toEAf_mem_intAf_of_idem hidem) (hw i j)
  · intro i j
    simp only [m, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    linear_combination ((c : AE D) * y i j) * hidem
  · ext i j
    have hfin : finPart D (t i j - incA D (γ i j) - (K * c) • y i j) = 0 := by
      have h0 : toEAf D (t i j - incA D (γ i j) - (K * c) • y i j) = 0 := by
        rw [map_sub, map_sub, nsmul_eq_mul, map_mul, map_natCast, GlobalTheory.IdemIntegral.toEAf_incA, hy, heq i j,
          nsmul_eq_mul]
        abel
      unfold toEAf at h0
      rw [RingHom.comp_apply] at h0
      exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective (h0.trans (map_zero _).symm)
    have hz := mul_eq_zero_of_parts hinf hfin
    rw [mul_sub, mul_sub, sub_sub, sub_eq_zero, ht i j] at hz
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, m, Matrix.of_apply]
    rw [hz]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring

theorem eq_of_rat : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q →
    ∀ Φ₁ Φ₂ : WO S T → ℂ, IsSBHalf E₂ (stdHom S T) Φ₁ → IsSBHalf E₂ (stdHom S T) Φ₂ →
    (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      Φ₁ (γ.map fun a => E₂ * incA D a) = Φ₂ (γ.map fun a => E₂ * incA D a)) → Φ₁ = Φ₂ := by
  intro D S T Q E₂ hE Φ₁ Φ₂ h₁ h₂ hrat
  obtain ⟨s₁, k₁, hk₁, inv₁, -⟩ := h₁
  obtain ⟨s₂, k₂, hk₂, inv₂, -⟩ := h₂
  funext t
  by_cases ht : IsHalf E₂ t
  · obtain ⟨γ, u, hu, huh, rfl⟩ := exists_half_approx hE (k₁ * k₂) (Nat.mul_pos hk₁ hk₂) t ht
    have half_smul : ∀ n : ℕ, IsHalf E₂ (n • u) := fun n i j => by
      simp only [Matrix.smul_apply, nsmul_eq_mul]
      rw [mul_left_comm, huh i j]
    have e1 : Φ₁ (γ.map (fun a => E₂ * incA D a) + (k₁ * k₂) • u) = Φ₁ (γ.map (fun a => E₂ * incA D a)) := by
      rw [mul_smul]
      exact inv₁ _ (AddSubgroup.nsmul_mem _ hu _) (half_smul _) _
    have e2 : Φ₂ (γ.map (fun a => E₂ * incA D a) + (k₁ * k₂) • u) = Φ₂ (γ.map (fun a => E₂ * incA D a)) := by
      rw [mul_comm, mul_smul]
      exact inv₂ _ (AddSubgroup.nsmul_mem _ hu _) (half_smul _) _
    rw [e1, e2, hrat]
  · have a1 : Φ₁ t = 0 := by
      by_contra h
      exact ht (s₁ t h)
    have a2 : Φ₂ t = 0 := by
      by_contra h
      exact ht (s₂ t h)
    rw [a1, a2]

end GlobalTheory.RatHalfDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepCell


set_option maxHeartbeats 4000000 in
theorem cell_collapse : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) ρ₁ μ₁ ρ₂ μ₂, IsNormAt (c.V (j + 1)) (jacGrp (c.jac j (σ + 1) h).d) (v.N (j + 1)) (· ∈ w.Q) ρ₁ μ₁ → IsNormAt (c.V (j + 1 + 1)) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) (v.N (j + 1 + 1)) (· ∈ w.Q) ρ₂ μ₂ → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ z, Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) (v.kap j σ h * z) := by
  classical
  intro D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h ρ₁ μ₁ ρ₂ μ₂ hN₁ hN₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf z hz
  change Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ => integ v w j σ h Ψ₁ Ψ₂ φ f q₁.1 q₂.1) z at hz
  change Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
    (fun q₁ q₂ => integ v w j σ h Ψ₁ Ψ₂ φ f q₁.1 q₂.1) (v.kap j σ h * z)
  have hA1 := GlobalTheory.T.doubleStep_integrand_leftInvariant_fourierJacobi_first D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hA2 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_first_offLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hA3 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_first_fixedLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hB := GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_fourierJacobi D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC1 := GlobalTheory.T.doubleStep_integrand_leftInvariant_bessel_second D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC2 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_second_offLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC3 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_second_fixedLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC4 := GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_bessel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  set F := integ v w j σ h Ψ₁ Ψ₂ φ f with hFdef
  obtain ⟨f₁', hf₁', hinn⟩ := hz

  obtain ⟨-, hfc₁, -, -, -, hd₁⟩ := _root_.GlobalTheory.AdelicSplit.adelic_split D (c.V (j + 1))
  obtain ⟨-, hfc₂, -, -, -, hd₂⟩ := _root_.GlobalTheory.AdelicSplit.adelic_split D (c.V (j + 1 + 1))
  have invJ : (c.ρJ j (σ + 1) h).IsInvInvariant := (hd₁ _ _ (c.jac j (σ + 1) h).d).1.2.2 _ (hc.ρJ j (σ + 1) h)
  have invB : (c.ρB (j + 1 + 1) σ (idx_step h)).IsInvInvariant :=
    ((hd₂ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d).2 _ _ (c.bes (j + 1 + 1) σ (idx_step h)).o).2.2 _ (hc.ρB _ _ _)
  obtain ⟨hQc₁, hQ'c₁, hQle₁, hQ'le₁, hcm₁, he₁, -, -, -, hR₁⟩ := _root_.GlobalTheory.FinPl.SetCut.grp_split D (c.V (j + 1)) w.Q
  obtain ⟨hQc₂, hQ'c₂, hQle₂, hQ'le₂, hcm₂, he₂, -, -, -, hR₂⟩ := _root_.GlobalTheory.FinPl.SetCut.grp_split D (c.V (j + 1 + 1)) w.Q
  have splitJ := (hR₁ _ _ (c.jac j (σ + 1) h).d).1
  have splitB := (hR₂ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d).2 _ _ (c.bes (j + 1 + 1) σ (idx_step h)).o
  have hJcl := GlobalTheory.jacGrp_isClosed D _ _ _ (c.jac j (σ + 1) h).d
  have hBcl := GlobalTheory.BesClosed.besGrp_isClosed D _ _ _ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o

  obtain ⟨hJG₁, hJG₁c, hJG₁o⟩ := hv.JG (j + 1) (by omega)
  obtain ⟨hJG₂, hJG₂c, hJG₂o⟩ := hv.JG (j + 1 + 1) (by omega)
  obtain ⟨K₁, K₂, hK₁, hK₁Q, hK₂Q, hK₁c, hK₂c, hK₁o, hK₂o, hK₂, hKK⟩ :=
    _root_.GlobalTheory.CellLevels.levels D _ (v.N (j + 1)) v.gP w.Q (v.JG (j + 1)) (hv.sd _ (by omega)) hVF.disjG hJG₁ hJG₁c hJG₁o
  obtain ⟨K₁', K₂', hK₁', hK₁Q', hK₂Q', hK₁c', hK₂c', hK₁o', hK₂o', hK₂', hKK'⟩ :=
    _root_.GlobalTheory.CellLevels.levels D _ (v.N (j + 1 + 1)) v.gP w.Q (v.JG (j + 1 + 1)) (hv.sd _ (by omega)) hVF.disjG hJG₂ hJG₂c hJG₂o
  have hμ₁K : μ₁ {g | (g : GA D (c.V (j + 1))) ∈ K₁} = 1 := by
    rw [show {g : grpAt (c.V (j + 1)) (· ∈ w.Q) | (g : GA D (c.V (j + 1))) ∈ K₁} =
      {g | InK _ (v.N (j + 1)) (· ∈ w.Q) g.1} from Set.ext fun g => hK₁ g.1]
    exact hN₁.2.2.1
  have hρ₁K : ρ₁ {g | ((g : grpAt (c.V (j + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1))) ∈ K₁} = 1 := by
    rw [show {g : (jacGrp (c.jac j (σ + 1) h).d).subgroupOf (grpAt (c.V (j + 1)) (· ∈ w.Q)) |
      ((g : grpAt (c.V (j + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1))) ∈ K₁} =
      {g | InK _ (v.N (j + 1)) (· ∈ w.Q) g.1.1} from Set.ext fun g => hK₁ g.1.1]
    exact hN₁.2.2.2
  have hμ₂K : μ₂ {g | (g : GA D (c.V (j + 1 + 1))) ∈ K₁'} = 1 := by
    rw [show {g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q) | (g : GA D (c.V (j + 1 + 1))) ∈ K₁'} =
      {g | InK _ (v.N (j + 1 + 1)) (· ∈ w.Q) g.1} from Set.ext fun g => hK₁' g.1]
    exact hN₂.2.2.1
  have hρ₂K : ρ₂ {g | ((g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1 + 1))) ∈ K₁'} = 1 := by
    rw [show {g : (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf
        (grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) |
      ((g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1 + 1))) ∈ K₁'} =
      {g | InK _ (v.N (j + 1 + 1)) (· ∈ w.Q) g.1.1} from Set.ext fun g => hK₁' g.1.1]
    exact hN₂.2.2.2

  have hinner : ∀ q₁ : grpAt (c.V (j + 1)) (· ∈ w.Q), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
      (fun g => F q₁.1 g.1) (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * f₁' q₁) := by
    intro q₁
    have hl : ∀ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o,
        r ∈ GfC (c.V (j + 1 + 1)) → ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 (r * g) = F q₁.1 g :=
      fun r hr _ g _ => hC1 r hr q₁.1 g
    have hr : ∀ k ∈ K₂', ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 (g * k) = F q₁.1 g := by
      intro k hk g _
      obtain ⟨κ, hκ, k', hk', rfl⟩ := (hK₂' k).1 hk
      rw [← mul_assoc, hC3 k' hk', hC2 κ hκ]
    have hs : ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 g ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d
        (c.bes (j + 1 + 1) σ (idx_step h)).o, r ∈ GfC (c.V (j + 1 + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1 + 1)) (· ∈ w.Q),
        ∃ k ∈ K₂', g = r * y * k := by
      intro g hg hne
      obtain ⟨r, hr, hrG, y, hy, κ, hκ, k, hk, e⟩ := hC4 q₁.1 q₁.2 g hg hne
      exact ⟨r, hr, hrG, y, hy, κ * k, (hK₂' _).2 ⟨κ, hκ, k, hk, rfl⟩, e⟩
    have H := _root_.GlobalTheory.CollapseFactor.collapse_factor (GA D (c.V (j + 1 + 1))) (GfC _) (grpAt _ (· ∈ w.Q)) (grpAt _ (· ∉ w.Q))
      (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) K₁' K₂'
      hfc₂ hQc₂ hQ'c₂ hBcl hQle₂ hQ'le₂ hcm₂ he₂ splitB hK₁Q' hK₂Q' hK₁c' hK₂c' hK₁o' hK₂o'
      (c.ρB _ _ _) (c.μf _) ρ₂ μ₂ (hc.ρB _ _ _) (hc.μf _) hN₂.2.1 hN₂.1 invB hμ₂K hρ₂K (F q₁.1) (f₁' q₁) hl hr hs (hinn q₁)
    have e1 : {g : GfC (c.V (j + 1 + 1)) | ∃ a ∈ K₁', ∃ b ∈ K₂', (g : GA D (c.V (j + 1 + 1))) = a * b} =
        {g | g.1 ∈ v.K (j + 1 + 1)} := Set.ext fun g => hKK' g.1
    have e2 : {g : (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf
        (GfC (c.V (j + 1 + 1))) | ∃ a ∈ K₁', ∃ b ∈ K₂', ((g : GfC (c.V (j + 1 + 1))) : GA D (c.V (j + 1 + 1))) = a * b} =
        {g | g.1.1 ∈ v.K (j + 1 + 1)} := Set.ext fun g => hKK' g.1.1
    rw [e1, e2] at H
    exact H

  haveI : LocallyCompactSpace (GfC (c.V (j + 1 + 1))) := hfc₂.locallyCompactSpace
  haveI := hc.μf (j + 1 + 1)
  haveI := hc.ρB (j + 1 + 1) σ (idx_step h)
  haveI := invB
  have hBcl' : IsClosed (((besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf
      (GfC (c.V (j + 1 + 1))) : Subgroup _) : Set (GfC (c.V (j + 1 + 1)))) := hBcl.preimage continuous_subtype_val
  have huniq : ∀ (Φ : GfC (c.V (j + 1 + 1)) → ℂ) (z₁ z₂ : ℂ), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h))
      (c.μf (j + 1 + 1)) Φ z₁ → IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) Φ z₂ → z₁ = z₂ :=
    fun Φ z₁ z₂ h1 h2 => IsQuotIntL1.unique hBcl' h1 h2

  have hex : ∀ q : GfC (c.V (j + 1)), ∃ z', IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
      (fun g => F q.1 g.1) z' := by
    intro q
    by_cases hq : ∃ q₂, F q.1 q₂ ≠ 0
    · obtain ⟨q₂, hq₂⟩ := hq
      obtain ⟨r, hr, -, y, hy, κ, hκ, k, hk, e⟩ := hB q.1 q.2 q₂ hq₂
      have e' : F q.1 = F y := funext fun q₂ => by rw [e, ← mul_assoc, hA3 k hk, hA2 κ hκ, hA1 r hr]
      exact ⟨_, by rw [e']; exact hinner ⟨y, hy⟩⟩
    · push_neg at hq
      refine ⟨0, ?_⟩
      have e : (fun g : GfC (c.V (j + 1 + 1)) => F q.1 g.1) = 0 := funext fun g => hq g.1
      rw [e]
      exact IsQuotIntL1.zero
  let fo : GA D (c.V (j + 1)) → ℂ := fun y => if hy : y ∈ GfC (c.V (j + 1)) then (hex ⟨y, hy⟩).choose else 0
  have hfo_spec : ∀ y (hy : y ∈ GfC (c.V (j + 1))), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
      (fun g => F y g.1) (fo y) := by
    intro y hy
    have e : fo y = (hex ⟨y, hy⟩).choose := dif_pos hy
    rw [e]
    exact (hex ⟨y, hy⟩).choose_spec
  have hleft : ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) → ∀ g ∈ GfC (c.V (j + 1)), fo (r * g) = fo g := by
    intro r hr hrG g hg
    have e : F (r * g) = F g := funext fun q₂ => hA1 r hr g q₂
    have h1 := hfo_spec _ (mul_mem hrG hg)
    rw [e] at h1
    exact huniq _ _ _ h1 (hfo_spec g hg)
  have hright : ∀ k ∈ K₂, ∀ g ∈ GfC (c.V (j + 1)), fo (g * k) = fo g := by
    intro k hk g hg
    have hkG : k ∈ GfC (c.V (j + 1)) := hQ'le₁ (hK₂Q hk)
    obtain ⟨κ, hκ, k', hk', e0⟩ := (hK₂ k).1 hk
    have e : F (g * k) = F g := funext fun q₂ => by rw [e0, ← mul_assoc, hA3 k' hk', hA2 κ hκ]
    have h1 := hfo_spec _ (mul_mem hg hkG)
    rw [e] at h1
    exact huniq _ _ _ h1 (hfo_spec g hg)
  have hsupp : ∀ g ∈ GfC (c.V (j + 1)), fo g ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) ∧
      ∃ y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∃ k ∈ K₂, g = r * y * k := by
    intro g hg hne
    have hq : ∃ q₂, F g q₂ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hne
      have e : (fun g' : GfC (c.V (j + 1 + 1)) => F g g'.1) = 0 := funext fun g' => hcon g'.1
      have h0 := hfo_spec g hg
      rw [e] at h0
      exact huniq _ _ _ h0 IsQuotIntL1.zero
    obtain ⟨q₂, hq₂⟩ := hq
    obtain ⟨r, hr, hrG, y, hy, κ, hκ, k, hk, e⟩ := hB g hg q₂ hq₂
    exact ⟨r, hr, hrG, y, hy, κ * k, (hK₂ _).2 ⟨κ, hκ, k, hk, rfl⟩, e⟩
  have hint : IsQuotIntL1 ρ₁ μ₁ (fun y : grpAt (c.V (j + 1)) (· ∈ w.Q) => fo y.1)
      (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * z) := by
    have e : (fun y : grpAt (c.V (j + 1)) (· ∈ w.Q) => fo y.1) =
        v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) • f₁' := funext fun y => by
      rw [Pi.smul_apply, smul_eq_mul]
      exact huniq _ _ _ (hfo_spec y.1 (hQle₁ y.2)) (hinner y)
    rw [e]
    exact hf₁'.smul _
  have Hout := _root_.GlobalTheory.CollapseFactor.collapse_factor (GA D (c.V (j + 1))) (GfC _) (grpAt _ (· ∈ w.Q)) (grpAt _ (· ∉ w.Q))
    (jacGrp (c.jac j (σ + 1) h).d) K₁ K₂ hfc₁ hQc₁ hQ'c₁ hJcl hQle₁ hQ'le₁ hcm₁ he₁ splitJ hK₁Q hK₂Q hK₁c hK₂c hK₁o hK₂o
    (c.ρJ j (σ + 1) h) (c.μf _) ρ₁ μ₁ (hc.ρJ _ _ _) (hc.μf _) hN₁.2.1 hN₁.1 invJ hμ₁K hρ₁K fo _ hleft hright hsupp hint
  have e1 : {g : GfC (c.V (j + 1)) | ∃ a ∈ K₁, ∃ b ∈ K₂, (g : GA D (c.V (j + 1))) = a * b} =
      {g | g.1 ∈ v.K (j + 1)} := Set.ext fun g => hKK g.1
  have e2 : {g : (jacGrp (c.jac j (σ + 1) h).d).subgroupOf (GfC (c.V (j + 1))) |
      ∃ a ∈ K₁, ∃ b ∈ K₂, ((g : GfC (c.V (j + 1))) : GA D (c.V (j + 1))) = a * b} =
      {g | g.1.1 ∈ v.K (j + 1)} := Set.ext fun g => hKK g.1.1
  rw [e1, e2] at Hout
  refine ⟨fun q => fo q.1, ?_, fun q => hfo_spec q.1 q.2⟩
  have ek : v.kap j σ h * z = v.vr (j + 1) _ (c.ρJ j (σ + 1) h) * (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * z) := by
    unfold VCom.kap; ring
  rw [ek]
  exact Hout

end GlobalTheory.DStepCell

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportAndValueAtFixedLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSawLaws

open GlobalTheory.LocMod

theorem gsupp2_all (D : D7) : GlobalTheory.LocMod.GSupp2 D := by
  have hFL : FlatLaw D := _root_.GlobalTheory.Unf.Flat.flatLaw D
  have hFLs : GlobalTheory.FinPl.FlatLaws D := _root_.GlobalTheory.FinPl.flatLaws_all D
  have hOm : OmLoc D := _root_.GlobalTheory.LocOm.omLoc D
  have hBF : FlatBF D := _root_.GlobalTheory.FlatBFLoc.flatBF_of_laws D hFL hFLs hOm
  have hFB : FlatFB D := _root_.GlobalTheory.LocMod.flatFB_holds D hFL hFLs hOm
  have hC : ContrLoc D := _root_.GlobalTheory.ContrLocProof.contrLoc D GlobalTheory.LocFlat.contrFactor
  have hS : GlobalTheory.LocFlat.SymCollapse := GlobalTheory.LocFlat.symCollapse_of_allPositions GlobalTheory.SymChain.allPositions_holds
  intro k _ _ _ _ p s κ S t _ _ ψ hψ j c H σ B J B' F s₁ s₂ l vL hc T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ hΦ₁ hΦ₂ h hh hne
  exact _root_.GlobalTheory.LocMod.GSuppTwo.gsupp2_std D hOm hBF hFB hC hS k p s κ S t ψ s₁.weil.std hψ j c H σ B J B' F s₁ s₂ l vL hc T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ hΦ₁ hΦ₂ h hh hne

theorem gsupp1_all (D : D7) : GlobalTheory.LocMod.GSupp1 D :=
  _root_.GlobalTheory.LocMod.SuppFirst.gsupp1 D (_root_.GlobalTheory.LocOm.omLoc D)
    (_root_.GlobalTheory.FlatBFLoc.flatBF_of_laws D (_root_.GlobalTheory.Unf.Flat.flatLaw D) (_root_.GlobalTheory.FinPl.flatLaws_all D) (_root_.GlobalTheory.LocOm.omLoc D))
    (GlobalTheory.LocFlat.symCollapse_of_allPositions GlobalTheory.SymChain.allPositions_holds)

theorem gLaws : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → (∀ i, (G i).Chars t) → GSupp (t := t) (v.withCG a) ∧ GValue (t := t) (v.withCG a) := by
  intro D c v n G hc hv hG
  obtain ⟨a, ha, hval⟩ := GlobalTheory.T.seeSaw_unfoldedValue_commonConstants_fixedLevel D c v n G hc hv hG
  refine ⟨a, ha, fun t ht hW hch => ⟨?_, hval t ht hW⟩⟩
  have hs : GSupp (t := t) v :=
    GlobalTheory.T.seeSaw_unfoldedSupport_fixedLevelPlaces D c v n G hc hv hG (gsupp1_all D) (gsupp2_all D) (_root_.GlobalTheory.Unf.Flat.flatLaw D) t ht hch
  exact hs

end GlobalTheory.SeeSawLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartLevelStandardBasePointEqMemberStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroChartLevel_standardBasePoint_eq_member : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ x, x ∈ (A.K 0 (Nat.zero_le _) β).lev.U ↔ x ∈ (C.forms u).to0.cls0.lev.U := by
  first | exact @GlobalTheory.ZeroLevel.lev_zero_std | exact GlobalTheory.ZeroLevel.lev_zero_std | (intros; apply GlobalTheory.ZeroLevel.lev_zero_std <;> assumption)
end

