module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0011
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapBound
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0009
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothVectorsDiscreteSeriesGlModuleStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapExistsFunctionalStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_gap_exists_functional : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∃ l, IsBeL R z π μW μN l := by
  first | exact @CompanionTheory.FamilyDerivativeExpansion.BeL.exists_normalised_bessel_map | exact CompanionTheory.FamilyDerivativeExpansion.BeL.exists_normalised_bessel_map | (intros; apply CompanionTheory.FamilyDerivativeExpansion.BeL.exists_normalised_bessel_map <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapBoundDualStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_orbital_integral_factors_through_right_functional : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ Bb : R.H → Wp → Wq → Wp, (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = Bb x (X (l' y)) c := by
  first | exact @GlobalTheory.besselJ_coef_through_right | exact GlobalTheory.besselJ_coef_through_right | (intros; apply GlobalTheory.besselJ_coef_through_right <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapBoundStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_orbital_integral_factors_through_left_functional : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ A : R.H → Wq → Wq → Wp, (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = A y (ContinuousLinearMap.adjoint X (l x)) c := by
  first | exact @GlobalTheory.BesselFirstLeft.bessel_integrate_left | exact GlobalTheory.BesselFirstLeft.bessel_integrate_left | (intros; apply GlobalTheory.BesselFirstLeft.bessel_integrate_left <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyEndomorphismsModular
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem isMod_smooth_of_isDS : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), 1 ≤ k → R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → IsMod ε E mu := by
  intro hH k r ε mu R hk hDS Q E hQ hE
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hU : IsUnit Q := by
    have h1 : Q * star Q = 1 := (Matrix.mem_unitaryGroup_iff).1 hQ.2
    have h2 : star Q * Q = 1 := (Matrix.mem_unitaryGroup_iff').1 hQ.2
    exact ⟨⟨Q, star Q, h1, h2⟩, rfl⟩
  have hG : Formalism.REAL.GlRel E := (GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hDS Q E hU hE).1
  refine ⟨hG, GlobalTheory.T.cayley_endomorphisms_unitary hK k r ε mu R hDS Q E hQ hE, ?_⟩
  exact _root_.GlobalTheory.CapelliCasimir.cas_of_capelli R.smSub (2 * r + k + 1) E mu (by omega) hG
    (GlobalTheory.T.quantum_determinant_eigenvalue hH k r ε mu R hDS Q E hU hE)

end GlobalTheory
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DualTensorBesselMoment
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace BesselProjectorValue

lemma star_Hpk (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    star (Formalism.QuantumDeterminants.Hpk k r i j) = Formalism.QuantumDeterminants.Hpk k r i j := by
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

lemma ev_flat {k r : ℕ} (R : Rep k r) (f : Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1) → R.H) :
    ev (Formalism.QuantumDeterminants.Hpk k r) R (flat k r f) x = ∑ j, f j • x j := by
  unfold ev
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h1 : ∀ i, star (flat k r f i) = ∑ p, f p * Formalism.QuantumDeterminants.Hpk k r p i := by
    intro i
    simp [flat, Formalism.QuantumDeterminants.herm, dotProduct, Matrix.mulVec_single_one, Matrix.col, star_Hpk]
  simp only [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h2 : ∀ p, ∑ i, f p * Formalism.QuantumDeterminants.Hpk k r p i * Formalism.QuantumDeterminants.Hpk k r i j = f p * (1 : Mx k r) p j := by
    intro p
    rw [← Formalism.QuantumDeterminants.GBasic.Hpk_sq k r, Matrix.mul_apply, Finset.mul_sum]
    simp only [mul_assoc]
  simp only [h2, Matrix.one_apply]
  simp

lemma sum_frame {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g)
    (f : Fin n → ℂ) (x : Fin n → V) :
    ∑ j, f j • x j = ∑ d, (g⁻¹ *ᵥ f) d • ∑ c, g c d • x c := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have : (g *ᵥ (g⁻¹ *ᵥ f)) j = f j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
  rw [← this]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

lemma sum_coframe {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g)
    (ω : Fin n → ℂ) (v : V) (c : Fin n) :
    ∑ d, g⁻¹ d c • ((gᵀ *ᵥ ω) d • v) = ω c • v := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  simp only [smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have : ((g⁻¹)ᵀ *ᵥ (gᵀ *ᵥ ω)) c = ω c := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.transpose_one,
      Matrix.one_mulVec]
  rw [← this]
  rfl

end BesselProjectorValue


open BesselProjectorValue in
theorem bessel_ev_projector_value : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (RI : Fin (2 * r + k + 1) → Rep k r) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp), 1 ≤ k → R.IsDG ε mu → (∀ s, (RI s).IsDG ε (mu - Pi.single s 1)) → TensRaw dualM R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π l → ∀ s, ∃ c : ℂ, ‖c‖ = Formalism.QuantumDeterminants.Tz k r z * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ v ∈ R.sm, l (ev (Formalism.QuantumDeterminants.Hpk k r) R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (fun c' => io s c' (∑ d, pr s d (tm R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d)))) = c • l v := by
  intro hy k r ε mu R RI io pr Wp _ _ _ _ z π u μW μN μG νq l hk hR hRI hT hS hB s
  have hK : PI.KFinSmooth := hy.1.2.2.1
  obtain ⟨hz, hTz, ⟨u₀, hu₀⟩, hcap, -⟩ := hS
  have hπ1 : π 1 = 1 := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hTz hu₀).1
  obtain ⟨g, hg, -⟩ := hu₀
  obtain ⟨hgu, hN, ⟨hfr, hunit⟩, hf, hω⟩ := _root_.GlobalTheory.CapFrame.frame_matrix_units k r z g hz hTz hg
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hgu
  have hQ : IsUnit g⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 hgu
  have hgi : g⁻¹⁻¹ = g := Matrix.nonsing_inv_nonsing_inv g hd
  obtain ⟨E, hE, hEg⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε mu R hR g⁻¹ hQ
  choose F hF hFg using fun t => GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε _ (RI t) (hRI t) g⁻¹ hQ
  obtain ⟨io', pr', hcomm, -, hsum, -, -, hio, hpr⟩ :=
    GlobalTheory.T.dual_tensor_cayley_compatible hK k r ε mu R hR RI _ io pr g⁻¹ E F hRI hT hQ hE hF
  have hn : 2 ≤ 2 * r + k + 1 := by omega
  have hqE := GlobalTheory.T.quantum_determinant_eigenvalue hy k r ε mu R hR g⁻¹ E hQ hE
  have hcE := _root_.GlobalTheory.CapelliCasimir.cas_of_capelli _ _ E mu hn hEg hqE
  have hcF := fun t => _root_.GlobalTheory.CapelliCasimir.cas_of_capelli _ _ (F t) _ hn (hFg t)
    (GlobalTheory.T.quantum_determinant_eigenvalue hy k r ε _ (RI t) (hRI t) g⁻¹ (F t) hQ (hF t))
  have hsp := fun t => _root_.GlobalTheory.splitCas_on_summand _ _ _ E (F t) (io' t) mu t hcE (hcF t) (hcomm t)
  let L : R.smSub →ₗ[ℂ] Wp :=
    { toFun := fun v => l v
      map_add' := fun v w => hB.1 _ v.2 _ w.2
      map_smul' := fun c v => hB.2.1 c _ v.2 }
  have hL : ∀ v : R.smSub, L v = l v := fun _ => rfl
  have hE' : ∀ a b (v : R.smSub), ((E a b v : R.smSub) : R.H) = R.dC (g * Matrix.single a b 1 * g⁻¹) v := by
    intro a b v
    rw [hE a b v, hgi]
  obtain ⟨c, hc, hcv⟩ := _root_.GlobalTheory.capelli_projector_entry_value R.smSub Wp k r E L
    (fun a b => Formalism.QuantumDeterminants.ell k r z (g * Matrix.single a b 1 * g⁻¹) - star (Formalism.QuantumDeterminants.ell k r z
      (-((Formalism.QuantumDeterminants.Hpk k r) * (g * Matrix.single a b (1 : ℂ) * g⁻¹)ᴴ * (Formalism.QuantumDeterminants.Hpk k r)))))
    (Real.sqrt (Formalism.QuantumDeterminants.Tz k r z)) hk hEg
    (fun a b hab hnot => ⟨fun v => by
      rw [hL, hL, hE']
      exact GlobalTheory.T.bessel_functional_lie_triangular_eq_character_smul hK k r ε mu R hR Wp z π l hz (fun x => by rw [hπ1]; rfl) hB _ (hN a b hab hnot).1 _ v.2,
      (hN a b hab hnot).2⟩)
    mu u (fun i j => Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (Formalism.FourierDecayAlt.Q.unitB (Formalism.QuantumDeterminants.Hpk k r)
      (fun i : Fin k => g *ᵥ Pi.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) 1) i j))
    hR.1.1.injective hqE
    (fun i j v => by
      rw [hL, hL, hE', hunit]
      exact GlobalTheory.T.bessel_frame_entry_relation hK k r ε mu R hR Wp z π l g hz hTz hg hB i j _ v.2)
    (fun w x => hcap _ hfr w x) s
  set a : ℂ := (if r = 0 then -((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) else 1) with ha
  set b : ℂ := (if r = 0 then ((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) else 1) with hb
  set i₀ : Fin (2 * r + k + 1) := (if r = 0 then Fin.last (2 * r + k) else 0) with hi₀
  have hf' : g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z 0 = b • Pi.single i₀ 1 := by
    rw [hf, hb, hi₀]
    split_ifs <;> simp
  refine ⟨b * c * a, ?_, fun v hv => ?_⟩
  · rw [norm_mul, norm_mul, hc, ha, hb]
    have hsq : Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) ^ 2 = Formalism.QuantumDeterminants.Tz k r z := Real.sq_sqrt hTz.le
    have hab : |Real.sqrt (Formalism.QuantumDeterminants.Tz k r z)| = Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) :=
      abs_of_nonneg (Real.sqrt_nonneg _)
    split_ifs
    · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, hab]
      generalize ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) = P
      linear_combination P * hsq
    · rw [hsq, norm_one, one_mul, mul_one]
  · let v' : R.smSub := ⟨v, hv⟩
    let x : Fin (2 * r + k + 1) → R.smSub := Pi.single (Fin.last (2 * r + k)) (a • v')
    have hx : ∀ d, ((x d : R.smSub) : R.H) = (gᵀ *ᵥ flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) d • v := by
      intro d
      rw [hω]
      by_cases h : d = Fin.last (2 * r + k)
      · subst h; simp [x, v']
      · simp [x, Pi.single_eq_of_ne h]
    have hp : ((pr' s x : (RI s).smSub) : (RI s).H) =
        ∑ d, pr s d (tm R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d) := by
      rw [hpr]
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [hx]
      rw [sum_coframe g hgu]
      rfl
    have hmain := hcv (a • v') (fun t => io' t (pr' t x)) (fun t => hsp t _) (hsum x)
    rw [ev_flat, sum_frame g hgu, ← hp, hf']
    have h3 : ∀ d, ∑ c', g c' d • io s c' ((pr' s x : (RI s).smSub) : (RI s).H) =
        ((io' s (pr' s x) d : R.smSub) : R.H) := by
      intro d
      rw [hio, hgi]
    simp only [h3]
    rw [Finset.sum_eq_single i₀ (fun d _ hd => by simp [Pi.single_eq_of_ne hd]) (by simp)]
    have h4 : (b • Pi.single i₀ (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i₀ = b := by simp
    rw [h4]
    have h5 : l (b • ((io' s (pr' s x) i₀ : R.smSub) : R.H)) = b • L (io' s (pr' s x) i₀) :=
      hB.2.1 b _ (io' s (pr' s x) i₀).2
    rw [h5, hmain, map_smul, hL, smul_smul, smul_smul]

end GlobalTheory
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupBesselGrowth
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomMass

theorem integrand_eq {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {d : ℝ} (hd : 0 ≤ d) (v : Wp) :
    ENNReal.ofReal (1 * (d * ‖v‖ ^ 2)) = ((‖((Real.sqrt d : ℝ) : ℂ) • v‖₊ : ENNReal)) ^ 2 := by
  have hn : ‖((Real.sqrt d : ℝ) : ℂ) • v‖ = Real.sqrt d * ‖v‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg d)]
  have hc : ((‖((Real.sqrt d : ℝ) : ℂ) • v‖₊ : ENNReal)) = ENNReal.ofReal (Real.sqrt d * ‖v‖) := by
    rw [← hn, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  rw [hc, ← ENNReal.ofReal_pow (mul_nonneg (Real.sqrt_nonneg d) (norm_nonneg v)), mul_pow,
    Real.sq_sqrt hd, one_mul]

theorem mom_mass : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν ≤ q0 → (∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (‖w‖ ^ 2)) ∧ (NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧ ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν
  obtain ⟨hNum, hFam, hSide, hSF⟩ := hS
  obtain ⟨hBeL, hdg, hfd⟩ := hSF ν hν
  have hDG : (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) := hFam ν hν
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hGap0, hGapOK, _, hq0h, _⟩ := hNum
  have hνa : ∀ a, |(ν a : ℝ)| ≤ (q0 : ℝ) := by
    intro a
    have h1 : (ν a).natAbs ≤ BranchingSupport.n1 ν :=
      Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
    have h2 : ((ν a).natAbs : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast h1.trans hν
    have h3 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h3]
    exact h2
  have hgap : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (h / 4) := by
    intro a c hac
    have h0 := hGap0 a c hac
    obtain ⟨ha1, ha2⟩ := abs_le.mp (hνa a)
    obtain ⟨hc1, hc2⟩ := abs_le.mp (hνa c)
    have hd : |(ν c : ℝ) - ν a| ≤ 2 * (q0 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
    have hx := abs_sub_abs_le_abs_sub (lam a - lam c) ((ν c : ℝ) - ν a)
    have e : (lam a - lam c) - ((ν c : ℝ) - ν a) = (lam a + ν a) - (lam c + ν c) := by ring
    rw [e] at hx
    have hq : (0 : ℝ) ≤ q0 := Nat.cast_nonneg q0
    show h / 4 ≤ |(lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ))|
    linarith
  have hIso : BranchingSupport.NzOn (R ν) (l ν) →
      BranchingSupport.IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) := fun hNz =>
    Gp91.GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH k r _ _ (h / 4) (R ν) Wp z π u μW μN μG νq (l ν) (dg ν) hDG hgap hGapOK hSide hBeL
      hfd hNz
  have hEq : BranchingSupport.NzOn (R ν) (l ν) → ∀ w ∈ (R ν).sm,
      ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2) := by
    intro hNz w hw
    calc ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq
        = ∫⁻ x, ((‖((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν ((R ν).σ (Matrix.of x) w)‖₊ : ENNReal)) ^ 2 ∂νq :=
          MeasureTheory.lintegral_congr (fun x => integrand_eq hdg.le _)
      _ = ENNReal.ofReal (‖w‖ ^ 2) := (hIso hNz).2 w hw
  refine ⟨fun w hw => ?_, fun hNz => ⟨hIso hNz, hEq hNz⟩⟩
  by_cases hNz : BranchingSupport.NzOn (R ν) (l ν)
  · exact (hEq hNz w hw).le
  · have hz : ∀ v ∈ (R ν).sm, l ν v = 0 := by
      intro v hv
      by_contra hne
      exact hNz ⟨v, hv, hne⟩
    obtain ⟨_, _, _, _, hW, hN, hG, hQ⟩ := hSide
    obtain ⟨hmS, hmS0⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hmS hmS0 hQ
    have hKF : PI.KFinSmooth := hH.1.2.2.1
    have hinv := (Gp91.GlobalTheory.rep_basic_of_isDS hKF k r _ _ (R ν) hDG).2.2.2.1
    have h0 : ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = 0 := by
      calc ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq
          = ∫⁻ _x, (0 : ENNReal) ∂νq :=
            MeasureTheory.lintegral_congr_ae (hae.mono fun x hx => by simp [hz _ (hinv _ hx w hw)])
        _ = 0 := MeasureTheory.lintegral_zero
    rw [h0]
    exact zero_le

end GlobalTheory.MomMass
end Gp91
end

