module

public import Mathlib
public import Formalism.HermitianCurvature.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0025
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableBesselFunctionContinuousFami
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory


set_option synthInstance.maxSize 2000 in
theorem besselJ_family_aestronglyMeasurable : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (α : Type) [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α] (μ : Measure α) [SFinite μ] (U : Set α) (γ : α → B.Mat k r) (V : Set (B.Mat k r)) (H : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U → ContinuousOn γ U → (∀ x ∈ U, ∀ q, Bs.inSS q → B.sgs q (γ x) ∈ V) → ContinuousOn H V → AEStronglyMeasurable (fun x => B.JF Bs H (γ x)) (μ.restrict U) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs α _ _ _ _ μ _ U γ V H hU hγ hV hH
  set S : Set (B.SS k r) := {p | Bs.inSS p} with hS
  have hWc := (P.weyl_subgroup_closed k r Bs.z).closed
  have hWc' := (P.weyl_subgroup_closed k r Bs.z').closed
  have hNc := (P.unipotent_radical_closed k r).closed
  have hSc : IsClosed S := by
    have e : S = (fun p : B.SS k r => (p.1.1 : B.Mat k r)) ⁻¹' (UWset k r Bs.z) ∩
        ((fun p : B.SS k r => (p.1.2 : B.Mat k r)) ⁻¹' (Nset k r) ∩
          ((fun p : B.SS k r => (p.2.1 : B.Mat k r)) ⁻¹' (UWset k r Bs.z') ∩
            (fun p : B.SS k r => (p.2.2 : B.Mat k r)) ⁻¹' (Nset k r))) := by
      ext p; rfl
    rw [e]
    exact (hWc.preimage continuous_fst.fst).inter ((hNc.preimage continuous_fst.snd).inter
      ((hWc'.preimage continuous_snd.fst).inter (hNc.preimage continuous_snd.snd)))
  have hxi : Continuous fun p : B.SS k r => B.xiTau Bs (1, 1) p :=
    (P.B7.continuous_xi Bs).comp (by fun_prop : Continuous fun p : B.SS k r => (((1 : ℝ), (1 : ℝ)), p))
  have hπ : ContinuousOn (fun p : B.SS k r => Bs.π (Matrix.of p.1.1)) S :=
    Bs.π_cont.comp (continuous_fst.fst).continuousOn (fun p hp => hp.1)
  have hinv1 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.fst).continuousOn (fun p hp => hp.1.1)
  have hinv2 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.snd).continuousOn (fun p hp => hp.2.1.1)
  have hinv3 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_snd.fst).continuousOn (fun p hp => hp.2.2.1.1)
  have hπ' : ContinuousOn (fun p : B.SS k r => Bs.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    Bs.π'_cont.comp hinv3 (fun p hp => Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.2.2.1)
  have hc4 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) S :=
    (continuous_snd.snd).continuousOn
  have hc5 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) S :=
    (continuous_snd.fst).continuousOn
  have up : ∀ {β : Type} [TopologicalSpace β] {f : B.SS k r → β}, ContinuousOn f S →
      ContinuousOn (fun y : α × B.SS k r => f y.2) (U ×ˢ S) :=
    fun hf => hf.comp continuous_snd.continuousOn (fun y hy => hy.2)
  have hγ' : ContinuousOn (fun y : α × B.SS k r => γ y.1) (U ×ˢ S) :=
    hγ.comp continuous_fst.continuousOn (fun y hy => hy.1)
  have hsgs : ContinuousOn (fun y : α × B.SS k r => B.sgs y.2 (γ y.1)) (U ×ˢ S) :=
    (((((up hinv1).mul (up hinv2)).mul hγ').mul (up hc4)).mul (up hc5))
  have hFs : ContinuousOn (fun y : α × B.SS k r => H (B.sgs y.2 (γ y.1))) (U ×ˢ S) :=
    hH.comp hsgs (fun y hy => hV y.1 hy.1 y.2 hy.2)
  have hcont : ContinuousOn (fun y : α × B.SS k r => D.orbIntegrand Bs (γ y.1) H y.2) (U ×ˢ S) := by
    unfold D.orbIntegrand B.rho
    exact (up hxi.continuousOn).smul ((up hπ).clm_comp (hFs.clm_comp (up hπ')))
  have hW : SigmaFinite Bs.μW := P.Dx2.MN.sigma_of_haar Bs.haarW
  have hW' : SigmaFinite Bs.μW' := P.Dx2.MN.sigma_of_haar Bs.haarW'
  have hN : SigmaFinite Bs.μN := P.Dx2.MN.sigma_of_haar Bs.haarN
  have hsf : SFinite Bs.μSS := by unfold B.RealPlaceData.μSS; infer_instance
  have h1 := hcont.aestronglyMeasurable (μ := μ.prod Bs.μSS) (hU.measurableSet.prod hSc.measurableSet)
  have hae : ∀ᵐ p ∂Bs.μSS, p ∈ S := P.Dx2.OrbJ.ae_inSS Bs
  rw [← Measure.prod_restrict, Measure.restrict_eq_self_of_ae_mem hae] at h1
  have h2 := h1.integral_prod_right'
  have e : (fun x => B.JF Bs H (γ x)) = fun x => ∫ p, D.orbIntegrand Bs (γ x) H p ∂Bs.μSS := by
    funext x
    rw [← P.bessel_function_trivial_index k r Wp Wq Bs H (γ x)]
    rfl
  rw [e]
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConjEntrySmulCapelliEigenSum
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem conj_entry_smul_eigenSum : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ s t, s ≠ t → 2 * ((d : ℕ) : ℝ) < |lam s - lam t|) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d + 1 : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (fun g => star (g i j) • F g) g = ∑ i, Fi i g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam d A i j F hsep hF
  obtain ⟨N₀, Fi, ν, hν, hcl, heig, hsum⟩ := hF
  obtain ⟨⟨co, hco⟩, -⟩ := _root_.GlobalTheory.unitary_conj_entry_and_inv_entry k r i j
  refine _root_.GlobalTheory.capelli_eigenSum_linearCombination k r Wp Wq lam (d + 1) (A - 1)
    (Fin N₀ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) Finset.univ
    (fun x => co x.2.1 x.2.2) (fun x g => g⁻¹ x.2.1 x.2.2 • Fi x.1 g)
    (fun g => star (g i j) • F g) ?_ ?_
  · rintro ⟨x, a, b⟩ -
    refine ⟨d + 1, A - 1, le_rfl, le_rfl, ?_⟩
    have hinj : Function.Injective (fun s => lam s + (ν x s : ℝ)) := by
      intro s t hst
      by_contra hne
      have h1 := hsep s t hne
      have h2 : |(ν x s : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν x s
      have h3 : |(ν x t : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν x t
      have h4 : lam s - lam t = (ν x t : ℝ) - (ν x s : ℝ) := by
        simp only at hst
        linarith
      rw [h4] at h1
      have h5 := abs_sub (ν x t : ℝ) (ν x s : ℝ)
      linarith
    obtain ⟨G, hG1, hG2, hG3⟩ := _root_.GlobalTheory.inv_entry_smul_eigen_split k r Wp Wq (fun s => lam s + (ν x s : ℝ)) A a b
      (Fi x) hinj (hcl x) (by
        intro Y g hg
        rw [heig x Y g hg]
        simp only [add_assoc])
    refine ⟨2 * r + k + 1, G, fun t s => ν x s - if s = t then 1 else 0, ?_, hG1, ?_, hG3⟩
    · intro t s
      have h := abs_le.mp (hν x s)
      rw [abs_le]
      push_cast
      split_ifs <;> constructor <;> omega
    · intro t Y g hg
      rw [hG2 t Y g hg]
      congr 2
      refine Finset.prod_congr rfl fun s _ => ?_
      push_cast
      split_ifs <;> ring
  · intro g hg
    beta_reduce
    rw [hco g hg, hsum g hg, Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContinuousOfIsPolyDeg
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Filter Topology

namespace GlobalTheory.HatNF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open MeasureTheory Filter Topology in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma norm_opApply_le_of_polynomial_coeffs_lemma {k r : ℕ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (A : ℝ)
    (Θ : List (_root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq))
    (hΘ : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (B : ℝ), _root_.Formalism.FourierDecayAlt.B.CCle A o G B →
      ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, ‖_root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖ ≤ C * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by
  induction Θ with
  | nil => exact ⟨0, le_rfl, fun G B hG g _ => by
      simp [_root_.Formalism.FourierDecayAlt.B.opApply]⟩
  | cons T Θ ih =>
    obtain ⟨C₁, hC₁0, hC₁⟩ := ih (fun S hS => hΘ S (List.mem_cons_of_mem _ hS))
    obtain ⟨hlen, Q, hQ, hcoef⟩ := hΘ T List.mem_cons_self
    obtain ⟨CQ, hCQ0, hCQ⟩ := _root_.PI.UnitaryCorollaryDerivatives.pb_nonneg (_root_.PI.UnitaryCorollaryDerivatives.pb_poly hQ) 0
    have hunit : ∀ X ∈ List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word, _root_.Formalism.FourierDecayAlt.B.unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
      exact _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm_unit (T.word_lie Y hY)
    set ν : ℝ := ‖((List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nz T.word).prod : ℂ)‖ with hν
    refine ⟨CQ * ν + C₁, by positivity, fun G B hG g hg => ?_⟩
    have hgpos : 0 < _root_.Formalism.FourierDecayAlt.B.gN g := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg
    have hB : 0 ≤ B := _root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hG
    have hRw : _root_.Formalism.FourierDecayAlt.B.CCle A 0 (_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G) B :=
      _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_Rw hunit (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by simpa using hlen) hG)
    have hRw' := hRw.2 [] [] (by simp) (by simp) (by simp) g hg
    simp only [_root_.Formalism.FourierDecayAlt.B.dLR, List.foldr_nil, _root_.Formalism.FourierDecayAlt.B.Rw] at hRw'
    have hword : ‖_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G g‖ ≤ B * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A) := by
      rw [Real.rpow_neg hgpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgpos _),
        mul_comm]
      simpa [_root_.Formalism.FourierDecayAlt.B.Rw] using hRw'
    have hQg : ‖Q g‖ ≤ CQ * _root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ) := by
      have := hCQ [] (by simp) (by simp) g hg
      simpa [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw] using this
    have hterm : ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)‖ ≤ CQ * ν * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by
      rw [hcoef, smul_apply, ContinuousLinearMap.id_apply, norm_smul,
        congrFun (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_scale T.word G) g, norm_smul, ← hν, sub_eq_add_neg,
        Real.rpow_add hgpos]
      calc ‖Q g‖ * (ν * ‖_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G g‖)
          ≤ (CQ * _root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ)) * (ν * (B * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A))) := by
            gcongr
        _ = CQ * ν * B * (_root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ) * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A)) := by ring
    have hrest := hC₁ G B hG g hg
    have hsplit : _root_.Formalism.FourierDecayAlt.B.opApply (T :: Θ) G g = (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ G g := by
      simp [_root_.Formalism.FourierDecayAlt.B.opApply]
    rw [hsplit]
    calc ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖
        ≤ ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)‖ + ‖_root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖ := norm_add_le _ _
      _ ≤ CQ * ν * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) + C₁ * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) :=
          add_le_add hterm hrest
      _ = (CQ * ν + C₁) * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by ring

open MeasureTheory Filter Topology in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma continuousOn_opApply_of_polynomial_coeffs_lemma_2 {k r : ℕ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ)
    (Θ : List (_root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq))
    (hΘ : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) G) :
    ContinuousOn (_root_.Formalism.FourierDecayAlt.B.opApply Θ G) (_root_.Formalism.FourierDecayAlt.B.GV k r) := by
  apply _root_.Formalism.FourierDecayAlt.P.PBE.opApply_continuousOn
  intro T hT
  obtain ⟨-, Q, hQ, hcoef⟩ := hΘ T hT
  have hQc : Continuous Q := (_root_.Formalism.FourierDecayAlt.P.poly_adm (n := 0) hQ).1.continuous
  have hRw : ContinuousOn (_root_.Formalism.FourierDecayAlt.B.Rw T.word G) (_root_.Formalism.FourierDecayAlt.B.GV k r) :=
    _root_.Formalism.FourierDecayAlt.P.PBE.ckOn_continuousOn' subset_rfl (_root_.Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top hG T.word_lie)
  have hfun : (fun g => (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)) =
      fun g => Q g • _root_.Formalism.FourierDecayAlt.B.Rw T.word G g := by
    funext g
    rw [hcoef]
    simp
  rw [hfun]
  exact hQc.continuousOn.smul hRw


open MeasureTheory Filter Topology in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem _root_.GlobalTheory.HatNF.vecV_cut_polyOp : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (o κ : ℕ) (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp P.k P.r Wp Wq) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp o κ Θ → _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F → _root_.Formalism.FourierDecayAlt.B.InCC A o F → c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A - 1 - κ → ∀ cut : ℕ → _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℂ, (∀ n g, cut n g = ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) → ∀ γ : _root_.Formalism.FourierDecayAlt.C.LPt, Filter.Tendsto (fun n => p.V (_root_.Formalism.FourierDecayAlt.B.opApply Θ (fun g => cut n g • F g)) γ) Filter.atTop (nhds (p.V (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) γ)) := by
  obtain ⟨c₃, hc₃⟩ := _root_.Formalism.FourierDecayAlt.P.PBE.vecV_tendsto
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p o κ Θ F A hΘ hF hCC hA cut hcut γ
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hΘ
  have hΘ' : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := by
    intro T hT
    obtain ⟨hl, Q, hQ, hc, -⟩ := hΘ T hT
    exact ⟨hl, Q, hQ, hc⟩
  have hcutφ : ∀ n : ℕ, cut n = fun g => _root_.Formalism.FourierDecayAlt.P.JCx2.pdPhi (((n : ℝ) + 1)⁻¹ • g) := by
    intro n
    funext g
    rw [hcut]
    rfl
  have hψ : ∀ (n : ℕ) g, cut n g = 1 - _root_.Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    have h : _root_.Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g = 1 - _root_.Formalism.FourierDecayAlt.P.JCx2.pdPhi (((n : ℝ) + 1)⁻¹ • g) := rfl
    rw [hcutφ, h]
    ring
  unfold _root_.Formalism.FourierDecayAlt.B.InCC at hCC
  obtain ⟨b, hb⟩ := hCC
  have hb0 : 0 ≤ b := _root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hb
  have hb1 : _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o F b := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hb
  obtain ⟨K, hK0, hK⟩ := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) o
  have hGn : ∀ n : ℕ, _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o (fun g => cut n g • F g) (b + K * b) := by
    intro n
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hb1 (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1 : ℂ) (hK ((n : ℝ) + 1) hR A F b hb))
    refine _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (_root_.Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr ?_ h3) ?_
    · intro g _
      rw [hψ n g, sub_smul, one_smul, neg_one_smul, sub_eq_add_neg]
    · rw [norm_neg, norm_one, one_mul]
      linarith [div_le_self (mul_nonneg hK0 hb0) (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)]
  have hG0 : _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o F (b + K * b) := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb1 (by nlinarith)
  obtain ⟨C, hC0, hC⟩ := norm_opApply_le_of_polynomial_coeffs_lemma o κ (A - 1) Θ hΘ'
  have hexp : (κ : ℝ) - (A - 1) = -(A - 1 - κ) := by ring
  have hckn : ∀ n : ℕ, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) (fun g => cut n g • F g) := by
    intro n
    have h := (_root_.Formalism.FourierDecayAlt.P.JCx2.pd_cut_nice (R := (n : ℝ) + 1) (by positivity) hF).1
    rw [hcutφ n]
    exact h
  unfold _root_.Formalism.FourierDecayAlt.KB.Pl.V
  refine hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ (A - 1 - κ) hA
    (fun n => _root_.Formalism.FourierDecayAlt.B.opApply Θ (fun g => cut n g • F g)) (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) (C * (b + K * b))
    (by positivity)
    (fun n => (continuousOn_opApply_of_polynomial_coeffs_lemma_2 o κ Θ hΘ' (hckn n)).mono
      (fun g hg => hg.1))
    ((continuousOn_opApply_of_polynomial_coeffs_lemma_2 o κ Θ hΘ' hF).mono (fun g hg => hg.1))
    (fun n g hg => by
      have := hC _ _ (hGn n) g hg.1
      rwa [hexp] at this)
    (fun g hg => by
      have := hC _ _ hG0 g hg.1
      rwa [hexp] at this) ?_
  intro g _
  set S : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℝ := fun h => ∑ i, ∑ j, Complex.normSq (h i j) with hS
  have hScont : Continuous S :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  have hO : IsOpen {h | S h < S g + 1} := isOpen_lt hScont continuous_const
  obtain ⟨N, hN⟩ := exists_nat_ge (S g + 1)
  apply tendsto_const_nhds.congr'
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  symm
  apply _root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Θ hO _ g (by simp)
  intro h hh
  have hSh : S h < S g + 1 := hh
  have hS0 : 0 ≤ S h := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Complex.normSq_nonneg _
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hscaled : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • h) i j) =
      ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ * S h := by
    simp only [hS, Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul,
      Complex.normSq_ofReal, Finset.mul_sum]
  have hle : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ * S h ≤ 1 := by
    rw [← mul_inv, inv_mul_le_iff₀ (by positivity)]
    nlinarith
  have hone : cut n h = 1 := by
    rw [hcut, hscaled, Real.smoothTransition.one_of_one_le (by linarith)]
    simp
  simp only [hone, one_smul]

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecLowAndKFinDecayOfGapOfDecAll
section
namespace GlobalTheory.DecTransport


open Matrix Finset Formalism.FourierDecayAlt.ThreeDimData in
open scoped InnerProductSpace in
lemma decE_le {q : ℕ} (hq : 1 ≤ q) {h d : ℝ} (hh : 0 ≤ h) (hd : 0 ≤ d) :
    GlobalTheory.Count.decE q h d ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q)) * d) := by
  unfold GlobalTheory.Count.decE
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs : 1 ≤ Real.sqrt (q : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hq)

  have key : d / Real.sqrt q - min (2 * d ^ 2) (d / Real.sqrt q) ≤ 1 := by
    rcases le_total (2 * d ^ 2) (d / Real.sqrt q) with hm | hm
    · rw [min_eq_left hm]
      have : d / Real.sqrt q ≤ d := div_le_self hd hs
      nlinarith [sq_nonneg (d - 1 / 4)]
    · rw [min_eq_right hm]; linarith
  have e : -(h / (8 * Real.sqrt q)) * d = -(h / 8) * (d / Real.sqrt q) := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ h / 8)]

private lemma inv_mul_and_mul_inv_of_isCayleyU {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hP : PI.UpqRep.IsCayleyU k r ε P) :
    P⁻¹ * P = 1 ∧ P * P⁻¹ = 1 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  exact ⟨Matrix.nonsing_inv_mul P hd, Matrix.mul_nonsing_inv P hd⟩

private lemma conjTranspose_mem_Kset' {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : PI.UpqRep.IsCayleyU k r ε P) (hQ : PI.UpqRep.IsCayleyU k r ε Q) :
    P * Q⁻¹ ∈ PI.UpqRep.UJset ε := by
  obtain ⟨⟨-, hPJ⟩, -⟩ := hP
  obtain ⟨⟨-, hQJ⟩, hQu⟩ := hQ
  have hQi : Q⁻¹ = Q.conjTranspose := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hQu)
  have hQQ : Q * Q.conjTranspose = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hQu
  show (P * Q⁻¹).conjTranspose * PI.UpqRep.Jm ε * (P * Q⁻¹) = PI.UpqRep.Jm ε
  rw [hQi, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc Q * P.conjTranspose * PI.UpqRep.Jm ε * (P * Q.conjTranspose)
        = Q * (P.conjTranspose * PI.UpqRep.Jm ε * P) * Q.conjTranspose := by
        simp only [Matrix.mul_assoc]
    _ = Q * (Q.conjTranspose * PI.UpqRep.Jm ε * Q) * Q.conjTranspose := by rw [hPJ, hQJ]
    _ = (Q * Q.conjTranspose) * PI.UpqRep.Jm ε * (Q * Q.conjTranspose) := by simp only [Matrix.mul_assoc]
    _ = PI.UpqRep.Jm ε := by rw [hQQ, Matrix.one_mul, Matrix.mul_one]

private lemma rpow_three_div_two_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_one_add' hx (by norm_num), Real.sqrt_eq_rpow]


open Matrix Finset GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap Formalism.FourierDecayAlt.B in
open scoped InnerProductSpace in
theorem decLow_of_decGap (hA : GlobalTheory.DSId.DecGap) : Formalism.FourierDecayAlt.ThreeDimData.DecLow := by
  intro k r hk ε lam h H _ _ _ σ hl hσ hg h120 P hP w₁ w₂ h₁ h₂
  have hh : 0 ≤ h := by
    have : (0 : ℝ) ≤ 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by positivity
    linarith
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have hPi : P⁻¹ = star P := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hPu)
  have hPP := inv_mul_and_mul_inv_of_isCayleyU hP

  obtain ⟨P0, hP0, hDS0⟩ := hσ
  have hP0P := inv_mul_and_mul_inv_of_isCayleyU hP0
  have hDS : PI.UpqRep.IsDS ε lam (fun g => σ (P⁻¹ * g * P)) := by
    have h0 := GlobalTheory.CayleyChoice.isDS_conj hDS0 (conjTranspose_mem_Kset' hP hP0) (conjTranspose_mem_Kset' hP0 hP)
      (by
        calc P * P0⁻¹ * (P0 * P⁻¹) = P * (P0⁻¹ * P0) * P⁻¹ := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hP0P.1, Matrix.mul_one, hPP.2])
    have hfun : (fun g => σ (P⁻¹ * g * P)) =
        (fun g => σ (P0⁻¹ * (P0 * P⁻¹ * g * (P * P0⁻¹)) * P0)) := by
      funext g
      congr 1
      calc P⁻¹ * g * P = (P0⁻¹ * P0) * (P⁻¹ * g * P) * (P0⁻¹ * P0) := by
            rw [hP0P.1, Matrix.one_mul, Matrix.mul_one]
        _ = P0⁻¹ * (P0 * P⁻¹ * g * (P * P0⁻¹)) * P0 := by simp only [Matrix.mul_assoc]
    rw [hfun]
    exact h0

  have hq : rkR ε = r + 1 := rkR_eq hk hP
  have hgap : 120 * ((2 * r + k + 1 : ℕ) : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [hq]
    have h1 := GlobalTheory.GapSizeCheck.decay_range k r h h120
    have e : (((r + 1 : ℕ) : ℝ)) ^ ((3 : ℝ) / 2) = ((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1) := by
      push_cast
      exact rpow_three_div_two_eq_mul_sqrt (by positivity)
    rw [e]
    exact h1

  have ha : 0 ≤ h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))) := by positivity
  have hab : h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))) ≤ h / (8 * Real.sqrt ((r : ℝ) + 1)) := by
    apply div_le_div_of_nonneg_left hh (by positivity)
    have : (0 : ℝ) ≤ r := r.cast_nonneg
    gcongr
    linarith
  refine ⟨Real.exp (h / 8) * Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) *
    ‖w₁‖ * ‖w₂‖, fun x hx => ?_⟩

  have ex : P⁻¹ * (P * x * P⁻¹) * P = x := by
    calc P⁻¹ * (P * x * P⁻¹) * P = (P⁻¹ * P) * x * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hPP.1, Matrix.one_mul, Matrix.mul_one]
  have hgU : P * x * P⁻¹ ∈ PI.UpqRep.UJset ε :=
    (GlobalTheory.UnitaryCayley.transport hP (P * x * P⁻¹)).1.mp (by rw [ex]; exact hx)
  have hb : ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ decE (r + 1) h (dOp (P * x * P⁻¹)) * ‖w₁‖ * ‖w₂‖ := by
    have h0 := (hA _ ε lam H (fun g => σ (P⁻¹ * g * P)) hl hDS h hg hgap (P * x * P⁻¹) hgU w₁ h₁ w₂ h₂).2
    rw [hq] at h0
    simpa only [ex] using h0
  have hd : 0 ≤ dOp (P * x * P⁻¹) := ((GlobalTheory.Dec.dFacts_holds _ ε).1 _ hgU).1
  have hdecE : decE (r + 1) h (dOp (P * x * P⁻¹)) ≤
      Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt ((r : ℝ) + 1))) * dOp (P * x * P⁻¹)) := by
    have h0 := decE_le (q := r + 1) (by omega) hh hd
    push_cast at h0
    exact h0

  have hcl : Matrix.toEuclideanCLM (n := Fin (2 * r + k + 1)) (𝕜 := ℂ) (P * x * P⁻¹) =
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹)) := by
    first
      | rfl
      | (apply ContinuousLinearMap.coe_injective; simp [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin])
  have hGN : gN x ≤ Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) *
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹))‖ := by
    have h1 := hs_le_op x
    have h2 : ‖Matrix.toEuclideanCLM (n := Fin (2 * r + k + 1)) (𝕜 := ℂ) x‖ =
        ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹))‖ := by
      rw [← hcl, ← op_conj hPu x, hPi]
    rw [h2] at h1
    show Real.sqrt (∑ i, ∑ j, Complex.normSq (x i j)) ≤ _
    calc Real.sqrt (∑ i, ∑ j, Complex.normSq (x i j))
        ≤ Real.sqrt (((2 * r + k + 1 : ℕ) : ℝ) *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹))‖ ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  have hE : Real.exp (-(h / (8 * Real.sqrt ((r : ℝ) + 1))) * dOp (P * x * P⁻¹)) ≤
      Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) *
        gN x ^ (-(h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))) :=
    exp_le_rpow ha hab (by positivity) hd (gN_pos hx) hGN
  calc ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ decE (r + 1) h (dOp (P * x * P⁻¹)) * ‖w₁‖ * ‖w₂‖ := hb
    _ ≤ (Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt ((r : ℝ) + 1))) * dOp (P * x * P⁻¹))) *
          ‖w₁‖ * ‖w₂‖ := by gcongr
    _ ≤ (Real.exp (h / 8) * (Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) *
          gN x ^ (-(h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))))) * ‖w₁‖ * ‖w₂‖ := by gcongr
    _ = _ := by ring

theorem decLow_holds : Formalism.FourierDecayAlt.ThreeDimData.DecLow :=
  decLow_of_decGap GlobalTheory.Deep.ptBound_and_farBound_and_decGap.2.2

end GlobalTheory.DecTransport
end

