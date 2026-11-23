module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0174
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
public import Formalism.HermitianCurvature.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelModuleFormEqIntegralOfCompactCoeff
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0145

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionSmulStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCellExpansion_smul : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) (t : ℂ), Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁ → Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p (fun g => t • f g) b C₃ a₁ := by
  first | exact @GlobalTheory.familyDerivativeExpansion_smul | exact GlobalTheory.familyDerivativeExpansion_smul | (intros; apply GlobalTheory.familyDerivativeExpansion_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellJetBoundShiftedTypePlace
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP2 Formalism.QuantumDeterminants

namespace GlobalTheory.JetBoundShifted

open Formalism.FourierDecayAlt.TBB MeasureTheory
open scoped ENNReal

theorem bigCellJetBound_shiftedTypePlace {P : M.Par} {Wp Wq Wq' : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] {up up' : ℕ → ℝ}
    (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P up up') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp)) (n₀ p₀ : ℕ) (hT : 0 < Tq p)
    (h : ∀ c : Fin (P.r + 1) → ℂ, Ew q (fun _ => 1) F (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c)) :
    jN2 q F ≤ ENNReal.ofReal ((Tq p)⁻¹ ^ n₀) * bigCellDetWeightedEnergyIntegral p f (2 * p₀ + n₀) := by
  have hT0 : 0 ≤ (Tq p)⁻¹ ^ n₀ := by positivity
  unfold jN2 bigCellDetWeightedEnergyIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun c => ?_
  rw [← ENNReal.ofReal_mul hT0]
  refine ENNReal.ofReal_le_ofReal ((h c).trans (le_of_eq ?_))
  ring

end GlobalTheory.JetBoundShifted

namespace GlobalTheory.JetBoundShifted

open MeasureTheory
open scoped ENNReal

theorem main : ∀ C₃ CΛ C₀ C₂ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → 0 < C₂ → ∃ C₄ : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Fp : B.Mat P.k P.r → (Wqp →L[ℂ] Wp)) (Fm : B.Mat P.k P.r → (Wqm →L[ℂ] Wp)) (b Λ : ℝ) (n₀ p₀ : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → TBB.TTp pp = TBB.TTp p → TBB.TTp pm = TBB.TTp p → NormAtSh p pp pm f Fp Fm b n₀ p₀ → TBB.PtBound pp Fp (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) → TBB.PtBound pm Fm (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro C₃ CΛ C₀ C₂ hC₃ hCΛ hC₀ hC₂
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.JetConstSq.main C₃ CΛ C₀ C₂ hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Fp Fm b Λ n₀ p₀ hb hΛ hΛb
    hn₀ hp₀ htp htm hNorm hPp hPm hReg γ hγ hG
  have hGp : 0 < TBB.Gp pp γ := by rw [gp_eq p pp htp]; exact hG
  have hGm : 0 < TBB.Gp pm γ := by rw [gp_eq p pm htm]; exact hG
  have hK := hC₄ b Λ P.r n₀ p₀ hb hΛ hΛb hn₀ hp₀
  set G := TBB.Gp p γ with hGdef
  set m : ℝ := ((2 * P.r + 2 : ℕ) : ℝ) with hm
  have hb0 : 0 < b := by linarith
  have hT0 : 0 < TBB.Tq p := p.T.base.T'_pos
  set c : ℝ := 1 * (C₂ * Λ ^ 2) ^ (P.r + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  set T : ℝ := (TBB.Tq p)⁻¹ ^ n₀ with hTdef
  have hT0' : 0 ≤ T := by positivity
  set B3 : ℝ := b ^ (2 * C₃ * m ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) with hB3
  have hB30 : 0 ≤ B3 := by positivity
  set A : ℝ := (3 * b) ^ (2 * n₀) * (TBB.Tq p / G) ^ n₀ * G⁻¹ ^ (2 * p₀) with hA
  have hA0 : 0 ≤ A := by positivity
  set J := TBB.jN2 p f
  have hReg' : TBB.bigCellDetWeightedEnergyIntegral p f (2 * p₀ + n₀) ≤ ENNReal.ofReal B3 * J := hReg _ le_rfl
  have hEp : ENNReal.ofReal (TBB.Ew pp (fun _ => 1) Fp (P.r + 1) [] γ) ≤
      ENNReal.ofReal c * (ENNReal.ofReal T * (ENNReal.ofReal B3 * J)) := by
    refine (hPp γ hγ hGp).trans ?_
    gcongr
    exact (bigCellJetBound_shiftedTypePlace p pp f Fp n₀ p₀ hT0 fun c => hNorm.2.1 c).trans (by gcongr)
  have hEm : ENNReal.ofReal (TBB.Ew pm (fun _ => 1) Fm (P.r + 1) [] γ) ≤
      ENNReal.ofReal c * (ENNReal.ofReal T * (ENNReal.ofReal B3 * J)) := by
    refine (hPm γ hγ hGm).trans ?_
    gcongr
    exact (bigCellJetBound_shiftedTypePlace p pm f Fm n₀ p₀ hT0 fun c => hNorm.2.2 c).trans (by gcongr)
  set X := ENNReal.ofReal c * (ENNReal.ofReal T * (ENNReal.ofReal B3 * J))
  have hE : ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] γ) ≤ ENNReal.ofReal A * (2 * X) := by
    refine (ENNReal.ofReal_le_ofReal (hNorm.1 γ hγ hG)).trans ?_
    rw [ENNReal.ofReal_mul hA0]
    gcongr
    refine ENNReal.ofReal_add_le.trans ?_
    rw [two_mul]; exact add_le_add hEp hEm
  refine hE.trans ?_
  clear_value A c T B3 J G m
  have hX : ENNReal.ofReal A * (2 * X) = ENNReal.ofReal (A * 2 * c * T * B3) * J := by
    simp only [X]
    rw [show A * 2 * c * T * B3 = A * (2 * (c * (T * B3))) by ring, ENNReal.ofReal_mul hA0,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul hT0', ENNReal.ofReal_ofNat]
    ring
  rw [hX]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by simp)
  have hGne : G ≠ 0 := hG.ne'
  have heq : A * 2 * c * T * B3 = (2 * (3 * b) ^ (2 * n₀) * c * B3) * G⁻¹ ^ (2 * p₀ + n₀) := by
    simp only [hA, hTdef]
    rw [pow_add, div_eq_mul_inv]
    have : (TBB.Tq p * G⁻¹) ^ n₀ * (TBB.Tq p)⁻¹ ^ n₀ = G⁻¹ ^ n₀ := by
      rw [← mul_pow]; congr 1; field_simp
    linear_combination (2 * (3 * b) ^ (2 * n₀) * G⁻¹ ^ (2 * p₀) * c * B3) * this
  rw [heq]
  exact mul_le_mul_of_nonneg_right hK (by positivity)

end GlobalTheory.JetBoundShifted
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormEqBigCellIntegralTopDensityCompact
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

lemma levWeight_nonneg (P : M.Par) (j : ℕ) (t : ℂ) : 0 ≤ KB.levW P j t := by
  unfold KB.levW
  split_ifs
  · exact Formalism.FourierDecayAlt.P.JCx2.rb_zWeight_nonneg _ _ _ _
  · positivity

lemma ofFn_snoc_unit {j : ℕ} (c : Fin j → ℂ) (t : ℂ) :
    (List.ofFn fun l : Fin (j + 1) => ((1 : ℕ), Fin.snoc (α := fun _ => ℂ) c t l)) =
      (List.ofFn fun l : Fin j => ((1 : ℕ), c l)) ++ [((1 : ℕ), t)] := by
  rw [List.ofFn_succ']
  simp

lemma isLocPt_ofFn_unit {j : ℕ} (c : Fin j → ℂ) (hc : ∀ i, c i ≠ 0) :
    D.IsLocPt (List.ofFn fun l : Fin j => ((1 : ℕ), c l)) j := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rw [List.mem_ofFn] at hb
    obtain ⟨i, rfl⟩ := hb
    exact ⟨le_rfl, hc i⟩
  · simp [D.ptSize, List.map_ofFn, List.sum_ofFn]

theorem levelZero_eq_integral_topVector_of_cpt :
    P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → MemLp (tv p H w) 2 volume ∧ B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H = ((∫ c, ‖tv p H w c‖ ^ 2 : ℝ) : ℂ) := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H w hD hH hw
  have hmeas := _root_.GlobalTheory.TopVec.aestronglyMeasurable_tv Wp Wq P p Cb H w hD hw hH.1
  set R : (j : ℕ) → (Fin j → ℂ) → ℝ := fun j c =>
    (p.RR H j w (List.ofFn fun l : Fin j => ((1 : ℕ), c l)) (List.ofFn fun l : Fin j => ((1 : ℕ), c l))).re with hR
  have hae : (fun c : Fin (P.r + 1) → ℂ => (∏ i : Fin (P.r + 1), KB.levW P ((i : ℕ) + 1) (c i)) * R (P.r + 1) c)
      =ᵐ[volume] fun c => ‖tv p H w c‖ ^ 2 := by
    filter_upwards [GlobalTheory.ae_coords_ne_zero (P.r + 1)] with c hc
    rw [← GlobalTheory.TopVec.Ew_eq_norm_tv_sq Wp Wq P p H w c, (_root_.GlobalTheory.TopDensity.topDensity_eq Wp Wq P p H w c hc).1]
    rfl
  obtain ⟨hint, heq⟩ := GlobalTheory.iterated_integral_eq_integral_pi (P.r + 1) (KB.levW P) R (levWeight_nonneg P)
    (fun c hc => (_root_.GlobalTheory.TopDensity.topDensity_eq Wp Wq P p H w c hc).2.2)
    ((hmeas.norm.pow 2).aemeasurable.congr hae.symm)
    (fun j hj c hc => by
      obtain ⟨h1, h2⟩ := _root_.GlobalTheory.LevelIntegralStep.levelForm_eq_integral hP Wp Wq P p Cb H w j _ hD hH hw (Nat.lt_succ_iff.1 hj)
        (isLocPt_ofFn_unit c hc)
      have h3 := h1.re
      have h4 := integral_re h1
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3 h4
      simp only [hR, ofFn_snoc_unit]
      exact ⟨h3, by rw [h4, ← h2]⟩)
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).2 (hint.congr hae), ?_⟩
  rw [← integral_congr_ae hae, ← heq]
  have him := _root_.GlobalTheory.LevelFormsReal.levelZero_im_eq_zero hP Wp Wq P p Cb H w hD hH hw
  have h0 : p.RR H 0 w [] [] = B.beta p.T.base
      (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H := by
    unfold KB.Pl.RR
    rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hH.1 (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw)]
    rfl
  rw [← h0]
  apply Complex.ext
  · simp [hR]
  · simpa using him

end GlobalTheory.TopVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialSmulCapelliEigenfunctionSum
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory.EigenSumPoly

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def IsEigenSum (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ),
    (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧
    (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧
    (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g =
      ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧
    ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g

def entryVar (g : B.Mat k r) :
    (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℂ :=
  Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))

end

end GlobalTheory.EigenSumPoly
end

