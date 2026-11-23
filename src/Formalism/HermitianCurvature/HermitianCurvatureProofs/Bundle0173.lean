module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0172
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0171
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0150
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AeMemOfHaar
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section reorder

variable {X Y A X' Y' A' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A] [MeasurableSpace X']
  [MeasurableSpace Y'] [MeasurableSpace A']

def reorderE : ((X × Y) × (X' × Y')) × (A × A') ≃ᵐ (X × (A × Y)) × (X' × (A' × Y')) where
  toFun q := ((q.1.1.1, (q.2.1, q.1.1.2)), (q.1.2.1, (q.2.2, q.1.2.2)))
  invFun p := (((p.1.1, p.1.2.2), (p.2.1, p.2.2.2)), (p.1.2.1, p.2.2.1))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable fun q : ((X × Y) × (X' × Y')) × (A × A') => ((q.1.1.1, (q.2.1, q.1.1.2)), (q.1.2.1, (q.2.2, q.1.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable fun p : (X × (A × Y)) × (X' × (A' × Y')) => (((p.1.1, p.1.2.2), (p.2.1, p.2.2.2)), (p.1.2.1, p.2.2.1))
    fun_prop

theorem reorder_mp (μX : Measure X) (μY : Measure Y) (μA : Measure A) (μX' : Measure X') (μY' : Measure Y')
    (μA' : Measure A') [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μA] [SigmaFinite μX'] [SigmaFinite μY']
    [SigmaFinite μA'] :
    MeasurePreserving (reorderE (X := X) (Y := Y) (A := A) (X' := X') (Y' := Y') (A' := A'))
      (((μX.prod μY).prod (μX'.prod μY')).prod (μA.prod μA'))
      ((μX.prod (μA.prod μY)).prod (μX'.prod (μA'.prod μY'))) := by
  have h1 := Dx2.SplitM.middle_four_swap_measure_preserving (μX.prod μY) (μX'.prod μY') μA μA'
  have h2 := ((MeasurePreserving.id μX).prod (Measure.measurePreserving_swap (μ := μY) (ν := μA))).comp
    (measurePreserving_prodAssoc μX μY μA)
  have h2' := ((MeasurePreserving.id μX').prod (Measure.measurePreserving_swap (μ := μY') (ν := μA'))).comp
    (measurePreserving_prodAssoc μX' μY' μA')
  have hall := (h2.prod h2').comp h1
  convert hall using 1
  funext ⟨⟨⟨x, y⟩, ⟨x', y'⟩⟩, ⟨a, a'⟩⟩
  rfl

end reorder

variable {k : ℕ}

def MCOm : Prop :=
  ∀ (k ρ : ℕ) (z0 z0' : Fin (2 * ρ + k + 1) → ℂ), inWb k ρ z0 → inWb k ρ z0' → ∀ c : ℂ, c ≠ 0 →
    ∀ γ ∈ B.GV k ρ, γ ∈ Q.OmPlus k ρ z0 z0' →
      D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) ∈
        JF.Om k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0'))

theorem ae_mem_of_haar {r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ U := by
  rw [ae_iff]; exact h.conc

theorem jfStep_of (hO : MCOm) : JFStep := by
  intro k ρ m e Wp Wq _ _ _ _ _ _ B1 B0 hz hz' hπ hπ' hW1 hW1' hW0 hW0' hN1 hN0 f1 f0 c hc hf1 hstep γ hγ hγO
  subst e
  rw [Dx2.Tower.castV_rfl] at hz hz'
  set κ : 1 + ρ = ρ + 1 := Nat.add_comm 1 ρ with hκ
  have hπ1 : ∀ y : B.Mat k ρ, B0.π y = B1.π (D.castM κ (ιLev k 1 ρ y)) := by
    intro y; rw [hπ y]; unfold lev1; rw [Dx2.MN.castM_rfl]
  have hπ1' : ∀ y : B.Mat k ρ, B0.π' y = B1.π' (D.castM κ (ιLev k 1 ρ y)) := by
    intro y; rw [hπ' y]; unfold lev1; rw [Dx2.MN.castM_rfl]
  have hmc : mc rfl c γ = D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) := by
    unfold mc; rw [Dx2.MN.castM_rfl]

  have hμW : B1.μW = B0.μW.map (levA ρ) :=
    muW_lev B0.z B0.μW B1.μW B0.haarW (by rw [← hz]; exact B1.haarW) hW0 hW1
  have hμW' : B1.μW' = B0.μW'.map (levA ρ) :=
    muW_lev B0.z' B0.μW' B1.μW' B0.haarW' (by rw [← hz']; exact B1.haarW') hW0' hW1'
  have hμN : B1.μN = ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Qm ρ) := by rw [hN1, muN_succ']

  have hOm := hO k ρ B0.z B0.z' B0.z_mem B0.z'_mem c hc γ hγ hγO
  rw [← hz, ← hz', ← hmc] at hOm
  have hInt := rhs_int B1 f1 hf1 _ hOm
  have hsH := sf_heis (k := k) ρ
  have hsN := sf_muN (k := k) ρ
  have hfW : IsFiniteMeasure B0.μW := ⟨by rw [hW0]; exact ENNReal.one_lt_top⟩
  have hfW' : IsFiniteMeasure B0.μW' := ⟨by rw [hW0']; exact ENNReal.one_lt_top⟩
  set T : (Mt k ρ × (Mt k (1 + ρ) × Mt k ρ)) × (Mt k ρ × (Mt k (1 + ρ) × Mt k ρ)) → B.SS k (ρ + 1) :=
    Prod.map (Prod.map (levA ρ) (Qm ρ)) (Prod.map (levA ρ) (Qm ρ)) with hT
  have hTm : Measurable T :=
    ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable).prodMap
      ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable)
  set big := (B0.μW.prod ((B2.μHeis k ρ).prod (D.muN k ρ))).prod
    (B0.μW'.prod ((B2.μHeis k ρ).prod (D.muN k ρ))) with hbig
  have hμSS : B1.μSS = big.map T := by
    unfold B.RealPlaceData.μSS
    rw [hμW, hμW', hμN, Measure.map_prod_map _ _ (levA_cont ρ).measurable (Qm_cont ρ).measurable,
      Measure.map_prod_map _ _ (levA_cont ρ).measurable (Qm_cont ρ).measurable,
      Measure.map_prod_map _ _ ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable)
        ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable)]
  set FI := JF.integrand B1 f1 (mc rfl c γ) with hFI
  have hR : B.JF B1 f1 (mc rfl c γ) = ∫ p, FI p ∂B1.μSS := rfl
  have hL : B.JF B0 f0 γ = ∫ p, JF.integrand B0 f0 γ p ∂((B0.μW.prod (D.muN k ρ)).prod (B0.μW'.prod (D.muN k ρ))) := by
    rw [← hN0]; rfl
  have hAE : AEStronglyMeasurable FI (big.map T) := by rw [← hμSS]; exact hInt.aestronglyMeasurable
  have hInt2 : Integrable (FI ∘ T) big := (integrable_map_measure hAE hTm.aemeasurable).1 (by rw [← hμSS]; exact hInt)
  have hRmp := reorder_mp B0.μW (D.muN k ρ) (B2.μHeis k ρ) B0.μW' (D.muN k ρ) (B2.μHeis k ρ)
  have hInt3 : Integrable (FI ∘ T ∘ reorderE) (((B0.μW.prod (D.muN k ρ)).prod (B0.μW'.prod (D.muN k ρ))).prod
      ((B2.μHeis k ρ).prod (B2.μHeis k ρ))) :=
    (hRmp.integrable_comp_emb reorderE.measurableEmbedding).2 hInt2
  rw [hR, hμSS, integral_map hTm.aemeasurable hAE, ← hRmp.integral_comp reorderE.measurableEmbedding]
  change B.JF B0 f0 γ = ∫ x, (FI ∘ T ∘ reorderE) x ∂_
  rw [integral_prod _ hInt3, hL]

  have w1 : ∀ᵐ x ∂B0.μW, Matrix.of x ∈ UWset k ρ B0.z := ae_mem_of_haar B0.haarW
  have w1' : ∀ᵐ x ∂B0.μW', Matrix.of x ∈ UWset k ρ B0.z' := ae_mem_of_haar B0.haarW'
  have w2 : ∀ᵐ x ∂(D.muN k ρ), Matrix.of x ∈ QuantumDeterminants.Nset k ρ := ae_mem_of_haar (Dx2.MN.haar ρ)
  have wH : ∀ᵐ x ∂(B2.μHeis k ρ), Matrix.of x ∈ QuantumDeterminants.Nset k (1 + ρ) := by
    filter_upwards [ae_mem_of_haar (Formalism.FourierDecayAlt.P.heisenberg_haar_measure k ρ)] with x hx
    obtain ⟨p, hp⟩ := hx
    rw [← hp]; exact Formalism.FourierDecayAlt.P.heisenberg_mem_unipotent k ρ p
  set μO := (B0.μW.prod (D.muN k ρ)).prod (B0.μW'.prod (D.muN k ρ)) with hμO
  have o1 : ∀ᵐ o ∂μO, Matrix.of o.1.1 ∈ UWset k ρ B0.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae w1)
  have o2 : ∀ᵐ o ∂μO, Matrix.of o.1.2 ∈ QuantumDeterminants.Nset k ρ :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae w2)
  have o3 : ∀ᵐ o ∂μO, Matrix.of o.2.1 ∈ UWset k ρ B0.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae w1')
  have o4 : ∀ᵐ o ∂μO, Matrix.of o.2.2 ∈ QuantumDeterminants.Nset k ρ :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae w2)
  have i1 : ∀ᵐ i ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)), Matrix.of i.1 ∈ QuantumDeterminants.Nset k (1 + ρ) :=
    Measure.quasiMeasurePreserving_fst.ae wH
  have i2 : ∀ᵐ i ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)), Matrix.of i.2 ∈ QuantumDeterminants.Nset k (1 + ρ) :=
    Measure.quasiMeasurePreserving_snd.ae wH
  apply integral_congr_ae
  filter_upwards [o1, o2, o3, o4] with o ho1 ho2 ho3 ho4
  obtain ⟨⟨h0, y⟩, ⟨h0', y'⟩⟩ := o
  simp only at ho1 ho2 ho3 ho4
  have hH := Ux3.hpk_det k ρ
  have hgG : Matrix.of y * Matrix.of h0 ∈ B.GV k ρ := HermitianFormFactor.UH_mul ho2.1 ho1.1
  have hgG' : Matrix.of y' * Matrix.of h0' ∈ B.GV k ρ := HermitianFormFactor.UH_mul ho4.1 ho3.1
  set γh := (Matrix.of y * Matrix.of h0)⁻¹ * γ * (Matrix.of y' * Matrix.of h0') with hγhd
  have hγh : γh ∈ B.GV k ρ := HermitianFormFactor.UH_mul (HermitianFormFactor.UH_mul (HermitianFormFactor.UH_inv hH hgG) hγ) hgG'

  have hrep := B0.π_rep
  have hrep' := B0.π'_rep
  have hi0 : (Matrix.of h0)⁻¹ ∈ UWset k ρ B0.z := WeylGroupFacts.uw_inv ho1
  have hi0' : (Matrix.of h0')⁻¹ ∈ UWset k ρ B0.z' := WeylGroupFacts.uw_inv ho3
  have hu0 : IsUnit (Matrix.of h0).det := HermitianFormFactor.UH_unit hH ho1.1
  have hu0' : IsUnit (Matrix.of h0').det := HermitianFormFactor.UH_unit hH ho3.1
  let eA : Wp ≃L[ℂ] Wp := ContinuousLinearEquiv.equivOfInverse (B0.π (Matrix.of h0)) (B0.π (Matrix.of h0)⁻¹)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hi0 _ ho1, Matrix.nonsing_inv_mul _ hu0, hrep.1]; rfl)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ ho1 _ hi0, Matrix.mul_nonsing_inv _ hu0, hrep.1]; rfl)
  let eB : Wq ≃L[ℂ] Wq := ContinuousLinearEquiv.equivOfInverse (B0.π' (Matrix.of h0')) (B0.π' (Matrix.of h0')⁻¹)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep'.2 _ hi0' _ ho3, Matrix.nonsing_inv_mul _ hu0', hrep'.1]; rfl)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep'.2 _ ho3 _ hi0', Matrix.mul_nonsing_inv _ hu0', hrep'.1]; rfl)
  let Λ : (Wq →L[ℂ] Wp) ≃L[ℂ] (Wq →L[ℂ] Wp) := eB.arrowCongr eA
  have hΛ : ∀ Tm : Wq →L[ℂ] Wp, Λ Tm = (B0.π (Matrix.of h0)).comp (Tm.comp (B0.π' (Matrix.of h0')⁻¹)) := by
    intro Tm; ext v; rfl
  set K : ℂ := psi k ρ B0.z cStd (Matrix.of y) * star (psi k ρ B0.z' cStd (Matrix.of y')) with hK
  set Ψ : Mt k (1 + ρ) × Mt k (1 + ρ) → (Wq →L[ℂ] Wp) := fun p => psiInt B1 f1 c γh (Matrix.of p.1) (Matrix.of p.2)
    with hΨ
  symm
  calc ∫ i, (FI ∘ T ∘ reorderE) (((h0, y), (h0', y')), i) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ))
      = ∫ i, K • Λ (Ψ (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) i.1,
          conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) i.2)) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) := by
        apply integral_congr_ae
        filter_upwards [i1, i2] with i hi1 hi2
        rw [hΛ]
        show JF.integrand B1 f1 (mc rfl c γ) ((levA ρ h0, Qm ρ (i.1, y)), (levA ρ h0', Qm ρ (i.2, y'))) = _
        rw [hmc, pt_eq B1 B0 hz hz' hπ1 hπ1' f1 c γ h0 y h0' y' i.1 i.2 ho1 ho2 ho3 ho4 hi1 hi2]
    _ = K • Λ (∫ i, Ψ (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) i.1,
          conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) i.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ))) := by
        rw [integral_smul, Λ.integral_comp_comm]
    _ = K • Λ (∫ i, Ψ i ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ))) := by
        rw [heis_conj_int ρ hgG hgG' Ψ]
    _ = K • Λ (∫ xx : U.RC k 1 ρ × U.RC k 1 ρ, psiInt B1 f1 c γh (U.Rn k 1 ρ xx.1) (U.Rn k 1 ρ xx.2)
          ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ))) := by
        rw [← heis_int ρ (fun b b' => psiInt B1 f1 c γh b b')]
    _ = K • Λ (f0 γh) := by
        rw [hstep γh hγh]
        rfl
    _ = JF.integrand B0 f0 γ ((h0, y), (h0', y')) := by
        rw [hΛ]
        unfold JF.integrand JF.xiP B.rho B.sgs
        congr 3
        show f0 γh = f0 ((Matrix.of h0)⁻¹ * (Matrix.of y)⁻¹ * γ * Matrix.of y' * Matrix.of h0')
        rw [hγhd, Matrix.mul_inv_rev]
        simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
section
namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

theorem big_cell_values : TL.CellVals := by
  intro k r Wp Wq _ _ _ _ _ Bs x hx
  obtain ⟨hc, hg, hG⟩ := hx
  obtain ⟨μ, -, hμ⟩ := (TwoByOneBlock.UWb_iff x.2).1 (NFRadRedA.glev_uwb hg)
  have hGV : wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by
    have h1 : wCell k r (Fin.last r) x.1 ∈ Glev k r 0 := by
      unfold wCell
      exact Qx3.wlist_glev hc _
    exact (Qx5.Glev_mul h1 (Qx4.glev0 hg.1)).1
  have hM : wCell k r (Fin.last r) x.1 * x.2 = bigCell k r x.1 μ := by
    rw [P5.Rad.wCell_last_eq, hμ, ← (bruhat_big_cell_factorization k r x.1 μ).1]
  rw [hM] at hGV ⊢
  set ζ := zetaL k r Bs.z Bs.z' (Fin.last r) x.2 with hζdef
  have hz : ζ = herm (Hb k) (μ *ᵥ wbPart k r Bs.z') (wbPart k r Bs.z) := by
    rw [hζdef, P5.Rad.zetaL_last, hμ]
    have e1 : B2.embWb k r μ *ᵥ Bs.z' = TwoByOneBlock.jV k r (μ *ᵥ wbPart k r Bs.z') := by
      conv_lhs => rw [← TwoByOneBlock.jV_wbPart Bs.z'_mem]
      exact TwoByOneBlock.emb_mulVec_jV _ _
    rw [e1]
    conv_lhs => rw [← TwoByOneBlock.jV_wbPart Bs.z_mem]
    rw [TwoByOneBlock.herm_jV]
  let d : Fin (r + 1) → ℂ := fun a => if h : (a : ℕ) < r then x.1 ⟨a, h⟩ else ζ
  have hZ : Zhat k r Bs.z Bs.z' (bigCell k r x.1 μ) = diagonal d := by
    rw [bigCellZhat k r Bs.z Bs.z' x.1 μ Bs.z_mem Bs.z'_mem]
    congr 1
    funext a
    by_cases h : (a : ℕ) < r
    · simp [d, h]
    · simp only [d, h, dite_false]
      rw [BigCellHermitian.herm_bigCell x.1 μ Bs.z_mem Bs.z'_mem, hz]
  have hD := BruhatBigCell.dmin_diag Bs.z Bs.z' _ d hZ
  have hTT : 0 < Tz k r Bs.z * Tz k r Bs.z' := mul_pos Bs.T_pos Bs.T'_pos
  have hζ : ζ ≠ 0 := by
    intro h0
    have : GGl k r Bs.z Bs.z' x.2 = Complex.normSq ζ - Tz k r Bs.z * Tz k r Bs.z' := rfl
    rw [this, h0, map_zero] at hG
    linarith
  have hd0 : ∀ a, d a ≠ 0 := by
    intro a
    by_cases h : (a : ℕ) < r
    · simp only [d, h, dite_true]
      exact hc _
    · simp only [d, h, dite_false]
      exact hζ
  have hP : ∏ a : Fin r, x.1 a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc a
  have hDr : Dmin k r Bs.z Bs.z' (bigCell k r x.1 μ) ⟨r, by omega⟩ = ∏ a : Fin r, x.1 a := by
    rw [hD]
    refine Finset.prod_congr rfl ?_
    intro i _
    have hi : ((Fin.castLE (by omega) i : Fin (r + 1)) : ℕ) < r := i.isLt
    simp only [d, hi, dite_true]
    rfl
  have hDl : Dmin k r Bs.z Bs.z' (bigCell k r x.1 μ) (Fin.last (r + 1)) = (∏ a : Fin r, x.1 a) * ζ := by
    rw [hD]
    show ∏ i : Fin (r + 1), d (Fin.castLE (by omega) i) = _
    rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl ?_
      intro i _
      have hi : ((Fin.castLE (by omega) i.castSucc : Fin (r + 1)) : ℕ) < r := i.isLt
      simp only [d, hi, dite_true]
      rfl
    · have hi : ¬ ((Fin.castLE (by omega) (Fin.last r) : Fin (r + 1)) : ℕ) < r := by simp
      simp only [d, hi, dite_false]
  have hGf : Gf k r Bs.z Bs.z' (bigCell k r x.1 μ) = Complex.normSq (∏ a : Fin r, x.1 a) * GGl k r Bs.z Bs.z' x.2 := by
    unfold Gf
    rw [hDl, hDr]
    show _ = _ * (Complex.normSq ζ - Tz k r Bs.z * Tz k r Bs.z')
    rw [map_mul]
    ring
  refine ⟨⟨hGV, ?_, ?_⟩, hDr, hDl, hGf⟩
  · rw [hGf]
    exact mul_pos (Complex.normSq_pos.mpr hP) hG
  · intro l _
    rw [hD]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportInClassGeneral
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CompactSupportClassLemmas

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem compact_support_in_class_general (D : RealPlaceData k r Wp Wq) (Θ : DiffOp k r Wp Wq) (hS : SmoothCoef (GPos D) Θ)
    (hC : Commutes D (GPos D) Θ) (F F' : Mat k r → (Wq →L[ℂ] Wp))
    (hF : CkOn ⊤ (GV k r) F) (hFc : HasCompactSupport F) (hFO : ∀ g ∈ tsupport F, g ∈ GV k r → g ∈ GPos D)
    (hF' : CkOn ⊤ (GV k r) F') (hF'c : HasCompactSupport F') (hF'O : ∀ g ∈ tsupport F', g ∈ GV k r → g ∈ GPos D) :
    InCC (AB k r) 5 F ∧ InCC (AB k r) 5 F' ∧ InCC (AB k r) 5 (opApply Θ F) ∧ InCC (AB k r) 5 (opAdj Θ F') ∧
      beta D (opApply Θ F) F' = beta D F (opAdj Θ F') := by
  set C : Set (Mat k r) := tsupport F with hCdef
  set C' : Set (Mat k r) := tsupport F' with hC'def
  have hCc : IsCompact C := hFc
  have hC'c : IsCompact C' := hF'c
  obtain ⟨_, _, _, _, _, hL3, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq D (AB k r) le_rfl
  have supp : ∀ {φ : Mat k r → (Wq →L[ℂ] Wp)} {K : Set (Mat k r)}, IsCompact K →
      (∀ g ∈ K, g ∈ GV k r → g ∈ GPos D) →
      (∀ g ∈ GV k r, g ∉ K → φ g = 0) → closure {g | g ∈ GV k r ∧ φ g ≠ 0} ⊆ GPos D :=
    by
    intro φ K hK hKO hz
    exact (closure_minimal (s := {g | g ∈ GV k r ∧ φ g ≠ 0}) (t := K ∩ GV k r) (fun g hg => by
      refine ⟨?_, hg.1⟩
      by_contra hgK
      exact hg.2 (hz g hg.1 hgK)) (hK.isClosed.inter Formalism.FourierDecayAlt.P.B5.GV_closed)).trans (fun g hg => hKO g hg.1 hg.2)
  have rwz : ∀ {φ : Mat k r → (Wq →L[ℂ] Wp)} {K : Set (Mat k r)}, IsCompact K →
      (∀ g ∈ GV k r, g ∉ K → φ g = 0) → ∀ w : List (Mat k r), (∀ X ∈ w, inLie k r X) →
        ∀ g ∈ GV k r, g ∉ K → Rw w φ g = 0 :=
    fun hK hz w hw g hg hgK => Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hK.isClosed.isOpen_compl hw (fun x hx hxK => hz x hx hxK) g hg hgK
  have hFz : ∀ g ∈ GV k r, g ∉ C → F g = 0 := fun g _ h => image_eq_zero_of_notMem_tsupport h
  have hF'z : ∀ g ∈ GV k r, g ∉ C' → F' g = 0 := fun g _ h => image_eq_zero_of_notMem_tsupport h
  have hap : ∀ T ∈ Θ, CkOn ⊤ (GV k r) (fun x => T.coefAdj x (F' x)) ∧
      ∀ g ∈ GV k r, g ∉ C' → T.coefAdj g (F' g) = 0 := fun T hT =>
    ⟨Formalism.FourierDecayAlt.P.B5.ckOn_coef (hS T hT).2 hF' (supp hC'c hF'O hF'z), fun g hg hgK => by rw [hF'z g hg hgK, map_zero]⟩
  have hrev : ∀ T ∈ Θ, ∀ X ∈ T.word.reverse, inLie k r X := fun T _ X hX => T.word_lie X (List.mem_reverse.1 hX)
  have hΘF : InCC (AB k r) 5 (opApply Θ F) := by
    show InCC _ 5 (fun g => (Θ.map fun T => T.coef g (Rw T.word F g)).sum)
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum Θ (fun T g => T.coef g (Rw T.word F g)) fun T hT => ?_
    exact cptInCC_G (Formalism.FourierDecayAlt.P.B5.ckOn_coef (hS T hT).1 (ckOn_Rw_top hF T.word T.word_lie)
        (supp hCc hFO (rwz hCc hFz T.word T.word_lie))) hCc
      (fun g hg hgK => by
        show T.coef g (Rw T.word F g) = 0
        rw [rwz hCc hFz T.word T.word_lie g hg hgK, map_zero]) _ 5
  have hΘF' : InCC (AB k r) 5 (opAdj Θ F') := by
    show InCC _ 5 (fun g => (Θ.map fun T =>
      ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g).sum)
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum Θ
      (fun T g => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g) fun T hT => ?_
    exact cptInCC_G (ckOn_smul ((-1 : ℂ) ^ T.word.length) (ckOn_Rw_top (hap T hT).1 _ (hrev T hT))) hC'c
      (fun g hg hgK => by
        show ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g = 0
        rw [rwz hC'c (hap T hT).2 _ (hrev T hT) g hg hgK, smul_zero]) _ 5
  have hIC : IntClause D Θ F F' := by
    intro p hp T hT i j hij hj
    have hlie1 : ∀ X ∈ (T.word.take i).reverse, inLie k r X := fun X hX =>
      T.word_lie X (List.mem_of_mem_take (List.mem_reverse.mp hX))
    have hlie2 : ∀ X ∈ T.word.drop j, inLie k r X := fun X hX => T.word_lie X (List.mem_of_mem_drop hX)
    set f₁ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.take i).reverse (fun x => T.coefAdj x (F' x)) with hf₁
    set f₂ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.drop j) (rho D p F) with hf₂
    have hf₁c : CkOn ⊤ (GV k r) f₁ := ckOn_Rw_top (hap T hT).1 _ hlie1
    have hf₁z : ∀ g ∈ GV k r, g ∉ C' → f₁ g = 0 := rwz hC'c (hap T hT).2 _ hlie1
    obtain ⟨K₁, hK₁⟩ := cptInCC_G hf₁c hC'c hf₁z 0 0
    have hb₁ : ∀ g ∈ GV k r, ‖f₁ g‖ ≤ K₁ := by
      intro g hg
      have := hK₁.2 [] [] (by simp) (by simp) (by simp) g hg
      simpa [Real.rpow_zero, dLR, Rw] using this
    have hf₂c : ContinuousOn f₂ (GV k r) :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_cont subset_rfl (Formalism.FourierDecayAlt.P.B5.ckOn_mono bot_le
        (ckOn_Rw_top (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) _ hlie2))
    have hf₁cont : ContinuousOn f₁ (GV k r) :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_cont subset_rfl (Formalism.FourierDecayAlt.P.B5.ckOn_mono bot_le hf₁c)
    obtain ⟨K₂, hK₂⟩ := (hC'c.inter_right Formalism.FourierDecayAlt.P.B5.GV_closed).exists_bound_of_continuousOn
      (hf₂c.mono Set.inter_subset_right)
    set G : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((‖f₂ g‖ : ℝ) : ℂ) • f₁ g with hG
    have hGn : ∀ g, ‖G g‖ = ‖f₁ g‖ * ‖f₂ g‖ := by
      intro g
      simp only [hG, norm_smul, Complex.norm_real, norm_norm]
      ring
    have hGc : ContinuousOn G (GV k r) := (Complex.continuous_ofReal.comp_continuousOn hf₂c.norm).smul hf₁cont
    have hGm := Formalism.FourierDecayAlt.P.BetaSesquilinearity.aesm_of_continuousOn D hGc
    have hfin : D.μG (C' : Set (Mt k r)) ≠ ⊤ := (D.haarG.finite_compact C' hC'c).ne
    have hind : Integrable ((C' : Set (Mt k r)).indicator fun _ => K₁ * K₂) D.μG :=
      (integrableOn_const hfin).integrable_indicator (IsClosed.measurableSet (α := Mt k r) hC'c.isClosed)
    have hint : Integrable (fun g : Mt k r => G (Matrix.of g)) D.μG := by
      refine hind.mono' hGm ?_
      filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae D.haarG] with x hx
      by_cases hxC : x ∈ (C' : Set (Mt k r))
      · rw [Set.indicator_of_mem hxC, hGn]
        have h1 := hb₁ (Matrix.of x) hx
        have h2 := hK₂ (Matrix.of x) ⟨hxC, hx⟩
        exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      · rw [Set.indicator_of_notMem hxC, hGn, hf₁z (Matrix.of x) hx hxC, norm_zero, zero_mul]
    exact hint.norm.congr (Filter.Eventually.of_forall fun g => hGn _)
  have hIF := cptInCC_G hF hCc hFz (AB k r) 5
  have hIF' := cptInCC_G hF' hC'c hF'z (AB k r) 5
  exact ⟨hIF, hIF', hΘF, hΘF', hL3 (GPos D) Θ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gPos_stable D) hS hC F F'
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF) (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF')
    (supp hCc hFO hFz) (supp hC'c hF'O hF'z) hIF hIF' hΘF hΘF' hIC⟩

end Formalism.FourierDecayAlt.P.CompactSupportClassLemmas

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

theorem compact_support_lemma_three : CompactSupportClassMembership := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ _hB v Θ hΘ F F' hF hFc hFO hF' hF'c hF'O
  exact Formalism.FourierDecayAlt.P.CompactSupportClassLemmas.compact_support_in_class_general (T v).base Θ hΘ.1 hΘ.2 F F' hF hFc
    (fun g hg hgG => ⟨hgG, (hFO hg).1⟩) hF' hF'c (fun g hg hgG => ⟨hgG, (hF'O hg).1⟩)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CoreLF
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def CoreLF : Prop :=
  ∀ (k p m n : ℕ) (e : p + m = n), 1 ≤ p → ∀ (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k m Wp Wq) (B0 : B.RealPlaceData k n Wp Wq),
    D.castV e (liftVec k p m Bj.z) = B0.z → D.castV e (liftVec k p m Bj.z') = B0.z' →
    (∀ y : B.Mat k m, Bj.π' y = B0.π' (D.castM e (ιLev k p m y))) →
    Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p m e) →
    Bj.μN = D.muN k m → B0.μN = D.muN k n →
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) (sx : X → B.Mat k n),
      (∀ x, sx x ∈ Sset k n B0.z) ∧
      ∀ g ∈ JF.Om k m Bj.z Bj.z', ∀ H : B.Mat k n → (Wq →L[ℂ] Wp),
        ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0} →
        (∃ R : ℝ, ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) →
        Integrable (fun x => ℓ x (PBG.Kr B0 H (sx x * D.castM e (U.mMap k p m (U.hMat σ d) g)))) μ ∧
        B.JF Bj (U.PhiFun (s := 0) k m σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
            (fun a => a.elim0)) g =
          ∫ x, ℓ x (PBG.Kr B0 H (sx x * D.castM e (U.mMap k p m (U.hMat σ d) g))) ∂μ

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjCut
section
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CapAdjInt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s Y : ℂ) (μ : Measure (Mt k r)),
    B.IsHaarOn (B.GV k r) μ → ∀ φ ψ : B.Mat k r → (Wq →L[ℂ] Wp),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
    (∫ x : Mt k r, B.hsInner (φ (Matrix.of x)) (B.opAdj (capTh k r Wp Wq s Y) ψ (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, B.hsInner (φ (Matrix.of x)) (conj s • Q.CV k r (conj Y) ψ (Matrix.of x)) ∂μ

def CapAdjFromInt : Prop := CapAdjInt → CapAdj

end Formalism.FourierDecayAlt.P.CutMP.ER
end

