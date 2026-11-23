module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurGA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSFA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HsInnerSmulSmul
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

namespace Cut3H

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem hsVec_smul (c : ℂ) (A : Wp →L[ℂ] Wp) : hsVec (c • A) = c • hsVec A := rfl

theorem hsInner_smul_smul (c c' : ℂ) (A B : Wp →L[ℂ] Wp) :
    hsInner (c • A) (c' • B) = c * star c' * hsInner A B := by
  unfold hsInner
  rw [hsVec_smul, hsVec_smul, inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  ring

end Cut3H

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Cut3H

theorem stCut3 (h : UnitaryGroupStructuralFacts) : StCut3 := by
  intro hInv k r Wp _ _ _ D X hD hSq γ hγ hZ a₁ b₁ a₂ b₂ X₀ p hp
  have hI := hInv k r Wp D X hD hSq γ hγ
  have hG : ∀ g ∈ GV k r, gbar k r γ g ∈ GV k r := hI.1
  have hmul : ∀ g ∈ GV k r, ∀ g' ∈ GV k r, th k r γ (g * g') = th k r γ g' * th k r γ g := hI.2.2.2.2.1
  have thG : ∀ g ∈ GV k r, th k r γ g ∈ GV k r := fun g hg => WeylGroupFacts.uh_inv (hG g hg)
  have hrep := X.rep.1.2
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have m1 : (Matrix.of p.1.1 : Mat k r) ∈ GV k r := h1.1
  have m2 : (Matrix.of p.1.2 : Mat k r) ∈ GV k r := h2.1
  have m3 : (Matrix.of p.2.1 : Mat k r) ∈ GV k r := h3.1
  have m4 : (Matrix.of p.2.2 : Mat k r) ∈ GV k r := h4.1
  set A : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hA
  set B : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hB
  have mA : A ∈ GV k r := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv m1) (WeylGroupFacts.uh_inv m2)
  have mB : B ∈ GV k r := WeylGroupFacts.uh_mul m4 m3
  set P : Wp →L[ℂ] Wp := (D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹) with hP
  set x : X.Hs := X.σ (th k r γ A) a₁ with hx
  set y : X.Hs := ContinuousLinearMap.adjoint (X.σ (th k r γ B)) b₁ with hy
  have key : ∀ g : Mat k r, g ∈ GV k r →
      hsInner (rho D p (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) g) (mc X a₂ b₂ g • X₀) =
        hsInner P X₀ * (⟪y, X.σ (th k r γ g) x⟫_ℂ * star ⟪b₂, X.σ g a₂⟫_ℂ) := by
    intro g hg
    have e1 : sgs p g = A * g * B := by simp only [sgs, hA, hB, Matrix.mul_assoc]
    have mAg : A * g ∈ GV k r := WeylGroupFacts.uh_mul mA hg
    have e2 : th k r γ (sgs p g) = th k r γ B * (th k r γ g * th k r γ A) := by
      rw [e1, hmul _ mAg _ mB, hmul _ mA _ hg]
    have e3 : X.σ (th k r γ (sgs p g)) =
        (X.σ (th k r γ B)).comp ((X.σ (th k r γ g)).comp (X.σ (th k r γ A))) := by
      rw [e2, hrep _ (thG _ mB) _ (WeylGroupFacts.uh_mul (thG _ hg) (thG _ mA)), hrep _ (thG _ hg) _ (thG _ mA)]
    have e4 : rho D p (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) g = (mc X a₁ b₁ (th k r γ (sgs p g))) • P := by
      simp only [rho, scalF, Function.comp_apply, hP, hD.π_eq, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.comp_smul, ContinuousLinearMap.id_comp]
    rw [e4, hsInner_smul_smul]
    have e5 : mc X a₁ b₁ (th k r γ (sgs p g)) = ⟪y, X.σ (th k r γ g) x⟫_ℂ := by
      rw [mc, e3, hy, hx, ContinuousLinearMap.adjoint_inner_left]
      rfl
    rw [e5, mc]
    ring
  unfold Ph
  have hae : ∀ᵐ g ∂D.μG, (g : Mt k r) ∈ (GV k r : Set (Mt k r)) := mem_ae_iff.2 D.haarG.conc
  rw [integral_congr_ae (g := fun g : Mt k r =>
      hsInner P X₀ * (⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪b₂, X.σ (Matrix.of g) a₂⟫_ℂ))
    (by filter_upwards [hae] with g hg; exact key _ hg)]
  rw [integral_const_mul, hZ x y a₂ b₂, mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.IsTestGTranslate
section
noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace Cut0Aux

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def lmulCLM (a : Mat k r) : Mat k r →L[ℝ] Mat k r where
  toFun y := a * y
  map_add' y y' := Matrix.mul_add a y y'
  map_smul' c y := Matrix.mul_smul a c y
  cont := continuous_const.matrix_mul continuous_id

theorem cont_lmulM (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  show Continuous fun x => a * Matrix.of x
  exact continuous_const.matrix_mul continuous_id

def lmulME (a b : Mat k r) (hab : a * b = 1) (hba : b * a = 1) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM (k := k) (r := r) a
  invFun := lmulM (k := k) (r := r) b
  left_inv x := by
    show b * (a * Matrix.of x) = x
    rw [← Matrix.mul_assoc, hba, Matrix.one_mul]
    rfl
  right_inv x := by
    show a * (b * Matrix.of x) = x
    rw [← Matrix.mul_assoc, hab, Matrix.one_mul]
    rfl
  measurable_toFun := (cont_lmulM a).measurable
  measurable_invFun := (cont_lmulM b).measurable

theorem isTestG_translate {g : Mat k r} (hg : g ∈ GV k r) {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    IsTestG (fun y => φ (g⁻¹ * y)) := by
  obtain ⟨hsm, K, hK, hKv⟩ := hφ
  have hgi : g⁻¹ ∈ GV k r := WeylGroupFacts.uh_inv hg
  have hdet := WeylGroupFacts.isUnit_of_uh hg
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  refine ⟨fun g₀ hg₀ => ?_, (fun y => g * y) '' K,
    hK.image (continuous_const.matrix_mul continuous_id), fun y hy hyK => ?_⟩
  · obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hsm (g⁻¹ * g₀) (WeylGroupFacts.uh_mul hgi hg₀)
    refine ⟨(fun y => g⁻¹ * y) ⁻¹' U, fun y => f' (g⁻¹ * y),
      hU.preimage (continuous_const.matrix_mul continuous_id), hgU, ?_,
      fun y hyU hyG => hfe _ hyU (WeylGroupFacts.uh_mul hgi hyG)⟩
    exact hf'.comp (lmulCLM g⁻¹).contDiff.contDiffOn (fun y hy => hy)
  · apply hKv _ (WeylGroupFacts.uh_mul hgi hy)
    intro hK'
    apply hyK
    refine ⟨g⁻¹ * y, hK', ?_⟩
    show g * (g⁻¹ * y) = y
    rw [← Matrix.mul_assoc, hgg, Matrix.one_mul]

theorem sigInt_translate {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (X : SigData k r)
    {g : Mat k r} (hg : g ∈ GV k r) (φ : Mat k r → ℂ) :
    sigInt D X (fun y => φ (g⁻¹ * y)) X.w = X.σ g (sigInt D X φ X.w) := by
  have hdet := WeylGroupFacts.isUnit_of_uh hg
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  have hgg' : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdet
  let e := lmulME (k := k) (r := r) g g⁻¹ hgg hgg'
  have hmap : D.μG.map e = D.μG := D.haarG.left g hg
  have hconc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ GV k r := ae_iff.mpr D.haarG.conc
  let L : X.Hs →ₗᵢ[ℂ] X.Hs :=
    { toLinearMap := (X.σ g).toLinearMap, norm_map' := fun v => X.rep.2.1 g hg v }
  have hL : ∀ v, L v = X.σ g v := fun v => rfl
  unfold sigInt
  conv_lhs => rw [← hmap]
  rw [integral_map_equiv, ← hL, ← LinearIsometry.integral_comp_comm]
  refine integral_congr_ae ?_
  filter_upwards [hconc] with x hx
  have h1 : Matrix.of (e x) = g * Matrix.of x := rfl
  rw [h1, ← Matrix.mul_assoc, hgg', Matrix.one_mul, X.rep.1.2 g hg _ hx, map_smul]
  rfl

end Cut0Aux

theorem stCut0 (h : UnitaryGroupStructuralFacts) : StCut0 := by
  intro k r Wp _ _ _ D X g hg v hv
  obtain ⟨φ, hφ, rfl⟩ := hv
  exact ⟨fun y => φ (g⁻¹ * y), Cut0Aux.isTestG_translate hg hφ, (Cut0Aux.sigInt_translate D X hg φ).symm⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeConv
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem bc_continuous_ell (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Continuous (ell k r z) := by
  unfold ell
  refine continuous_finsetSum _ (fun a _ => ?_)
  split_ifs <;> fun_prop

theorem bc_norm_psiD {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (m : Mat k r) :
    ‖psiD D m‖ = 1 := by
  simp [psiD, psi, Complex.norm_exp]

theorem stBeConv (h : UnitaryGroupStructuralFacts) : StBeConv := by
  intro k r Wp _ _ _ D X hD hsq b hb u v ⟨C, hC⟩
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGL, -, -, -, hCG, hCN, hCW, -⟩, -⟩ := id h
  have sW := bc_isHaarOn_sigmaFinite D.haarW
  have sN := bc_isHaarOn_sigmaFinite D.haarN
  have hint := (stSInt h k r Wp D hD b (bc_AB_le_of b hb)).const_mul C
  set S : Set (Mt k r × Mt k r) := {p | (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧
    (Matrix.of p.2 : Mat k r) ∈ Nset k r} with hSdef
  have aeS : ∀ᵐ p ∂(D.μW.prod D.μN), p ∈ S :=
    bc_ae_prod_and (bc_isHaarOn_ae_mem D.haarW) (bc_isHaarOn_ae_mem D.haarN)
  have hinvW : ∀ x ∈ UWset k r D.z, x⁻¹ ∈ UWset k r D.z := (hCW k r D.z).inv_mem
  have hnorm : ∀ p ∈ S, ‖beInt D X u v p‖ ≤ C * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) := by
    intro p hp
    have hG : (Matrix.of p.2 : Mat k r) * Matrix.of p.1 ∈ GV k r := (hCG k r).mul_mem _ hp.2.1 _ hp.1.1
    have h1 := hC _ hG
    have hπ : ‖D.π (Matrix.of p.1 : Mat k r)⁻¹‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => ?_)
      rw [D.π_unitary _ (hinvW _ hp.1) w, one_mul]
    unfold beInt
    rw [norm_smul, norm_mul, norm_star, bc_norm_psiD, mul_one]
    calc ‖mc X u v (Matrix.of p.2 * Matrix.of p.1)‖ * ‖D.π (Matrix.of p.1 : Mat k r)⁻¹‖
        ≤ ‖mc X u v (Matrix.of p.2 * Matrix.of p.1)‖ * 1 :=
          mul_le_mul_of_nonneg_left hπ (norm_nonneg _)
      _ ≤ C * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) := by rw [mul_one]; exact h1
  refine Integrable.mono' hint ?_ ?_
  · have cW : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r D.z} := (hCW k r D.z).closed
    have cN : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ Nset k r} := (hCN k r).closed
    have hSmeas : MeasurableSet S :=
      (cW.measurableSet.preimage measurable_fst).inter (cN.measurableSet.preimage measurable_snd)
    have c1 : ContinuousOn (fun p : Mt k r × Mt k r => mc X u v (Matrix.of p.2 * Matrix.of p.1)) S := by
      have hm : ContinuousOn (fun p : Mt k r × Mt k r => X.σ (Matrix.of p.2 * Matrix.of p.1) u) S :=
        (X.rep.2.2 u).comp (bc_continuous_mulM.comp continuous_swap).continuousOn
          (fun p hp => (hCG k r).mul_mem _ hp.2.1 _ hp.1.1)
      exact continuousOn_const.inner hm
    have c2 : Continuous (fun p : Mt k r × Mt k r => star (psiD D (Matrix.of p.2))) := by
      unfold psiD psi
      exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul ((bc_continuous_ell k r D.z).comp continuous_snd)))))).star
    have c3 : ContinuousOn (fun p : Mt k r × Mt k r => D.π (Matrix.of p.1 : Mat k r)⁻¹) S := by
      refine D.π_cont.comp (f := fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)⁻¹) ?_
        (fun p hp => hinvW _ hp.1)
      intro p hp
      apply ContinuousAt.continuousWithinAt
      have hdet : (Matrix.of p.1 : Mat k r).det ≠ 0 := ((hCW k r D.z).unit _ hp.1).ne_zero
      have hi : ContinuousAt (fun x : Mat k r => x⁻¹) (Matrix.of p.1) :=
        continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
      exact hi.comp (f := fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) continuous_fst.continuousAt
    have hcont : ContinuousOn (beInt D X u v) S := (c1.mul c2.continuousOn).smul c3
    have hm := hcont.aestronglyMeasurable (μ := D.μW.prod D.μN) hSmeas
    rwa [Measure.restrict_eq_self_of_ae_mem aeS] at hm
  · filter_upwards [aeS] with p hp
    exact hnorm p hp

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoG
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem psiM_inv' {k r : ℕ} (u : Formalism.REAL.UJ (epsG k r)) : psiM k r u⁻¹ = (psiM k r u)⁻¹ := by
  exact (Matrix.inv_eq_right_inv (by rw [← psiM_mul, mul_inv_cancel, psiM_one])).symm

theorem stDichoG (h : UnitaryGroupStructuralFacts) : StDichoG := by
  intro k r Wp _ _ _ D X hD hSq γ hγ
  obtain ⟨hgbG, -, -, -, hanti', hinv', hμG, -, -⟩ := stInvGroup h k r Wp D X hD hSq γ hγ
  have hG := D.haarG
  haveI := nuG_left hG
  haveI := nuG_inv hG
  haveI := nuG_openPos hG
  haveI : Nontrivial X.Hs := ⟨⟨X.w, 0, fun e => by have hw := X.w_norm; simp [e] at hw⟩⟩
  have inj := (isClosedEmbedding_psiM k r).injective

  have hex : ∀ u : Formalism.REAL.UJ (epsG k r), ∃ u', psiM k r u' = gbar k r γ (psiM k r u) := by
    intro u
    have hm : gbar k r γ (psiM k r u) ∈ Set.range (psiM k r) := by
      rw [range_psiM]
      exact hgbG _ (psiM_mem u)
    exact hm
  choose G hGs using hex
  let θ : Formalism.REAL.UJ (epsG k r) → Formalism.REAL.UJ (epsG k r) := fun u => (G u)⁻¹
  have hθ : ∀ u, psiM k r (θ u) = th k r γ (psiM k r u) := by
    intro u
    simp only [θ, th, psiM_inv', hGs]
  have hanti : ∀ a b, θ (a * b) = θ b * θ a := by
    intro a b
    apply inj
    rw [hθ, psiM_mul, psiM_mul, hθ, hθ]
    exact hanti' _ (psiM_mem a) _ (psiM_mem b)
  have hinv : ∀ u, θ (θ u) = u := by
    intro u
    apply inj
    rw [hθ, hθ]
    exact hinv' _ (psiM_mem u)
  have hgbar : Continuous (gbar k r γ) := by
    unfold gbar
    exact ((continuous_const.matrix_mul ((((continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const).matrix_map Complex.continuous_conj))).matrix_mul continuous_const)
  have hGc : Continuous G := by
    rw [(isClosedEmbedding_psiM k r).toIsEmbedding.continuous_iff]
    have e : psiM k r ∘ G = gbar k r γ ∘ psiM k r := funext hGs
    rw [e]
    exact hgbar.comp (continuous_psiM k r)
  have hθc : Continuous θ := continuous_inv.comp hGc
  have hE := measurableEmbedding_psiG k r
  let T : Mt k r → Mt k r := fun x => fun i j => th k r γ (Matrix.of x) i j
  have hT : AEMeasurable T D.μG := by
    have hc : Continuous (fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) := by
      exact continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply j).comp ((continuous_apply i).comp (hgbar.comp continuous_id))
    exact (InvGrp.measurable_invM.comp hc.measurable).aemeasurable
  have hcomp : psiG k r ∘ θ = T ∘ psiG k r := by
    funext u
    show Matrix.of.symm (psiM k r (θ u)) = fun i j => th k r γ (Matrix.of (psiG k r u)) i j
    rw [of_psiG, hθ]
    rfl
  have key : ((nuG D.μG).map θ).map (psiG k r) = (nuG D.μG).map (psiG k r) := by
    rw [Measure.map_map hE.measurable hθc.measurable, hcomp,
      ← AEMeasurable.map_map_of_aemeasurable (by rw [map_nuG hG]; exact hT) hE.measurable.aemeasurable,
      map_nuG hG]
    exact hμG
  have hmap : (nuG D.μG).map θ = nuG D.μG := by
    calc (nuG D.μG).map θ = (((nuG D.μG).map θ).map (psiG k r)).comap (psiG k r) := (hE.comap_map _).symm
      _ = ((nuG D.μG).map (psiG k r)).comap (psiG k r) := by rw [key]
      _ = nuG D.μG := hE.comap_map _
  have hSR : Formalism.MainNotions.BridgeCSchur.SqRep (nuG D.μG)
      (fun u => X.σ (psiM k r u)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [psiM_one]; exact X.rep.1.1
    · intro a b
      rw [psiM_mul]; exact X.rep.1.2 _ (psiM_mem a) _ (psiM_mem b)
    · intro g v
      exact X.rep.2.1 _ (psiM_mem g) v
    · intro v
      exact (X.rep.2.2 v).comp_continuous (continuous_psiM k r) psiM_mem
    · intro v w
      have hs := hSq v w
      rw [← map_nuG hG] at hs
      have hs' := (hE.memLp_map_measure_iff).mp hs
      convert hs' using 1
      simp [mc, Function.comp_def, of_psiG]
  have hI : ∀ S : Submodule ℂ X.Hs, IsClosed (S : Set X.Hs) →
      (∀ u : Formalism.REAL.UJ (epsG k r), ∀ v ∈ S, X.σ (psiM k r u) v ∈ S) →
      S = ⊥ ∨ S = ⊤ := by
    intro S hS hinv
    apply X.irr S hS
    intro g hg v hv
    obtain ⟨u, rfl⟩ : g ∈ Set.range (psiM k r) := by rw [range_psiM]; exact hg
    exact hinv u v hv
  rcases schurDichotomy (Formalism.REAL.UJ (epsG k r)) (nuG D.μG) X.Hs θ (fun u => X.σ (psiM k r u)) hθc hanti hinv
      hmap hSR.one hSR.mul hSR.iso hSR.cont hSR.sq hI with h0 | ⟨C, hC1, hC2⟩
  · left
    intro x y x' y'
    rw [← map_nuG hG, hE.integral_map]
    simp only [of_psiG, ← hθ]
    exact h0 x y x' y'
  · right
    refine ⟨C, ?_, ?_⟩
    · intro g hg x y
      obtain ⟨u, rfl⟩ : g ∈ Set.range (psiM k r) := by rw [range_psiM]; exact hg
      rw [← hθ]
      exact hC1 u x y
    · intro g hg v
      obtain ⟨u, rfl⟩ : g ∈ Set.range (psiM k r) := by rw [range_psiM]; exact hg
      rw [← hθ, ← psiM_inv']
      exact hC2 u v

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSF
section
open MeasureTheory
open scoped NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def HaarUniqueSF : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)) (μ₀ μ : Measure (Mt k r)), IsClosedSubgroup U → Formalism.FourierDecayAlt.B.IsHaarOn U μ₀ →
    Formalism.MainNotions.S.IsHaarOn U μ → ∃ c : ℝ≥0, c ≠ 0 ∧ μ = c • μ₀

theorem haarUniqueSF' : HaarUniqueSF := by
  intro k r U μ₀ μ hU h₀ hμ
  have : Fact (IsClosedSubgroup U) := ⟨hU⟩
  obtain ⟨hσ, hne, hconc, hleft⟩ := hμ
  have : IsFiniteMeasureOnCompacts μ₀ := ⟨h₀.finite_compact⟩
  have hcμ : μ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hconc
  have hcν : μ₀ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := h₀.conc
  have := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ
  have := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ₀
  have := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap (U := U) μ hcμ hleft
  have := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap (U := U) μ₀ hcν h₀.left
  have hμS : μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Mt k r) ≠ 0 := fun h0 => hne (by
    rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ hcμ, h0, Measure.map_zero])
  have hνS : μ₀.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Mt k r) ≠ 0 := fun h0 => h₀.ne_zero (by
    rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ₀ hcν, h0, Measure.map_zero])
  obtain ⟨c, hc0, hc⟩ := HaarSigmaFiniteUniqueness.eq_smul_of_sigmaFinite _ _ hμS hνS
  refine ⟨c, hc0, ?_⟩
  rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ hcμ, hc, Measure.map_smul,
    HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ₀ hcν]
  exact (HaarSigmaFiniteUniqueness.mEmb (U := U)).measurable.aemeasurable

theorem haarUniqueSF (_h : UnitaryGroupStructuralFacts) : HaarUniqueSF := haarUniqueSF'

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut4
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stCut4 (h : UnitaryGroupStructuralFacts) : StCut4 := by
  intro hS k r Wp _ _ _ D hD γ P₁ Q P₂ Q₂ hPQ
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z :=
    ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarW.conc)
  have key : ∀ g ∈ UWset k r D.z, ∀ x y : Wp,
      ⟪P₁ y, D.π g (Q x)⟫_ℂ = ⟪P₂ y, D.π (th k r γ g) (Q₂ x)⟫_ℂ := by
    intro g hg x y
    have e := congrArg (fun T : Wp →L[ℂ] Wp => ⟪y, T x⟫_ℂ) (hPQ g hg)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right] using e
  have hL : ∀ x y ξ η : Wp,
      ∫ g : Mt k r, ⟪P₁ y, D.π (Matrix.of g) (Q x)⟫_ℂ * star ⟪ξ, D.π (Matrix.of g) η⟫_ℂ ∂D.μW =
        ⟪η, Q x⟫_ℂ * ⟪P₁ y, ξ⟫_ℂ / (Module.finrank ℂ Wp : ℂ) :=
    fun x y ξ η => hS k r Wp D hD (Q x) (P₁ y) η ξ
  have hE : ∀ x y ξ η : Wp,
      ∫ g : Mt k r, ⟪P₁ y, D.π (Matrix.of g) (Q x)⟫_ℂ * star ⟪ξ, D.π (Matrix.of g) η⟫_ℂ ∂D.μW =
        ∫ g : Mt k r, ⟪P₂ y, D.π (th k r γ (Matrix.of g)) (Q₂ x)⟫_ℂ *
          star ⟪ξ, D.π (Matrix.of g) η⟫_ℂ ∂D.μW := by
    intro x y ξ η
    refine integral_congr_ae (hW.mono fun g hg => ?_)
    simp only [key _ hg]
  have hdim : (Module.finrank ℂ Wp : ℂ) = 0 → ∀ v : Wp, v = 0 := fun h0 =>
    finrank_zero_iff_forall_zero.1 (by exact_mod_cast h0)
  refine ⟨fun h0 x y ξ η => ?_, fun C₀ hC x y ξ η => ?_⟩
  · have e := (hL x y ξ η).symm.trans ((hE x y ξ η).trans (h0 (Q₂ x) (P₂ y) η ξ))
    by_cases hn : (Module.finrank ℂ Wp : ℂ) = 0
    · simp [hdim hn η]
    · exact (div_eq_zero_iff.1 e).resolve_right hn
  · have e2 : ∫ g : Mt k r, ⟪P₂ y, D.π (th k r γ (Matrix.of g)) (Q₂ x)⟫_ℂ *
          star ⟪ξ, D.π (Matrix.of g) η⟫_ℂ ∂D.μW =
        ⟪η, C₀ (P₂ y)⟫_ℂ * ⟪C₀ (Q₂ x), ξ⟫_ℂ / (Module.finrank ℂ Wp : ℂ) := by
      rw [← hS k r Wp D hD (C₀ (P₂ y)) (C₀ (Q₂ x)) η ξ]
      refine integral_congr_ae (hW.mono fun g hg => ?_)
      simp only [hC _ hg]
    have e := (hL x y ξ η).symm.trans ((hE x y ξ η).trans e2)
    by_cases hn : (Module.finrank ℂ Wp : ℂ) = 0
    · simp [hdim hn η]
    · exact (div_left_inj' hn).1 e

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

