module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0221
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0190
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0216
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0226
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0125
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0192
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0195
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0184
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0197
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CayleySmoothnessHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0203
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0189
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFixesTailCoords
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0223
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtieLevTransportHerOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0225
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0210
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JacquetRaisingOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialSideRaising
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0206

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTopKr
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem emb_mu_uni {k p ρ : ℕ} (ν : B.Mat k ρ) (V : Matrix (Fin p) (Fin p) ℂ) (a : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (b : Matrix (Fin p) (Fin p) ℂ) (c : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) :
    U.embG k p ρ ν * U.muP k p ρ V * U.blk3 1 a b 0 1 c 0 0 1 =
      U.blk3 V (V * a) (V * b) 0 ν (ν * c) 0 0 (G.wMat p * Vᴴ⁻¹ * G.wMat p) := by
  unfold U.embG U.muP
  rw [Ux3.block3_mul, Ux3.block3_mul]
  congr 1 <;> simp

theorem upper_inj {p : ℕ} {u u' : G.UT p → ℂ} (h : G.upper u = G.upper u') : u = u' := by
  funext p
  have h1 := congrFun (congrFun h p.1.1) p.1.2
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_lt p.2),
    zero_add, dif_pos p.2] at h1
  exact h1

theorem kr_eq_integral_krI_psiR {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k (p + ρ))
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (y₀ : B.Mat k (p + ρ)) :
    PBG.Kr B0 H y₀ = ∫ s, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s) ∂(LeftFubiniLemmas.muR (p := p) Bj) := by
  classical
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ

  set S : Set (LeftFubiniLemmas.XR k p ρ) := {s | LeftFubiniLemmas.GoodR Bj s} with hSdef
  have hSc : IsClosed S :=
    IsClosed.and ((Formalism.FourierDecayAlt.P.B6.isClosed_UWset k ρ Bj.z').preimage (continuous_fst.comp continuous_fst))
      ((Formalism.FourierDecayAlt.P.B6.isClosed_Nset k ρ).preimage (continuous_snd.comp continuous_fst))
  have hBS : BorelSpace (LeftFubiniLemmas.XR k p ρ) := by
    have : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ × (G.UT p → ℂ)) := Prod.borelSpace
    have : BorelSpace (Mt k ρ × Mt k ρ) := Prod.borelSpace
    exact Prod.borelSpace
  have hSm : MeasurableSet S := hSc.measurableSet

  have hmp : MeasurePreserving (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) (LeftFubiniLemmas.muR Bj) (B0.μW'.prod B0.μN) := by
    have h := LeftFubiniLemmas.right_measure_preserving k p ρ Bj.z' Bj.μW' B0.μW' Bj.haarW' hW' hW0'
    unfold LeftFubiniLemmas.muR
    rw [hN0, hNj]
    exact h

  have hinj : Set.InjOn (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) S := by
    intro s hs s' hs' he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    have h11 : s.1.1 = s'.1.1 := by
      have := congrArg (Formalism.FourierDecayAlt.P.PBM.midMt p ρ rfl) he1
      simpa only [LeftFubiniLemmas.PsiR, Formalism.FourierDecayAlt.P.PBM.midMt_levMt] using this
    have hN : LeftFubiniLemmas.NR s = LeftFubiniLemmas.NR s' := Matrix.of.symm.injective he2
    obtain ⟨a, b, c, hRn⟩ : ∃ a b c, U.Rn k p ρ (LeftFubiniLemmas.rcAct (Matrix.of s.1.1) s.2.1) = U.blk3 1 a b 0 1 c 0 0 1 :=
      ⟨_, _, _, Formalism.FourierDecayAlt.P.Ux3.rn_eq _⟩
    obtain ⟨a', b', c', hRn'⟩ : ∃ a b c, U.Rn k p ρ (LeftFubiniLemmas.rcAct (Matrix.of s'.1.1) s'.2.1) = U.blk3 1 a b 0 1 c 0 0 1 :=
      ⟨_, _, _, Formalism.FourierDecayAlt.P.Ux3.rn_eq _⟩
    unfold LeftFubiniLemmas.NR at hN
    rw [hRn, hRn', emb_mu_uni, emb_mu_uni, Formalism.FourierDecayAlt.P.Ux3.block3_eq_iff] at hN
    obtain ⟨hU, hUa, hUb, -, hν, hνc, -, -, -⟩ := hN
    have hUu : IsUnit (G.upper s.2.2).det := by rw [Formalism.FourierDecayAlt.P.Ux3.det_upper]; exact isUnit_one
    have hνu : IsUnit (Matrix.of s.1.2 : B.Mat k ρ).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hs.2.1
    have hu : s.2.2 = s'.2.2 := upper_inj hU
    rw [← hU] at hUa hUb
    rw [← hν] at hνc
    have ha : a = a' := by
      have := congrArg (fun M => (G.upper s.2.2)⁻¹ * M) hUa
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul] using this
    have hb : b = b' := by
      have := congrArg (fun M => (G.upper s.2.2)⁻¹ * M) hUb
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul] using this
    have hc : c = c' := by
      have := congrArg (fun M => (Matrix.of s.1.2 : B.Mat k ρ)⁻¹ * M) hνc
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hνu, Matrix.one_mul] using this
    have hR : LeftFubiniLemmas.rcAct (Matrix.of s.1.1) s.2.1 = LeftFubiniLemmas.rcAct (Matrix.of s'.1.1) s'.2.1 :=
      (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).1 (by rw [hRn, hRn', ha, hb, hc])
    rw [← h11] at hR
    have hhu : IsUnit (Matrix.of s.1.1 : B.Mat k ρ).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hs.1.1
    have h21 : s.2.1 = s'.2.1 := by
      have e1 := congrArg Prod.fst hR
      have e2 := congrArg Prod.snd hR
      simp only [LeftFubiniLemmas.rcAct] at e1 e2
      have e1' : (Matrix.of s.1.1 : B.Mat k ρ) * Matrix.of s.2.1.1 = Matrix.of s.1.1 * Matrix.of s'.2.1.1 := by
        ext v w; exact congrFun (congrFun e1 v) w
      have e3 := congrArg (fun M => (Matrix.of s.1.1 : B.Mat k ρ)⁻¹ * M) e1'
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hhu, Matrix.one_mul] at e3
      exact Prod.ext (by ext v w; exact congrFun (congrFun e3 v) w) e2
    have h12 : s.1.2 = s'.1.2 := by
      ext v w; exact congrFun (congrFun hν v) w
    exact Prod.ext (Prod.ext h11 h12) (Prod.ext h21 hu)
  have hres : (LeftFubiniLemmas.muR (p := p) Bj).restrict S = LeftFubiniLemmas.muR Bj :=
    Measure.restrict_eq_self_of_ae_mem (LeftFubiniLemmas.ae_goodR Bj)
  have hcont : Continuous (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) := by
    unfold LeftFubiniLemmas.PsiR
    exact ((Formalism.FourierDecayAlt.P.PBM.levMt_cont p ρ rfl).comp (continuous_fst.comp continuous_fst)).prodMk LeftFubiniLemmas.NR_cont
  have hPol : PolishSpace (LeftFubiniLemmas.XR k p ρ) := {}
  have hSB : StandardBorelSpace (LeftFubiniLemmas.XR k p ρ) := inferInstance
  have : StandardBorelSpace S := hSm.standardBorel
  have hemb : MeasurableEmbedding (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) :=
    (hcont.measurable.comp measurable_subtype_coe).measurableEmbedding
      (fun a b hab => Subtype.ext (hinj a.2 b.2 hab))
  rw [LeftFubiniLemmas.kr_eq_int]
  calc ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂(B0.μW'.prod B0.μN)
      = ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂((LeftFubiniLemmas.muR (p := p) Bj).map LeftFubiniLemmas.PsiR) := by rw [hmp.map_eq]
    _ = ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂((Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)).map
          (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ))) := by
        rw [show (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) = LeftFubiniLemmas.PsiR ∘ Subtype.val from rfl,
          ← Measure.map_map hcont.measurable measurable_subtype_coe, map_comap_subtype_coe hSm, hres]
    _ = ∫ s : S, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) ∂(Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)) :=
        hemb.integral_map _
    _ = ∫ s, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s) ∂((Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)).map
          (Subtype.val : S → LeftFubiniLemmas.XR k p ρ)) :=
        ((MeasurableEmbedding.subtype_coe hSm).integral_map (fun s => LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s))).symm
    _ = _ := by rw [map_comap_subtype_coe hSm, hres]

end Formalism.FourierDecayAlt.P.PBQ
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapShared
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jABddKapQQ_of_shared (hG : SSn.SSnGeom) (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines)
    (hDU : SSn.Rep.DatumUnit) : JABddKapQQ :=
  jABddKapQQ_of_cut hG hPE hGL hDU weighted_norm_facts_hold

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjComm
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

theorem adjoint_commutation_holds : AdjComm := adjComm_of_parts fundamental_domain_group adjoint_continuity_holds adjoint_integral_identity_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem conj_phD_sq {r : ℕ} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) :
    (conj (SSn.phD c)) ^ 2 = (∏ i, conj (c i)) * ∏ i, (c i)⁻¹ := by
  have hP : (∏ i, c i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  rw [← map_prod, Finset.prod_inv_distrib]
  unfold SSn.phD
  set D := ∏ i, c i with hD
  have hn : ((‖D‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hP
  have hnn : ((‖D‖ : ℝ) : ℂ) ^ 2 = D * conj D := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [map_div₀, Complex.conj_ofReal, div_pow, hnn]
  field_simp

section gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem cd_comp {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {U V W : Type} [NormedAddCommGroup U]
    [NormedSpace ℂ U] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {n : WithTop ℕ∞} {g : X → V →L[ℂ] W} {f : X → U →L[ℂ] V} (hg : ContDiff ℝ n g) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => (g x).comp (f x)) :=
  ((ContinuousLinearMap.compL ℂ U V W).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp (hg.prodMk hf)

theorem hsVec_zero' : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsVec; ext i; simp

theorem hsInner_zero_l (B' : Wq →L[ℂ] Wp) : B.hsInner (0 : Wq →L[ℂ] Wp) B' = 0 := by
  unfold B.hsInner; rw [hsVec_zero', inner_zero_right]

theorem hsInner_zero_r (A : Wq →L[ℂ] Wp) : B.hsInner A (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsInner; rw [hsVec_zero', inner_zero_left]

theorem inner_hs_smul (c : ℂ) (A B' : Wq →L[ℂ] Wp) :
    inner ℂ (B.hsVec A) (B.hsVec (c • B')) = c * inner ℂ (B.hsVec A) (B.hsVec B') := by
  rw [Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right]

theorem mat_gen {Ty : Type} [Fintype Ty] [DecidableEq Ty] (Qd : Ty → (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))
    (T0 : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (c : Ty → Ty → ℂ) (e : Ty → (Wq →L[ℂ] Wp))
    (hQadj : ∀ σ A B', B.hsInner (Qd σ A) B' = B.hsInner A (Qd σ B'))
    (hline : ∀ σ ρ, Qd σ (e ρ) = if σ = ρ then e ρ else 0) (π ρ : Ty) :
    B.hsInner (∑ π', ∑ ρ', c π' ρ' • Qd ρ' (T0 (Qd π' (e π)))) (e ρ) = c π ρ * B.hsInner (T0 (e π)) (e ρ) := by
  rw [kap_hsInner_sum_left, Finset.sum_eq_single π]
  · rw [kap_hsInner_sum_left, Finset.sum_eq_single ρ]
    · rw [kap_hsInner_smul_left, hQadj, hline π π, hline ρ ρ, if_pos rfl, if_pos rfl]
    · intro ρ' _ hne
      rw [kap_hsInner_smul_left, hQadj, hline ρ' ρ, if_neg hne, hsInner_zero_r, mul_zero]
    · intro h; exact absurd (Finset.mem_univ ρ) h
  · intro π' _ hne
    rw [hline π' π, if_neg hne, map_zero]
    simp only [map_zero, smul_zero, Finset.sum_const_zero]
    exact hsInner_zero_l _
  · intro h; exact absurd (Finset.mem_univ π) h

theorem mat_gen' {Ty : Type} [Fintype Ty] [DecidableEq Ty] (Qd : Ty → (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))
    (T0 : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (c : Ty → Ty → ℂ) (e : Ty → (Wq →L[ℂ] Wp))
    (hQadj : ∀ σ A B', B.hsInner (Qd σ A) B' = B.hsInner A (Qd σ B'))
    (hline : ∀ σ ρ, Qd σ (e ρ) = if σ = ρ then e ρ else 0) (π ρ : Ty) :
    inner ℂ (B.hsVec (e ρ)) (B.hsVec ((∑ π', ∑ ρ', c π' ρ' • (Qd ρ').comp (T0.comp (Qd π'))) (e π))) =
      c π ρ * inner ℂ (B.hsVec (e ρ)) (B.hsVec (T0 (e π))) := by
  have h := mat_gen Qd T0 c e hQadj hline π ρ
  unfold B.hsInner at h
  rw [← h]
  congr 2
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.comp_apply]

theorem sandw_apply (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) (X : Wq →L[ℂ] Wp) : sandw A B' X = A.comp (X.comp B') := rfl

end gen

theorem ssnRep_of (hTP : TypeProj) (hTF : ThtFacts) (hTG : ThtGaugeConst) : SSnRep := by
  obtain ⟨K, hK, hTP⟩ := hTP
  refine ⟨K, hK, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hk : 2 ≤ S.G.k := by
    have := (Finset.mem_Icc.1 hl)
    have h2 : (D.parOf S v).k = S.G.k := rfl
    omega
  obtain ⟨Qp, hQs, hQadj, hQeq, hQline⟩ := hTP Cc hCc E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ
  obtain ⟨Bw, hBw⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists (T v).base.z_mem (T v).base.T_pos
  obtain ⟨Bw', hBw'⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists (T v).base.z'_mem (T v).base.T'_pos
  obtain ⟨hc, hca, hadj, heqv, hph⟩ := hTF (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl Bw Bw' hBw hBw'
  obtain ⟨κ, hκ⟩ := hTG Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk l hl Bw Bw' hBw hBw'
  classical
  set th := tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw' with hth
  set thA := thtA S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw' with hthA
  refine ⟨fun a a' ι => ∑ π, ∑ ρ, (if M.Up (D.parOf S v) l π ρ then κ π else 0) •
      (Qp ρ a).comp ((th a a' ι).comp (Qp π a)),
    fun a a' ι => ∑ π, ∑ ρ, (if M.Up (D.parOf S v) l π ρ then conj (κ π) else 0) •
      (Qp π a).comp ((thA a a' ι).comp (Qp ρ a)), ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ContDiff.sum fun π _ => ContDiff.sum fun ρ _ => ContDiff.const_smul _ ?_
    exact cd_comp ((hQs ρ).comp contDiff_fst) (cd_comp hc ((hQs π).comp contDiff_fst))
  · refine ContDiff.sum fun π _ => ContDiff.sum fun ρ _ => ContDiff.const_smul _ ?_
    exact cd_comp ((hQs π).comp contDiff_fst) (cd_comp hca ((hQs ρ).comp contDiff_fst))
  ·
    intro a a' ι A B'
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]
    rw [kap_hsInner_sum_left, kap_hsInner_sum_right]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [kap_hsInner_sum_left, kap_hsInner_sum_right]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [kap_hsInner_smul_left, kap_hsInner_smul_right, hQadj, hadj, hQadj]
    congr 1
    split_ifs <;> simp
  ·
    intro h hh h' hh' a a' ι X
    have hsum : ∀ (F : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) →
        ((Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))),
        ((T v).base.π h).comp (((∑ π, ∑ ρ, F π ρ) X).comp ((T v).base.π' h'⁻¹)) =
          ∑ π, ∑ ρ, ((T v).base.π h).comp ((F π ρ X).comp ((T v).base.π' h'⁻¹)) := by
      intro F
      have := map_sum (sandw ((T v).base.π h) ((T v).base.π' h'⁻¹)) (fun π => (∑ ρ, F π ρ) X) Finset.univ
      simp only [sandw_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply] at this ⊢
      rw [this]
      refine Finset.sum_congr rfl fun π _ => ?_
      exact map_sum (sandw ((T v).base.π h) ((T v).base.π' h'⁻¹)) (fun ρ => F π ρ X) Finset.univ
    constructor
    · rw [hsum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]
      refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hQeq π h hh h' hh' a X, (heqv h hh h' hh' a a' ι _).1, hQeq ρ h hh h' hh' a _]
      split_ifs <;> ext y <;> simp
    · rw [hsum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]
      refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hQeq ρ h hh h' hh' a X, (heqv h hh h' hh' a a' ι _).2, hQeq π h hh h' hh' a _]
      split_ifs <;> ext y <;> simp
  ·
    intro q hq ρ π
    have hq1 : ∀ a, q.1 a ≠ 0 := hq.1
    have hζ : (D.parOf S v).TT < Complex.normSq q.2 := hq.2
    have hline := hQline q hq
    refine (mat_gen' (fun σ => Qp σ (SSn.phD q.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2))
      (th (SSn.phD q.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2)
        (conj (SSn.phD q.1) • SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2)
        (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2))
      (fun π' ρ' => if M.Up (D.parOf S v) l π' ρ' then κ π' else 0) (fun σ => e σ q.2)
      (fun σ => hQadj σ _) hline π ρ).trans ?_
    rw [hph (SSn.phD q.1), ContinuousLinearMap.smul_apply, inner_hs_smul]
    unfold SSn.ssnV
    split_ifs with hup
    · have h1 := hκ q.2 hζ π ρ hup
      rw [← conj_phD_sq hq1]
      linear_combination (conj (SSn.phD q.1)) ^ 2 * h1
    · simp

theorem second_shift_representation_assembly : SSnRepOfCut := fun hPE hGL hTF hDU hTG =>
  ssnRep_of (typeProj_of hPE hGL hDU weighted_norm_facts_hold) hTF hTG

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DegLiftOfParts
section
open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def KrHyp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (j : ℕ) (hj : j ≤ r) (H : B.Mat k r → (Wq →L[ℂ] Wp)),
    (∀ x ∈ B.GV k r, Dmin k r Bs.z Bs.z' x ⟨j, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) H x) →
    (∃ R : ℝ, ∀ x ∈ B.GV k r, H x ≠ 0 → B.gN x ≤ R) →
    ∀ y ∈ B.GV k r, Dmin k r Bs.z Bs.z' y ⟨j, by omega⟩ ≠ 0 →
      CapelliWordSumExpansion.Loc (⊤ : ℕ∞) (Kr Bs H) y ∧
      ∀ (l : C.Letter) (e : Fin 2), Kr Bs (D.vLet k r Bs.z Bs.z' j hj l e H) y = D.vLet k r Bs.z Bs.z' j hj l e (Kr Bs H) y

theorem liftDegAll_of (hLF : LeftFubiniLemmas.LeftFubini) (hNF : LeftFubiniLemmas.NFHypL) (hKr : KrHyp) : LiftDegAll := by
  intro Wp Wq _ _ _ _ _ _ P p F hF j s hj h τ ha w' a' b δ g hg
  have hsz : D.ptSize (h ++ [(s, τ)]) = D.ptSize h + s := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s τ
  have hs1 : 1 ≤ s := (ha.1 (s, τ) (by simp)).1
  have hj1 : 1 ≤ j := by rw [← ha.2, hsz]; omega
  obtain ⟨X, _, μ, ℓ, sx, hsx, hFubG⟩ := hLF P.k P.r Wp Wq p.T p.hT j hj hj1 (h ++ [(s, τ)]) ha
  have hgG : g ∈ B.GV P.k (P.r - j) := hg.1
  have hg' : D.castM (by rw [ha.2]) g ∈ B.GV P.k (P.r - D.ptSize (h ++ [(s, τ)])) :=
    Formalism.FourierDecayAlt.P.PBE.castM_GV _ hgG
  have hl : D.IsLocPt (h ++ [(s, τ)]) (D.ptSize (h ++ [(s, τ)])) := ⟨ha.1, rfl⟩
  obtain ⟨hx₁G, hxi, hy⟩ := hNF P.k P.r (h ++ [(s, τ)]) (by rw [ha.2]; exact hj) _ hg' hl
  set PC : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → Prop := fun H =>
    (∀ x ∈ B.GV P.k P.r, Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨j, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) H x) ∧
    (∃ R : ℝ, ∀ x ∈ B.GV P.k P.r, H x ≠ 0 → B.gN x ≤ R) with hPC
  refine liftDeg_core p.T F j s hj h τ ha w' a' b δ g X μ ℓ sx _ hsx hx₁G ?_ ?_ PC
    (fun H hH => hFubG g hg H (contOn_of_loc (S := {x | Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨j, by omega⟩ ≠ 0}) (fun x hx hxG => hH.1 x hxG hx)) hH.2) ?_
    (fun H hH y hyG hyD => (hKr P.k P.r Wp Wq p.T.base j hj H hH.1 hH.2 y hyG hyD).1)
    (fun H hH y hyG hyD => (hKr P.k P.r Wp Wq p.T.base j hj H hH.1 hH.2 y hyG hyD).2)
  · intro a₀ q ha₀
    rw [hxi a₀ q (by rw [hsz]; exact ha₀)]
    by_cases hq : q.val < D.ptSize h + s
    · rw [dite_eq_left (by rw [hsz]; exact hq), if_pos hq]
      exact hmat_zb h s τ hl a₀.val q.val _ _
    · rw [dite_eq_right (by rw [hsz]; exact hq), if_neg hq]
  · intro a₀ q ha₀
    rw [hy a₀ q (by rw [hsz]; exact ha₀)]
    by_cases hq : P.r + P.k < q.val ∧ 2 * P.r + P.k - q.val < D.ptSize h + s
    · rw [dite_eq_left (by rw [hsz]; exact hq), if_pos hq, hmat_zb h s τ hl a₀.val _ _ _]
    · rw [dite_eq_right (by rw [hsz]; exact hq), if_neg hq]
  · intro w e
    refine ⟨fun x hxG hxD => uwG_mem (E := Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' j hj hF.1 w e x hxD hxG, ?_⟩
    obtain ⟨R, hR⟩ := hF.2.1
    exact ⟨R, uwG_supp p.T.base.z p.T.base.z' F R hR j hj w e⟩

theorem degLift_of_parts (hLF : LeftFubiniLemmas.LeftFubini) (hKr : KrHyp) : KB.DegLift :=
  degLift_of (liftDegAll_of hLF LeftFubiniLemmas.normal_form_left_hypothesis hKr)

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfRest
section
namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem group_chart_holds : GChart := gChart_of lie_basis_holds cayley_algebraic_holds group_vector_space cayley_smoothness_holds

theorem unitary_capelli_holds : UCap := uCap_of positive_domain_is_domain right_type_action_holds left_type_action_holds

theorem jfSmoothBuilt_of_rest (hN : NDiff) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hE : ChartEqs) (hR : EllRegW) :
    JfSmoothBuilt :=
  jfSmoothBuilt_of_leaves hN unitary_capelli_holds hP hC group_chart_holds hE classical_to_weak_solution hR JfS.symbol_nilpotent_holds lie_stabilizer_splitting

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PTieAll
section
namespace Formalism.FourierDecayAlt.P

theorem ptie_levTransportHer_of_sliceStep (hS : Formalism.FourierDecayAlt.P.PTie.SliceStepHer) : Formalism.FourierDecayAlt.P.PTie.LevTransportHer :=
  ptie_levTransportHer_of jacquet_scaling hS

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbDegTopOfPolyTop
section
namespace Formalism.FourierDecayAlt.P

theorem minor_cell : PBN.MinorCell :=
  minor_cell_of_parts right_rule_derivative left_rule_cell torus_cell gauge_positivity

theorem radial_raising_top : PBN.RadAATop :=
  radial_raising_top_of_parts jacquet_raising_operator raising_cell minor_cell radial_side_raising raising_compact_support

theorem pb_degTop_of_polyTop (hPT : PBN.PolyTop) : Formalism.FourierDecayAlt.KB.DegTop := pb_degTop_of radial_raising_top hPT

end Formalism.FourierDecayAlt.P
end

