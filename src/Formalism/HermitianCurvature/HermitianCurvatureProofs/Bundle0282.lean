module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0281
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0280
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0095

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFApxDom
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def DominatedL2TruncationBound : Prop :=
  ∀ Cb C₁ : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ Th : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th →
      ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ n : ℕ, ∀ᵐ c : Fin (P.r + 1) → ℂ,
        ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
          TBB.Ew p (fun _ => 1) (B.opApply Th (fun g => cutN P.k P.r n g • f g)) (P.r + 1) [] (TBB.bigPt P.r c) ≤ h c

section cutn

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cutN_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : B.CkOn (⊤ : ℕ∞) (B.GV k r) f) (n : ℕ) :
    B.CkOn (⊤ : ℕ∞) (B.GV k r) (fun g => cutN k r n g • f g) := by
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.normSq z) := by
    simp_rw [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutN k r n) := by
    unfold cutN
    refine Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp ?_)
    refine ContDiff.div_const (contDiff_const.sub ?_) _
    refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    exact hN.comp ((contDiff_apply_apply (𝕜 := ℝ) i j).comp (contDiff_const_smul _))
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀
  refine ⟨U, fun g => cutN k r n g • f' g, hU, hgU, hc.contDiffOn.smul hf', fun g hg hgv => ?_⟩
  show cutN k r n g • f g = cutN k r n g • f' g
  rw [hff g hg hgv]

end cutn

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolTop
section
namespace Formalism.FourierDecayAlt.P.CutBP.PolTop

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem orbital_integrand_linear {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (a b : ℂ) (p : B.SS k r) :
    D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) p =
      a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p := by

  unfold D.orbIntegrand B.rho
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add, map_smul, smul_add]
  rw [smul_comm (B.xiTau Bs (1, 1) p) a, smul_comm (B.xiTau Bs (1, 1) p) b]

theorem orbJ_linear_of_decay : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (A : ℝ),
    γ ∈ B.GV k r → (∀ a, d a ≠ 0) → Zhat k r Bs.z Bs.z' γ = C2.monoP w d →
    0 < Gf k r Bs.z Bs.z' γ → C6.IsRelevant Bs γ →
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₁) Bs.μSS →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₂) Bs.μSS →
      (∀ p, Bs.inSS p → ‖H₁ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) →
      (∀ p, Bs.inSS p → ‖H₂ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) → ∀ a b : ℂ,
      D.orbJ Bs γ (D.muR Bs γ w) (fun g => a • H₁ g + b • H₂ g) =
        a • D.orbJ Bs γ (D.muR Bs γ w) H₁ + b • D.orbJ Bs γ (D.muR Bs γ w) H₂ := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs γ w d A hγ hd hZ hpos hrel hA H₁ H₂ cF hcF hm₁ hm₂ hb₁ hb₂ a b
  obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs γ w d A hγ hd hZ hpos hA
  have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs γ w d := ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZ,
    Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZ, fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZ hρ⟩
  have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
  have hInt : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c →
      AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) →
      Integrable (fun p => θ p • D.orbIntegrand Bs γ G p) Bs.μSS := fun G c hc hGm hGb =>
    Integrable.mono' (hmaj.const_mul c) (hθ.1.aestronglyMeasurable.smul hGm) (hdom G c hc hGb)
  have hEq : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c →
      AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) →
      D.orbJ Bs γ (D.muR Bs γ w) G = ∫ p, θ p • D.orbIntegrand Bs γ G p ∂Bs.μSS := by
    intro G c hc hGm hGb
    have hex : ∃ θ', D.IsNormCut Bs γ (D.muR Bs γ w) θ' ∧
        Integrable (fun p => θ' p • D.orbIntegrand Bs γ G p) Bs.μSS := ⟨θ, hθ, hInt G c hc hGm hGb⟩
    unfold D.orbJ
    rw [dif_pos hex]
    exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs γ (D.muR Bs γ w) hrel hR G _ θ hex.choose_spec.1 hθ
      hex.choose_spec.2 (hInt G c hc hGm hGb)
  have hlin : D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) =
      fun p => a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p :=
    funext fun p => orbital_integrand_linear Bs γ H₁ H₂ a b p
  have hm : AEStronglyMeasurable (D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g)) Bs.μSS := by
    rw [hlin]
    exact (hm₁.const_smul a).add (hm₂.const_smul b)
  have hc' : 0 ≤ (‖a‖ + ‖b‖) * cF := mul_nonneg (by positivity) hcF
  have hb : ∀ p, Bs.inSS p → ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤
      (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by
    intro p hp
    have h1 := hb₁ p hp
    have h2 := hb₂ p hp
    calc ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤ ‖a‖ * ‖H₁ (B.sgs p γ)‖ + ‖b‖ * ‖H₂ (B.sgs p γ)‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_smul, norm_smul]
      _ ≤ ‖a‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) + ‖b‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by ring
  have i₁ := hInt H₁ cF hcF hm₁ hb₁
  have i₂ := hInt H₂ cF hcF hm₂ hb₂
  rw [hEq _ _ hc' hm hb, hEq H₁ cF hcF hm₁ hb₁, hEq H₂ cF hcF hm₂ hb₂, hlin]
  have e : (fun p => θ p • (a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p)) =
      fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p) + b • (θ p • D.orbIntegrand Bs γ H₂ p) := by
    funext p
    rw [smul_add, smul_comm (θ p) a, smul_comm (θ p) b]
  have j₁ : Integrable (fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p)) Bs.μSS := i₁.smul a
  have j₂ : Integrable (fun p => b • (θ p • D.orbIntegrand Bs γ H₂ p)) Bs.μSS := i₂.smul b
  rw [e, integral_add j₁ j₂, integral_smul, integral_smul]

theorem vector_valued_orbital_linear : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt) (A : ℝ),
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      ContinuousOn H₁ (B.GPos Bs) → ContinuousOn H₂ (B.GPos Bs) →
      (∀ g ∈ B.GPos Bs, ‖H₁ g‖ ≤ cF * B.gN g ^ (-A)) → (∀ g ∈ B.GPos Bs, ‖H₂ g‖ ≤ cF * B.gN g ^ (-A)) →
      ∀ a b : ℂ, D.vecV Bs ν' m₀ (fun g => a • H₁ g + b • H₂ g) q =
        a • D.vecV Bs ν' m₀ H₁ q + b • D.vecV Bs ν' m₀ H₂ q := by
  obtain ⟨c₃, hc₃⟩ := orbJ_linear_of_decay
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs ν' m₀ q A hA H₁ H₂ cF hcF hc₁ hc₂ hb₁ hb₂ a b
  unfold D.vecV
  by_cases h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos h]
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
      have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
      obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
      have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
      have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
        ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
      exact hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd (hZ.trans hmono) hpos hrel hA H₁ H₂ cF hcF
        (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₁) (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₂)
        (fun p hp => hb₁ _ (horb p hp)) (fun p hp => hb₂ _ (horb p hp)) a b
    · simp only [dif_neg h']
      simp
  · simp only [dif_neg h]
    simp

end

end Formalism.FourierDecayAlt.P.CutBP.PolTop

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFOpOKMulG
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

def NFOpOKMulG : Prop :=
  ∀ C : ℝ, ∃ C' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (N : ℕ) (Th : B.DiffOp P.k P.r Wp Wq), NFOpOK C p N Th →
      ∃ Th' : B.DiffOp P.k P.r Wp Wq, NFOpOK C' p N Th' ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r),
          B.opApply Th' F g = ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • B.opApply Th F g

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def xD (φ : ℝ → ℝ) : ℝ → ℝ := fun x => x * deriv φ x

def IsSCoef {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq) : Prop :=
  ∀ (s : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV P.k P.r) F → ∀ g ∈ C6.domL p.T.base ∅,
    ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (-s) : ℝ) : ℂ) •
        p.Θ.Θ w e (fun g' => ((Gf P.k P.r p.T.base.z p.T.base.z' g' ^ s : ℝ) : ℂ) • F g') g =
      ∑ q : Fin (Q + 1), ((s ^ (q : ℕ) : ℝ) : ℂ) • B.opApply (L q) F g

def NFUnfoldTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), w ≠ [] →
    D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      topD p H w c = (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
          Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c))) *
        ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P, Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 *
          ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c)))‖ ^ 2

def NFVMul : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (φ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt), D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) γ = ((φ (TBB.Gp p γ) : ℝ) : ℂ) • p.V F γ

def NFCutSup : Prop :=
  ∀ χ : ℝ → ℝ, C6.IsCut0 χ → ∀ q : ℕ, ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ∀ x : ℝ, 0 < x →
    |(xD^[q] (fun y => χ (y / ε))) x| ≤ K

def NFLeibV : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → ∀ w, KB.CutWord P p.l0 w → ∀ e : Wd.Ix (Fin w.length),
      ∃ (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq),
        (∀ q, B.SmoothCoef (C6.domL p.T.base ∅) (L q)) ∧ IsSCoef p w e Q L ∧
        ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ),
          B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
            p.V (p.Θ.Θ w e (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g)) γ =
              ∑ q : Fin (Q + 1), (((xD^[(q : ℕ)] φ) (TBB.Gp p γ) : ℝ) : ℂ) • p.V (B.opApply (L q) F) γ

def NFEmptyOps : Prop :=
  ∃ C₁ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (N : ℕ), ∃ Th₀ Th₁ : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th₀ ∧ NFOpOK C₁ p N Th₁ ∧
      ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r),
        B.opApply Th₀ F g = F g ∧ B.opApply Th₁ F g = ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • F g

theorem unfolding_top_term_holds : NFUnfoldTop := by
  intro Wp Wq _ _ _ _ _ _ P p H w c hw hloc _
  have hn : TBB.normC (fun _ => 1) w = 1 := by
    simp [TBB.normC]
  have hRR : p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c) =
      Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w (TBB.bigPt P.r c) (TBB.bigPt P.r c) := by
    rw [KB.Pl.RR, D.RRplace, dite_eq_left ⟨hloc, hloc⟩, dite_eq_right (Nat.not_succ_le_self _), if_pos rfl, if_neg hw]
  show (TBB.NP p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re = _
  rw [TBB.NP, hn, div_one, hRR, Top.topOf, Complex.re_ofReal_mul]
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hsq : ∀ v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp), (inner ℂ v v : ℂ).re = ‖v‖ ^ 2 :=
    fun v => by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [Complex.re_ofReal_mul, B.hsInner, hsq]
  simp only [TBB.TTp, KB.Pl.V]
  ring

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDM
section
namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def TypeNormMeas : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), JF.TransportedAlt P.k P.r A 0 → B.InCC A 0 Y → ∀ ρ : M.Ty P,
      AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        ‖B.hsVec ((p.TP.E ρ).comp (p.V Y (TBB.bigPt P.r c)))‖) volume

def VecVGPos : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (Y Y' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
    (∀ g ∈ B.GV P.k P.r, 0 < Gf P.k P.r p.T.base.z p.T.base.z' g → Y g = Y' g) → ∀ a : C.LPt, p.V Y a = p.V Y' a

def DopCC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base X → KB.CutWord P p.l0 w →
    ∀ e : Wd.Ix (Fin w.length), ∃ Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      (∀ g ∈ B.GV P.k P.r, 0 < Gf P.k P.r p.T.base.z p.T.base.z' g → Y g = p.Θ.Θ w e X g) ∧
        ∀ A : ℝ, B.InCC A 0 Y

def ScalarMeas : Prop :=
  ∀ (k r : ℕ) (TT : ℝ), Measurable (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) ∧
    Measurable (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c))

def EmptyMeas : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base X → AEStronglyMeasurable (topD p X []) volume

theorem ae_all_ne (r : ℕ) : ∀ᵐ c : Fin (r + 1) → ℂ, ∀ i, c i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  have h : volume ((fun c : Fin (r + 1) → ℂ => c i) ⁻¹' {0}) = 0 := by
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null _ (measure_singleton 0)
  have e : {a : Fin (r + 1) → ℂ | ¬a i ≠ 0} = (fun c : Fin (r + 1) → ℂ => c i) ⁻¹' {0} := by
    ext a; simp
  exact ae_iff.2 (by rw [e]; exact h)

theorem topDMeasCpt_of_parts (h1 : TypeNormMeas) (h2 : VecVGPos) (h3 : DopCC) (h4 : ScalarMeas) (h5 : EmptyMeas) :
    TopDMeasCpt := by
  intro Wp Wq _ _ _ _ _ _ P p X w Cb hD hX hw
  by_cases hw0 : w = []
  · subst hw0; exact h5 Wp Wq P p X hX
  choose Y hYe hYc using h3 Wp Wq P p X w Cb hD hX hw
  set TT : ℝ := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
  set A : ℝ := 9 * ((P.r : ℝ) + 1) * (((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + 1) with hA
  have hThr : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    have hr : (0 : ℝ) < 9 * ((P.r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hr, hA]
    nlinarith
  have hV : ∀ e a, p.V (p.Θ.Θ w e X) a = p.V (Y e) a := fun e a =>
    h2 Wp Wq P p _ _ (fun g hg hG => (hYe e g hg hG).symm) a
  obtain ⟨hn, hW⟩ := h4 P.k P.r TT
  set g : (Fin (P.r + 1) → ℂ) → ℝ := fun c =>
    ((((Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) * Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) /
        TBB.normC (fun _ => 1) w : ℝ) : ℂ) *
      ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ))).re with hg
  have hgm : AEStronglyMeasurable g volume := by
    have hdH : ∀ e ρ, Measurable (fun c : Fin (P.r + 1) → ℂ => Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ) := by
      intro e ρ
      unfold Top.dH
      exact ((hW.pow_const _).mul_const _).sqrt
    have hterm : ∀ e ρ, AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume := by
      intro e ρ
      have h1' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          ‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2) volume :=
        (h1 Wp Wq P p (Y e) A hThr (hYc e A) ρ).pow 2
      have h2' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable h1'
      have h3' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ)) volume :=
        (Complex.measurable_ofReal.comp ((hdH e ρ).mul (hdH e ρ))).aestronglyMeasurable
      exact h3'.mul h2'
    have hsum : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume :=
      Finset.aestronglyMeasurable_fun_sum _ fun e _ => Finset.aestronglyMeasurable_fun_sum _ fun ρ _ => hterm e ρ
    have hpre : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        (((Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) * Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) /
          TBB.normC (fun _ => 1) w : ℝ) : ℂ))) volume :=
      (Complex.measurable_ofReal.comp (((hn.sqrt.mul hn.sqrt).div_const _))).aestronglyMeasurable
    exact Complex.continuous_re.comp_aestronglyMeasurable (hpre.mul hsum)
  refine hgm.congr ?_
  filter_upwards [ae_all_ne P.r] with c hc
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc
  show g c = topD p X w c
  unfold topD TBB.Ew TBB.NP KB.Pl.RR D.RRplace
  rw [dite_eq_left ⟨hl, hl⟩, dite_eq_right (by omega), if_pos rfl, if_neg hw0]
  unfold Top.topOf
  simp only [hg]
  congr 3
  funext e
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self]
  show _ = _ * (((‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e X) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)
  rw [hV e]

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
end

