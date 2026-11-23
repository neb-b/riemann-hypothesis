module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0068
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NfRadOrder0OfRadRed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0070
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CkOnZeroOfContOn
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem gv_closed (k r : ℕ) : IsClosed (B.GV k r) := by
  show IsClosed {g : B.Mat k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem ckOn_zero_of_contOn {k r : ℕ} (f : Mx k r → ℂ) (hf : ContinuousOn f (B.GV k r)) :
    B.CkOn ((0 : ℕ) : ℕ∞) (B.GV k r) (fun g => f g • (1 : ℂ →L[ℂ] ℂ)) := by
  have hcl := gv_closed k r
  haveI : NormalSpace (B.Mat k r) :=
    inferInstanceAs (NormalSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨g, hg⟩ := ContinuousMap.exists_extension' hcl.isClosedEmbedding_subtypeVal
    (⟨fun x : B.GV k r => f x, hf.restrict⟩ : C(B.GV k r, ℂ))
  intro g₀ hg₀
  refine ⟨Set.univ, fun y => g y • (1 : ℂ →L[ℂ] ℂ), isOpen_univ, Set.mem_univ _, ?_, fun y _ hy => ?_⟩
  · show ContDiffOn ℝ 0 _ _
    rw [contDiffOn_zero]
    exact (g.continuous.smul continuous_const).continuousOn
  · exact congrArg (fun c : ℂ => c • (1 : ℂ →L[ℂ] ℂ)) (congrFun hg ⟨y, hy⟩).symm

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ZJ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r N : ℕ) (f : Q.Mx k r → E) (g₀ : Q.Mx k r) : Prop :=
  ∃ (U : Set (Q.Mx k r)) (F : Q.Mx k r → E), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧
    (∀ g ∈ U, g ∈ Q.Glev k r (Fin.last r) → f g = F g) ∧ ∀ j ≤ N, iteratedFDeriv ℝ j F g₀ = 0

def GTCLRJetT : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (a b : Fin 2), ∃ N : ℕ, ∀ (f : Q.Mx k r → E) (g₀ : Q.Mx k r), g₀ ∈ Q.Glev k r (Fin.last r) →
      ZJ k r N f g₀ → Q.tL k r z z' (Fin.last r) Y a b f g₀ = 0

def GTCLRJetRad : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
    ∀ N : ℕ, (∀ j ≤ N, iteratedFDeriv ℝ j
        (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)) q.2 = 0) →
      ZJ P.k P.r N ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1) (NF.muZ P.k P.r Bs.μsec q.2)

def GTCLRTaylor : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (ψ : ℂ → V) (U : Set ℂ) (ζ₀ : ℂ) (N : ℕ),
    IsOpen U → ζ₀ ∈ U → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ U →
    ∀ i ≤ N, iteratedFDeriv ℝ i (fun ζ => ψ ζ - ∑ j ∈ Finset.range (N + 1),
        ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) ζ₀ = 0

def GTCLRadTOfCut : Prop := GTCLRJetT → GTCLRJetRad → GTCLRTaylor → GTCLRadT

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocalFrameA
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem gcl_slice_iter {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : (Fin r → ℂ) × ℂ → V) (s : Set ((Fin r → ℂ) × ℂ)) (hs : IsOpen s)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F s) (q : (Fin r → ℂ) × ℂ) (hq : q ∈ s) (j : ℕ) :
    iteratedFDeriv ℝ j (fun ζ => F (q.1, ζ)) q.2 =
      (iteratedFDeriv ℝ j F q).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ (Fin r → ℂ) ℂ) := by
  let a : (Fin r → ℂ) × ℂ := (q.1, 0)
  let L : ℂ →L[ℝ] (Fin r → ℂ) × ℂ := ContinuousLinearMap.inr ℝ (Fin r → ℂ) ℂ
  let G : (Fin r → ℂ) × ℂ → V := fun p => F (a + p)
  let s' : Set ((Fin r → ℂ) × ℂ) := (fun p => a + p) ⁻¹' s
  have hs' : IsOpen s' := hs.preimage (continuous_const.add continuous_id)
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G s' :=
    hF.comp ((contDiff_const.add contDiff_id).contDiffOn) (fun p hp => hp)
  have hslice : (fun ζ : ℂ => F (q.1, ζ)) = G ∘ L := by
    funext ζ
    simp [G, a, L]
  have hq' : L q.2 ∈ s' := by
    show a + L q.2 ∈ s
    simpa [a, L] using hq
  have hpre : IsOpen (L ⁻¹' s') := hs'.preimage L.continuous
  have hmem : q.2 ∈ L ⁻¹' s' := hq'
  rw [hslice, ← iteratedFDerivWithin_of_isOpen j hpre hmem,
    L.iteratedFDerivWithin_comp_right hG hs'.uniqueDiffOn hpre.uniqueDiffOn hq'
      (by exact_mod_cast (le_top : ((j : ℕ∞)) ≤ ⊤)),
    iteratedFDerivWithin_of_isOpen j hs' hq']
  have hGq : iteratedFDeriv ℝ j G (L q.2) = iteratedFDeriv ℝ j F q := by
    show iteratedFDeriv ℝ j (fun p => F (a + p)) (L q.2) = _
    rw [iteratedFDeriv_comp_add_left']
    show iteratedFDeriv ℝ j F (a + L q.2) = _
    congr 1
    ext <;> simp [a, L]
  rw [hGq]

theorem gcl_isRadDiff {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hRB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π')
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hT : RadDZ P Bs T) :
    NF.IsRadDiff P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' T := by
  obtain ⟨n, A, hA, hT'⟩ := hT
  have hmem : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))) (NF.QR P.k P.r Bs.z Bs.z') :=
    fun Φ => (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB Φ Φ.2).1
  have hopen : IsOpen (NF.QR P.k P.r Bs.z Bs.z') := by
    have h1 : IsOpen (Formalism.QuantumDeterminants.OmX P.r) := by
      have h2 : Formalism.QuantumDeterminants.OmX P.r = ⋂ l, {x : Fin P.r → ℂ | x l ≠ 0} := by
        ext x
        simp [Formalism.QuantumDeterminants.OmX]
      rw [h2]
      exact isOpen_iInter_of_finite (fun l => isOpen_ne_fun (continuous_apply l) continuous_const)
    exact (h1.preimage continuous_fst).inter
      (isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd))
  refine ⟨n, fun j q => (A j q.2).comp (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin j => ContinuousLinearMap.inr ℝ (Fin P.r → ℂ) ℂ)), ?_, ?_⟩
  · intro j
    have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (Fin P.r → ℂ) × ℂ => A j q.2)
        (NF.QR P.k P.r Bs.z Bs.z') :=
      (hA j).comp contDiff_snd.contDiffOn (fun q hq => hq.2)
    exact hA'.clm_comp contDiffOn_const
  · intro Φ q hq
    rw [hT' Φ q hq]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [gcl_slice_iter _ _ hopen (hmem Φ) q hq j]
    simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.compContinuousLinearMapL_apply]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def dTy (P : M.Par) (ρ : M.Ty P) : M.Ty P → ℂ := fun σ => if σ = ρ then 1 else 0

def GTCCurvId : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ ρ : M.Ty P,
      (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * d.κ (dTy P ρ) =
        algebraMap ℂ (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) *
          (d.L.GGi * d.L.GGi) * d.κ (dTy P ρ)

def GTCCurvTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → (∀ ρ, ∀ ζ ∈ Ann P, B ρ ζ = star (A ρ ζ)) →
        (∀ ρ : M.Ty P, (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * d.κ (dTy P ρ) =
          algebraMap ℂ (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) *
            (d.L.GGi * d.L.GGi) * d.κ (dTy P ρ)) →
        ∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A ρ w) ζ).re = 0

def GTCRefTrace : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e0 ∧ KapF P Bs d e0 ∧
      ∃ A0 B0 : M.Ty P → ℂ → ℂ, SmAB P A0 B0 ∧ ConnF P Bs d e0 A0 B0 ∧
        ∀ ρ, ∃ n : ℤ, ∀ ζ ∈ Ann P, (ζ * (modA P ρ ζ - A0 ρ ζ)).re = (n : ℝ) / 2

def GTCRefAn : Prop :=
  ∀ (TT : ℝ) (α : ℂ → ℂ) (c : ℝ), 0 ≤ TT →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → (ζ * α ζ).re = c) →
    ∀ R : ℝ, 0 < R → TT < R ^ 2 → (circleIntegral α 0 R).im = 2 * Real.pi * c

def GTCRefOfCut : Prop := GTCReal → GTCCurvId → GTCCurvTr → GTCRefTrace → GTCRefAn → GTCRef

private theorem contDiffOn_modA_ann (P : M.Par) (ρ : M.Ty P) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => star ζ) := by
    first
    | exact contDiff_id.star
    | exact Complex.conjCLE.contDiff
    | simpa using (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have h : modA P ρ = fun ζ : ℂ => (M.aC P ρ : ℂ) * star ζ * (ζ * star ζ - (P.TT : ℂ))⁻¹ := by
    funext ζ
    simp only [modA, div_eq_mul_inv]
    rw [← Complex.mul_conj]
    rfl
  rw [h]
  apply ContDiffOn.mul
  · exact (contDiff_const.mul hs).contDiffOn
  · apply ContDiffOn.inv
    · exact ((contDiff_id.mul hs).sub contDiff_const).contDiffOn
    · intro ζ hζ
      have hz : ζ * star ζ = ((Complex.normSq ζ : ℝ) : ℂ) := Complex.mul_conj ζ
      rw [hz, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hζ).ne'

theorem gTCRef_of_cut : GTCRefOfCut := by
  intro hReal hCurvId hCurvTr hTrace hAn Wp Wq _ _ _ _ _ _ P Bs X d hH
  obtain ⟨e0, he0, hk0, A0, B0, hAB, hC, hn⟩ := hTrace Wp Wq P Bs X d hH
  have hB : ∀ ρ, ∀ ζ ∈ Ann P, B0 ρ ζ = star (A0 ρ ζ) := hReal Wp Wq P Bs X d hH e0 he0 hk0 A0 B0 hAB hC
  refine ⟨e0, he0, hk0, A0, B0, hAB, hC,
    hCurvTr Wp Wq P Bs X d hH e0 he0 hk0 A0 B0 hAB hC hB (hCurvId Wp Wq P Bs X d hH), ?_⟩
  intro ρ R hR hR2
  obtain ⟨n, hn'⟩ := hn ρ
  refine ⟨n, ?_⟩
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := contDiffOn_modA_ann P ρ
  have key := hAn (max P.TT 0) (fun w => modA P ρ w - A0 ρ w) ((n : ℝ) / 2) (le_max_right _ _)
    ((hsm.sub (hAB ρ).1).mono (fun ζ hζ => show P.TT < Complex.normSq ζ from
      lt_of_le_of_lt (le_max_left _ _) (show max P.TT 0 < Complex.normSq ζ from hζ)))
    (fun ζ hζ => hn' ζ (show P.TT < Complex.normSq ζ from lt_of_le_of_lt (le_max_left _ _) hζ)) R hR (max_lt hR2 (pow_pos hR 2))
  rw [key]; ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGauge
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem mulQ_zbP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P (MA.DQ P).zbP f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = star q.1.2 * (f : MA.Qp P.r P.TT → ℂ) q := mul_conjCoordinate_apply P f q

theorem mulQ_zP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P (MA.DQ P).zP f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = q.1.2 * (f : MA.Qp P.r P.TT → ℂ) q := algebraMap_comp_ofPadicInt_apply P f q

theorem mulQ_ggiP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P ((MA.DQ P).ggiP P.TT) f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * (f : MA.Qp P.r P.TT → ℂ) q := ggiP_apply P f q

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nabF_phase (P : M.Par) (hTT : 0 ≤ P.TT) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A B u : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hC : ConnF P Bs d e A B) (hu : PhaseEq P A B u) :
    NabF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) := by
  have hu' : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 :=
    fun ρ => ⟨(hu ρ).1, fun ζ hζ => ((hu ρ).2 ζ hζ).1⟩
  intro Φ
  constructor
  · funext ρ
    rw [actA_nabA, trR_phase P Bs e u hu', trR_phase P Bs e u hu', (hC Φ ρ).1]
    apply Subtype.ext
    funext q
    have hv := conj_smooth (hu ρ).1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    obtain ⟨_, hA, _⟩ := (hu ρ).2 q.1.2 hζ
    have hdc := (dZ_conj_unit P (hu ρ).1 (fun ζ hζ => ((hu ρ).2 ζ hζ).1) hζ).1
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul, Pi.add_apply, Pi.mul_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [mulQ_zbP, mulQ_ggiP, dzQ_apply P hTT, dzQ_apply P hTT, wirtQ_mul, wirtinger_derivative_fibre_function P hv, fnZ_val P hv,
      fnZ_val P (hAB ρ).1, hdc]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P hv]
    unfold modA at hA
    linear_combination (star (u ρ q.1.2) * ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) * hA
  · funext ρ
    rw [actA_nabsA, trR_phase P Bs e u hu', trR_phase P Bs e u hu', (hC Φ ρ).2]
    apply Subtype.ext
    funext q
    have hv := conj_smooth (hu ρ).1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    obtain ⟨_, _, hB⟩ := (hu ρ).2 q.1.2 hζ
    have hdc := (dZ_conj_unit P (hu ρ).1 (fun ζ hζ => ((hu ρ).2 ζ hζ).1) hζ).2
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul, Subalgebra.coe_neg, Pi.add_apply,
      Pi.mul_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    rw [mulQ_zP, mulQ_ggiP, dzbQ_apply P hTT, dzbQ_apply P hTT, wirtQ_mul, wirt_fnZ_zb P hv, fnZ_val P hv,
      fnZ_val P (hAB ρ).2, hdc]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P hv]
    unfold modB at hB
    linear_combination (star (u ρ q.1.2) * ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) * hB

end main

theorem gauge_transform_holds : GTCGauge := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk A B' u hAB hC hu
  have hTT : 0 ≤ P.TT := torus_parameter Wp Wq P Bs X d hH
  have hu' : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 :=
    fun ρ => ⟨(hu ρ).1, fun ζ hζ => ((hu ρ).2 ζ hζ).1⟩
  exact ⟨isFrameB_phase P Bs e u he hu', kapF_phase P Bs d e u hu' hk,
    nabF_phase P hTT Bs d e A B' u hAB hC hu⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLocalCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def SliceLoc (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Prop :=
  ∀ (Φ Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c c' : Fin P.r → ℂ), c ∈ OmX P.r → c' ∈ OmX P.r →
    (∀ ζ ∈ Ann P, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      (Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ)) →
    ∀ ζ ∈ Ann P, (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ)

end preds

def GTSSLSliceDZ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∀ T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), RadDZ P Bs T → SliceLoc P Bs T

def GTSSLSliceSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → (∀ (Y : ℂ) (a b : Fin 2), SliceLoc P Bs (X.t Y a b)) →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), SliceLoc P Bs (d.SS l).1 ∧ SliceLoc P Bs (star (d.SS l)).1

def GTSSLMat : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    (∀ l ∈ Finset.Icc 1 (P.k - 1), SliceLoc P Bs (d.SS l).1 ∧ SliceLoc P Bs (star (d.SS l)).1) →
      ∃ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t ∧ SSLoc P Bs d e s t

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ebM (k r : ℕ) (v b : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  Matrix.of fun p q => v p * herm (Hpk k r) (bvec q) b

section tht

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sandw (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp A).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B')

def tht (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (Bw Bw' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ p, ∑ q, herm (Hpk k r) (ι *ᵥ Bw' q) (Bw p) •
    sandw (QrD.ecOp π (ebM k r (Bw p) (SSn.prWv k r z a))) (QrD.ecOp π' (ebM k r (SSn.prWv k r z' a') (Bw' q)))

def thtA (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (Bw Bw' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ p, ∑ q, conj (herm (Hpk k r) (ι *ᵥ Bw' q) (Bw p)) •
    sandw (QrD.ecOp π (ebM k r (SSn.prWv k r z a) (Bw p))) (QrD.ecOp π' (ebM k r (Bw' q) (SSn.prWv k r z' a')))

end tht

def ThtFacts : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * P.r + P.k + 1) → ℂ) × (Fin (2 * P.r + P.k + 1) → ℂ) ×
          B.Mat P.k P.r => tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' x.1 x.2.1 x.2.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * P.r + P.k + 1) → ℂ) × (Fin (2 * P.r + P.k + 1) → ℂ) ×
          B.Mat P.k P.r => thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' x.1 x.2.1 x.2.2) ∧
      (∀ a a' ι A B', B.hsInner (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι A) B' =
        B.hsInner A (thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι B')) ∧
      (∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z', ∀ a a' ι X,
        tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹)
            ((Bs.π h).comp (X.comp (Bs.π' h'⁻¹))) =
          (Bs.π h).comp ((tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι X).comp (Bs.π' h'⁻¹)) ∧
        thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹)
            ((Bs.π h).comp (X.comp (Bs.π' h'⁻¹))) =
          (Bs.π h).comp ((thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι X).comp (Bs.π' h'⁻¹))) ∧
      ∀ (c : ℂ) a a' ι, tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (c • a) (conj c • a') ι =
        (conj c) ^ 2 • tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι

def DatumUnit : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ), BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ (v : Fin S.f) (ζ : ℂ), (D.parOf S v).TT < Complex.normSq ζ →
      SSn.prWv S.G.k S.G.r (T v).base.z (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) =
          SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ ∧
        herm (Hpk S.G.k S.G.r) (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) = 1 ∧
        SSn.prWv S.G.k S.G.r (T v).base.z' (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) =
          SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ ∧
        herm (Hpk S.G.k S.G.r) (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) = 1

def ThtGaugeConst : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    PRho.Hyp Cc S T f χ ν' m₀ top A₀ v e → 2 ≤ S.G.k → ∀ l ∈ Finset.Icc 1 (S.G.k - 1),
    ∀ Bw Bw' : Fin S.G.k → Fin (2 * S.G.r + S.G.k + 1) → ℂ,
      Q.IsFrameOf S.G.k S.G.r [(T v).base.z] Bw → Q.IsFrameOf S.G.k S.G.r [(T v).base.z'] Bw' →
      ∃ κ : M.Ty (D.parOf S v) → ℂ, ∀ ζ : ℂ, (D.parOf S v).TT < Complex.normSq ζ → ∀ π ρ : M.Ty (D.parOf S v),
        M.Up (D.parOf S v) l π ρ →
        κ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw'
          (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) (e π ζ))) =
          ((Real.sqrt (M.Nrm (D.parOf S v) l π) : ℝ) : ℂ)

def SSnRepOfCut : Prop :=
  PRho.PRhoExists → PRho.GaugeLines → ThtFacts → DatumUnit → ThtGaugeConst → SSnRep

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

