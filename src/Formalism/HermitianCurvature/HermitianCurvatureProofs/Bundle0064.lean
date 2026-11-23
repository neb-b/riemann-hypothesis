module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZinvBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0055
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AlgebraicQuantumDeterminant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0057
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0003
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0026
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.HermitianOrthogonalProjectionVector

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def FundG : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A A' : B.Mat k r → (Wq →L[ℂ] Wp)), ContinuousOn A (B.GV k r) → ContinuousOn A' (B.GV k r) →
    (∀ φ : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) φ → HasCompactSupport φ → B.SuppIn (B.GPos D) φ →
      ∫ x : Mt k r, B.hsInner (A (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG =
        ∫ x : Mt k r, B.hsInner (A' (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG) →
    ∀ g ∈ B.GPos D, A g = A' g

def AdjCont : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ →
    ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → B.SuppIn (B.GPos D) f →
      ∀ p, D.inSS p → ContinuousOn (B.opAdj Θ (B.rho D p f)) (B.GV k r) ∧
        ContinuousOn (B.rho D p (B.opAdj Θ f)) (B.GV k r)

def AdjInt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → B.SuppIn (B.GPos D) f →
      ∀ p, D.inSS p → ∀ φ : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) φ → HasCompactSupport φ →
        B.SuppIn (B.GPos D) φ →
        ∫ x : Mt k r, B.hsInner (B.opAdj Θ (B.rho D p f) (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG =
          ∫ x : Mt k r, B.hsInner (B.rho D p (B.opAdj Θ f) (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG

theorem adjComm_of_parts (hF : FundG) (hC : AdjCont) (hI : AdjInt) : AdjComm := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hs hc f hf hfc hfs p hp g hg
  obtain ⟨c1, c2⟩ := hC k r Wp Wq D Θ hs f hf hfc hfs p hp
  exact hF k r Wp Wq D _ _ c1 c2 (fun φ h1 h2 h3 => hI k r Wp Wq D Θ hs hc f hf hfc hfs p hp φ h1 h2 h3) g hg

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jAFFStable_of_parts (hG : GermOps) (hE : ExtLoc) (hS : SmoothOps) (hA : AdjComm) (hQ : EquivOps)
    (hO : OmPDom) : JAFFStable := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ _ v Θ hΘ J hJ
  obtain ⟨hDom, hPos⟩ := hO E Wp Wq S T v
  have hG' := hG S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Θ
  have hsupp : ∀ f' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), tsupport f' ⊆ OmP S T v →
      B.SuppIn (B.GPos (T v).base) f' := by
    intro f' hs x hx
    have hxG : x ∈ B.GV S.G.k S.G.r :=
      (Formalism.FourierDecayAlt.P.B5.GV_closed (k := S.G.k) (r := S.G.r)).closure_subset_iff.2 (by exact fun y hy => hy.1) hx
    have hxT : x ∈ tsupport f' := closure_mono (by exact fun y hy => hy.2) hx
    exact hPos x (hs hxT) hxG
  constructor
  · refine hQ hE _ _ _ _ (T v).base (OmP S T v) (B.opApply Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).1) (fun c f₁ g _ => (hG'.2 c f₁ g).1)
      (fun f₁ hf hs => (hS _ _ _ _ (T v).base Θ _ hDom.1 hPos hΘ.1 f₁ hf hs).1) ?_ J hJ
    intro f₁ hf _ _ p hp g hg hgG
    exact hΘ.2 p hp f₁ (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hf) g (hPos g hg hgG)
  · refine hQ hE _ _ _ _ (T v).base (OmP S T v) (B.opAdj Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).2) (fun c f₁ g _ => (hG'.2 c f₁ g).2)
      (fun f₁ hf hs => (hS _ _ _ _ (T v).base Θ _ hDom.1 hPos hΘ.1 f₁ hf hs).2) ?_ J hJ
    intro f₁ hf hc hs p hp g hg hgG
    exact hA _ _ _ _ (T v).base Θ hΘ.1 hΘ.2 f₁ hf hc (hsupp f₁ hs) p hp g (hPos g hg hgG)

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableGerm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section germ

variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem deriv_const_smul_any (c : ℂ) (h : ℝ → E') (t : ℝ) :
    deriv (fun s => c • h s) t = c • deriv h t := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hd : DifferentiableAt ℝ h t
  · exact deriv_const_smul c hd
  · have hd' : ¬ DifferentiableAt ℝ (fun s => c • h s) t := by
      intro h'
      apply hd
      have e : h = fun s => c⁻¹ • (c • h s) := by
        funext s
        simp [smul_smul, inv_mul_cancel₀ hc]
      rw [e]
      exact h'.const_smul c⁻¹
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', smul_zero]

theorem rdV_smul (X : B.Mat k r) (c : ℂ) (f : B.Mat k r → E') :
    RdV X (c • f) = c • RdV X f := by
  funext g
  exact deriv_const_smul_any c (fun t => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

theorem rw_smul (w : List (B.Mat k r)) (c : ℂ) (f : B.Mat k r → E') :
    B.Rw w (c • f) = c • B.Rw w f := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show RdV X (B.Rw w (c • f)) = c • RdV X (B.Rw w f)
    rw [ih, rdV_smul]

theorem rdV_local {X : B.Mat k r} (hX : B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E'} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) {g : B.Mat k r} (hg : g ∈ U)
    (hgG : g ∈ B.GV k r) : RdV X f g = RdV X f' g := by
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f' (g * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  have hev : ∀ᶠ t : ℝ in nhds (0 : ℝ), g * NormedSpace.exp (((t : ℝ) : ℂ) • X) ∈ U := by
    apply hc.continuousAt.preimage_mem_nhds
    show U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))
    rw [Formalism.FourierDecayAlt.P.B5.curve_zero]
    exact hU.mem_nhds hg
  filter_upwards [hev] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)

theorem rw_local (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E'} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) :
    ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f x = B.Rw w f' x := by
  induction w with
  | nil => exact he
  | cons X w ih =>
    intro x hx hxG
    exact rdV_local (hw X (by simp)) hU (ih (fun Y hY => hw Y (by simp [hY]))) hx hxG

theorem sum_map_smul' {ι M : Type*} [AddCommMonoid M] [Module ℂ M] (c : ℂ) (l : List ι) (φ : ι → M) :
    (l.map fun i => c • φ i).sum = c • (l.map φ).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, smul_add]

end germ

theorem germ_operators_holds : GermOps := by
  intro k r Wp Wq _ _ _ _ _ Θ
  refine ⟨fun U f f' hU he g hg hgG => ⟨?_, ?_⟩, fun c f g => ⟨?_, ?_⟩⟩
  · unfold B.opApply
    congr 1
    apply List.map_congr_left
    intro T _
    rw [rw_local T.word T.word_lie hU he g hg hgG]
  · unfold B.opAdj
    congr 1
    apply List.map_congr_left
    intro T _
    rw [rw_local T.word.reverse (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) hU
      (f := fun x => T.coefAdj x (f x)) (f' := fun x => T.coefAdj x (f' x))
      (fun x hx hxG => by simp only [he x hx hxG]) g hg hgG]
  · unfold B.opApply
    rw [← sum_map_smul']
    congr 1
    apply List.map_congr_left
    intro T _
    rw [rw_smul, Pi.smul_apply, map_smul]
  · unfold B.opAdj
    rw [← sum_map_smul']
    congr 1
    apply List.map_congr_left
    intro T _
    have e : (fun x => T.coefAdj x ((c • f) x)) = c • (fun x => T.coefAdj x (f x)) := by
      funext x; simp
    rw [e, rw_smul, Pi.smul_apply, smul_comm]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatPolyOK
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

open scoped ContDiff

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jdh_ckOn_of_contDiff {k r : ℕ} {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {f : B.Mat k r → E'}
    (hf : ContDiff ℝ ∞ f) (UU : Set (B.Mat k r)) : B.CkOn ⊤ UU f :=
  fun _ _ => ⟨Set.univ, f, isOpen_univ, trivial, hf.contDiffOn, fun _ _ _ => rfl⟩

theorem jdh_opOrder_le {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o : ℕ) (Θ : B.DiffOp k r Wp Wq)
    (h : ∀ Tm ∈ Θ, Tm.word.length ≤ o) : B.opOrder Θ ≤ o := by
  unfold B.opOrder
  induction Θ with
  | nil => simp
  | cons T Θ ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h T (List.mem_cons_self ..)) (ih fun Tm hTm => h Tm (List.mem_cons_of_mem _ hTm))

theorem jdh_pd_star {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg κ P) :
    U.IsPolyDeg κ (fun g => star (P g)) := by
  obtain ⟨q, hq, he⟩ := h
  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, fun g => ?_⟩
  · refine (MvPolynomial.totalDegree_rename_le _ _).trans (le_trans ?_ hq)
    exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  · show star (P g) = _
    rw [he g, MvPolynomial.eval_rename, MvPolynomial.eval_map]
    show (starRingEnd ℂ) (MvPolynomial.eval₂ (RingHom.id ℂ) _ q) = _
    rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
    congr 1
    funext x
    rcases x with x | x <;> simp

theorem polynomial_decay_admissible : JDPolyOK := by
  intro k r Wp Wq _ _ _ _ _ o κ Θ hΘ
  let Lm : ℂ →L[ℂ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
  have hLm : ∀ c : ℂ, Lm c = c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := fun c => by
    simp [Lm]

  have key : ∀ Tm ∈ Θ, ∃ P : B.Mat k r → ℂ, U.IsPolyDeg κ P ∧ ContDiff ℝ ∞ P ∧
      Tm.coef = (fun g => Lm (P g)) ∧ Tm.coefAdj = (fun g => Lm (star (P g))) := by
    intro Tm hTm
    obtain ⟨-, P, hP, hc, ha⟩ := hΘ Tm hTm
    exact ⟨P, hP, (poly_adm (n := 0) hP).1, funext fun g => by rw [hc g, hLm],
      funext fun g => by rw [ha g, hLm]⟩
  have smooth : ∀ Tm ∈ Θ, ContDiff ℝ ∞ Tm.coef ∧ ContDiff ℝ ∞ Tm.coefAdj := by
    intro Tm hTm
    obtain ⟨P, -, hc, e1, e2⟩ := key Tm hTm
    refine ⟨?_, ?_⟩
    · rw [e1]; exact (Lm.restrictScalars ℝ).contDiff.comp hc
    · rw [e2]
      have hs : ContDiff ℝ ∞ (fun g => star (P g)) := by
        have := (Complex.conjCLE.contDiff (n := ∞)).comp hc
        simpa [Function.comp_def, Complex.conjCLE_apply] using this
      exact (Lm.restrictScalars ℝ).contDiff.comp hs
  refine ⟨fun UU Tm hTm => ⟨jdh_ckOn_of_contDiff (smooth Tm hTm).1 UU, jdh_ckOn_of_contDiff (smooth Tm hTm).2 UU⟩,
    fun d hd Tm hTm => ⟨jdh_ckOn_of_contDiff (smooth Tm hTm).1 _, jdh_ckOn_of_contDiff (smooth Tm hTm).2 _,
      fun m => ?_⟩, jdh_opOrder_le o Θ fun Tm hTm => (hΘ Tm hTm).1⟩
  obtain ⟨P, hP, -, e1, e2⟩ := key Tm hTm
  obtain ⟨⟨C, hC0, hUB⟩, -⟩ :=
    ubl_clm (Lm.restrictScalars ℝ) (subset_refl (GV k r)) (ubl_poly hP (GV k r) (subset_refl _) m 0)
  obtain ⟨⟨C', hC0', hUB'⟩, -⟩ :=
    ubl_clm (Lm.restrictScalars ℝ) (subset_refl (GV k r)) (ubl_poly (jdh_pd_star hP) (GV k r) (subset_refl _) m 0)
  refine ⟨max C C', fun u w hu hw hl g hg => ?_⟩
  have hg1 : 1 ≤ gN g := gN_ge_one hg
  have hpow : gN g ^ κ ≤ gN g ^ d := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hg1 hd
  have hd0 : 0 ≤ gN g ^ d := Real.rpow_nonneg (by linarith) _
  constructor
  · rw [e1, dLR_eq]
    have hb := hUB (wL u ++ wR w) ⟨u, w, hu, hw, hl, rfl⟩ g hg
    simp only [zero_mul, add_zero] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hpow hC0).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd0))
  · rw [e2, dLR_eq]
    have hb := hUB' (wL u ++ wR w) ⟨u, w, hu, hw, hl, rfl⟩ g hg
    simp only [zero_mul, add_zero] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hpow hC0').trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hd0))

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DeterminantGeneric
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem algebraic_quantum_determinant : Qr.AlgDet :=
  qr_algDet_of (qr_algDetBasis_of quantum_jacobi_identity quantum_determinant_vector quantum_minor_covariance)

theorem capelli_hat_frame : Qr.ChatFrame := qr_chatFrame_of frame_minor

theorem determinant_hat : DetHat :=
  qr_detHat_of algebraic_quantum_determinant capelli_hat_frame capelli_right_good left_right_swap

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DminStarPd
section
open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma gf_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    U.IsPolyDeg (2 * r + 2) (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) := by
  exact gram_function_polynomial k r z z'

section fac

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma ubl_monoM (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) (a b : Fin (r + 2) → ℕ) (c : ℕ)
    (hab : ∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l))
    (hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ)) (n : ℕ) :
    UBL (C6.monoM D a b c) S n 0 (2 * r + 2) := by
  have hfac : ∀ l ∈ (Finset.univ : Finset (Fin (r + 2))),
      UBL (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l)
        S n 0 (2 * r + 2) := by
    intro l _
    by_cases hl : l ∈ L ∨ l = Fin.last (r + 1)
    · have hl' : l.val ≤ 2 * r + 2 := by have := l.isLt; omega
      have h1 : UBL (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l) S n 0 (2 * r + 2) :=
        ubl_mono hSG (ubl_invpow (minor_polynomial_property k r D.z D.z' l) hSG hc₀
          (fun g hg => hSD g hg l hl) (a l) n) le_rfl hl'
      have h2 : UBL (fun g => (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) S n 0 (2 * r + 2) :=
        ubl_mono hSG (ubl_invpow (dmin_star_pd k r D.z D.z' l) hSG hc₀
          (fun g hg => by rw [Complex.star_def, Complex.normSq_conj]; exact hSD g hg l hl) (b l) n)
          le_rfl hl'
      exact ubl_mul hSG h1 h2
    · push_neg at hl
      obtain ⟨ha, hb⟩ := hab l hl.1 hl.2
      have e : (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) =
          fun _ => (1 : ℂ) := by
        funext g
        simp [ha, hb]
      rw [e]
      exact ubl_const 1 hSG n _
  have hP := ubl_prod hSG Finset.univ
    (fun l g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) hfac
  have hG := ubl_invpow (gram_function_polynomial k r D.z D.z') hSG hc₀ hSGf c n
  exact ubl_mul hSG hP hG

private lemma rw_congr_on_open_of_eq_on_GV {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {V : Set (Mat k r)}
    (hV : IsOpen V) {f f' : Mat k r → F} (he : ∀ g ∈ GV k r, g ∈ V → f g = f' g) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ g ∈ GV k r, g ∈ V → Rw w f g = Rw w f' g := by
  intro w
  induction w with
  | nil => intro _ g hg hgV; exact he g hg hgV
  | cons X w ih =>
    intro hw g hg hgV
    have ih' := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    show Dx (false, X) (Rw w f) g = Dx (false, X) (Rw w f') g
    rw [Dx_eq, Dx_eq]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [crv_ev (x := (false, X)) hV hgV] with t ht
    exact ih' _ (crv_mem (x := (false, X)) (hw X (by simp)) hg t) ht

private lemma dw_const_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (c : ℂ) (f : Mat k r → F) :
    ∀ w : List (Bool × Mat k r), Dw w (fun g => c • f g) = fun g => c • Dw w f g := by
  intro w
  induction w with
  | nil => rfl
  | cons x w ih =>
    funext g
    show Dx x (Dw w (fun g => c • f g)) g = c • Dx x (Dw w f) g
    rw [ih, Dx_eq, Dx_eq]
    first
    | exact deriv_const_smul_field c (f := fun t => Dw w f (crv x g t))
    | exact deriv_const_smul' (f := fun t => Dw w f (crv x g t)) c
    | simp [deriv_const_smul']

lemma ubl_fib (D : RealPlaceData k r Wp Wq) (E : Mat k r → C6.EndH Wp Wq) (hE : C6.FibBound D E) {ε : ℝ} (hε : 0 < ε)
    {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (v : List (Mat k r))
    (hv : ∀ X ∈ v, inLie k r X) (n : ℕ) :
    UBL (Rw v E) S n (3 * (r + 1) * v.length) (3 * (r + 1)) := by
  obtain ⟨hE1, hE2⟩ := hE
  have hSsub : S ⊆ GPos D := fun g hg => ⟨(hS g hg).1, lt_of_lt_of_le hε (hS g hg).2⟩
  choose Cf hCf using fun i => hE2 ε hε i
  refine ⟨⟨|(v.map nz).prod| * ∑ j ∈ Finset.range (n + v.length + 1), |Cf j|, by positivity, ?_⟩, ?_⟩
  · intro w hw g hg
    obtain ⟨u, v', hu, hv', hlen, rfl⟩ := hw
    have hgGV := (hS g hg).1
    have hgε := (hS g hg).2
    have hX : 0 ≤ gN g := by
      first
      | positivity
      | (unfold gN; positivity)
      | (simp only [gN]; positivity)
    rw [Rw_scale v E, dw_const_smul, norm_smul]
    have hsplit : Dw (wL u ++ wR v') (Rw (v.map nrm) E) g = dLR u (v' ++ v.map nrm) E g := by
      rw [dLR_eq, Dw_append, Dw_append, Dw_wR, Dw_wR]
      rw [show Rw (v' ++ v.map nrm) E = Rw v' (Rw (v.map nrm) E) by simp only [Rw, List.foldr_append]]
    rw [hsplit]
    have hU : C6.UnitWords k r u (v' ++ v.map nrm) (u.length + (v' ++ v.map nrm).length) := by
      refine ⟨hu, fun X hX => ?_, rfl⟩
      rcases List.mem_append.1 hX with h | h
      · exact hv' X h
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 h
        exact nrm_unit (hv Y hY)
    have hb := hCf (u.length + (v' ++ v.map nrm).length) u (v' ++ v.map nrm) hU g hgGV hgε
    have hlenw : (wL u ++ wR v').length = u.length + v'.length := by simp [wL, wR]
    have hexp : 3 * (r + 1) * (u.length + (v' ++ v.map nrm).length) =
        3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length := by
      rw [hlenw, List.length_append, List.length_map]; ring
    rw [hexp] at hb
    have hX' : 0 ≤ gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length) :=
      pow_nonneg hX _
    have hi : u.length + (v' ++ v.map nrm).length < n + v.length + 1 := by
      rw [List.length_append, List.length_map]; omega
    have hCi : Cf (u.length + (v' ++ v.map nrm).length) ≤
        ∑ j ∈ Finset.range (n + v.length + 1), |Cf j| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cf j|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.2 hi))
    have hnorm : ‖(((v.map nz).prod : ℝ) : ℂ)‖ = |(v.map nz).prod| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    calc |(v.map nz).prod| * ‖dLR u (v' ++ v.map nrm) E g‖
        ≤ |(v.map nz).prod| * (Cf (u.length + (v' ++ v.map nrm).length) *
            gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |(v.map nz).prod| * ((∑ j ∈ Finset.range (n + v.length + 1), |Cf j|) *
            gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCi hX') (abs_nonneg _)
      _ = _ := by ring
  · intro g₀ hg₀
    obtain ⟨f', hf', V, hV, hgV, he⟩ := lss_of_ckOn hE1 hSsub g₀ hg₀
    refine ⟨Rw v f', ?_, V, hV, hgV, fun g' hg' hg'V => rw_congr_on_open_of_eq_on_GV hV he v hv g' hg' hg'V⟩
    rw [← Dw_wR]
    exact cdw _ hf'

end fac

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorsCommuteTranslations
section
namespace Formalism.FourierDecayAlt.P

theorem operators_commute_translations' : Formalism.FourierDecayAlt.C3.OperatorsCommuteTranslations := operators_commute_translations

end Formalism.FourierDecayAlt.P
end

