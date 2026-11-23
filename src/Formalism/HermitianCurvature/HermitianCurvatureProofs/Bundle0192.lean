module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0132
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0146
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0144
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0181
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0187
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0129

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACProper
section
open Matrix MeasureTheory Topology
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem averaging_properness_holds : ACProper := by
  intro k r Wp Wq _ _ _ _ D C C' hC hC' hC'O
  have hW : IsCompact (UWset k r D.z) := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z D.z_mem D.T_pos
  have hW' : IsCompact (UWset k r D.z') := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z' D.z'_mem D.T'_pos
  have hgc : Continuous (B.gN : B.Mat k r → ℝ) := Formalism.FourierDecayAlt.P.B6.gN_continuous
  obtain ⟨MW, hMW⟩ := hW.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨MW', hMW'⟩ := hW'.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨MC, hMC⟩ := hC.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨Co, hCo0, hCo⟩ := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.orbit D.z D.z' C' hC' hC'O
  have gN_nn : ∀ M : B.Mat k r, 0 ≤ B.gN M := fun M => Real.sqrt_nonneg _
  have bnd : ∀ {s : Set (B.Mat k r)} {M : ℝ}, (∀ x ∈ s, ‖B.gN x‖ ≤ M) → ∀ x ∈ s, B.gN x ≤ M :=
    fun h x hx => (le_abs_self _).trans (h x hx)
  set Bd : ℝ := max MW 0 * max MC 0 * max MW' 0 with hBd
  set R : ℝ := max (max MW MW') (Co * Bd ^ (2 * r + 1)) with hR
  refine ⟨Metric.closedBall 0 (max R 0), isCompact_closedBall _ _, ?_⟩
  intro p hp g hg hsg
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  set h : B.Mat k r := Matrix.of p.1.1
  set n : B.Mat k r := Matrix.of p.1.2
  set h' : B.Mat k r := Matrix.of p.2.1
  set n' : B.Mat k r := Matrix.of p.2.2
  have hdet : IsUnit h.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have hdet' : IsUnit h'.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh'.1
  have hx : n⁻¹ * g * n' = h * B.sgs p g * h'⁻¹ := by
    have e1 : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have e2 : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet'
    calc n⁻¹ * g * n' = (h * h⁻¹) * (n⁻¹ * g * n') * (h' * h'⁻¹) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = h * (h⁻¹ * n⁻¹ * g * n' * h') * h'⁻¹ := by simp only [Matrix.mul_assoc]
  have hb : B.gN (n⁻¹ * g * n') ≤ Bd := by
    rw [hx]
    have h1 := bnd hMW h hh
    have h2 := bnd hMC _ hsg
    have h3 := bnd hMW' _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh')
    calc B.gN (h * B.sgs p g * h'⁻¹) ≤ B.gN (h * B.sgs p g) * B.gN h'⁻¹ := Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ B.gN h * B.gN (B.sgs p g) * B.gN h'⁻¹ :=
        mul_le_mul_of_nonneg_right (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) (gN_nn _)
      _ ≤ max MW 0 * max MC 0 * max MW' 0 :=
        mul_le_mul (mul_le_mul (h1.trans (le_max_left _ _)) (h2.trans (le_max_left _ _)) (gN_nn _) (le_max_right _ _))
          (h3.trans (le_max_left _ _)) (gN_nn _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
  have hBd0 : 0 ≤ Bd := by positivity
  have hpow : B.gN (n⁻¹ * g * n') ^ (2 * r + 1) ≤ Bd ^ (2 * r + 1) := pow_le_pow_left₀ (gN_nn _) hb _
  obtain ⟨hon, hon'⟩ := hCo g hg n hn n' hn'
  have hnR : B.gN n ≤ max R 0 :=
    (hon.trans (mul_le_mul_of_nonneg_left hpow hCo0)).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hn'R : B.gN n' ≤ max R 0 :=
    (hon'.trans (mul_le_mul_of_nonneg_left hpow hCo0)).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hhR : B.gN h ≤ max R 0 :=
    (bnd hMW h hh).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hh'R : B.gN h' ≤ max R 0 :=
    (bnd hMW' h' hh').trans ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have sup : ∀ x : Mt k r, ‖x‖ ≤ B.gN (Matrix.of x) := fun x => Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.sup_le_gN (Matrix.of x)
  rw [mem_closedBall_zero_iff]
  refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · exact (sup _).trans hhR
  · exact (sup _).trans hnR
  · exact (sup _).trans hh'R
  · exact (sup _).trans hn'R

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAGrp
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def capA (k r : ℕ) (y : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X := C3.AAop k r r le_rfl (Q.uC k r 0 y) F

def capAv (k r : ℕ) (y : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X :=
  C3.AAvop k r r le_rfl (y - ((2 * r + k : ℕ) : ℂ) / 2) F

def capBeta (k r : ℕ) (c : Fin r → Fin (2 * r + k + 1)) (g : Q.Mx k r) : ℂ :=
  Matrix.det (Matrix.of fun a l : Fin r => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE le_rfl a))))

def capAlphaV (k r : ℕ) (B : Fin r → Fin (2 * r + k + 1)) (g : Q.Mx k r) : ℂ :=
  Matrix.det (Matrix.of fun a l : Fin r => ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l))

end defs

def JDACapRep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (y : ℂ),
    ∃ Θ Θv : B.DiffOp k r Wp Wq,
      PolyOp (2 * r + k + 1) ((r + 1) * (2 * r + k + 1)) Θ ∧ PolyOp (2 * r + k + 1) ((r + 1) * (2 * r + k + 1)) Θv ∧
      B.opOrder Θ = r ∧ B.opOrder Θv = r ∧
      (∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → B.CkOn (B.opOrder Θ : ℕ∞) {g} F →
        B.opApply Θ F g = capA k r y F g) ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → B.CkOn (B.opOrder Θv : ℕ∞) {g} F →
        B.opApply Θv F g = capAv k r y F g

def JDACapInv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ (y : ℂ) (Θ : B.DiffOp P.k P.r Wp Wq), P.r ≤ B.opOrder Θ →
      ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capA P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ) ∧
      ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capAv P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ)

def JDACapToda : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        Q.resG P.k P.r (Fin.last P.r) (capA P.k P.r y J) c g =
          dMul (drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g

def JDACapTodaV : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
          dMul (drbF P.r) (Q.crd (Q.cmp (vABm P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g

section assembly

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem capa_J_ck (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)) {c : Fin P.r → ℂ} (hc : c ∈ OmX P.r)
    {g : Q.Mx P.k P.r} (hg : g ∈ Q.Glev P.k P.r (Fin.last P.r))
    (hcg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs) (m : ℕ∞) :
    Q.wCell P.k P.r (Fin.last P.r) c * g ∈ B.GV P.k P.r ∧ B.CkOn m {Q.wCell P.k P.r (Fin.last P.r) c * g} J := by
  have hGV : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ B.GV P.k P.r := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV hc hg
  refine ⟨hGV, fun g₀ hg₀ => ?_⟩
  rw [Set.mem_singleton_iff] at hg₀
  subst hg₀
  have hG0 : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Q.Glev P.k P.r 0 :=
    ⟨hGV, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
  obtain ⟨U, F, hU, hmem, hF, hJF⟩ := hJ.1 _ ⟨hG0, hcg⟩
  refine ⟨U, F, hU, hmem, hF.of_le ?_, fun x hx hxG => hJF x hx ⟨hxG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩⟩
  exact_mod_cast le_top

end assembly

theorem jDAGrp_of_parts (hR : JDACapRep) (hI : JDACapInv) (hT : JDACapToda) (hTv : JDACapTodaV) : JDAGrp := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -, -, -, -, -, -, hk, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  obtain ⟨Θ, Θv, hP, hPv, hO, hOv, hA, hAv⟩ := hR S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) y
  refine ⟨Θ, Θv, hP, hPv, (hI _ _ (D.parOf S v) (T v).base hpl hk y Θ hO.ge).1 hA,
    (hI _ _ (D.parOf S v) (T v).base hpl hk y Θv hOv.ge).2 hAv, fun J hJ c hc g hg hcg => ⟨?_, ?_⟩⟩
  · obtain ⟨hGV, hCk⟩ := capa_J_ck (D.parOf S v) (T v).base hJ hc hg hcg (B.opOrder Θ)
    rw [← hT _ _ (D.parOf S v) (T v).base hpl hk y J hJ c hc g hg hcg]
    simp only [Q.resG]
    rw [hA J _ hGV hCk]
  · obtain ⟨hGV, hCk⟩ := capa_J_ck (D.parOf S v) (T v).base hJ hc hg hcg (B.opOrder Θv)
    rw [← hTv _ _ (D.parOf S v) (T v).base hpl hk y J hJ c hc g hg hcg]
    simp only [Q.resG]
    rw [hAv J _ hGV hCk]

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGGfStep
section
open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

theorem gf_castPt {k a b : ℕ} (h : a = b) (z z' : Fin (2 * a + k + 1) → ℂ) (A M C : B.Mat k a) :
    Gf k b (D.castV h z) (D.castV h z') ((D.castM h A)⁻¹ * D.castM h M * D.castM h C) =
      Gf k a z z' (A⁻¹ * M * C) := by
  subst h
  have h1 : ∀ v : Fin (2 * a + k + 1) → ℂ, D.castV rfl v = v := fun v => by
    funext i
    simp [D.castV]
  have h2 : ∀ X : B.Mat k a, D.castM rfl X = X := fun X => by
    ext i j
    simp [D.castM]
  rw [h1, h1, h2, h2, h2]

theorem gram_function_induction : GfStep := by
  intro k ρ m e z z' hz hz' t _ γ xx
  have h1 : 1 + ρ = ρ + 1 := Nat.add_comm 1 ρ
  show Gf k m (D.castV e (D.castV h1 (liftVec k 1 ρ z))) (D.castV e (D.castV h1 (liftVec k 1 ρ z')))
      ((D.castM e (D.castM h1 (U.Rn k 1 ρ xx.1)))⁻¹ *
        D.castM e (D.castM h1 (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ)) *
        D.castM e (D.castM h1 (U.Rn k 1 ρ xx.2))) = _
  rw [gf_castPt e, gf_castPt h1,
    level_function_slice k 1 ρ _ _ (Qx4.lift_inWb hz) (Qx4.lift_inWb hz'), lowV_lift, lowV_lift]
  simp [Matrix.det_unique, Complex.normSq_eq_norm_sq]

end Formalism.FourierDecayAlt.P.CutSH.SFG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH_SFG_PtGV
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBH

theorem radial_embedding_mem_unitary_group {k ρ m : ℕ} (e : ρ + 1 = m) (x : U.RC k 1 ρ) : rn1 e x ∈ B.GV k m := by
  exact PBE.castM_GV e (PBE.castM_GV _ (Ux6.Rn_mem x))

private theorem mMap_mem_GV_of_isUnit_det_of_mem_GV {k j ρ : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : IsUnit Z.det)
    (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ) : U.mMap k j ρ Z γ ∈ B.GV k (j + ρ) := by
  have hr : ∀ a b : Fin j, a = b.rev ↔ b = a.rev := fun a b =>
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  have hw : G.wMat j * G.wMat j = 1 := by
    ext a b
    simp only [G.wMat, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single b.rev]
    · simp [Fin.rev_rev, Fin.rev_inj, eq_comm]
    · intro c _ hc
      rw [if_neg (fun h => hc ((hr c b).2 h))]
      simp
    · simp
  have hwh : (G.wMat j).conjTranspose = G.wMat j := by
    ext a b
    simp only [G.wMat, Matrix.conjTranspose_apply, Matrix.of_apply]
    split_ifs with h1 h2 h2 <;> simp_all [hr]
  have hZ' : IsUnit Z.conjTranspose.det := by
    rw [Matrix.det_conjTranspose]
    exact hZ.star
  have hγ' : Matrix.conjTranspose γ * Hpk k ρ * γ = Hpk k ρ := hγ
  have h1 : Z.conjTranspose * (G.wMat j).conjTranspose * G.wMat j * (Z.conjTranspose⁻¹ * G.wMat j)
      = G.wMat j := by
    rw [hwh, Matrix.mul_assoc Z.conjTranspose, hw, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hZ', Matrix.one_mul]
  have h3 : (G.wMat j).conjTranspose * Z.conjTranspose⁻¹.conjTranspose * G.wMat j * (G.wMat j * Z)
      = G.wMat j := by
    rw [hwh, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (G.wMat j) (G.wMat j) Z, hw, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZ, Matrix.mul_one]
  show Matrix.conjTranspose (U.mMap k j ρ Z γ) * Hpk k (j + ρ) * U.mMap k j ρ Z γ = Hpk k (j + ρ)
  rw [Ux6.hpkBlocks k j ρ]
  unfold U.mMap
  rw [Ux6.block3_conjTranspose, Ux6.block3_mul, Ux6.block3_mul]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_mul]
  rw [h1, hγ', h3]

theorem mc_GV {k ρ m : ℕ} (e : ρ + 1 = m) {t : ℂ} (ht : t ≠ 0) {γ : B.Mat k ρ} (hγ : γ ∈ B.GV k ρ) :
    mc e t γ ∈ B.GV k m := by
  unfold mc
  refine PBE.castM_GV e (PBE.castM_GV _ (mMap_mem_GV_of_isUnit_det_of_mem_GV _ ?_ γ hγ))
  simp [Matrix.det_unique, ht]

theorem point_mem_unitary_group : PtGV := by
  intro k ρ m e t ht γ hγ xx
  unfold pt
  exact HermitianFormFactor.UH_mul (HermitianFormFactor.UH_mul (HermitianFormFactor.UH_inv (B2x5.isUnit_det_Hpk k m) (radial_embedding_mem_unitary_group e xx.1))
    (mc_GV e ht hγ)) (radial_embedding_mem_unitary_group e xx.2)

end Formalism.FourierDecayAlt.P.CutSH.SFG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddingMapApplyFirstBlock
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def NFHypL : Prop :=
  ∀ (k r : ℕ) (a : C.LPt) (hle : D.ptSize a ≤ r) (g' : B.Mat k (r - D.ptSize a)), g' ∈ B.GV k (r - D.ptSize a) →
    D.IsLocPt a (D.ptSize a) →
    levelZeroPointOver a hle g' ∈ B.GV k r ∧
    (∀ (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < D.ptSize a),
      PBG.xi0 (levelZeroPointOver a hle g') a' q =
        if hq : q.val < D.ptSize a then U.hMat (D.ptPerm a) (D.ptDiag a) ⟨a'.val, ha'⟩ ⟨q.val, hq⟩ else 0) ∧
    (∀ (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < D.ptSize a),
      PBG.y0 (levelZeroPointOver a hle g') a' q =
        if hq : r + k < q.val ∧ 2 * r + k - q.val < D.ptSize a then
          star (U.hMat (D.ptPerm a) (D.ptDiag a) ⟨a'.val, ha'⟩ ⟨2 * r + k - q.val, hq.2⟩) else 0)

theorem castM_apply' {k a b : ℕ} (h : a = b) (g : B.Mat k a) (i j : Fin (2 * b + k + 1)) :
    D.castM h g i j = g (Fin.cast (by rw [h]) i) (Fin.cast (by rw [h]) j) := rfl

theorem embedding_map_apply_last_block {k p ρ : ℕ} (Z : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ) (c : Fin p)
    (j : Fin (2 * (p + ρ) + k + 1)) :
    U.mMap k p ρ Z γ (U.eB k p ρ (Sum.inr c)) j =
      if hj : j.val < p then Z c.rev ⟨j.val, hj⟩ else 0 := by
  obtain ⟨y, rfl⟩ := (U.eB k p ρ).surjective j
  rw [U.mMap, Ux3.block3_apply]
  rcases y with (y | y) | y
  · rw [dite_eq_left (by rw [Ux3.block_index_first_val]; exact y.isLt)]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    rw [Ux3.wMat_mul_apply]
    exact congrArg (Z c.rev) (Fin.ext (Ux3.block_index_first_val (k := k) (ρ := ρ) y).symm)
  · rw [dite_eq_right (by rw [Ux3.block_index_middle_val]; omega)]
    simp [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inr]
  · rw [dite_eq_right (by rw [Ux3.block_index_last_val]; omega)]
    simp [Matrix.fromBlocks_apply₂₂]

theorem embedding_map_apply_first_block {k p ρ : ℕ} (Z : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ) (b : Fin p)
    (i : Fin (2 * (p + ρ) + k + 1)) :
    U.mMap k p ρ Z γ i (U.eB k p ρ (Sum.inl (Sum.inl b))) =
      if hi : p + (2 * ρ + k + 1) ≤ i.val then
        (G.wMat p * Z) ⟨i.val - (p + (2 * ρ + k + 1)), by omega⟩ b else 0 := by
  obtain ⟨y, rfl⟩ := (U.eB k p ρ).surjective i
  rw [U.mMap, Ux3.block3_apply]
  rcases y with (y | y) | y
  · rw [dite_eq_right (by rw [Ux3.block_index_first_val]; omega)]
    simp [Matrix.fromBlocks_apply₁₁]
  · rw [dite_eq_right (by rw [Ux3.block_index_middle_val]; omega)]
    simp [Matrix.fromBlocks_apply₁₁]
  · rw [dite_eq_left (by rw [Ux3.block_index_last_val]; omega)]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    exact congrArg (fun c => (G.wMat p * Z) c b) (Fin.ext (by
      show (U.eB k p ρ (Sum.inr y)).val - (p + (2 * ρ + k + 1)) = y.val
      rw [Ux3.block_index_last_val]; omega)).symm

theorem normal_form_left_hypothesis : NFHypL := by
  intro k r a hle g' hg' hloc
  have hd : ∀ i, D.ptDiag a i ≠ 0 := fun i => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne a hloc.1 i i.2
  have hZ : (U.hMat (D.ptPerm a) (D.ptDiag a)).det ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hd
  have hM : U.mMap k (D.ptSize a) (r - D.ptSize a) (U.hMat (D.ptPerm a) (D.ptDiag a)) g' ∈
      B.GV k (D.ptSize a + (r - D.ptSize a)) :=
    (Formalism.FourierDecayAlt.P.slice_membership k (D.ptSize a) (r - D.ptSize a)).1 _ g' hZ hg'
  refine ⟨Formalism.FourierDecayAlt.P.PBE.castM_GV _ hM, fun a' q ha' => ?_, fun a' q ha' => ?_⟩
  · unfold PBG.xi0
    rw [Formalism.FourierDecayAlt.P.PBM.herm_bvec_eI', Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
    unfold levelZeroPointOver
    rw [castM_apply']
    have hi : (Fin.cast (by omega) (esI k r a') : Fin (2 * (D.ptSize a + (r - D.ptSize a)) + k + 1)) =
        U.eB k (D.ptSize a) (r - D.ptSize a) (Sum.inr ⟨D.ptSize a - 1 - a'.val, by omega⟩) := by
      ext; rw [Ux3.block_index_last_val]; simp [esI]; omega
    rw [hi, embedding_map_apply_last_block]
    by_cases hq : q.val < D.ptSize a
    · rw [dite_eq_left (by simpa using hq), dite_eq_left hq]
      congr 1; ext; simp [Fin.val_rev]; omega
    · rw [dite_eq_right (by simpa using hq), dite_eq_right hq]
  · unfold PBG.y0
    rw [Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
    have hgu : IsUnit g'.det := WeylGroupFacts.isUnit_of_uh hg'
    unfold levelZeroPointOver
    rw [← Formalism.FourierDecayAlt.P.PBH.asm_castM_inv, Formalism.FourierDecayAlt.P.PBM.mMap_inv _ _ (isUnit_iff_ne_zero.mpr hZ) hgu, castM_apply']
    have hj : (Fin.cast (by omega) (eI k r a') : Fin (2 * (D.ptSize a + (r - D.ptSize a)) + k + 1)) =
        U.eB k (D.ptSize a) (r - D.ptSize a) (Sum.inl (Sum.inl ⟨a'.val, ha'⟩)) := by
      ext; rw [Ux3.block_index_first_val]; simp [eI]
    rw [hj, embedding_map_apply_first_block]
    by_cases hq : r + k < q.val ∧ 2 * r + k - q.val < D.ptSize a
    · rw [dite_eq_left (by simp; omega), dite_eq_left hq, Ux3.wMat_mul_apply, Matrix.conjTranspose_apply]
      congr 2 <;> ext <;> simp [Fin.val_rev] <;> omega
    · rw [dite_eq_right (by simp; omega), dite_eq_right hq]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadTopOfRadialExhaustion
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBI

def ExhPic : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    KB.IsTopLift2 P p.l0 p.T.base L₀ st₀ p.Θ →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (e : Wd.Ix (Fin w.length)) (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F₁ ∧ KB.CptCoef p.T.base F₂ ∧
      (∀ ζ : ℂ, p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = p.V (p.Θ.Θ w e F₁) (h ++ [(1, ζ)])) ∧
      (∀ Φ₁ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ₁ F₁ →
        Top.IsRadOf P p.T.base
          (P5.act ((Fr.ofWord L₀ st₀ (D.positionted w)).F * P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ₁) e) F₂) ∧
      ∀ (Φ : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
          (p.T.bs P.r).π (p.T.bs P.r).π'),
        (∀ e', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e') (KB.slv p.T F P.r le_rfl w h hh.2 e')) →
        ∀ (c : Fin (JC.parLev P P.r).r → ℂ) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
          0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
          B.JF (p.T.bs P.r) (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F₂ h)) γ =
            (P5.act (Fr.ofWord L st (D.positionted w)).F Φ e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c γ

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem exhaustion_of_radial_form : PBI.ExhPic → PBI.Exh := by
  intro hPic Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb hD hdd hF hcut e h hh
  obtain ⟨X₀, μ₀, L₀, st₀, hD₀, hTL⟩ := p.hΘ
  obtain ⟨F₁, F₂, hF₁, hF₂, hloc, hpic, hii⟩ :=
    hPic Wp Wq P p F w X μ L st Cb X₀ μ₀ L₀ st₀ hD hD₀ hTL hdd hF hcut e h hh
  obtain ⟨F', hF', hagree, hVeq⟩ := theta_compact_support Wp Wq P p F₁ w e Cb hdd hF₁ hcut
  refine ⟨F₂, hF₂, fun ζ => ?_, hii⟩
  obtain ⟨Φ₁, hΦ₁⟩ := PBN.radExists p hF₁
  have hΘpic := hTL w hcut F₁ hF₁ Φ₁ hΦ₁ e
  have hF'pic := PBN.isRadOf_congr p.T.base hΘpic hagree
  rw [hloc ζ, hVeq]
  exact PBN.vecV_eq_of_rad density_constant p hF' hF₂ hF'pic (hpic Φ₁ hΦ₁) _

theorem head_top_of_radial_exhaustion (hU5 : PBI.HighestUnipotentIntegral) (hPic : PBI.ExhPic) (hW : PBI.HeadWeightAt) : KB.HeadTop :=
  head_top_of_parts hU5 (exhaustion_of_radial_form hPic) hW

end Formalism.FourierDecayAlt.P
end
end

