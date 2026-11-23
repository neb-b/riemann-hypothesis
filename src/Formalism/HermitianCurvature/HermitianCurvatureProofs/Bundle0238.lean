module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0232
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0132
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0160
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0136
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPBeta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0139
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPConseq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPContPf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMConseq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0206
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMBeta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemDomain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0133
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0106
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0227
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0221
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0233
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0234
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0235

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrpCut
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def RightRuleEv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z' → IsOpen D → Q.SmoothLev k r 0 D f →
    Q.RightEq k r z' 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ a b : Fin r, b.val < a.val →
      Q.EH k r (esI k r a) (esI k r b) f g = (if a.val = b.val + 1 then (1 : ℂ) else 0) • f g

def LeftRuleCellv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z → IsOpen D →
    (∀ g ∈ Q.Glev k r 0 ∩ D, ∀ n ∈ Q.Nlev k r 0, n * g ∈ D) → Q.SmoothLev k r 0 D f → Q.LeftEq k r z 0 D f →
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D → ∀ a b : Fin r, b.val < a.val →
      Q.EH k r (esI k r b) (esI k r a) f (Q.wCell k r (Fin.last r) c * g) =
        (if a.val = b.val + 1 then star (c a) / star (c b) else 0) • f (Q.wCell k r (Fin.last r) c * g)

def TorusCellv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r 0 D f → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
    Q.wCell k r (Fin.last r) c * g ∈ D → ∀ l : Fin r,
      Q.EH k r (esI k r l) (esI k r l) f (Q.wCell k r (Fin.last r) c * g) =
        -pbOp l (fun c' => f (Q.wCell k r (Fin.last r) c' * g)) c

def MirrorChainExpansion : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) (ρ : ℂ), GlRel E →
    ∀ (m : ℕ) (hm : m + 2 ≤ r) (u : ℂ),
    (∀ (x : A) (a : Fin r), r - m - 1 < a.val → La (x * E (esI k r a) (esI k r ⟨r - m - 2, by omega⟩)) = 0) →
    (∀ x : A, La (x * E (esI k r ⟨r - m - 1, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) = La x) →
    (∀ (x : A) (b : Fin r), r - m - 2 < b.val →
      La (E (esI k r ⟨r - m - 2, by omega⟩) (esI k r b) * x) = (if b.val = r - m - 1 then ρ else 0) • La x) →
    La (qminor E (colsVm k r (m + 2)) (colsVm k r (m + 2)) u) =
      La (qminor E (colsVm k r (m + 1)) (colsVm k r (m + 1)) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (esI k r ⟨r - m - 2, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) -
        ρ • La (qminor E (colsVm k r m) (colsVm k r m) u)

end Formalism.FourierDecayAlt.P.CutMP.TVG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

theorem jDRRadP_of_steps (hA : JDRStepA) (hB : JDRStepB) : JDRRadP :=
  jDRRadP_of_parts JDBeta.residue_beta_holds residue_top_holds hA hB (jDRConseq_of residue_projection_commutation residue_continuity_holds)

theorem jDRGrpP_of_invFn (hA : JDRStepA) (hB : JDRStepB) (hI : JDRInvFn) : JDRGrpP :=
  jDRGrpP_of_parts (jDRRadP_of_steps hA hB) (jDRRealInvP_of_inv hI)

theorem jDRGrpM_of_vBeta_invFnM (hvB : JDRvBeta) (hvA : JDRvStepA) (hvS : JDRvStepB) (hIM : JDRInvFnM) : JDRGrpM :=
  jDRGrpM_of_parts (jDRRadM_of_parts hvB mirror_residue_top_holds hvA hvS (jDRvConseq_of mirror_residue_continuity))
    (jDRRealInvM_of_inv hIM)

theorem jDCapR_of_halves (hP : JDRGrpP) (hM : JDRGrpM) : JDCapR :=
  jDCapR_of_parts (jDRGrp_of_halves hP hM) residue_derivative_transition mirror_residue_model_holds

theorem jDOpR_of_poly_grp (hPoly : JDPolyOK) (hP : JDRGrpP) (hM : JDRGrpM) : JDOpR :=
  jDOpR_of_parts hPoly (jDCapR_of_halves hP hM)

theorem jDOpR_of_leaves (hPoly : JDPolyOK) (hA : JDRStepA) (hI : JDRInvFn) (hvB : JDRvBeta)
    (hvA : JDRvStepA) (hvS : JDRvStepB) (hIM : JDRInvFnM) : JDOpR :=
  jDOpR_of_poly_grp hPoly (jDRGrpP_of_invFn hA residue_second_move_holds hI) (jDRGrpM_of_vBeta_invFnM hvB hvA hvS hIM)

theorem jDOpR_of_invFn (hI : JDRInvFn) (hvS : JDRvStepB) (hIM : JDRInvFnM) : JDOpR :=
  jDOpR_of_leaves polynomial_decay_admissible residue_first_move_holds hI mirror_residue_beta_holds GrpMA.mirror_residue_first_move hvS hIM

theorem jDOpR_of_vStepB (hvS : JDRvStepB) : JDOpR :=
  jDOpR_of_invFn inverse_function_positive_holds hvS inverse_function_minus_holds

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHCellTie
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

private theorem castV_liftVec_liftVec_eq_castV_liftVec_succ {k j ρ m n : ℕ} (e : 1 + ρ = m) (h1 : j + m = n)
    (h2 : j + 1 + ρ = n) (v : Fin (2 * ρ + k + 1) → ℂ) :
    D.castV h1 (QuantumDeterminants.liftVec k j m (D.castV e (QuantumDeterminants.liftVec k 1 ρ v))) =
      D.castV h2 (QuantumDeterminants.liftVec k (j + 1) ρ v) := by
  funext p
  simp only [D.castV, QuantumDeterminants.liftVec, Fin.coe_cast]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; ext; simp only [Fin.coe_cast]; omega)

private theorem consC_castM_ιLev_mem_DomR_of_mem_DomR {k ρ m : ℕ} (e : 1 + ρ = m) {t : ℂ} (ht : t ≠ 0)
    (z z' : Fin (2 * ρ + k + 1) → ℂ) (c : Fin ρ → ℂ) (g : Q.Mx k ρ)
    (h : (c, g) ∈ Q.DomR k ρ z z') :
    ((fun l : Fin m => PBH.consC t c (Fin.cast e.symm l)), D.castM e (QuantumDeterminants.ιLev k 1 ρ g)) ∈
      Q.DomR k m (D.castV e (QuantumDeterminants.liftVec k 1 ρ z)) (D.castV e (QuantumDeterminants.liftVec k 1 ρ z')) := by
  subst e
  rw [JCTx5.castV_rfl, JCTx5.castV_rfl, JCTx5.castM_rfl]
  exact (PBH.domR_iota ht z z' c g).2 h

theorem cell_compatibility : CellTie := by
  intro Wp Wq _ _ _ _ _ _ P T hP hN j hj hPj hPj1 t ht x hx
  have e : 1 + (P.r - (j + 1)) = P.r - j := by omega
  have hz : (T.bs j).z = D.castV e (QuantumDeterminants.liftVec P.k 1 (P.r - (j + 1)) (T.bs (j + 1)).z) := by
    apply JCTx5.liftVec_inj (i := j)
    apply PBH.castV_inj (show j + (P.r - j) = P.r by omega)
    rw [T.z_lev j (by omega), castV_liftVec_liftVec_eq_castV_liftVec_succ e (show j + (P.r - j) = P.r by omega)
      (show j + 1 + (P.r - (j + 1)) = P.r by omega), T.z_lev (j + 1) hj]
  have hz' : (T.bs j).z' =
      D.castV e (QuantumDeterminants.liftVec P.k 1 (P.r - (j + 1)) (T.bs (j + 1)).z') := by
    apply JCTx5.liftVec_inj (i := j)
    apply PBH.castV_inj (show j + (P.r - j) = P.r by omega)
    rw [T.z'_lev j (by omega), castV_liftVec_liftVec_eq_castV_liftVec_succ e (show j + (P.r - j) = P.r by omega)
      (show j + 1 + (P.r - (j + 1)) = P.r by omega), T.z'_lev (j + 1) hj]
  refine ⟨?_, PBF.wCell_mul_GV hx.1 hx.2.1,
    P5.Rad.wCell_mem_omPlus hPj1.2.1 hPj1.2.2.1 hx.1 hx.2.1 hx.2.2⟩
  rw [hz, hz']
  exact consC_castM_ιLev_mem_DomR_of_mem_DomR e ht _ _ x.1 x.2 hx

end Formalism.FourierDecayAlt.P.CutSH

theorem Formalism.FourierDecayAlt.P.cell_compatibility_identity : Formalism.FourierDecayAlt.P.CutSH.CellTie := Formalism.FourierDecayAlt.P.CutSH.cell_compatibility
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DegreeTop
section
namespace Formalism.FourierDecayAlt.P

theorem degree_top : Formalism.FourierDecayAlt.KB.DegTop := pb_degTop_of_polyTop polynomial_top

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameParameterRegularity
section
noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem good_function_leaf : CutFP.GoodFnLeaf :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hT X j => ParameterFamilyAlgebra.good_fn hT X j

theorem good_transfer_leaf : CutFP.GoodTLeaf :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hOm hS X Y a b => ParameterFamilyAlgebra.good_alt_bis hOm hS X Y a b

theorem frame_parameter_regularity : PBI.FrameParam :=
  CutFP.frameParam_of good_function_leaf good_transfer_leaf

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GoodCongr
section
open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

section fam2

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem good_congr {Φ Ψ : X → V1 E} (h : Good Φ) (hΨ : ∀ v τ, τ ≠ 0 → (Ψ v : ℂ → E) τ = (Φ v : ℂ → E) τ) :
    Good Ψ := by
  refine ⟨h.1.congr fun q hq => hΨ q.1 q.2 hq.2, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  exact ⟨C, hC, fun v hv τ hτ => by rw [hΨ v τ (hK0 hτ), hz v hv τ hτ]⟩

theorem good_zero : Good (fun _ : X => (0 : V1 E)) :=
  ⟨contDiffOn_const.congr fun _ _ => rfl, fun _ _ _ => ⟨∅, isCompact_empty, fun _ _ _ _ => rfl⟩⟩

theorem good_add {Φ Ψ : X → V1 E} (h : Good Φ) (h' : Good Ψ) : Good (fun v => Φ v + Ψ v) := by
  refine ⟨(h.1.add h'.1).congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  obtain ⟨C', hC', hz'⟩ := h'.2 K hK hK0
  refine ⟨C ∪ C', hC.union hC', fun v hv τ hτ => ?_⟩
  simp only [Set.mem_union, not_or] at hv
  show (Φ v : ℂ → E) τ + (Ψ v : ℂ → E) τ = 0
  rw [hz v hv.1 τ hτ, hz' v hv.2 τ hτ, add_zero]

theorem good_smul {Φ : X → V1 E} (h : Good Φ) (c : ℂ) : Good (fun v => c • Φ v) := by
  refine ⟨(h.1.const_smul c).congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  show c • (Φ v : ℂ → E) τ = 0
  rw [hz v hv τ hτ, smul_zero]

theorem good_sum {ι : Type*} (s : Finset ι) (Φ : ι → X → V1 E) (h : ∀ i ∈ s, Good (Φ i)) :
    Good (fun v => ∑ i ∈ s, Φ i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (good_zero : Good (fun _ : X => (0 : V1 E)))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact good_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem good_opM {Φ : X → V1 E} (h : Good Φ) (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0}) :
    Good (fun v => opM m hm (Φ v)) := by
  have hm2 : ContDiffOn ℝ ∞ (fun q : X × ℂ => m q.2) (UX X) :=
    hm.comp contDiff_snd.contDiffOn fun q hq => hq.2
  refine ⟨(hm2.smul h.1).congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  show m τ • (Φ v : ℂ → E) τ = 0
  rw [hz v hv τ hτ, smul_zero]

def dzF (Φ : X → V1 E) : X → V1 E := fun v => ⟨PBP.dz (Φ v : ℂ → E), contDiffOn_wirtinger_dz (Φ v).2⟩

def dzbF (Φ : X → V1 E) : X → V1 E := fun v => ⟨PBP.dzb (Φ v : ℂ → E), contDiffOn_wirtinger_dzbar (Φ v).2⟩

theorem good_dz {Φ : X → V1 E} (h : Good Φ) : Good (dzF Φ) := by
  have hc : ContDiffOn ℝ ∞ (fun q : X × ℂ => PBP.dz (Φ q.1 : ℂ → E) q.2) (UX X) := by
    unfold PBP.dz
    exact ((cd_partial h 1).sub ((cd_partial h Complex.I).const_smul Complex.I)).const_smul _
  refine ⟨hc.congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h hK hK0
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  show PBP.dz (Φ v : ℂ → E) τ = 0
  unfold PBP.dz
  rw [hz v hv τ hτ]
  simp

theorem good_dzb {Φ : X → V1 E} (h : Good Φ) : Good (dzbF Φ) := by
  have hc : ContDiffOn ℝ ∞ (fun q : X × ℂ => PBP.dzb (Φ q.1 : ℂ → E) q.2) (UX X) := by
    unfold PBP.dzb
    exact ((cd_partial h 1).add ((cd_partial h Complex.I).const_smul Complex.I)).const_smul _
  refine ⟨hc.congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h hK hK0
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  show PBP.dzb (Φ v : ℂ → E) τ = 0
  unfold PBP.dzb
  rw [hz v hv τ hτ]
  simp

theorem opP_apply (κ : ℂ) (f : V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    ((opP κ f : V1 E) : ℂ → E) τ = τ • PBP.dz (f : ℂ → E) τ + κ • (f : ℂ → E) τ := by
  show off0 (fun τ => τ • PBP.dz (f : ℂ → E) τ + κ • (f : ℂ → E) τ) τ = _
  rw [off0, if_neg hτ]

theorem opPb_apply (κ : ℂ) (f : V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    ((opPb κ f : V1 E) : ℂ → E) τ = conj τ • PBP.dzb (f : ℂ → E) τ + κ • (f : ℂ → E) τ := by
  show off0 (fun τ => conj τ • PBP.dzb (f : ℂ → E) τ + κ • (f : ℂ → E) τ) τ = _
  rw [off0, if_neg hτ]

section ok

variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ℓ : X → E →L[ℂ] E)

def OK (T : Module.End ℂ (V1 E)) : Prop :=
  ∀ (Φ : X → V1 E) (f : V1 E), Good Φ → IsInt μ ℓ Φ f →
    Good (fun v => T (Φ v)) ∧ IsInt μ ℓ (fun v => T (Φ v)) (T f)

variable {μ ℓ}

theorem int_add {Φ Ψ : X → V1 E} {f g : V1 E} (hℓ : Continuous ℓ) (h : Good Φ) (h' : Good Ψ)
    (hf : IsInt μ ℓ Φ f) (hg : IsInt μ ℓ Ψ g) : IsInt μ ℓ (fun v => Φ v + Ψ v) (f + g) := by
  intro τ hτ
  show (f : ℂ → E) τ + (g : ℂ → E) τ = ∫ v, ℓ v ((Φ v : ℂ → E) τ + (Ψ v : ℂ → E) τ) ∂μ
  rw [hf τ hτ, hg τ hτ, ← integral_add (good_int μ ℓ h hℓ hτ) (good_int μ ℓ h' hℓ hτ)]
  congr 1
  funext v
  rw [map_add (f := _)]

theorem int_smul {Φ : X → V1 E} {f : V1 E} (hf : IsInt μ ℓ Φ f) (c : ℂ) :
    IsInt μ ℓ (fun v => c • Φ v) (c • f) := by
  intro τ hτ
  show c • (f : ℂ → E) τ = ∫ v, ℓ v (c • (Φ v : ℂ → E) τ) ∂μ
  rw [hf τ hτ, ← integral_smul]
  congr 1
  funext v
  rw [map_smul]

theorem int_zero : IsInt μ ℓ (fun _ : X => (0 : V1 E)) 0 := by
  intro τ _
  show (0 : E) = ∫ v, ℓ v (0 : E) ∂μ
  simp

theorem int_sum {ι : Type*} (hℓ : Continuous ℓ) (s : Finset ι) (Φ : ι → X → V1 E) (f : ι → V1 E)
    (h : ∀ i ∈ s, Good (Φ i)) (hf : ∀ i ∈ s, IsInt μ ℓ (Φ i) (f i)) :
    IsInt μ ℓ (fun v => ∑ i ∈ s, Φ i v) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (int_zero : IsInt μ ℓ (fun _ : X => (0 : V1 E)) 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact int_add hℓ (h a (Finset.mem_insert_self a s))
      (good_sum s Φ fun i hi => h i (Finset.mem_insert_of_mem hi)) (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem ok_zero : OK μ ℓ (0 : Module.End ℂ (V1 E)) := fun _ _ _ _ => ⟨good_zero, int_zero⟩

theorem ok_one : OK μ ℓ (1 : Module.End ℂ (V1 E)) := fun _ _ h hf => ⟨h, hf⟩

theorem ok_add (hℓ : Continuous ℓ) {T T' : Module.End ℂ (V1 E)} (h : OK μ ℓ T) (h' : OK μ ℓ T') :
    OK μ ℓ (T + T') := fun Φ f hΦ hf =>
  ⟨good_add (h Φ f hΦ hf).1 (h' Φ f hΦ hf).1, int_add hℓ (h Φ f hΦ hf).1 (h' Φ f hΦ hf).1 (h Φ f hΦ hf).2
    (h' Φ f hΦ hf).2⟩

theorem ok_mul {T T' : Module.End ℂ (V1 E)} (h : OK μ ℓ T) (h' : OK μ ℓ T') : OK μ ℓ (T * T') :=
  fun Φ f hΦ hf => h _ _ (h' Φ f hΦ hf).1 (h' Φ f hΦ hf).2

theorem ok_smul {T : Module.End ℂ (V1 E)} (h : OK μ ℓ T) (c : ℂ) : OK μ ℓ (c • T) := fun Φ f hΦ hf =>
  ⟨good_smul (h Φ f hΦ hf).1 c, int_smul (h Φ f hΦ hf).2 c⟩

theorem ok_neg {T : Module.End ℂ (V1 E)} (h : OK μ ℓ T) : OK μ ℓ (-T) := by
  rw [← neg_one_smul ℂ T]
  exact ok_smul h (-1)

theorem ok_alg (c : ℂ) : OK μ ℓ (algebraMap ℂ (Module.End ℂ (V1 E)) c) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact ok_smul ok_one c

theorem ok_opM (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0}) : OK μ ℓ (opM (E := E) m hm) := by
  intro Φ f hΦ hf
  refine ⟨good_opM hΦ m hm, fun τ hτ => ?_⟩
  show m τ • (f : ℂ → E) τ = ∫ v, ℓ v (m τ • (Φ v : ℂ → E) τ) ∂μ
  rw [hf τ hτ, ← integral_smul]
  congr 1
  funext v
  rw [map_smul]

theorem ok_opP (hℓ : Continuous ℓ) (κ : ℂ) : OK μ ℓ (opP (E := E) κ) := by
  intro Φ f hΦ hf
  have hg : Good (fun v => opM (fun τ => τ) cd_id (dzF Φ v) + κ • Φ v) :=
    good_add (good_opM (good_dz hΦ) _ _) (good_smul hΦ κ)
  refine ⟨good_congr hg fun v τ hτ => by rw [opP_apply κ _ hτ]; rfl, fun τ hτ => ?_⟩
  have i1 : Integrable (fun v => τ • ℓ v (PBP.dz (Φ v : ℂ → E) τ)) μ := (good_int μ ℓ (good_dz hΦ) hℓ hτ).smul τ
  have i2 : Integrable (fun v => κ • ℓ v ((Φ v : ℂ → E) τ)) μ := (good_int μ ℓ hΦ hℓ hτ).smul κ
  rw [opP_apply κ f hτ, dz_int μ ℓ hΦ hℓ hf hτ, hf τ hτ, ← integral_smul, ← integral_smul, ← integral_add i1 i2]
  congr 1
  funext v
  rw [opP_apply κ _ hτ, map_add (f := _), map_smul, map_smul]

theorem ok_opPb (hℓ : Continuous ℓ) (κ : ℂ) : OK μ ℓ (opPb (E := E) κ) := by
  intro Φ f hΦ hf
  have hg : Good (fun v => opM (fun τ => conj τ) cd_conj (dzbF Φ v) + κ • Φ v) :=
    good_add (good_opM (good_dzb hΦ) _ _) (good_smul hΦ κ)
  refine ⟨good_congr hg fun v τ hτ => by rw [opPb_apply κ _ hτ]; rfl, fun τ hτ => ?_⟩
  have i1 : Integrable (fun v => conj τ • ℓ v (PBP.dzb (Φ v : ℂ → E) τ)) μ :=
    (good_int μ ℓ (good_dzb hΦ) hℓ hτ).smul (conj τ)
  have i2 : Integrable (fun v => κ • ℓ v ((Φ v : ℂ → E) τ)) μ := (good_int μ ℓ hΦ hℓ hτ).smul κ
  rw [opPb_apply κ f hτ, dzb_int μ ℓ hΦ hℓ hf hτ, hf τ hτ, ← integral_smul, ← integral_smul, ← integral_add i1 i2]
  congr 1
  funext v
  rw [opPb_apply κ _ hτ, map_add (f := _), map_smul, map_smul]

end ok

end fam2

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LamSumPos
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem firstSt_inj {w : List C.Letter} : ∀ ys : List ℝ, Function.Injective (KB.firstSt (w := w) ys)
  | [] => fun _ _ h => h
  | _ :: ys => fun e e' h => firstSt_inj ys (Fin.cons_right_injective (α := fun _ => Fin 2) (0 : Fin 2) h)

theorem lam_sum_eq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) :
    ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| = ∏ b, ∑ i, |F7.lagCo (grid b) i| := by
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun n _ => Finset.abs_prod _ _

theorem lam_sum_pos {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hinj : ∀ b, Function.Injective (grid b)) :
    0 < ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| := by
  rw [lam_sum_eq]
  refine Finset.prod_pos fun b _ => ?_
  exact lt_of_lt_of_le (abs_pos.2 (PBD.lagCo_ne_zero _ (hinj b) 0))
    (Finset.single_le_sum (f := fun i => |F7.lagCo (grid b) i|) (fun i _ => abs_nonneg _) (Finset.mem_univ 0))

theorem thGrid_eq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (n : Fin K → Fin (d + 1)) :
    F7.thGrid grid n = |∏ b, F7.lagCo (grid b) (n b)| / ∑ m : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (m b)| := by
  unfold F7.thGrid
  rw [Finset.prod_div_distrib, lam_sum_eq, Finset.abs_prod]

theorem lam_sum_le {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (B : ℝ)
    (hb : ∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ B) :
    ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| ≤ B ^ K := by
  rw [lam_sum_eq]
  calc ∏ b, ∑ i, |F7.lagCo (grid b) i| ≤ ∏ _b : Fin K, B :=
        Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun b _ => hb b
    _ = B ^ K := by simp

theorem zpow_sq_eq (x : ℝ) (hx : 0 < x) (ν : ℤ) : (x ^ ν) ^ 2 = x⁻¹ ^ (-(2 * ν)) := by
  rw [inv_zpow', neg_neg, ← zpow_natCast, ← zpow_mul, mul_comm]
  norm_num

section psd

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

theorem psd_dsum {Ea R : Type} [Fintype Ea] [Fintype R] (Y : Finset α) (d : Ea → R → ℝ) (hd : ∀ e ρ, 0 ≤ d e ρ)
    (V : Ea → R → α → H) : TB.PSDOn Y (fun P Q => ∑ e, ∑ ρ, (d e ρ : ℂ) * gramH (V e ρ) P Q) := by
  have h := loe_sum (Finset.univ : Finset Ea) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun e P Q => ∑ ρ, (d e ρ : ℂ) * gramH (V e ρ) P Q) fun e _ => by
      have := loe_sum (Finset.univ : Finset R) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
        (B := fun ρ P Q => (d e ρ : ℂ) * gramH (V e ρ) P Q) fun ρ _ => by
          have := loe_smul (d e ρ) (hd e ρ) (loe_zero_of_psd (psd_gramH Y (V e ρ)))
          exact loe_congr (fun x _ y _ => by ring) (fun x _ y _ => rfl) this
      exact loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) this
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

theorem psd_mixω {N : Type} [Fintype N] (Y : Finset α) (ω : α → ℝ) (θ κ : N → ℝ) (hθ : ∀ n, 0 ≤ θ n)
    (hκ : ∀ n, 0 ≤ κ n) (Kn : N → α → α → ℂ) (hK : ∀ n, TB.PSDOn Y (Kn n)) :
    TB.PSDOn Y (fun P Q => ∑ n, (θ n : ℂ) * ((ω P : ℂ) * (ω Q : ℂ) * ((κ n : ℂ) * Kn n P Q))) := by
  have h := loe_sum (Finset.univ : Finset N) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun n P Q => (θ n : ℂ) * ((ω P : ℂ) * (ω Q : ℂ) * ((κ n : ℂ) * Kn n P Q))) fun n _ => by
      have h1 := loe_diag ω (loe_smul (θ n * κ n) (mul_nonneg (hθ n) (hκ n)) (loe_zero_of_psd (hK n)))
      exact loe_congr (fun x _ y _ => by simp) (fun x _ y _ => by push_cast; ring) h1
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

end psd

theorem mix_alg {N : Type} [Fintype N] (ω1 ω2 ka X L : ℝ) (lam Pn : N → ℝ) (Kn : N → ℂ) (hL : L ≠ 0)
    (hP : ∀ n, Pn n ≠ 0) :
    (ω1 : ℂ) * (ω2 : ℂ) * ((ka : ℂ) * ((X : ℂ) * ∑ n, ((|lam n| / Pn n : ℝ) : ℂ) * Kn n)) =
      ((X * L : ℝ) : ℂ) * ∑ n, ((|lam n| / L : ℝ) : ℂ) * ((ω1 : ℂ) * (ω2 : ℂ) * (((ka / Pn n : ℝ) : ℂ) * Kn n)) := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 := hP n
  push_cast
  field_simp

end

end Formalism.FourierDecayAlt.P.PBL
end

