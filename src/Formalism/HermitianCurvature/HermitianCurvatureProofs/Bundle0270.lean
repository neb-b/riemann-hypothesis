module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0267
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0266
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0265
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSIpInt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSFund
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0268
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0269
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSAGrp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0207
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0227
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0232
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSRhR
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTop

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpecAsm
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem rDIdentSpec_of_open (h0 : RDSOpAv) (h1 : RDSOpR) (h2 : RDSOpRv) (h3 : RDSOpA)
    (hp : RDSPAdj) (hQ : RDSQQAdj) (hX : RDSXiTest) (hP : RDSPair) : RDIdentSpec :=
  rDIdentSpec_of_cut spectral_Y_real h0 h1 h2 h3 spectral_inner_product_linear (rDSCoordAdj_of_p hp) spectral_function_adjoint hQ hX spectral_fundamental_identity spectral_section_identity hP
    radial_residue_formula radial_operator_function_field

end Formalism.FourierDecayAlt.P.CutSE
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSNicePoly
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_nice_polynomial : RDSNicePoly := by
  intro k r Wp Wq _ _ _ _ _ _ D o κ Θ hΘ F hF
  obtain ⟨-, hGl, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hΘ
  have hG : CutMP.GlobCoef Θ (κ : ℝ) := hGl κ le_rfl
  have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  obtain ⟨ε, hε, hFck, hFcc, hFs⟩ := hF
  have hO : IsOpen {g : B.Mat k r | Gf k r D.z D.z' g < ε} := isOpen_lt (Gf_cont _ _) continuous_const
  have hz : ∀ g ∈ B.GV k r, g ∈ {g : B.Mat k r | Gf k r D.z D.z' g < ε} → F g = 0 := by
    intro g hg hgO
    by_contra hne
    exact absurd hgO (not_lt.2 (hFs g hg hne))
  refine ⟨⟨ε, hε, ?_, ?_, ?_⟩, ⟨ε, hε, ?_, ?_, ?_⟩⟩
  · exact (CutMP.class_lower_decay_holds k r Wp Wq Θ κ 0 hκ hG F hFck (fun m => hFcc _ m)).1
  · intro A' m'
    have h := (CutMP.class_lower_decay_holds k r Wp Wq Θ κ (A' + κ) hκ hG F hFck (fun m => hFcc _ m)).2 m'
    rwa [add_sub_cancel_right] at h
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opApply_vanish Θ hO hz g hg (not_le.1 hlt))
  · exact (rdsp_opAdj_cc Θ κ hG F hFck 0 (fun m => hFcc _ m)).1
  · intro A' m'
    exact (rdsp_opAdj_cc Θ κ hG F hFck A' (fun m => hFcc _ m)).2 m'
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opAdj_vanish Θ hO hz g hg (not_le.1 hlt))

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpADone
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_operator_A : RDSOpA :=
  rDSOpA_of_parts spectral_polynomial_property spectral_group_action spectral_radial_action spectral_action_locality

theorem spectral_operator_A_adjoint : RDSOpAv :=
  rDSOpAv_of_parts spectral_polynomial_property spectral_group_action spectral_radial_action spectral_action_locality

end Formalism.FourierDecayAlt.P.CutSE
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPOp
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Help

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem rdsp_rw_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E) (w : List (B.Mat k r)) :
    ∀ g, g ∉ tsupport F → B.Rw w F g = 0 := by
  intro g hg
  rw [Formalism.FourierDecayAlt.P.JCTx6.Pos.rw_congr_open (isClosed_tsupport F).isOpen_compl (f₁ := F) (f₂ := 0)
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) w g hg, Formalism.FourierDecayAlt.P.CutMP.JA.GA.rw_zero_fn]
  rfl

theorem rdsp_tsupport_sub {E E' : Type*} [Zero E] [Zero E'] {G : B.Mat k r → E} {F : B.Mat k r → E'}
    (h : ∀ g, g ∉ tsupport F → G g = 0) : tsupport G ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro g hg
  by_contra hc
  exact hg (h g hc)

variable [FiniteDimensional ℂ Wq]

theorem rdsp_opApply_vanishP (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    ∀ g, g ∉ tsupport F → B.opApply Θ F g = 0 := by
  have hz : ∀ x ∈ (tsupport F)ᶜ, F x = 0 := by
    intro x hx
    by_contra hne
    exact hx (subset_tsupport F (Function.mem_support.mpr hne))
  intro g hg
  unfold Formalism.FourierDecayAlt.B.opApply
  have h0 : ∀ T ∈ Θ, T.coef g (B.Rw T.word F g) = 0 := by
    intro T _
    rw [Formalism.FourierDecayAlt.P.Ux8.Rw_vanish (isClosed_tsupport F).isOpen_compl hz T.word g hg, map_zero]
  first
    | (apply List.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hx
       exact h0 T hT)
    | (apply Multiset.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp hx
       exact h0 T hT)

theorem rdsp_opAdj_vanishP (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    ∀ g, g ∉ tsupport F → B.opAdj Θ F g = 0 := by
  have hz : ∀ x ∈ (tsupport F)ᶜ, F x = 0 := by
    intro x hx
    by_contra hne
    exact hx (subset_tsupport F (Function.mem_support.mpr hne))
  intro g hg
  unfold Formalism.FourierDecayAlt.B.opAdj
  have h0 : ∀ T ∈ Θ, ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g = 0 := by
    intro T _
    have hz' : ∀ x ∈ (tsupport F)ᶜ, T.coefAdj x (F x) = 0 := by
      intro x hx
      rw [hz x hx, map_zero]
    rw [Formalism.FourierDecayAlt.P.Ux8.Rw_vanish (isClosed_tsupport F).isOpen_compl hz' T.word.reverse g hg, smul_zero]
  first
    | (apply List.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hx
       exact h0 T hT)
    | (apply Multiset.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp hx
       exact h0 T hT)

end Help

theorem spectral_pairing_operator : RDSPOp := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hS hC F hF hFc hFO
  have hOP : tsupport F ⊆ B.GPos D := fun g hg => ⟨(hFO hg).1, (hFO hg).2.2⟩
  have hsuppF : B.SuppIn (B.GPos D) F :=
    (closure_mono (by exact fun g hg => hg.2)).trans ((closure_minimal subset_closure (isClosed_tsupport F)).trans hOP)
  have hA1t : tsupport (B.opApply Θ F) ⊆ tsupport F := rdsp_tsupport_sub (rdsp_opApply_vanishP Θ F)
  have hB1t : tsupport (B.opAdj Θ F) ⊆ tsupport F := rdsp_tsupport_sub (rdsp_opAdj_vanishP Θ F)
  have hA1s : B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) := by
    refine Formalism.FourierDecayAlt.P.PBJ.ckOn_opApply_list (B.GPos D) F hF hsuppF Θ (fun T hT => (hS T hT).1) fun T _ => ?_
    refine (closure_minimal (fun g hg => ?_) (isClosed_tsupport F)).trans hOP
    by_contra hgF
    exact hg.2 (rdsp_rw_vanish F T.word g hgF)
  have hB1s : B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) := Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC.ckOn_opAdj D Θ hS hF hsuppF
  refine ⟨⟨hA1s, hFc.of_isClosed_subset (isClosed_tsupport _) hA1t, hA1t⟩,
    ⟨hB1s, hFc.of_isClosed_subset (isClosed_tsupport _) hB1t, hB1t⟩, ?_⟩

  have hpos : ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ tsupport F, ε ≤ Formalism.QuantumDeterminants.Gf k r D.z D.z' g := by
    rcases (tsupport F).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨g₀, hg₀, hmin⟩ := hFc.exists_isMinOn h (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont D.z D.z').continuousOn
      exact ⟨_, (hFO hg₀).2.2, fun g hg => isMinOn_iff.mp hmin g hg⟩
  obtain ⟨ε, hε, hεG⟩ := hpos
  have hCk : B.CkOn ⊤ (JF.Om k r D.z D.z') (B.JF D F) :=
    (radial_orbital_niceness k r Wp Wq D F ⟨ε, hε, hF, fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hF hFc
      (fun g _ hg => image_eq_zero_of_notMem_tsupport hg) A m,
      fun g _ hg => hεG g (subset_tsupport F hg)⟩).2
  have hIn := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hF hFc (fun g _ hg => image_eq_zero_of_notMem_tsupport hg)
    (6 * (r : ℝ) * (B.opOrder Θ : ℝ) + (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ)) * (6 * (r : ℝ) + 1) + 1) (B.opOrder Θ)
  obtain ⟨hT1, hT2⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.LT.thetaJ_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds k r Wp Wq D Θ _ F
    (JF.Om k r D.z D.z') (Formalism.FourierDecayAlt.P.CutMP.JA.SA.thrW_sa k r (B.opOrder Θ)) hS hC hF hIn subset_rfl
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hCk)
  exact fun g hg => ⟨hT1 g hg, hT2 g hg⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSRhvR
section
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

namespace RhvRPf

open RhRPf

theorem pbOp_loc {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r)
    {f₁ f₂ : (Fin r → ℂ) → E} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    pbOp l f₁ c = pbOp l f₂ c := by
  have hev : f₁ =ᶠ[nhds c] f₂ := by
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using h c' hc'
  simp only [pbOp, wirtBar, if_pos hc, hev.fderiv_eq]

theorem vABs_loc {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) :
    ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
      ∀ c ∈ OmX r, (vABs r Y i).1 f₁ c = (vABs r Y i).1 f₂ c ∧ (vABs r Y i).2 f₁ c = (vABs r Y i).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | i + 1, f₁, f₂, h, c, hc => by
    by_cases hi : i < r
    · simp only [vABs, dif_pos hi]
      have hsub : ∀ c' ∈ OmX r, (Y • f₁ - pbOp ⟨i, hi⟩ f₁) c' = (Y • f₂ - pbOp ⟨i, hi⟩ f₂) c' := by
        intro c' hc'
        simp only [Pi.sub_apply, Pi.smul_apply]
        rw [h c' hc', pbOp_loc _ h hc']
      have hcb : ∀ c' ∈ OmX r, cbOp ⟨i, hi⟩ f₁ c' = cbOp ⟨i, hi⟩ f₂ c' := by
        intro c' hc'
        simp only [cbOp]
        rw [h c' hc']
      have hcbi : ∀ c' ∈ OmX r, cbiOp ⟨i, hi⟩ f₁ c' = cbiOp ⟨i, hi⟩ f₂ c' := by
        intro c' hc'
        simp only [cbiOp]
        rw [h c' hc']
      refine ⟨?_, ?_⟩
      · simp only [Pi.sub_apply]
        rw [(vABs_loc Y i _ _ hsub c hc).1, (vABs_loc Y i _ _ hcb c hc).2]
      · exact (vABs_loc Y i _ _ hcbi c hc).1
    · simp only [vABs, dif_neg hi]
      exact vABs_loc Y i f₁ f₂ h c hc

def rowP {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : R.LevelData A r) (Y : ℂ) (n : ℕ) :
    Matrix (Fin 2) (Fin 2) A :=
  ((List.ofFn fun l => (L.Tvl Y l)ᵀ).take n).prod

theorem partialProduct_succ {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : R.LevelData A r) (Y : ℂ) (n : ℕ) (h : n < r) :
    rowP L Y (n + 1) = rowP L Y n * (L.Tvl Y ⟨n, h⟩)ᵀ := by
  unfold rowP
  rw [List.take_add_one, List.prod_append]
  have e : (List.ofFn fun l => (L.Tvl Y l)ᵀ)[n]? = some ((L.Tvl Y ⟨n, h⟩)ᵀ) := by simp [h]
  rw [e]
  simp

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rowSide_chain (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (Y : ℂ) :
    ∀ n, n ≤ r → ∀ (Ψ : RadSp k r z z' π π'), ∀ x ∈ DomR k r z z',
      (((rowP L Y n 0 0).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          crd (vABs r Y n).1 (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 ∧
        (((rowP L Y n 0 1).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          crd (vABs r Y n).2 (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2
  | 0, _, Ψ, x, _ => by
    have e : rowP L Y 0 = 1 := by simp [rowP]
    rw [e]
    refine ⟨rfl, ?_⟩
    simp [vABs, crd]
    rfl
  | n + 1, hn, Ψ, x, hx => by
    have h : n < r := by omega
    have ih := rowSide_chain X L hL Y n (by omega)
    have ev : vABs (E := Wq →L[ℂ] Wp) r Y (n + 1) =
        (fun f => (vABs r Y n).1 (Y • f - pbOp ⟨n, h⟩ f) - (vABs r Y n).2 (cbOp ⟨n, h⟩ f),
          fun f => (vABs r Y n).1 (cbiOp ⟨n, h⟩ f)) := by
      show (if h : n < r then _ else _) = _
      rw [dif_pos h]
    have e00 : rowP L Y (n + 1) 0 0 =
        rowP L Y n 0 0 * (algebraMap ℂ _ Y - L.pb ⟨n, h⟩) + rowP L Y n 0 1 * (-L.cb ⟨n, h⟩) := by
      rw [partialProduct_succ L Y n h]
      simp [Matrix.mul_apply, Fin.sum_univ_two, R.LevelData.Tvl]
    have e01 : rowP L Y (n + 1) 0 1 = rowP L Y n 0 0 * L.cbi ⟨n, h⟩ := by
      rw [partialProduct_succ L Y n h]
      simp [Matrix.mul_apply, Fin.sum_univ_two, R.LevelData.Tvl]
    have hpb : JCx2.rma_fst _ (L.pb ⟨n, h⟩) = X.op ⟨n, h⟩ 3 := by rw [hL.2.1]; rfl
    have hcb : JCx2.rma_fst _ (L.cb ⟨n, h⟩) = X.op ⟨n, h⟩ 4 := by rw [hL.2.2.2.2.1]; rfl
    have hcbi : (L.cbi ⟨n, h⟩).1 = X.op ⟨n, h⟩ 5 := by rw [hL.2.2.2.2.2.1]; rfl
    refine ⟨?_, ?_⟩
    · have h1 : (((rowP L Y (n + 1) 0 0).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (((rowP L Y n 0 0).1 (Y • Ψ - X.op ⟨n, h⟩ 3 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 -
            (((rowP L Y n 0 1).1 (X.op ⟨n, h⟩ 4 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 := by
        change (JCx2.rma_fst _ (rowP L Y (n + 1) 0 0) Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
        rw [e00]
        simp only [map_add, map_mul, map_sub, map_neg, AlgHom.commutes, LinearMap.add_apply,
          LinearMap.sub_apply, LinearMap.neg_apply, mul_apply_eq_comp, Module.algebraMap_end_apply,
          hpb, hcb, ← sub_eq_add_neg, Submodule.coe_sub, Pi.sub_apply]
        rfl
      rw [h1, (ih _ x hx).1, (ih _ x hx).2, ev]
      simp only [Submodule.coe_sub, Submodule.coe_smul, X.op_apply]
      rfl
    · have h1 : (((rowP L Y (n + 1) 0 1).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (((rowP L Y n 0 0).1 (X.op ⟨n, h⟩ 5 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 := by
        rw [e01, fst_mul_apply, hcbi]
      rw [h1, (ih _ x hx).1, ev]
      simp only [X.op_apply]
      rfl

end RhvRPf

open RhRPf RhvRPf in
theorem spectral_adjoint_rho_action : RDSRhvR := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD hl1 hl2 hr Y hY
  obtain ⟨_, _, hL, hQQ, -⟩ := hD
  refine ⟨M.sgn P l0, ?_⟩
  intro J hJ Φ hΦ x hx
  have hT : (L.Tvprod Y)ᵀ = rowP L Y P.r := by
    rw [Formalism.FourierDecayAlt.P.MAx3.Q.Tvprod_transpose L Y, rowP, List.take_of_length_le (by simp)]
  have eA : L.Avr Y = rowP L Y P.r 0 0 := by rw [← hT]; rfl
  have eB : L.Bvr Y = rowP L Y P.r 0 1 := by rw [← hT]; rfl
  have hch := rowSide_chain X L hL Y P.r le_rfl
  have hA : ∀ y ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx8.Dp P.k P.r z z',
      (((L.Avr Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y =
        crd (Q.cmp (vABs P.r Y P.r) 0) (resG P.k P.r (Fin.last P.r) J) x.1 y := by
    intro y hy
    have hxy : (x.1, y) ∈ DomR P.k P.r z z' := ⟨hx.1, hy.1, hy.2⟩
    rw [eA, (hch Φ (x.1, y) hxy).1]
    simp only [crd, Q.cmp, if_true]
    exact (vABs_loc Y P.r _ _ (fun c' hc' => hΦ (c', y) ⟨hc', hy.1, hy.2⟩) x.1 hx.1).1
  have hB : ∀ y ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx8.Dp P.k P.r z z',
      (((L.Bvr Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y =
        crd (Q.cmp (vABs P.r Y P.r) 1) (resG P.k P.r (Fin.last P.r) J) x.1 y := by
    intro y hy
    have hxy : (x.1, y) ∈ DomR P.k P.r z z' := ⟨hx.1, hy.1, hy.2⟩
    rw [eB, (hch Φ (x.1, y) hxy).2]
    simp only [crd, Q.cmp, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
    exact (vABs_loc Y P.r _ _ (fun c' hc' => hΦ (c', y) ⟨hc', hy.1, hy.2⟩) x.1 hx.1).2
  have e1 : (((RhvR L st Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      (((L.Dr).1 ((st.QQ Y 0 1).1 ((L.Avr Y).1 Φ) + (st.QQ Y 1 1).1 ((L.Bvr Y).1 Φ)) :
        RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := rfl
  rw [e1, dr_apply X L hL, st_fst X st l0 hQQ, st_fst X st l0 hQQ]
  simp only [CutMP.dMul, CutMP.rhvGrp, Submodule.coe_add, Pi.add_apply, LinearMap.smul_apply,
    Submodule.coe_smul, Pi.smul_apply, QL, grp]
  rw [X.t_apply Y 0 1 _ x hx, X.t_apply Y 1 1 _ x hx,
    t_slice_congr X Y 0 1 _ _ x hx hA, t_slice_congr X Y 1 1 _ _ x hx hB]
  simp only [smul_add, smul_comm (CutMP.drF P.r x.1) (M.sgn P l0)]

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbBuiltBounds2CptOfMkTop
section
namespace Formalism.FourierDecayAlt.P

theorem pb_builtBounds2Cpt_of_mkTop (hM : CutEX.MkTop) : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt :=
  built_bounds_compact_of_head_top (pb_headTop_of_mkTop hM)

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion
section
namespace Formalism.FourierDecayAlt.P

theorem head_top : KB.HeadTop := pb_headTop_of_mkTop top_truncation_of_averages

end Formalism.FourierDecayAlt.P
end

