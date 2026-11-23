module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0308
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnTupleStepZeroReadByMemberLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnTuple_stepZero_read_by_memberLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), ReadsOne I l Z u a 0 (Nat.zero_le _) (fun _ => ()) K0 ∧ (∀ β, (K0 β).lev.Lb = F.to0.cls0.lev.Lb ∧ (K0 β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ (K0 β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : (K0 β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → (K0 β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, ((K0 ((fun _ : (I.stp u a 0).Cl => ()) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  exact @GlobalTheory.TwU.AtTrue.StepZeroRead.reads
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownLiftUpLiftPositiveScalarUsedTuples
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.NRows.LamUsedProof

theorem main : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → GlobalTheory.NRows.LamUsed D := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hD μ hU0 i σ
  have hU : Used0 D μ := hU0
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨_, Y.tupTie μ hU⟩
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  by_cases hne : D.what₂.isot ((i : ℕ) + 1) σ = ⊥
  · refine ⟨fun f hf => ?_, fun h => absurd hne h⟩
    rw [hne, Submodule.mem_bot] at hf
    subst hf
    simp
  obtain ⟨p, hL⟩ := GlobalTheory.Mem.R3.LabProof.hasLab_exists h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD σ
  set c : ℝ := R.lam3 i t p A3.A.v0 with hc

  have hpre : ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, ∃ x ∈ (LinearMap.ker θ)ᗮ, θ x = y ∧
      ∀ x', ⟪θ x, θ x'⟫_ℂ = (c : ℂ) * ⟪x, x'⟫_ℂ := by
    intro y hy
    obtain ⟨x, rfl⟩ := GlobalTheory.T.liftThetaMap_surjective_onto_cuspForms_usedTuple h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t hU y
    set K := (LinearMap.ker θ)ᗮ
    have hx0 : x - K.starProjection x ∈ LinearMap.ker θ := by
      have := K.sub_starProjection_mem_orthogonal x
      rwa [Submodule.orthogonal_orthogonal] at this
    have he : θ (K.starProjection x) = θ x := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hx0; exact hx0.symm
    have hW : Y.mj.eW i (θ (K.starProjection x)) ∈ R.Wp3 i p := by
      rw [he]; exact hL.1 i ⟨θ x, hy, rfl⟩
    exact ⟨K.starProjection x, K.starProjection_apply_mem x, he,
      GlobalTheory.T.liftThetaMap_inner_eq_lambda_labelPart_baseLevel h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t p hU (K.starProjection x)
        (K.starProjection_apply_mem x) hW⟩

  have heig : ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ,
      D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.thetaT (Y.tup t) ((i : ℕ) + 1) y) = ((c : ℝ) : ℂ) • y := by
    intro y hy
    obtain ⟨x, -, rfl, hx⟩ := hpre y hy
    have ha : LinearMap.adjoint θ (θ x) = (c : ℂ) • x := by
      refine ext_inner_right ℂ fun x' => ?_
      rw [LinearMap.adjoint_inner_left, hx, inner_smul_left, Complex.conj_ofReal]
    show θ (LinearMap.adjoint θ (θ x)) = (c : ℂ) • θ x
    rw [ha, map_smul]
  have hlam : D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = c := Y.tied.lift.lamP (Y.tup t) hU i σ c hne heig
  refine ⟨fun f hf => by rw [hlam]; exact heig f hf, fun _ => ?_⟩
  rw [hlam]
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨x, -, rfl, hx⟩ := hpre y hy
  have h := hx x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hyn : 0 < ‖θ x‖ := norm_pos_iff.2 hy0
  have h' : ‖θ x‖ ^ 2 = c * ‖x‖ ^ 2 := by
    have h2 : ((‖θ x‖ ^ 2 : ℝ) : ℂ) = ((c * ‖x‖ ^ 2 : ℝ) : ℂ) := by
      first | (push_cast; exact h) | (push_cast; simpa using h) | (simp only [RCLike.ofReal_pow, Complex.ofReal_pow, Complex.ofReal_mul] at h ⊢; exact h) | (rw [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_pow]; exact h)
    exact Complex.ofReal_injective h2
  by_contra hcn
  push_neg at hcn
  nlinarith [sq_nonneg ‖x‖, sq_pos_of_pos hyn]

end GlobalTheory.NRows.LamUsedProof
end

