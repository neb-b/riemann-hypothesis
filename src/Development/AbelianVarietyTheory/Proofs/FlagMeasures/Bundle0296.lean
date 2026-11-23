module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0039
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelLinearMapMatrixExists
section
noncomputable section
open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.TypeAsm.GramPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D}

theorem crd_map_mulVec (m : (VS D).V →ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    X.crd (m y) = (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i) *ᵥ X.crd y := by
  unfold Formalism.L2.SG.Pf.toV HidaSetting.crd crdOf
  have hb : ∀ j : Fin X.B.I.n, (∑ i, X.ιE ((Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) i) • X.bas i) = X.bas j := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [Pi.single_apply, hbj]
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [hb]
  funext i
  conv_lhs => rw [← X.bas.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Matrix.of_apply, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem phiV_linMat (C : Choice X 1) (τ : D.what₂.Tau) (m : (VS D).V →ₗ[D.host.E] (VS D).V) :
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  obtain ⟨-, hQ, -⟩ := C.isT τ
  refine ⟨C.Qi τ * (X.B.I.P (vOf X τ))⁻¹ *
      (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map (X.B.I.φ (vOf X τ)) *
      X.B.I.P (vOf X τ) * C.Q τ, fun y => ?_⟩
  have hP : (X.B.I.P (vOf X τ))⁻¹ * ((Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map
      (X.B.I.φ (vOf X τ)) * (X.B.I.P (vOf X τ) * (X.B.I.P (vOf X τ))⁻¹)) =
      (X.B.I.P (vOf X τ))⁻¹ * (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map
      (X.B.I.φ (vOf X τ)) := by
    by_cases h : IsUnit (X.B.I.P (vOf X τ)).det
    · rw [Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.zero_mul, Matrix.zero_mul]
  have hw : (fun i => X.B.I.φ (vOf X τ) (X.crd (m y) i)) =
      (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map (X.B.I.φ (vOf X τ)) *ᵥ
        (fun i => X.B.I.φ (vOf X τ) (X.crd y i)) := by
    rw [crd_map_mulVec m y]
    funext i
    exact RingHom.map_mulVec _ _ _ i
  have e1 : ∀ z, GlobalTheory.TypeAsm.phiV C τ z =
      (C.Qi τ * (X.B.I.P (vOf X τ))⁻¹) *ᵥ (fun i => X.B.I.φ (vOf X τ) (X.crd z i)) := by
    intro z
    unfold GlobalTheory.TypeAsm.phiV Formalism.L2.SG.HidaSetting.rv
    rw [Matrix.mulVec_mulVec]
  rw [e1, e1, hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul, hP]

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm

theorem phiV_linMat_all : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau)
    (m : (VS D).V →ₗ[D.host.E] (VS D).V),
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  intro D X C τ m
  exact GramPf.phiV_linMat C τ m

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColsSharpDictionary
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St

section Abstract

open Formalism.L2.SG.ColsDim

theorem cols_sharp_abstract {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (ιi : Γ →* Gi) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (ψ : K →* ℂˣ) (π : Representation ℂ Gi V)
    (hπ : ∀ h : Gi, ∀ v w : V, ⟪π h v, π h w⟫_ℂ = ⟪v, w⟫_ℂ)
    (hψ : ∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1)
    (sh : (V →ₗ[ℂ] (Gi × Gf → ℂ)) → Gf → V)
    (hsh : ∀ (T : V →ₗ[ℂ] (Gi × Gf → ℂ)) (x : Gf) (ξ : V), ⟪sh T x, ξ⟫_ℂ = T ξ (1, x)) :
    (∀ (T : Cols ℂ ιi ιf K ψ π) (γ : Γ) (x : Gf) (κ : K),
      sh T.1 (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (sh T.1 x)) ∧
    (∀ T : Cols ℂ ιi ιf K ψ π, (∀ x, sh T.1 x = 0) → T = 0) ∧
    ∀ φ : Gf → V, (∀ (γ : Γ) (x : Gf) (κ : K),
      φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) →
      ∃ T : Cols ℂ ιi ιf K ψ π, ∀ x, sh T.1 x = φ x := by
  obtain ⟨e, he, hsm⟩ := sharp_bijective Γ Gi Gf V ιi ιf K ψ π hπ hψ
  have key : ∀ (T : Cols ℂ ιi ιf K ψ π) (x : Gf), sh T.1 x = (e T).1 x := fun T x =>
    ext_inner_right ℂ fun ξ => by
      rw [hsh]
      exact he T x ξ
  refine ⟨?_, ?_, ?_⟩
  · intro T γ x κ
    rw [key, key]
    exact (e T).2 γ x κ
  · intro T hT
    have h0 : e T = e ((0 : ℂ) • T) := by
      apply Subtype.ext
      rw [hsm]
      funext x
      rw [← key, hT x]
      simp
    have := e.injective h0
    rw [this]
    simp
  · intro φ hφ
    refine ⟨e.symm ⟨φ, hφ⟩, fun x => ?_⟩
    rw [key, Equiv.apply_symm_apply]

end Abstract

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cols_sharp_dictionary :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), (∀ κ : Ku X u hK, ‖((psiK X u hK κ : ℂˣ) : ℂ)‖ = 1) ∧ (∀ (h : Hinf X u) (v w : X.Vpi u), ⟪piRep X u h v, piRep X u h w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ (T : Cu X u hK) (γ : Gam X u) (x : Hfin X u) (κ : Ku X u hK), shP X u T.1 (iotaF X u γ * x * κ) = (((psiK X u hK κ)⁻¹ : ℂˣ) : ℂ) • piRep X u (iotaI X u γ) (shP X u T.1 x)) ∧ (∀ T : Cu X u hK, (∀ x, shP X u T.1 x = 0) → T = 0) ∧ ∀ φ : Hfin X u → X.Vpi u, (∀ (γ : Gam X u) (x : Hfin X u) (κ : Ku X u hK), φ (iotaF X u γ * x * κ) = (((psiK X u hK κ)⁻¹ : ℂˣ) : ℂ) • piRep X u (iotaI X u γ) (φ x)) → ∃ T : Cu X u hK, ∀ x, shP X u T.1 x = φ x := by
  intro D X u hK
  have hψ : ∀ κ : Ku X u hK, ‖((psiK X u hK κ : ℂˣ) : ℂ)‖ = 1 := fun κ => hK.2.2.2.2 _ κ.2
  have hπ : ∀ (h : Hinf X u) (v w : X.Vpi u), ⟪piRep X u h v, piRep X u h w⟫_ℂ = ⟪v, w⟫_ℂ :=
    fun h v w => (X.piU_rep u).2.2.1 _ (hinf_le_sinf X u _ h.2) v w
  exact ⟨hψ, hπ, cols_sharp_abstract (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) (piRep X u) hπ hψ
    (shP X u) (inner_shP X u)⟩

end GlobalTheory.St

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St

variable {D : D7}

theorem hspace_gram_det_ne {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : S.frame.equivFun.symm v = 0 := by
    refine S.nondeg.2 _ fun x => ?_
    have hx : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := fun i => by
      have := congrFun h0 i
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    rw [← S.frame.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_zero,
      Finset.sum_const_zero]
  exact (LinearEquiv.map_eq_zero_iff _).1 this

theorem hform_crd_setting (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w)) = (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, HidaSetting.crd, crdOf, starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply,
    X.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem gram_entry {A : Type} [CommRing A] {n ι : Type} [Fintype n] (σ : A →+* A) (Q : Matrix n ι A)
    (J : Matrix n n A) (k l : ι) :
    ((Q.map σ)ᵀ * J * Q) k l = Formalism.UG.hform σ J (fun i => Q i k) (fun i => Q i l) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Formalism.UG.hform, Finset.sum_mul]
  exact Finset.sum_comm

def famQ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) → (VS D).V :=
  Sum.elim (qFr wt) (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u))

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem hT_symm_zero {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [← (VS D).herm.eq x y, h, map_zero]

theorem hT_wt_symm (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : ∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y)
    (x y : (VS D).V) : (VS D).hT (wt.symm x) y = (VS D).hT x (wt y) := by
  rw [← hiso, LinearEquiv.apply_symm_apply]

theorem hT_qFr_qFr (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : ∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y)
    (a b : Fin (D.R.N 0)) : (VS D).hT (qFr wt a) (qFr wt b) = Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) a b := by
  rw [qFr, hT_wt_symm wt hiso, qFr, LinearEquiv.apply_symm_apply, xFr, xFr,
    D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)]
  rfl

theorem hT_qFr_rest (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hw : WittX X u wt)
    (a : Fin (D.R.N 0)) (k : Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) :
    (VS D).hT (qFr wt a) (famQ X u wt (Sum.inr k)) = 0 := by
  obtain ⟨hiso, he, hf, hz⟩ := hw
  rw [qFr, hT_wt_symm wt hiso]
  rcases k with b | b | b
  · simp only [famQ, Sum.elim_inr, Sum.elim_inl, he]; exact (D.sp.hyp_orthX b _).1
  · simp only [famQ, Sum.elim_inr, Sum.elim_inl, hf]; exact (D.sp.hyp_orthX b _).2
  · simp only [famQ, Sum.elim_inr, hz, Formalism.BasicNotions.D7.zmOf, LinearMap.map_smul]
    rw [xFr, D.sp.zm_orth, smul_zero]

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem hT_fe (X : HidaSetting D) (a b : Fin D.R.rS) :
    (VS D).hT (X.fY a) (X.eX b) = if b = a then 1 else 0 := by
  rw [← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
  split_ifs <;> simp

theorem hT_ze (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS) : (VS D).hT (X.zu u) (X.eX b) = 0 :=
  hT_symm_zero (X.zu_orth u b).1

theorem hT_zf (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS) : (VS D).hT (X.zu u) (X.fY b) = 0 :=
  hT_symm_zero (X.zu_orth u b).2

theorem hT_zz_ne (X : HidaSetting D) (u : D.what₂.Word) : (VS D).hT (X.zu u) (X.zu u) ≠ 0 := by
  rw [X.zu_norm, neg_ne_zero, Nat.cast_ne_zero]
  exact ((D.mem u).A.T_prime).ne_zero

def gramR (X : HidaSetting D) (u : D.what₂.Word) :
    Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E :=
  Matrix.of fun k l => X.ιE.symm ((VS D).hT (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u) k)
    (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u) l))

def gramRinv (X : HidaSetting D) (u : D.what₂.Word) :
    Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E :=
  Matrix.of fun k l => match k, l with
    | Sum.inl a, Sum.inr (Sum.inl b) => if a = b then 1 else 0
    | Sum.inr (Sum.inl a), Sum.inl b => if a = b then 1 else 0
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => (X.ιE.symm ((VS D).hT (X.zu u) (X.zu u)))⁻¹
    | _, _ => 0

theorem gramR_mul_inv (X : HidaSetting D) (u : D.what₂.Word) : gramR X u * gramRinv X u = 1 := by
  have ht : X.ιE.symm ((VS D).hT (X.zu u) (X.zu u)) ≠ 0 := by
    rw [Ne, RingEquiv.map_eq_zero_iff]; exact hT_zz_ne X u
  ext (a | a | a) (b | b | b) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, gramR, gramRinv, X.ee, X.ff, X.ef, hT_fe, hT_ze, hT_zf,
      X.zu_orth, Matrix.one_apply, ht, eq_comm]

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem qFrame_basis_gram : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ (Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E) (Qi : Matrix (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) (Fin X.B.I.n) X.B.I.E) (G' : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E), Q * Qi = 1 ∧ Qi * Q = 1 ∧ (∀ j i, Q i (Sum.inl j) = X.crd (qFr wt j) i) ∧ (∀ a i, Q i (Sum.inr (Sum.inl a)) = X.eR a i) ∧ (∀ a i, Q i (Sum.inr (Sum.inr (Sum.inl a))) = X.fR a i) ∧ (∀ i, Q i (Sum.inr (Sum.inr (Sum.inr ()))) = X.zR u i) ∧ IsUnit G'.det ∧ (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q = Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 G' := by
  intro D X u wt hw
  classical
  let Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E :=
    Matrix.of fun i k => X.crd (famQ X u wt k) i
  have hiso := hw.1

  have hM : (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q =
      Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 (gramR X u) := by
    ext k l
    rw [gram_entry]
    apply X.ιE.injective
    rw [show (fun i => Q i k) = X.crd (famQ X u wt k) from rfl, show (fun i => Q i l) = X.crd (famQ X u wt l) from rfl,
      hform_crd_setting]
    rcases k with a | k <;> rcases l with b | l
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.map_apply, RingEquiv.apply_symm_apply]
      exact hT_qFr_qFr wt hiso a b
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, map_zero]
      exact hT_qFr_rest X u wt hw a l
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, map_zero]
      exact hT_symm_zero (hT_qFr_rest X u wt hw b k)
    · simp only [Matrix.fromBlocks_apply₂₂, gramR, Matrix.of_apply, RingEquiv.apply_symm_apply]
      rfl

  have hA : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det ≠ 0 := by
    have h1 : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det =
        X.ιE.symm.toRingHom (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det := by
      rw [RingHom.map_det]; rfl
    rw [h1]
    refine (map_ne_zero _).2 ?_
    unfold Formalism.L2.Forms.gramN
    rw [Matrix.det_reindex_self]
    exact hspace_gram_det_ne _
  have hG : IsUnit (gramR X u).det := Matrix.isUnit_det_of_right_inverse (gramR_mul_inv X u)
  have hMu : IsUnit ((Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q).det := by
    rw [hM, Matrix.det_fromBlocks_zero₂₁]
    exact (isUnit_iff_ne_zero.2 hA).mul hG

  have hcard : Fintype.card (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) = X.B.I.n := by
    rw [X.n_eq, ← dimS_eq, Formalism.BasicNotions.Ranks.N_zero]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  let σ := Fintype.equivFinOfCardEq hcard
  let P := Q.submatrix σ id
  have hQ : Q = P.submatrix σ.symm id := by
    ext i k; simp [P]
  have hconj : (Q.map (starRingEnd X.B.I.E))ᵀ = Qᴴ := by
    ext i k
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
    exact starRingEnd_apply _
  have hPJ : (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q = Pᴴ * X.B.I.J.submatrix σ σ * P := by
    have hJ : X.B.I.J = (X.B.I.J.submatrix σ σ).submatrix σ.symm σ.symm := by
      simp [Matrix.submatrix_submatrix]
    rw [hconj, hQ, Matrix.conjTranspose_submatrix]
    conv_lhs => rw [hJ]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hP : IsUnit P.det := by
    rw [hPJ, Matrix.det_mul, Matrix.det_mul] at hMu
    exact isUnit_of_mul_isUnit_right hMu
  refine ⟨Q, (P⁻¹).submatrix id σ.symm, gramR X u, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, hG, hM⟩
  · rw [hQ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_nonsing_inv _ hP,
      Matrix.submatrix_one_equiv]
  · rw [hQ, Matrix.submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hP, Matrix.submatrix_id_id]

end GlobalTheory.St
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousDensitySelfDualLatticeIndicatorAtUnit
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.LatticeContDensity

theorem contDensity_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v → ∀ ψ : AddChar (Fv F v) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsLocalChar v ψ → ∀ n : ℤ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.DualExponent v ψ n → ∀ L : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin M → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v L → ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), SdW F E σ M J (Fv F v) ψ 1 μ → SdR (Fv F v) ψ ν → ∀ g : Fv F v → ℂ, IsContDensityOn μ (fun X => qR (Fv F v) σ J (X 0)) id ν {c | c ≠ 0} ({X | X 0 ∈ L}.indicator 1) g → ∀ β : Fv F v, Valued.v β = 1 → g β = (((GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ n) ^ ((1 / 2 : ℝ) - (M : ℝ)) * (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹) : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ hσ M hM J hJ v hv ψ hψ n hn L hL μ ν hμ hν g hg β hβ

  have H : GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.SelfDualLatticeDensity :=
    GlobalTheory.LocalDensityCompare.localDensity_iff.1
      (GlobalTheory.LatticeDensity.localDensity_of_selfDualLatticeLemmas
        GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas)
  obtain ⟨η, hη⟩ := GlobalTheory.LocalDensityCompare.exists_eta F E v
  have hEta : GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.IsEtaAt F E v η :=
    (GlobalTheory.LocalDensityCompare.isEtaAt_iff F E v hσ.2.2.1 η).2 ⟨hv, hη⟩
  have key := (H F E σ hσ M J hM hJ v η hEta ψ hψ).2 n hn L
    ((GlobalTheory.LocalDensityCompare.isSelfDualLattice_iff v σ J L).1 hL) μ hμ ν hν

  have hβ' : Valued.v (β - β) < 1 := by simp
  have hgβ := (key.2.2 β hβ).2 g hg β hβ'
  rw [hgβ, ← GlobalTheory.LocalDensityCompare.dens_eq v n M η hη]

end GlobalTheory.LatticeContDensity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousRepresentativeProperties
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.ContRepUniq

theorem lintegral_enorm_sq_eq {X : Type} [MeasurableSpace X] (μ : Measure X) (F : Lp ℂ 2 μ) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (‖F‖ ^ 2) := by
  rw [Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top (Lp.aestronglyMeasurable F)]
  have h2 : ((2 : ENNReal).toReal) = 2 := by norm_num
  simp only [h2, ← ENNReal.rpow_two]
  rw [← ENNReal.rpow_mul]
  norm_num

theorem contRep_unique_linear : ∀ (B : RowsAut), (∀ F f f', IsContRep B F f → IsContRep B F f' → f = f') ∧ (∀ F F' f f' (c : ℂ), IsContRep B F f → IsContRep B F' f' → IsContRep B (F + c • F') (fun x => f x + c * f' x)) ∧ (∀ F f g, IsContRep B F f → IsContRep B (B.R g F) (fun x => f (x * g))) ∧ ∀ F f, IsContRep B F f → f =ᵐ[B.I.muA B.μf] B.I.ext F ∧ ∫⁻ x in B.fund, ‖f x‖ₑ ^ 2 ∂(B.I.muA B.μf) = ENNReal.ofReal (‖F‖ ^ 2) := by
  intro B
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F f f' hf hf'
    exact ((GlobalTheory.ExtContRep.ext_ae_eq_contRep B F f hf).2.1 f' hf').symm
  · intro F F' f f' c hf hf'
    refine ⟨hf.1.add (continuous_const.mul hf'.1), ?_, ?_⟩
    · intro γ hγ x
      show f (γ * x) + c * f' (γ * x) = f x + c * f' x
      rw [hf.2.1 γ hγ x, hf'.2.1 γ hγ x]
    · filter_upwards [Lp.coeFn_add F (c • F'), Lp.coeFn_smul c F', hf.2.2, hf'.2.2]
        with x h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, h3, h4]
  · intro F f g hf
    exact (GlobalTheory.ExtContRep.ext_ae_eq_contRep B F f hf).2.2.1 g
  · intro F f hf
    refine ⟨(GlobalTheory.ExtContRep.ext_ae_eq_contRep B F f hf).1.symm, ?_⟩
    refine Eq.trans ?_ (lintegral_enorm_sq_eq ((B.I.muA B.μf).restrict B.fund) F)
    refine lintegral_congr_ae ?_
    filter_upwards [hf.2.2] with x hx
    rw [hx]

end GlobalTheory.ContRepUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeSelfDualIsFullRank
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem coordLat_isLat (D : D7) (X : HidaSetting D) :
    IsLat ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by
  have hcomb : ∀ x : Fin _ → D.host.E,
      Fintype.linearCombination D.host.E X.bas x = X.bas.equivFun.symm x := by
    intro x
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
  have heq : (VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E)) =
      (VS D).L0.map (X.bas.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap := by
    ext x
    simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, hcomb, Submodule.mem_map,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
    constructor
    · intro hx
      exact ⟨_, hx, X.bas.equivFun.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [heq]
  refine ⟨Module.Finite.iff_fg.2 ((VS D).standardTuple_isLattice.fg.map _), ?_⟩
  have : ((VS D).L0.map (X.bas.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap : Set (Fin _ → D.host.E)) =
      X.bas.equivFun.toLinearMap '' ((VS D).L0 : Set (VS D).V) := rfl
  have hspan : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) = ⊤ := by
    let V := VS D
    let W := Submodule.span D.host.E (V.L0 : Set V.V)
    change W = ⊤
    by_contra h
    let e : V.V ≃ₗ⋆[D.host.E] V.V :=
      (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
    let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
      (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
        Module.finrank D.host.E V.V := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
      rw [← V.baseLattice_isUnimodular]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
        Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      intro y hy
      have hzy : V.hT (e z) y = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hz)
      have hyz : V.hT y (e z) = 0 := by
        have hh := V.herm.eq (e z) y
        simpa [hzy] using hh.symm
      simp [hyz]
    let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
      ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
    let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
    let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
  rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.St.G
end

