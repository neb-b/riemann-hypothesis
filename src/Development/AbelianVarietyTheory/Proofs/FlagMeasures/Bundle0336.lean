module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsType
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CapelliOfHC

open PI.UpqRep PI.HwUniqW GlobalTheory.BesselFrame GlobalTheory.SupNonzero

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

private theorem conj_blockW_exp_eq_exp_unitB {g : Mx k r} (hg : IsFrameW k r z g) (Z : Matrix (Fin k) (Fin k) ℂ) (t : ℝ) :
    g * blockW k r (NormedSpace.exp ((t : ℂ) • Z)) * g⁻¹ = NormedSpace.exp ((t : ℂ) •
      ∑ a, ∑ b, Z a b • Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b) := by
  have hunit : IsUnit g := by
    have hgg := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_eq ▸ hg.1)).2
    exact ⟨⟨g, g⁻¹, hgg.1, hgg.2⟩, rfl⟩
  have hs : ∀ a b : Fin k, Matrix.single a b (Z a b) = Z a b • Matrix.single a b (1 : ℂ) := fun a b => by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have hu : ∀ a b : Fin k, Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b =
      g * incl k r * Matrix.single a b (1 : ℂ) * ((incl k r)ᴴ * g⁻¹) := fun a b => by
    rw [unitB_eq, co_eq hg.1]
  rw [blockW_eq, ← exp_corner (incl k r) (incl k r)ᴴ incl_incl, ← Matrix.exp_conj g _ hunit]
  congr 1
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [hu, hs, Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, smul_smul]

theorem exists_eigen {u₀ : Fin k → ℝ} (hR : Qr.IsRepW k r z π) (h₀ : IsHCTypeW k r z u₀ π) :
    ∃ B : Fin k → (Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z] B ∧ ∃ v : W, v ≠ 0 ∧
      ∀ Y : ℂ, Formalism.REAL.qdet (Qr.EB π B) (Y + ((k : ℂ) - 1) / 2) v = (∏ s, (Y + (u₀ s : ℂ))) • v := by
  obtain ⟨g, hg, hU⟩ := h₀
  have hB : Q.IsFrameOf k r [z] (fun a => g *ᵥ bvec (bl k r a)) := isFrameOf hg
  refine ⟨fun a => g *ᵥ bvec (bl k r a), hB, ?_⟩
  have hgl := (Formalism.FourierDecayAlt.P.frame_general_linear W k r k z π _ hR hB).1
  refine qdet_eigen hU _ hgl ?_
  intro Z hZ v
  set X : Mx k r := ∑ a, ∑ b, Z a b • Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b with hXdef
  have hadj : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X := by
    simp only [hXdef, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.mul_sum, Finset.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, Formalism.FourierDecayAlt.P.QrCap.unitB_adj]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 := congrFun (congrFun hZ a) b
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h1
    rw [h1, neg_smul]
  have hX1 : Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) X = X := by
    rw [Formalism.QuantumDeterminants.hpart1, hadj, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
    norm_num
  have hX2 : Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) X = 0 := by
    rw [Formalism.QuantumDeterminants.hpart2, hadj, add_neg_cancel, smul_zero]
  have hsum := Formalism.FourierDecayAlt.P.HermitianFormSums.ec_sum Formalism.FourierDecayAlt.P.elementary_lie_elements hR (Finset.univ : Finset (Fin k × Fin k))
    (fun p => Z p.1 p.2) (fun p => Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) p.1 p.2)
    (fun p => Formalism.FourierDecayAlt.P.QrD.frame_lie hB p.1 p.2) 0 (Formalism.FourierDecayAlt.P.SkewHermitianParts.inGl_zero z)
  rw [← Finset.univ_product_univ, Finset.sum_product] at hsum
  have hXlie : Formalism.FourierDecayAlt.P.QrD.InLieW k r z X := by
    have h := hsum.1.1
    rwa [hX1] at h
  have hec : ∑ a, ∑ b, Z a b • Qr.EB π (fun a => g *ᵥ bvec (bl k r a)) a b v = Formalism.FourierDecayAlt.P.QrD.dOp π X v := by
    have h := hsum.2
    have h' : Formalism.FourierDecayAlt.P.QrD.ecOp π X = Formalism.FourierDecayAlt.P.QrD.dOp π X := by
      rw [Formalism.FourierDecayAlt.P.QrD.ecOp, hX1, hX2, Formalism.FourierDecayAlt.P.SkewHermitianParts.dOp_zero, smul_zero, add_zero]
    rw [h'] at h
    rw [h]
    simp only [Finset.sum_product, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    rfl
  have hexp : ∀ t : ℝ, g * blockW k r (NormedSpace.exp ((t : ℂ) • Z)) * g⁻¹ = NormedSpace.exp ((t : ℂ) • X) :=
    fun t => conj_blockW_exp_eq_exp_unitB hg Z t
  have hd := Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hR.1 hR.2 hXlie
  have hd' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (Formalism.FourierDecayAlt.P.QrD.dOp π X v) 0 := by
    have h2 := ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simpa [Function.comp_def] using h2
  rw [hec]
  convert hd' using 1
  funext t
  rw [hexp t]

theorem exists_isType : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u₀ : Fin k → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsHCTypeW k r z u₀ π → ∃ u : ℕ → ℝ, Q.IsType k r z π u := by
  intro k r Wp _ _ _ z π u₀ hz hT h₀
  obtain ⟨h1, hmul, hnorm, hcont⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT h₀
  have hR : Qr.IsRepW k r z π := ⟨⟨h1, hmul⟩, continuousOn_clm_apply.2 hcont⟩
  have ⟨g, hg, hU⟩ := h₀
  have hirr : ∀ S : Submodule ℂ Wp, (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    refine hU.2.2.2.2.2.1 S le_top ?_
    intro h hh v hv
    have hh' : hᴴ * h = 1 := by
      have := (Matrix.mem_unitaryGroup_iff').1 hh.1
      rwa [Matrix.star_eq_conjTranspose] at this
    exact hS _ (Formalism.FourierDecayAlt.P.QrCap.emb_uw hg.1 hg.2.1 _ hg.2.2 hh') v hv
  obtain ⟨B, hB, v0, hv0, heig⟩ := exists_eigen hR h₀
  have hgl := (Formalism.FourierDecayAlt.P.frame_general_linear Wp k r k z π B hR hB).1
  have key : ∀ (w : ℂ) (v : Wp), Formalism.REAL.qdet (Qr.EB π B) w v =
      (∏ s, (w - ((k : ℂ) - 1) / 2 + (u₀ s : ℂ))) • v := by
    intro w
    set c : ℂ := ∏ s, (w - ((k : ℂ) - 1) / 2 + (u₀ s : ℂ)) with hc
    set S : Submodule ℂ Wp := LinearMap.ker (Formalism.REAL.qdet (Qr.EB π B) w - c • (1 : Module.End ℂ Wp)) with hSdef
    have hmem : ∀ v, v ∈ S ↔ Formalism.REAL.qdet (Qr.EB π B) w v = c • v := fun v => by
      rw [hSdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    have hv0S : v0 ∈ S := by
      rw [hmem]
      have := heig (w - ((k : ℂ) - 1) / 2)
      rwa [sub_add_cancel] at this
    have hstab : Qr.Stab (Qr.EB π B) S := by
      intro a b v hv
      rw [hmem] at hv ⊢
      have hcomm := Formalism.REAL.qDetCentral (Module.End ℂ Wp) k (Qr.EB π B) hgl w a b
      have := congrArg (fun T : Module.End ℂ Wp => T v) hcomm
      simp only [Module.End.mul_apply] at this
      rw [this, hv, map_smul]
    have hUW := Formalism.FourierDecayAlt.P.lie_stabilizer Wp k r z π B hz hT hR hB S hstab
    rcases hirr S hUW with hbot | htop
    · exact absurd (by rw [hbot] at hv0S; exact (Submodule.mem_bot ℂ).1 hv0S) hv0
    · intro v
      exact (hmem v).1 (htop ▸ Submodule.mem_top)
  refine ⟨fun i => if h : i - 1 < k then u₀ ⟨i - 1, h⟩ else 0, hU.1, ⟨h1, hmul⟩, continuousOn_clm_apply.2 hcont,
    hnorm, hirr, ?_⟩
  intro Bs hBs w v
  rw [(Formalism.FourierDecayAlt.P.frame_general_linear Wp k r k z π Bs hR hBs).2,
    GlobalTheory.capelli_det_frame_indep Wp k r z π Bs B hz hT hR hBs hB, key]
  congr 1
  refine Finset.prod_bij' (fun s _ => s.val + 1) (fun i hi => ⟨i - 1, by simp only [Finset.mem_Icc] at hi; omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro s _
    simp only [Finset.mem_Icc]
    omega
  · intro i _
    exact Finset.mem_univ _
  · intro s _
    exact Fin.ext (by simp)
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    show i - 1 + 1 = i
    omega
  · intro s _
    simp only [Nat.add_sub_cancel, s.isLt, dite_true, Fin.eta]
    ring

end GlobalTheory.CapelliOfHC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryOfFixingBothFrames
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StabCnt
open Formalism.L2.SG.Pf

variable {D : D7}

theorem mem_orth_iff {U : Submodule D.host.E (VS D).V} {v : (VS D).V} :
    v ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem sup_span_add {P : Submodule D.host.E (VS D).V} {x d : (VS D).V} (hd : d ∈ P) :
    P ⊔ Submodule.span D.host.E {x + d} = P ⊔ Submodule.span D.host.E {x} := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
      (Submodule.mem_sup_left hd)
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have h2 : x + d ∈ P ⊔ Submodule.span D.host.E {x + d} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self (x + d))
    have h3 : d ∈ P ⊔ Submodule.span D.host.E {x + d} := Submodule.mem_sup_left hd
    have h1 := Submodule.sub_mem _ h2 h3
    simpa using h1

variable {T : D.host.E}

theorem xflag_succ (A : LFlag (D.sp.Y 0) D.R.rS T) (j : ℕ) (hj : j < D.R.rS) :
    Xflag A (j + 1) = Xflag A j ⊔ Submodule.span D.host.E {A.fl.e ⟨j, hj⟩} := by
  show Submodule.span _ (A.fl.e '' {i | i.1 < j + 1}) = Submodule.span _ (A.fl.e '' {i | i.1 < j}) ⊔ _
  rw [← Set.image_singleton, ← Submodule.span_union, ← Set.image_union]
  congr 2
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
  omega

theorem xflag_ge (A : LFlag (D.sp.Y 0) D.R.rS T) (j : ℕ) (hj : D.R.rS ≤ j) : Xflag A j = Xflag A D.R.rS := by
  show Submodule.span _ (A.fl.e '' {i | i.1 < j}) = Submodule.span _ (A.fl.e '' {i | i.1 < D.R.rS})
  congr 2
  ext i
  simp only [Set.mem_setOf_eq]
  omega

theorem frame_castSucc (A : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) : frame A i.castSucc = A.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_last (A : LFlag (D.sp.Y 0) D.R.rS T) : frame A (Fin.last _) = A.fl.z := by
  simp [frame, FlagG.fvec]

theorem adapt_xflag {A B : LFlag (D.sp.Y 0) D.R.rS T} {a : GV D} (h : Adapt a A B) (j : ℕ) :
    (Xflag A j).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag B j := by
  induction j with
  | zero => rw [xflag_zero, xflag_zero, Submodule.map_bot]
  | succ j ih =>
    by_cases hj : j < D.R.rS
    · rw [xflag_succ A j hj, xflag_succ B j hj, Submodule.map_sup, ih, Submodule.map_span, Set.image_singleton]
      have hd := h.2 (Fin.castSucc ⟨j, hj⟩)
      rw [frame_castSucc, frame_castSucc, Fin.coe_castSucc] at hd
      have e : (a : (VS D).V →ₗ[D.host.E] (VS D).V) (A.fl.e ⟨j, hj⟩) = B.fl.e ⟨j, hj⟩ + (a (A.fl.e ⟨j, hj⟩) - B.fl.e ⟨j, hj⟩) := by
        simp
      rw [e, sup_span_add hd]
    · rw [xflag_ge A (j + 1) (by omega), xflag_ge B (j + 1) (by omega), ← xflag_ge A j (by omega),
        ← xflag_ge B j (by omega), ih]

theorem adapt_xsp {A B : LFlag (D.sp.Y 0) D.R.rS T} {a : GV D} (h : Adapt a A B) :
    (Xsp A).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B := by
  rw [xsp_eq, xsp_eq, adapt_xflag h]

theorem orth_map_isom {a : GV D} (ha : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {U U' : Submodule D.host.E (VS D).V}
    (hU : U.map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = U') :
    (orth (VS D) U).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = orth (VS D) U' := by
  ext w
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, mem_orth_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩ x' hx'
    rw [← hU] at hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    simp only [LinearEquiv.coe_coe]
    rw [ha]; exact hv x hx
  · intro hw
    refine ⟨a.symm w, fun x hx => ?_, by simp⟩
    have := hw (a x) (hU ▸ Submodule.mem_map_of_mem hx)
    have e : (VS D).hT (a x) (a (a.symm w)) = (VS D).hT x (a.symm w) := ha _ _
    simp only [LinearEquiv.apply_symm_apply] at e
    rw [← e]; exact this

theorem adapt_orth {A B : LFlag (D.sp.Y 0) D.R.rS T} {a : GV D} (h : Adapt a A B) :
    (orth (VS D) (Xsp A)).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = orth (VS D) (Xsp B) :=
  orth_map_isom h.1 (adapt_xsp h)

theorem mem_of_map_eq {a : GV D} {U U' : Submodule D.host.E (VS D).V}
    (hU : U.map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = U') {x : (VS D).V} (hx : x ∈ U) : a x ∈ U' := by
  rw [← hU]; exact Submodule.mem_map_of_mem hx

theorem symm_mem_of_map_eq {a : GV D} {U U' : Submodule D.host.E (VS D).V}
    (hU : U.map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = U') {y : (VS D).V} (hy : y ∈ U') : a.symm y ∈ U := by
  rw [← hU] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using hx

theorem adapt_mul {A B C : LFlag (D.sp.Y 0) D.R.rS T} {a b : GV D} (ha : Adapt a A B) (hb : Adapt b B C) :
    Adapt (b * a) A C := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hb.1 ha.1, fun k => ?_⟩
  have e : (b * a) (frame A k) - frame C k = b (a (frame A k) - frame B k) + (b (frame B k) - frame C k) := by
    rw [le_mul_app, map_sub]; abel
  rw [e]
  exact add_mem (mem_of_map_eq (adapt_xflag hb _) (ha.2 k)) (hb.2 k)

theorem adapt_inv {A B : LFlag (D.sp.Y 0) D.R.rS T} {a : GV D} (ha : Adapt a A B) : Adapt a⁻¹ B A := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem ha.1, fun k => ?_⟩
  have e : a⁻¹ (frame B k) - frame A k = -(a.symm (a (frame A k) - frame B k)) := by
    rw [le_inv_app, map_sub]; simp
  rw [e]
  exact neg_mem (symm_mem_of_map_eq (adapt_xflag ha _) (ha.2 k))

theorem z_mem_orth (A : LFlag (D.sp.Y 0) D.R.rS T) : A.fl.z ∈ orth (VS D) (Xsp A) := by
  rw [mem_orth_iff]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact A.fl.z_orth i
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem adapt_nrat {A : LFlag (D.sp.Y 0) D.R.rS T} {n : GV D} (hn : n ∈ NRat A) : Adapt n A A := by
  refine ⟨hn.1, fun k => ?_⟩
  induction k using Fin.lastCases with
  | last =>
    rw [frame_last, Fin.val_last, ← xsp_eq]
    exact hn.2.2 _ (z_mem_orth A)
  | cast i =>
    rw [frame_castSucc, Fin.coe_castSucc]
    apply hn.2.1 i.1
    show A.fl.e i ∈ Submodule.span _ (A.fl.e '' {k | k.1 < i.1 + 1})
    exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩

theorem frameAdaptedIsometry_of_fixing_both_frames {T' : D.host.E} {A : LFlag (D.sp.Y 0) D.R.rS T} {A' : LFlag (D.sp.Y 0) D.R.rS T'} {h : GV D}
    (hh : h ∈ H0 A A') : Adapt h A A ∧ Adapt h A' A' :=
  ⟨⟨hh.1, fun k => by rw [hh.2.1 k, sub_self]; exact zero_mem _⟩,
   ⟨hh.1, fun k => by rw [hh.2.2 k, sub_self]; exact zero_mem _⟩⟩

theorem adapt_mapLF {A : LFlag (D.sp.Y 0) D.R.rS T} {γ : GV D} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    Adapt γ A (mapLF γ A) := by
  refine ⟨hγ, fun k => ?_⟩
  have : frame (mapLF γ A) k = γ (frame A k) := by
    simp only [mapLF, dif_pos hγ, frame]
    rw [fvec_mapFlag]
  rw [this, sub_self]; exact zero_mem _

theorem nrat_conj {A B : LFlag (D.sp.Y 0) D.R.rS T} {a n : GV D} (ha : Adapt a A B) (hn : n ∈ NRat A) :
    a * n * a⁻¹ ∈ NRat B := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ha.1 hn.1)
    ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem ha.1), fun j x hx => ?_, fun x hx => ?_⟩
  · have e : (a * n * a⁻¹) x - x = a (n (a.symm x) - a.symm x) := by
      rw [le_mul_app, le_mul_app, le_inv_app, map_sub]; simp
    rw [e]
    exact mem_of_map_eq (adapt_xflag ha j) (hn.2.1 j _ (symm_mem_of_map_eq (adapt_xflag ha _) hx))
  · have e : (a * n * a⁻¹) x - x = a (n (a.symm x) - a.symm x) := by
      rw [le_mul_app, le_mul_app, le_inv_app, map_sub]; simp
    rw [e]
    exact mem_of_map_eq (adapt_xsp ha) (hn.2.2 _ (symm_mem_of_map_eq (adapt_orth ha) hx))

theorem nrat_eq_nlam (A : LFlag (D.sp.Y 0) D.R.rS T) : NRat A = NLam ⊤ A := by
  ext n
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, ?_⟩, h2, h3⟩
    rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_top, LinearMap.range_eq_top]
    exact n.surjective
  · rintro ⟨⟨h1, _⟩, h2, h3⟩
    exact ⟨h1, h2, h3⟩

def NRatSub (A : LFlag (D.sp.Y 0) D.R.rS T) : Subgroup (GV D) := NLamSub ⊤ A

theorem mem_nratSub {A : LFlag (D.sp.Y 0) D.R.rS T} {n : GV D} : n ∈ NRatSub A ↔ n ∈ NRat A := by
  rw [nrat_eq_nlam]; rfl

theorem nrat_mul {A : LFlag (D.sp.Y 0) D.R.rS T} {a b : GV D} (ha : a ∈ NRat A) (hb : b ∈ NRat A) : a * b ∈ NRat A :=
  mem_nratSub.1 ((NRatSub A).mul_mem (mem_nratSub.2 ha) (mem_nratSub.2 hb))

theorem nrat_inv {A : LFlag (D.sp.Y 0) D.R.rS T} {a : GV D} (ha : a ∈ NRat A) : a⁻¹ ∈ NRat A :=
  mem_nratSub.1 ((NRatSub A).inv_mem (mem_nratSub.2 ha))

theorem nrat_one (A : LFlag (D.sp.Y 0) D.R.rS T) : (1 : GV D) ∈ NRat A :=
  mem_nratSub.1 (NRatSub A).one_mem

section Defs

variable {T T' : D.host.E}

def InB (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (lam lam' : LV D) (γ : GV D)
    (b : GV D × GV D) : Prop :=
  b.1 ∈ Aut0 F0 lam ∧ b.2 ∈ Aut0 F0' lam' ∧ KeyEq F0 F0' lam γ (b.1 * γ * b.2⁻¹)

def Corr (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (F0' F' : LFlag (D.sp.Y 0) D.R.rS T') (γ g : GV D) (b : GV D × GV D)
    (h : GV D) : Prop :=
  h ∈ H0 F F' ∧ ∃ n ∈ NRat F0, ∃ n' ∈ NRat F0', b.1 * γ * b.2⁻¹ = n * γ * n' ∧
    h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F ∧ h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F'

end Defs

end GlobalTheory.StabCnt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableOfIntegrableProdOfContinuous
section
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.ProdFactor

theorem integrable_of_integrable_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℂ}
    (hm : ∀ i, AEStronglyMeasurable (f i) (μ i)) (h0 : ∀ i, ¬ f i =ᵐ[μ i] 0)
    (h : Integrable (fun x : ∀ i, E i => ∏ i, f i (x i)) (Measure.pi μ)) (i : ι) :
    Integrable (f i) (μ i) := by

  by_contra hi
  have hn : ¬ Integrable (fun x => ‖f i x‖) (μ i) := fun h' => hi ((integrable_norm_iff (hm i)).1 h')
  have hprod : ∫ x : (∀ j, E j), ∏ j, ‖f j (x j)‖ ∂(Measure.pi μ) = 0 :=
    (integral_fintype_prod_eq_prod (μ := μ) (fun j (y : E j) => ‖f j y‖)).trans
      (Finset.prod_eq_zero (Finset.mem_univ i) (integral_undef hn))
  have hnorm : Integrable (fun x : ∀ j, E j => ∏ j, ‖f j (x j)‖) (Measure.pi μ) := by
    have h' := h.norm
    simp only [norm_prod] at h'
    exact h'
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => Finset.prod_nonneg fun j _ => norm_nonneg (f j (x j))) hnorm).1 hprod
  have hbox : Measure.pi μ (Set.univ.pi fun j => {y | f j y ≠ 0}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq] at hx
    simp only [Set.mem_ofPred_eq, Pi.zero_apply]
    exact Finset.prod_ne_zero_iff.2 fun j _ => norm_ne_zero_iff.2 (hx j)
  rw [Measure.pi_pi] at hbox
  refine (Finset.prod_ne_zero_iff.2 fun j _ => ?_) hbox
  intro hz
  exact h0 j (ae_iff.2 (by simpa using hz))

theorem integrable_of_integrable_prod_of_continuous {ι : Type} [Fintype ι] {E : ι → Type}
    [∀ i, TopologicalSpace (E i)] {mE : ∀ i, MeasurableSpace (E i)} [∀ i, OpensMeasurableSpace (E i)]
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsOpenPosMeasure] {f : ∀ i, E i → ℂ}
    (hc : ∀ i, Continuous (f i)) (h0 : ∀ i, ∃ x, f i x ≠ 0)
    (h : Integrable (fun x : ∀ i, E i => ∏ i, f i (x i)) (Measure.pi μ)) (i : ι) :
    Integrable (f i) (μ i) := by

  refine integrable_of_integrable_prod (fun j => (hc j).aestronglyMeasurable) (fun j hj => ?_) h i
  obtain ⟨x, hx⟩ := h0 j
  exact hx (congrFun (((hc j).ae_eq_iff_eq (μ j) continuous_zero).1 hj) x)

section Local

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem continuous_coefOn (hU : IsURepOn (UJset ε) σ) (v w : H) : Continuous (coefOn (ε := ε) σ v w) := by
  obtain ⟨-, -, hcont⟩ := hU
  have hσ : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) v :=
    (hcont v).comp_continuous (Units.continuous_val.comp continuous_subtype_val) fun g => g.2
  exact continuous_const.inner hσ

theorem coefOn_one (hU : IsURepOn (UJset ε) σ) {w : H} (hw : ‖w‖ = 1) : coefOn (ε := ε) σ w w 1 = 1 := by
  obtain ⟨⟨h1, -⟩, -, -⟩ := hU
  have hu : umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  show ⟪w, σ (umat (1 : Formalism.REAL.UJ ε)) w⟫_ℂ = 1
  rw [hu, h1, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hw]
  norm_num

theorem fdegOf_pos (hU : IsURepOn (UJset ε) σ) (hsq : IsSqIntOn ε σ) {w : H} (hw : ‖w‖ = 1) :
    0 < fdegOf (Formalism.REAL.muG ε) σ w := by

  show 0 < ‖w‖ ^ 4 / ∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε)
  rw [hw, one_pow]
  refine div_pos one_pos ?_
  have hcont : Continuous fun g : Formalism.REAL.UJ ε => ‖coefOn (ε := ε) σ w w g‖ ^ 2 :=
    (continuous_coefOn hU w w).norm.pow 2
  have hint : Integrable (fun g => ‖coefOn (ε := ε) σ w w g‖ ^ 2) (Formalism.REAL.muG ε) :=
    (hsq w w).norm.integrable_sq
  rw [integral_pos_iff_support_of_nonneg (fun g => by positivity) hint]
  refine hcont.isOpen_support.measure_pos _ ⟨1, ?_⟩
  simp [Function.mem_support, coefOn_one hU hw]

end Local

theorem integrable_factor {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin n) (Fin n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (d : ι → ℝ)
    (hU : ∀ v, IsURepOn (UJset (ε v)) (σ v)) (hw : ∀ v, ‖w v‖ = 1) (hd : ∀ v, d v ≠ 0)
    (h : Integrable (fun g : ∀ v, Formalism.REAL.UJ (ε v) =>
      ∏ v, (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) (g v))) (Measure.pi fun v => Formalism.REAL.muG (ε v)))
    (v : ι) :
    Integrable (fun g => (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) g)) (Formalism.REAL.muG (ε v)) := by

  exact integrable_of_integrable_prod_of_continuous (E := fun v => Formalism.REAL.UJ (ε v))
    (μ := fun v => Formalism.REAL.muG (ε v))
    (f := fun v g => (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) g))
    (fun v => continuous_const.mul (continuous_coefOn (hU v) (w v) (w v)).star)
    (fun v => ⟨1, by simp [coefOn_one (hU v) (hw v), hd v]⟩) h v

theorem integrable_factor' {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin n) (Fin n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (d : ι → ℝ)
    (hU : ∀ v, IsURepOn (UJset (ε v)) (σ v)) (hw : ∀ v, ‖w v‖ = 1) (hd : ∀ v, d v ≠ 0)
    (h : Integrable (fun g : ∀ v, Formalism.REAL.UJ (ε v) =>
      ((∏ v, d v : ℝ) : ℂ) * star (∏ v, coefOn (ε := ε v) (σ v) (w v) (w v) (g v)))
      (Measure.pi fun v => Formalism.REAL.muG (ε v))) (v : ι) :
    Integrable (fun g => (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) g)) (Formalism.REAL.muG (ε v)) := by
  have hfun : (fun g : ∀ v, Formalism.REAL.UJ (ε v) =>
      ((∏ v, d v : ℝ) : ℂ) * star (∏ v, coefOn (ε := ε v) (σ v) (w v) (w v) (g v))) =
      fun g => ∏ v, (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) (g v)) := by
    funext g
    rw [Complex.ofReal_prod, star_prod, Finset.prod_mul_distrib]
  rw [hfun] at h
  exact integrable_factor ε σ w d hU hw hd h v

end GlobalTheory.ProdFactor
end
end

