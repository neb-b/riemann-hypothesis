module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
public import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ParabolicAtStandardWeylElement
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatProductFormula
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorMvPolynomialSubmoduleEqTopOfOneMulX
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift

theorem atPl_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem mvPolynomial_submodule_eq_top {σ : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) (h1 : (1 : MvPolynomial σ ℂ) ∈ S)
    (hX : ∀ (l : σ), ∀ p ∈ S, MvPolynomial.X l * p ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro p _
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : (MvPolynomial.C a : MvPolynomial σ ℂ) = a • (1 : MvPolynomial σ ℂ) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [this]; exact S.smul_mem a h1
  | add p q hp hq => exact S.add_mem (hp trivial) (hq trivial)
  | mul_X p n hp => rw [mul_comm]; exact hX n p (hp trivial)

theorem tensor_submodule_eq_top : ∀ {ι σ : Type} [Fintype ι] [DecidableEq ι] (N : Submodule ℂ (⨂[ℂ] _ : ι, MvPolynomial σ ℂ)),
    PiTensorProduct.tprod ℂ (fun _ => (1 : MvPolynomial σ ℂ)) ∈ N →
    (∀ (w : ι) (l : σ), ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial σ ℂ)) T ∈ N) → N = ⊤ := by
  intro ι σ _ _ N h1 hX
  have key : ∀ s : Finset ι, ∀ f : ι → MvPolynomial σ ℂ, (∀ i ∉ s, f i = 1) → PiTensorProduct.tprod ℂ f ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      have : f = fun _ => 1 := funext fun i => hf i (Finset.notMem_empty i)
      rw [this]; exact h1
    | insert w₀ s hw₀ ih =>
      intro f hf
      let S : Submodule ℂ (MvPolynomial σ ℂ) :=
        N.comap ((PiTensorProduct.tprod ℂ : (∀ _ : ι, MvPolynomial σ ℂ) →ₘₗ[ℂ] (⨂[ℂ] _ : ι, MvPolynomial σ ℂ)).toLinearMap f w₀)
      have hS1 : (1 : MvPolynomial σ ℂ) ∈ S := by
        show PiTensorProduct.tprod ℂ (Function.update f w₀ 1) ∈ N
        apply ih
        intro i hi
        by_cases h : i = w₀
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hf i (by simp [h, hi])
      have hSX : ∀ (l : σ), ∀ p ∈ S, MvPolynomial.X l * p ∈ S := by
        intro l p hp
        have hp' : PiTensorProduct.tprod ℂ (Function.update f w₀ p) ∈ N := hp
        show PiTensorProduct.tprod ℂ (Function.update f w₀ (MvPolynomial.X l * p)) ∈ N
        have := hX w₀ l _ hp'
        rw [atPl_tprod] at this
        simpa using this
      have htop := mvPolynomial_submodule_eq_top S hS1 hSX
      have hf0 : f w₀ ∈ S := by rw [htop]; trivial
      have : PiTensorProduct.tprod ℂ (Function.update f w₀ (f w₀)) ∈ N := hf0
      simpa using this
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact key Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)

end GlobalTheory.RealLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowersLinearIndependentOverLocalTensorCenter
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem pow_indep_tensor : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n →
    ∀ (v : AwayP p) (c : Fin G.n → Qv v ⊗[ℚ] G.F),
      ∑ i, iotaF G v (c i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = 0 → c = 0 := by
  intro p _ G γ hn v c hc

  let ψ : (Fin G.n → G.F) →ₗ[ℚ] G.C :=
    { toFun := fun f => ∑ i, f i • γ ^ (i : ℕ)
      map_add' := fun f g => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun q f => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_assoc] }
  have li : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hn] at this
    exact this
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    exact funext ((Fintype.linearIndependent_iff.mp li) f hf)
  have hinj : Function.Injective (ψ.lTensor (Qv v)) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ hψ
  let e := TensorProduct.piRight ℚ ℚ (Qv v) (fun _ : Fin G.n => G.F)
  have key : ∀ t : Qv v ⊗[ℚ] (Fin G.n → G.F),
      ∑ i, iotaF G v (e t i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = ψ.lTensor (Qv v) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), ← hx, ← hy, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply, map_add (f := _), add_mul]
    | tmul q f =>
      rw [LinearMap.lTensor_tmul]
      have : ∀ i, e (q ⊗ₜ[ℚ] f) i = q ⊗ₜ[ℚ] f i := fun i => rfl
      simp only [this, iotaF_tmul, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.tmul_sum, Algebra.smul_def]

  have h0 : ψ.lTensor (Qv v) (e.symm c) = 0 := by
    rw [← key, LinearEquiv.apply_symm_apply]; exact hc
  have : e.symm c = 0 := hinj (by rw [h0, map_zero])
  rw [← e.apply_symm_apply c, this, map_zero]

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsEqTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.PrincipalRows

theorem theta_adjoint_mem {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (cv : CrdV A) (hKR : X.KFormR) (hJR : X.JIsoR cv) (hRT : Formalism.IndefR.Rat.RowTest X) (t : Bs.Tup) (S : Submodule ℂ X.EE)
    (hZ : ∀ z ∈ X.Z t, X.Θ t (X.jR t z) ∈ S) (e : X.EE) : X.Θ t (LinearMap.adjoint (X.Θ t) e) ∈ S := by
  obtain ⟨N, ψ, hψ, hr⟩ := hRT
  have hspan : Submodule.span ℂ ((X.jR t) '' (X.Z t : Set (A.FR t))) = LinearMap.range (LinearMap.adjoint (X.Θ t)) :=
    Formalism.IndefR.Rat.range_adjoint_rat Bs.v0.embedding (X.jR t) (cv.hR t) (CxData.bR t) (hKR t).1 (hKR t).2 (hJR t) (X.Θ t) ψ hψ
      (fun i x => hr t i x)
  have hsub : LinearMap.range (LinearMap.adjoint (X.Θ t)) ≤ S.comap (X.Θ t) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact hZ z hz
  exact hsub ⟨e, rfl⟩

end GlobalTheory.PrincipalRows

namespace GlobalTheory.PrincipalRows

theorem mem_range_toF_full {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (Xc : Finset (G → K)) (Z : Submodule K B.S.Forms) (z : B.S.Forms) (hz : z ∈ Z)
    (hg : z ∈ B.goodF Xc) : z ∈ LinearMap.range (B.toF ⟨Xc, ⊥, 1⟩ Z) := by
  rw [GlobalTheory.OneForm.range_toF]
  refine ⟨hz, ?_⟩
  obtain ⟨w, hw⟩ := hg
  refine ⟨w, ?_⟩
  rw [← hw, Formalism.L2.DIV.CSD.gaOp, GlobalTheory.OneForm.asAlg_eq_sum, LinearMap.sum_apply]
  rfl

theorem theta_base_forms_mem_principal_good_part {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type}
    {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
    {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} (hIB : X.zs.InBlock) :
    ∀ z ∈ X.Z A3.A.fam.μ0, X.Θ A3.A.fam.μ0 (X.jR A3.A.fam.μ0 z) ∈
      EEg3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) := by
  intro z hz
  have h1 : z ∈ (A3.A.fam.R A3.A.fam.μ0).ZHg A3.A.fam.X := hIB.1 A3.A.fam.μ0 hz
  obtain ⟨x, hx⟩ := mem_range_toF_full (A3.A.fam.R A3.A.fam.μ0) A3.A.fam.X (X.zs.Z A3.A.fam.μ0) z hz h1.2
  refine ⟨cpt A3.A.v0.embedding x, ?_⟩
  have h3 := GlobalTheory.OneForm.iC_cpt X (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0 x
  refine h3.trans ?_
  exact congrArg (fun y => X.Θ A3.A.fam.μ0 (X.jR A3.A.fam.μ0 y)) hx

end GlobalTheory.PrincipalRows

namespace GlobalTheory.PrincipalRows


set_option maxHeartbeats 1000000 in
theorem principal_level_rows_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (⨆ p, R.EEp3 p) = ⊤ → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) = ⊤ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC hTop hPos hB hRT hIB
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hC.base.models
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hC.base.models
  have hmem := theta_adjoint_mem (R.toCx3 F) F.cv hKR hJR hRT A3.A.fam.μ0
    (EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc))
    (theta_base_forms_mem_principal_good_part A3 (R.toCx3 F) hIB)

  have hpart : ∀ p, ∀ y ∈ R.EEp3 p, (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) := by
    intro p y hy
    have hc : (0 : ℝ) < R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p := by
      refine mul_pos hPos.1 (Finset.prod_pos fun j _ => ?_)
      unfold RealDat3.lamN
      split_ifs
      · exact hPos.2 _ _ _
      · exact one_pos
    have hne : ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hce : ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y ∈ R.EEp3 p :=
      (R.EEp3 p).smul_mem _ hy
    have key : R.Th A3.A.fam.μ0 (LinearMap.adjoint (R.Th A3.A.fam.μ0)
        (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y)) = y := by
      refine (hB A3.A.fam.μ0 p _ hce).trans ?_
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    have h3 := hmem (Tw.mk (twAt D.what₂.embLL A3.A.v0) (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y))
    have h4 : (R.toCx3 F).Θ A3.A.fam.μ0 (LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0)
        (Tw.mk (twAt D.what₂.embLL A3.A.v0) (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y))) = Tw.mk (twAt D.what₂.embLL A3.A.v0) y := by
      show Tw.map _ (R.Th A3.A.fam.μ0) (LinearMap.adjoint (Tw.map _ (R.Th A3.A.fam.μ0)) _) = _
      rw [Tw.adjoint_map]
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) key
    rw [h4] at h3
    exact h3
  rw [eq_top_iff]
  intro e0 _
  have hx : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) e0 ∈ ⨆ p, R.EEp3 p := by rw [hTop]; exact Submodule.mem_top
  have hall : ∀ y ∈ ⨆ p, R.EEp3 p, (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) := by
    intro y hy
    exact Submodule.iSup_induction R.EEp3 (motive := fun y => (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc)) hy hpart
      (Submodule.zero_mem _) (fun a b ha hb => Submodule.add_mem _ ha hb)
  exact hall _ hx

end GlobalTheory.PrincipalRows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLiftFormsEqGoodForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.WgLift

open Formalism.IndefR.CxPass.LevelOperators


set_option maxHeartbeats 1000000 in
theorem principal_lift_forms_eq_good_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (⨆ p, R.Wp3 i p) = LinearMap.range (eH R.toRealDat i)) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmA → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ i, principalFormsSubspace A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) i = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hW hpos hA hLT hB i
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak hch hex
  have hM := hc.models
  have hCore : Core R.toRealDat F.lv2 := ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩
  have hL := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hok.ok2.irr i
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hM
  have hJ : (R.toCx3 F).JIsoL F.cv := Formalism.IndefR.Links.RealDat3.jIsoL_of (F := F) hM
  have hθ : ∀ t (u : (R.toCx3 F).FLC i t), Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) =
      cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u) := by
    intro t u
    rfl

  have hsub : ∀ t, ∀ y ∈ LinearMap.range ((R.toCx3 F).θ' i t), y ∈ Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) := by
    rintro t _ ⟨u, rfl⟩
    change Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) ∈ LinearMap.range (eH R.toRealDat i)
    rw [hθ]
    exact ⟨cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u), by rw [map_smul, hL.2.2.2]⟩

  have hrng : ∀ t, LinearMap.range ((R.toCx3 F).θ' i t) ≤
      LinearMap.range ((R.toCx3 F).tC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t) := by
    intro t
    obtain ⟨N, ψ, hψ, hr⟩ := hLT i
    have hRZ := Formalism.IndefR.Rat.range_adjoint_rat A3.fam3.base3.v0.embedding ((R.toCx3 F).jL i t) (F.cv.hL i t)
      (Formalism.IndefR.Cx.CxData.bL (A := A3.fam3.amb3) i t)
      (hK i t).1 (hK i t).2 (hJ i t) ((R.toCx3 F).θ' i t) ψ hψ (fun k x => hr t k x)
    have hgood : (LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) ≤
        LinearMap.range (opF (A3.A.fam.L i t).r (idemOf A3.A.X)) := by
      intro z hz
      have h1 : z ∈ (A3.A.fam.L i t).goodF A3.A.X := (hB.2 i t hz).2
      have h2 : (A3.A.fam.L i t).goodF A3.A.X = LinearMap.range (opF (A3.A.fam.L i t).r (idemOf A3.A.X)) := by
        unfold BlockDat.goodF
        rw [Formalism.IndefR.CxPass.LevelOperators.goodAt_bot]
        rfl
      rwa [h2] at h1
    rintro _ ⟨v, rfl⟩
    obtain ⟨u, hu, k, hk, hak⟩ := (LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).exists_add_mem_mem_orthogonal v
    have hk0 : (R.toCx3 F).θ' i t k = 0 := by
      have h0 : ⟪LinearMap.adjoint ((R.toCx3 F).θ' i t) ((R.toCx3 F).θ' i t k), k⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hk _ ⟨_, rfl⟩
      rw [LinearMap.adjoint_inner_left] at h0
      exact inner_self_eq_zero.1 h0
    rw [hak, map_add (f := _), hk0, add_zero]
    have hZeq : (((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t)) ⊓
        LinearMap.range (opF (A3.A.fam.L i t).r (idemOf A3.A.X)) : Submodule _ _) =
        LinearMap.range ((A3.A.fam.L i t).toF (A3.A.fam.lvlA ⊥ 1) ((R.toCx3 F).Zl i t)) := by
      refine Eq.trans ?_ (Formalism.IndefR.CxPass.LevelOperators.range_toF (A3.A.fam.L i t) (A3.A.fam.lvlA ⊥ 1) _).symm
      rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq,
        show goodAt (A3.A.fam.lvlA ⊥ 1).X (A3.A.fam.lvlA ⊥ 1).P (A3.A.fam.lvlA ⊥ 1).ψ = idemOf A3.A.X from
          Formalism.IndefR.CxPass.LevelOperators.goodAt_bot _ _]
      rfl
    have hZ2 : (LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) =
        LinearMap.range ((A3.A.fam.L i t).toF (A3.A.fam.lvlA ⊥ 1) ((R.toCx3 F).Zl i t)) := (inf_eq_left.2 hgood).symm.trans hZeq
    rw [← hRZ, hZ2] at hu
    obtain ⟨c, hc⟩ : u ∈ LinearMap.range (lin ((R.toCx3 F).uL (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t)) := by
      refine (Submodule.span_le.2 ?_) hu
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨cpt A3.fam3.base3.v0.embedding x,
        ((R.toCx3 F).jL_toL (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t x).symm⟩
    exact ⟨c, by rw [(R.toCx3 F).tC_eq, hc]⟩

  have hsup : Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) ≤ LinearMap.range ((R.toCx3 F).θ' i A3.A.μ0) := by
    intro w hw
    have hw' : Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) w ∈ ⨆ p, R.Wp3 i p := by rw [hW i]; exact hw
    have hcc : starRingEnd ℂ (R.phs i) * R.phs i = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, (hch.phase i).1]; norm_num
    refine Submodule.iSup_induction (fun p => R.Wp3 i p) (motive := fun (x : (R.HW i (sg0 D A3.A)).H) => (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : (R.toCx3 F).W i) ∈
      LinearMap.range ((R.toCx3 F).θ' i A3.A.μ0)) hw' ?_ ?_ ?_
    · intro p x hx
      have hlam := hpos.2 i A3.A.μ0 p
      have ha : LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x) =
          Tw.map (twAt D.what₂.embLL A3.A.v0) (LinearMap.adjoint (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x) :=
        congrArg (fun f => f (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)) (Formalism.IndefR.Links.Tw.adjoint_map (s := (twAt D.what₂.embLL A3.A.v0)) (R.thG i A3.A.μ0))
      have key : Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0) (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)) =
          ((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ) • Tw.mk (twAt D.what₂.embLL A3.A.v0) x := by
        refine (congrArg (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) ha).trans ?_
        show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0 (LinearMap.adjoint (R.thG i A3.A.μ0) x)) = _
        rw [hA i A3.A.μ0 p _ hx, Tw.mk_smul, cj_ofReal]
      have h3 := (Formalism.IndefR.Links.RealDat3.phase_cancel hcc (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)).trans key
      refine ⟨((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ)⁻¹ •
        LinearMap.adjoint (R.phs i • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x), ?_⟩
      change (R.phs i • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ)⁻¹ •
        LinearMap.adjoint (R.phs i • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)) = Tw.mk (twAt D.what₂.embLL A3.A.v0) x
      refine (map_smul _ _ _).trans ((congrArg (fun z => ((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ)⁻¹ • z) h3).trans ?_)
      rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hlam.ne'), one_smul]
    · exact Submodule.zero_mem _
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  unfold principalFormsSubspace
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rintro _ ⟨c, rfl⟩
    rw [(R.toCx3 F).tC_eq]
    exact hsub t _ ⟨_, rfl⟩
  · exact (hsup.trans (hrng A3.A.μ0)).trans
      (le_iSup (fun t => LinearMap.range ((R.toCx3 F).tC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t)) A3.A.μ0)

end GlobalTheory.WgLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdLowestKTypeDimsIndepComplexEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DimProdLab

theorem lab_spec {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    labE σ (lab σ ρ) = tauE D ρ ∨ labE σ (lab σ ρ) = (starRingEnd ℂ).comp (tauE D ρ) := by
  unfold lab; rw [dite_eq_left (GlobalTheory.ConjReading.lab_exists σ ρ)]; exact (GlobalTheory.ConjReading.lab_exists σ ρ).choose_spec

theorem lab_injective {D : D7} (σ : D.what₂.LL →+* ℂ) : Function.Injective (lab σ : D.what₂.Tau → D.what₂.Tau) := by
  intro ρ ρ' h
  have cc : ∀ f : D.host.E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp f) = f := GlobalTheory.ConjReading.conj_conj
  rcases lab_spec σ ρ with h1 | h1 <;> rcases lab_spec σ ρ' with h2 | h2 <;> rw [h] at h1
  · exact Formalism.IndefR.Fock.KV.tauE_injective (h1.symm.trans h2)
  · exact absurd (h1.symm.trans h2) (Formalism.IndefR.Fock.KV.tauE_ne_conj _ _)
  · exact absurd (h2.symm.trans h1) (Formalism.IndefR.Fock.KV.tauE_ne_conj _ _)
  · have e := congrArg (fun f => (starRingEnd ℂ).comp f) (h1.symm.trans h2)
    simp only [cc] at e
    exact Formalism.IndefR.Fock.KV.tauE_injective e

theorem dimK_congr {R : Ranks} (hc : HCParam R) {a b : ℕ × ℕ} (e : a = b) :
    dimK a.1 a.2 (Formalism.L2.NTheta.kapW hc a.1 a.2) = dimK b.1 b.2 (Formalism.L2.NTheta.kapW hc b.1 b.2) := by
  subst e; rfl

theorem prod_dims (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := by
  set s := D.R.sigW ((i : ℕ) + 1)
  let hd : D.what₂.Tau → ℚ := fun τ => dimK s.1 s.2 (Formalism.L2.NTheta.kapW (D.hc τ) s.1 s.2)
  have h1 : ∀ ρ, dimK _ _ (kapAt (Wc D i) σ ρ) = hd (lab σ ρ) := fun ρ =>
    dimK_congr (D.hc (lab σ ρ)) (Formalism.IndefR.Fock.KV.sig_Wc i ρ)
  have h2 : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ = ((hd τ : ℚ) : ℝ) := fun τ =>
    congrArg (fun q : ℚ => (q : ℝ)) (dimK_congr (D.hc τ) (Formalism.IndefR.Fock.KV.sig_Wc i τ))
  have hb : Function.Bijective (lab σ : D.what₂.Tau → D.what₂.Tau) := (lab_injective σ).bijective_of_finite
  simp only [h1, h2]
  refine (Equiv.prod_comp (Equiv.ofBijective _ hb) (fun τ => ((hd τ : ℚ) : ℂ))).trans ?_
  push_cast
  rfl

end GlobalTheory.DimProdLab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComplexPointsLevelFormsEqGoodForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.LevelRange

theorem range_w0C_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.LUnif → ∀ b i, LinearMap.range ((R.toCx3 F).w0C b i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) ((R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 b (sg0 D A3.A))).comap (R.HW i (sg0 D A3.A)).e) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hU b i
  have hL := GlobalTheory.LevelForms.levelW_of_irr R.toRealDat F.lv2 hOk.ok2.irr hU hC.base.models.HW
  rw [← hL b i (sg0 D A3.A)]
  have h3 : Submodule.span ℂ (Set.range fun k => (⟨R.toRealDat.bC F.lv2 b i (sg0 D A3.A) k, Submodule.subset_span ⟨k, rfl⟩⟩ :
      R.toRealDat.WS F.lv2 b i (sg0 D A3.A))) = ⊤ := Submodule.span_range_subtype_eq_top_iff _ _ |>.2 rfl
  have h4 : LinearMap.range ((R.toCx3 F).wC b i A3.A.v0) = ⊤ :=
    (Fintype.range_linearCombination _ _).trans (Tw.span_top (E := R.toRealDat.WS F.lv2 b i (sg0 D A3.A)) _ h3)
  have hc : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) b)).ne'
  refine (LinearMap.range_comp_of_range_eq_top _ h4).trans (le_antisymm ?_ fun x hx => ?_)
  · rintro _ ⟨y, rfl⟩
    exact (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).smul_mem _ (Tw.out y : R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).2
  · let y : (R.HW i (sg0 D A3.A)).H := x
    exact ⟨(⟨((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ)⁻¹ • y, (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).smul_mem _ hx⟩ :
      R.toRealDat.WS F.lv2 b i (sg0 D A3.A)), smul_inv_smul₀ hc y⟩

end GlobalTheory.LevelRange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementsBoundedPadic
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_elements_bounded_padic : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (h₂ : Gr G 1), ∃ (B : ℝ) (e : ℕ), ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (∀ (w : Fin G.m) (a b : Fin G.n), ‖((G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B ∧ ‖((G.rho w (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B) ∧ ∃ (k : ℤ) (m : ℕ), ¬ p ∣ m ∧ (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ * (p : ℚ) ^ e = k / m := by
  first | (exact @GlobalTheory.FixBound.bounded_of_support) | (exact GlobalTheory.FixBound.bounded_of_support) | (intros; apply GlobalTheory.FixBound.bounded_of_support <;> assumption)
end

