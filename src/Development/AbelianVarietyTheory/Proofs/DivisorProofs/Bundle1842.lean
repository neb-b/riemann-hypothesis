module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFramedLiftsEquivMovedGroupCosets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportSelfDualDataOneHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqSelfDualLatticesSameHermitianSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1835
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfCore
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1635
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

def commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) : LB Y where
  ι := C.J
  U j := (B s).U (C.idx s j)
  g j j' := (B s).g (C.idx s j) (C.idx s j')

theorem isLB_commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    (commonRestr C s).IsLB := {
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := C.cover y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (C.mem s j y).2 hj⟩
  g_self j := (C.isLB s).g_self (C.idx s j)
  cocycle i j k := (C.isLB s).cocycle (C.idx s i) (C.idx s j) (C.idx s k) }

theorem commonRestr_iso {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    LBIso (commonRestr C s) (B s) :=
  iso_of_chart (C.isLB s)
    { idx := C.idx s
      le := fun _ _ h => h
      g := fun _ _ _ _ _ => rfl }

theorem commonRestr_iso_tens {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    LBIso (commonRestr C (a + b)) (tens (B a) (B b)) :=
  iso_of_chart (isLB_tens (C.isLB a) (C.isLB b))
    { idx := fun j => (C.idx a j, C.idx b j)
      le := fun j y h => by
        have h' : y ∈ C.U j := (C.mem (a + b) j y).1 h
        exact ⟨(C.mem a j y).2 h', (C.mem b j y).2 h'⟩
      g := fun y j j' hj hj' => by
        have h₁ : y ∈ C.U j := (C.mem (a + b) j y).1 hj
        have h₂ : y ∈ C.U j' := (C.mem (a + b) j' y).1 hj'
        refine (C.add a b y j j' h₁ h₂).trans ?_
        exact (tr_tens (B a) (B b) y (a := (C.idx a j, C.idx b j)) (b := (C.idx a j', C.idx b j'))
          ⟨(C.mem a j y).2 h₁, (C.mem b j y).2 h₁⟩ ⟨(C.mem a j' y).2 h₂, (C.mem b j' y).2 h₂⟩).symm }

theorem cls_common_add {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    cls (B (a + b)) (C.isLB (a + b)) = cls (B a) (C.isLB a) + cls (B b) (C.isLB b) := by
  have e₁ := (cls_eq_iff (isLB_commonRestr C (a + b)) (C.isLB (a + b))).2 (commonRestr_iso C (a + b))
  have e₂ := (cls_eq_iff (isLB_commonRestr C (a + b)) (isLB_tens (C.isLB a) (C.isLB b))).2
    (commonRestr_iso_tens C a b)
  rw [← e₁, e₂, cls_tens (C.isLB a) (C.isLB b)]

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFramedLiftsEquivMovedGroupCosetsStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexFramedLifts_equiv_movedGroupCosets : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E), (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0 ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ (π k₂) (δ k₂)) → ∀ k (x' : ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).dom), letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra; Nonempty ({y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} ≃ Σ k₂ : {k₂ // π k₂ = k}, ↥((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ⧸ (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).subgroupOf ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) := by
  first | exact @GlobalTheory.LevModel.frLifts_equiv_cosets | exact GlobalTheory.LevModel.frLifts_equiv_cosets | (intros; apply GlobalTheory.LevModel.frLifts_equiv_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationComponentsCovolumeEq
section
open NumberField

namespace GlobalTheory.EqCovol

theorem covol_eq_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k k' : U.Comp, GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol (U.X k') := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hG hp hq k k'
  obtain ⟨Y, hΨ, hp0, -, -, -, hL, hS, hc⟩ := GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k
  obtain ⟨Y', hΨ', hp0', -, -, -, hL', hS', hc'⟩ := GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k'
  obtain ⟨hr, hk, -⟩ := hU
  have hY : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => hΨ ▸ (hk k).2 τ
  have hY' : ∀ τ : E →+* ℂ, τ ∈ Y'.Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => hΨ' ▸ (hk k').2 τ
  have eΨ : Y'.Ψ = Y.Ψ := Finset.ext fun τ => (hY' τ).trans (hY τ).symm
  have ep : Y'.p0 = Y.p0 := by rw [hp0, hp0', (hk k).1, (hk k').1]
  have h1 : 1 ≤ Y.p0 := by rw [hp0, (hk k).1]; exact hq
  have h2 : Y.p0 < r := by rw [hp0, (hk k).1, hr]; omega
  obtain ⟨Z, hZΨ, hZG, hZξ, hZp, hZL, hZS, hZc⟩ := _root_.GlobalTheory.EqCovol.exists_transport E H l r Y Y' hY eΨ ep h1 h2 hL' hS hS'
  rw [hc, hc', ← hZc]
  exact _root_.GlobalTheory.EqCovol.SameSpace.covol_eq_of_same_space E H l r Y Z hG hY hZΨ hZG hZξ hZp h1 h2 hL hZL hS hZS

end GlobalTheory.EqCovol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.CovTop

namespace GlobalTheory.LawsDeep

theorem goodAt_of_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l l₂ : Level H) (b : ℕ) (hM : l₂.M = l.M * b) (hl : ∀ p : ℕ, p.Prime → l.GoodAt p) (p : ℕ) (hp : p.Prime) :
    l₂.GoodAt p := by
  rw [GlobalTheory.HostProbe.goodAt_iff l₂ hp]
  intro k hk
  have hdvd : l.M ∣ p ^ k := ⟨b, by rw [← hk]; exact hM⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact (GlobalTheory.HostProbe.goodAt_iff l hp).1 (hl p hp) i hi

theorem levLaws (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (hT : LawsJ T) (hj : InR D j)
    (hG : Y.Good e o) : GlobalTheory.LevGeo.Laws D j Y.d.Xo₂ Y.d.c₂ Y.U Y.dict := by
  refine
    { inR := hj
      host := hT.toLawsM.pins.1
      dat := hT.toLawsM.pins.2.2.2 j hj
      levA := hG.lev.2
      unf := hG.unf
      chiTriv := hG.chiTriv
      dictU := ?_
      modelW := hG.modelW }
  intro σ hσ
  obtain ⟨th, hr, hth, hd⟩ := hG.dictU σ hσ
  refine ⟨Y.Kf, th, hr, ?_, hth, hd, hG.unit σ hσ⟩
  have h₁ := hG.lev.1
  unfold DeltaDat.IsLev at h₁
  have h₂ := hT.toLawsM.pins.2.1
  unfold Par.PinLevel at h₂
  rw [h₁.2.1, h₂.1]
  exact hG.levelK

theorem laws_deep : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ),
    LawsJ T → InR D j → Y.Good e o → Laws Y.U (xiR D) := by
  intro D T j Y e o hT hj hG
  have hM : Y.d.l₂.M = T.Q.l.M * Y.d.pd := by
    have h₁ := hG.lev.1
    unfold DeltaDat.IsLev at h₁
    exact h₁.2.1
  have hgood : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := fun p hp =>
    goodAt_of_mul T.Q.l Y.d.l₂ Y.d.pd hM (GlobalTheory.RecDict.level_good_and_sign D T.Q hT.toLawsM.pins).1 p hp
  exact (GlobalTheory.T.moduliLaws_of_principalLevel_fieldOfDefinition D j T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ Y.U Y.dict
    (levLaws D T j Y e o hT hj hG) hG.geo hgood).1

end GlobalTheory.LawsDeep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovarianceAtConstantXi
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtIdCore

theorem exists_scalar_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W), ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0' → GlobalTheory.PtId.IoAt O (v₀ i (sg0 D A)) ka := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT hI i c0L
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) ∧ CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0'
  swap
  · exact ⟨1, norm_one, fun Tp tup O h1 h2 => absurd ⟨Tp, tup, O, h1, h2⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀, hB₀⟩ := hex
  obtain ⟨ka₀, hn₀, hk₀⟩ := GlobalTheory.AdTh.PhaseMap.io_eq_phase_smul_ofCore D G Pl0 T0 A T R F κ v₀ hC hT hI i Tp₀ tup₀ O₀ hP₀
  refine ⟨ka₀, hn₀, fun Tp tup O hP hB => ?_⟩
  obtain ⟨ka, -, hk⟩ := GlobalTheory.AdTh.PhaseMap.io_eq_phase_smul_ofCore D G Pl0 T0 A T R F κ v₀ hC hT hI i Tp tup O hP
  intro lt hlt u hu
  suffices h : ka = ka₀ by
    subst h
    exact hk lt hlt u hu
  have e1 := hk lt hlt u hu A.μ0 O.hw
  have e2 := hk₀ lt hlt u hu A.μ0 O₀.hw
  obtain ⟨hw1, cga, -, hinj, -, -, -, -, hio, -⟩ := hP.io
  obtain ⟨hw2, cga', -, -, -, -, -, -, hio₀, -⟩ := hP₀.io
  have hne : O.io O.hw ≠ 0 := by
    intro h0
    have h1 : O.hw = 0 := hinj (h0.trans (map_zero _).symm)
    have h2 := (GlobalTheory.AdTh.coefMap_norm_equivariant_basis_ofCore D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hP).1
    rw [h1, map_zero, norm_zero] at h2
    exact zero_ne_one h2
  rw [GlobalTheory.PtId.OneScalar.coefficientMap_extremalTensor_baseChange O hw1 hB] at e1
  rw [GlobalTheory.PtId.OneScalar.coefficientMap_extremalTensor_baseChange O₀ hw2 hB₀, hio₀, GlobalTheory.PtId.OneScalar.map_pG_eq O₀.c' O.c' (inC O₀.c') (inC O.c'), ← hio, e1] at e2
  have hV := hP.lift.std
  obtain ⟨f1, f2, f3, f4, f5⟩ := GlobalTheory.AdTh.VecFock.vec_fock_ofCore D G Pl0 T0 A T.Q.c.F R F hC i A.μ0 hV
  have hON : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ => by
    refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩
    · simp [gramAt, hV.1]
    · simp
  have hinjP := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) (hC.thP.ωP i A.μ0).std hC.models.inf
    (fun _ => 1) (fun _ => 1) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) _ f4 f3 hON f5
    (D.sp.V_sig _) (D.sp.W_sig _) (R.vP i A.μ0) f1 f2 (GlobalTheory.AdTh.VecNe.thetaVector_ne_zero_of_core D G Pl0 T0 A T.Q.c.F R F hC i hV)
  have hlti : Function.Injective lt := GlobalTheory.PtId.OneScalar.lt_injective (fun ρ => hT.laws.pins.1.2.2.2 ρ) lt hlt
  refine smul_left_injective ℂ (fun h0 => hne ?_) e2
  have h1 := hinjP (h0.trans (map_zero _).symm)
  have h2 := MvPolynomial.rename_injective lt hlti (h1.trans (map_zero _).symm)
  exact MvPolynomial.map_injective _ (inC O.c').injective (h2.trans (map_zero _).symm)


open GlobalTheory.AdTh.CoverVal in
theorem covAt_of_xiConst_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ c0 : ℂ, GlobalTheory.OneMapTuples.XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → GlobalTheory.PtId.CovAt O c0 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i Tp tup O hO c0 hc
    t X g bas idx e k xk mk hX hp hs hi hL hxk hmk hk y₂ A₂ hA₂
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc t
  obtain ⟨hlev, hA, -⟩ := hO.cov t
  obtain ⟨hX₀, hon₀, -, hp₀, -, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_ofCore D G Pl0 T0 A T R F κ v₀ hR hT i O.s0
    (sOv_eq _ _ _) (T.dict _ O.s0 1).1
  have hσ : GoodEmb (O.dδ t).c₂ ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((O.U₂ t).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((O.U₂ t).X j) (T.x₀ ((i : ℕ) + 1) O.s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  obtain ⟨Wt⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU)
  obtain ⟨hon, γ, ⟨hγ, hl, hf⟩, hma, -⟩ := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (O.U₂ t) hσ hU h1 hA R.θ (Wc D i)
    (rank_Wc i) (O.dict₂ t) (iotaW T i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt k
  obtain ⟨hd, hpt⟩ := point_eq (Formalism.L2.PjFree.Unf.ofPj (O.U₂ t)) hσ hU h1 hA hR.models.inf (Wc D i) (rank_Wc i) (iotaW T i)
    _ Wt (O.dict₂ t k).1 (O.dict₂ t k).2 γ k hγ (hmod _) hl hf hon hma X g bas idx e mk hX hp hs hi hL hmk hk y₂ A₂ hA₂
  obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 k
  obtain ⟨-, -, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  obtain ⟨a, ha⟩ := hrat γ' hγ'
  have hv := hval k γ' ⟨hγ', h2, h3⟩
  rw [(hO.tuple t).xi _ _ (hmul _ _ _ _ ha hxk), map_mul, (hR.lev.xi (tup t)).1.2 a, _root_.one_mul] at hv
  exact (evR_eq_of_point _ hlev.2.2.2.2.2.2.2.1 _ y₂ hpt).trans ((dif_pos hd).symm.trans hv)


set_option maxHeartbeats 2000000 in
open Formalism.L2.DIV GlobalTheory.OneMapTuples GlobalTheory.PtId in
theorem point_identity_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → IoExt R → ∀ (i : Fin D.R.m) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ (lam : AutQ (Wc D i) → ℂ) (z : G), (∀ q, lam q ≠ 0) ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → O.lev = lev → CoefficientBaseChange R i O.jL (inC O.c') (c0L i) O.c0' → ∀ c0 : ℂ, XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → PtIdent O (κ i) lam z c0 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ _ ⟨tie⟩ _ hio i lev gramR c0R c0L _
  have hT : TieIn T R κ v₀ := ⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)
  swap
  · exact ⟨fun _ => 1, 1, fun _ => one_ne_zero, fun Tp tup O _ hP => absurd ⟨Tp, tup, O, hP⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀⟩ := hex
  obtain ⟨ka, hka1, hka⟩ := exists_scalar_core D G Pl0 T0 A T R F κ v₀ hC hT hio i (c0L i)
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.AdTh.CcEx.exists_ccIs_ofCore GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R F κ v₀ hC hT i Tp₀ tup₀ O₀ hP₀
  have hs₀ : O₀.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨hemb, hiso, -⟩ := dict_cast T hT.laws _ (inR i) O₀.s0 (hs₀ ▸ T.toCore.good_σ₀) (Wc D i) O₀.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := GlobalTheory.AdTh.ShortSeries.thetaKO_eq_short_series_ofCore D G Pl0 T0 A _ R F hC i hP₀.lift.std _ _ (iotaW T i) hemb hiso
  refine ⟨fun q => cmpConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * c₀ (O₀.dict q.out).1, 1, fun q => ?_, ?_⟩
  · exact mul_ne_zero (cmpConst_ne_zero (norm_ne_zero_iff.1 (hka1 ▸ one_ne_zero)) _ _)
      (norm_ne_zero_iff.1 (hc₀.1 _ ▸ one_ne_zero))
  intro Tp tup O _ hP _ hbc c0 hxi t
  obtain ⟨cst, hcst, hceq⟩ := ccIs_transport (hs₀.trans (sOv_eq _ O.c' O.hle).symm) O₀.hV O.hV hc₀
  refine ⟨1, one_mem _, ⟨1, Nat.one_pos, one_pow _⟩, fun x hx f hf hcl q => ?_⟩
  obtain ⟨h, J', hR, -, hA, hPl⟩ := (hP.tuple t).reps
  obtain ⟨x₀, hx₀⟩ := (hPl x).1 hx
  have hL := hP.act.2
  have h1 : actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2 1 f = f :=
    actL_one _ _ _ hL.total hL.func hL.one hf.1
  have h2 := exact_identity_ofCore hC hT O hP (hka Tp tup O hP hbc) hδ
    (covAt_of_xiConst_core D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hP c0 hxi) hcst t h J' hR _ x hx₀ f hcl q.out
  rw [rdQ, h1, hA _ x hx₀, one_mul]
  exact h2.trans (congrArg (fun z => _ * z * _) (hceq q.out))

end GlobalTheory.PtIdCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGrowthOnComponentNsmul
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Filter
open scoped ENNReal NNReal

namespace GlobalTheory.GrowthMul

theorem limsup_le_iSup_classes {a : ℕ} (ha : 1 ≤ a) (f : ℕ → ℝ≥0∞) :
    limsup f atTop ≤ ⨆ j : Fin a, limsup (fun k => f (a * k + j)) atTop := by
  refine le_of_forall_gt_imp_ge_of_dense fun x hx => ?_
  have h1 : ∀ j : Fin a, ∀ᶠ k in atTop, f (a * k + j) < x := fun j =>
    eventually_lt_of_limsup_lt ((le_iSup (fun j : Fin a => limsup (fun k => f (a * k + j)) atTop) j).trans_lt hx)
  choose K hK using fun j => eventually_atTop.1 (h1 j)
  refine limsup_le_of_le (by isBoundedDefault) (eventually_atTop.2 ⟨a * Finset.univ.sup K, fun τ hτ => ?_⟩)
  have hm : τ % a < a := Nat.mod_lt _ (by omega)
  have hq : Finset.univ.sup K ≤ τ / a := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hτ)
  have := hK ⟨τ % a, hm⟩ (τ / a) ((Finset.le_sup (Finset.mem_univ _)).trans hq)
  rw [Nat.div_add_mod] at this
  exact this.le

theorem term_mul_eq (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞) {k : ℕ} (hk : 1 ≤ k) :
    (D.factorial : ℝ≥0∞) * (r (a * k) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D =
      (a : ℝ≥0∞) ^ D * ((D.factorial : ℝ≥0∞) * (r (a * k) : ℝ≥0∞) / ((a * k : ℕ) : ℝ≥0∞) ^ D) := by
  have ha0 : (a : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  rw [Nat.cast_mul, mul_pow, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ ha0 hat, mul_comm]

theorem growth_mul_le (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞) :
    growth D (fun k => r (a * k)) ≤ (a : ℝ≥0∞) ^ D * growth D r := by
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  set g : ℕ → ℝ≥0∞ := fun τ => (D.factorial : ℝ≥0∞) * (r τ : ℝ≥0∞) / (τ : ℝ≥0∞) ^ D
  have h1 : growth D (fun k => r (a * k)) = limsup (fun k => (a : ℝ≥0∞) ^ D * g (a * k)) atTop :=
    limsup_congr ((eventually_ge_atTop 1).mono fun k hk => term_mul_eq D ha r hk)
  rw [h1, ENNReal.limsup_const_mul_of_ne_top hat, growth]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le)
  have ht : Tendsto (fun k : ℕ => a * k) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega)
  exact (limsup_comp g (fun k => a * k) atTop).le.trans (limsup_le_limsup_of_le ht)

theorem limsup_class_le (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞) (j c : ℕ)
    (h : ∀ k, r (a * k + j) ≤ r (a * (k + c))) :
    limsup (fun k => (D.factorial : ℝ≥0∞) * (r (a * k + j) : ℝ≥0∞) / ((a * k + j : ℕ) : ℝ≥0∞) ^ D) atTop ≤
      ((a : ℝ≥0∞) ^ D)⁻¹ * growth D (fun k => r (a * k)) := by
  have ha0 : (a : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hit : ((a : ℝ≥0∞) ^ D)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 ha0
  refine (limsup_le_limsup ((eventually_ge_atTop 1).mono fun k hk => ?_)).trans
    ((ENNReal.limsup_const_mul_of_ne_top hit).le.trans (by gcongr; exact GlobalTheory.GrowthShift.growth_shift_le D c _))
  show _ ≤ ((a : ℝ≥0∞) ^ D)⁻¹ * ((D.factorial : ℝ≥0∞) * (r (a * (k + c)) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D)
  have hk0 : (k : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hkt : (k : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  have e : ((a : ℝ≥0∞) ^ D)⁻¹ * ((D.factorial : ℝ≥0∞) * (r (a * (k + c)) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D) =
      (D.factorial : ℝ≥0∞) * (r (a * (k + c)) : ℝ≥0∞) / ((a : ℝ≥0∞) ^ D * (k : ℝ≥0∞) ^ D) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl ha0) (Or.inl hat)]
    ring
  rw [e]
  refine ENNReal.div_le_div (by gcongr; exact h k) ?_
  rw [← mul_pow]
  gcongr
  exact_mod_cast Nat.le_add_right _ _

theorem growth_mul_eq_of_classes (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞)
    (h : ∀ j, j < a → ∃ c, ∀ k, r (a * k + j) ≤ r (a * (k + c))) :
    growth D (fun k => r (a * k)) = (a : ℝ≥0∞) ^ D * growth D r := by
  refine le_antisymm (growth_mul_le D ha r) ?_
  have ha0 : (a : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  have h1 : growth D r ≤ ((a : ℝ≥0∞) ^ D)⁻¹ * growth D (fun k => r (a * k)) := by
    refine (limsup_le_iSup_classes ha _).trans (iSup_le fun j => ?_)
    obtain ⟨c, hc⟩ := h j j.2
    exact limsup_class_le D ha r j c hc
  calc (a : ℝ≥0∞) ^ D * growth D r ≤ (a : ℝ≥0∞) ^ D * (((a : ℝ≥0∞) ^ D)⁻¹ * growth D (fun k => r (a * k))) :=
        mul_le_mul_of_nonneg_left h1 zero_le
    _ = growth D (fun k => r (a * k)) := by rw [← mul_assoc, ENNReal.mul_inv_cancel ha0 hat, one_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem pow_mul_mem_cuspOn {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) {τ₀ τ : ℕ} {g f : Rul Xo c}
    (hg : g ∈ cuspOn U Z (τ₀ • G)) (hf : f ∈ cuspOn U Z (τ • G)) (n : ℕ) :
    g ^ n * f ∈ cuspOn U Z ((τ + n * τ₀) • G) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have e : (τ + (n + 1) * τ₀) • G = (τ + n * τ₀) • G + τ₀ • G := by rw [← add_nsmul]; ring_nf
    rw [e, pow_succ, mul_right_comm]
    exact GlobalTheory.DegTop.mul_mem_cuspOn (GlobalTheory.DegTop.even_nsmul hG _) (GlobalTheory.DegTop.even_nsmul hG _) ih hg.1

set_option synthInstance.maxHeartbeats 100000 in
theorem rank_le_of_ne_zero {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) {τ₀ : ℕ} {g : Rul Xo c}
    (hg : g ∈ cuspOn U Z (τ₀ • G)) (hg0 : g ≠ 0) (τ n : ℕ) :
    Module.rank c.F (cuspOn U Z (τ • G)) ≤ Module.rank c.F (cuspOn U Z ((τ + n * τ₀) • G)) := by
  have hv : genVal Z g ≠ 0 := fun h0 => hg0 (GlobalTheory.DegTop.eq_zero_of_genVal hg h0)
  let m := (genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F (g ^ n)
  have hpow : genVal Z (g ^ n) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hv
  have hinj : Function.Injective (m ∘ₗ (cuspOn U Z (τ • G)).subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
      rw [injective_iff_map_eq_zero]
    intro f hf
    have hzero : genVal Z (g ^ n * f) = 0 := hf
    rw [map_mul] at hzero
    exact Subtype.ext (GlobalTheory.DegTop.eq_zero_of_genVal f.2
      ((mul_eq_zero.1 hzero).resolve_left hpow))
  have hrank : Module.rank c.F ((cuspOn U Z (τ • G)).map m) =
      Module.rank c.F (cuspOn U Z (τ • G)) := by
    rw [← rank_range_of_injective _ hinj, LinearMap.range_comp, Submodule.range_subtype]
  rw [← hrank]
  refine (Submodule.rank_mono ?_).trans (rank_map_le (genVal Z).toLinearMap _)
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨_, pow_mul_mem_cuspOn hG hg hf n, rfl⟩

theorem classes_bound (Z : Comp Xo c) {G : WTZ E} (hG : Even G.2) {a : ℕ} (ha : 1 ≤ a) (j : ℕ) :
    ∃ c' : ℕ, ∀ k, Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k + j) • G))) ≤
      Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * (k + c')) • G))) := by
  by_cases hex : ∃ q : ℕ, ∃ g ∈ cuspOn U Z ((a * q + j) • G), g ≠ 0
  · obtain ⟨q, g, hg, hg0⟩ := hex
    refine ⟨j + (a - 1) * q, fun k => ?_⟩
    have e : a * (k + (j + (a - 1) * q)) = (a * k + j) + (a - 1) * (a * q + j) := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [e]
    exact OrderHomClass.mono Cardinal.toENat (rank_le_of_ne_zero hG hg hg0 _ _)
  · push_neg at hex
    refine ⟨0, fun k => ?_⟩
    have h0 : cuspOn U Z ((a * k + j) • G) = ⊥ := (Submodule.eq_bot_iff _).2 (hex k)
    rw [h0, rank_bot, map_zero]
    exact zero_le

end GlobalTheory.GrowthMul

theorem GlobalTheory.GrowthMul.growthOn_nsmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G : WTZ E), Even G.2 → ∀ a : ℕ, 1 ≤ a → growthOn U Z (a • G) = (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
  intro E _ _ _ H Dw l Xo c r U _ Z G hG a ha
  rw [growthOn, growthOn]
  convert GlobalTheory.GrowthMul.growth_mul_eq_of_classes (dimFlag Dw) ha (fun τ => Cardinal.toENat (Module.rank c.F (cuspOn U Z (τ • G))))
    (fun j _ => GlobalTheory.GrowthMul.classes_bound (U := U) Z hG ha j) using 4 with τ
  rw [smul_smul, mul_comm]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledStabilizerWeilOperatorTransportsLatticeEiStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledStabilizer_weilOperator_transports_latticeEigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    ∀ (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ₁
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ₁)) := by
  first | exact @GlobalTheory.DblVacTransport.transport | exact GlobalTheory.DblVacTransport.transport | (intros; apply GlobalTheory.DblVacTransport.transport <;> assumption)
end

