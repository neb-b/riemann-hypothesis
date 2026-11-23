module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryFactorFiniteSetOfPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.PlaceCut

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι : Type} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem glue_mul {e : R} (he : e * e = e) (a b c d : Matrix ι ι A) :
    (e • a + (1 - e) • b) * (e • c + (1 - e) • d) = e • (a * c) + (1 - e) • (b * d) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, h2, mul_one, sub_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, h1, h2, h3,
    zero_smul, add_zero, zero_add]

omit [Fintype ι] [DecidableEq ι] in
theorem glue_self (e : R) (a : Matrix ι ι A) : e • a + (1 - e) • a = a := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem exists_glue (c : A →ₐ[R] A) (J : Matrix ι ι A) {e : R} (he : e * e = e) (g h : GlobalTheory.WeilM.UG c J) :
    ∃ p : GlobalTheory.WeilM.UG c J, (p.1.1 : Matrix ι ι A) = e • g.1.1 + (1 - e) • h.1.1 ∧
      ((p⁻¹).1.1 : Matrix ι ι A) = e • (g⁻¹).1.1 + (1 - e) • (h⁻¹).1.1 := by
  let q : GL ι A :=
    { val := e • g.1.1 + (1 - e) • h.1.1
      inv := e • g.1.2 + (1 - e) • h.1.2
      val_inv := by rw [glue_mul he, g.1.3, h.1.3, glue_self]
      inv_val := by rw [glue_mul he, g.1.4, h.1.4, glue_self] }
  have hq : q ∈ GlobalTheory.WeilM.UG c J := by
    have hg : (g.1.1)ᵀ * J * (g.1.1).map c = J := g.2
    have hh : (h.1.1)ᵀ * J * (h.1.1).map c = J := h.2
    show (e • g.1.1 + (1 - e) • h.1.1)ᵀ * J * (e • g.1.1 + (1 - e) • h.1.1).map c = J
    have m : (e • g.1.1 + (1 - e) • h.1.1).map c = e • (g.1.1).map c + (1 - e) • (h.1.1).map c := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_smul]
    rw [m, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul]
    have k := glue_mul he (g.1.1)ᵀ (h.1.1)ᵀ J J
    rw [glue_self] at k
    rw [k, glue_mul he, hg, hh, glue_self]
  exact ⟨⟨q, hq⟩, rfl, rfl⟩

end Alg

theorem exists_idem {F : Type} [Field F] [NumberField F] (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) :
    ∃ e : AF F, e * e = e ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F e = 0 ∧ (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w e = 1) ∧
      (∀ w ∉ S, GlobalTheory.AdelicU.evFin F w e = 0) ∧
      ∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u * e = 0 := by
  classical
  let b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F := ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v 1
  have hb1 : ∀ w ∈ S, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w b = 1 := by
    intro w hw
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single_of_mem w hw, GlobalTheory.AdelicU.evalV_singleFin_self]
    intro v _ hv
    exact GlobalTheory.AdelicU.evalV_singleFin_ne hv.symm 1
  have hb0 : ∀ w ∉ S, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w b = 0 := by
    intro w hw
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun v hv => GlobalTheory.AdelicU.evalV_singleFin_ne ?_ 1
    rintro rfl
    exact hw hv
  refine ⟨((0 : Ainf F), b), ?_, ?_, hb1, hb0, ?_⟩
  · refine Prod.ext (by change (0 : Ainf F) * 0 = 0; exact mul_zero _) ?_
    change b * b = b
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w ∈ S
    · rw [hb1 w hw, mul_one]
    · rw [hb0 w hw, mul_zero]
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  · intro u hu
    refine Prod.ext (by change u.1 * 0 = 0; exact mul_zero _) ?_
    change u.2 * b = 0
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul, map_zero]
    by_cases hw : w ∈ S
    · have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w u.2 = 0 := hu w hw
      rw [this, zero_mul]
    · rw [hb0 w hw, mul_zero]

theorem exists_cut : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))),
    ∃ gS k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J, g = gS * k ∧
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) ∧
      (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
        u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1)) ∧
      (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z) := by
  intro F E _ _ _ _ _ σ n X g S
  obtain ⟨e, he, heI, he1, he0, heu⟩ := exists_idem S
  obtain ⟨gS, hS, -⟩ := exists_glue (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) he g 1
  obtain ⟨k, hk, hk'⟩ := exists_glue (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) he 1 g
  have hS2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS = e • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g + (1 - e) • 1 := hS
  have hk2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k = e • 1 + (1 - e) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g := hk
  have hk3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ = e • 1 + (1 - e) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ := by
    rw [inv_one] at hk'
    exact hk'
  have hoff : ∀ (u : AF F) (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), u * e = 0 →
      u • (e • (1 : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + (1 - e) • M) = u • M := by
    intro u M hu
    rw [smul_add, smul_smul, smul_smul, mul_sub, hu, mul_one, sub_zero, zero_smul, zero_add]
  refine ⟨gS, k, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k
    rw [hS2, hk2, glue_mul he, Matrix.mul_one, Matrix.one_mul, glue_self]
  · intro u hu
    rw [hS2, smul_sub, smul_add, smul_smul, smul_smul, mul_sub, heu u hu, mul_one, sub_zero, zero_smul, zero_add,
      sub_self]
  · intro w hw u hu
    have h1 : (1 - e) * u = 0 := hu (1 - e) (by rw [map_sub, map_one, he1 w hw, sub_self])
    have h2 : u * (1 - e) = 0 := by rw [mul_comm, h1]
    have h3 : u * e = u := by rw [mul_sub, mul_one, sub_eq_zero] at h2; exact h2.symm
    rw [hk2, smul_sub, smul_add, smul_smul, smul_smul, h2, h3, zero_smul, add_zero, sub_self]
  · intro u hu
    have h1 : e * u = 0 := hu e heI
    rw [hk2, smul_sub, smul_sub, hoff u _ (by rw [mul_comm, h1])]
  · intro w hw z hz
    have key : ∀ M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
        (e • (1 : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + (1 - e) • M) *ᵥ z = M *ᵥ z := by
      intro M
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, -, y, -, rfl⟩ := hz
        have h1 : e * a = 0 := ha e (he0 w hw)
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec,
          hoff a M (by rw [mul_comm, h1])]
      | zero => rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, Matrix.mulVec_add, hx, hy]
      | neg x _ hx => rw [Matrix.mulVec_neg, Matrix.mulVec_neg, hx]
    rw [hk2, hk3]
    exact ⟨key _, key _⟩

end GlobalTheory.PlaceCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchOperatorUnitaryWSeesaw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchFactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def liftI (t : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)

end GlobalTheory.ArchFactor

end

namespace GlobalTheory.ArchFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem evI_add' (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul' (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem comm_offI {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    {χX χW : Chr F E} {om : Rep σ X W} (hw : M.IsWeil ψ χX χW om) (x : UA σ X.J × UA σ W.J)
    (hx1 : x.1 ∈ UAt σ X (evI F)) (hx2 : x.2 ∈ UAt σ W (evI F))
    (u : AF F) (hu : evI F u = 0) (p q : Fin n × Fin d → AF F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    om x (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (om x Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  set w := M.co.e.symm (p, q) with hw'
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw', LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h1 : u • (mat x.1 - 1) = 0 := hx1 u hu
  have h2 : u • (mat x.2 - 1) = 0 := hx2 u hu
  have e1 : mat x.1 * (u • w) = u • w := by
    have : mat x.1 * (u • w) - u • w = (u • (mat x.1 - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h1, Matrix.zero_mul, sub_eq_zero] at this
    exact this
  have e2 : (u • w) * (mat x.2)ᵀ = u • w := by
    have : (u • w) * (mat x.2)ᵀ - u • w = w * (u • (mat x.2 - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : GlobalTheory.WeilM.actAB (cA σ) x (u • w) = u • w := by
    simp only [GlobalTheory.WeilM.actAB]
    have := e1
    simp only [mat] at this e2
    rw [this, e2]
  have h3 := hW.impl x (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

theorem schr_trans' (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (w : κ → AF F) (Φ : (κ → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

end GlobalTheory.ArchFactor


open GlobalTheory.ArchFactor in
theorem GlobalTheory.ArchFactor.exists_archOperator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ h ∈ UAt σ G.W (evI F),
    ∃ T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')), ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, h)) f (T f) := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT h hh
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), om (1, h) Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (1, h) Φ hΦ
  have h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evI F) := by
    intro u _
    simp [mat]
  have hcomm := comm_offI hT.weil (1, h) h1 hh
  obtain ⟨R, hR0, hR⟩ := _root_.GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin a × Fin (a + a'))
  have hB : ∀ f : SInf F (Fin a × Fin (a + a')), ∃ g : SInf F (Fin a × Fin (a + a')),
      ∀ t, g t = (R 0)⁻¹ * om (1, h) (tens (evI F) (⇑f) R) (liftI t) := by
    intro f
    obtain ⟨g, hg⟩ := _root_.GlobalTheory.ArchSlice.exists_schwartz_slice _ (Submodule.smul_mem _ (R 0)⁻¹ (hkeep _ (hR f).2))
    exact ⟨g, fun t => by rw [hg]; rfl⟩
  choose Tf hTf using hB
  have htens_add : ∀ f g : SInf F (Fin a × Fin (a + a')),
      tens (evI F) (⇑(f + g)) R = tens (evI F) (⇑f) R + tens (evI F) (⇑g) R := by
    intro f g; funext x; simp only [tens, SchwartzMap.add_apply, Pi.add_apply]; ring
  have htens_smul : ∀ (c : ℂ) (f : SInf F (Fin a × Fin (a + a'))),
      tens (evI F) (⇑(c • f)) R = c • tens (evI F) (⇑f) R := by
    intro c f; funext x; simp only [tens, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]; ring
  let T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    { toFun := Tf
      map_add' := fun f g => by
        ext t
        rw [SchwartzMap.add_apply, hTf, hTf, hTf, htens_add, map_add (f := _), Pi.add_apply]; ring
      map_smul' := fun c f => by
        ext t
        rw [SchwartzMap.smul_apply, hTf, hTf, htens_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          RingHom.id_apply]; ring }
  refine ⟨T, fun f r hr => ?_⟩
  funext y
  set T0 := om (1, h) with hT0
  set u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) with hudef
  have hu : evI F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  set p : Fin a × Fin (a + a') → AF F := liftI (fun i => evI F (y i)) with hpdef
  have hyp : y + u • (-y) = p := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef, liftI, evI,
      RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_
    · show (y i).1 + 0 * (-(y i)).1 = (y i).1
      simp
    · show (y i).2 + 1 * (-(y i)).2 = 0
      rw [one_mul]
      exact add_neg_cancel ((y i).2)
  have hpat : At (evI F) p := by
    intro u' hu'
    have h0 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu')
    funext i
    refine Prod.ext ?_ ?_
    · show u'.1 * (p i).1 = 0
      rw [h0, zero_mul]
    · show u'.2 * (p i).2 = 0
      simp [hpdef, liftI]
  set Φ₀ := tens (evI F) (⇑f) R with hΦ₀
  set Φ₁ := tens (evI F) (⇑f) r with hΦ₁
  set Φ₂ : (Fin a × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR f).2
  have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hfz : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
    have hpz : At (evI F) (p + z) := fun u' hu' => by
      rw [smul_add, hpat u' hu', hz u' hu', add_zero]
    have e3 : R (p + z) = R 0 := by simpa using (hR f).1 0 (p + z) hpz
    have e4 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add', evI_mul', hu, zero_mul, add_zero]
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
    rw [e4, e2, e3, e1]
    field_simp
    ring
  have h0 := _root_.GlobalTheory.FinFibre.fibre_zero B.ψ T0 hT.base.std hkeep (fun u hu p q Φ hΦ => hcomm u hu p q Φ hΦ) (Φ₁ - Φ₂)
    (sub_mem hr.2 hm₂) y hfz
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have htr : T0 (fun w => Φ₀ (w + u • (-y))) = fun w => T0 Φ₀ (w + u • (-y)) := by
    have h := hcomm u hu (-y) 0 Φ₀ hm₀
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  have h2 : T0 Φ₂ y = (r y / R 0) * T0 Φ₀ p := by
    rw [hΦ₂, map_smul, htr, Pi.smul_apply, smul_eq_mul, hyp]
  show T0 Φ₁ y = tens (evI F) (⇑(Tf f)) r y
  rw [h0, h2]
  show r y / R 0 * T0 Φ₀ p = (Tf f) (fun i => evI F (y i)) * r y
  rw [hTf]
  show r y / R 0 * T0 Φ₀ p = (R 0)⁻¹ * T0 Φ₀ p * r y
  rw [div_eq_mul_inv]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergDerivativeArchimedeanDirection
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree


open scoped Classical in
theorem GlobalTheory.HeisLineDeriv.exists_actsD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
      ∃ g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) g g₁ :=
  fun M ψ hψ g u hu => by
    obtain ⟨D, hD⟩ := GlobalTheory.HeisDeriv.exists_actsD_heisLine M ψ hψ u hu
    exact ⟨D g, hD g⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoordinateOfRationalPointDefiniteVeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryCoordinate_of_rationalPoint_definiteVertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ r : FinPt G X, GlobalTheory.MovedKappaEx.RatFin (G.V X) r →
    ∃ U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E, GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U := by
  first | exact @GlobalTheory.RatMoveJets.exists_unitary_ratCoord | exact GlobalTheory.RatMoveJets.exists_unitary_ratCoord | (intros; apply GlobalTheory.RatMoveJets.exists_unitary_ratCoord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasCtpId
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.PlaceDecomp

variable {D : D7}

def TyOf (θ : InfFam D) (N : GlobalTheory.Grid.Node D) {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) : D.what₂.Tau → (GA D N.V → ℂ) → Prop :=
  fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f

def HasCtp (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop)
    (τ : D.what₂.Tau) (T : N.M.H τ → N.M.H τ) : Prop :=
  ∃ A : (GA D N.V → ℂ) → (GA D N.V → ℂ), GlobalTheory.KFinDecomp.IsOpAt θ N (GlobalTheory.KFinDecomp.Cls θ N U) Ty τ A ∧
    ∀ φ ∈ GlobalTheory.KFinDecomp.Cls θ N U, GlobalTheory.SeriesToClosure.Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) T φ (A φ)

theorem hasCtp_id (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop)
    (τ : D.what₂.Tau) : HasCtp θ N U Ty τ id :=
  ⟨id, GlobalTheory.KFinDecomp.isOpAt_id θ N _ Ty τ, fun _ _ _ _ _ _ _ _ _ h => h⟩

end GlobalTheory.PlaceDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutMemLatticeStabilizerOfProductLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentCut_mem_latticeStabilizer_of_productLevel : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    {n' : P → ℕ} (h : ∀ w, n' w = n) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (x : GL (Fin n) (Lev.EAf D)),
    x ∈ prodLev β P h K → ∀ (b : Lev.EAf D) (hb : b * b = b),
    (∀ w : Pl D.host.E, (∃ PP ∈ P, w.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.StdFrames.cpt (D := D) w b = 0) →
    GlobalTheory.UnitaryIdemCut.cutGL b hb x ∈ St β := by
  first | exact @GlobalTheory.CutProdLev.cutGL_mem_St_of_mem_prodLev | exact GlobalTheory.CutProdLev.cutGL_mem_St_of_mem_prodLev | (intros; apply GlobalTheory.CutProdLev.cutGL_mem_St_of_mem_prodLev <;> assumption)
end

