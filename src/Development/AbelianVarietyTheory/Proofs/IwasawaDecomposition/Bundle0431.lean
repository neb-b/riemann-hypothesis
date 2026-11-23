module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.DualLattices.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepParametersPartitionExtendedByZeros
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsOfThetaDatumInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCoefficientCompatibility
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLastStepRealIntertwiner
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompactHowe.LastStep

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem Jm_allPos (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  simp [Formalism.REAL.Jm, allPos]

theorem fr_det (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (M.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)

def inFr (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  M.fr τ * g * (M.fr τ)⁻¹

theorem inFr_one (M : DSModel V S) (τ : D.what₂.Tau) : inFr M τ 1 = 1 := by
  rw [inFr, Matrix.mul_one, Matrix.mul_nonsing_inv _ (fr_det M τ)]

theorem det_inFr (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (inFr M τ g).det = g.det := by
  rw [inFr, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    Matrix.mul_nonsing_inv _ (fr_det M τ), Matrix.det_one, one_mul]

theorem inFr_mem (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : inFr M τ g ∈ UJset (M.ε τ) := by
  have h : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h1 := Matrix.mul_nonsing_inv _ (fr_det M τ)
  have h2 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (inFr M τ g)ᴴ * Formalism.REAL.Jm (M.ε τ) * inFr M τ g = Formalism.REAL.Jm (M.ε τ)
  calc (inFr M τ g)ᴴ * Formalism.REAL.Jm (M.ε τ) * inFr M τ g
      = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [inFr, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        rw [M.fr_gram, h, ← M.fr_gram]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem cart_eq_one (M : DSModel V S) (h : ∀ τ, M.ε τ = allPos V.rank) : cart M = fun _ => 1 := by
  funext τ
  rw [cart, h, Jm_allPos, Matrix.mul_one, Matrix.nonsing_inv_mul _ (fr_det M τ)]

theorem isCartan_one (M : DSModel V S) (h : ∀ τ, M.ε τ = allPos V.rank) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) 1 := by
  refine ⟨Matrix.mul_one _, by simp, ?_⟩
  rw [Matrix.mul_one, ← M.fr_gram, h, Jm_allPos]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 (M.fr_unit τ))

def polAct (M : DSModel V S) (M' : DSModel W S') (x₁ x₃ : D.what₂.Tau → ℤ)
    (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (φ : PolF D W.rank V.rank) : PolF D W.rank V.rank :=
  (∏ τ, (inFr M' τ (h τ)).det ^ x₁ τ * (inFr M τ (g τ)).det ^ x₃ τ) •
    substF (fun τ => inFr M' τ (h τ)) (fun τ => ((inFr M τ (g τ))⁻¹)ᵀ) φ

theorem totalDegree_polAct (M : DSModel V S) (M' : DSModel W S') (x₁ x₃ : D.what₂.Tau → ℤ) (g h φ) :
    (polAct M M' x₁ x₃ g h φ).totalDegree ≤ φ.totalDegree :=
  (MvPolynomial.totalDegree_smul_le _ _).trans (totalDegree_substF_le _ _ _)

theorem om_ptOf {k : Fin D.R.m} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) (hV : V.SigOK) (hW : W.SigOK)
    (M : DSModel V S) (M' : DSModel W S') (hε : ∀ τ, M.ε τ = allPos V.rank) (hε' : ∀ τ, M'.ε τ = allPos W.rank)
    (x₁ x₃ : D.what₂.Tau → ℤ) (h1 : ∀ τ, (x₁ τ : ℚ) = expS D k τ + (V.rank : ℚ) / 2)
    (h3 : ∀ τ, (x₃ τ : ℚ) = -((W.rank : ℚ) / 2 + expT D k τ))
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsStepWeil k ψ V W ω) {f : WO V W → ℂ}
    (hf : IsVacVec ψ θ M M' f) {g : GA D V} (hg : g ∈ GinfC V) {h : GA D W} (hh : h ∈ GinfC W) (φ : PolF D W.rank V.rank) :
    ω (g, h) (ptOf ψ θ M M' f φ) = ptOf ψ θ M M' f
      (polAct M M' x₁ x₃ (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) (fun τ => compAt θ τ (Formalism.L2.Theta.mt W h)) φ) := by
  obtain ⟨χS, χT, hw, he⟩ := hω
  have hv := hf.vac
  unfold ptOf
  rw [cart_eq_one M hε, cart_eq_one M' hε'] at hv ⊢
  have e1 := _root_.GlobalTheory.VacuumCharacter.vacuum_character D ψ θ V W χS χT ω hw hθ hV hW (fun _ => 1) (isCartan_one M hε) (isCartan_one M' hε')
    _ _ (fun τ => (he τ).1) (fun τ => (he τ).2) x₁ (fun τ => x₁ τ - V.rank) x₃ h1
    (fun τ => by push_cast; rw [h1]; ring)
    (fun τ => by
      have := congrArg (fun q : ℚ => (q : ℂ)) (h3 τ)
      simp only [Matrix.trace_one, Fintype.card_fin]
      push_cast at this
      exact this)
    f hf.theta hv g hg h hh (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
  have e2 := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χS χT ω hw hθ (fun _ => 1) (fun _ => 1) (onb M)
    (fun τ => onb M τ * inFr M τ (compAt θ τ (Formalism.L2.Theta.mt V g))) (fun _ => 1) (fun _ => 1) (onb M')
    (fun τ => onb M' τ * inFr M' τ (compAt θ τ (Formalism.L2.Theta.mt W h))) g h
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by
      rw [onb, inFr, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (fr_det M τ)])
    (fun τ => by
      rw [onb, inFr, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (fr_det M' τ)]) f hf.theta φ).2
  rw [e2, e1, GlobalTheory.FiniteFock.pureTensorO_smul, GlobalTheory.T.fockPolynomialVector_basisChange_eq_substitution D ψ θ V W hw.std hθ _ _ _ _ f hf.theta, polAct, map_smul]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have a1 : (1 / 2 : ℂ) • ((1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) + 1) = 1 := by module
  rw [det_inFr, det_inFr, a1, sub_self, smul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, Matrix.det_one,
    _root_.one_zpow, mul_one]

open Classical in
theorem compAt_atTau {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V τ g))) = Function.update (fun _ => 1) τ g := by
  have h := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  funext ρ
  by_cases e : ρ = τ
  · subst e
    rw [Function.update_self]
    exact h.2.1
  · rw [Function.update_of_ne e]
    exact h.2.2 ρ e

theorem compAt_one (θ : InfFam D) : (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt V 1)) = fun _ => 1 :=
  funext fun ρ => GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)

theorem rep_one (M : DSModel V S) (τ : D.what₂.Tau) : M.σ τ (inFr M τ 1) = 1 := by
  rw [inFr_one]
  exact (M.ds τ).2.2.1.1.1

open Classical in
theorem map_update (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    PiTensorProduct.map (fun ρ => (M.σ ρ (inFr M ρ (Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ)) : M.H ρ →ₗ[ℂ] M.H ρ)) =
      actT M τ g := by
  unfold actT
  congr 1
  funext ρ
  by_cases e : ρ = τ
  · subst e
    rw [Function.update_self, Function.update_self]
    rfl
  · rw [Function.update_of_ne e, Function.update_of_ne e, rep_one]
    rfl

theorem map_one' (M : DSModel V S) :
    PiTensorProduct.map (fun ρ => (M.σ ρ (inFr M ρ 1) : M.H ρ →ₗ[ℂ] M.H ρ)) = LinearMap.id := by
  rw [← PiTensorProduct.map_id]
  congr 1
  funext ρ
  rw [rep_one]
  rfl

open Classical in
theorem update_mem (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (ρ : D.what₂.Tau) : Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ ∈
      Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  by_cases e : ρ = τ
  · subst e
    rwa [Function.update_self]
  · rw [Function.update_of_ne e]
    exact GlobalTheory.PointAtPlaceHom.one_mem_UH _


open Classical in
theorem exists_it (k : Fin D.R.m) (hk : (k : ℕ) + 1 = D.R.m) (a : ℕ) (ha : a = k) (hV : V.SigOK) (hW : W.SigOK)
    (rV : V.rank = D.R.r + k * D.R.t) (rW : W.rank = V.rank + D.R.t)
    (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) D.R.m)) (θ : InfFam D) (hθ : IsInfFam θ)
    (ψ : AddChar (AF D.host.F) ℂ) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      ∀ ω f, IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  subst ha
  have hp := fun τ => _root_.GlobalTheory.LastStepParam.lastStep_param D k τ V.rank W.rank (M.lam τ) (M.ε τ) (M'.lam τ) (M'.ε τ) hk rV rW (M.enum τ) (M'.enum τ)
  have hε := fun τ => (hp τ).1
  have hε' := fun τ => (hp τ).2.1
  choose x₁ x₃ h1 h3 hn ν n1 n2 n3 n4 using fun τ => (hp τ).2.2
  have m := fun τ => _root_.GlobalTheory.CompactModel.model_allPos D V _ M τ (hε τ)
  have m' := fun τ => _root_.GlobalTheory.CompactModel.model_allPos D W _ M' τ (hε' τ)
  have hl := fun τ =>
    haveI := (m τ).1
    haveI := (m' τ).1
    _root_.GlobalTheory.CompactHowe.exists_local_contraction W.rank V.rank (hn τ) (ν τ) (x₁ τ) (x₃ τ) _ _ (M.H τ) (M.σ τ) (M'.H τ) (M'.σ τ) (n1 τ) (n2 τ) (n3 τ) (n4 τ)
      (m τ).2.2.1 (m τ).2.2.2 (m' τ).2.2.1 (m' τ).2.2.2
  choose I I0 hI using hl
  obtain ⟨J, J0, hJ⟩ := _root_.GlobalTheory.CompactHowe.PolyTensor.exists_tensor D.what₂.Tau W.rank V.rank M'.H M.H I I0
  have key : ∀ (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → (∀ τ, h τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ)) → ∀ φ x,
      J (polAct M M' x₁ x₃ g h φ) (PiTensorProduct.map (fun τ => (M'.σ τ (inFr M' τ (h τ)) : M'.H τ →ₗ[ℂ] M'.H τ)) x) =
        PiTensorProduct.map (fun τ => (M.σ τ (inFr M τ (g τ)) : M.H τ →ₗ[ℂ] M.H τ)) (J φ x) := fun g h hg hh =>
    hJ _ _ _ _ _ fun τ P v => hI τ _ (hε' τ ▸ inFr_mem M' τ (hh τ)) _ (hε τ ▸ inFr_mem M τ (hg τ)) P v
  obtain ⟨It, hIt⟩ := _root_.GlobalTheory.CompactIntertwiner.exists_isItW D V W _ _ θ M M' J
    (fun τ g => polAct M M' x₁ x₃ (Function.update (fun _ => 1) τ g) fun _ => 1)
    (fun τ h => polAct M M' x₁ x₃ (fun _ => 1) (Function.update (fun _ => 1) τ h)) hθ
    (fun τ => ⟨(m τ).1, (m τ).2.1⟩) (fun τ => ⟨(m' τ).1, (m' τ).2.1⟩) J0
    (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _) (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _)
    (fun τ g hg φ x => by
      have := key _ (fun _ => 1) (update_mem τ hg) (fun _ => GlobalTheory.PointAtPlaceHom.one_mem_UH _) φ x
      rwa [map_update, map_one'] at this)
    (fun τ h hh φ x => by
      have := key (fun _ => 1) _ (fun _ => GlobalTheory.PointAtPlaceHom.one_mem_UH _) (update_mem τ hh) φ x
      rwa [map_update, map_one'] at this)
  refine ⟨It, fun ω f hω hf => hIt ω (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f)
    (_root_.GlobalTheory.FockInj.ptOf_injective D V W _ _ ψ θ M M' f hω.choose_spec.choose_spec.1.std hθ hf) (fun τ g hg φ => ?_) fun τ h hh φ => ?_⟩
  · have := om_ptOf hθ hV hW M M' hε hε' x₁ x₃ h1 h3 hω hf (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) V τ g) (one_mem _) φ
    rwa [compAt_atTau hθ τ hg, compAt_one] at this
  · have := om_ptOf hθ hV hW M M' hε hε' x₁ x₃ h1 h3 hω hf (one_mem _) (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) W τ h) φ
    rwa [compAt_atTau hθ τ hh, compAt_one] at this

theorem lastStep_intertwiner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.chain_ωX → R.chain_vX → R.chain_ptX ∧ ∃ It, ({ R with ItX := It } : RealDat D A Ks).chain_ItX := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL _ hM hω hv
  have hm := D.R.two_le_m
  let k : Fin D.R.m := ⟨D.R.m - 1, by omega⟩
  have hk : (k : ℕ) = D.R.m - 1 := rfl
  have hS := fun t => _root_.GlobalTheory.LastStepVac.last_step D G Pl0 T A Ks R hL hM.inf hω hv t k hk
  have rV : (Yc D (D.R.m - 1)).rank = D.R.r + k * D.R.t := by
    rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left (Nat.sub_le _ _)]; rfl
  have rW : D.sp.X'.rank = (Yc D (D.R.m - 1)).rank + D.R.t := by
    rw [rV, D.sp.X'_rank, Ranks.rankX', add_assoc, ← Nat.succ_mul]
    congr 2
    omega
  refine ⟨fun t P => ?_, ?_⟩
  · exact (GlobalTheory.OrientedHeis.om_pureTensorO D R.ψ R.θ _ _ _ _ (R.ωX t) (hω t) hM.inf _ (cart (R.MY (D.R.m - 1))) _
      (fun τ => compAt R.θ τ (Formalism.L2.Theta.mt _ 1) * onb (R.MY (D.R.m - 1)) τ) _ (cart R.MX) _
      (fun τ => compAt R.θ τ (Formalism.L2.Theta.mt _ 1) * onb R.MX τ) 1 1
      (fun τ => by rw [congrFun (compAt_one R.θ) τ, Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [congrFun (compAt_one R.θ) τ, Matrix.one_mul, Matrix.mul_one])
      (fun _ => rfl) (fun _ => rfl) (R.vX t) (hS t).2.theta P).1
  · obtain ⟨It, hIt⟩ := exists_it k (by omega) (min (D.R.m - 1) D.R.m) (by omega) (D.sp.Y_sig _) D.sp.X'_sig rV rW
      (R.MY (D.R.m - 1)) R.MX R.θ hM.inf R.ψ
    exact ⟨It, fun t => hIt (R.ωX t) (R.vX t) (hS t).1 (hS t).2⟩

end GlobalTheory.CompactHowe.LastStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinnedPre

open GlobalTheory.PinnedData

variable {D : D7}

theorem exists_char_field (S : Finset (Pl D.host.E)) : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ PP ∈ S, ∀ (ξ : (kP PP)ˣ →* ℂˣ) (x : (kP PP)ˣ), ((ξ x : ℂˣ) : ℂ) ∈ M := by
  have hf : ∀ PP : Pl D.host.E, 0 < Nat.card (kP PP)ˣ := fun PP => by
    have : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
    exact Nat.card_pos
  obtain ⟨M, hM, h⟩ := GlobalTheory.Mem.FrameVal.exists_roots (∏ PP ∈ S, Nat.card (kP PP)ˣ) (Finset.prod_pos fun PP _ => hf PP)
  refine ⟨M, hM, fun PP hPP ξ x => h _ ?_⟩
  obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Nat.card (kP PP)ˣ) hPP
  rw [hu, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, one_pow]

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Data

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)


set_option maxHeartbeats 1000000 in
theorem exists_phi (hR : GlobalTheory.RealGeo.PreChar R) (hV : VStd D i) (t : T0) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (hι : LatEmb (Wc D i) ι) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ M' : IntermediateField ℚ ℂ, M ≤ M' →
      (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) →
      ∀ J : Ideal (𝓞 D.host.E),
        (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) →
        ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M',
          PhiIs R i M'.val.toRingHom t ι (J • ⊤) φ := by
  obtain ⟨M, hM, hv⟩ := exists_omega_field R.Pg (R.Q t)
  refine ⟨M, hM, fun M' hle hP J hJ => ?_⟩
  obtain ⟨-, e, he, -⟩ := hR.thP.vP i t
  have hβ := _root_.GlobalTheory.StdFrameInv.isIntM_inv D i _ _ hV (hR.lev.βV i)
  have hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    rowP_int _ _ _ (hR.lev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _
      (hι.2.le (LinearMap.mem_range_self ι x)) a
  refine ⟨fun q => ⟨_, hle (hv (Wc D i).rank (R.xiR t) (-1) fun PP => redM PP
    (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out))⟩, e, he, fun x =>
    ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩
  exact omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _
    fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)


set_option maxHeartbeats 1000000 in
theorem exists_thAd (hR : R.IsModels) (t : T0) {K' : Type} [Field K'] {σ' : K' →+* ℂ}
    (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) {Cl : Type} (h : Cl → GA D (Vc D i)) {J' : Subgroup (Bridge.Gf (Vc D i))}
    (hle : J' ≤ levJ R i t) (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => FWT.fin _ (h k)))
    (v₀ : (R.MW i (sg0 D A)).Vec) : ∃ thAd, ThAdIs R i t h c0' v₀ thAd := by
  classical
  obtain ⟨hinj, hrange, -⟩ := hR.HV i t
  have huniq : ∀ y y' x, Place R i t h c0' y x → Place R i t h c0' y' x → y = y' := fun y y' x h1 h2 =>
    hinj (adForms_ext _ _ _ hle hr (hrange.le (LinearMap.mem_range_self _ y)) (hrange.le (LinearMap.mem_range_self _ y'))
      fun k => (h1 k).trans (h2 k).symm)
  refine ⟨fun x => if hx : ∃ y, Place R i t h c0' y x then onQ (Wc D i) (R.thF i t hx.choose v₀) else 0, fun y x hy => ?_⟩
  have hx : ∃ y, Place R i t h c0' y x := ⟨y, hy⟩
  simp only [dif_pos hx]
  rw [huniq _ _ _ hx.choose_spec hy]


set_option maxHeartbeats 1600000 in
theorem exists_coef (hF : R.IsFam) (hM : R.IsModels) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)
    (hσ : σ'.comp jL = D.what₂.embLL)
    (hv : ∀ t PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (x : (kP PP)ˣ), ((ξ x : ℂˣ) : ℂ) ∈ σ'.fieldRange) :
    ∃ c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W,
      (∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
        (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i jL σ' (c0L i) c0') ∧
      ∀ t (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i t h c0' := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := hF.tie
  obtain ⟨c0', hc⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R.cV i).W) jL σ' hσ (lamV D i) (c0L i)
  exact ⟨c0', ⟨gramR, c0R, c0L, hT, hc⟩, fun t Cl _ h =>
    GlobalTheory.RationalValues.placeEx_of_type_mem R i jL σ' t h c0' hM.jV hT hc
      (GlobalTheory.RationalValues.type_mem R i t _ (fun PP hPP x => hv t PP (Or.inl hPP) _ x) fun PP hPP x => hv t PP (Or.inr hPP) _ x)⟩

end Data

section Level

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)


open GlobalTheory.LevelAction in
theorem exists_levIs (hT : LawsJ T) (hL : R.toLevCh.Is A.μ0) (hpb : T.pb = R.C.P.pb) (i : Fin D.R.m) :
    ∃ lev, LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev := by
  have hβ := hL.βW i
  have hle : ∀ PP ∈ R.Pg, T.Q.l.Mb ≤ PP.asIdeal := by
    intro PP hP
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
    rw [hT.half.2]
    refine (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ k))).trans ?_
    rw [hpb, ← show PP.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact Ideal.map_comap_le
  have hlift : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
    obtain ⟨c, hc⟩ := hβ
    refine _root_.GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP h PP' h' => ?_) (Finset.disjoint_empty_right _)
    rcases h' with h' | h'
    · exact not_isConjPl T.Q.l (hle PP h) (hle PP' h')
    · exact absurd h' (Finset.notMem_empty _)
  have hM : 0 < T.Q.l.M := lt_of_lt_of_le (by norm_num) T.Q.l.three_le
  choose k hk using fun g => hlift (R.eG g)
  choose f hf using fun g => exists_endo (iotaW T i) (GlobalTheory.LevelAction.latEmb_iotaW T hT i) hM
    (finCong_of_mem_St hβ (parLev_St (hk g).2.1))
  exact ⟨f, fun g => ⟨k g, hk g, fun a _ => hf g a⟩⟩


open GlobalTheory.LevelActAnyField in
theorem actLev_of_levIs (hT : LawsJ T) (hL : R.toLevCh.Is A.μ0) (hO : T.pb = R.C.P.pb) (i : Fin D.R.m)
    (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l)
    (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)
    (hlev : LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev) :
    ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) c' (fun g => (lev g,
      (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    have h1 := (hT.pins.2.2.2 _ hj).1
    have h2 := D.R.m_add_three_le_k
    rw [h1]
    simp only [Ranks.sigW]
    omega
  have hA : T.Q.l.A.Coprime T.Q.l.M := by rw [hT.pins.2.1.2]; exact Nat.coprime_one_left _
  have hprod := T.Q.l.prod
  have hMb : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal := by
    refine GlobalTheory.CoverHalf.eq_prod_of_squarefree ?_ _ fun PP => ?_
    · rw [hT.pins.2.1.1] at hprod
      exact (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (T.Q.l.Mb * _)).of_mul_left
    · rw [hL.Pg, hT.half.2, GlobalTheory.CoverHalf.prod_map_le_iff, hO]
      rfl
  have hM : T.Q.l.M ≠ 0 := by have := T.Q.l.three_le; omega
  obtain ⟨h1, hm⟩ := mul_on_half (hL.βW i) (R.datWp i R.triv) (rank_Wc i) (J := Mfr T.Q.l)
    (hMb ▸ hprod) hM (GlobalTheory.PinnedData.latEmb_iotaW T hT i) R.eG.toMonoidHom lev hlev
  exact actLaws_of_action_mod hpq hA _ c' lev (mem_of_half (lev 1 - LinearMap.id) h1)
    fun g g' => mem_of_half (lev (g * g') - lev g ∘ₗ lev g') (hm g g')

end Level


open GlobalTheory.RealGeo in
set_option maxHeartbeats 2000000 in
theorem exists_pins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), PreChar R → TieIn T R κ v₀ → T.pb = R.C.P.pb → Finite T0 → QGuard R → ∀ i : Fin D.R.m, VStd D i → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) := by
  classical
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hR fw hpb hfin hG i hV
  have hT := fw.laws
  obtain ⟨pd, l₂, c₁, h1, h2, hc⟩ := GlobalTheory.TupleCover.exists_covers T R hT hR.lev hpb hG i (Vc D i).rank
  choose Mφ hMφ hφ using fun t => exists_phi R i hR hV t (iotaW T i) (latEmb_iotaW T hT i)
  choose MB hMB hB using fun t => _root_.GlobalTheory.Mem.BVal.exists_field_BIs D G Pl0 T0 A _ R hR.lev i t
  choose MC hMC hC using fun t => exists_char_field (R.Pg ∪ R.Q t)
  have := c₁.fin
  obtain ⟨c', hc'⟩ := GlobalTheory.TupleCover.exists_coeff_ge T.Q.l (c₁.F ⊔ ⨆ t, ((Mφ t ⊔ MB t) ⊔ MC t))
  have h3 : c₁.F ≤ c'.F := le_sup_left.trans hc'
  have h4' : ∀ t, (Mφ t ⊔ MB t) ⊔ MC t ≤ c'.F := fun t =>
    ((le_iSup (fun t => (Mφ t ⊔ MB t) ⊔ MC t) t).trans le_sup_right).trans hc'
  have h4 : ∀ t, Mφ t ⊔ MB t ≤ c'.F := fun t => le_sup_left.trans (h4' t)
  have hle : T.Q.c.F ≤ c'.F := h1.trans h3
  have hLL := h2.trans h3
  obtain ⟨dδ, U₂, dict₂, xi, -, hcov, hhalf, hxi, hcxi, hmod, -⟩ := hc c' hle h3
  let jL : D.what₂.LL →+* c'.F := D.what₂.embLL.codRestrict c'.F fun x => hLL ⟨x, rfl⟩
  have hjL : (inC c').comp jL = D.what₂.embLL := RingHom.ext fun _ => rfl
  obtain ⟨c0', hc0, hplace⟩ := exists_coef R i hR.fam hR.models c'.F jL (inC c') hjL fun t PP hPP ξ x =>
    ⟨⟨_, (le_sup_right.trans (h4' t)) (hC t PP (Finset.mem_union.2 hPP) ξ x)⟩, rfl⟩
  obtain ⟨lev, hlev⟩ := exists_levIs T R hT hR.lev hpb i
  obtain ⟨Cl, fCl, h, J', bad, Lh, gam, vol, La, Nc, hrep, hbad, hcl⟩ :=
    GlobalTheory.SplitReps.exists_repsR_repsCov R i (hR.lev.βV i) hV c'.F (T.Q.Xo ((i : ℕ) + 1)) c' id dδ
  choose B hBis using fun t => hB t c'.F (le_sup_right.trans (h4 t)) (bad t) (hbad t).2.2.2.2
    fun PP hPP => (hrep t).1.2.1 PP (Or.inr hPP)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad t) (B t)).2 fun L cc g d => _root_.GlobalTheory.LawOfSquares.law_of_squares _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  obtain ⟨io, hw, hio⟩ := _root_.GlobalTheory.CoefMapRecord.exists_io_record D T.Q hT.pins κ fw.kap i c'
  choose φ hφis using fun t => hφ t c'.F (le_sup_left.trans (h4 t)) (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => exists_thAd R i hR.models t c0' (h t) (hrep t).1.2.2.1 (hrep t).1.2.2.2.2.2.1 (v₀ i (sg0 D A))
  refine ⟨{ c' := c', hle := hle, jL := jL, hV := hT.spaceW _ (inR i) _ rfl, c0' := c0', lev := lev, dδ := dδ, Cl' := Cl,
            bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := fun t k => epF t (Lh t k), B := B,
            epF := epF, io := io, hw := hw, φ := φ,
            w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
            U₂ := U₂, dict₂ := dict₂, xi := xi, thAd := thAd,
            Plc := fun t x => ∃ x₀, Place R i t (h t) c0' (jVx R i t x₀) x }, hLL,
    ⟨hjL, hV, fw.hv₀ i _, hc0, hlev⟩,
    fun t => ⟨⟨h t, J' t, (hrep t).1, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
    ⟨actLev_of_levIs T R hT hR.lev hpb i _ lev hlev, actLev_of_levIs T R hT hR.lev hpb i _ lev hlev⟩,
    hbad, hcl, fun t => ⟨fun _ => rfl, hepF t⟩, hio, fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩

end GlobalTheory.PinnedPre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupIndepFiniteTypeComponentsThetaLiftFormsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iSupIndep_finiteTypeComponents_thetaLiftForms : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ i : Fin D.R.m, iSupIndep (fun σ : D.what₂.FT => D.what₂.isot ((i : ℕ) + 1) σ) := by
  first | exact @GlobalTheory.Mem.R3.IsotIndep.isot_iSupIndep | exact GlobalTheory.Mem.R3.IsotIndep.isot_iSupIndep | (intros; apply GlobalTheory.Mem.R3.IsotIndep.isot_iSupIndep <;> assumption)
end

