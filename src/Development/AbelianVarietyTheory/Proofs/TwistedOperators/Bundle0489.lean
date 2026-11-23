module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdPartialEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X Y : ι → Type} (T : ∀ i, (X i → ℂ) →ₗ[ℂ] (Y i → ℂ)) {δ : Type}

theorem sum_prod_partial_eq_zero (s : Finset δ) (a : δ → ℂ) (F : δ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ s, a d * ∏ i, F d i (x i) = 0) (A : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) :
    ∑ d ∈ s, a d * ((∏ i ∈ A, T i (F d i) (y i)) * ∏ i ∈ Aᶜ, F d i (x i)) = 0 := by
  induction A using Finset.induction_on generalizing x with
  | empty => simpa using h x
  | @insert b A hb ih =>
    set c : δ → ℂ := fun d => a d * ((∏ i ∈ A, T i (F d i) (y i)) * ∏ i ∈ (insert b A)ᶜ, F d i (x i)) with hc
    have hbA : b ∈ Aᶜ := Finset.mem_compl.2 hb
    have hcompl : (insert b A)ᶜ = (Aᶜ).erase b := by
      ext i; simp [Finset.mem_erase, and_comm]
    have hφ : (∑ d ∈ s, c d • F d b) = 0 := by
      funext z
      have := ih (Function.update x b z)
      rw [Finset.sum_apply, Pi.zero_apply, ← this]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hc, ← Finset.mul_prod_erase _ _ hbA, Function.update_self, hcompl]
      have : ∏ i ∈ (Aᶜ).erase b, F d i (Function.update x b z i) = ∏ i ∈ (Aᶜ).erase b, F d i (x i) :=
        Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [this]; ring
    have h2 := congrArg (fun f => T b f (y b)) hφ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.prod_insert hb, hc]; ring

theorem sum_prod_map_eq_zero (s : Finset δ) (a : δ → ℂ) (F : δ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ s, a d * ∏ i, F d i (x i) = 0) (y : ∀ i, Y i) :
    ∑ d ∈ s, a d * ∏ i, T i (F d i) (y i) = 0 := by
  by_cases hX : Nonempty (∀ i, X i)
  · obtain ⟨x⟩ := hX
    simpa using sum_prod_partial_eq_zero T s a F h Finset.univ x y
  · have hi : ∃ i, IsEmpty (X i) := by
      by_contra hn
      push_neg at hn
      exact hX ⟨fun i => Classical.choice (hn i)⟩
    obtain ⟨i, hi⟩ := hi
    have h0 : ∀ f : X i → ℂ, f = 0 := fun f => funext fun z => hi.elim z
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0 (F d i), map_zero]; rfl), mul_zero]

theorem sum_prod_map_congr {δ' : Type} (s : Finset δ) (s' : Finset δ') (a : δ → ℂ) (a' : δ' → ℂ) (F : δ → ∀ i, X i → ℂ)
    (F' : δ' → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ s', a' d * ∏ i, F' d i (x i) = ∑ d ∈ s, a d * ∏ i, F d i (x i)) (y : ∀ i, Y i) :
    ∑ d ∈ s', a' d * ∏ i, T i (F' d i) (y i) = ∑ d ∈ s, a d * ∏ i, T i (F d i) (y i) := by
  have key := sum_prod_map_eq_zero T (s'.disjSum s) (Sum.elim a' fun d => -a d) (Sum.elim F' F) (fun x => by
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, h x, add_neg_cancel]) y
  rw [Finset.sum_disjSum] at key
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
  exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact key)

end Tensor

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def stdLatO (S : GridChoice W U) (p : Pair T) : AddSubgroup (WO (G.pS p) (G.pT p)) :=
  latO (G.pS p) (G.pT p) (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E)) (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E))
    fun _ => True

def movedFn (_S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) → ℂ :=
  Function.update (Function.update (fun j' => (d.1 j').fn) ⟨j, by omega⟩
      fun x => (d.1 ⟨j, by omega⟩).fn (actO _ _ 1⁻¹ (g : GA D (G.V (.top (j + 1))))⁻¹ x))
    ⟨j + 1, hj⟩ fun x => (d.1 ⟨j + 1, hj⟩).fn (actO _ _ (g : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x)

theorem vec_eq_model (S : GridChoice W U) {t : T} {p : Pair T} (d : FinDatum G t p) (hz : d.z = 1) (hv : S.Z.HasVec d)
    (Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ))
    (hTm : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) d.e (stdLatO S p) 1 (S.Z.vac p) Tm) : S.Z.vec d = Tm d.fn := by
  obtain ⟨f, hf⟩ := hv
  rw [Normal.vec, FinDatum.vec_eq W hf, hz, ← hf.2 Tm hTm]
  rw [show ((1 : GA D (G.pS p)), (1 : GA D (G.pT p))) = 1 from rfl, map_one]
  rfl

end GlobalTheory.ExpansionInvariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumReImAddSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7}

theorem sum_re_im_add_smul {m n a b : ℕ} (U V : Fin a → Fin b → Matrix (Fin m) (Fin n) ℂ) (z e : Fin a → Fin b → ℂ)
    (t : ℝ) :
    ∑ i, ∑ j, ((((z i j + t • e i j).re : ℝ) : ℂ) • U i j + (((z i j + t • e i j).im : ℝ) : ℂ) • V i j) =
      ∑ i, ∑ j, ((((z i j).re : ℝ) : ℂ) • U i j + (((z i j).im : ℝ) : ℂ) • V i j) +
        t • ∑ i, ∑ j, ((((e i j).re : ℝ) : ℂ) • U i j + (((e i j).im : ℝ) : ℂ) • V i j) := by
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_mul, add_smul, smul_add, mul_smul, Complex.coe_smul]
  abel

theorem fmR_add_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank)
    (t : ℝ) : fmR A B (z + t • e) = fmR A B z + t • fmR A B e := by
  funext τ
  exact sum_re_im_add_smul _ _ (z τ) (e τ) t

theorem heis_dRho_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (z e : VCx D.what₂.Tau S.rank T.rank) (τ : D.what₂.Tau) (v : Matrix (Fin T.rank) (Fin S.rank) ℂ), GlobalTheory.FockTransl.Jet.fmR A B e τ = v → (∀ τ', τ' ≠ τ → GlobalTheory.FockTransl.Jet.fmR A B e τ' = 0) → heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ v h) x = deriv (fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * Complex.I) * ((t * GlobalTheory.FockTransl.Jet.omF A B z e : ℝ) : ℂ)) * heisO ψ S T (fockPt σ A B (z + t • e)) h x) 0 := by
  intro D ψ θ σ hψ hC S T A B h x z e τ v hv h0
  have hux : GlobalTheory.AdForm.JetRead.ux τ v = fmR A B e := by
    funext τ' i j
    unfold GlobalTheory.AdForm.JetRead.ux
    split_ifs with hτ
    · subst hτ; rw [← hv]
    · rw [h0 τ' hτ]; rfl
  have hline : ∀ t : ℝ, (lineAt θ τ v t : WO S T) = iotaW σ T S (t • fmR A B e) := fun t => by
    rw [GlobalTheory.AdForm.JetRead.lineAt_eq hC, hux]
  have hfun : (fun t : ℝ => ψ (symplOH S T x (fockPt σ A B z)) *
      heisO ψ S T (lineAt θ τ v t) h (x + fockPt σ A B z)) = fun t : ℝ =>
      Complex.exp (-((Real.pi : ℂ) * Complex.I) * ((t * omF A B z e : ℝ) : ℂ)) *
        heisO ψ S T (fockPt σ A B (z + t • e)) h x := by
    funext t
    have e1 : ψ (symplOH S T x (fockPt σ A B z)) * heisO ψ S T (lineAt θ τ v t) h (x + fockPt σ A B z) =
        heisO ψ S T (fockPt σ A B z) (heisO ψ S T (lineAt θ τ v t) h) x := rfl
    have e2 : fockPt σ A B z = iotaW σ T S (fmR A B z) := rfl
    have e3 : fockPt σ A B (z + t • e) = iotaW σ T S (fmR A B z) + iotaW σ T S (t • fmR A B e) := by
      rw [← AddMonoidHom.map_add (f := _), ← fmR_add_smul]; rfl
    rw [e1, GlobalTheory.OrientedHeis.heisO_heisO, Pi.smul_apply, smul_eq_mul, hline, e3, e2,
      GlobalTheory.OrientedHeis.psi_symplOH hC hψ, hC.pi_iota, LinearMap.map_smul, smul_eq_mul]
    rfl
  show ψ (symplOH S T x (fockPt σ A B z)) *
      deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ v t) h (x + fockPt σ A B z)) 0 = _
  rw [← deriv_const_mul_field, hfun]

end GlobalTheory.FockTransl.Jet

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7}

theorem GQ_negGA_mem (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  obtain ⟨x, hx, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, e⟩)
  have hx' : Formalism.UG.cT _ (x : Matrix _ _ _) * V.gram * (x : Matrix _ _ _) = V.gram := hx
  show Formalism.UG.cT _ (x : Matrix _ _ _) * (-V.gram) * (x : Matrix _ _ _) = -V.gram
  rw [Matrix.mul_neg, Matrix.neg_mul, hx']

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_GQ (p : Pair T) {γ : GA D (G.V p.small)} {γ' : GA D (G.V p.big)} (hγ : γ ∈ GQ (G.V p.small))
    (hγ' : γ' ∈ GQ (G.V p.big)) : (G.toPair p γ γ').1 ∈ GQ (G.pS p) ∧ (G.toPair p γ γ').2 ∈ GQ (G.pT p) := by
  cases p with
  | chi i j => exact ⟨GQ_negGA_mem _ hγ', hγ⟩
  | mu t i j => exact ⟨hγ, hγ'⟩
  | core i => exact ⟨GQ_negGA_mem _ hγ', hγ⟩
  | top t j => exact ⟨hγ, hγ'⟩

theorem ker_rat_left : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T),
    p.InRange D.R.m →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ (G.pS p) (G.pT p) f → ∀ γ ∈ GQ (G.V p.small), ∀ γ' ∈ GQ (G.V p.big),
    ∀ g h, W.ker p f (γ * g) (γ' * h) = W.ker p f g h := by
  intro D T L sc G W p hp f hf γ hγ γ' hγ' g h
  have hw := W.om_is p hp
  obtain ⟨h1, h2⟩ := toPair_GQ p hγ hγ'
  have e : W.ker p f (γ * g) (γ' * h) =
      W.om p (G.toPair p γ γ') (W.om p (G.toPair p g h) f) 0 := by
    simp only [GridData.Weil.ker, thetaKO, toPair_mul, Prod.mk.eta, map_mul, Module.End.mul_apply]
  rw [e]
  have := hw.om_aut _ h1 _ h2 (W.om p (G.toPair p g h) f) (hw.om_pres (G.toPair p g h) f hf)
  rw [Prod.mk.eta] at this
  rw [this]
  simp only [GridData.Weil.ker, thetaKO, Prod.mk.eta]

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
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

namespace GlobalTheory.ThetaTransformInj

theorem linear_injective : ∀ (D : D7) {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d), Mo.IsGood ψ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → Y.J.det ≠ 0 → Z.J.det ≠ 0 → G.det ≠ 0 →
    ∃ T : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ),
      (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ) ∧
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = 0 → Φ = 0 := by
  intro D m k d Y Z Mo ψ G e _ hψ _ _ hG
  have hGG : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹ = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), Matrix.map_one _ (map_zero _) (map_one _)]
  have hsur : ∀ u, ∃ x, GlobalTheory.TripleRead.ptO G e x = u := by
    intro u
    refine ⟨(HMul.hMul (u.submatrix id e.symm)ᵀ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G) : Matrix (Fin d) (Fin m) (AE D)), ?_⟩
    simp only [GlobalTheory.TripleRead.ptO, Matrix.mul_assoc, hGG, Matrix.mul_one, Matrix.transpose_transpose]
    ext i j
    simp
  have hadd : ∀ (u : Matrix (Fin m) (Fin k) (AE D)) (Φ Ψ : (Fin m × Fin k → AF D.host.F) → ℂ),
      Mo.co.rho ψ u (Φ + Ψ) = Mo.co.rho ψ u Φ + Mo.co.rho ψ u Ψ := by
    intro u Φ Ψ
    funext y
    simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]
  have hsmul : ∀ (u : Matrix (Fin m) (Fin k) (AE D)) (c : ℂ) (Φ : (Fin m × Fin k → AF D.host.F) → ℂ),
      Mo.co.rho ψ u (c • Φ) = c • Mo.co.rho ψ u Φ := by
    intro u c Φ
    funext y
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
    ring
  let f : GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ) :=
    { toFun := fun Φ => GlobalTheory.TripleRead.thO Mo ψ G e Φ.1
      map_add' := fun Φ Ψ => by
        funext x
        simp only [GlobalTheory.TripleRead.thO, Submodule.coe_add, Pi.add_apply, hadd]
        exact GlobalTheory.WeilM.thetaSum_add _ (GlobalTheory.HeisSchA.rho_mem_schA Mo ψ hψ _ _ Φ.2)
          (GlobalTheory.HeisSchA.rho_mem_schA Mo ψ hψ _ _ Ψ.2)
      map_smul' := fun c Φ => by
        funext x
        simp only [GlobalTheory.TripleRead.thO, Submodule.coe_smul, Pi.smul_apply, hsmul, smul_eq_mul, RingHom.id_apply]
        exact GlobalTheory.WeilM.thetaSum_smul _ c _ }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend f
  have hTf : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ := by
    intro Φ hΦ
    exact LinearMap.congr_fun hT ⟨Φ, hΦ⟩
  refine ⟨T, hTf, fun Φ hΦ h0 => ?_⟩
  rw [hTf Φ hΦ] at h0
  refine GlobalTheory.ThetaInj.theta_inj Mo ψ hψ (fun u => u) Φ 0 (fun _ => 0) ⟨hΦ, fun u => ?_⟩
    ⟨Submodule.zero_mem _, fun u => ?_⟩
  · obtain ⟨x, rfl⟩ := hsur u
    exact congrFun h0 x
  · simp [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

end GlobalTheory.ThetaTransformInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransferBottom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

theorem triIs_congr {D : D7} {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ ψ' : AddChar (AF D.host.F) ℂ} {θ θ' : InfFam D}
    {α α' β β' : T → ((AE D)ˣ →* Circle)} {ν ν' : T → Formalism.L2.Host.HChar D.host.E} {S S' : T → Finset (Pl D.host.E)}
    (h : X.Is ψ θ α β ν S) (e1 : ψ' = ψ) (e2 : θ' = θ) (e3 : ∀ t, α' t = α t) (e4 : ∀ t, β' t = β t) (e5 : ∀ t, ν' t = ν t)
    (e6 : ∀ t, S' t = S t) : X.Is ψ' θ' α' β' ν' S' := by
  obtain rfl := e1
  obtain rfl := e2
  obtain rfl := funext e3
  obtain rfl := funext e4
  obtain rfl := funext e5
  obtain rfl := funext e6
  exact h


set_option maxHeartbeats 1000000 in
theorem trBot_holds : TrBot := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA M σ hB
  obtain ⟨hl, hg, hw, -⟩ := hA
  have pre := hl.pre
  cases X with | mk B C Wr V Sg N Gj =>
  cases X' with | mk B' C' Wr' V' Sg' N' Gj' =>
  cases B
  cases B'
  dsimp only at pre
  subst pre
  let DX := GlobalTheory.Mem.Stages.toD7 ⟨_, C, Wr, V, Sg, N, Gj⟩
  let DX' := GlobalTheory.Mem.Stages.toD7 ⟨_, C', Wr', V', Sg', N', Gj'⟩
  obtain ⟨f, f', hff, hC, hC'⟩ := hl.C
  obtain rfl : f' = f := eq_of_heq hff
  have hψ : W'.ψ = (by with_unfolding_all exact (W.ψ :)) := eq_of_heq hw.ψ
  have hθ : W'.θ = (by with_unfolding_all exact (W.θ :)) := eq_of_heq hw.θ
  have hxiH : ∀ t, L'.xiH t = (by with_unfolding_all exact ((L.xiH (ι t)) :)) := fun t => eq_of_heq (hl.xi t)
  have hQ : ∀ t, L'.Q t = (by with_unfolding_all exact ((L.Q (ι t)) :)) := fun t => eq_of_heq (hl.Q t)
  have hchi : G'.ch.chi = (by with_unfolding_all exact (G.ch.chi :)) := eq_of_heq hg.chi
  have hchiH : G'.ch.chiH = (by with_unfolding_all exact (G.ch.chiH :)) := eq_of_heq hg.chiH
  have hv0 : G'.pl.v0 = (by with_unfolding_all exact (G.pl.v0 :)) := eq_of_heq hg.v0
  have hwp : G'.pl.w = (by with_unfolding_all exact (G.pl.w :)) := eq_of_heq hg.w
  have hCmu : ∀ j, L'.C.mu0 j = (by with_unfolding_all exact ((L.C.mu0 j) :)) := fun j => by
    have a : L.C.mu0 j = f'.mu0 j := by rw [hC]; rfl
    have b : L'.C.mu0 j = f'.mu0 j := by rw [hC']; rfl
    exact b.trans ((by with_unfolding_all exact (a.symm :)))
  have hCeta : L'.C.eta = (by with_unfolding_all exact (L.C.eta :)) := by
    have a : L.C.eta = f'.eta := by rw [hC]; rfl
    have b : L'.C.eta = f'.eta := by rw [hC']; rfl
    exact b.trans ((by with_unfolding_all exact (a.symm :)))
  have hmu0 : ∀ j : Fin DX'.R.m, L'.mu0 (↑j + 1) = (by with_unfolding_all exact ((L.mu0 (↑j + 1)) :)) := fun j => by
    have h1 : ChrEq ((by with_unfolding_all exact ((L.mu0 (↑j + 1)) :))) (L'.C.mu0 j) := by rw [hCmu j]; exact (by with_unfolding_all exact ((hl.is.mu0 j) :))
    exact (GlobalTheory.ChrEqUnique.chrEq_unique DX').2.1 _ _ _ (hl.is'.mu0 j) h1
  have heta : L'.eta = (by with_unfolding_all exact (L.eta :)) := by
    have h1 : ChrEq ((by with_unfolding_all exact (L.eta :))) L'.C.eta := by rw [hCeta]; exact (by with_unfolding_all exact (hl.is.eta :))
    exact (GlobalTheory.ChrEqUnique.chrEq_unique DX').2.1 _ _ _ hl.is'.eta h1
  have hxi : ∀ t, L'.xi t = (by with_unfolding_all exact ((L.xi (ι t)) :)) := fun t => by
    have h1 : ChrEq ((by with_unfolding_all exact ((L.xi (ι t)) :))) (L'.xiH t) := by rw [hxiH t]; exact (by with_unfolding_all exact ((hl.is.xi (ι t)) :))
    exact (GlobalTheory.ChrEqUnique.chrEq_unique DX').2.1 _ _ _ (hl.is'.xi t) h1

  have thImp : ∀ ψ S T f, @IsThetaFunO DX ψ S T f → @IsThetaFunO DX' ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) :=
    fun ψ S T f h => ⟨(by with_unfolding_all exact (h.quasi :)), (by with_unfolding_all exact (h.level :)), (by with_unfolding_all exact (h.cont :)), (by with_unfolding_all exact (h.smooth :))⟩
  have thImp' : ∀ ψ S T f, @IsThetaFunO DX' ψ S T f → @IsThetaFunO DX ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) :=
    fun ψ S T f h => ⟨(by with_unfolding_all exact (h.quasi :)), (by with_unfolding_all exact (h.level :)), (by with_unfolding_all exact (h.cont :)), (by with_unfolding_all exact (h.smooth :))⟩
  have thEq : @IsThetaFunO DX' = fun ψ S T f => @IsThetaFunO DX ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) := by
    funext ψ S T f
    exact propext ⟨fun h => (by with_unfolding_all exact ((thImp' _ _ _ _ h) :)), fun h => (by with_unfolding_all exact ((thImp _ _ _ _ h) :))⟩
  have wImp : ∀ ψ S T x1 x2 ω, @IsWeilDatumO DX ψ S T x1 x2 ω →
      @IsWeilDatumO DX' ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (ω :))) := fun ψ S T x1 x2 ω h =>
    { std := (by with_unfolding_all exact (h.std :))
      hecS := (by with_unfolding_all exact (h.hecS :))
      hecT := (by with_unfolding_all exact (h.hecT :))
      resS := (by with_unfolding_all exact (h.resS :))
      resT := (by with_unfolding_all exact (h.resT :))
      om_pres := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_pres :))
      om_heis := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_heis :))
      om_aut := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_aut :))
      om_cont := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_cont :))
      om_unit := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_unit :))
      om_split := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_split :)) }
  have vacImp : ∀ ψ θ S T sS sT LS LT f, @IsVacO DX ψ θ S T sS sT LS LT f →
      @IsVacO DX' ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (θ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (sS :))) ((by with_unfolding_all exact (sT :))) ((by with_unfolding_all exact (LS :))) ((by with_unfolding_all exact (LT :))) ((by with_unfolding_all exact (f :))) :=
    fun ψ θ S T sS sT LS LT f h => by
      unfold IsVacO
      rewrite [thEq]
      exact ⟨(by with_unfolding_all exact (h.1 :)), (by with_unfolding_all exact (h.2.inf :)), (by with_unfolding_all exact (h.2.theta :)), (by with_unfolding_all exact (h.2.lat :)), (by with_unfolding_all exact (h.2.fock :)), (by with_unfolding_all exact (h.2.norm :))⟩
  have pmImp : ∀ m n ψ B hs e Λ c f₀ T, @IsPlaceModel DX m n ψ B hs e Λ c f₀ T →
      @IsPlaceModel DX' m n ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (B :))) ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (e :))) ((by with_unfolding_all exact (Λ :))) c ((by with_unfolding_all exact (f₀ :))) ((by with_unfolding_all exact (T :))) :=
    fun m n ψ B hs e Λ c f₀ T h => ⟨(by with_unfolding_all exact (h.trans :)), (by with_unfolding_all exact (h.modul :)), (by with_unfolding_all exact (h.vac :))⟩
  have pmImp' : ∀ m n ψ B hs e Λ c f₀ T, @IsPlaceModel DX' m n ψ B hs e Λ c f₀ T →
      @IsPlaceModel DX m n ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (B :))) ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (e :))) ((by with_unfolding_all exact (Λ :))) c ((by with_unfolding_all exact (f₀ :))) ((by with_unfolding_all exact (T :))) :=
    fun m n ψ B hs e Λ c f₀ T h => ⟨(by with_unfolding_all exact (h.trans :)), (by with_unfolding_all exact (h.modul :)), (by with_unfolding_all exact (h.vac :))⟩
  have pmEq : @IsPlaceModel DX' = fun m n ψ B hs e Λ c f₀ T =>
      @IsPlaceModel DX m n ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (B :))) ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (e :))) ((by with_unfolding_all exact (Λ :))) c ((by with_unfolding_all exact (f₀ :))) ((by with_unfolding_all exact (T :))) := by
    funext m n ψ B hs e Λ c f₀ T
    exact propext ⟨fun h => (by with_unfolding_all exact ((pmImp' _ _ _ _ _ _ _ _ _ _ h) :)), fun h => (by with_unfolding_all exact ((pmImp _ _ _ _ _ _ _ _ _ _ h) :))⟩
  intro i j
  obtain ⟨A, A', WW, Y, hb, hsum⟩ := hB i j
  have hmu : ∀ t, L'.mu t (↑j + 1) = (by with_unfolding_all exact ((L.mu (ι t) (↑j + 1)) :)) := fun t => by
    show L'.mu0 (↑j + 1) * L'.xi t = _
    rw [hmu0 j, hxi t]
    exact (by with_unfolding_all exact ((Eq.refl (L.mu (ι t) (↑j + 1))) :))
  have hnu : ∀ t, SqNum.nuH G' t i j = (by with_unfolding_all exact ((SqNum.nuH G (ι t) i j) :)) := fun t => by
    show L'.C.mu0 j * L'.xiH t / G'.ch.chiH (DX'.R.m - ↑i) = _
    rw [hCmu j, hxiH t, hchiH]
    exact (by with_unfolding_all exact ((Eq.refl (SqNum.nuH G (ι t) i j)) :))
  have hloc : ∀ t, locPl G' t = (by with_unfolding_all exact ((locPl G (ι t)) :)) := fun t => by
    unfold locPl GlobalTheory.ChiGrid.Places.W0 GlobalTheory.ChiGrid.Places.S0
    rw [hQ t, hv0, hwp]
    exact (by with_unfolding_all exact ((Eq.refl (locPl G (ι t))) :))
  refine ⟨A, A', WW,
    ⟨⟨(by with_unfolding_all exact (Y.rA.Λ :)), (by with_unfolding_all exact (Y.rA.β :)), (by with_unfolding_all exact (Y.rA.s :)), (by with_unfolding_all exact (Y.rA.B :))⟩, ⟨(by with_unfolding_all exact (Y.rA'.Λ :)), (by with_unfolding_all exact (Y.rA'.β :)), (by with_unfolding_all exact (Y.rA'.s :)), (by with_unfolding_all exact (Y.rA'.B :))⟩,
      ⟨(by with_unfolding_all exact (Y.rW.Λ :)), (by with_unfolding_all exact (Y.rW.β :)), (by with_unfolding_all exact (Y.rW.s :)), (by with_unfolding_all exact (Y.rW.B :))⟩, fun t => (by with_unfolding_all exact ((Y.ω (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.ω' (ι t)) :)), (by with_unfolding_all exact (Y.vac :)),
      (by with_unfolding_all exact (Y.vac' :)), fun t => (by with_unfolding_all exact ((Y.e (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.c (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.f (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.f' (ι t)) :)),
      (by with_unfolding_all exact (Y.m :)), (by with_unfolding_all exact (Y.fd :)), (by with_unfolding_all exact (Y.m' :)), (by with_unfolding_all exact (Y.fd' :))⟩, ⟨(by with_unfolding_all exact (hb.rank :)), (by with_unfolding_all exact (hb.rank' :)), (by with_unfolding_all exact (hb.std :)), (by with_unfolding_all exact (hb.std' :)), (by with_unfolding_all exact (hb.stdW :)), ?_⟩, ?_⟩
  · have e3 : ∀ t, L'.mu t (↑j + 1) * L'.eta ^ (rankV DX' i j % 2) =
        (by with_unfolding_all exact ((L.mu (ι t) (↑j + 1) * L.eta ^ (rankV DX i j % 2)) :)) := fun t => by
      rw [hmu t, heta]
      exact (by with_unfolding_all exact ((Eq.refl (L.mu (ι t) (↑j + 1) * L.eta ^ (rankV DX i j % 2))) :))
    have e4 : ∀ _ : T', G'.ch.chi (DX'.R.m - ↑i) * L'.eta ^ (rankV DX' i j % 2) =
        (by with_unfolding_all exact ((G.ch.chi (DX.R.m - ↑i) * L.eta ^ (rankV DX i j % 2)) :)) := fun _ => by
      rw [hchi, heta]
      exact (by with_unfolding_all exact ((Eq.refl (G.ch.chi (DX.R.m - ↑i) * L.eta ^ (rankV DX i j % 2))) :))
    refine triIs_congr ?_ hψ hθ e3 e4 hnu hloc
    exact ⟨(by with_unfolding_all exact (hb.is.rank :)), (by with_unfolding_all exact (hb.is.rigA :)), (by with_unfolding_all exact (hb.is.rigA' :)), (by with_unfolding_all exact (hb.is.rigW :)),
      fun t => by unfold GlobalTheory.Grid.IsWeil; exact (by with_unfolding_all exact ((wImp _ _ _ _ _ _ (hb.is.weil (ι t))) :)),
      fun t => by unfold GlobalTheory.Grid.IsWeil; exact (by with_unfolding_all exact ((wImp _ _ _ _ _ _ (hb.is.weil' (ι t))) :)),
      (by with_unfolding_all exact ((vacImp _ _ _ _ _ _ _ _ _ hb.is.isVac) :)), (by with_unfolding_all exact ((vacImp _ _ _ _ _ _ _ _ _ hb.is.isVac') :)),
      fun t => (by with_unfolding_all exact ((hb.is.idem (ι t)) :)), fun t => (by with_unfolding_all exact ((hb.is.expo (ι t)) :)),
      fun t => by unfold IsThetaAt; rewrite [pmEq]; exact (by with_unfolding_all exact ((hb.is.fst (ι t)) :)),
      fun t => by unfold IsThetaAt; rewrite [pmEq]; exact (by with_unfolding_all exact ((hb.is.snd (ι t)) :)),
      (by with_unfolding_all exact (hb.is.meas :)), (by with_unfolding_all exact (hb.is.meas' :))⟩
  · obtain ⟨Ω, Ω', h0, h0', H⟩ := hsum
    refine ⟨Ω, Ω', h0, h0', fun t h hh => ?_⟩
    rw [hψ, hθ]
    have H3 := H (ι t) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (hh :)))
    exact (by with_unfolding_all exact (H3 :))

end GlobalTheory.RowEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeSpanProjectionPreservesFiniteDimInvariantSubStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeSpanProjection_preserves_finiteDim_invariant_subspace : ∀ {M ι : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (G : Submodule ℂ M) (ρ : ι → M →ₗ[ℂ] M)
    (inv : ι → ι), (∀ x ∈ G, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ G, ∀ y ∈ G, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ G, ρ i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, b (ρ i x) y = b x (ρ (inv i) y)) →
    (∀ F : Submodule ℂ M, F ≤ G → FiniteDimensional ℂ F →
      ∃ π : M →ₗ[ℂ] M, (∀ x, π x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (π x) f = b x f) →
    ∀ (Y₀ : Submodule ℂ M) (e : M →ₗ[ℂ] M), (∀ x, e x ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G) →
    (∀ x, ∀ f ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G, b (e x) f = b x f) →
    ∀ Y : Submodule ℂ M, FiniteDimensional ℂ Y → Y ≤ G → (∀ i, ∀ y ∈ Y, ρ i y ∈ Y) → ∀ x ∈ Y, e x ∈ Y := by
  first | exact @GlobalTheory.KTypeProj.typeSpan_proj_mem | exact GlobalTheory.KTypeProj.typeSpan_proj_mem | (intros; apply GlobalTheory.KTypeProj.typeSpan_proj_mem <;> assumption)
end

