module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNegatedSpaceDiscreteSeriesModelTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelInductionFromPairs
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.SepRows GlobalTheory.PairLift GlobalTheory.ChainFr GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowArrow

variable {D : D7}

theorem unit_of_gram {n : ℕ} {G b : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool} (h : bᴴ * G * b = Formalism.REAL.Jm ε) :
    IsUnit b.det := by
  have hJ : IsUnit (Formalism.REAL.Jm ε).det := by
    unfold Formalism.REAL.Jm
    rw [det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num
  rw [← h, det_mul] at hJ
  exact isUnit_of_mul_isUnit_right hJ

theorem inv_gram {n : ℕ} {G b : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool} (h : bᴴ * G * b = Formalism.REAL.Jm ε) :
    (b⁻¹)ᴴ * Formalism.REAL.Jm ε * b⁻¹ = G := by
  have hb := unit_of_gram h
  have h1 : (bᴴ)⁻¹ * bᴴ = 1 := nonsing_inv_mul _ (by rw [det_conjTranspose]; exact hb.star)
  have h2 : b * b⁻¹ = 1 := mul_nonsing_inv _ hb
  rw [← h, conjTranspose_nonsing_inv]
  calc (bᴴ)⁻¹ * (bᴴ * G * b) * b⁻¹ = ((bᴴ)⁻¹ * bᴴ) * G * (b * b⁻¹) := by simp only [Matrix.mul_assoc]
    _ = G := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem exists_frame (V : HSp D) (c b : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : ∀ τ, ∃ ε : Fin V.rank → Bool, (b τ)ᴴ * gramAt D V τ * b τ = Formalism.REAL.Jm ε ∧ c τ * b τ = b τ * Formalism.REAL.Jm ε) :
    ∃ A : Fr V, A.cart = c ∧ A.onb = b := by
  choose ε hε using h
  refine ⟨⟨ε, fun τ => (b τ)⁻¹, fun τ => isUnit_nonsing_inv_iff.2 ((isUnit_iff_isUnit_det _).2 (unit_of_gram (hε τ).1)),
    fun τ => inv_gram (hε τ).1⟩, ?_, ?_⟩
  · funext τ
    simp only [Fr.cart]
    rw [nonsing_inv_nonsing_inv _ (unit_of_gram (hε τ).1), ← (hε τ).2, Matrix.mul_assoc,
      mul_nonsing_inv _ (unit_of_gram (hε τ).1), Matrix.mul_one]
  · funext τ
    simp only [Fr.onb]
    rw [nonsing_inv_nonsing_inv _ (unit_of_gram (hε τ).1)]

theorem lifts_neg {X : ProvA} (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X)
    (hP : PairLifts D X) (hE : PairEx) {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {A B : HSp D} {S S' : D.what₂.Tau → SPar} (MA : DSModel A S) (MB : DSModel B S') {aS aT : D.what₂.Tau → ℚ}
    (hR : ∀ τ, PairPar (GlobalTheory.SignedHC.flip (S' τ)) (S τ) (aS τ) (aT τ)) (FA : Fr A) (FB : Fr B)
    (hA : cart MA = FA.cart) (hB : cart MB = FB.cart) {ω : GlobalTheory.Grid.WRep (GlobalTheory.Grid.sgn true B) A}
    (hω : IsWeilExp ψ (GlobalTheory.Grid.sgn true B) A aS aT ω) {f₀ : WO (GlobalTheory.Grid.sgn true B) A → ℂ}
    (hf₀ : IsVacF ψ θ (frSgn true FB) FA f₀) (h0 : f₀ ≠ 0) {ν : Measure (GA D A)} {𝓕 : Set (GA D A)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 ν) :
    ∃ It : PolF D A.rank B.rank → SmT MA → SmT MB, ∀ f, IsVacF ψ θ (frSgn true FB) FA f →
      LiftsM θ MA MB ν 𝓕 (fun P h g => thetaKO ω ((GlobalTheory.Grid.ofSgn true B).symm h) g (ptF ψ θ (frSgn true FB) FA f P)) It := by
  obtain ⟨N, κ, hN⟩ := GlobalTheory.negModel_tr D θ hθ B S' MB
  have cS : ∀ τ, (Fr.ofModel N).cart τ = (frSgn true FB).cart τ := fun τ =>
    (hN.cart τ).trans ((congrArg _ (congrFun hB τ)).trans (cart_frSgn true FB τ).symm)
  have cT : ∀ τ, (Fr.ofModel MA).cart τ = FA.cart τ := fun τ => congrFun hA τ
  have vac : ∀ f, IsVacF ψ θ (frSgn true FB) FA f → IsVacF ψ θ (Fr.ofModel N) (Fr.ofModel MA) f :=
    fun f h => ⟨h.1, fun τ => by rw [cS, cT]; exact h.2 τ⟩
  obtain ⟨j, hj⟩ := GlobalTheory.FrameChange.ptF_frame_change D ψ θ hψ hθ (GlobalTheory.Grid.sgn true B) A _ _ _ _ cS cT
  obtain ⟨It, hIt⟩ := hE D _ S aS aT hR _ A N MA θ ψ hθ
  have hv : IsVacVec ψ θ N MA f₀ := ⟨hf₀.1, h0, (vac f₀ hf₀).2⟩
  refine ⟨fun P v => κ (It (j P) v), fun f hf F hF => ?_⟩
  obtain ⟨F₁, hF₁, e₁⟩ := hP _ _ aS aT (fun τ => GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 (hR τ)) _ A N MA θ ψ hθ ω hω f₀ It hv
    (hIt ω hω f₀ hv) ν 𝓕 hν h𝓕 f (vac f hf) F hF
  obtain ⟨F', hF', e'⟩ := hN.mult' F₁ hF₁
  refine ⟨F', hF', fun P v h => ?_⟩
  have := e₁ (j P) v ((GlobalTheory.Grid.ofSgn true B).symm h)
  rw [← ptF_ofModel, e'] at this
  simp only [hj f hf.1 P, MulEquiv.apply_symm_apply, RingHom.id_apply] at this
  exact this

theorem cen_eq (τ : D.what₂.Tau) : GlobalTheory.Grid.cen D τ = GlobalTheory.ChiGrid.cen D 1 τ := by
  funext i
  unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
  rw [GlobalTheory.GridJoin.gap_eq_chiGap D]
  rfl

theorem parRow_eq (i : ℕ) (τ : D.what₂.Tau) : parRow D 1 i τ = GlobalTheory.Grid.parV D i 0 τ := by
  have hg : GlobalTheory.Grid.grid D τ = GlobalTheory.ChiGrid.num D 1 τ := by
    unfold GlobalTheory.Grid.grid GlobalTheory.Grid.gridOf GlobalTheory.ChiGrid.num
    rw [cen_eq, GlobalTheory.GridJoin.gap_eq_chiGap D]
    rfl
  rw [GlobalTheory.Grid.parV, hg]
  rfl

theorem exp_att {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {c : ℚ} (h : HasInfExp D χ τ c)
    (hη : HasInfExp D η τ (1 / 2)) (n : ℕ) : HasInfExp D (Lift.attChr χ η n) τ (att c n) := by
  unfold Lift.attChr att
  split_ifs
  · rw [sub_eq_add_neg]
    exact StepVac.hasInfExp_mul h (StepVac.hasInfExp_inv hη)
  · exact h

end GlobalTheory.RowArrow


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftedCuspFormsListed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.StartCusp

open Formalism.IndefR.Mult Matrix Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

variable {D : D7}

theorem hasTypeAll_const_mul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} {Lie Gs : Set (Mx n)} {f : Mx n → ℂ} (c : ℂ) (h : HasTypeAll Lie Gs σ f) :
    HasTypeAll Lie Gs σ fun g => c * f g := by
  obtain ⟨v, h1, ℓ, hℓ, ⟨S, C, hS, h2, h3, B, hB, hc⟩, h4⟩ := hasTypeAll_iff.1 h
  refine hasTypeAll_iff.2 ⟨v, h1, fun i => c • ℓ i, fun i => GlobalTheory.MultMem.sobCont_smul c (hℓ i),
    ⟨S, fun i => ‖c‖ * C i, hS, fun i w hw => ?_, fun S' hS' => ?_, B, hB, hc⟩, fun g hg => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h2 i w hw) (norm_nonneg c)
  · simpa only [mul_assoc] using (h3 S' hS').mul_left ‖c‖
  · simpa only [LinearMap.smul_apply, smul_eq_mul] using (h4 g hg).mul_left c

def TypedBy (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (φ : GA D V → ℂ) : Prop :=
  ∀ x, HasTypeAll (lieOf (gramAt D V τ)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹))
    fun g => φ (x * atTau θ V τ g)

theorem isTypeAt_of_typedBy (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {φ : GA D V → ℂ} (h : TypedBy θ M τ φ) : IsTypeAt θ V τ (S τ) φ :=
  ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, M.ds τ, M.fr_unit τ, M.fr_gram τ, fun x => hasTypeAll_iff.1 (h x)⟩

theorem typedBy_value (θ : InfFam D) (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {Sp : D.what₂.Tau → SPar}
    (M : DSModel V Sp) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec)
    (τ : D.what₂.Tau) : TypedBy θ M τ (T v) := by
  have hD := M.ds τ
  haveI : CompleteSpace (M.H τ) := hD.1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hHC hD
  intro x
  obtain ⟨ℓ, hℓ, hℓv⟩ := hT.cont τ v x
  have hu : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v τ : M.H τ) :=
    GlobalTheory.SmVecModel.smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) ((GlobalTheory.SmVecModel.mem_sm_iff M τ _).1 (v τ).2)
  refine GlobalTheory.CuspValueType.hasTypeAll_single hσ (M.fr_unit τ) (M.fr_gram τ) hu hℓ fun g hg => ?_
  have h1 := hT.equiv τ g hg v ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩ rfl
  have h2 := hℓv ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩
  show ℓ (M.rep τ g (v τ)) = _
  rw [h2, h1]
  rfl

theorem star_lift_isTypeAt (θ : InfFam D) (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) (z : SmT M)
    (τ : D.what₂.Tau) : IsTypeAt θ V τ (dualPar (S τ)) fun g => star (PiTensorProduct.lift T z g) := by
  obtain ⟨M', c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M
  obtain ⟨hsm, hmult⟩ := GlobalTheory.ConjMult.conj_mult θ M M' c hc
  obtain ⟨T', hT'm, hT'⟩ := hmult J χ T hT
  have hT'' := (GlobalTheory.MultMem.mem_mult_iff D θ V _ M' J _ T').1 hT'm
  refine isTypeAt_of_typedBy θ M' τ ?_
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    let f' : M'.Vec := fun ρ => ⟨(c ρ).symm (f ρ), (hsm ρ _).2 (by simp)⟩
    have e : (fun g => star (PiTensorProduct.lift T (r • PiTensorProduct.tprod ℂ f) g)) = fun g => star r * T' f' g := by
      funext g
      rw [hT' f' f (fun ρ => by simp [f']) g, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul, star_mul']
    rw [e]
    intro x
    exact hasTypeAll_const_mul (star r) (typedBy_value θ hHC M' hT'' f' τ x)
  | add a b ha hb =>
    intro x
    have e : (fun g => star (PiTensorProduct.lift T (a + b) (x * atTau θ V τ g))) =
        fun g => star (PiTensorProduct.lift T a (x * atTau θ V τ g)) + star (PiTensorProduct.lift T b (x * atTau θ V τ g)) := by
      funext g
      rw [map_add (f := _), Pi.add_apply, star_add]
    rw [e]
    exact (ha x).add (hb x)

end GlobalTheory.StartCusp

namespace GlobalTheory.StartCusp

open Formalism.IndefR.Mult

variable {D : D7}

theorem isCuspFun_lift {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (z : SmT M) : IsCuspFun V (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact GlobalTheory.MultMem.isCuspFun_add (GlobalTheory.EndCusp.isAutFunSm_lift hT a).toIsAutFun
      (GlobalTheory.EndCusp.isAutFunSm_lift hT b).toIsAutFun ha hb


end GlobalTheory.StartCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingPiCurry
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Topology

noncomputable section
namespace GlobalTheory.ColFourier

section Curry
variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)] {Y : (i : ι) → κ i → Type*}
  [∀ i j, MeasurableSpace (Y i j)]

theorem measurePreserving_piCurry (μ : ∀ i j, Measure (Y i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry Y) (Measure.pi fun p : (i : ι) × κ i => μ p.1 p.2)
      (Measure.pi fun i => Measure.pi fun j => μ i j) := by
  refine ⟨(MeasurableEquiv.piCurry Y).measurable, ?_⟩
  symm
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.univ.pi '' Set.univ.pi fun j => {s : Set (Y i j) | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi fun j => (μ i j).toFiniteSpanningSetsIn) fun s hs => ?_
  choose S hS hSs using hs
  have hpre : (MeasurableEquiv.piCurry Y) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun p : (i : ι) × κ i => S p.1 p.2 := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi, ← hSs, MeasurableEquiv.piCurry_apply, Sigma.forall]
    rfl
  rw [Measure.map_apply (MeasurableEquiv.piCurry Y).measurable (MeasurableSet.univ_pi fun i => by
      rw [← hSs i]; exact MeasurableSet.univ_pi fun j => hS i j (Set.mem_univ j)), hpre, Measure.pi_pi,
    Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hSs i, Measure.pi_pi]

end Curry

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A C : Type*} [Fintype A] [DecidableEq C]


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
def restrictCols (P : Finset C) (X : Matrix A C k) : Matrix A P k := Matrix.of fun i j => X i j

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
@[simp] theorem restrictCols_setCols (P : Finset C) (Y : Matrix A C k) (U : Matrix A P k) :
    restrictCols P (setCols P Y U) = U := by
  ext i j; simp [restrictCols, setCols, j.2]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
@[simp] theorem setCols_restrictCols (P : Finset C) (Y : Matrix A C k) : setCols P Y (restrictCols P Y) = Y := by
  ext i j; by_cases h : j ∈ P <;> simp [restrictCols, setCols, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
@[simp] theorem setCols_setCols (P : Finset C) (Y : Matrix A C k) (U V : Matrix A P k) :
    setCols P (setCols P Y U) V = setCols P Y V := by
  ext i j; by_cases h : j ∈ P <;> simp [setCols, h]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_restrictCols (P : Finset C) : Continuous (restrictCols (k := k) (A := A) P) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (j : C)).comp (continuous_apply i)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_setCols (P : Finset C) (Y : Matrix A C k) : Continuous (setCols P Y) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : j ∈ P
  · simp only [setCols, of_apply, dif_pos h]
    exact (continuous_apply (⟨j, h⟩ : P)).comp (continuous_apply i)
  · simp only [setCols, of_apply, dif_neg h]
    exact continuous_const

theorem comp_setCols_mem_SB {Ξ : Matrix A C k → ℂ} (hΞ : Ξ ∈ SB (Matrix A C k)) (P : Finset C)
    (Y : Matrix A C k) : (fun U => Ξ (setCols P Y U)) ∈ SB (Matrix A P k) := by
  haveI := t2Space k
  refine ⟨hΞ.1.comp_continuous (continuous_setCols P Y),
    HasCompactSupport.intro (hΞ.2.image (continuous_restrictCols P)) fun U hU => ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h => hU ⟨_, h, restrictCols_setCols P Y U⟩

theorem pairCols_eq_dotProduct (P : Finset C) (Y : Matrix A C k) (U : Matrix A P k) :
    pairCols P Y U = (fun p : (_ : A) × P => U p.1 p.2) ⬝ᵥ (fun p : (_ : A) × P => Y p.1 p.2) := by
  simp only [pairCols, dotProduct, Fintype.sum_sigma]

variable [MeasurableSpace k] [BorelSpace k]


omit [DecidableEq C] in
theorem isAddHaarMeasure_volM (m : Measure k) [m.IsAddHaarMeasure] (B : Type*) [Fintype B] :
    (volM m A B).IsAddHaarMeasure := by
  haveI := secondCountable k; haveI := t2Space k
  haveI : (Measure.pi fun _ : B => m).IsAddHaarMeasure := inferInstance
  exact Measure.pi.isAddHaarMeasure (fun _ : A => (Measure.pi fun _ : B => m))


omit [DecidableEq C] in
theorem integral_volM (m : Measure k) [SigmaFinite m] (B : Type*) [Fintype B] (f : Matrix A B k → ℂ) :
    ∫ U, f U ∂(volM m A B) =
      ∫ x : (_ : A) × B → k, f (Matrix.of fun i j => x ⟨i, j⟩) ∂(Measure.pi fun _ => m) := by
  have h := measurePreserving_piCurry (Y := fun (_ : A) (_ : B) => k) (fun _ _ => m)
  exact (h.integral_comp' (g := f)).symm

theorem fourierInt_eq_pi (ψ : AddChar k Circle) (m : Measure k) [SigmaFinite m] (P : Finset C)
    (Φ : Matrix A C k → ℂ) (Y : Matrix A C k) :
    fourierInt ψ m P Φ Y = ∫ x : (_ : A) × P → k, Φ (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩)) *
      (ψ (x ⬝ᵥ fun p => Y p.1 p.2) : ℂ) ∂(Measure.pi fun _ => m) := by
  rw [fourierInt, integral_volM]
  congr 1
  funext x
  rw [pairCols_eq_dotProduct]
  rfl

end GlobalTheory.ColFourier

namespace GlobalTheory.ColFourier
variable {k : Type*} [Field k] [ValuativeRel k]

theorem hasConductor_inv {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) : HasConductor ψ⁻¹ c := fun x => by
  simpa only [AddChar.inv_apply', inv_eq_one] using h x

end GlobalTheory.ColFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

theorem GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ κ : GA D (Yc D 0), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → finE (Yc D 0) κ ∈ St β → (((iotaX X h).toMulEquiv κ).2 ∈ X.K2 ↔ ∀ PP ∈ R.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp β hβ hred κ hK hS
  classical
  obtain ⟨⟨I⟩, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq, lam_eq, ds, low, g_eq, g0_eq, Rph,
    Rph_spec, eX, fY, ee, ff, ef, Lb, Lb_perp, Lam_split, zu, zu_norm, zu_orth, zu_Lb, Fu, Fu_e, flagZVector, Fu_fixed,
    psiEf, psiEf_add, psiEf_int, psiEf_rat, e0, f0, z0, bw, bwd, ew, vectorsInLattice, basisApprox, gramIntegral, formsAtZero, weightVectorsIntegral, ew_idem,
    ew_orth, ew_int, ew_full, bw_w, bwd_w, bw_dual, latticeSpan⟩ := X
  dsimp only at h
  subst h
  dsimp only at g_eq
  subst g_eq
  have hFH : Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd ew :=
    ⟨vectorsInLattice, gramIntegral, formsAtZero, weightVectorsIntegral, ew_orth, bw_w, bwd_w, bw_dual, latticeSpan⟩
  obtain ⟨hgP, hZ⟩ := _root_.GlobalTheory.SeeConjZMod.main R F hIs hGrp
  have hL : (II D).L = Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 := by
    ext x
    refine (Formalism.L2.SG.InstExistsPf.mem_Lv D x).trans ?_
    simp only [Formalism.L2.Herm.crdLat, Formalism.L2.Herm.crd]
    constructor
    · intro hx
      refine ⟨(VS D).frame.equivFun.symm x, ?_, (VS D).frame.equivFun.apply_symm_apply x⟩
      have e := Module.Basis.equivFun_symm_apply (VS D).frame x
      rw [← e] at hx
      exact hx
    · rintro ⟨y, hy, hyx⟩
      change (VS D).frame.equivFun y = x at hyx
      rw [← hyx, (VS D).frame.sum_equivFun y]
      exact hy
  have hβ' : IsFrame β (II D).L := by rw [hL]; exact hβ
  have hloc : ∀ PP ∈ R.Pg, ∃ w : Bool,
      LocAt (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd ew β PP w := by
    intro PP hP
    obtain ⟨h1, h2, hA1, hA0⟩ := _root_.GlobalTheory.SeeConjIdem.resS_idem_conj (D.host.g 0 * D.host.g 1) ew ew_idem ew_orth ew_int ew_full PP (hgP PP hP)
    have hr : RedIs β PP (if GlobalTheory.StdFrames.cpt PP ew = 1 then
        flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 bw z0
      else flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (fun i => bwd (Fin.rev i)) z0) := hred PP hP
    by_cases hc : GlobalTheory.StdFrames.cpt PP ew = 1
    · rw [if_pos hc] at hr
      exact ⟨true, hgP PP hP, fun _ => by simpa using (hA1 hc).1, fun _ => by simpa using (hA1 hc).2, hr⟩
    · rw [if_neg hc] at hr
      exact ⟨false, hgP PP hP, fun _ => by simpa using (hA0 hc).1, fun _ => by simpa using (hA0 hc).2, hr⟩
  have hxM : (II D).fmat ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = (finE (Yc D 0) κ).val := _root_.GlobalTheory.SeeConjGroup.fmat_iota_eq_finE κ
  show _ ∧ _ ↔ _
  constructor
  · rintro ⟨-, hc⟩ PP hP
    obtain ⟨w, hw⟩ := hloc PP hP
    exact GlobalTheory.T.congruences_reduction_mem_symmetricUnipotent _ e0 f0 z0 bw bwd ew hFH β PP w hβ' hw _ (finE (Yc D 0) κ) hK hxM hS hc
  · intro hu
    exact ⟨hK, GlobalTheory.T.local_frame_hermitian_ideal _ e0 f0 z0 bw bwd ew hFH β R.Pg hβ' hloc hZ _ (finE (Yc D 0) κ) hK hxM hS hu⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def fnOf {t : T} (d : PureDat G t) : ∀ a, FactorFn G t a
  | .inl j => (d.1 j).fn
  | .inr i => (d.2 i).fn

def movFn (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) : ∀ a, FactorFn G t a :=
  Function.update
    (Function.update v (.inr ⟨j, by omega⟩)
      (fun x => v (.inr ⟨j, by omega⟩)
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 x) :
        FactorFn G t (.inr ⟨j, by omega⟩)))
    (.inr ⟨j + 1, hj⟩)
    (fun x => v (.inr ⟨j + 1, hj⟩)
        (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1 (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 x) :
        FactorFn G t (.inr ⟨j + 1, hj⟩))

def scaleAt (j : ℕ) (hj : j + 1 < D.R.m) (c₁ c₂ : ℂ) : Fin D.R.m ⊕ Fin D.R.m → ℂ :=
  Function.update (Function.update (fun _ => 1) (.inr ⟨j, by omega⟩) c₁) (.inr ⟨j + 1, hj⟩) c₂

end GlobalTheory.RowVertexInv
end
end

