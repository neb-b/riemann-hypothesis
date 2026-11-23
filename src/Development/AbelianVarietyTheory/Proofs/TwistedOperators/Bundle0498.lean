module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumArchimedeanHeisenbergLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockPolyInj

open GlobalTheory.FockVecInj GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7}

theorem pureTensorO_injective_of_on (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sV BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (s BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (pV pW : D.what₂.Tau → ℕ)
    (hBV : ∀ τ, IsONBasis (gramAt D V τ) (sV τ) (BV τ) (pV τ))
    (hBW : ∀ τ, IsONBasis (gramAt D W τ) (s τ) (BW τ) (pW τ)) (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f)
    (hvac : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sV τ) (s τ)) f) (hf0 : f ≠ 0) :
    Function.Injective (pureTensorO ψ θ V W sV s BV BW f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  choose ε hε hG hs using hBV
  choose ε' hε' hG' hs' using hBW
  have sq : ∀ τ a, (ε τ a : ℂ) * ε τ a = 1 := fun τ a => by
    rcases hε τ a with h | h <;> simp [h.1]
  have sq' : ∀ τ a, (ε' τ a : ℂ) * ε' τ a = 1 := fun τ a => by
    rcases hε' τ a with h | h <;> simp [h.1]
  have hdet : ∀ τ, IsUnit (BV τ).det := fun τ => by
    have e : (diagonal (fun a => (ε τ a : ℂ)) * ((BV τ)ᴴ * gramAt D V τ)) * BV τ = 1 := by
      rw [Matrix.mul_assoc, hG, Matrix.diagonal_mul_diagonal]
      simp only [sq, Matrix.diagonal_one]
    exact Matrix.isUnit_det_of_left_inverse e
  have hE : ∀ τ z g, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z g = hD (iotaW σ W V) (piW θ W V) (omO V W)
      (Pi.single τ z : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) g := fun τ z g => by
    rw [← pi_lineAt hθ]
    exact dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  let M : Submodule ℂ (WO V W → ℂ) :=
    { carrier := {g | Sm (iotaW σ W V) g}
      add_mem' := fun ha hb w => (ha w).add (hb w)
      zero_mem' := fun w => contDiff_const
      smul_mem' := fun c g hg w => contDiff_const.mul (hg w) }
  have hform := fun g hg u w => hD_eq_fderiv (iotaW σ W V) (piW θ W V) (omO V W) g hg u w
  obtain ⟨Dop, hD1, -⟩ := exists_heisenberg_operators _ _ (iotaW σ W V) (piW θ W V) (omO V W) (h.pi_iota W V) hform M
    (fun _ hg => hg) fun u g hg => (hD_formula_smooth _ _ _ _ _ (h.pi_iota W V) g hg u).2
  have sk : ∀ u v, omO V W v u = -omO V W u v := fun u v => by
    have h1 := omO_self h (S := V) (T := W) (u + v)
    simp only [LinearMap.map_add (f := _), LinearMap.add_apply, omO_self h] at h1
    linarith
  have hcomm : ∀ u v g, Dop u (Dop v g) = Dop v (Dop u g) + (-(2 * Real.pi * I) * (omO V W u v : ℝ)) • g :=
    fun u v g => by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, hD1, hD1, hD1, hD1]
    exact eq_add_of_sub_eq' (heisenberg_derivative_commutator _ _ _ _ _ (h.pi_iota W V) hform sk g g.2 u v)
  let η : FVar D W.rank V.rank → ℝ := fun k => ε' k.1 k.2.1 * ε k.1 k.2.2
  have hη : ∀ k, η k = 1 ∨ η k = -1 := fun k => by
    rcases hε k.1 k.2.2 with h | h <;> rcases hε' k.1 k.2.1 with h' | h' <;> simp [η, h.1, h'.1]
  let u : ℂ → FVar D W.rank V.rank → RW W V := fun c k =>
    (Pi.single k.1 (c • unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ)
  have hom : ∀ c c' k l, omO V W (u c k) (u c' l) =
      if k = l then 2 * (tauE D k.1 D.host.xi0 * (c * conj c' * η k)).re else 0 := by
    rintro c c' ⟨τ, i, j⟩ ⟨τ', k, l⟩
    refine (omO_single V W τ τ' _ _).trans ?_
    by_cases hτ : τ = τ'
    · subst hτ
      rw [if_pos rfl, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.trace_smul, Matrix.trace_smul, trace_unitMap (sq τ) (hG τ) (hG' τ)]
      by_cases hk : i = k ∧ j = l
      · rw [if_pos hk, if_pos (by rw [hk.1, hk.2])]
        simp only [η, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
        rfl
      · rw [if_neg hk, if_neg (by simpa using hk)]
        simp
    · rw [if_neg hτ, if_neg fun hh => hτ (congrArg Prod.fst hh)]
  have hJ : ∀ k : FVar D W.rank V.rank, cplxO (sV k.1) (s k.1) (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) =
      (I * η k) • unitMap (BV k.1) (BW k.1) k.2.1 k.2.2 := fun k => by
    rw [cplxO_unitMap (hdet _) (hs _) (hs' _)]
    simp only [η, Complex.ofReal_mul]
  have h1 : ∀ k : FVar D W.rank V.rank, u 1 k = (Pi.single k.1 (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) :
      D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) := fun k => congrArg (Pi.single k.1) (one_smul _ _)
  have hξ : ∀ τ, tauE D τ D.host.xi0 ≠ 0 := fun τ => (_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hre := fun τ => GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero (D := D) τ
  have him : ∀ τ, (tauE D τ D.host.xi0).im ≠ 0 := fun τ hh => hξ τ (Complex.ext (hre τ) hh)
  have hsc : ∀ τ, (fockScale D τ : ℂ) ≠ 0 := fun τ => by
    have := norm_pos_iff.2 (hξ τ)
    have h2 : 0 < fockScale D τ := by unfold fockScale; positivity
    exact Complex.ofReal_ne_zero.2 h2.ne'
  refine injective_of_canonicalCommutation M _ (fun k => (fockScale D k.1 : ℂ)⁻¹ • (Dop (u 1 k) - I • Dop (u (I * η k) k)))
    (fun k => Dop (u 1 k) + I • Dop (u (I * η k) k))
    (fun k => (fockScale D k.1 : ℂ)⁻¹ * (-8 * Real.pi * (tauE D k.1 D.host.xi0).im)) (fun k g => ?_) (fun k l g => ?_)
    (fun k l g => ?_) (fun k => ?_) ⟨f, theta_sm h hf⟩ (fun k => ?_) (fun hh => hf0 (congrArg Subtype.val hh))
  · simp only [aPlusAll, aPlus, crea, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub,
      hD1, hE, hJ]
    rw [h1]
  · rw [(ccr_of_comm Dop _ hcomm _ _ _ _ _ _ g).1]
    refine add_eq_left.2 (smul_eq_zero.2 (Or.inl ?_))
    simp only [hom]
    split_ifs with hh
    · subst hh
      rcases hη k with e | e <;> simp [e, hre]
    · simp
  · rw [(ccr_of_comm Dop _ hcomm _ _ _ _ 0 _ g).2]
    refine congrArg (fun c : ℂ => _ + c • g) ?_
    by_cases hh : k = l
    · subst hh
      simp only [hom, if_true]
      refine congrArg _ ?_
      rcases hη k with e | e <;> simp [e, hre] <;> ring_nf <;> simp only [I_sq] <;> ring1
    · simp [hom, hh]
  · exact mul_ne_zero (inv_ne_zero (hsc _)) (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) (Complex.ofReal_ne_zero.2 (him _)))
  · apply Subtype.ext
    have := hvac k.1 (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2)
    simp only [annih, hE, hJ] at this
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add, hD1]
    rw [h1]
    exact this

theorem isONBasis_one {V : HSp D} (hV : V.gram = 1) (τ : D.what₂.Tau) :
    IsONBasis (gramAt D V τ) 1 1 V.rank := by
  have hg : gramAt D V τ = 1 := by
    unfold gramAt
    rw [hV]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.isLt⟩, ?_, ?_⟩ <;>
    simp [hg, Matrix.diagonal_one]

theorem fvec_injective : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → f ≠ 0 → Function.Injective (C.fvec B f) := by
  intro D S T C B hB f hf hvac hf0
  have hT := ((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.2.1
  exact pureTensorO_injective_of_on C.ψ C.θ S T C.std C.inf (fun _ => 1) (fun _ => 1) (C.sB B) B
    (fun _ => S.rank) (fun _ => C.X.p0) (isONBasis_one C.m.gS) (fun τ => (hT τ).2) f hf hvac hf0

end GlobalTheory.FockPolyInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsPrincipalLevelAreRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows.Good

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem princGL_le_princAt (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {I : Ideal (𝓞 E)} {PP : Pl E} (h : I ≤ PP.asIdeal) :
    GlobalTheory.Grid.princGL β I ≤ princAt β PP := by
  intro x hx
  obtain ⟨y, rfl, hy⟩ := GlobalTheory.Grid.mem_princGL.1 (GlobalTheory.Grid.princGL_mono β h hx)
  refine mem_princAt.2 ⟨⟨y, rfl⟩, ?_⟩
  rw [redFn_frGL]
  apply Units.ext
  ext i j
  have h0 : resS F PP ((y.1 - 1) i j) = 0 := by
    unfold resS
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (hy i j), map_zero]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0
  refine h0.trans ?_
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem congLev_le_Kg [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ) {I : Ideal (𝓞 E)} {T : Finset (Pl E)}
    (h : ∀ PP ∈ T, I ≤ PP.asIdeal) : congLev hc J Λ I ≤ Kg hc J β T := by
  rw [← GlobalTheory.ColMeas.princ_eq_congLev hc J hfr I]
  rintro x ⟨h1, h2⟩
  refine ⟨⟨h1, ?_⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => princGL_le_princAt β (h PP hP) h2⟩
  obtain ⟨y, e, -⟩ := GlobalTheory.Grid.mem_princGL.1 h2
  exact ⟨y, e⟩

end General

variable {D : D7} {T : Type}

theorem g_mem {P : Formalism.L2.Host.PiBar D.host} {k : Fin 2} {PP : Pl D.host.E} (h : P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := P.pb_over k
  have h2 : PP.under (𝓞 D.host.K) = P.pb k := h
  rw [← h2] at h1
  have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
  rwa [map_natCast] at h3

theorem levRow_sub {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) :
    (levRow L : Set (GA D (Yc D 0))) ⊆ levS _ (L.βY 0) (L.dat0 L.triv) := by
  rintro k ⟨hk1, hk2⟩
  obtain ⟨c, hfr, -⟩ := hL.βY 0 (by have := D.R.two_le_m; omega)
  refine ⟨hk1, Kg_le_lev (T := L.Pg) (D := L.dat0 L.triv) subset_rfl (Finset.empty_subset _)
    (congLev_le_Kg _ _ hfr (fun PP hP => ?_) hk2)⟩
  obtain ⟨l, hl⟩ := (hL.Pg PP).1 hP
  have hg := g_mem hl
  rw [Ideal.span_singleton_le_iff_mem, Nat.cast_mul]
  fin_cases l
  · exact Ideal.mul_mem_right _ _ hg
  · exact Ideal.mul_mem_left _ _ hg

theorem principalRowLevelCharacter_trivial (L : LevCh D T) (k : GA D (Yc D 0)) : Lev.levChi _ (L.βY 0) (L.dat0 L.triv) k = 1 := by
  have h : levFn (L.βY 0) (L.dat0 L.triv) (Lev.finE (Yc D 0) k) = 1 := by
    have h1 : ext1 (L.dat0 L.triv).P.H (L.dat0 L.triv).P.chi (rTup (L.βY 0) (L.dat0 L.triv) (Lev.finE (Yc D 0) k)) = 1 :=
      Lev.subgroupCharExtension_one_apply _ _
    unfold levFn
    rw [h1]
    simp [LevCh.dat0, Lev.datY]
  unfold Lev.levChi
  rw [h, Units.val_one]

end GlobalTheory.SepRows.Good

theorem GlobalTheory.SepRows.goodRows : GoodRows := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R hL t ht
  rw [mem_multT, LinearEquiv.symm_apply_apply]
  refine Submodule.span_mono (fun U hU => ?_) (goodPart_le _ _ _ _ _ ht)
  exact ⟨hU.aut, hU.cusp, fun v k hk g => by
    rw [hU.lev v k (Good.levRow_sub hL hk) g, Good.principalRowLevelCharacter_trivial]; rfl, hU.equiv, hU.cont⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumArchimedeanHeisenbergLineStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_thetaSum_archimedeanHeisenbergLine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → ∀ (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
    ∀ (g g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (Fin n × Fin d → v.adicCompletion F) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) g g₁ →
      ∀ u' : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
        HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u' (M.heisLine ψ u t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))))
          (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ))) 0 := by
  first | exact @GlobalTheory.ThetaLinePure.hasDerivAt_thetaSum_heisLine | exact GlobalTheory.ThetaLinePure.hasDerivAt_thetaSum_heisLine | (intros; apply GlobalTheory.ThetaLinePure.hasDerivAt_thetaSum_heisLine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutMemLatticeStabilizerOfProductLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix

namespace GlobalTheory.CutProdLev

theorem cutGL_mem_St_of_mem_prodLev : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    {n' : P → ℕ} (h : ∀ w, n' w = n) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (x : GL (Fin n) (Lev.EAf D)),
    x ∈ prodLev β P h K → ∀ (b : Lev.EAf D) (hb : b * b = b),
    (∀ w : Pl D.host.E, (∃ PP ∈ P, w.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.StdFrames.cpt (D := D) w b = 0) →
    GlobalTheory.UnitaryIdemCut.cutGL b hb x ∈ St β := by
  intro D n β P n' h K x hx b hb hb0
  apply StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO
  intro w

  have hc : GlobalTheory.StdFrames.cpt (D := D) w b * GlobalTheory.StdFrames.cpt (D := D) w b = GlobalTheory.StdFrames.cpt (D := D) w b :=
    (map_mul (GlobalTheory.StdFrames.cpt (D := D) w) b b).symm.trans (congrArg _ hb)
  have h01 : GlobalTheory.StdFrames.cpt (D := D) w b = 0 ∨ GlobalTheory.StdFrames.cpt (D := D) w b = 1 := by
    have h' : GlobalTheory.StdFrames.cpt (D := D) w b * (GlobalTheory.StdFrames.cpt (D := D) w b - 1) = 0 := by
      rw [mul_sub, hc, mul_one, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)

  have hconj : (MulAut.conj β⁻¹).toMonoidHom (GlobalTheory.UnitaryIdemCut.cutGL b hb x) =
      GlobalTheory.UnitaryIdemCut.cutGL b hb ((MulAut.conj β⁻¹).toMonoidHom x) :=
    (GlobalTheory.UnitaryIdemCut.cutGL_conj b hb β⁻¹ x).symm
  have hloc : ∀ y : GL (Fin n) (Lev.EAf D), GlobalTheory.StdFrames.loc w (GlobalTheory.UnitaryIdemCut.cutGL b hb y) =
      GlobalTheory.UnitaryIdemCut.cutGL _ hc (GlobalTheory.StdFrames.loc w y) := fun y =>
    GlobalTheory.UnitaryIdemCut.bc_cutGL (GlobalTheory.StdFrames.cpt w) b hb _ hc rfl y
  rcases h01 with h0 | h1
  ·
    have e1 : ∀ g : GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.E w), GlobalTheory.UnitaryIdemCut.cutGL _ hc g = 1 := fun g => Units.ext (by
      rw [GlobalTheory.UnitaryIdemCut.cutGL_val, h0]
      simp)
    have e : GlobalTheory.FunObj.inBasis rfl β w (GlobalTheory.UnitaryIdemCut.cutGL b hb x) = 1 := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply]
      rw [hconj, hloc, e1, map_one]
    rw [e]
    exact one_mem _
  ·

    unfold GlobalTheory.FunObj.prodLev at hx
    have hx2 := (Subgroup.mem_inf.mp hx).2
    rw [Subgroup.mem_iInf] at hx2
    have hx3 := hx2 w
    rw [Subgroup.mem_iInf] at hx3
    have hxw := Subgroup.mem_comap.mp (hx3 fun PP hPP e => by
      have h2 := hb0 w ⟨PP, hPP, e⟩
      rw [h1] at h2
      exact one_ne_zero h2)
    have e1 : ∀ g : GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.E w), GlobalTheory.UnitaryIdemCut.cutGL _ hc g = g := fun g => Units.ext (by
      rw [GlobalTheory.UnitaryIdemCut.cutGL_val, h1]
      simp)
    have e : GlobalTheory.FunObj.inBasis rfl β w (GlobalTheory.UnitaryIdemCut.cutGL b hb x) = GlobalTheory.FunObj.inBasis rfl β w x := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply]
      rw [hconj, hloc, e1]
    rw [e]
    exact hxw

end GlobalTheory.CutProdLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexMovedHomLatticeSplitPlaceChartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_movedHomLattice_splitPlaceChart : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v (e.symm (k₁ * t * k₂))))) = qV D.host.E w ^ (S.rank * (∑ i, |d i|).toNat) := by
  first | exact @GlobalTheory.SplitIdx.index_moved_split | exact GlobalTheory.SplitIdx.index_moved_split | (intros; apply GlobalTheory.SplitIdx.index_moved_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsContRepLeftRep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory Matrix

noncomputable section

namespace GlobalTheory.LeftRegularRepresentation

def leftRep {K : Type} [Group K] (F : Submodule ℂ (K → ℂ)) (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F) :
    Representation ℂ K F where
  toFun a :=
    { toFun := fun φ => ⟨fun k => φ.1 (a⁻¹ * k), hF _ φ.2 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext φ k
    simp
  map_mul' a b := by
    ext φ k
    simp [mul_assoc]

theorem dual_mem_span {K : Type} (F : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ F] (ℓ : Module.Dual ℂ F) :
    ℓ ∈ Submodule.span ℂ (Set.range fun y : K => (LinearMap.proj y).comp F.subtype) := by
  have h : (Submodule.span ℂ (Set.range fun y : K =>
      ((LinearMap.proj y).comp F.subtype : Module.Dual ℂ F))) = ⊤ := by
    refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
    by_contra hc
    push Not at hc
    exact hz (Subtype.ext (funext fun y => hc _ ⟨y, rfl⟩))
  rw [h]
  trivial

theorem isContRep_leftRep {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (F : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ F] (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F)
    (hc : ∀ φ ∈ F, Continuous φ) : GlobalTheory.Published.AutFin.IsContRep (leftRep F hF) := by
  intro ℓ w
  induction dual_mem_span F ℓ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact (hc _ w.2).comp (continuous_inv.mul continuous_const)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

theorem conv_mem {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
    (F : Submodule ℂ (K → ℂ)) (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F)
    (hc : ∀ φ ∈ F, Continuous φ) {e : K → ℂ} (he : e ∈ F) {f : K → ℂ} (hf : Continuous f) :
    (fun a => ∫ k, e k * f (a * k) ∂μ) ∈ GlobalTheory.Published.AutFin.coeffSpan (leftRep F hF) := by
  have hi : ∀ φ : F, Integrable (fun k => φ.1 k * f k) μ := fun φ =>
    ((hc _ φ.2).mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let ℓ : Module.Dual ℂ F :=
    { toFun := fun φ => ∫ k, φ.1 k * f k ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hi a) (hi b)]
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul _ _ }
  refine Submodule.subset_span ⟨ℓ, ⟨e, he⟩, funext fun a => ?_⟩
  change _ = ∫ k, e (a⁻¹ * k) * f k ∂μ
  rw [← integral_mul_left_eq_self (fun k => e (a⁻¹ * k) * f k) a]
  simp only [inv_mul_cancel_left]

theorem kFinAt_avg : ∀ (D : Formalism.BasicNotions.D7) (θ : Formalism.IndefR.Datum.InfFam D), Formalism.L2.Theta.IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : Formalism.L2.Theta.GA D (GlobalTheory.Grid.Node.V N) → ℂ), Formalism.L2.Theta.IsAutFunSm θ (GlobalTheory.Grid.Node.V N) ψ → ∀ (τ : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D)) (e : ↥(Formalism.REAL.KG (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ)) → ℂ), GlobalTheory.TypeSum.KFinFun (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ) e → GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ (GlobalTheory.Grid.Node.V N) τ (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ) (Formalism.IndefR.Mult.DSModel.fr (GlobalTheory.Grid.Node.M N) τ) e ψ) := by
  intro D θ hθ N ψ hψ τ e he
  obtain ⟨F, hfd, heF, hc, hF⟩ := he
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hmem := GlobalTheory.Published.AutFin.conj_mem_UH hP hJ
  have hd : IsUnit (N.M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hK : Continuous fun k : Formalism.REAL.KG (N.M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hk : Continuous (GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ)) :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ).comp_continuous
      ((continuous_const.matrix_mul hK).matrix_mul continuous_const) hmem
  have hmul : ∀ a b, GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (a * b) =
      GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) a * GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) b := by
    intro a b
    unfold GlobalTheory.Published.AutFin.kAt
    rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ N.V τ (hmem a) (hmem b)]
    congr 1
    have e1 : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
    rw [e1]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  refine ⟨F, inferInstance, inferInstance, hfd, leftRep F fun φ h a => (hF φ h a).1,
    isContRep_leftRep F _ hc, fun x => ?_⟩
  have h := conv_mem (Formalism.REAL.muK (N.M.ε τ)) F (fun φ h a => (hF φ h a).1) hc heF
    (f := fun k => ψ (x * GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k))
    (hψ.cont.comp (continuous_const.mul hk))
  simp only [hmul, ← mul_assoc] at h
  exact h

end GlobalTheory.LeftRegularRepresentation

end
end

