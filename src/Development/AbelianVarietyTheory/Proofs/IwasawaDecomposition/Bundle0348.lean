module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Formalism.DoubleCosetMeasures.LatticeCoset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIntertwinerValuesSobolevContinuous
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxUnramifiedSubfieldConjIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
public import Development.AutomorphicArithmetic.BlochKatoExtensions.PhtCmp
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AevalWeightedHomogeneousChernMemChernCoefficientStatement
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_weightedHomogeneous_chern_mem_chernCoefficientSpan : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (R : MvPolynomial (ι × ℕ) ℝ), R.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) n → (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) ∈ Reach m n S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach | exact GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach | (intros; apply GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLFiniteFieldEqPowMulProd
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem

theorem card_GL_eq_pow_mul_qE (k : Type) [Field k] [Fintype k] (r : ℕ) :
    (Nat.card (GL (Fin r) k) : ℝ)
      = (Fintype.card k : ℝ) ^ (r * r) * Formalism.MainNotions.ZetaProductPairs.qE (Fintype.card k : ℝ) 1 r := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hq0 : (Fintype.card k : ℝ) ≠ 0 := by
    have : 0 < Fintype.card k := by omega
    exact_mod_cast this.ne'
  have hconst : (Fintype.card k : ℝ) ^ (r * r)
      = ∏ _j ∈ Finset.Icc 1 r, (Fintype.card k : ℝ) ^ r := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, ← pow_mul]
  rw [Matrix.card_GL_field, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range
      (fun i => ((Fintype.card k ^ r - Fintype.card k ^ i : ℕ) : ℝ)) r,
    hconst, Formalism.MainNotions.ZetaProductPairs.qE, ← Finset.prod_mul_distrib]
  refine Finset.prod_nbij' (fun i => r - i) (fun j => r - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr (by omega)
  · intro j hj
    have := Finset.mem_Icc.mp hj
    exact Finset.mem_range.mpr (by omega)
  · intro i hi
    have := Finset.mem_range.mp hi
    show r - (r - i) = i
    omega
  · intro j hj
    have := Finset.mem_Icc.mp hj
    show r - (r - j) = j
    omega
  · intro i hi
    have hir : i < r := Finset.mem_range.mp hi
    have hle : Fintype.card k ^ i ≤ Fintype.card k ^ r :=
      Nat.pow_le_pow_right (by omega) hir.le
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
    congr 1
    have hcast : (-((r - i : ℕ) : ℤ)) = (i : ℤ) - (r : ℤ) := by
      rw [Nat.cast_sub hir.le]; ring
    rw [hcast, zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    field_simp

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardResidueRingCompletionChosenUniformiser
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ResidueCardUnif

theorem card_kF_piP : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (h : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ OP P), Nat.card (kF (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) h) = qP P := by
  intro L _ _ P h
  have ha : Valued.v ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec P
  have h1 : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ P.adicCompletionIntegers L := h
  have e : IsLocalRing.maximalIdeal (P.adicCompletionIntegers L) = Ideal.span {⟨_, h1⟩} := by
    ext y
    rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers P
      (by rw [ha]; exact WithZero.exp_ne_zero)]
    rw [ha, ← GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp]
    exact Valuation.mem_maximalIdeal_iff _ _
  have c := GlobalTheory.GaugeProdFormula.card_residue L P
  rw [IsLocalRing.ResidueField, e] at c
  exact c

end GlobalTheory.ResidueCardUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterQuotientValuesInEmbeddingField
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Member.character_quotient_values_in_embedding_field

theorem small_quot_values : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (k : Type) [Field k] (σ : k →+* ℂ), SmallIn R i σ → (R.C.mu0 i * R.C.eta⁻¹).ValuesIn (-1 / 2) σ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i k _ σ h v hv
  have hE : R.C.eta.UnrAt v := R.C.isEta.unr v
  have hM : (R.C.mu0 i).UnrAt v := by
    intro x hx
    have h1 := hv x hx
    have h2 := hE x hx
    have h3 : ((R.C.mu0 i * R.C.eta⁻¹).loc v) x = (R.C.mu0 i).loc v x * (R.C.eta.loc v x)⁻¹ := rfl
    rw [h3, h2, inv_one, mul_one] at h1
    exact h1
  obtain ⟨y1, hy1⟩ := h.1 v hM
  obtain ⟨y2, hy2⟩ := h.2 v hE
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast this
  have hval : ((R.C.mu0 i * R.C.eta⁻¹).val v : ℂ) = ((R.C.mu0 i).val v : ℂ) * ((R.C.eta.val v : ℂ))⁻¹ := by
    have : (R.C.mu0 i * R.C.eta⁻¹).val v = (R.C.mu0 i).val v * (R.C.eta.val v)⁻¹ := rfl
    rw [this, Units.val_mul, Units.val_inv_eq_inv_val]
  have hy2' : σ y2 ≠ 0 := by
    rw [hy2, Formalism.L2.Host.HChar.valTw]
    exact mul_ne_zero (Units.ne_zero _) ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hN)
  refine ⟨y1 / y2, ?_⟩
  rw [map_div₀, hy1, hy2]
  simp only [Formalism.L2.Host.HChar.valTw, hval]
  have e1 : (-((-1 / 2 : ℝ) : ℂ)) = -(-((1 / 2 : ℝ) : ℂ)) := by push_cast; ring
  rw [e1, Complex.cpow_neg _ (-((1/2 : ℝ) : ℂ))]
  push_cast
  simp only [neg_zero, Complex.cpow_zero, mul_one]
  field_simp

end GlobalTheory.Member.character_quotient_values_in_embedding_field
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIntertwinerMapSobolevSeparatelyContinuous
section
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem GlobalTheory.ConjRowCont.conjMap_sobCont_ofIdE : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : (MP R).Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : (MP R).H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) ((MP R).rep τ) ℓ ∧ ∀ w : (MP R).sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) x := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hιE _ _ hinf _ _ c hc Φ hΦ _ τ v x
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h R.θ hinf hιE
  exact GlobalTheory.ConjRowCont.sobCont_conjMap X h R.θ (MP R) t c hinf (fun k hk => (hf k).1 hk)
    (fun τ g hg => ⟨(hat τ g hg).1, (hat τ g hg).2.1⟩) hc Φ hΦ τ v x
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
section
noncomputable section

namespace GlobalTheory.HaarMat

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD Topology

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

theorem intMat_eq_pi (n m : ℕ) : intMat (OP P) n m = Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
      fun _ : Fin m => ((P.adicCompletionIntegers L : Set (P.adicCompletion L)))) := by
  ext y
  exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩

theorem isCompact_intMat (n m : ℕ) : IsCompact (intMat (OP P) n m) := by
  rw [intMat_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers P

theorem isOpen_intMat (n m : ℕ) : IsOpen (intMat (OP P) n m) := by
  rw [intMat_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _

def intMatK (n m : ℕ) : TopologicalSpace.PositiveCompacts (Matrix (Fin n) (Fin m) (P.adicCompletion L)) where
  carrier := intMat (OP P) n m
  isCompact' := isCompact_intMat P n m
  interior_nonempty' := by
    rw [(isOpen_intMat P n m).interior_eq]
    exact ⟨0, fun i j => (OP P).zero_mem⟩

theorem exists_haar_intMat : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (n m : ℕ),
    letI : MeasurableSpace (P.adicCompletion L) := borel _;
    ∃ ν : Measure (Matrix (Fin n) (Fin m) (P.adicCompletion L)),
      ν.IsAddLeftInvariant ∧ SFinite ν ∧ ν (intMat (OP P) n m) = 1 := by
  intro L _ _ P n m
  letI : MeasurableSpace (P.adicCompletion L) := borel _
  haveI : BorelSpace (P.adicCompletion L) := ⟨rfl⟩
  haveI : BorelSpace (Matrix (Fin n) (Fin m) (P.adicCompletion L)) :=
    inferInstanceAs (BorelSpace (Fin n → Fin m → P.adicCompletion L))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin m) (P.adicCompletion L)) :=
    (isCompact_intMat P n m).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((isOpen_intMat P n m).mem_nhds fun i j => (OP P).zero_mem)
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin m) (P.adicCompletion L)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin m → P.adicCompletion L))
  haveI : SigmaCompactSpace (Matrix (Fin n) (Fin m) (P.adicCompletion L)) := inferInstance
  haveI : SigmaFinite (Measure.addHaarMeasure (intMatK P n m)) := inferInstance
  refine ⟨Measure.addHaarMeasure (intMatK P n m), inferInstance, inferInstance,
    Measure.addHaarMeasure_self⟩

end GlobalTheory.HaarMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBridge
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 NumberField IsDedekindDomain Module GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.PhtCompare

section
variable {l : ℕ} [Fact l.Prime]
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}

theorem exists_bridge (j : Ω →+* Om l) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ (L : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL L)), Bw.j = j ∧ Bw.Kw.1 ≤ Bw.LL.1 ∧
      Bw.Kw.1 = IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)) := by
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩
  have := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj K rfl
  exact ⟨⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩,
    { Kw := K
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (j.comp (algebraMap E Ω))
      e := e
      e_cont := he
      e_symm_cont := he'
      e_comm := hec
      LL := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
      LL_split := fun τ x => AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, rfl, IntermediateField.le_normalClosure _, rfl⟩

end

end GlobalTheory.PhtCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjIdempotentSumOverLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.HalfLevelConj

theorem exists_conj_idemSum : ∀ (D : D7) (N : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P →
    (∀ PP ∈ P, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ (e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)),
    IsIdemSum e' P' ∧ (∀ PP ∈ P', ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ cA D e' = e := by
  intro D N e P hE hN
  classical
  refine ⟨cA D e, P.image Formalism.L2.DIV.conjPl, Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hE, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    have hmem : ((N : ℕ) : 𝓞 D.host.E) ∈ (Formalism.L2.DIV.conjPl PP).asIdeal ↔
        Formalism.L2.DIV.starO ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := Iff.rfl
    have hs : Formalism.L2.DIV.starO ((N : ℕ) : 𝓞 D.host.E) = ((N : ℕ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.ext
      rw [Formalism.L2.DIV.starO_coe]
      simp
    rw [hmem, hs]
    exact hN PP hPP
  · rw [Formalism.L2.Theta.cA_cA]

end GlobalTheory.HalfLevelConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoupledTameInertiaGeneratorStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coupled_tame_inertia_generator : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, IsGenSys ζ → ∃ κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g, ∃ σ ∈ Ine (F := E) A, TameGenAt A σ ∧ TameCoupled A κ σ ζ := by
  first | exact @GlobalTheory.TameCoupledEx.exists_coupled_tame_generator | exact GlobalTheory.TameCoupledEx.exists_coupled_tame_generator | (intros; apply GlobalTheory.TameCoupledEx.exists_coupled_tame_generator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbOfRangeLe
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.Mem GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isIdG_unique (X : Stages) {px : PreX X.B.toPre} {Pg : Finset (Pl X.toD7.host.E)} (hPg : Pg = (X.B.primes px).vGs)
    {eG eG' : Gc X.B px ≃* G0 Pg X.toD7.R.r} (h : IsPlacewiseIdentity X (px := px) eG) (h' : IsPlacewiseIdentity X (px := px) eG') : eG = eG' := by
  subst hPg
  exact MulEquiv.ext fun g => funext fun P => (h g P.1 P.2 P.2).trans (h' g P.1 P.2 P.2).symm

theorem isStdChar_unique {D : D7} {ψ ψ' : AddChar (AF D.host.F) ℂ} {s : ℤ} (h : IsStdChar D ψ s) (h' : IsStdChar D ψ' s) :
    ψ = ψ' := by
  obtain ⟨θ, hθ⟩ := h.2.1
  exact GlobalTheory.StdAdelicChar.eq_of_psiInf_eq h.1 h'.1 fun x => (h.2.2 θ hθ x).trans (h'.2.2 θ hθ x).symm

theorem isInfFam_unique {D : D7} {θ θ' : Formalism.IndefR.Datum.InfFam D} (h : IsInfFam θ) (h' : IsInfFam θ') : θ = θ' :=
  Formalism.IndefR.Eqv.infFamUnique_holds D θ θ' h h'


end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarGLCompletionIntegersVolOne
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory

theorem haar_glInt_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r : ℕ), ∃ μ : Measure (GL (Fin r) (P.adicCompletion L)), μ.IsMulLeftInvariant ∧ μ ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) = 1 := by
  intro L _ _ P r
  have hc : IsCompact ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) :=
    Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_compact (OP P) (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers P) r
  have ho : IsOpen ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) :=
    Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_open (OP P) (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers P) r
  let K₀ : TopologicalSpace.PositiveCompacts (GL (Fin r) (P.adicCompletion L)) :=
    ⟨⟨_, hc⟩, by
      rw [ho.interior_eq]; exact ⟨1, (GLint (OP P) r).one_mem⟩⟩
  refine ⟨Measure.haarMeasure K₀, Measure.isMulLeftInvariant_haarMeasure K₀, ?_⟩
  exact Measure.haarMeasure_self

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.NrmCompl

theorem isNrm_nrmAbs {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) : IsNrm P (nrmAbs P) := by
  intro x
  refine ⟨fun hx => (nrmAbs_eq_one_iff P (x : P.adicCompletion L)).2 hx, fun hx => ?_⟩
  have h : Valued.v (x : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := hx
  rw [nrmAbs_of_valuation_eq_exp P h, _root_.zpow_neg_one]
  rfl

theorem exists_isNrm : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)),
    ∃ nrm : AbsoluteValue (P.adicCompletion L) ℝ, IsNrm P nrm :=
  fun _ _ _ P => ⟨nrmAbs P, isNrm_nrmAbs P⟩

end GlobalTheory.Mem.NrmCompl
end

