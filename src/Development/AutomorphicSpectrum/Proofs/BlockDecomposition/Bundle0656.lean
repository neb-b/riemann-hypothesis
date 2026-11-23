module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0487
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0484
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0654
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0647
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0651
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0652
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0053
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0653

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DictionaryMaximalCompactParts
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SWDict

open PositivityTheory.PfSWUS GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd

theorem dictKA_of_parts : PositivityTheory.PfSWUS.DictKAOfParts := by
  intro hF hW hI hM D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨N, φs, hsum, hmono⟩ := hF D n V ψ χ θ μ ω H l s ν Φ hS hR k hk
  refine ⟨N, φs, fun j => npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
    IfrB V ν (fun x => φs j (HMul.hMul x a.1)) β, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hW D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k N φs hmono
    exact ⟨t, fun z hz => by rw [hsum]; exact ht z hz⟩
  · rw [hsum, hI D n V ψ χ θ μ ω H l s ν Φ hS hR β hβ a N φs hmono, Finset.mul_sum]
  · exact fun j => hM D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk (φs j) (hmono j)

end GlobalTheory.CompanionTheory.SWDict

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinThetaInvariance
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCellsTheta

theorem thetaInv : PositivityTheory.GramSchwartzFunctions.EC.ThetaInv := by
  intro D n V ψ χ θ μ ω hS
  let S : Subgroup (G D n) :=
    { carrier := {γ | ∀ Φ : schwartzA θ V.rank n,
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
          ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D))}
      one_mem' := fun Φ => by simp
      mul_mem' := fun {g h} hg hh Φ => by
        rw [map_mul, Module.End.mul_apply]
        exact (hg _).trans (hh Φ)
      inv_mem' := fun {g} hg Φ => by
        have := hg (ω g⁻¹ Φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hle : GF D n ≤ S := _root_.GlobalTheory.CompanionTheory.RatGen.GF_le_of_levi_unip_weyl D n S (fun g a hg Φ => GlobalTheory.T.theta_sum_invariant_levi_element D n V ψ χ θ μ ω hS g a hg Φ)
    (fun g b hg Φ => GlobalTheory.T.theta_sum_invariant_unipotent_translate D n V ψ χ θ μ ω hS g b hg Φ)
    (fun g hg Φ => _root_.GlobalTheory.CompanionTheory.ThetaPoisson.theta_weyl D n V ψ χ θ μ ω hS g hg Φ)
  intro Φ γ hγ
  exact hle hγ Φ

end GlobalTheory.CompanionTheory.EisCellsTheta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVanishingStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_vanishing : PositivityTheory.GramSchwartzFunctions.EC.Zero := by
  first | exact @GlobalTheory.CompanionTheory.EisZero.zero | exact GlobalTheory.CompanionTheory.EisZero.zero | (intros; apply GlobalTheory.CompanionTheory.EisZero.zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentation
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegExists

theorem hasFiniteLength_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) :=
  GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x))

theorem exists_isLSeg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), ∃ π : IrrRep (GL (Fin Δ.deg) k), IsLSeg Δ π.ρ := by
  intro k _ _ _ _ hA Δ
  have hd : ∑ a, (Δ.term a).1 = Δ.deg := Δ.sum_term_fst
  obtain ⟨hd', ⟨φ⟩⟩ := _root_.GlobalTheory.CompanionTheory.SegIncDual.contra_prodIrr_term hA Δ hd
  obtain ⟨τ', hτ'⟩ := _root_.GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec hA (segDual Δ) hd'
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra hA (prodIrr Δ.term hd)
    (isSmooth_prodIrr _ _) (hasFiniteLength_prodIrr hA _ _) τ' (hτ'.of_equiv (.refl _) φ.symm)
  exact ⟨τ, hd, hτ⟩

end GlobalTheory.CompanionTheory.SegExists

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTestFunctionProductStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_test_function_product : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    (y : Hf E a b), finFn S φ₁ φ₂ y = ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) := by
  first | exact @GlobalTheory.CompanionTheory.FinActS.finFn_eq_finprod_factor | exact GlobalTheory.CompanionTheory.FinActS.finFn_eq_finprod_factor | (intros; apply GlobalTheory.CompanionTheory.FinActS.finFn_eq_finprod_factor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzRestrictionColumns
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColSlice

variable {D : D7} {n r t a : ℕ}

def colIdx (hn : r + t = n) (j : Fin t) : Fin n := finCongr hn (finSumFinEquiv (Sum.inr j))

theorem colIdx_injective (hn : r + t = n) : Function.Injective (colIdx hn) := fun _ _ h =>
  Sum.inr_injective (finSumFinEquiv.injective ((finCongr hn).injective h))

def colPr (hn : r + t = n) (y : Mx D a n) : Mx D a t := y.submatrix id (colIdx hn)

theorem colPr_jn (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) : colPr hn (jn hn x v) = v := by
  ext i j
  simp [colPr, colIdx, jn, Matrix.submatrix_apply]

theorem continuous_colPr (hn : r + t = n) : Continuous (colPr (D := D) (a := a) hn) :=
  continuous_id.matrix_submatrix _ _

theorem continuous_jn (hn : r + t = n) (x : Mx D a r) : Continuous (jn (D := D) hn x) :=
  continuous_matrix fun i j => by
    show Continuous fun v : Mx D a t => Matrix.fromCols x v i ((finSumFinEquiv.trans (finCongr hn)).symm j)
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with s | s
    · exact continuous_const
    · exact continuous_id.matrix_elem i s

theorem realSize_le (θ : InfFam D) (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) :
    GlobalTheory.Unf.realSize θ v ≤ GlobalTheory.Unf.realSize θ (jn hn x v) := by
  unfold GlobalTheory.Unf.realSize
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => ?_
  have e : ∀ j, compAt θ τ v i j = compAt θ τ (jn hn x v) i (colIdx hn j) := fun j => by
    have := colPr_jn hn x v
    conv_lhs => rw [← this]
    rfl
  simp only [e]
  have h := Finset.sum_le_univ_sum_of_nonneg (f := fun j => ‖compAt θ τ (jn hn x v) i j‖)
    (s := Finset.univ.map ⟨colIdx hn, colIdx_injective hn⟩) fun _ => norm_nonneg _
  rw [Finset.sum_map] at h
  exact h

theorem maj_jn_le (θ : InfFam D) (hn : r + t = n) (K : Set (Mx D a n)) (N : ℕ) (x : Mx D a r) (v : Mx D a t) :
    GlobalTheory.Unf.maj θ K N (jn hn x v) ≤ GlobalTheory.Unf.maj θ (colPr hn '' K) N v := by
  by_cases hb : GlobalTheory.Unf.InBox K (jn hn x v)
  · have hb' : GlobalTheory.Unf.InBox (colPr hn '' K) v := by
      obtain ⟨k, hk, h0⟩ := hb
      refine ⟨colPr hn k, ⟨k, hk, rfl⟩, ?_⟩
      ext i j
      have := congrFun (congrFun h0 i) (colIdx hn j)
      have e : v i j = jn hn x v i (colIdx hn j) := by
        conv_lhs => rw [← colPr_jn hn x v]
        rfl
      show finPart D (v i j - k i (colIdx hn j)) = 0
      rw [e]
      exact this
    unfold GlobalTheory.Unf.maj
    rw [if_pos hb, if_pos hb']
    have h1 := GlobalTheory.Unf.realSize_nonneg θ v
    have h2 := realSize_le θ hn x v
    gcongr
  · have h0 : GlobalTheory.Unf.maj θ K N (jn hn x v) = 0 := by unfold GlobalTheory.Unf.maj; rw [if_neg hb]
    rw [h0]
    exact GlobalTheory.Unf.maj_nonneg θ _ N v

theorem integrable_slice : ∀ {D : D7} {n r t : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) {a : ℕ} (hn : r + t = n)
    (μt : Measure (Mx D a t)) [μt.IsAddHaarMeasure] (Φ : schwartzA θ a n) (x : Mx D a r),
    Integrable (fun v => Φ.1 (jn hn x v)) μt := by
  intro D n r t θ hθ a hn μt _ Φ x
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D a t
  haveI : BorelSpace (Mx D a t) := ⟨rfl⟩
  obtain ⟨hc, K, hK, hC⟩ := GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ a n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ a n Φ.1 Φ.2)
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajInt.maj_integrable D θ hθ a t (fun _ _ => True) 0 μt inferInstance
    (.of_forall fun _ _ _ h => (h trivial).elim) (fun s _ => map_add_right_eq_self μt s)
  obtain ⟨C, hC⟩ := hC N
  have hK' : IsCompact (colPr hn '' K) := hK.image (continuous_colPr hn)
  have hC0 : ∀ v, ‖Φ.1 (jn hn x v)‖ ≤ |C| * GlobalTheory.Unf.maj θ (colPr hn '' K) N v := fun v =>
    (hC _).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (GlobalTheory.Unf.maj_nonneg θ K N _)).trans
      (mul_le_mul_of_nonneg_left (maj_jn_le θ hn K N x v) (abs_nonneg C)))
  exact ((hN _ hK').const_mul |C|).mono' (hc.comp (continuous_jn hn x)).aestronglyMeasurable (.of_forall hC0)

end GlobalTheory.CompanionTheory.ColSlice
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerVolumeAlmostAll
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab

section Rows

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mem_latV_iff_rows {d M n : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    X ∈ latV b v ↔ ∀ a, (fun _ : Fin 1 => X a) ∈ latV b v :=
  ⟨fun h a _ i k => h a i k, fun h a i k => h a 0 i k⟩

theorem actW_mem_iff (σ : E →ₐ[F] E) {d M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (g : HA (Fv F v) σ J)
    (hg : latStab σ J b v g) (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    actW (Fv F v) σ J g X ∈ latV b v ↔ X ∈ latV b v := by
  rw [mem_latV_iff_rows, mem_latV_iff_rows b v X]
  exact forall_congr' fun a => hg fun _ => X a

theorem consA_mem_iff {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F)
    (a : Fin 1 → Fin n → Fv F v ⊗[F] E) (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    consA a Y ∈ latV b v ↔ a ∈ latV b v ∧ Y ∈ latV b v := by
  constructor
  · intro hX
    refine ⟨fun p j k => ?_, fun j i k => ?_⟩
    · have := hX j.succ 0 k
      rw [Subsingleton.elim p 0]
      simpa [consA] using this
    · have := hX j.succ i.succ.succ k
      simpa [consA] using this
  · rintro ⟨ha, hY⟩ p
    refine Fin.cases ?_ (fun j => ?_) p
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro k
        simpa [consA] using GlobalTheory.CompanionTheory.SW.LatRat.one_mem_latR h k
      · simp [consA]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro k
        simpa [consA] using ha 0 j k
      · refine Fin.cases ?_ (fun i => ?_) i
        · simp [consA]
        · intro k
          simpa [consA] using hY j i k

end Rows

theorem stageInt_latStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ (m : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : HA (Fv F v) σ (hypOne J)), latStab σ (hypOne J) b v g → stageInt (Fv F v) σ J b lam m ((latV b v).indicator 1) g = m (latV b v) := by
  intro F E _ _ _ _ _ σ hCM M J _ n d b
  have h0 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k,
      algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => GlobalTheory.CompanionTheory.SW.LatRat.eventually_integral (b.repr (1 : E) k)
  filter_upwards [h0] with v hv
  intro lam hlam m g hg
  classical
  have hmass : coordW (Fv F v) b lam 1 n (latV b v) = 1 := by
    choose std hstd using GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdV F
    have hfam : ∀ w, IsStdV w (Function.update std v lam w) := by
      intro w
      by_cases hw : w = v
      · subst hw
        simpa using hlam
      · simpa [Function.update_of_ne hw] using hstd w
    simpa using GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.coordW_latV σ hCM b (Function.update std v lam) hfam 1 n v
  have hin : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E,
      ∫⁻ a, (latV b v).indicator 1 (actW (Fv F v) σ (hypOne J) g (consA a Y))
        ∂(coordW (Fv F v) b lam 1 n) = (latV b v).indicator 1 Y := by
    intro Y
    by_cases hY : Y ∈ latV b v
    · have hf : (fun a : Fin 1 → Fin n → Fv F v ⊗[F] E =>
          (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ (hypOne J) g (consA a Y))) =
          (latV b v).indicator 1 := by
        funext a
        by_cases ha : a ∈ latV b v
        · rw [Set.indicator_of_mem ha, Set.indicator_of_mem
            ((actW_mem_iff σ _ b v g hg _).2 ((consA_mem_iff hv a Y).2 ⟨ha, hY⟩))]
          rfl
        · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem
            fun hc => ha ((consA_mem_iff hv a Y).1 ((actW_mem_iff σ _ b v g hg _).1 hc)).1]
      rw [hf, lintegral_indicator_one (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ hCM b 1 n v), hmass,
        Set.indicator_of_mem hY]
      rfl
    · have hf : (fun a : Fin 1 → Fin n → Fv F v ⊗[F] E =>
          (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ (hypOne J) g (consA a Y))) = 0 := by
        funext a
        exact Set.indicator_of_notMem
          (fun hc => hY ((consA_mem_iff hv a Y).1 ((actW_mem_iff σ _ b v g hg _).1 hc)).2) _
      rw [hf, Set.indicator_of_notMem hY, lintegral_zero_fun]
  unfold stageInt
  simp_rw [hin]
  exact lintegral_indicator_one (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ hCM b n M v)

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen

theorem lip_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : PI.VolStabS.TensAllW.LIP S) : PI.VolStabS.TensAllW.LIP R := by
  intro m n _ _ _ _ W hW
  obtain ⟨P, hP⟩ := h m n (W.map e) (by
    intro c hc
    have hc' : W *ᵥ (fun j => e.symm (c j)) = 0 := by
      funext i
      apply e.injective
      have := congrFun hc i
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum] using this
    have h0 := hW _ hc'
    funext j
    have := congrFun h0 j
    simpa using this)
  refine ⟨P.map e.symm, ?_⟩
  ext i j
  apply e.injective
  have := congrFun (congrFun hP i) j
  simp only [Matrix.mul_apply, Matrix.map_apply] at this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  simp only [map_mul, Matrix.map_apply, RingEquiv.apply_symm_apply]
  rw [this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem lip_of_artinian_reduced (R : Type) [CommRing R] [IsArtinianRing R] [IsReduced R] :
    PI.VolStabS.TensAllW.LIP R := by
  classical
  letI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  letI : ∀ m : MaximalSpectrum R, Field (R ⧸ m.asIdeal) := fun m =>
    Ideal.Quotient.field m.asIdeal
  exact lip_of_ringEquiv (IsArtinianRing.equivPi R)
    (PI.VolStabS.TensAllW.lip_pi (fun m : MaximalSpectrum R => R ⧸ m.asIdeal)
      (fun m => PI.VolStabS.TensAllW.lip_field _))

theorem isOpen_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ), IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  intro F E _ _ _ _ _ σ _ R _ _ _ _ _ hR n M
  obtain ⟨hT, -, -, -, hA, hRed, hU, -⟩ := hR
  haveI := hT
  haveI := hA
  haveI := hRed
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hUo : IsOpen {r : R | IsUnit r} := by
    have := hU.isOpen_range
    convert this using 1
    ext r
    simp [IsUnit]
  exact PI.VolStabS.TensAllW.isOpen_linIndep (Module.finBasis F E) R hUo
    (lip_of_artinian_reduced R)

end GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAdelic
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem sb_integrable_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Integrable Φ dx := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ dx hdx Φ hΦ
  exact (GlobalTheory.CompanionTheory.SiegelND.CoefSum.continuous_integrable_tuple σ hCM M n dx hdx.1 Φ hΦ).2

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlotLevelSubgroupsExistStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.position_level_subgroups_exist : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂),
    ∃ L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl),
      (∀ i, IsOpen (L i : Set (GLw a i.pl × GLw b i.pl))) ∧ (∀ᶠ i in cofinite, L i = K2 a b i.pl) ∧
      (∀ i, ∀ k ∈ L i, ∀ x, sf φ₁ φ₂ i (x * k) = sf φ₁ φ₂ i x) ∧
      (∀ i : Slot S, HasCompactSupport (sf φ₁ φ₂ i)) ∧
      ∀ᶠ i : Slot S in cofinite, sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1 := by
  first | exact @GlobalTheory.CompanionTheory.PositionTest.exists_factor_level₂ | exact GlobalTheory.CompanionTheory.PositionTest.exists_factor_level₂ | (intros; apply GlobalTheory.CompanionTheory.PositionTest.exists_factor_level₂ <;> assumption)
end

