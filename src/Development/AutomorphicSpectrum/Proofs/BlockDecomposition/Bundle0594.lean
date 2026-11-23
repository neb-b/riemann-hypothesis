module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.AdmProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0578
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityOfFourierPairingIntegrable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalShuffleCountProduct
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0579
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermConvolutionHecke
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleParabolicInduction
section
namespace GlobalTheory.CompanionTheory.ProdAdm

theorem isAdmissible_multiProd_smIrr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {c n : ℕ} (N : Fin c → ℕ) (h : ∑ i, N i = n)
    (σ : ∀ i, GlobalTheory.CuspRep.SmIrr (GL (Fin (N i)) k)) :
    GlobalTheory.PRep.IsAdmissible (GlobalTheory.SmGL.multiProd (GlobalTheory.SmGL.stdBlocks N h) fun i => (σ i).ρ) :=
  PositivityTheory.PfBern.Props1.isAdmissible_parInd_of _ _
    (GlobalTheory.ContraProd.isAdmissible_piTensor _ _ fun i =>
      PositivityTheory.PfBern.Props1.irrSmoothAdmissible_holds k (N i) (σ i).V (σ i).ρ (σ i).smooth (σ i).irred)

end GlobalTheory.CompanionTheory.ProdAdm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCompactSetDensityBounded
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens NumberField

open GlobalTheory.CompanionTheory.SiegelND.Coef (gramH)

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens

theorem exists_cutoff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hF : IsTotallyReal F) (n M : ℕ) (S : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (hS : IsCompact S) :
    ∃ P : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0, Continuous P ∧ HasCompactSupport P ∧ (∀ X ∈ S, 1 ≤ P X) ∧
      GlobalTheory.Published.SiegelOneVector.IsSchwartzArch (F := F) (E := E) fun X => ((P X : ℝ) : ℂ) := by
  haveI := hF
  obtain ⟨k, eK, hK⟩ := PI.VolStabS.exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := PI.VolStabS.exists_coord_pi eK hK (Fin M)
  obtain ⟨N, eV, hV⟩ := PI.VolStabS.exists_coord_pi e1 h1 (Fin n)
  let eA : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ) := { eV.toEquiv with map_add' := hV }
  have hb : Bornology.IsBounded (eV '' S) := (hS.image eV.continuous).isBounded
  obtain ⟨R, hR0, hR⟩ := hb.subset_closedBall_lt 0 0
  let β : ContDiffBump (0 : Fin N → ℝ) := ⟨R, R + 1, hR0, by linarith⟩
  have hs : HasCompactSupport fun z => ((β z : ℝ) : ℂ) := β.hasCompactSupport.comp_left Complex.ofReal_zero
  let f : SchwartzMap (Fin N → ℝ) ℂ := hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)
  refine ⟨fun X => ⟨β (eV X), β.nonneg⟩, ?_, ?_, fun X hX => ?_,
    ⟨N, eA, eV.continuous, eV.symm.continuous, f, fun _ => rfl⟩⟩
  · exact Continuous.subtype_mk (β.continuous.comp eV.continuous) _
  · have h2 : HasCompactSupport fun X => β (eV X) := β.hasCompactSupport.comp_homeomorph eV
    have h3 : (fun X => (⟨β (eV X), β.nonneg⟩ : ℝ≥0)) = Real.toNNReal ∘ fun X => β (eV X) :=
      funext fun X => (Real.toNNReal_of_nonneg β.nonneg).symm
    rw [h3]
    exact h2.comp_left (g := Real.toNNReal) (by simp)
  · have : β (eV X) = 1 := β.one_of_mem_closedBall (hR ⟨X, hX, rfl⟩)
    exact NNReal.coe_le_coe.1 (show (1 : ℝ) ≤ β (eV X) from this.ge)

theorem density_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ S : Set (Fin n → Fin M → Ainf F ⊗[F] E), IsCompact S → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n) (GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F)) S C := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ hM d b lam hlam S hS
  have hLoc := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  obtain ⟨l1, l2, l3, l4, -, -, -, -⟩ := id hLoc
  haveI := l1
  haveI := l2
  haveI := l3
  haveI := l4
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, t10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  obtain ⟨x1, x2, x3, x4, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Ainf F) n
  haveI := x1
  haveI := x2
  haveI := x3
  haveI := x4
  haveI : LocallyCompactSpace (HermR (Ainf F) σ n) := x1
  haveI : SecondCountableTopology (HermR (Ainf F) σ n) := x2
  haveI : T2Space (HermR (Ainf F) σ n) := x3
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b lam hlam
  set μ := GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M with hμdef
  let ν : Measure (HermR (Ainf F) σ n) := GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n
  haveI hμH : μ.IsAddHaarMeasure := hW n M
  haveI hνH : ν.IsAddHaarMeasure := hH n
  have hqc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => gramH hCM hJ (Ainf F) X :=
    (t10 n M J).subtype_mk _
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.SW.CharEx.exists_isCharAF F
  obtain ⟨ρ, e, hρ, he, heρ, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.real_iso F hCM.1
  obtain ⟨a, ha, hinf, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Glob.CharAF.exists_char_data F hCM.1 ρ e hρ he heρ ψ hψ
  obtain ⟨τ, Θ, hΘ⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.exists_isCoord F E σ hCM ρ e hρ he heρ
  have c1 : Continuous Θ := hΘ.1.continuous
  have c2 : Continuous Θ.symm := HermCoord.continuous_symm Θ hΘ.1
  let Ψ0 := HermCoord.hermEquiv σ Θ hΘ.2.1 n
  have h1 : Continuous Ψ0 := HermCoord.continuous_hermEquiv σ Θ hΘ.2.1 c1 n
  have h2 : Continuous Ψ0.symm := HermCoord.continuous_hermEquiv_symm σ Θ hΘ.2.1 c2 n
  let Ψh : HermR (Ainf F) σ n ≃ₜ (InfinitePlace F → hermC n) :=
    { toEquiv := Ψ0.toEquiv, continuous_toFun := h1, continuous_invFun := h2 }
  let Ψ : HermR (Ainf F) σ n ≃ᵐ (InfinitePlace F → hermC n) := Ψh.toMeasurableEquiv
  have hνΨ : (ν.map Ψ).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν Ψ0 h1 h2
  obtain ⟨P, hPc, hPs, hP1, hPS⟩ := exists_cutoff (E := E) hCM.1 n M S hS
  let c : InfinitePlace F → ℝ := fun w => ρ w a
  have hc : ∀ w, c w ≠ 0 := fun w => by simpa [c] using (map_ne_zero (ρ w)).2 ha
  have hfin : ∫⁻ X, P X ∂μ ≠ ⊤ := by
    have hcs : HasCompactSupport fun X => (P X : ℝ) := hPs.comp_left (g := fun x : ℝ≥0 => (x : ℝ)) rfl
    have hint : Integrable (fun X => (P X : ℝ)) μ :=
      (NNReal.continuous_coe.comp hPc).integrable_of_hasCompactSupport hcs
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hint.2)
    refine lintegral_congr fun X => ?_
    beta_reduce
    rw [Real.enorm_eq_ofReal (NNReal.coe_nonneg (P X)), ENNReal.ofReal_coe_nnreal]
  have hstar := integrable_starLoc_inf F E σ hCM M J hJ n hM ψ hψ μ hμH ν hνH _ hPS
  have hphase : ∀ (b' : HermR (Ainf F) σ n) (X : Fin n → Fin M → Ainf F ⊗[F] E),
      psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
        (Matrix.trace ((b' : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * gramR (Ainf F) σ J X))) =
      Complex.exp (2 * Real.pi * Complex.I * ((pairC n c (Ψ b') (Ψ (gramH hCM hJ (Ainf F) X)) : ℝ) : ℂ)) := by
    intro b' X
    rw [_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord.psiInf_phase F E σ ρ e τ Θ hΘ heρ a ψ hinf M n J _ X]
    congr 3
    rw [phaseM, pairC_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [PhaseCoord.gramC_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      ← PhaseCoord.coord_gramR σ e τ Θ hΘ]
    rfl
  have hi : Integrable (fun b' => ∫ X, ((P X : ℝ≥0) : ℂ) * Complex.exp (2 * Real.pi * Complex.I *
      ((pairC n c (Ψ b') (Ψ (gramH hCM hJ (Ainf F) X)) : ℝ) : ℂ)) ∂μ) ν := by
    refine hstar.congr (Filter.Eventually.of_forall fun b' => ?_)
    show ∫ X, _ ∂μ = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    beta_reduce
    rw [hphase]
  obtain ⟨C, hC, h⟩ := density_transport (pairC n c) (fun u hu => pairC_nondeg hc u hu) μ ν Ψ hνΨ
    (fun X => gramH hCM hJ (Ainf F) X) hqc.measurable P hPc.measurable hfin S hP1 hi
  exact ⟨C, hC, h⟩

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalShuffleCountProductStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_shuffle_count_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), IsCanon Γ → shuffleCount (List.ofFn fun i => decWord (Γ i)).flatten (fun i => decWord (Γ i)) = ∏ i, (Finset.univ.filter fun j => j ≤ i ∧ Γ j = Γ i).card := by
  first | exact @GlobalTheory.CompanionTheory.WordCount.shuffleCount_canon | exact GlobalTheory.CompanionTheory.WordCount.shuffleCount_canon | (intros; apply GlobalTheory.CompanionTheory.WordCount.shuffleCount_canon <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDoubleComplexMap
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre

section MorDbl

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} {ι ι' : Type}
  {U : ι → ObjectProperty C} {U' : ι' → ObjectProperty C'} {hU : ∀ α, Cosieve (U α)}
  {hU' : ∀ α, Cosieve (U' α)}

def nerveG (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (p : ℕ) :
    (CH.cech (idxπ U' hU') p).Elements ⥤ (CH.cech (idxπ U hU) p).Elements where
  obj x := (CH.cech (idxπ U hU) p).elementsMk (m.G.obj x.obj)
    ⟨fun k => ⟨τ (x.val.1 k).1, hτ _ _ (x.val.1 k).2⟩, fun _ _ => rfl⟩
  map {_x y} f := ⟨m.G.map f.hom, Subtype.ext (funext fun k => Subtype.ext
    (congrArg (fun z : (CH.cech (idxπ U' hU') p).obj y.obj => τ (z.1 k).1) f.map_val))⟩
  map_id x := Functor.Elements.hom_ext (m.G.map_id x.obj)
  map_comp f g := Functor.Elements.hom_ext (m.G.map_comp f.hom g.hom)

def nerveM (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (p : ℕ) :
    CH.Mor (CH.elF (CH.cech (idxπ U hU) p) F) (CH.elF (CH.cech (idxπ U' hU') p) F') (RingHom.id R) where
  G := nerveG m τ hτ p
  τ T := m.τ T.obj
  nat φ x := m.nat φ.hom x

theorem nerveM_face (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T))
    (p q : ℕ) (k : Fin (p + 2)) (x : CH.Cn (CH.elF (CH.cech (idxπ U hU) p) F) q) :
    (CH.elMor (CH.cechMap (idxπ U' hU') k.succAbove) F').pullC q ((nerveM (hU := hU) (hU' := hU') m τ hτ p).pullC q x) =
      (nerveM (hU := hU) (hU' := hU') m τ hτ (p + 1)).pullC q ((CH.elMor (CH.cechMap (idxπ U hU) k.succAbove) F).pullC q x) :=
  rfl

def dblHom (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) :
    DCx.Hom (dbl U hU F) (dbl U' hU' F') (RingHom.id R) where
  f p q := (nerveM m τ hτ p).pullC q
  ch p q x := by
    refine (Cos.d_apply ((CH.cechCos (idxπ U' hU') F').cos q) p _).trans ?_
    refine Eq.trans ?_ (congrArg _ (Cos.d_apply ((CH.cechCos (idxπ U hU) F).cos q) p x).symm)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    exact congrArg _ (nerveM_face m τ hτ p q k x)
  cv p q x := (nerveM m τ hτ p).d_pullC q x

theorem cls_eq_of_eq {K : Cx.{1} R} {n : ℕ} {a b : K.X n} (h : a = b) (ha : K.d n a = 0) (hb : K.d n b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h; rfl

theorem dblHom_sgl {K L : DCx.{1} R} (φ : DCx.Hom K L (RingHom.id R)) (a b : ℕ) (y : K.X a b) (p q : ℕ) :
    φ.f p q (K.sgl a b y p q) = L.sgl a b (φ.f a b y) p q := by
  by_cases h : p = a ∧ q = b
  · obtain ⟨rfl, rfl⟩ := h
    rw [K.sgl_self, L.sgl_self]
  · rw [K.sgl_ne _ (by omega), L.sgl_ne _ (by omega), map_zero]

end MorDbl

theorem dbl_mor : ∀ {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R)
    (F' : C' ⥤ ModuleCat.{0} R) {ι ι' : Type} (U : ι → ObjectProperty C) (U' : ι' → ObjectProperty C') (hU : ∀ α, Cosieve (U α))
    (hU' : ∀ α, Cosieve (U' α)) (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)),
    ∃ φ : DCx.Hom (dbl U hU F) (dbl U' hU' F') (RingHom.id R),
      (∀ n (x : CH.H F n), φ.tot.mapH n ((CH.cechAugRow (idxπ U hU) F).edge.mapH n
          ((CH.Mor.restrict F (Functor.Elements.π ((Functor.const C).obj PUnit.{1}))).hom.mapH n x)) =
        (CH.cechAugRow (idxπ U' hU') F').edge.mapH n
          ((CH.Mor.restrict F' (Functor.Elements.π ((Functor.const C').obj PUnit.{1}))).hom.mapH n (m.pull n x))) ∧
      ∀ p q (x : ((dbl U hU F).col p).H q) (i : Fin (p + 1) → ι'),
        (tupM U' hU' F' i).pull q ((φ.col p).mapH q x) =
          (morU m (U := capT U (τ ∘ i)) (U' := capT U' i) fun T hT k => hτ (i k) T (hT k)).pull q ((tupM U hU F (τ ∘ i)).pull q x) := by
  intro R _ C C' _ _ F F' ι ι' U U' hU hU' m τ hτ
  refine ⟨dblHom m τ hτ, fun n x => ?_, fun p q x i => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (P.cls_surj (CH.cx F) n).1 x
    refine cls_eq_of_eq (Subtype.ext (funext fun p => funext fun q => ?_)) _ _
    exact dblHom_sgl (dblHom m τ hτ) 0 n _ p q
  · obtain ⟨a, ha, rfl⟩ := (P.cls_surj ((dbl U hU F).col p) q).1 x
    exact cls_eq_of_eq rfl _ _

end GlobalTheory.CompanionTheory.CechSerre
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterLevelFormula
section
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrLev

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

theorem trace_red_mul {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (red ϖ k A * red ϖ k B) = Ideal.Quotient.mk (lev ϖ k) (∑ a, ∑ c, A a c * B c a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, red, Matrix.map_apply, map_sum, map_mul]

theorem psiLev_holds : PositivityTheory.SiegelWeilFormula.Gunr.PsiLev := by
  unfold PositivityTheory.SiegelWeilFormula.Gunr.PsiLev
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG hT k X hX
  rw [trace_red_mul]
  show _ = PositivityTheory.SiegelWeilFormula.Gunr.psiF ψv ϖ _ k _
  unfold PositivityTheory.SiegelWeilFormula.Gunr.psiF PositivityTheory.PfSWUS.Loc.trPair
  congr 1
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.hermOf, PositivityTheory.SiegelWeilFormula.Gunr.GoodLoc.hermLev, PositivityTheory.SiegelWeilFormula.Gunr.matS,
    Matrix.map_apply, Matrix.of_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
    mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul]
  rw [one_div, map_inv₀, map_ofNat]
  ring

end GlobalTheory.CompanionTheory.GunrLev

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassLevelFormula
section
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrClassLev

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem coe_mul_pS_pow (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (t : S) :
    ((t * hG.pS ^ k : S) : Fv F v ⊗[F] E) = (ϖ ^ k) • (t : Fv F v ⊗[F] E) := by
  rw [Subring.coe_mul, Subring.coe_pow, Algebra.smul_def, map_pow, mul_comm]
  rfl

theorem smul_sub_mem_iff (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (s s' : S) :
    (ϖ ^ k)⁻¹ • (s : Fv F v ⊗[F] E) - (ϖ ^ k)⁻¹ • (s' : Fv F v ⊗[F] E) ∈ S ↔ s - s' ∈ lev hG.pS k := by
  have hne : ϖ ^ k ≠ 0 := pow_ne_zero _ hG.unif_ne
  constructor
  · intro h
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, h⟩, Subtype.ext ?_⟩
    rw [coe_mul_pS_pow hG]
    show (ϖ ^ k) • ((ϖ ^ k)⁻¹ • (s : Fv F v ⊗[F] E) - (ϖ ^ k)⁻¹ • (s' : Fv F v ⊗[F] E)) = (s : Fv F v ⊗[F] E) - s'
    rw [← smul_sub, smul_smul, mul_inv_cancel₀ hne, one_smul]
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    have e : (s : Fv F v ⊗[F] E) - (s' : Fv F v ⊗[F] E) = (ϖ ^ k) • (c : Fv F v ⊗[F] E) := by
      rw [← coe_mul_pS_pow hG, hc, AddSubgroupClass.coe_sub]
    rw [← smul_sub, e, smul_smul, inv_mul_cancel₀ hne, one_smul]
    exact c.2

theorem classLev : ClassLev := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG k X X' hX hX'
  constructor
  · intro h
    refine Matrix.ext fun a b => ?_
    exact Ideal.Quotient.eq.2 ((smul_sub_mem_iff hG k (X a b) (X' a b)).1 (h a b))
  · intro h a b
    exact (smul_sub_mem_iff hG k (X a b) (X' a b)).2 (Ideal.Quotient.eq.1 (congrFun (congrFun h a) b))

end GlobalTheory.CompanionTheory.GunrClassLev

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointsSecondCountableStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_second_countable : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ),
    GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D → SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.secondCountable_cxPts | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.secondCountable_cxPts | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.secondCountable_cxPts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorizationStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.concatenated_jacquet_multiplicity_factorization : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (hpos : ∀ a, 0 < ∑ i, (x a i).1) (hcat : ∑ i, (concat c x i).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), 1 ≤ jm (concat c x) hcat π → ∃ (σ : Fin s → IrrGL (k := k)) (hσ : ∑ a, (σ a).1 = N), (∀ a, (σ a).1 = ∑ i, (x a i).1) ∧ 1 ≤ jm σ hσ π := by
  first | exact @GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse | exact GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse | (intros; apply GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermConvolutionHeckeStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_convolution_hecke : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f₁ f₂ : GLw n w → ℂ, IsHk K' f₁ → IsHk K' f₂ → ∀ x ∈ X, ∀ z ∈ X, ∀ m, phi3 h w (gconv f₁ f₂) x z m = ((X.card : ℂ))⁻¹ * ∑ y ∈ X, mconv (phi3 h w f₁ x y) (phi3 h w f₂ y z) m := by
  first | exact @GlobalTheory.CompanionTheory.ConvMat.constant_term_convolution | exact GlobalTheory.CompanionTheory.ConvMat.constant_term_convolution | (intros; apply GlobalTheory.CompanionTheory.ConvMat.constant_term_convolution <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetIntegralUnramifiedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_integral_unramified : PositivityTheory.SiegelWeilFormula.Gunr.CosetInt := by
  first | exact @GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq | exact GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq | (intros; apply GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetMeasureFormula
section
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrCoset

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_Rv {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (Rv bs v) := by
  have hO : IsOpen ((v.adicCompletionIntegers F : ValuationSubring (Fv F v)) : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  have hc : ∀ k : Fin d, Continuous fun y : Fv F v ⊗[F] E =>
      (Algebra.TensorProduct.basis (Fv F v) bs).repr y k := fun k =>
    (continuous_apply k).comp (GlobalTheory.CompanionTheory.SW.TopK.isHomeomorph_coord (Fv F v) bs).continuous
  have : Rv bs v = ⋂ k : Fin d, (fun y : Fv F v ⊗[F] E =>
      (Algebra.TensorProduct.basis (Fv F v) bs).repr y k) ⁻¹'
        ((v.adicCompletionIntegers F : ValuationSubring (Fv F v)) : Set (Fv F v)) := by
    ext y
    simp [Rv]
  rw [this]
  exact isOpen_iInter_of_finite fun k => hO.preimage (hc k)

theorem continuousAdd_tens (v : HeightOneSpectrum (𝓞 F)) : ContinuousAdd (Fv F v ⊗[F] E) :=
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isModTop (Fv F v)
  IsModuleTopology.toContinuousAdd (Fv F v) _

theorem isOpen_integral_hermitian (σ : E →ₐ[F] E) (n : ℕ) {v : HeightOneSpectrum (𝓞 F)} (S : Subring (Fv F v ⊗[F] E))
    (hS : IsOpen (S : Set (Fv F v ⊗[F] E))) :
    IsOpen (H0 S σ n : Set (HermR (Fv F v) σ n)) := by
  have : (H0 S σ n : Set (HermR (Fv F v) σ n)) =
      ⋂ i : Fin n, ⋂ j : Fin n, (fun b : HermR (Fv F v) σ n =>
        (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j) ⁻¹' (S : Set (Fv F v ⊗[F] E)) := by
    ext b
    simp only [Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hS.preimage (continuous_subtype_val.matrix_elem i j)

theorem cosetMeas : CosetMeas := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := continuousAdd_tens v
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  have hS : IsOpen (S : Set (Fv F v ⊗[F] E)) := by
    rw [hG.carrier]
    exact isOpen_Rv bs v
  haveI : ContinuousAdd (HermR (Fv F v) σ n) := ⟨continuous_induced_rng.2
    ((continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd))⟩
  refine ⟨⟨fun c => (continuous_const.add continuous_id).measurable,
    fun c => (continuous_id.add continuous_const).measurable⟩, fun g => ?_⟩
  have hc : Continuous fun x : HermR (Fv F v) σ n => x + -g := continuous_id.add continuous_const
  have : {x : HermR (Fv F v) σ n | x - g ∈ H0 S σ n} =
      (fun x : HermR (Fv F v) σ n => x + -g) ⁻¹' (H0 S σ n : Set (HermR (Fv F v) σ n)) := by
    ext x
    simp [sub_eq_add_neg]
  rw [this]
  exact ((isOpen_integral_hermitian σ n S hS).preimage hc).measurableSet

end GlobalTheory.CompanionTheory.GunrCoset

end
end

