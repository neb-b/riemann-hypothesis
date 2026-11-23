module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothAutomorphicOpenInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0440
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0509
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0432
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0438
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalAddOfKill
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0680
public import GroundTheory.PAdicHodge.NormalizedTrace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0683
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0684
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupProjections
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSets
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
public import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0681
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0676
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0678
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0682
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantOfLieOneLEqZero
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.CuspFinGL.Split

theorem cuspRapidDecaySiegelGL : GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ
  have hs := GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hφ.1.level
  exact GlobalTheory.CompanionTheory.SiegelDecay.rapid_decay_of_one_parabolic_bounds E a φ.1 hc
    (GlobalTheory.CompanionTheory.GGPS.ggps_bound E a φ.1 hs (GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E a φ hφ.1)
      (GlobalTheory.CompanionTheory.AutLevel.exists_open_level E a φ hφ.1) (GlobalTheory.CompanionTheory.CuspBridge.isCuspidal_of_isCuspForm E a φ hφ)
      (GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv E a φ hs hφ.1) (GlobalTheory.CompanionTheory.BoxBound.box_bound E a φ hφ.1))

theorem cuspFormsBoundedGL : GlobalTheory.Published.CuspFormsBoundedGL :=
  GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay cuspRapidDecaySiegelGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem cuspFin_zero : CuspFin E 0 := by
  intro L hL W _ _ _ ρ hρ J hJ
  haveI : Finite (GA E 0) := Finite.of_subsingleton
  haveI : FiniteDimensional ℂ (GA E 0 → ℂ) := inferInstance
  infer_instance

theorem invariant_of_lie_oneL_eq_zero {a : ℕ} (ψ : Sm E a) (h : lie E a (oneL E a) ψ = 0) (t : ℝ) (g : GA E a) :
    ψ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = ψ.1 g := by
  rw [CuspidalL2GL.splitCentre_comm]
  have hd : ∀ s, HasDerivAt (fun s : ℝ => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) 0 s := by
    intro s
    have := (GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre) E a ψ g s
    rwa [h] at this
  have := is_const_of_deriv_eq_zero (f := fun s : ℝ => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [CuspidalL2GL.splitCentre_zero] using this

theorem cuspFin_pos {a : ℕ} (ha : 0 < a) : CuspFin E a := by
  intro L hL W _ _ _ ρ hρ J hJ
  set V := Submodule.span ℂ {φ : Sm E a | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1} with hV
  have hVC : ∀ φ ∈ V, φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 := (GlobalTheory.CompanionTheory.CuspSubspace.mem_of_mem_span_cuspForms) E a L W ρ J
  set z := lie E a (oneL E a) with hz
  obtain ⟨p, hpm, hp⟩ := GlobalTheory.CompanionTheory.Affgl.minpoly_on_killed E a J hJ z (GlobalTheory.CompanionTheory.CapelliTrace.lie_oneL_mem_Zalg E a)
  obtain ⟨T, w, hTw⟩ := (GlobalTheory.CompanionTheory.LinearODE.deriv_zero_eq_sum) p hpm
  have hstab : ∀ φ ∈ V, z φ ∈ V := by
    intro φ hφ
    obtain ⟨hg, hc⟩ := hVC φ hφ
    have key : z φ = ∑ t ∈ T, w t • rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ := by
      apply Subtype.ext
      funext g
      have h := hTw (fun k s => ((z ^ k) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
        (fun k s => by
          have h := (GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre) E a ((z ^ k) φ) g s
          rwa [← Module.End.mul_apply, ← pow_succ'] at h)
        (fun s => by
          have h0 := congrArg (fun ψ : Sm E a => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (hp φ hg.2.2.2)
          simpa [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply] using h0)
      simp only [pow_one, pow_zero, Module.End.one_apply, CuspidalL2GL.splitCentre_zero, mul_one] at h
      rw [h, Submodule.coe_sum, Finset.sum_apply]
      rfl
    rw [key]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _
      (Submodule.subset_span ((GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem) E a L W ρ J hJ.1 φ hg hc t))
  refine (GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces) (Sm E a) z V hstab p hpm.ne_zero (fun v hv => hp v (hVC v hv).1.2.2.2) fun c => ?_
  obtain ⟨χ, L', J', hL', hJ', hχ⟩ := (GlobalTheory.CompanionTheory.CuspTwist.twist_central) E a ha L hL W ρ hρ J hJ c
  have hfin := (GlobalTheory.CompanionTheory.CuspInvariant.cuspInvFin) cuspFormsBoundedGL (GlobalTheory.CompanionTheory.UnifAlpha.unifAlpha) E a L' hL' W ρ hρ J' hJ'
  have hle : (Submodule.span ℂ {v | v ∈ V ∧ z v = c • v}).map (mulChi a χ).toLinearMap ≤
      Submodule.span ℂ {φ | φ ∈ genSpace L' ρ J' ∧ IsCuspidal φ.1 ∧
        ∀ t g, φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = φ.1 g} := by
    rw [Submodule.map_span_le]
    rintro v ⟨hv, hzv⟩
    obtain ⟨hg, hc⟩ := hVC v hv
    obtain ⟨h1, h2, h3⟩ := hχ v hg hc hzv
    exact Submodule.subset_span ⟨h1, h2, invariant_of_lie_oneL_eq_zero _ h3⟩
  haveI := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (mulChi a χ).injective _).symm

theorem cuspFin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), CuspFin E a := by
  intro E _ _ _ a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact cuspFin_zero
  · exact cuspFin_pos ha

end GlobalTheory.CompanionTheory.CuspFinGL.Split
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalImageOfUnipotentElementStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_image_of_unipotent_element : ∀ (D : D7) (n : ℕ) (nb : hermA D n → G D n), IsNMap nb → ∀ (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n), thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x)) = nU (tauC τ x.1) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.thU_proj_nMap | exact GlobalTheory.CompanionTheory.Jp.thU_proj_nMap | (intros; apply GlobalTheory.CompanionTheory.Jp.thU_proj_nMap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemMaximalCompactIffIntegralImageStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maximal_compact_iff_integral_image : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (g : GLoc D.sp.cm.sig (Jst D n) v), g ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v ↔ thU D n v τ g ∈ (inL (O := Ov D v) (L := Lv D v) (n := n)).range := by
  first | exact @GlobalTheory.CompanionTheory.Jp.SplitK.mem_KUpFin_iff | exact GlobalTheory.CompanionTheory.Jp.SplitK.mem_KUpFin_iff | (intros; apply GlobalTheory.CompanionTheory.Jp.SplitK.mem_KUpFin_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusUpperParabolicLocalStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_upper_parabolic_local : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (y : GLoc D.sp.cm.sig (Jst D n) v) (a d : GL (Fin n) (Fv D.host.F v)) (b : Matrix (Fin n) (Fin n) (Fv D.host.F v)), thU D n v τ y = pM a d b → ∃ hy : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv D.host.F v) D.sp.cm.sig (Jst D n), absEv D.host.F D.host.E v (GlobalTheory.LocIntw.aUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) ⟨y, hy⟩) = nvL D v (Matrix.GeneralLinearGroup.det a) / nvL D v (Matrix.GeneralLinearGroup.det d) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.UpTri.upperParabolic_height | exact GlobalTheory.CompanionTheory.Jp.UpTri.upperParabolic_height | (intros; apply GlobalTheory.CompanionTheory.Jp.UpTri.upperParabolic_height <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedValuationUniformizerStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_valuation_uniformizer : ∀ (D : D7) (v : Pl D) (ϖ : Ov D v), Irreducible ϖ → ∀ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → NvOK (O := Ov D v) (nvL D v) w := by
  first | exact @GlobalTheory.CompanionTheory.Jp.nvOK_nvL | exact GlobalTheory.CompanionTheory.Jp.nvOK_nvL | (intros; apply GlobalTheory.CompanionTheory.Jp.nvOK_nvL <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def Psi (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) : ℝ≥0∞ :=
  {Y : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin Y) ∈ A v}.indicator
    (fun Y => ENNReal.ofReal (φ (projInf Y))) Y

def Th (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (y : (AF F ⊗[F] E)ˣ) : ℝ≥0∞ :=
  ∑' X : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _),
    Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X.1 a i))

def ofF : (AF F)ˣ →* (AF F ⊗[F] E)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : AF F →ₐ[F] AF F ⊗[F] E).toMonoidHom

def ofE : Eˣ →* (AF F ⊗[F] E)ˣ := Units.map (inclR (AF F)).toMonoidHom

end

def cV {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    AF F ⊗[F] E →ₐ[F] Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).comp
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))

def cI {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] :
    AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E :=
  Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)

def ue {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E) (h : HA R σ J) : (R ⊗[F] E)ˣ :=
  Matrix.GeneralLinearGroup.det (HA.mat R σ J h)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientHeisenbergExpansion
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.PcShear

theorem jc_zero {D : D7} {ρ p : ℕ} (y : Mx D ρ p) : GlobalTheory.CompanionTheory.FJE.jc y 0 = 0 := by
  apply Subtype.ext
  have h : adj (0 : Mx D ρ p) = 0 := by
    ext i j
    simp [adj]
  show (HMul.hMul y (adj (0 : Mx D ρ p)) : Mx D ρ ρ) + (HMul.hMul (0 : Mx D ρ p) (adj y) : Mx D ρ ρ) = _
  rw [h]
  simp

theorem chz_neg {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (z : hermA D ρ) : chz ψ b₀ (-z) = conj (chz ψ b₀ z) := by
  obtain ⟨hadd, hnorm, -, -⟩ := _root_.GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts ψ hψ b₀
  have h0 : chz ψ b₀ (0 : hermA D ρ) = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have hne : chz ψ b₀ (0 : hermA D ρ) ≠ 0 := by
      intro h'
      have := hnorm 0
      rw [h'] at this
      simp at this
    exact (mul_eq_left₀ hne).1 h.symm
  have h1 : chz ψ b₀ z * chz ψ b₀ (-z) = 1 := by
    rw [← hadd, add_neg_cancel, h0]
  have h2 : chz ψ b₀ z * conj (chz ψ b₀ z) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    simp
  have hne : chz ψ b₀ z ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem zc_sh {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (F : G D n → ℂ) (hF : LeftInv (GF D n) F)
    (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (k : G D n) :
    zc M m ψ b₀ F (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * k) = zc M m ψ b₀ F k := by
  unfold zc
  congr 1
  funext z
  have hc : M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * M.nzx z 0 = M.nzx z 0 * M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) := by
    have := _root_.GlobalTheory.CompanionTheory.FJE.sh_mul_nzx M (GlobalTheory.CompanionTheory.FJE.rt ξ) z 0
    rwa [jc_zero, add_zero] at this
  have hr : M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n := (_root_.GlobalTheory.CompanionTheory.FJE.rat_maps_mem_GF M).1 ξ
  rw [← mul_assoc, ← hc, mul_assoc, hF _ hr]

theorem zc_at {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (F : G D n → ℂ)
    (hF : LeftInv (GF D n) F) (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (h : G D n) (x : Mx D ρ p) :
    zc M m ψ b₀ F (M.nzx 0 x * (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h)) =
      conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ)) * zc M m ψ b₀ F (M.nzx 0 x * h) := by
  set c : hermA D ρ := -GlobalTheory.CompanionTheory.FJE.jc (GlobalTheory.CompanionTheory.FJE.rt ξ) x with hc
  have h1 : M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * M.nzx c x = M.nzx 0 x * M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) := by
    have := _root_.GlobalTheory.CompanionTheory.FJE.sh_mul_nzx M (GlobalTheory.CompanionTheory.FJE.rt ξ) c x
    rwa [hc, neg_add_cancel] at this
  have h2 : M.nzx c x = M.nzx c 0 * M.nzx 0 x := by
    rw [GlobalTheory.CompanionTheory.NzxAdd.nzx_add, add_zero, zero_add]
  have h3 : M.nzx 0 x * (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h) =
      M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * (M.nzx c 0 * (M.nzx 0 x * h)) := by
    rw [← mul_assoc, ← h1, h2]
    simp only [mul_assoc]
  rw [h3, zc_sh M m ψ b₀ F hF, _root_.GlobalTheory.CompanionTheory.ZcShift.zc_shift M m ψ hψ b₀ F hF, hc, chz_neg ψ hψ, _root_.GlobalTheory.CompanionTheory.FJE.chz_jc]

theorem pc_sh : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (h : G D n), pc M m ψ b₀ F (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h) = ∫ x in m.𝓕, conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ)) * zc M m ψ b₀ F (M.nzx 0 x * h) ∂m.μ := by
  intro D n ρ p hn M m ψ hψ b₀ F hF ξ h
  unfold PositivityTheory.Rg.Rsw.pc
  congr 1
  funext x
  exact zc_at M m ψ hψ b₀ F hF ξ h x

end GlobalTheory.CompanionTheory.FJE.PcShear
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilRankOneBaseCase
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal Matrix
open PositivityTheory.SiegelWeilFormula.Densx PositivityTheory.Rg.Base1

namespace GlobalTheory.CompanionTheory.Base1

private theorem isClosed_nonnegReal : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

private theorem mul_mem_nonnegReal {z w : ℂ} (hz : z ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re})
    (hw : w ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}) : z * w ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
  obtain ⟨hz0, hz1⟩ := hz
  obtain ⟨hw0, hw1⟩ := hw
  refine ⟨by simp [Complex.mul_im, hz0, hw0], ?_⟩
  simp only [Complex.mul_re, hz0, hw0, mul_zero, sub_zero]
  exact mul_nonneg hz1 hw1

private theorem tprod_mem_nonnegReal {ι : Type*} (f : ι → ℂ)
    (hf : ∀ i, f i ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}) :
    ∏' i, f i ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
  by_cases hm : Multipliable f
  · refine isClosed_nonnegReal.mem_of_tendsto hm.hasProd (Eventually.of_forall fun s => ?_)
    exact Finset.prod_induction f (fun z => z ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re})
      (fun _ _ => mul_mem_nonnegReal) (by simp) (fun i _ => hf i)
  · rw [tprod_eq_one_of_not_multipliable hm]
    simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem factor_mem (v : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : 1 < s) :
    (1 - PositivityTheory.SiegelWeilFormula.Gen.eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) ∈
      {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hc : (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)) = ((q ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hq0]
    simp [hq]
  have hle : q ^ (-s) ≤ 1 := by
    rcases Nat.eq_zero_or_pos (Ideal.absNorm v.asIdeal) with h | h
    · have : q = 0 := by simp [hq, h]
      rw [this, Real.zero_rpow (by linarith)]
      exact zero_le_one
    · exact Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.2 h) (by linarith)
  have hnn : 0 ≤ q ^ (-s) := Real.rpow_nonneg hq0 _
  rw [hc]
  unfold PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs
  · refine ⟨by simp, ?_⟩
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.one_im, Complex.ofReal_im]
    linarith
  · refine ⟨by simp, ?_⟩
    simp only [one_mul, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith

theorem lamLim_nonneg {Λ : ℂ} (h : IsLamLim F E Λ) : Λ.im = 0 ∧ 0 ≤ Λ.re := by
  refine isClosed_nonnegReal.mem_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact tprod_mem_nonnegReal _ fun v => factor_mem v hs

theorem lamLim_unique {Λ Λ' : ℂ} (h : IsLamLim F E Λ) (h' : IsLamLim F E Λ') : Λ = Λ' :=
  tendsto_nhds_unique h h'


variable (F E) in
theorem exists_half_lamLim : ∃ c : ℝ≥0, ∀ Λ : ℂ, IsLamLim F E Λ → ((c : ℝ) : ℂ) = Λ / 2 := by
  by_cases h : ∃ Λ, IsLamLim F E Λ
  · obtain ⟨Λ₀, h₀⟩ := h
    obtain ⟨him, hre⟩ := lamLim_nonneg h₀
    refine ⟨Real.toNNReal (Λ₀.re / 2), fun Λ hΛ => ?_⟩
    rw [lamLim_unique hΛ h₀, Real.coe_toNNReal _ (by linarith)]
    apply Complex.ext <;> simp [him]
  · exact ⟨0, fun Λ hΛ => absurd ⟨Λ, hΛ⟩ h⟩

theorem baseOne_of_parts : Prop1 → Simil → Hasse → Cnt → PositivityTheory.SiegelWeilFormula.Densx.BaseOne := by
  intro hP hS hH hC F E _ _ _ _ _ σ hcm J hJ T hT hd d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  obtain ⟨β, rfl, hβ, he⟩ := _root_.GlobalTheory.CompanionTheory.SW.hermOne_eq_scal F E σ hcm T hT
  have hβ0 : β ≠ 0 := hβ hd
  simp only [he]
  have hsph : {X : Fin 1 → Fin 1 → E | gramE σ J X = fun _ _ => algebraMap F E β} = sph σ J β := rfl
  rw [hsph]
  obtain ⟨c, hc⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β hβ0
  by_cases h0 : mi (hermScal (Ainf F) σ (algebraMap F _ β)) = 0 ∨
      ∃ v, (cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β))) = 0
  · obtain ⟨c', hc'⟩ := exists_half_lamLim F E
    refine ⟨c', ?_, hc'⟩
    rw [(_root_.GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero F E σ hcm d b 1 1 _ c _ _).2.1 hc h0]
    exact (_root_.GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero F E σ hcm d b 1 1 0 c' _ _).2.2 hc.1 hc.2.1 h0
  push Not at h0
  have hmne : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) ≠ 0 := fun v hz =>
    h0.2 v (by rw [hz, smul_zero])
  have hne : (sph σ J β).Nonempty :=
    hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β hβ0 h0.1 hmne
  have hall : ∀ β' : F, β' ≠ 0 → EP b μ 𝓕 mi m β' c := by
    intro β' hβ'
    by_cases hn : (sph σ J β').Nonempty
    · exact hS F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β β' hβ0 hβ' hne hn c hc
    · obtain ⟨c', hc'⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β' hβ'
      have hz : mi (hermScal (Ainf F) σ (algebraMap F _ β')) = 0 ∨
          ∃ v, (cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β'))) = 0 := by
        by_contra hz
        push Not at hz
        exact hn (hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β' hβ' hz.1
          fun v hv => hz.2 v (by rw [hv, smul_zero]))
      have ht : thetaMeas σ J μ 𝓕 (sph σ J β') = 0 := by
        have he' : IsEmpty (sph σ J β') := Set.not_nonempty_iff_eq_empty.1 hn ▸ inferInstance
        simp [thetaMeas]
      unfold EP
      rw [ht]
      exact (_root_.GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero F E σ hcm d b 1 1 0 c _ _).2.2 hc'.1 hc'.2.1 hz
  exact ⟨c, hc, hC F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm c hall⟩

end GlobalTheory.CompanionTheory.Base1
end

