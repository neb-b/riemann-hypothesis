module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0190
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeRightDerivativeCommutator
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DerBracket

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem bracket_mem_lieAt {τ : D.what₂.Tau} {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) : X * Y - Y * X ∈ lieAt V τ := by

  have hX0 : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  have hY0 : Yᴴ * gramAt D V τ + gramAt D V τ * Y = 0 := hY
  have hX' : Xᴴ * gramAt D V τ = -(gramAt D V τ * X) := eq_neg_of_add_eq_zero_left hX0
  have hY' : Yᴴ * gramAt D V τ = -(gramAt D V τ * Y) := eq_neg_of_add_eq_zero_left hY0
  have e1 : Yᴴ * Xᴴ * gramAt D V τ = gramAt D V τ * Y * X := by
    rw [Matrix.mul_assoc Yᴴ Xᴴ, hX', Matrix.mul_neg, ← Matrix.mul_assoc Yᴴ, hY', Matrix.neg_mul, neg_neg]
  have e2 : Xᴴ * Yᴴ * gramAt D V τ = gramAt D V τ * X * Y := by
    rw [Matrix.mul_assoc Xᴴ Yᴴ, hY', Matrix.mul_neg, ← Matrix.mul_assoc Xᴴ, hX', Matrix.neg_mul, neg_neg]
  show (X * Y - Y * X)ᴴ * gramAt D V τ + gramAt D V τ * (X * Y - Y * X) = 0
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2]
  noncomm_ring

private theorem mem_smF_of_mem_smFun (R : GlobalTheory.SmoothForms.RealPoints θ V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    φ ∈ GlobalTheory.SmoothForms.SmF θ V :=
  (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 hφ)

private theorem rder_eq_opInf_atPlace (R : GlobalTheory.SmoothForms.RealPoints θ V) (τ : D.what₂.Tau) (X : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ)
    (ψ : GlobalTheory.SmoothForms.SmF θ V) :
    Rder θ V τ X.1 ψ.1 = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X) ψ).1 := by
  rw [GlobalTheory.SmoothForms.opInf_coe]
  exact GlobalTheory.SmoothForms.Rder_eq R τ X ψ.1

theorem Rder_bracket (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) :
    Rder θ V τ X (Rder θ V τ Y φ) = Rder θ V τ Y (Rder θ V τ X φ) + Rder θ V τ (X * Y - Y * X) φ := by

  have R : GlobalTheory.SmoothForms.RealPoints θ V := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hXY := bracket_mem_lieAt hX hY
  set ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, mem_smF_of_mem_smFun R hφ⟩ with hψ
  set Xl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ X).1 hX⟩ with hXl
  set Yl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨Y, (GlobalTheory.SmoothForms.mem_lieAt_iff τ Y).1 hY⟩ with hYl
  set Zl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X * Y - Y * X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ _).1 hXY⟩ with hZl
  have e := GlobalTheory.SmoothForms.opAt_bracket R τ Xl Yl Zl rfl
  have a1 : Rder θ V τ Y φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ).1 := rder_eq_opInf_atPlace R τ Yl ψ
  have a2 : Rder θ V τ X φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 := rder_eq_opInf_atPlace R τ Xl ψ
  have a3 : Rder θ V τ X (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ).1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ)).1 := rder_eq_opInf_atPlace R τ Xl _
  have a4 : Rder θ V τ Y (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ)).1 := rder_eq_opInf_atPlace R τ Yl _
  have a5 : Rder θ V τ (X * Y - Y * X) φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Zl) ψ).1 :=
    rder_eq_opInf_atPlace R τ Zl ψ
  rw [a1, a3, a2, a4, a5, e, LinearMap.sub_apply, Submodule.coe_sub]
  change _ = _ + ((GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ)).1 -
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ)).1)
  abel

theorem Rder_comm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ τ' : D.what₂.Tau} (hτ : τ ≠ τ')
    {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ') :
    Rder θ V τ X (Rder θ V τ' Y φ) = Rder θ V τ' Y (Rder θ V τ X φ) := by

  have R : GlobalTheory.SmoothForms.RealPoints θ V := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  set ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, mem_smF_of_mem_smFun R hφ⟩ with hψ
  set Xl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ X).1 hX⟩ with hXl
  set Yl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ' := ⟨Y, (GlobalTheory.SmoothForms.mem_lieAt_iff τ' Y).1 hY⟩ with hYl
  have hc := (GlobalTheory.SmoothForms.opAt_comm R hτ Xl Yl).eq
  have a1 : Rder θ V τ' Y φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ' Yl) ψ).1 := rder_eq_opInf_atPlace R τ' Yl ψ
  have a2 : Rder θ V τ X φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 := rder_eq_opInf_atPlace R τ Xl ψ
  rw [a1, a2, rder_eq_opInf_atPlace R τ Xl, rder_eq_opInf_atPlace R τ' Yl]
  exact congrArg Subtype.val (LinearMap.congr_fun hc ψ)

private theorem commutator_add_I_smul' {n : ℕ} (A B X : Matrix (Fin n) (Fin n) ℂ) :
    (A + Complex.I • B) * X - X * (A + Complex.I • B) = (A * X - X * A) + Complex.I • (B * X - X * B) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  abel

theorem RderC_Rder : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, (RderC θ V τ Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ Z φ) + RderC θ V τ (Z * X - X * Z) φ) ∧ (τ' ≠ τ → RderC θ V τ' Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ' Z φ)) := by
  intro D θ hθ V τ τ' Z X hX φ hφ
  constructor
  ·
    obtain ⟨hA, hB⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    have hZ := GlobalTheory.SmoothAutCheck.parts_sum V τ Z
    set A := (1 / 2 : ℂ) • (Z + conjAt V τ Z) with hAdef
    set B := (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) with hBdef
    have hc := commutator_add_I_smul' A B X
    rw [hZ] at hc
    have hAX := bracket_mem_lieAt hA hX
    have hBX := bracket_mem_lieAt hB hX
    have e1 : RderC θ V τ (Z * X - X * Z) φ =
        Rder θ V τ (A * X - X * A) φ + Complex.I • Rder θ V τ (B * X - X * B) φ := by
      rw [hc, GlobalTheory.Mem.RealTranslate.RderC_add hθ hφ, GlobalTheory.Mem.RealTranslate.RderC_smul hθ hφ,
        GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hAX, GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hBX]
    rw [e1]
    show Rder θ V τ A (Rder θ V τ X φ) + Complex.I • Rder θ V τ B (Rder θ V τ X φ) =
      Rder θ V τ X (Rder θ V τ A φ + Complex.I • Rder θ V τ B φ) + _
    rw [Rder_bracket hθ hφ hA hX, Rder_bracket hθ hφ hB hX,
      Rder_add (Rder_mem hφ hA) ((SmFun θ V).smul_mem _ (Rder_mem hφ hB)) hX, Rder_smul]
    rw [smul_add]
    abel
  ·
    intro hne
    obtain ⟨hA, hB⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ' Z
    show Rder θ V τ' ((1 / 2 : ℂ) • (Z + conjAt V τ' Z)) (Rder θ V τ X φ) +
        Complex.I • Rder θ V τ' ((1 / (2 * Complex.I)) • (Z - conjAt V τ' Z)) (Rder θ V τ X φ) =
      Rder θ V τ X (Rder θ V τ' ((1 / 2 : ℂ) • (Z + conjAt V τ' Z)) φ +
        Complex.I • Rder θ V τ' ((1 / (2 * Complex.I)) • (Z - conjAt V τ' Z)) φ)
    rw [Rder_add (Rder_mem hφ hA) ((SmFun θ V).smul_mem _ (Rder_mem hφ hB)) hX, Rder_smul,
      Rder_comm hθ hφ hne hA hX, Rder_comm hθ hφ hne hB hX]

end GlobalTheory.DerBracket

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceModPrimeOfPolarisationIdealTimesLattic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevkLoc

theorem smul_mem_of_isAA {D : D7} {k : ℕ} {Λ ΛT : Lt D.host.E k} (h : IsAA Λ ΛT) (c : D.host.E)
    (hc : ∀ x ∈ D.host.AA, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c * x) : ∀ x ∈ Λ, c • x ∈ ΛT := by
  intro x hx
  have hx' := (h x).1 hx
  clear hx
  induction hx' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hy
    obtain ⟨b, hb⟩ := hc a ha
    rw [smul_smul, ← hb]
    have : ((b : D.host.E)) • t = b • t := (algebraMap_smul D.host.E b t)
    rw [this]
    exact ΛT.smul_mem b ht
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact ΛT.add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact ΛT.neg_mem hx

theorem smul_mem_ideal_smul {D : D7} {k : ℕ} {Λ ΛT : Lt D.host.E k} (P : Ideal (𝓞 D.host.E)) (c : D.host.E)
    (h : ∀ x ∈ Λ, c • x ∈ ΛT) : ∀ x ∈ P • Λ, c • x ∈ P • ΛT := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun p hp y hy => ?_) (fun x y hx hy => ?_)
  · rw [smul_comm]
    exact Submodule.smul_mem_smul hp (h y hy)
  · rw [smul_add]; exact Submodule.add_mem _ hx hy

theorem congr_of_isAA : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (P : Ideal (𝓞 D.host.E)), P.IsPrime → IsAA Λ ΛT →
    ∀ m : Matrix (Fin k) (Fin k) (AfE D), (∀ u ∈ hatV Λ, m *ᵥ u - u ∈ hatV (P • Λ)) →
    ∃ b : 𝓞 D.host.E, b ∉ P ∧ ∀ u ∈ hatV ΛT,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (m *ᵥ u - u) ∈ hatV (P • ΛT) := by
  intro D k Λ ΛT P hP hAA m hm
  obtain ⟨n, a, c, ha, hc, hsum⟩ := _root_.GlobalTheory.HostAAPartition.host_AA_partition D
  choose b hb using fun i => hc i (a i) (ha i)
  have hb1 : ∑ i, b i = 1 := by
    have : ((∑ i, b i : 𝓞 D.host.E) : D.host.E) = ((1 : 𝓞 D.host.E) : D.host.E) := by
      push_cast
      rw [← hsum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; exact hb i
    exact RingOfIntegers.ext this
  obtain ⟨i, hi⟩ : ∃ i, b i ∉ P := by
    by_contra hcon
    push_neg at hcon
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one, ← hb1]
    exact Ideal.sum_mem _ fun i _ => hcon i
  refine ⟨b i, hi, fun u hu => ?_⟩
  have hA : ∀ t ∈ ΛT, a i • t ∈ Λ := fun t ht =>
    (hAA _).2 (AddSubgroup.subset_closure ⟨a i, ha i, t, ht, rfl⟩)
  have hC : ∀ x ∈ P • Λ, c i • x ∈ P • ΛT :=
    smul_mem_ideal_smul P (c i) (smul_mem_of_isAA hAA (c i) (hc i))
  have hu' := _root_.GlobalTheory.LevkSmul.smul_mem_hatV D ΛT Λ (a i) hA u hu
  have h1 := hm _ hu'
  have h2 := _root_.GlobalTheory.LevkSmul.smul_mem_hatV D (P • Λ) (P • ΛT) (c i) hC _ h1
  convert h2 using 1
  rw [Matrix.mulVec_smul, ← smul_sub, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hb i]

end GlobalTheory.LevkLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumFockVectorsIsVacuumOffLevel
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVacua

open GlobalTheory.IdemSupport

variable {D : D7}

theorem cP_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem delta_orth {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ)
    {P Q : HeightOneSpectrum (𝓞 D.host.E)} {a b : AE D} (ha : IsDelta Φ P a) (hb : IsDelta Φ Q b) (h : P ≠ Q) :
    a * b = 0 := by
  refine hΦ.ext' (by rw [RingHom.map_mul, ha.1, zero_mul, RingHom.map_zero]) fun Q' => ?_
  rw [ev_mul, ev_zero]
  by_cases hQ : Q' = P
  · rw [hb.2.2 Q' (hQ ▸ h), mul_zero]
  · rw [ha.2.2 Q' hQ, zero_mul]

theorem half_orth {m n : ℕ} {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) {u : Matrix (Fin m) (Fin n) (AE D)}
    (hu : IsHalf e u ∨ IsHalf (cA D e) u) :
    u.map (infPart D) = 0 ∧ ∀ (S : Finset (Pl D.host.E)) (e' : AE D), IsIdemSum e' S →
      (∀ PP ∈ S, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → ∀ i j, e' * u i j = 0 ∧ cA D e' * u i j = 0 := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := (of_isPrimeIdem hΦ h).1
  obtain ⟨Q, a, hQ, ha, hu⟩ : ∃ Q a, (Q = P ∨ Q = cP P) ∧ IsDelta Φ Q a ∧ ∀ i j, a * u i j = u i j := by
    rcases hu with hu | hu
    exacts [⟨P, e, Or.inl rfl, hd, hu⟩, ⟨cP P, cA D e, Or.inr rfl, delta_conj hΦ hd, hu⟩]
  refine ⟨Matrix.ext fun i j => ?_, ?_⟩
  · rw [Matrix.map_apply, ← hu, RingHom.map_mul, ha.1, zero_mul, Matrix.zero_apply]
  · rintro S e' ⟨⟨es, hes, rfl⟩, -⟩ hS i j
    have key : ∀ PP ∈ S, PP ≠ Q ∧ cP PP ≠ Q := fun PP hPP => by
      obtain ⟨h1, h2⟩ := hS PP hPP
      rw [isConjPl_iff] at h2
      rcases hQ with rfl | rfl
      · exact ⟨h1, Ne.symm h2⟩
      · exact ⟨fun e => h2 (by rw [e, cP_cP]), fun e => h1 (by rw [← cP_cP PP, e, cP_cP])⟩
    have k1 : (∑ PP ∈ S, es PP) * a = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun PP hPP => delta_orth hΦ (delta_of_isIdemAt hΦ (hes PP hPP)) ha (key PP hPP).1
    have k2 : cA D (∑ PP ∈ S, es PP) * a = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul]
      exact Finset.sum_eq_zero fun PP hPP =>
        delta_orth hΦ (delta_conj hΦ (delta_of_isIdemAt hΦ (hes PP hPP))) ha (key PP hPP).2
    rw [← hu, ← mul_assoc, ← mul_assoc, k1, k2, zero_mul]
    exact ⟨rfl, rfl⟩

theorem isVacAt_ptAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → ∀ φ, GlobalTheory.Hk3.IsVacAt R.ψ _ _ P (GlobalTheory.GalLift.ptAt R i σ B f φ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hθ i σ f₀ f B hV P hP φ
  obtain ⟨⟨-, hvac⟩, e, he, hth⟩ := hV.vec
  obtain ⟨c, hc⟩ := hL.βV i
  obtain ⟨c', hc'⟩ := hL.βW i
  rw [one_pow] at hc hc'
  have h0 : GlobalTheory.Hk3.IsVacAt R.ψ _ _ P f₀ :=
    _root_.GlobalTheory.VacLat.isVacAt_of_isLatVac R.ψ _ _ (R.βV i) (R.βW i) (R.ΛV i) (R.ΛW i) 1 1 hc hc' P
      (by rw [mul_one, Nat.cast_one]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)) f₀ hvac.theta hvac.lat
  refine ⟨hV.theta φ, fun e' f' h' u hu hh => ?_⟩
  obtain ⟨h1, h2⟩ := half_orth h' hh
  refine _root_.GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite R.ψ R.θ _ _ hθ _ _ _ _ f hV.theta u h1 ?_ φ
  refine _root_.GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ f₀ _ f hth u (fun a b => ?_) (h0.2 e' f' h' u hu hh)
  have := h2 _ e he (fun PP hPP => hP PP (Or.inl (by simpa using hPP))) a b
  rw [cA_cA]
  exact this.symm

end GlobalTheory.ConjVacua
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateMaximalCompactMemParahoricLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Matrix
namespace GlobalTheory.KapLevel

theorem cast_one_fin {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (k : I'.Gf) (hk : k ∈ I'.Kset) :
    ((Formalism.L2.SG.RowsJoinPinned.castGA e).symm (1, k)).1 = 1 ∧
      ((Formalism.L2.SG.RowsJoinPinned.castGA e).symm (1, k)).2 ∈ I.Kset := by
  subst e
  exact ⟨rfl, hk⟩

theorem lat_eq (D : D7) : Formalism.L2.SG.InstExistsPf.Lv D = Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 := by
  rw [Formalism.L2.SG.InstExistsPf.Lv_eq_map]
  rfl

theorem hatL_eq (D : D7) :
    (Formalism.IndefR.RationalEmbedding.inst D).Lf = Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  show Formalism.MainNotions.S.lamAf (F := D.host.F) (Formalism.L2.SG.InstExistsPf.Lv D) = _
  rw [Formalism.MainNotions.S.Inh.aut_lamAf_eq, lat_eq]
  rfl

theorem kset_stab {D : D7} (x : (Formalism.IndefR.RationalEmbedding.inst D).Gf) (hx : x ∈ (Formalism.IndefR.RationalEmbedding.inst D).Kset)
    (g : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (hg : g = x.1) :
    (∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      g.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) ∧
    ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      (g⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  subst hg
  have h0 : x.1 ∈ Formalism.UG.stabGL (Formalism.IndefR.RationalEmbedding.inst D).Lf := hx
  have h1 : x.1⁻¹ ∈ Formalism.UG.stabGL (Formalism.IndefR.RationalEmbedding.inst D).Lf := (Formalism.UG.stabGL (Formalism.IndefR.RationalEmbedding.inst D).Lf).inv_mem h0
  have e := SetLike.ext_iff.1 (hatL_eq D)
  refine ⟨fun y hy => (e _).1 ((h0 y).1 ((e y).2 hy)), fun y hy => (e _).1 ((h1 y).1 ((e y).2 hy))⟩

theorem st_of_stab {D : D7} (g ft β : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D))
    (hF : Formalism.L2.DIV.IsFrame (ft * β) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (h0 : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      g.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (h1 : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      (g⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) :
    ft⁻¹ * g * ft ∈ Formalism.L2.DIV.St β := by
  have hS : g ∈ Formalism.L2.DIV.St (ft * β) := (GlobalTheory.LevSplit.mem_St_iff (ft * β) _ hF g).2 ⟨h0, h1⟩
  obtain ⟨z, hz⟩ := hS
  refine ⟨z, ?_⟩
  rw [← hz]
  show β * Formalism.L2.DIV.intGL _ _ _ z * β⁻¹ = ft⁻¹ * ((ft * β) * Formalism.L2.DIV.intGL _ _ _ z * (ft * β)⁻¹) * ft
  group

theorem kap_mem_parLev : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, kap X h t k ∈ GfC (Yc D 0) ∧ finE (Yc D 0) (kap X h t k) ∈ Formalism.L2.DIV.parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ cG t _ _ _ ht _ hF k hk
  obtain ⟨hy1, hy2⟩ := cast_one_fin h.symm k hk
  have hkap : kap X h t k = (@id (GA D (D.sp.Y 0)) t)⁻¹ * (Formalism.IndefR.RationalEmbedding.iota D).symm
      ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)) * @id (GA D (D.sp.Y 0)) t := rfl
  refine ⟨?_, ?_⟩
  · rw [hkap]
    exact mul_mem (mul_mem (inv_mem ht) ((Formalism.L2.SG.EvalTIota.brg_mem_GfC_i _).2 hy1)) ht
  · have hU := GlobalTheory.LevSplit.finE_mem_UA (Yc D 0) (kap X h t k)
    have hfin0 : Formalism.IndefR.Lev.finE (D.sp.Y 0) (kap X h t k) = (Formalism.IndefR.Lev.finE (D.sp.Y 0) t)⁻¹ *
        @id (GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)).2.1 *
        Formalism.IndefR.Lev.finE (D.sp.Y 0) t := by
      rw [hkap, map_mul, map_mul, map_inv, Formalism.L2.SG.EvalTIota.finE_brg_i]
      rfl
    have hfin : Formalism.IndefR.Lev.finE (Yc D 0) (kap X h t k) = (Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹ *
        @id (GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)).2.1 *
        Formalism.IndefR.Lev.finE (Yc D 0) t := hfin0
    rw [hfin] at hU ⊢
    obtain ⟨s0, s1⟩ := kset_stab _ hy2 _ rfl
    have hr : ∀ a : Fin (Yc D 0).rank, (a : ℕ) < (R.dat0 R.triv).r := fun a =>
      lt_of_lt_of_eq a.2 (Formalism.L2.SG.InstExistsPf.rank_eq D)
    refine Formalism.L2.DIV.mem_parLev.2 ⟨hU, st_of_stab _ _ _ hF s0 s1, fun PP _ => ?_, fun PP hP => ?_⟩
    · rw [Formalism.L2.DIV.mem_blockTri]
      intro i j hij
      exfalso
      unfold Formalism.L2.DIV.blkOf at hij
      rw [if_pos (hr i), if_pos (hr j)] at hij
      exact lt_irrefl 0 hij
    · exact absurd hP (Finset.notMem_empty PP)

end GlobalTheory.KapLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalUnitaryAntidiagonalFormExponentBalance
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem diag_unitary_exp_sym {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ)
    (hU : IsUnramInv ϖ c q) (r : ℕ) (d : Fin r → ℤ) (t : GU c r)
    (ht : t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i)) :
    ∑ i, max (-d i) 0 = ∑ i, max (d i) 0 := by
  obtain ⟨_, _, hcϖ, hv, _⟩ := hU
  have hmem := t.2
  change Formalism.UG.cT c (t.1.1) * Formalism.UG.antiJ L r * t.1.1 = Formalism.UG.antiJ L r at hmem
  rw [ht] at hmem
  have hcT : Formalism.UG.cT c (Matrix.diagonal (fun i => ϖ ^ d i)) = Matrix.diagonal (fun i => ϖ ^ d i) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp [map_zpow₀, hcϖ]
    · simp [h, Ne.symm h]
  rw [hcT] at hmem
  have hϖ : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.zero_ne_coe hv
  have key : ∀ i : Fin r, d (Fin.rev i) = -d i := by
    intro i
    have e := congrArg (fun M => M i (Fin.rev i)) hmem
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    have hJ : Formalism.UG.antiJ L r i (Fin.rev i) = 1 := by
      simp only [Formalism.UG.antiJ, Fin.val_rev]; rw [if_pos]; omega
    rw [hJ, mul_one] at e
    rw [← zpow_add₀ hϖ] at e
    have e2 := congrArg (fun x => Valued.v x) e
    simp only [map_zpow₀, map_one, hv] at e2
    rw [← WithZero.coe_zpow, ← ofAdd_zsmul] at e2
    have e3 : (d i + d (Fin.rev i)) • (-1 : ℤ) = 0 := by
      have := WithZero.coe_injective e2
      exact Multiplicative.ofAdd.injective (this.trans ofAdd_zero.symm)
    simp at e3
    omega
  calc ∑ i, max (-d i) 0 = ∑ i, max (d (Fin.rev i)) 0 := by simp [key]
    _ = ∑ i, max (d i) 0 := Equiv.sum_comp Fin.revPerm (fun i => max (d i) 0)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdjoinRootLinearEquivOfCharpolyEqStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjoinRoot_linearEquiv_of_charpoly_eq : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (P : PPol σ n) (A : Matrix (Fin n) (Fin n) E), A.charpoly = P.1 → ∃ φ : Fld P ≃ₗ[E] (Fin n → E), ∀ y, A *ᵥ φ y = φ (alpha P * y) := by
  first | exact @GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly | exact GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly | (intros; apply GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterSphericalUnramifiedUnitary
section
noncomputable section

namespace GlobalTheory.LFun.ExSatU

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem exists_hasSatU : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : w.adicCompletion E) (σ : w.adicCompletion E →+* w.adicCompletion E) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    ρ.IsIrreducible → IsAdmissible ρ → GlobalTheory.LGrp.IsSpherical ρ (KU σ n) → ∃ α, HasSatU ϖ q ρ α := by
  intro E _ _ w ϖ σ q n hU V _ _ ρ hi ha hs
  obtain ⟨ho, hc⟩ := _root_.GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU (w.adicCompletion E) ϖ σ q n hU
  exact GlobalTheory.LFun.SatCompare.exists_hasSatU hU ⟨ha.1, hi⟩ (ha.2 _ ho hc) hs

end GlobalTheory.LFun.ExSatU

end
end

