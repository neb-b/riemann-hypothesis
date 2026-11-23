module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInner
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0936
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0938
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0924
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0661
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0826
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicRealNonzero
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section

namespace GlobalTheory.LiftRefIrr

theorem exists_ne_of_mem_iSup' {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Sort*} (p : ι → Submodule ℂ M)
    (ℓ : M →+ ℂ) {x : M} (hx : x ∈ ⨆ i, p i) (h : ℓ x ≠ 0) : ∃ i, ∃ y ∈ p i, ℓ y ≠ 0 := by
  by_contra H
  push_neg at H
  exact h (Submodule.iSup_induction p (motive := fun z => ℓ z = 0) hx (fun i y hy => H i y hy) (map_zero ℓ)
    (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero]))

theorem exists_irr_pair {D : D7} {μ : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μ j) (x : D.what₂.Mt μ j) (hx : x ≠ 0) :
    ∃ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)) (_ : NG.IsIrrRep Mr.wt.ρ S),
      ∃ F ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, inner ℂ F x ≠ 0 := by
  obtain ⟨-, ι, -, S, hirr, -, -, -, -, hsum⟩ := _root_.GlobalTheory.CompRed.typeSp_decomp D.host.E D.R.nV Mr.wt Mr.J Mr.χ Mr.J_open
  let p : ι → Submodule ℂ (D.what₂.Mt μ j) :=
    fun i => (NG.isoTyp Mr.wt.ρ (S i) ⊓ NG.TypeSp Mr.wt.ρ Mr.J Mr.χ).comap Mr.real
  have htop : (⨆ i, p i) = ⊤ := by
    apply Submodule.map_injective_of_injective Mr.real_inj
    rw [Submodule.map_iSup, Submodule.map_top, Mr.real_range]
    conv_rhs => rw [← hsum]
    refine iSup_congr fun i => ?_
    show Submodule.map Mr.real (Submodule.comap Mr.real _) = _
    rw [Submodule.map_comap_eq, Mr.real_range]
    exact inf_eq_right.2 inf_le_right
  have hxm : x ∈ ⨆ i, p i := htop ▸ Submodule.mem_top
  let ℓ : D.what₂.Mt μ j →+ ℂ := AddMonoidHom.mk' (fun F => inner ℂ F x) (fun a b => inner_add_left a b x)
  obtain ⟨i, F, hF, hne⟩ := exists_ne_of_mem_iSup' p ℓ hxm (by
    show inner ℂ x x ≠ 0
    exact inner_self_ne_zero.2 hx)
  exact ⟨S i, hirr i, F, (Submodule.mem_inf.1 hF).1, hne⟩

end GlobalTheory.LiftRefIrr


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralNeTopOfBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.EisAbsPf

abbrev LA : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∃ (M : ℕ) (C : ℝ), ∀ g₁ g₂ : GA D W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ≤ ENNReal.ofReal (C * ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g₁ : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g₂ : ℝ)) ^ M)

abbrev LB : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (F₁ F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₂ → ∀ γ₁ ∈ GQ W, ∀ γ₂ ∈ GQ W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁) F₁) (om (1, γ₂) F₂)‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) F₁ F₂‖ₑ

theorem lintegral_ne_top_of_bounds {X : Type*} [MeasurableSpace X] [Mul X] (ν : Measure X) (𝓖 : Set X)
    (hfin : ν 𝓖 < ⊤) (Γ : Set X) (h q : X → ℝ) (hq : ∀ g, 0 ≤ q g)
    (htr : ∀ g, ∃ γ ∈ Γ, h (γ * g) ≤ 2 * q g) (hh : ∀ g, 0 ≤ h g)
    (S : X → X → ENNReal) (hinv : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, ∀ g₁ g₂, S (γ₁ * g₁) (γ₂ * g₂) = S g₁ g₂)
    (M : ℕ) (C : ℝ) (hC : ∀ g₁ g₂, S g₁ g₂ ≤ ENNReal.ofReal (C * (h g₁ * h g₂) ^ M))
    (a b : X → ℂ) (C₁ C₂ : ℝ) (hC₁ : ∀ g, ‖a g‖ * q g ^ M ≤ C₁) (hC₂ : ∀ g, ‖b g‖ * q g ^ M ≤ C₂) :
    ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤ := by
  have hpt : ∀ g₁ g₂, S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ≤ ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) := by
    intro g₁ g₂
    obtain ⟨γ₁, hγ₁, e1⟩ := htr g₁
    obtain ⟨γ₂, hγ₂, e2⟩ := htr g₂
    have hq₁ := hq g₁
    have hq₂ := hq g₂
    have hS1 : S g₁ g₂ ≤ ENNReal.ofReal (|C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M)) := by
      rw [← hinv γ₁ hγ₁ γ₂ hγ₂ g₁ g₂]
      refine (hC _ _).trans (ENNReal.ofReal_le_ofReal ?_)
      have hh' : h (γ₁ * g₁) * h (γ₂ * g₂) ≤ (2 * q g₁) * (2 * q g₂) :=
        mul_le_mul e1 e2 (hh _) (by linarith)
      calc C * (h (γ₁ * g₁) * h (γ₂ * g₂)) ^ M
          ≤ |C| * ((2 * q g₁) * (2 * q g₂)) ^ M :=
            mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_nonneg (hh _) (hh _)) hh' M) (pow_nonneg (mul_nonneg (hh _) (hh _)) M)
              (abs_nonneg _)
        _ = |C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M) := by
            rw [show (2 * q g₁) * (2 * q g₂) = 4 * (q g₁ * q g₂) by ring, mul_pow, mul_pow]; ring
    have hn1 : ‖a g₁‖ₑ = ENNReal.ofReal ‖a g₁‖ := (ofReal_norm_eq_enorm _).symm
    have hn2 : ‖b g₂‖ₑ = ENNReal.ofReal ‖b g₂‖ := (ofReal_norm_eq_enorm _).symm
    have a1 := hC₁ g₁
    have a2 := hC₂ g₂
    have p1 : 0 ≤ ‖a g₁‖ * q g₁ ^ M := mul_nonneg (norm_nonneg _) (pow_nonneg hq₁ M)
    have p2 : 0 ≤ ‖b g₂‖ * q g₂ ^ M := mul_nonneg (norm_nonneg _) (pow_nonneg hq₂ M)
    have c0 : 0 ≤ |C| * 4 ^ M := by positivity
    calc S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ
        ≤ ENNReal.ofReal (|C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M)) * ENNReal.ofReal ‖a g₁‖ * ENNReal.ofReal ‖b g₂‖ := by
          rw [hn1, hn2]; gcongr
      _ = ENNReal.ofReal (|C| * 4 ^ M * (‖a g₁‖ * q g₁ ^ M) * (‖b g₂‖ * q g₂ ^ M)) := by
          have c1 : 0 ≤ |C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M) := mul_nonneg c0 (mul_nonneg (pow_nonneg hq₁ M) (pow_nonneg hq₂ M))
          rw [← ENNReal.ofReal_mul c1, ← ENNReal.ofReal_mul (mul_nonneg c1 (norm_nonneg _))]
          congr 1; ring
      _ ≤ ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc |C| * 4 ^ M * (‖a g₁‖ * q g₁ ^ M) * (‖b g₂‖ * q g₂ ^ M)
              ≤ |C| * 4 ^ M * C₁ * (‖b g₂‖ * q g₂ ^ M) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a1 c0) p2
            _ ≤ |C| * 4 ^ M * C₁ * C₂ :=
                mul_le_mul_of_nonneg_left a2 (mul_nonneg c0 (p1.trans a1))
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) * ν 𝓖 * ν 𝓖) ?_ ?_
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hfin.ne
  · calc ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν
        ≤ ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) ∂ν ∂ν :=
          lintegral_mono fun g₁ => lintegral_mono fun g₂ => hpt g₁ g₂
      _ = ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) * ν 𝓖 * ν 𝓖 := by
          rw [setLIntegral_const, setLIntegral_const]

theorem eisAbs_of_bounds (hP : GlobalTheory.Published.CuspRapidDecay) (hV : GlobalTheory.Mem.Vol.FiniteVolume₂) (hA : LA) (hB : LB) :
    ∀ D : D7, EisAbs D := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ h1 h2 φ₁ φ₂ hA1 hC1 hA2 hC2
  obtain ⟨M, C, hC⟩ := hA D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ h1 h2
  have e : ∀ γ g : GA D W, om (1, γ * g) = om (1, γ) * om (1, g) := by
    intro γ g; rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have hinv : ∀ γ₁ ∈ (GQ W : Set (GA D W)), ∀ γ₂ ∈ (GQ W : Set (GA D W)), ∀ g₁ g₂ : GA D W,
      (∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁ * g₁) f₁) (om (1, γ₂ * g₂) f₂)‖ₑ) =
        ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ := by
    intro γ₁ hγ₁ γ₂ hγ₂ g₁ g₂
    rw [e γ₁ g₁, e γ₂ g₂, Module.End.mul_apply, Module.End.mul_apply]
    exact hB D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ _ (hS.weil.om_pres _ _ h1) (hS.weil.om_pres _ _ h2)
      γ₁ hγ₁ γ₂ hγ₂
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hA1 hC1 M
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hA2 hC2 M
  have hfin : νW 𝓖 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top hV W νW 𝓖 hS.haarW hS.fdW
  have key := lintegral_ne_top_of_bounds νW 𝓖 hfin (GQ W : Set (GA D W))
    (fun g => (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g : ℝ)) (fun g => (GlobalTheory.CuspDecay.quotHeight θ W g : ℝ))
    (fun g => NNReal.coe_nonneg _)
    (fun g => by
      obtain ⟨γ, hγ, hle⟩ := GlobalTheory.CuspDecay.exists_height_le (θ := θ) g
      exact ⟨γ, hγ, by exact_mod_cast hle⟩)
    (fun g => NNReal.coe_nonneg _)
    (fun g₁ g₂ => ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ) hinv M C hC φ₁ φ₂ C₁ C₂ hC₁ hC₂
  refine ne_top_of_le_ne_top key (le_of_eq ?_)
  refine lintegral_congr fun g₁ => lintegral_congr fun g₂ => ?_
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]

theorem eisAbs : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, EisAbs D :=
  fun hP => eisAbs_of_bounds hP GlobalTheory.Mem.VolFin.finVol _root_.GlobalTheory.SWAbsGrowth.tsum_lagTerm_le _root_.GlobalTheory.SWAbsInv.tsum_enorm_lagTerm_rat

end GlobalTheory.EisAbsPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNormSqLtAbsNormUnitaryCusp
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSStrict

theorem qpow (q : ℕ) (x : ℝ) : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
  simp

theorem pair_val (q : ℕ) (γ : ℂˣ) (x : ℝ) :
    (γ : ℂ) * ((Units.map (starRingEnd ℂ).toMonoidHom γ : ℂˣ) : ℂ) * (q : ℂ) ^ (-(x : ℂ)) =
      ((‖(γ : ℂ)‖ ^ 2 * (q : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [qpow]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem norm_conjU (γ : ℂˣ) : ‖((Units.map (starRingEnd ℂ).toMonoidHom γ : ℂˣ) : ℂ)‖ = ‖(γ : ℂ)‖ := by
  simp

theorem hasProd_split {ι : Type*} [DecidableEq ι] (f : ι → ℂ) (T : Finset ι) (w : ι) (hw : w ∉ T) {A B : ℂ}
    (h1 : HasProd (fun v : {v : ι // v ∉ T} => f v.1) A)
    (h2 : HasProd (fun v : {v : ι // v ∉ insert w T} => f v.1) B) : A = f w * B := by
  have h1' : HasProd ({v | v ∉ T}.mulIndicator f) A :=
    (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ T})).mp h1
  have h2' : HasProd ({v | v ∉ insert w T}.mulIndicator f) B :=
    (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ insert w T})).mp h2
  have h3 : HasProd (({w} : Set ι).mulIndicator f) (f w) := by
    have := hasProd_single (f := ({w} : Set ι).mulIndicator f) w (fun b hb => by simp [Set.mulIndicator_apply, hb])
    simpa using this
  have h4 := h3.mul h2'
  have heq : (fun v => ({w} : Set ι).mulIndicator f v * {v | v ∉ insert w T}.mulIndicator f v) =
      {v | v ∉ T}.mulIndicator f := by
    funext v
    by_cases hv : v = w
    · subst hv; simp [Set.mulIndicator_apply, hw]
    · by_cases hvT : v ∈ T <;> simp [Set.mulIndicator_apply, hv, hvT]
  rw [heq] at h4
  exact h1'.unique h4

theorem half_pow_le_norm_prod {α : Type*} (g : α → ℂ) (m : Multiset α) (h : ∀ p ∈ m, (1/2 : ℝ) ≤ ‖g p‖) :
    (1/2 : ℝ) ^ Multiset.card m ≤ ‖(m.map g).prod‖ := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
    have ha := h a (Multiset.mem_cons_self a s)
    have hs := ih (fun p hp => h p (Multiset.mem_cons_of_mem hp))
    calc (1/2 : ℝ) ^ Multiset.card s * (1/2) = (1/2) * (1/2) ^ Multiset.card s := mul_comm _ _
      _ ≤ _ := mul_le_mul ha hs (by positivity) (norm_nonneg _)

theorem half_le_norm_inv_one_sub {z : ℂ} (hz : ‖z‖ < 1) : (1/2 : ℝ) ≤ ‖(1 - z)⁻¹‖ := by
  have hpos : 0 < ‖1 - z‖ := by
    have := norm_sub_norm_le (1 : ℂ) z
    simp at this; linarith
  have hle : ‖1 - z‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) z
    simp at this; linarith
  rw [norm_inv, one_div]
  exact inv_anti₀ hpos hle

def gfac (q : ℕ) (x : ℝ) (p : ℂˣ × ℂˣ) : ℂ := (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(x : ℂ)))⁻¹

theorem locL_eq (q : ℕ) (B B' : Multiset ℂˣ) (x : ℝ) : locL q B B' (x : ℂ) = ((B ×ˢ B').map (gfac q x)).prod := rfl

theorem norm_sq_lt_absNorm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ : CG E a), 1 ≤ a →
    σ.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → ∀ w ∉ T, ∀ α ∈ sat σ w,
      ‖(α : ℂ)‖ ^ 2 < (Ideal.absNorm w.asIdeal : ℝ) := by
  intro E _ _ _ a σ ha hσ T hT w hw α hα
  classical
  obtain ⟨L1, hL1, -, c1, hc1, hlim1⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ T hT
  have hT' : UnrOutside (insert w T) σ := fun v hv => hT v (fun h => hv (Finset.mem_insert_of_mem h))
  obtain ⟨L2, hL2, -, c2, hc2, hlim2⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ (insert w T) hT'
  have hsplit : ∀ x : ℝ, 1 < x → (L1 x : ℂ) = ((sat σ w ×ˢ (sat σ w).map (Units.map (starRingEnd ℂ).toMonoidHom)).map
      (gfac (Ideal.absNorm w.asIdeal) x)).prod * (L2 x : ℂ) := by
    intro x hx
    rw [← locL_eq]
    have e := hasProd_split (ι := HeightOneSpectrum (𝓞 E)) (fun v : HeightOneSpectrum (𝓞 E) => locL (Ideal.absNorm v.asIdeal)
      (sat σ v) ((sat σ v).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) T w hw (hL1 x hx).1 (hL2 x hx).1
    exact e
  generalize hB' : (sat σ w).map (Units.map (starRingEnd ℂ).toMonoidHom) = B' at hsplit
  have hmem : ∀ γ ∈ sat σ w, (γ, Units.map (starRingEnd ℂ).toMonoidHom γ) ∈ (sat σ w) ×ˢ B' := fun γ hγ =>
    Multiset.mem_product.mpr ⟨hγ, hB' ▸ Multiset.mem_map_of_mem _ hγ⟩
  generalize hqd : Ideal.absNorm w.asIdeal = q at hsplit ⊢
  have hq1 : (1 : ℝ) < q := by rw [← hqd]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hq0 : (0 : ℝ) < q := by linarith

  have hle : ∀ γ ∈ sat σ w, ‖(γ : ℂ)‖ ^ 2 ≤ (q : ℝ) := by
    intro γ hγ
    by_contra hlt
    push_neg at hlt
    have hγ0 : (0 : ℝ) < ‖(γ : ℂ)‖ ^ 2 := by
      have : (γ : ℂ) ≠ 0 := γ.ne_zero
      positivity
    have hlogq : 0 < Real.log q := Real.log_pos hq1
    set x0 := Real.log (‖(γ : ℂ)‖ ^ 2) / Real.log q with hx0def
    have hx0 : 1 < x0 := by
      rw [hx0def, lt_div_iff₀ hlogq, one_mul]
      exact Real.log_lt_log hq0 hlt
    have hpow : (q : ℝ) ^ (-x0) = (‖(γ : ℂ)‖ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hq0.le, Real.rpow_def_of_pos hq0]
      congr 1
      have : Real.log q * x0 = Real.log (‖(γ : ℂ)‖ ^ 2) := by
        rw [hx0def]; field_simp
      rw [this, Real.exp_log hγ0]
    have hF0 : ((sat σ w ×ˢ B').map (gfac q x0)).prod = 0 := by
      apply Multiset.prod_eq_zero
      refine Multiset.mem_map.mpr ⟨(γ, Units.map (starRingEnd ℂ).toMonoidHom γ), hmem γ hγ, ?_⟩
      simp only [gfac]
      rw [pair_val, hpow, mul_inv_cancel₀ hγ0.ne']
      simp
    have h := hsplit x0 hx0
    rw [hF0, zero_mul] at h
    have h1 := (hL1 x0 hx0).2
    have : L1 x0 = 0 := by exact_mod_cast h
    linarith
  by_contra hnot
  push_neg at hnot
  have heq : ‖(α : ℂ)‖ ^ 2 = q := le_antisymm (hle α hα) hnot
  set t : ℝ → ℝ := fun x => (q : ℝ) * (q : ℝ) ^ (-x) with ht
  have ht1 : ∀ x, 1 < x → t x < 1 := by
    intro x hx
    have : (q : ℝ) ^ (1 + -x) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    rwa [Real.rpow_add hq0, Real.rpow_one] at this
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem (hmem α hα)

  have hlow : ∀ x, 1 < x → (1/2 : ℝ) ^ Multiset.card rest ≤
      (1 - t x) * ‖((sat σ w ×ˢ B').map (gfac q x)).prod‖ := by
    intro x hx
    have hspec : gfac q x (α, Units.map (starRingEnd ℂ).toMonoidHom α) = (((1 - t x : ℝ) : ℂ))⁻¹ := by
      simp only [gfac]
      rw [pair_val, heq]
      simp only [ht]
      push_cast
      ring
    have hrestb : ∀ p ∈ rest, (1/2 : ℝ) ≤ ‖gfac q x p‖ := by
      intro p hp
      have hp' : p ∈ (sat σ w) ×ˢ B' := by
        rw [hrest]; exact Multiset.mem_cons_of_mem hp
      obtain ⟨hp1, hp2⟩ := Multiset.mem_product.mp hp'
      rw [← hB'] at hp2
      obtain ⟨β, hβ, hβe⟩ := Multiset.mem_map.mp hp2
      have hb1 := hle p.1 hp1
      have hb2 := hle β hβ
      have hn2 : ‖(p.2 : ℂ)‖ = ‖(β : ℂ)‖ := by rw [← hβe]; exact norm_conjU β
      have hprod : ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ ≤ q := by
        rw [hn2]
        nlinarith [sq_nonneg (‖(p.1 : ℂ)‖ - ‖(β : ℂ)‖), norm_nonneg (p.1 : ℂ), norm_nonneg (β : ℂ)]
      apply half_le_norm_inv_one_sub
      rw [qpow, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
      calc ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ * (q : ℝ) ^ (-x) ≤ q * (q : ℝ) ^ (-x) :=
            mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hq0.le _)
        _ < 1 := ht1 x hx
    have hpos : 0 < 1 - t x := by linarith [ht1 x hx]
    rw [hrest, Multiset.map_cons, Multiset.prod_cons, norm_mul, hspec, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    exact half_pow_le_norm_prod (gfac q x) rest hrestb

  have hnorm : ∀ x, 1 < x → ‖((sat σ w ×ˢ B').map (gfac q x)).prod‖ = ((x - 1) * L1 x) / ((x - 1) * L2 x) := by
    intro x hx
    have h := hsplit x hx
    have hL2pos : 0 < L2 x := by linarith [(hL2 x hx).2]
    have hL1pos : 0 < L1 x := by linarith [(hL1 x hx).2]
    have hFx : ((sat σ w ×ˢ B').map (gfac q x)).prod = ((L1 x / L2 x : ℝ) : ℂ) := by
      push_cast
      rw [h, mul_div_assoc, div_self (by exact_mod_cast hL2pos.ne'), mul_one]
    rw [hFx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hL1pos hL2pos),
      mul_div_mul_left _ _ (by linarith : (x - 1) ≠ 0)]
  have htlim : Tendsto t (𝓝[>] 1) (𝓝 1) := by
    have hc : Continuous t := continuous_const.mul (continuous_const.rpow continuous_neg (fun _ => Or.inl hq0.ne'))
    have := hc.tendsto 1
    simp only [ht, Real.rpow_neg_one, mul_inv_cancel₀ hq0.ne'] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hlim : Tendsto (fun x => (1 - t x) * (((x - 1) * L1 x) / ((x - 1) * L2 x))) (𝓝[>] 1) (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub htlim).mul (hlim1.div hlim2 hc2.ne')
    simpa using this
  have hev1 : ∀ᶠ x in 𝓝[>] (1 : ℝ), (1 - t x) * (((x - 1) * L1 x) / ((x - 1) * L2 x)) <
      (1/2 : ℝ) ^ Multiset.card rest := hlim (gt_mem_nhds (by positivity))
  have hev2 : ∀ᶠ x in 𝓝[>] (1 : ℝ), 1 < x := self_mem_nhdsWithin
  obtain ⟨x, hx1, hx2⟩ := (hev1.and hev2).exists
  have := hlow x hx2
  rw [hnorm x hx2] at this
  linarith

end GlobalTheory.RSStrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivAtOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.LocalFactor

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem pureTensor_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : R.ptP i t 1 = R.vP i t := by
  unfold RealDat.ptP pureTensorO pureTensorL
  have : (1 : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp
  rw [this, Module.Basis.constr_basis]
  simp [opPow]

theorem trivAt_one (V : HSp D) (f : AE D) : TrivAt V f 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := rfl
  intro a b
  simp [this]

theorem finMult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Laws R F → R.FullP → ∀ i t, FinMult R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ v f hf γ hγ hγt k hk
  have hmul : ∀ g : GA D (Wc D i),
      R.ωP i t (1, g * k) (R.vP i t) = R.ωP i t (1, g) (R.ωP i t (1, k) (R.vP i t)) := by
    intro g
    have e : ((1 : GA D (Vc D i)), g * k) = (1, g) * (1, k) := by simp
    rw [e, map_mul, Module.End.mul_apply]
  have hone : R.ωP i t (1, 1) = 1 := map_one _
  unfold coef
  by_cases hbad : ∃ P, (P ∈ R.Pg ∨ P ∈ R.Q t) ∧ ∃ e, IsPrimeIdem P e f
  · obtain ⟨P, hP, e, he⟩ := hbad
    by_cases hkl : k ∈ levW R i
    · have hfix : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
        have := _root_.GlobalTheory.RawLift.LevelFix.levFix D G Pl0 T A Ks R F hL hF i t k hkl 1
        rwa [pureTensor_one] at this
      rw [hmul γ, hfix]
      by_cases hN : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
      · simp [hN]
      · rw [div_self hN, mul_one]
    · have h0 := _root_.GlobalTheory.BadPlace.coef_bad_vanish D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ P hP e f he γ hγ hγt k hk hkl
      have h1 := _root_.GlobalTheory.BadPlace.coef_bad_vanish D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ P hP e f he 1 (one_mem _) (trivAt_one _ f) k hk hkl
      rw [one_mul] at h1
      rw [h0, h1]
      simp
  · have hgood : ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f :=
      fun P hP e f' he hff => hbad ⟨P, hP, e, hff ▸ he⟩
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.RawLift.GoodFactor.finmult_good D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ v f hf hgood k hk
    have h1 := hc 1 (one_mem _) (trivAt_one _ f)
    rw [one_mul, hone, Module.End.one_apply] at h1
    rw [hc γ hγ hγt, h1]
    by_cases hN : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
    · simp [hN]
    · field_simp

end GlobalTheory.RawLift.LocalFactor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulPartialRankinSelbergLStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ Filter Topology Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedThetaIntegral_eq_mul_partialRankinSelbergL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) → (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ (N : ℕ) (Φ : (Fin a → Cinf E) → ℂ) (π π' : CuspSub E a) (φ φ' : GA E a → ℂ), CG.mk π = σ ∧ CG.mk π' = σ' ∧ φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ (∀ ℓ : Fin a, (ℓ : ℕ) + 1 = a → tsupport Φ ⊆ {u | ∀ w, u ℓ w ≠ 0}) ∧ ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ φ Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ' φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ' w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  first
  | exact @GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth
  | exact GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth
  | (intros; apply GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth <;> assumption)
end

