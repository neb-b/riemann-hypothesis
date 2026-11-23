module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqVolumeSumCharacterTwistedCosets
section
open MeasureTheory

namespace GlobalTheory.TwistedCosetSum

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem coset_integral [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableAdd X] (μ : Measure X)
    [μ.IsAddLeftInvariant] (U : AddSubgroup X) (hU : IsOpen (U : Set X)) (g : X → ℂ)
    (hg : ∀ y, ∀ u ∈ U, ∀ u' ∈ U, g (y + u + u') * g y = g (y + u) * g (y + u')) (c : X) :
    ∫ y, ((fun x => -c + x) ⁻¹' (U : Set X)).indicator g y ∂μ = 0 ∨
    ∫ y, ((fun x => -c + x) ⁻¹' (U : Set X)).indicator g y ∂μ = g c * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  classical
  set S : Set X := (fun x => -c + x) ⁻¹' (U : Set X) with hS
  have hmem : ∀ y, y ∈ S ↔ -c + y ∈ U := fun y => Iff.rfl
  have hmeas : MeasurableSet S := (hU.preimage (continuous_const.add continuous_id)).measurableSet
  have hvol : μ S = μ U := measure_preimage_add μ _ _
  by_cases h : ∀ u ∈ U, g (c + u) = g c
  · right
    have : S.indicator g = S.indicator (fun _ => g c) := by
      refine Set.indicator_congr fun y hy => ?_
      have := h _ ((hmem y).1 hy)
      rwa [add_neg_cancel_left] at this
    rw [this, integral_indicator_const _ hmeas]
    simp only [Measure.real, hvol, Complex.real_smul]
    ring
  · left
    push_neg at h
    obtain ⟨u, hu, hne⟩ := h
    have hc0 : g c ≠ 0 := by
      intro h0
      have := hg c u hu u hu
      rw [h0, mul_zero] at this
      exact hne (by rw [h0]; exact mul_self_eq_zero.1 this.symm)
    have hshift : ∀ y, S.indicator g (u + y) * g c = g (c + u) * S.indicator g y := by
      intro y
      have hiff : u + y ∈ S ↔ y ∈ S := by
        rw [hmem, hmem, add_left_comm]
        exact U.add_mem_cancel_left hu
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hiff.2 hy)]
        have := hg c u hu _ ((hmem y).1 hy)
        rw [add_neg_cancel_left, show c + u + (-c + y) = u + y by abel] at this
        exact this
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hiff.1 h)), zero_mul, mul_zero]
    have h1 : (∫ y, S.indicator g y ∂μ) * g c = g (c + u) * ∫ y, S.indicator g y ∂μ := by
      conv_lhs => rw [← integral_add_left_eq_self (μ := μ) (S.indicator g) u]
      rw [← integral_mul_const, ← integral_const_mul]
      simp only [hshift]
    have h2 : (g (c + u) - g c) * ∫ y, S.indicator g y ∂μ = 0 := by
      rw [sub_mul, ← h1]; ring
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)

theorem integral_eq_sum_twisted : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant] (U : AddSubgroup X), IsOpen (U : Set X) → μ (U : Set X) ≠ ⊤ →
    ∀ g : X → ℂ, HasCompactSupport g → (∀ y, ∀ u ∈ U, ∀ u' ∈ U, g (y + u + u') * g y = g (y + u) * g (y + u')) →
    ∃ s : Finset X, ∫ y, g y ∂μ = (∑ γ ∈ s, g γ) * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  intro X _ _ _ _ _ _ μ _ U hU _ g hc hg
  classical
  by_cases hint : Integrable g μ
  swap
  · exact ⟨∅, by rw [integral_undef hint]; simp⟩
  haveI := GlobalTheory.LCIntegralField.discrete_quot U hU
  have hfin : ((QuotientAddGroup.mk : X → X ⧸ U) '' tsupport g).Finite :=
    (hc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T := hfin.toFinset with hT
  have hind : ∀ (c : X ⧸ U) y, (-(Quotient.out c) + y ∈ U ↔ c = (y : X ⧸ U)) := by
    intro c y
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  have hdec : g = fun y => ∑ c ∈ T,
      ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator g y := by
    funext y
    have key : ∀ c : X ⧸ U, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator
        g y = if c = (y : X ⧸ U) then g y else 0 := by
      intro c
      by_cases h : c = (y : X ⧸ U)
      · rw [if_pos h, Set.indicator_of_mem (show y ∈ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from (hind c y).2 h)]
      · rw [if_neg h, Set.indicator_of_notMem (show y ∉ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from fun hm => h ((hind c y).1 hm))]
    simp only [key]
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · rw [hT, Set.Finite.mem_toFinset] at hmem
      exact image_eq_zero_of_notMem_tsupport (fun hs => hmem ⟨y, hs, rfl⟩)
  have hmeas : ∀ c : X ⧸ U, MeasurableSet ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) := fun c =>
    (hU.preimage (continuous_const.add continuous_id)).measurableSet
  have hsum : ∫ y, g y ∂μ = ∑ c ∈ T, ∫ y, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator g y ∂μ := by
    rw [← integral_finsetSum _ fun c _ => hint.indicator (hmeas c)]
    exact congrArg _ hdec
  refine ⟨(T.filter fun c => ∫ y, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator g y ∂μ ≠ 0).image
    Quotient.out, ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h), hsum, ← Finset.sum_filter_ne_zero,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  exact (coset_integral μ U hU g hg (Quotient.out c)).resolve_left (Finset.mem_filter.1 hc).2

end GlobalTheory.TwistedCosetSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralInjectiveSubspaceCompactOpenConstNeZero
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.integral_indicator_preimage_injective_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ],
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
    ∫ y, U.indicator (fun _ => c) (j y) ∂ν ≠ 0 := by
  intro F _ _ v κ _ N ν hν j hj c hc U hUo hUc h0
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hgc : Continuous g := IsModuleTopology.continuous_of_linearMap g
  set S : Set (Fin N → Fv F v) := j ⁻¹' U with hSdef
  have hSo : IsOpen S := hUo.preimage hjc
  have hSsub : S ⊆ g '' U := by
    intro y hy
    refine ⟨j y, hy, ?_⟩
    have := congrArg (fun f => f y) hg
    simpa using this
  have hfin : ν S < ⊤ := lt_of_le_of_lt (measure_mono hSsub) ((hUc.image hgc).measure_lt_top)
  have hpos : 0 < ν S := hSo.measure_pos ν ⟨0, by simp [hSdef, h0]⟩
  have heq : (fun y => U.indicator (fun _ => c) (j y)) = S.indicator (fun _ => c) := by
    funext y
    by_cases hy : j y ∈ U
    · have : y ∈ S := hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : y ∉ S := hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [heq, integral_indicator_const c hSo.measurableSet]
  refine smul_ne_zero ?_ hc
  rw [Measure.real]
  exact ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointsIndicatorFourierSelfUnramified
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.RatWeilOp

theorem ind_fourier_self : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    μ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 → (fun y : κ → Fv F v => ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ) = ind κ v := by
  intro F _ _ v ψ hψ κ _ _ _ μ _ hμ
  classical
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hSo : IsOpen {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
    have e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
        ⋂ i, (fun x : κ → Fv F v => x i) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext; simp
    rw [e]; exact isOpen_iInter_of_finite fun i => hO.preimage (continuous_apply i)
  have hSm := hSo.measurableSet
  have hψO : ∀ z ∈ v.adicCompletionIntegers F, ψ z = 1 := fun z hz => by
    simpa using (hψ 1).2 (v.adicCompletionIntegers F).one_mem z hz
  have hdot : ∀ x y : κ → Fv F v, (∀ i, x i ∈ v.adicCompletionIntegers F) → (∀ i, y i ∈ v.adicCompletionIntegers F) →
      x ⬝ᵥ y ∈ v.adicCompletionIntegers F := fun x y hx hy =>
    (v.adicCompletionIntegers F).sum_mem fun i _ => mul_mem (hx i) (hy i)
  funext y
  by_cases hy : ∀ i, y i ∈ v.adicCompletionIntegers F
  · have e : (fun x => ind κ v x * ψ (x ⬝ᵥ y)) =
        Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
      · have hx' : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_mem hx', Pi.one_apply, one_mul, hψO _ (hdot x y hx hy)]
      · have hx' : x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_notMem hx', zero_mul]
    have hy' : y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hy
    rw [e, integral_indicator hSm, setIntegral_const, Measure.real, hμ]
    simp [ind, Set.indicator_of_mem hy']
  · have hy' : y ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hy
    have h0 : ind κ v y = 0 := by simp only [ind, Set.indicator_of_notMem hy']
    rw [h0]
    push_neg at hy
    obtain ⟨i, hi⟩ := hy
    have : ¬ ∀ t ∈ v.adicCompletionIntegers F, ψ (y i * t) = 1 := fun h => hi ((hψ (y i)).1 h)
    push_neg at this
    obtain ⟨t, ht, hne⟩ := this
    have hs : ∀ j, (Pi.single i t : κ → Fv F v) j ∈ v.adicCompletionIntegers F := fun j => by
      by_cases hj : j = i
      · subst hj; simpa using ht
      · simp [Pi.single_apply, hj]
    have hind : ∀ x, ind κ v (Pi.single i t + x) = ind κ v x := fun x => by
      have : (∀ j, ((Pi.single i t : κ → Fv F v) + x) j ∈ v.adicCompletionIntegers F) ↔ ∀ j, x j ∈ v.adicCompletionIntegers F := by
        constructor
        · intro h j
          have := sub_mem (h j) (hs j)
          simpa using this
        · intro h j
          exact add_mem (hs j) (h j)
      by_cases hx : ∀ j, x j ∈ v.adicCompletionIntegers F
      · have h1 : Pi.single i t + x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := this.2 hx
        have h2 : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply]
      · have h1 : Pi.single i t + x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := fun h => hx (this.1 h)
        have h2 : x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    have key : ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ = ψ (y i * t) * ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ := by
      rw [← integral_const_mul]
      conv_lhs => rw [← integral_add_left_eq_self (μ := μ) (fun x => ind κ v x * ψ (x ⬝ᵥ y)) (Pi.single i t)]
      congr 1
      funext x
      rw [hind, add_dotProduct, single_dotProduct, AddChar.map_add_eq_mul, mul_comm t (y i)]
      ring
    have h1 : (1 - ψ (y i * t)) * ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm hne))

end GlobalTheory.RatWeilOp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
section
noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG)
open GlobalTheory.NormDict

namespace GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsScale (D : D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) : Prop :=
  r * D.host.conj r * ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E)

def coordY (θ : InfFam D) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ) (r : D.host.E) (w : WO S T) :
    VC D a d :=
  fun τ i j => δ * embT D τ r * compAt θ τ w (Fin.cast hT.symm i) (Fin.cast hS.symm j)

def Reads (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E) (G : VC D a d → ℂ) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ w : WO S T, w.map (finPart D) = 0 →
    f w = Complex.exp (-((Real.pi : ℂ) / 2) * Hf D (tor0 D cc δ) (coordY θ hS hT δ r w) (coordY θ hS hT δ r w)) *
      G (coordY θ hS hT δ r w)

structure Setup (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E) :
    Prop where
  std : IsStdChar D ψ (-1)
  inf : IsInfFam θ
  gS : S.gram = 1
  gT : T.gram = 1
  crv : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ
  scale : IsScale D cc r

def finPt {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (r : D.host.E) (z : Matrix (Fin d) (Fin a) D.host.E) :
    WO S T :=
  GlobalTheory.VacUnique.finRat S T (Matrix.of fun i j => -(r⁻¹ * z (Fin.cast hT i) (Fin.cast hS j)))

def IsFinIdl (x : (AE D)ˣ) (y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) = GlobalTheory.BotFormula.toFinE D (y : Formalism.MainNotions.StandardLatticesGL3.AE D)

def HasFinPart (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ) : Prop :=
  ∀ x y, IsFinIdl x y → ((χ x : Circle) : ℂ) = ((c.f y ^ e : ℂˣ) : ℂ)

def IsCongLevel {N : ℕ} (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D N)) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∀ k ∈ intG D N, (∀ i j, ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D,
    (((k : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j =
      (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * s) → k ∈ J

def period (D : D7) (δ : ℂ) (r : D.host.E) (τ : D.what₂.Tau) : ℂ :=
  δ * embT D τ r / (Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℂ)

def normConst (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : ℕ) (n : D.what₂.Tau → ℕ) : ℝ :=
  ∏ τ, (Real.pi / area (lamOf D cc δ)) ^ (a * n τ)

variable {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}

structure IsStdFrame (P : Pair D cc δ t0 Q) (Y : Frame P) : Prop where
  frame : IsFrame P Y
  ptA : ∀ x, GlobalTheory.BotFormula.IsFinPt Y.A (Y.ιA x) x
  ptB : ∀ h, GlobalTheory.BotFormula.IsFinPt Y.B (Y.ιB h) h

structure IsMaxLevel {P : Pair D cc δ t0 Q} (Y : Frame P) (K₀ : Subgroup (GL (Fin Y.B.rank) (Lev.EAf D)))
    (μ₀ : Measure (GA D Y.B)) : Prop where
  lev : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.B K₀
  mem_iff : ∀ h, Lev.finE Y.B (Y.ιB h) ∈ K₀ ↔ h ∈ intG D P.d
  meas : ∃ 𝓕, Links.IsMeasDef Y.B K₀ μ₀ 𝓕

structure IsExact (P : Pair D cc δ t0 Q) (X : Data P) (r : D.host.E) : Prop where
  std : IsStdFrame P X.toFrame
  inf : IsInfFam X.θ
  weil : IsWeilDatumO X.ψ X.A X.B X.χA X.χB X.om
  chA : HasFinPart X.χA P.W.chV P.W.ep
  chB : HasFinPart X.χB P.W.chV' (-P.W.ep')
  scale : IsScale D cc r
  read : Reads X.ψ X.θ X.rkA X.rkB cc δ r P.F X.vac
  const : X.c₁ = ∏ τ, period D δ r τ ^ (P.a * P.n τ)

theorem IsExact.setup {P : Pair D cc δ t0 Q} {X : Data P} {r : D.host.E} (h : IsExact P X r) :
    Setup X.ψ X.θ X.A X.B cc δ r :=
  ⟨h.weil.std, h.inf, h.std.frame.gramA, h.std.frame.gramB, P.crv, h.scale⟩

theorem isCongLevel_intG (N : ℕ) : IsCongLevel (intG D N) := ⟨1, one_pos, fun _ hk _ => hk⟩

theorem isScale_one (D : D7) : IsScale D D.host.ccK 1 := by simp [IsScale]

end GlobalTheory.NormExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExpansionIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest

namespace GlobalTheory.DepthUnf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def flatProd (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t)
    (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) : ℂ :=
  ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y)

def DepthOK (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (K : ℕ) : Prop :=
  (∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) → flatProd S t Φ β x y ≠ 0 →
        (∀ j : Fin D.R.m, K • x j ∈ pairLat G (.top t j)) ∧ ∀ i : Fin D.R.m, K • y i ∈ pairLat G (.chi i D.R.m)) ∧
  ∀ (x u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) → (∀ j : Fin D.R.m, IsHalf e (u j) ∧ u j ∈ pairLat G (.top t j)) →
      (∀ i : Fin D.R.m, IsHalf e (v i) ∧ v i ∈ pairLat G (.chi i D.R.m)) → flatProd S t Φ β (x + K • u) (y + K • v) = flatProd S t Φ β x y

def ExpWith (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) : Prop :=
  (∀ d ∈ τ.support, (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧
      ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1) ∧
    ∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) →
        (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) = flatProd S t Φ β x y

end GlobalTheory.DepthUnf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_heisenberg_lattice_vacuum_function : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))),
    IsOpen (Λ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (x₀ : κ → Fv F v),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : Fv F v) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → Fv F v, ((0 : κ → Fv F v), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, χ (u + u) = 1) → IsLocallyConstant (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) := by
  first | exact @GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place | exact GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place | (intros; apply GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour

variable {F : Type} [Field F] [NumberField F]

def IsSelfDualFor {v : Pl (F := F)} (χ : AddChar (Fv F v) ℂ) (ν : Measure (Fv F v)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∀ f ∈ SB (Fv F v), ∫ y, (∫ x, f x * χ (x * y) ∂ν) ∂ν = f 0

open Classical in
def measV (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) : Measure (Fv F v) :=
  if h : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν then h.choose else 0

def fourV (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) {κ : Type} [Fintype κ] (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) : ℂ :=
  ∫ x, φ x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y) ∂(Measure.pi fun _ : κ => measV ψ v)


open Classical in
variable (F) in
def measI (κ : Type) [Fintype κ] : Measure (κ → mixedEmbedding.mixedSpace F) :=
  Measure.pi fun _ : κ => (Measure.pi fun _ : {w : InfinitePlace F // w.IsReal} => (volume : Measure ℝ)).prod
    (Measure.pi fun _ : {w : InfinitePlace F // w.IsComplex} => (volume : Measure ℂ))

def eInf {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ))

end GlobalTheory.WeylFour

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerSkewConjMemThetaFunctions
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

theorem GlobalTheory.BotPairSmall.iop_skew_conj_mem_TT : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) ∈ TT D (tor0 D ⊤ δ) a d := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hlc := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have s0 := VacMove.sd_of_moves (VacMove.moves_one D a)
  have s0' := VacMove.sd_of_moves (VacMove.moves_one D d)
  have heT : e0 ∈ TT D (tor0 D ⊤ δ) a d := hlc.1 _ _ s0 s0' e0 hv.1
  have hne : D.host.conj • (D.host.conj • 𝔪) ≠ ⊥ :=
    GlobalTheory.BotPairSmall.conj_smul_ne_bot D (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm)
  obtain ⟨M, hM, hMs⟩ := GlobalTheory.BotPairSmall.CosetTheta.skewLat_nsmul_le (D := D) (D.host.conj • 𝔪) hne d
  exact GlobalTheory.BotPairSmall.CosetTheta.iop_mem_TT hc hM
    (fun x hx => GlobalTheory.BotPairSmall.CosetTheta.La_nsmul_mem (L := stdL D a) ⊤ δ M hMs hx) heT
end
end

