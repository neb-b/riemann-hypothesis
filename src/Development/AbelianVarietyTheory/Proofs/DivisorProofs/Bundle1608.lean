module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierDoubleReflection
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour.LocInv

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance borelFvLoc (v : Pl (F := F)) : BorelSpace (Fv F v) := ⟨rfl⟩

open GlobalTheory.SplitWeil

theorem norm_addChar_eq_one {v : Pl (F := F)} (χ : AddChar (Fv F v) ℂ) (hχ : Continuous χ) (x : Fv F v) :
    ‖χ x‖ = 1 := by
  have hb : ∀ y : Fv F v, ‖χ y‖ ≤ 1 := by
    intro y
    obtain ⟨s, hs⟩ : ∃ s : (Fv F v)ˣ, y ∈ cball s := by
      by_cases hy : y = 0
      · exact ⟨1, by simp [hy, cball]⟩
      · exact ⟨Units.mk0 y hy, by simp [cball]⟩
    obtain ⟨M, hM⟩ := (isCompact_cball s).exists_bound_of_continuousOn hχ.continuousOn
    have hn : ∀ n : ℕ, ‖χ y‖ ^ n ≤ M := by
      intro n
      have hmem : n • y ∈ cball s := by
        induction n with
        | zero => simp [cball]
        | succ n ih => rw [succ_nsmul]; exact add_mem_cball ih hs
      rw [← norm_pow, ← AddChar.map_nsmul_eq_pow]
      exact hM _ hmem
    by_contra h
    push_neg at h
    obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt M h
    exact absurd (hn n) (not_le.mpr hn')
  have h1 := hb x
  have h2 := hb (-x)
  have h3 : χ x * χ (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h4 : ‖χ x‖ * ‖χ (-x)‖ = 1 := by rw [← norm_mul, h3, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg (χ x), norm_nonneg (χ (-x))]

def toCirc {v : Pl (F := F)} (χ : AddChar (Fv F v) ℂ) (h : ∀ x, ‖χ x‖ = 1) : AddChar (Fv F v) Circle where
  toFun x := ⟨χ x, by simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using h x⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' a b := by
    apply Circle.ext
    exact χ.map_add_eq_mul a b

theorem coe_toCirc {v : Pl (F := F)} (χ : AddChar (Fv F v) ℂ) (h : ∀ x, ‖χ x‖ = 1) (x : Fv F v) :
    ((toCirc χ h x : Circle) : ℂ) = χ x := rfl

theorem continuous_psiAt' (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F)) :
    Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
  have hj : Continuous (GlobalTheory.LatVac.liftV (F := F) v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  exact hψ.comp hj

theorem measV_selfDual (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (v : Pl (F := F)) (hne : ∃ x, psiLoc ψ v x ≠ 1) :
    ∃ (h : ∀ x, ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1) (c : (Fv F v)ˣ),
      HasConductor (toCirc _ h) c ∧ IsSelfDual (toCirc _ h) (measV ψ v) := by
  have hc := continuous_psiAt' ψ hψ.1 v
  have hn : ∀ x, ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1 := norm_addChar_eq_one _ hc
  have hcc : Continuous (toCirc _ hn) := Continuous.subtype_mk hc _
  have hne1 : toCirc _ hn ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    intro h1
    apply hx
    have := congrArg (fun χ : AddChar (Fv F v) Circle => ((χ x : Circle) : ℂ)) h1
    simpa [coe_toCirc, GlobalTheory.LatVac.psiAt_apply] using this
  obtain ⟨c, hcond⟩ := exists_hasConductor_of_continuous _ hcc hne1
  obtain ⟨ν, hν⟩ := exists_isSelfDual_of_hasConductor hcond
  have hex : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := ⟨ν, hν.1, fun f hf => hν.2 f hf⟩
  refine ⟨hn, c, hcond, ?_⟩
  have hm : measV ψ v = hex.choose := by
    unfold measV
    rw [dite_eq_left hex]
  rw [hm]
  exact ⟨hex.choose_spec.1, fun f hf => hex.choose_spec.2 f hf⟩

end GlobalTheory.WeylFour.LocInv

namespace GlobalTheory.WeylFour.LocInv

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fourV_fourV : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl (F := F),
    (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ], ∀ φ ∈ SB (κ → Fv F v), fourV ψ v (fourV ψ v φ) = fun x => φ (-x) := by
  intro F _ _ ψ hψ v hne κ _ φ hφ
  classical
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hn, c, hcond, hself⟩ := measV_selfDual ψ hψ v hne
  haveI := hself.1
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  haveI := GlobalTheory.SplitWeil.t2Space (Fv F v)
  funext z
  have hinner : ∀ y, fourV ψ v φ y * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) =
      ∫ x, φ (x - z) * ((toCirc _ hn (x ⬝ᵥ y) : Circle) : ℂ) ∂(Measure.pi fun _ : κ => measV ψ v) := by
    intro y
    unfold fourV
    rw [← integral_mul_const]
    have h1 : ∀ x : κ → Fv F v, φ x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y) * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) =
        φ x * GlobalTheory.LatVac.psiAt ψ v ((x + z) ⬝ᵥ y) := by
      intro x
      rw [add_dotProduct, AddChar.map_add_eq_mul, dotProduct_comm z y, mul_assoc]
    simp only [h1]
    rw [← integral_sub_right_eq_self (μ := Measure.pi fun _ : κ => measV ψ v)
      (fun x => φ x * GlobalTheory.LatVac.psiAt ψ v ((x + z) ⬝ᵥ y)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [sub_add_cancel, coe_toCirc]
  have hg : (fun x : κ → Fv F v => φ (x - z)) ∈ GlobalTheory.SplitWeil.SB (κ → Fv F v) :=
    ⟨hφ.1.comp_continuous (continuous_id.sub continuous_const),
      hφ.2.comp_homeomorph (Homeomorph.subRight z)⟩
  have h2 := (GlobalTheory.SplitWeil.FourierPi.fourier_pi_of_conductor hcond hself hg).2
  show ∫ y, fourV ψ v φ y * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) ∂(Measure.pi fun _ : κ => measV ψ v) = φ (-z)
  simp only [hinner]
  rw [h2, zero_sub]

end GlobalTheory.WeylFour.LocInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchrodingerIntertwine
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeylFour

theorem schr_fourV_loc : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl (F := F)) (κ : Type) [Fintype κ]
    (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    fourV ψ v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (w.2, -w.1) (fourV ψ v φ) := by
  intro F _ _ ψ _ v κ _ w φ
  haveI hOc : CompactSpace (v.adicCompletionIntegers F) :=
    GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  haveI : LocallyCompactSpace (Fv F v) :=
    (isCompact_iff_compactSpace.2 hOc).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem (v.adicCompletionIntegers F)))
  haveI : SecondCountableTopology (Fv F v) := by
    have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    have : TopologicalSpace.SeparableSpace (Fv F v) :=
      ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
        IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
    exact UniformSpace.secondCountable_of_separable (Fv F v)
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hinv : (measV ψ v).IsAddLeftInvariant ∧ SigmaFinite (measV ψ v) := by
    unfold measV
    split_ifs with h
    · haveI := h.choose_spec.1
      exact ⟨inferInstance, inferInstance⟩
    · exact ⟨⟨fun g => by simp⟩, inferInstance⟩
  haveI := hinv.1
  haveI := hinv.2
  have h2 : (⅟2 : Fv F v) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  funext y
  simp only [fourV, schr]
  set χ := GlobalTheory.LatVac.psiAt ψ v
  set μ := Measure.pi fun _ : κ => measV ψ v
  let g : (κ → Fv F v) → ℂ := fun x =>
    χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ x * χ ((x - w.1) ⬝ᵥ y)
  have hg : ∀ x, χ (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ (x + w.1) * χ (x ⬝ᵥ y) = g (x + w.1) := by
    intro x; simp only [g, add_sub_cancel_right]
  simp_rw [hg]
  rw [integral_add_right_eq_self g w.1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [g]
  have key : (x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) + (x - w.1) ⬝ᵥ y =
      y ⬝ᵥ (-w.1) + ⅟(2 : Fv F v) * (w.2 ⬝ᵥ (-w.1)) + x ⬝ᵥ (y + w.2) := by
    simp only [sub_dotProduct, dotProduct_add, dotProduct_neg]
    rw [dotProduct_comm y w.1, dotProduct_comm w.2 w.1]
    linear_combination (w.1 ⬝ᵥ w.2) * h2
  calc χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ x * χ ((x - w.1) ⬝ᵥ y)
      = φ x * (χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * χ ((x - w.1) ⬝ᵥ y)) := by ring
    _ = φ x * χ (y ⬝ᵥ (-w.1) + ⅟(2 : Fv F v) * (w.2 ⬝ᵥ (-w.1)) + x ⬝ᵥ (y + w.2)) := by
      rw [← AddChar.map_add_eq_mul, key]
    _ = _ := by rw [AddChar.map_add_eq_mul]; ring

end GlobalTheory.WeylFour
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchwartzStable
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F]

theorem exists_circle_conductor (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F)) (h1 : ∃ x, psiLoc ψ v x ≠ 1) :
    ∃ (χ : AddChar (Fv F v) Circle) (c : (Fv F v)ˣ), GlobalTheory.SplitWeil.HasConductor χ c ∧
      ∀ x, (χ x : ℂ) = GlobalTheory.LatVac.psiAt ψ v x := by
  have hc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hψ v
  let χ : AddChar (Fv F v) Circle :=
    { toFun := fun x => ⟨GlobalTheory.LatVac.psiAt ψ v x, mem_sphere_zero_iff_norm.2 (GlobalTheory.norm_addChar_nonarch _ hc x)⟩
      map_zero_eq_one' := Circle.ext (by simp)
      map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul _ a b) }
  have hχ : ∀ x, (χ x : ℂ) = GlobalTheory.LatVac.psiAt ψ v x := fun _ => rfl
  have hχc : Continuous χ := continuous_induced_rng.2 hc
  have hχ1 : χ ≠ 1 := fun h => by
    obtain ⟨x, hx⟩ := h1
    refine hx ?_
    rw [← GlobalTheory.LatVac.psiAt_apply, ← hχ, h]
    simp
  obtain ⟨c, hc0⟩ := GlobalTheory.SplitWeil.exists_hasConductor_of_continuous χ hχc hχ1
  exact ⟨χ, c, hc0, hχ⟩

theorem isSelfDualFor_measV (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F)) (h1 : ∃ x, psiLoc ψ v x ≠ 1) :
    IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) (measV ψ v) := by
  obtain ⟨χ, c, hc, hχ⟩ := exists_circle_conductor ψ hψ v h1
  have h : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isSelfDual_of_hasConductor hc
    refine ⟨ν, hν.1, fun f hf => ?_⟩
    simpa only [hχ] using hν.2 f hf
  rw [measV, dite_eq_left h]
  exact h.choose_spec

theorem fourV_sb : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl (F := F), (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ],
    (∀ φ ∈ SB (κ → Fv F v), fourV ψ v φ ∈ SB (κ → Fv F v)) ∧
    (∀ φ ∈ SB (κ → Fv F v), ∀ χ ∈ SB (κ → Fv F v), fourV ψ v (φ + χ) = fourV ψ v φ + fourV ψ v χ) ∧
    ∀ (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v), schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ SB (κ → Fv F v) := by
  intro F _ _ ψ hψ v h1 κ _
  classical
  have hcont : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hψ.1 v
  obtain ⟨χ, c, hc, hχ⟩ := exists_circle_conductor ψ hψ.1 v h1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : SecondCountableTopology (Fv F v) := GlobalTheory.SplitWeil.secondCountable _
  haveI := (isSelfDualFor_measV ψ hψ.1 v h1).1
  refine ⟨fun φ hφ => ?_, fun φ hφ φ' hφ' => ?_, fun w φ hφ => GlobalTheory.SchrSBFin.schr_mem_SB v _ hcont w φ hφ⟩
  · have h := GlobalTheory.SplitWeil.FourierPi.fourier_mem_SB (Measure.pi fun _ : κ => measV ψ v) hc hφ
    simp only [hχ] at h
    exact h
  · have hint : ∀ f ∈ SB (κ → Fv F v), ∀ y : κ → Fv F v,
        Integrable (fun x => f x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y)) (Measure.pi fun _ : κ => measV ψ v) := fun f hf y =>
      Continuous.integrable_of_hasCompactSupport
        (hf.1.continuous.mul (hcont.comp (continuous_id.dotProduct continuous_const))) hf.2.mul_right
    funext y
    simp only [fourV, Pi.add_apply, add_mul]
    exact integral_add (hint φ hφ y) (hint φ' hφ' y)

end GlobalTheory.WeylFour

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIndicatorFourier
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour.IndOSelf

open ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F]

local instance borelFvAt (v : Pl (F := F)) : BorelSpace (Fv F v) := ⟨rfl⟩

theorem mem_int_iff {v : Pl (F := F)} (x : Fv F v) : x ∈ 𝒪[Fv F v] ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (Fv F v))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem exists_nat_mul_mem (v : Pl (F := F)) (x : Fv F v) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : Fv F v) * x ∈ v.adicCompletionIntegers F := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  · have h1 := congrArg (algebraMap (𝓞 F) (v.adicCompletion F)) hc
    rw [map_mul, map_natCast] at h1
    rw [← h1, mul_assoc, mul_comm _ x]
    exact mul_mem (HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v c) hbx

theorem norm_psiAt (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) (x : Fv F v) :
    ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1 := by
  obtain ⟨N, hN, hx⟩ := exists_nat_mul_mem v x
  have h1 : GlobalTheory.LatVac.psiAt ψ v ((N : Fv F v) * x) = 1 := by
    have := ((hψ 1).2 (one_mem _)) _ hx
    rwa [one_mul] at this
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h1
  exact Complex.norm_eq_one_of_pow_eq_one h1 hN

def psiC (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) : AddChar (Fv F v) Circle where
  toFun x := ⟨GlobalTheory.LatVac.psiAt ψ v x, mem_sphere_zero_iff_norm.2 (norm_psiAt ψ v hψ x)⟩
  map_zero_eq_one' := Subtype.ext (AddChar.map_zero_eq_one _)
  map_add_eq_mul' x y := Subtype.ext (AddChar.map_add_eq_mul _ x y)

theorem coe_psiC (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) (x : Fv F v) :
    ((psiC ψ v hψ x : Circle) : ℂ) = GlobalTheory.LatVac.psiAt ψ v x := rfl

theorem hasConductor_psiC (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) :
    GlobalTheory.SplitWeil.HasConductor (psiC ψ v hψ) 1 := by
  intro x
  have e1 : ∀ y, psiC ψ v hψ y = 1 ↔ GlobalTheory.LatVac.psiAt ψ v y = 1 := fun y =>
    ⟨fun h => by rw [← coe_psiC ψ v hψ, h]; rfl, fun h => Circle.ext (by rw [coe_psiC ψ v hψ, h]; rfl)⟩
  rw [Units.val_one, map_one, ← Valuation.mem_integer_iff, mem_int_iff, ← hψ x]
  simp only [e1]
  constructor
  · intro h y hy
    apply h
    rw [map_mul]
    have : valuation (Fv F v) y ≤ 1 := (Valuation.mem_integer_iff _ _).1 ((mem_int_iff y).2 hy)
    exact mul_le_of_le_one_right' this
  · intro h y hy
    by_cases hx : x = 0
    · subst hx
      rw [map_zero, le_zero_iff, map_eq_zero] at hy
      subst hy
      exact AddChar.map_zero_eq_one _
    · have hyx : y / x ∈ v.adicCompletionIntegers F := by
        rw [← mem_int_iff, Valuation.mem_integer_iff, map_div₀,
          div_le_one₀ (by rw [zero_lt_iff, Ne, map_eq_zero]; exact hx)]
        exact hy
      have := h _ hyx
      rwa [mul_div_cancel₀ _ hx] at this

theorem indO_mem_SB (v : Pl (F := F)) (κ : Type) [Fintype κ] : GlobalTheory.SympChange.indO (κ := κ) v ∈ SB (κ → Fv F v) := by
  set S : Set (κ → Fv F v) := {x | ∀ i, x i ∈ v.adicCompletionIntegers F} with hSdef
  have hS : S = Set.univ.pi fun _ => ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) := by
    ext x; simp [S, mem_int_iff]
  have hc : IsCompact S := hS ▸ isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int _
  have ho : IsOpen S := hS ▸ isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.isOpen_int _
  have hcl : IsClosed S := hc.isClosed
  have hind : GlobalTheory.SympChange.indO (κ := κ) v = S.indicator 1 := rfl
  rw [hind]
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ S
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl
  · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem exists_selfDual (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) :
    ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := by
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isUnitVol (Fv F v)
  have h := GlobalTheory.SplitWeil.isSelfDual_of_isUnitVol ν (hasConductor_psiC ψ v hψ) hν
  exact ⟨ν, h.1, fun f hf => h.2 f hf⟩

theorem isUnitVol_measV (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) :
    GlobalTheory.SplitWeil.IsUnitVol (measV ψ v) := by
  have hex := exists_selfDual ψ v hψ
  have hm : measV ψ v = hex.choose := by simp only [measV, dif_pos hex]
  have hs := hex.choose_spec
  rw [hm]
  exact (GlobalTheory.SplitWeil.isUnitVol_iff_isSelfDual (hasConductor_psiC ψ v hψ) _).2 ⟨hs.1, fun f hf => hs.2 f hf⟩

theorem fourV_indO (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) (κ : Type) [Fintype κ] :
    fourV ψ v (GlobalTheory.SympChange.indO (κ := κ) v) = GlobalTheory.SympChange.indO v := by
  classical
  have hU := isUnitVol_measV ψ v hψ
  haveI := hU.1
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  have hball : GlobalTheory.SplitWeil.cball (1 : (Fv F v)ˣ) = ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) := by
    ext x; simp [GlobalTheory.SplitWeil.cball, Valuation.mem_integer_iff]
  have hbox : GlobalTheory.SplitWeil.FourierPi.box κ (1 : (Fv F v)ˣ) = {x | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
    ext x; simp [GlobalTheory.SplitWeil.FourierPi.box, hball, ← mem_int_iff]
  have hvol : (Measure.pi fun _ : κ => measV ψ v).real (GlobalTheory.SplitWeil.FourierPi.box κ 1) = 1 := by
    simp [Measure.real, GlobalTheory.SplitWeil.FourierPi.box, Measure.pi_pi, hball, hU.2]
  funext y
  have h := GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi (Measure.pi fun _ : κ => measV ψ v)
    (hasConductor_psiC ψ v hψ) 1 y
  rw [mul_inv_cancel, hvol, hbox] at h
  exact h

theorem indO_self_fourier : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl (F := F))
    (κ : Type) [Fintype κ], GlobalTheory.SympChange.indO (κ := κ) v ∈ SB (κ → Fv F v) ∧
    (PsiUnr ψ v → fourV ψ v (GlobalTheory.SympChange.indO (κ := κ) v) = GlobalTheory.SympChange.indO v) := by
  intro F _ _ ψ _ v κ _
  exact ⟨indO_mem_SB v κ, fun h => fourV_indO ψ v h κ⟩

end GlobalTheory.WeylFour.IndOSelf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
section
noncomputable section

open NumberField

namespace GlobalTheory.VacRead

def cE (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {x | ∃ c ∈ cc, x = ((c : D.host.K) : D.host.E)}

def bInv (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {y | ∃ α ∈ cE D cc, ∃ γ ∈ cE D D.host.ccK,
    y = r * D.host.conj α * γ / (Ideal.absNorm cc : D.host.E)}

def lsB (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ) : GlobalTheory.InertSign.Lat D a :=
  Submodule.pi Set.univ fun _ => bInv D cc r

theorem mem_lsB {D : Formalism.BasicNotions.D7} {cc : Ideal (𝓞 D.host.K)} {r : D.host.E} {a : ℕ} {y : Fin a → D.host.E} :
    y ∈ lsB D cc r a ↔ ∀ i, y i ∈ bInv D cc r := by
  simp [lsB, Submodule.mem_pi]

end GlobalTheory.VacRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedAbsDetMulIntegralCompMulVecFinitePlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedAbsDet_mul_integral_comp_mulVec_finitePlace : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ (T : GL (Fin N) (Fv F v)) (f : (Fin N → Fv F v) → ℂ),
      ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  first | exact @GlobalTheory.InertLagChar.nabs_det_mul_integral_comp_mulVec | exact GlobalTheory.InertLagChar.nabs_det_mul_integral_comp_mulVec | (intros; apply GlobalTheory.InertLagChar.nabs_det_mul_integral_comp_mulVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompareStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_darboux_coordinates_compare : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (c₁ c₂ : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₂.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ G : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F,
      GlobalTheory.SympChange.IsSymp G ∧ ∀ w, c₂.e w = GlobalTheory.SympChange.spAct G (c₁.e w) := by
  first | exact @GlobalTheory.SympChange.darboux_change_rat | exact GlobalTheory.SympChange.darboux_change_rat | (intros; apply GlobalTheory.SympChange.darboux_change_rat <;> assumption)
end

