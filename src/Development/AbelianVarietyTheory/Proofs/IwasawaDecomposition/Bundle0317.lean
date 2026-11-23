module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0315
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitone
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AlgWtHW
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField Finset

section
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sle_mulVec {Φ : GL (Fin n) ℂ → Matrix ι ι ℂ} {M : Matrix ι ι ℂ} (hM : ∀ A, M * Φ A = Φ A * M)
    (lam : Fin n → ℤ) {x : ι → ℂ} (hx : x ∈ Sle Φ lam) : M *ᵥ x ∈ Sle Φ lam := by
  have h : Sle Φ lam ≤ (Sle Φ lam).comap (Matrix.mulVecLin M) := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨ν, hν, hw⟩
    refine Submodule.subset_span ⟨ν, hν, fun D hD => ?_⟩
    show Φ D *ᵥ (M *ᵥ w) = _
    rw [Matrix.mulVec_mulVec, ← hM, ← Matrix.mulVec_mulVec, hw D hD, Matrix.mulVec_smul]
    rfl
  exact h hx

theorem filter_succ (i : Fin n) : univ.filter (fun j : Fin n => (j : ℕ) < (i : ℕ) + 1) =
    insert i (univ.filter (fun j : Fin n => (j : ℕ) < i)) := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

theorem not_mem_filter_self (i : Fin n) : i ∉ univ.filter (fun j : Fin n => (j : ℕ) < i) := by
  simp

theorem domLE_antisymm {μ lam : Fin n → ℤ} (h1 : DomLE μ lam) (h2 : DomLE lam μ) : μ = lam := by
  have hs : ∀ k : ℕ, ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), μ i =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), lam i := fun k => le_antisymm (h1.2 k) (h2.2 k)
  funext i
  have h := hs ((i : ℕ) + 1)
  rw [filter_succ, sum_insert (not_mem_filter_self i), sum_insert (not_mem_filter_self i), hs i] at h
  linarith

theorem le_of_domLE_swap {lam : Fin n → ℤ} {i j : Fin n} (hij : i < j)
    (h : DomLE (lam ∘ Equiv.swap i j) lam) : lam j ≤ lam i := by
  have h1 := h.2 ((i : ℕ) + 1)
  rw [filter_succ, sum_insert (not_mem_filter_self i), sum_insert (not_mem_filter_self i)] at h1
  have h2 : ∑ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), (lam ∘ Equiv.swap i j) l =
      ∑ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), lam l := by
    refine sum_congr rfl fun l hl => ?_
    simp only [mem_filter, mem_univ, true_and] at hl
    have hli : l ≠ i := fun e => by rw [e] at hl; omega
    have hlj : l ≠ j := fun e => by rw [e] at hl; rw [Fin.lt_def] at hij; omega
    simp [Function.comp, Equiv.swap_apply_of_ne_of_ne hli hlj]
  rw [h2] at h1
  simp only [Function.comp, Equiv.swap_apply_left] at h1
  linarith

end

section
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem algWeight_space_nontrivial (a : AlgWt L n) : Nontrivial a.W := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := a.irr
  exact bot_ne_top (α := Subrepresentation a.ρ)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem beig_of_hwAt {a : AlgWt L n} {τ : L →+* ℂ} {lam : Fin n → ℤ} (h : a.HWAt τ lam) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι ℂ a.W)
      (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (v : ι → ℂ),
      Agrees a b P ∧ IsBEig (fun B => evM P (evPt τ B)) v lam := by
  obtain ⟨ι, i1, i2, b, P, hP, v, hv, hB⟩ := h
  exact ⟨ι, i1, i2, b, P, v, hP, hv, hB⟩

theorem domLE_of_agrees {a : AlgWt L n} {τ : L →+* ℂ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {b : Module.Basis ι ℂ a.W} {P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    (hP : Agrees a b P) {v : ι → ℂ} {lam μ : Fin n → ℤ}
    (hv : IsBEig (fun B => evM P (evPt τ B)) v lam) (hμ : IsWt (fun B => evM P (evPt τ B)) μ) :
    DomLE μ lam := by
  obtain ⟨w, hw0, hw⟩ := hμ
  have hR := GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ
  refine _root_.GlobalTheory.AlgWtHW.DomLEOfSle.domLE_of_mem_Sle n ι _ hR μ lam w hw hw0 ?_
  have hspan := _root_.GlobalTheory.AlgWtHW.span_tau_commutant L n a ι b P hP τ v hv.1 w
  refine (Submodule.span_le.2 ?_) hspan
  rintro x ⟨B, M, hM, rfl⟩
  have e : evM P (evPt τ B) *ᵥ (M *ᵥ v) = M *ᵥ (evM P (evPt τ B) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  rw [e]
  exact sle_mulVec hM lam (_root_.GlobalTheory.AlgWtHW.mulVec_mem_sle_of_isBEig n ι _ hR v lam hv B)

theorem isWt_of_beig {ι : Type} [Fintype ι] {Φ : GL (Fin n) ℂ → Matrix ι ι ℂ} {v : ι → ℂ} {lam : Fin n → ℤ}
    (h : IsBEig Φ v lam) : IsWt Φ lam :=
  ⟨v, h.1, fun D hD => h.2 D (fun i j hij => hD (ne_of_gt hij))⟩

theorem beig_transport {a : AlgWt L n} {τ : L →+* ℂ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {b : Module.Basis ι ℂ a.W} {P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {b' : Module.Basis ι' ℂ a.W} {P' : ι' → ι' → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    (hP : Agrees a b P) (hP' : Agrees a b' P') {v' : ι' → ℂ} {lam : Fin n → ℤ}
    (hv : IsBEig (fun B => evM P' (evPt τ B)) v' lam) :
    IsBEig (fun B => evM P (evPt τ B)) (b.toMatrix b' *ᵥ v') lam := by
  have hC : b'.toMatrix b * b.toMatrix b' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b' b
  refine ⟨fun h0 => hv.1 ?_, fun B hB => ?_⟩
  · have := congrArg (fun x => b'.toMatrix b *ᵥ x) h0
    simpa [Matrix.mulVec_mulVec, hC] using this
  · show evM P (evPt τ B) *ᵥ (b.toMatrix b' *ᵥ v') = _
    rw [_root_.GlobalTheory.AlgWtHW.evM_change_of_basis L n a ι' b' P' ι b P hP' hP τ B, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hC,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    have := hv.2 B hB
    simp only at this
    rw [this, Matrix.mulVec_smul]

theorem hw_exists_unique_antitone : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
    (τ : L →+* ℂ), (∃! lam, a.HWAt τ lam) ∧ ∀ lam, a.HWAt τ lam → Antitone lam := by
  intro L _ _ _ n a τ
  have hanti : ∀ lam, a.HWAt τ lam → Antitone lam := by
    intro lam h
    obtain ⟨ι, _, _, b, P, v, hP, hv⟩ := beig_of_hwAt h
    intro i j hij
    rcases eq_or_lt_of_le hij with e | hlt
    · rw [e]
    · exact le_of_domLE_swap hlt (domLE_of_agrees hP hv
        (_root_.GlobalTheory.isWt_comp_swap n ι _ (GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ) lam (isWt_of_beig hv) i j))
  refine ⟨?_, hanti⟩
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  haveI := algWeight_space_nontrivial a
  haveI := b.index_nonempty
  obtain ⟨v, lam, hv⟩ := _root_.GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep n ι _ (GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ)
  refine ⟨lam, ⟨ι, inferInstance, inferInstance, b, P, hP, v, hv.1, hv.2⟩, fun lam' h' => ?_⟩
  obtain ⟨ι', _, _, b', P', v', hP', hv'⟩ := beig_of_hwAt h'
  have hv'' := beig_transport hP hP' hv'
  exact domLE_antisymm (domLE_of_agrees hP hv (isWt_of_beig hv'')) (domLE_of_agrees hP hv'' (isWt_of_beig hv))

end

end GlobalTheory.AlgWtHW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAe
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.BlockVal

open NumberField IsDedekindDomain Polynomial in
private theorem block_val_mul_sqrt_normV_zpow_neg_eq_mul_inv {E : Type} [Field E] [NumberField E]
    (μ η : _root_.Formalism.L2.Host.HChar E) (r : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) * (Real.sqrt (_root_.Formalism.ConjugateSelfDual.normV v) : ℂ) ^ (-(r : ℤ)) =
      (((μ * η⁻¹).val v : ℂˣ) : ℂ) := by
  have hval : (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) =
      (((μ * η⁻¹).val v : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((((r : ℝ) / 2 : ℝ)) : ℂ) :=
    _root_.GlobalTheory.GalChar.block_val μ η r v
  have hN : (_root_.Formalism.ConjugateSelfDual.normV v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    unfold _root_.Formalism.ConjugateSelfDual.normV
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne : Ideal.absNorm v.asIdeal ≠ 0 := by
    have := _root_.GlobalTheory.GalChar.absNorm_ne_zero v
    exact_mod_cast this
  have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hne)
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hNdef
  have hpow : (N : ℂ) ^ ((((r : ℝ) / 2 : ℝ)) : ℂ) = ((Real.sqrt N ^ r : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hpos.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hpos.le]
    congr 2
    ring
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  rw [hval, hN]
  have hcast : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (N : ℂ) := by simp [hNdef]
  rw [hcast, hpow, zpow_neg, zpow_natCast, Complex.ofReal_pow, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hs)), mul_one]


open NumberField IsDedekindDomain Polynomial in
theorem _root_.GlobalTheory.BlockVal.block_val_ae : ∀ {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (ε : K →+* ℂ)
    (μ η : _root_.Formalism.L2.Host.HChar E),
    _root_.GlobalTheory.GalChar.AlmostIn ε μ → η.ValuesIn (1 / 2) ε → ∀ {r : ℕ}, Odd r →
    ∀ (μH ηH : _root_.Formalism.L2.NC.HC E),
    μH.χ = (μ : _root_.Neutral.B1.Ideles E →* ℂˣ) → ηH.χ = (η : _root_.Neutral.B1.Ideles E →* ℂˣ) → ∀ᶠ v in Filter.cofinite,
    (μH * ηH⁻¹).At v ((((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) *
      (Real.sqrt (_root_.Formalism.ConjugateSelfDual.normV v) : ℂ) ^ (-(r : ℤ))) ∧
    ∃ y : K, ε y = (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ)⁻¹ := by
  intro E _ _ K _ ε μ η hμ hη r hr μH ηH hμH hηH
  have hχ : (μH * ηH⁻¹).χ = ((μ * η⁻¹ : _root_.Formalism.L2.Host.HChar E) : _root_.Neutral.B1.Ideles E →* ℂˣ) := by
    change μH.χ * ηH.χ⁻¹ = _
    rw [hμH, hηH]
    rfl
  have hblock := _root_.GlobalTheory.GalChar.AlmostIn.block hμ hη hr
  unfold _root_.GlobalTheory.GalChar.AlmostIn at hblock
  filter_upwards [hblock, _root_.GlobalTheory.GalChar.unr_ae (μ * η⁻¹)] with v hv hunr
  refine ⟨?_, ?_⟩
  · rw [block_val_mul_sqrt_normV_zpow_neg_eq_mul_inv]
    exact (_root_.GlobalTheory.HeckeUnifVal.at_val_and_unr_iff (μ * η⁻¹) (μH * ηH⁻¹) hχ v).1 hunr
  · obtain ⟨y, hy⟩ := hv
    exact ⟨y⁻¹, by rw [map_inv₀, hy]⟩

end GlobalTheory.BlockVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharEqOfApplyRootEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
namespace GlobalTheory.TameTau

theorem char_eq_of_apply_root_eq : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (ϖ : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ π : Ω, π ^ m = algebraMap E Ω (ϖ : E) → ∀ σ ∈ Ine (F := E) A, ∀ σ' ∈ Ine (F := E) A, σ π = σ' π → χ σ = χ σ' := by
  intro E Ω _ _ _ _ _ A P hP O _ _ _ _ _ hO χ hχ m hm hmP hχm ϖ hϖP hϖ2 π hπ σ hσ σ' hσ' heq
  have hm0 : m ≠ 0 := hm.ne'
  have hvm : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    rw [← hP]
    simpa using h
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ2 (Ideal.zero_mem _)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0, eq_comm, map_eq_zero_iff _ (algebraMap E Ω).injective] at hπ
    exact hϖ0 (by exact_mod_cast hπ)
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt_of_valuationSubring (E := E) A
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ m := by
    have : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.2 hm0⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  obtain ⟨σ₀, hσ₀, hσ₀π⟩ := GlobalTheory.T.inertia_acts_on_tame_root A P hP m hm hmP ϖ hϖP hϖ2 π hπ ζ hζ.pow_eq_one
  have J := fun τ hτ => GlobalTheory.T.character_tameQuotient_jointPowers_tameGenerator A γ hγ hO χ hχ m hm hvm hχm (ϖ : E) π hπ0 hπ τ hτ
  obtain ⟨k, -, hk⟩ := J σ₀ hσ₀
  obtain ⟨n, hn1, hn2⟩ := J σ hσ
  obtain ⟨n', hn1', hn2'⟩ := J σ' hσ'
  set θ := γ π / π with hθ
  rw [hσ₀π, mul_div_cancel_right₀ _ hπ0] at hk
  have hθn : θ ^ n = θ ^ n' := by rw [← hn2, ← hn2', heq]
  have hζn : ζ ^ n = ζ ^ n' := by rw [hk, ← pow_mul, ← pow_mul, mul_comm k n, mul_comm k n', pow_mul, pow_mul, hθn]
  have hmod : n ≡ n' [MOD m] := by
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
    have hu : (Units.mk0 ζ hζ0) ^ n = (Units.mk0 ζ hζ0) ^ n' := Units.ext (by simpa using hζn)
    rw [pow_eq_pow_iff_modEq, ← orderOf_units, Units.val_mk0, ← hζ.eq_orderOf] at hu
    exact hu
  have hγI : γ ∈ Ine (F := E) A := hγ.1
  have hord : orderOf (χ γ) ∣ m := orderOf_dvd_of_pow_eq_one (hχm γ hγI)
  rw [hn1, hn1', pow_eq_pow_iff_modEq]
  exact Nat.ModEq.of_dvd hord hmod

end GlobalTheory.TameTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumsEqPairingsTopChainLiftsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSums_eq_pairings_topChain_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → let C := toChainReal R F tupT hm hTop; let L := toLiftReal R F tupT hm hTop hinj; ∀ μ : D.what₂.Tup, (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP true μ ∧ ∀ x y, C.ipXP true μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P1 F.ψ1 (tupT μ)) x y)) ∧ (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP false μ ∧ ∀ x y, C.ipXP false μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P0 F.ψ0 (tupT μ)) x y)) ∧ ∀ i : Fin D.R.m, (let a := fun x => R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)); Submodule.span ℂ (Set.range a) = L.Amt μ i ∧ ∀ x y, L.ipA μ i (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i (tupT μ)) x y)) := by
  first | exact @GlobalTheory.TopNorm.classSums_topNorm | exact GlobalTheory.TopNorm.classSums_topNorm | (intros; apply GlobalTheory.TopNorm.classSums_topNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEquivariantRealPlace
section
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.ConjEquivRealSee


set_option maxHeartbeats 1000000 in
theorem conjMap_update_real_see : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ (v : (MP R).Vec) (w : (MP R).sm τ), (w : (MP R).H τ) = (MP R).rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) = rTr (D.sp.Y 0) (atTau R.θ (D.sp.Y 0) τ g) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v) := by
  intro _ _ _ _ D G _ _ Pl0 T A Ks _ _ _ R F X h t hιE _ _ hinf _ hsee c hc Φ hΦ hrep τ g hg v w hw
  classical
  obtain ⟨hfin, -, hreal, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h R.θ hinf hιE
  have ht : t ∈ GfC (Yc D 0) := hsee.fin
  obtain ⟨ha2, ha1, -⟩ := hreal τ g hg
  obtain ⟨-, Rm, -, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  have hint : ∀ (x : X.B.I.Ginf) (z : X.B.Hs), Φ (X.B.σs x z) = X.B.R (x, 1) (Φ z) := by
    obtain ⟨B, hB, rfl⟩ := hΦ
    intro x z
    have hb : B (X.B.σs x z) = X.B.R (x, 1) (B z) := DFunLike.congr_fun (hB x) z
    show X.B.Re (B (X.B.σs x z)) = X.B.R (x, 1) (X.B.Re (B z))
    rw [hb]
    obtain ⟨-, hT⟩ := X.B.Re_spec
    apply ext_inner_left ℂ
    intro u
    rw [← ContinuousLinearMap.adjoint_inner_left (X.B.R (x, 1)), hT, hT]
    congr 1
    funext k
    rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      ← Rm, ← ContinuousLinearMap.comp_apply (X.B.R (x, 1)), ← Rm]
    simp
  have hσ1 : ∀ v', X.B.σ v' 1 = 1 := fun v' => (X.ds v').2.2.1.1.1
  have hvec : GlobalTheory.ConjRowMult.vecC X (MP R) c (Function.update v τ w) = fun v' =>
      X.B.σ v' (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v')) (GlobalTheory.ConjRowMult.vecC X (MP R) c v v') := by
    rw [GlobalTheory.ConjRowMult.vecC_update]
    funext v'
    by_cases hv : v' = X.pl.symm τ
    · subst hv
      rw [Function.update_self, hw, hc τ g hg]
      unfold GlobalTheory.ConjRowMult.vecC
      rw [Equiv.piCongrLeft_apply_apply]
    · rw [Function.update_of_ne hv, ha1 v' hv,
        show uMat (1 : Formalism.REAL.UJ (X.B.I.ε v')) = 1 from rfl, hσ1]
      rfl
  have hsig : X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c (Function.update v τ w)) =
      X.B.σs ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1) (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c v)) := by
    rw [hvec, X.B.tens_spec.2.1]
  have ea : iotaX X h (atTau R.θ (D.sp.Y 0) τ g) = ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1, 1) :=
    Prod.ext rfl ha2
  have hcomm : iotaX X h t⁻¹ * iotaX X h (atTau R.θ (D.sp.Y 0) τ g) =
      iotaX X h (atTau R.θ (D.sp.Y 0) τ g) * iotaX X h t⁻¹ := by
    have h1 : (iotaX X h t).1 = 1 := (hfin t).1 ht
    erw [map_inv]
    refine Prod.ext ?_ ?_
    · simp [h1]
    · simp [ha2]
  obtain ⟨ψ, hψ⟩ := hrep v
  have hψ' := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ (iotaX X h (atTau R.θ (D.sp.Y 0) τ g))
  funext y
  show _ = GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v (y * atTau R.θ (D.sp.Y 0) τ g)
  erw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.conjMap_apply]
  rw [hsig, hint, ← ea,
    GlobalTheory.ConjRowMult.contRepL_spec X hψ', GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  simp only [map_mul]
  rw [mul_assoc, hcomm, mul_assoc]

end GlobalTheory.ConjEquivRealSee

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaLiftContinuousInvariantHasDerivAt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLiftDer

theorem hasDerivAt_integral_of_cocompact {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [Countable Γ] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K K' : ℝ → H → ℂ)
    (hK : ∀ t, Continuous (K t)) (hK' : Continuous fun p : ℝ × H => K' p.1 p.2)
    (hinv : ∀ γ ∈ Γ, ∀ t h, K t (γ * h) = K t h) (hinv' : ∀ γ ∈ Γ, ∀ t h, K' t (γ * h) = K' t h)
    (hd : ∀ t h, HasDerivAt (fun s => K s h) (K' t h) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ h in 𝓕, K t h ∂μ) (∫ h in 𝓕, K' t₀ h ∂μ) t₀ := by
  obtain ⟨N, hN, hN₀⟩ := exists_compact_mem_nhds t₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hK'.continuousOn
  have hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ :=
    GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const
      (fun _ _ _ => rfl)
  have hconst' : Integrable (fun _ : H => M) (μ.restrict 𝓕) := by
    have h := hconst.re
    change Integrable (fun _ : H => Complex.re (M : ℂ)) (μ.restrict 𝓕) at h
    simpa only [Complex.ofReal_re] using h
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => M) hN₀
    (Filter.Eventually.of_forall fun t => (hK t).aestronglyMeasurable)
    (GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ (hK t₀) (fun γ hγ h => hinv γ hγ t₀ h))
    (hK'.comp (Continuous.prodMk_right t₀)).aestronglyMeasurable ?_ hconst'
    (Filter.Eventually.of_forall fun h t _ => hd t h)).2
  refine Filter.Eventually.of_forall fun h t ht => ?_
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
  rw [hinv' γ hγ]
  exact hM (t, c) ⟨ht, hc⟩

theorem kernel_continuous_invariant {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    (L : X →ₗ[ℂ] (WO S T → ℂ)) (hL : ∀ x, IsThetaFunO ψ S T (L x)) {F : GA D S → X} (hF : Continuous F)
    (hinv : ∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) :
    (Continuous fun p : GA D T × GA D S => thetaKO om p.2 p.1 (L (F p.2))) ∧
      (∀ γ ∈ GQ S, ∀ g h, thetaKO om (γ * h) g (L (F (γ * h))) = thetaKO om h g (L (F h))) ∧
      ∀ γ ∈ GQ T, ∀ g h, thetaKO om h (γ * g) (L (F h)) = thetaKO om h g (L (F h)) := by
  refine ⟨?_, fun γ hγ g h => ?_, fun γ hγ g h => ?_⟩
  · let b := Module.finBasis ℂ X
    have e : (fun p : GA D T × GA D S => thetaKO om p.2 p.1 (L (F p.2))) =
        fun p => ∑ k, b.coord k (F p.2) * om (p.2, p.1) (L (b k)) 0 := by
      funext p
      conv_lhs => rw [← b.sum_repr (F p.2)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
    rw [e]
    refine continuous_finsetSum _ fun k _ => Continuous.mul ?_ ?_
    · exact ((b.coord k).continuous_of_finiteDimensional.comp hF).comp continuous_snd
    · exact (hom.om_cont _ (hL (b k)) 0).comp continuous_swap
  · have := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hom _ (hL (F h))).2 γ hγ 1 (one_mem _) h g
    rw [one_mul] at this
    rw [hinv γ hγ, this]
  · have := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hom _ (hL (F h))).2 1 (one_mem _) γ hγ h g
    rwa [one_mul] at this

theorem lift_continuous_invariant_hasDerivAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → (Continuous (lift om ν 𝓕 fun h => L (F h)) ∧ ∀ γ ∈ GQ T, ∀ g, lift om ν 𝓕 (fun h => L (F h)) (γ * g) = lift om ν 𝓕 (fun h => L (F h)) g) ∧ ∀ τ, ∀ Y ∈ lieAt T τ, ∃ L' : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L' x)) ∧ (∀ x h g, HasDerivAt (fun t : ℝ => thetaKO om h (g * oneP θ T τ Y t) (L x)) (thetaKO om h g (L' x)) 0) ∧ ∀ g, HasDerivAt (fun t : ℝ => lift om ν 𝓕 (fun h => L (F h)) (g * oneP θ T τ Y t)) (lift om ν 𝓕 (fun h => L' (F h)) g) 0 := by
  intro D ψ S T χS χT om hom θ hθ hpos X _ _ _ L hL F hF hinv ν 𝓕 hν h𝓕
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  obtain ⟨hc, hiS, hiT⟩ := kernel_continuous_invariant hom L hL hF hinv
  refine ⟨⟨?_, fun γ hγ g => ?_⟩, fun τ Y hY => ?_⟩
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun g h => thetaKO om h g (L (F h))) hc hiS
  · simp only [GlobalTheory.DefLift.lift, hiT γ hγ]
  · obtain ⟨Gn, hGn⟩ := _root_.GlobalTheory.DefLift.Gen.exists_generator D ψ S T χS χT om hom θ hθ τ Y hY
    have hL' : ∀ x, IsThetaFunO ψ S T ((Gn ∘ₗ L) x) := fun x => (hGn _ (hL x)).1
    have hd : ∀ x h g, HasDerivAt (fun t : ℝ => thetaKO om h (g * oneP θ T τ Y t) (L x))
        (thetaKO om h g ((Gn ∘ₗ L) x)) 0 := by
      intro x h g
      have := (hGn _ (hL x)).2.2.2 (h, g) 0
      simp only [Prod.mk_mul_mk, mul_one] at this
      exact this
    refine ⟨Gn ∘ₗ L, hL', hd, fun g => ?_⟩
    obtain ⟨hc', hiS', -⟩ := kernel_continuous_invariant hom (Gn ∘ₗ L) hL' hF hinv
    have hp : Continuous fun t : ℝ => g * oneP θ T τ Y t :=
      continuous_const.mul (GlobalTheory.Mem.Lift.continuous_oneP hθ hY)
    have key := hasDerivAt_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun t h => thetaKO om h (g * oneP θ T τ Y t) (L (F h)))
      (fun t h => thetaKO om h (g * oneP θ T τ Y t) ((Gn ∘ₗ L) (F h)))
      (fun t => hc.comp (Continuous.prodMk_right (g * oneP θ T τ Y t)))
      (hc'.comp (hp.prodMap continuous_id))
      (fun γ hγ t h => hiS γ hγ _ h) (fun γ hγ t h => hiS' γ hγ _ h)
      (fun t h => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hY (φ := fun g => thetaKO om h g (L (F h)))
        (φ' := fun g => thetaKO om h g ((Gn ∘ₗ L) (F h))) (hd (F h) h) g t) 0
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
    exact key

end GlobalTheory.DefLiftDer
end

