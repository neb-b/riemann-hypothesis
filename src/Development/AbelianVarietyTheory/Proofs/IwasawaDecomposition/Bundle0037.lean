module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusInvMulMemInertia
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory

theorem frob_inv_mul_mem_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ'⁻¹ * τ ∈ Ine (F := E) A := by
  intro E Ω _ _ _ _ v A hA τ τ' hτ hτ'
  obtain ⟨hτD, hτF⟩ := hτ
  obtain ⟨hτ'D, hτ'F⟩ := hτ'

  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ v.asIdeal) := inferInstance
  letI : Fintype (𝓞 E ⧸ v.asIdeal) := Fintype.ofFinite _
  set p := ringChar (𝓞 E ⧸ v.asIdeal) with hpdef
  haveI : CharP (𝓞 E ⧸ v.asIdeal) p := ringChar.charP _
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (𝓞 E ⧸ v.asIdeal) p
  have hq : normV v = p ^ (n : ℕ) := by
    simp only [normV, Nat.card_eq_fintype_card, hcard]

  have hpv : ((p : 𝓞 E)) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  have hpA : A.valuation (p : Ω) < 1 := by
    have := (hA (p : 𝓞 E)).mpr hpv
    simpa using this

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    simpa using hpA
  haveI : CharP (IsLocalRing.ResidueField A) p := by
    have h := CharP.ringChar_of_prime_eq_zero (R := IsLocalRing.ResidueField A) hp hpk
    rw [← h]; exact ringChar.charP _
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : ExpChar (IsLocalRing.ResidueField A) p := ExpChar.prime hp
  refine ⟨(Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hτ'D) hτD, fun x hx => ?_⟩
  have hxA : x ∈ A := A.valuation_le_one_iff x |>.mp hx
  set z := (τ'⁻¹ : G E Ω) (τ x) with hz
  have hzA : z ∈ A := by
    rw [hz, apply_mem_iff_of_mem_Dec ((Dec (F := E) A).inv_mem hτ'D), apply_mem_iff_of_mem_Dec hτD]
    exact hxA
  have hτ'z : τ' z = τ x := mul_inv_apply (τ x)
  have h1 := hτ'F z ((A.valuation_le_one_iff z).mpr hzA)
  rw [hτ'z] at h1
  have h2 := hτF x hx
  have h3 : A.valuation (z ^ normV v - x ^ normV v) < 1 := by
    have e : z ^ normV v - x ^ normV v = (τ x - x ^ normV v) - (τ x - z ^ normV v) := by ring
    rw [e]; exact Valuation.map_sub_lt _ h2 h1

  have hres : IsLocalRing.residue A ⟨z, hzA⟩ ^ (p ^ (n : ℕ)) = IsLocalRing.residue A ⟨x, hxA⟩ ^ (p ^ (n : ℕ)) := by
    rw [← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    rw [← hq]
    simpa using h3
  have hinj := iterateFrobenius_inj (IsLocalRing.ResidueField A) p (n : ℕ)
  have heq : IsLocalRing.residue A ⟨z, hzA⟩ = IsLocalRing.residue A ⟨x, hxA⟩ := by
    apply hinj
    rw [iterateFrobenius_def, iterateFrobenius_def]
    exact hres
  have hzx : (⟨z, hzA⟩ - ⟨x, hxA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, heq, sub_self]
  have := (ValuationSubring.valuation_lt_one_iff A _).mp hzx
  have e2 : (τ'⁻¹ * τ) x = z := rfl
  rw [e2]
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRatioPiCongrTameUnit
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.TameRatio

theorem ratio_cong : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ u : 𝓞 E, u ∉ v.asIdeal → ∀ π t : Ω, π ≠ 0 →
    t ^ (normV v - 1) = algebraMap E Ω (u : E) → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ π = π → τ' (π * t) = π * t →
    A.valuation ((τ'⁻¹ * τ) π / π - algebraMap E Ω (u : E)) < 1 := by
  intro E Ω _ _ _ _ v A hA u hu π t hπ ht τ τ' _hτ hτ' h1 h2
  have hq1 : 1 < normV v := by
    unfold normV
    have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    have : Finite (𝓞 E ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    exact Finite.one_lt_card
  set U : Ω := algebraMap E Ω (u : E) with hUdef
  have hint : IsIntegral ℤ U := (RingOfIntegers.isIntegral_coe u).map ((algebraMap E Ω).toIntAlgHom)
  have hUle : A.valuation U ≤ 1 :=
    (Valuation.valuationSubring.integers A.valuation).isIntegral_iff_v_le_one.mp (IsIntegral.tower_top hint)
  have hU1 : A.valuation U = 1 := le_antisymm hUle (not_lt.mp fun h => hu ((hA u).mp h))
  set s : Ω := τ'⁻¹ t with hsdef
  have hs : τ' s = t := by
    show τ' (τ'⁻¹ t) = t
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hsn : s ^ (normV v - 1) = U := by
    show (τ'⁻¹ t) ^ (normV v - 1) = U
    rw [← map_pow, ht, hUdef, AlgEquiv.commutes]
  have hvs : A.valuation s = 1 := by
    have h : A.valuation s ^ (normV v - 1) = 1 := by rw [← map_pow, hsn, hU1]
    exact (pow_eq_one_iff.mp h).resolve_right (by omega)
  have hs0 : s ≠ 0 := by
    intro h; rw [h, map_zero] at hvs; exact zero_ne_one hvs
  have hF : A.valuation (t - s ^ normV v) < 1 := by
    have := hτ'.2 s hvs.le
    rwa [hs] at this
  have hinv : τ'⁻¹ π * s = π * t := by
    rw [hsdef, ← map_mul]
    calc τ'⁻¹ (π * t) = τ'⁻¹ (τ' (π * t)) := by rw [h2]
      _ = π * t := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hrat : (τ'⁻¹ * τ) π = τ'⁻¹ π := by rw [AlgEquiv.mul_apply, h1]
  have hqs : s ^ normV v = U * s := by
    rw [← hsn, ← pow_succ]; congr 1; omega
  have key : (τ'⁻¹ * τ) π / π - U = (t - s ^ normV v) / s := by
    rw [hrat, hqs]
    have e : τ'⁻¹ π = π * t / s := by rw [eq_div_iff hs0, hinv]
    rw [e]
    field_simp
  rw [key, map_div₀, hvs, div_one]
  exact hF

end GlobalTheory.TameRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtLineDH
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift

theorem hasDerivAt_line_dH {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) {ρ : V → B →L[ℂ] B} (h0 : ∀ x, om x x = 0)
    (h : IsHeis (fun x y => om x y) ρ) (v : V) {f : B} (hf : Sm ρ f) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ρ (t • v) f) (ρ (s • v) (dH ρ v f)) s := by
  have e : (fun t : ℝ => ρ (t • v) f) = fun t : ℝ => ρ (s • v) (ρ ((t - s) • v) f) := by
    funext t
    rw [h.2.1, ← add_smul]
    simp [h0]
  have h1 : HasDerivAt (fun t : ℝ => ρ ((t - s) • v) f) (dH ρ v f) s := by
    have h2 : HasDerivAt (fun t : ℝ => ρ (t • v) f) (dH ρ v f) (s - s) := by
      rw [sub_self]; exact hasDerivAt_dH v hf
    exact h2.comp_sub_const s s
  rw [e]
  exact ((ρ (s • v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1

theorem dH_integral : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) (F : Y → B), (∀ y, Sm ρ (F y)) → Integrable F ν → Sm ρ (∫ y, F y ∂ν) → ∀ v, Integrable (fun y => dH ρ v (F y)) ν → dH ρ v (∫ y, F y ∂ν) = ∫ y, dH ρ v (F y) ∂ν := by
  intro V _ _ B _ _ _ om ρ h0 h Y _ ν F hF hFi hS v hd
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (𝕜 := ℝ) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun (t : ℝ) y => ρ (t • v) (F y)) (F' := fun (t : ℝ) y => ρ (t • v) (dH ρ v (F y)))
    (bound := fun y => ‖dH ρ v (F y)‖) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => ((ρ (t • v)).integrable_comp hFi).aestronglyMeasurable)
    ((ρ _).integrable_comp hFi) ((ρ _).integrable_comp hd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y t _ => (h.2.2.1 _ _).le) hd.norm
    (Filter.Eventually.of_forall fun y t _ => hasDerivAt_line_dH om h0 h v (hF y) t)).2
  simp only [zero_smul, h.1, ContinuousLinearMap.integral_comp_comm _ hFi] at key
  exact (hasDerivAt_dH v hS).unique key

end GlobalTheory.Mem.Lift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaPowResidueCardSubOneApplyOfPowMem
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory

theorem eq_one_of_pow_eq_one_of_val_sub_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ}
    (hn : A.valuation (n : Ω) = 1) {ξ : Ω} (hξ : ξ ^ n = 1) (h1 : A.valuation (ξ - 1) < 1) : ξ = 1 := by
  by_contra hne
  have hξA : A.valuation ξ ≤ 1 := by
    have : ξ = (ξ - 1) + 1 := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le h1.le (by simp))
  have hS : (∑ k ∈ Finset.range n, ξ ^ k) = 0 := by
    have h := geom_sum_mul ξ n
    rw [hξ, sub_self] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  have hsum : (n : Ω) = ∑ k ∈ Finset.range n, (1 - ξ ^ k) := by
    rw [Finset.sum_sub_distrib, hS]; simp
  have hlt : A.valuation (n : Ω) < 1 := by
    rw [hsum]
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
    have e : 1 - ξ ^ k = -((∑ j ∈ Finset.range k, ξ ^ j) * (ξ - 1)) := by
      rw [geom_sum_mul]; ring
    rw [e, Valuation.map_neg, Valuation.map_mul]
    have hs : A.valuation (∑ j ∈ Finset.range k, ξ ^ j) ≤ 1 :=
      Valuation.map_sum_le _ fun j _ => by rw [Valuation.map_pow]; exact pow_le_one' hξA j
    calc A.valuation (∑ j ∈ Finset.range k, ξ ^ j) * A.valuation (ξ - 1)
        ≤ 1 * A.valuation (ξ - 1) := by gcongr
      _ < 1 := by rw [one_mul]; exact h1
  rw [hn] at hlt
  exact lt_irrefl _ hlt

theorem val_eq_one_of_pow_eq_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ} (hn0 : n ≠ 0)
    {ζ : Ω} (hζ : ζ ^ n = 1) : A.valuation ζ = 1 := by
  have h : A.valuation ζ ^ n = 1 := by rw [← Valuation.map_pow, hζ, Valuation.map_one]
  exact valuation_eq_one_of_pow_eq_one A hn0 hζ

theorem ine_pow_normV_sub_one_apply_of_pow_mem : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (w : E) (π : Ω), π ^ (normV v - 1) = algebraMap E Ω w →
    ∀ ρ ∈ Ine (F := E) A, (ρ ^ (normV v - 1)) π = π := by
  intro E Ω _ _ _ _ v A hA w π hπ ρ hρ
  set n := normV v - 1 with hn_def
  rcases eq_or_ne n 0 with hn0 | hn0
  · rw [hn0, pow_zero]; rfl
  rcases eq_or_ne π 0 with hπ0 | hπ0
  · rw [hπ0, map_zero]

  have hq1 : 1 ≤ normV v := by omega
  have hqv : ((normV v : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    show ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : 𝓞 E ⧸ v.asIdeal) = 0
    rcases finite_or_infinite (𝓞 E ⧸ v.asIdeal) with hf | hf
    · haveI := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal)
      rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
    · rw [Nat.card_eq_zero_of_infinite]; simp
  have hqA : A.valuation ((normV v : ℕ) : Ω) < 1 := by
    have := (hA _).mpr hqv
    simpa using this
  have hnA : A.valuation (n : Ω) = 1 := by
    rw [hn_def, Nat.cast_sub hq1, Nat.cast_one, Valuation.map_sub_swap]
    exact Valuation.map_one_sub_of_lt _ hqA

  have hρπ : (ρ π) ^ n = π ^ n := by
    rw [← map_pow, hπ]; exact ρ.commutes w
  set ζ := ρ π * π⁻¹ with hζ_def
  have hζn : ζ ^ n = 1 := by
    rw [hζ_def, mul_pow, hρπ, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hπ0)]
  have hρπ' : ρ π = ζ * π := by rw [hζ_def, mul_assoc, inv_mul_cancel₀ hπ0, mul_one]
  have hζ1 : A.valuation ζ = 1 := valuation_eq_one_of_pow_eq_one A hn0 hζn
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, zero_pow hn0] at hζn; exact zero_ne_one hζn
  have hρζn : (ρ ζ) ^ n = 1 := by rw [← map_pow, hζn, map_one]
  have hclose : A.valuation (ρ ζ - ζ) < 1 := hρ.2 ζ hζ1.le
  have hξ : ρ ζ * ζ⁻¹ = 1 := by
    refine eq_one_of_pow_eq_one_of_val_sub_lt A hnA ?_ ?_
    · rw [mul_pow, hρζn, inv_pow, hζn, inv_one, one_mul]
    · have e : ρ ζ * ζ⁻¹ - 1 = (ρ ζ - ζ) * ζ⁻¹ := by field_simp
      rw [e, Valuation.map_mul, map_inv₀, hζ1, inv_one, mul_one]; exact hclose
  have hρζ : ρ ζ = ζ := by
    have := congrArg (· * ζ) hξ
    simpa [mul_assoc, inv_mul_cancel₀ hζ0] using this
  have key : ∀ k : ℕ, (ρ ^ k) π = ζ ^ k * π := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hρζ, hρπ', pow_succ]; ring
  rw [key, hζn, one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
section
noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace GlobalTheory.AlgWtHW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def upt (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) : (L →+* ℂ) × Fin n × Fin n → ℂ :=
  fun p => X p.1 p.2.1 p.2.2

def IsUPt (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ σ, X σ * (X (ComplexEmbedding.conjugate σ))ᵀ = 1

def ratPt (γ₀ : Matrix (Fin n) (Fin n) L) : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ :=
  fun σ => γ₀.map σ

def evM {ι : Type} (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (x : (L →+* ℂ) × Fin n × Fin n → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => MvPolynomial.eval x (P i j)

def Agrees (a : AlgWt L n) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) : Prop :=
  ∀ (γ : GQ L n) (γ₀ : GL (Fin n) L),
    (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
    LinearMap.toMatrix b b (a.ρ γ) =
      fun i j => MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix _ _ L) p.2.1 p.2.2)) (P i j)

structure IsPolyRep {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) : Prop where
  one : Φ 1 = 1
  mul : ∀ A B, Φ (A * B) = Φ A * Φ B
  poly : ∀ i j, ∃ Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, ∀ B : GL (Fin n) ℂ,
    Φ B i j = MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2)) Q

def IsBEig {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (v : ι → ℂ) (lam : Fin n → ℤ) : Prop :=
  v ≠ 0 ∧ ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Φ B *ᵥ v = (∏ i, (B.val i i) ^ (lam i)) • v

def IsWtVec {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ : Fin n → ℤ) (w : ι → ℂ) : Prop :=
  ∀ D : GL (Fin n) ℂ, D.val.IsDiag → Φ D *ᵥ w = (∏ i, (D.val i i) ^ (μ i)) • w

def IsWt {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ : Fin n → ℤ) : Prop :=
  ∃ w : ι → ℂ, w ≠ 0 ∧ IsWtVec Φ μ w

def DomLE (μ lam : Fin n → ℤ) : Prop :=
  ∑ i, μ i = ∑ i, lam i ∧ ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), μ i ≤
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), lam i

def Sle {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (lam : Fin n → ℤ) : Submodule ℂ (ι → ℂ) :=
  Submodule.span ℂ {w | ∃ ν, DomLE ν lam ∧ IsWtVec Φ ν w}

end GlobalTheory.AlgWtHW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.NormCompat

def locUnit (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* Ideles F :=
  (localIdele F v).comp (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom)

theorem locUnit_apply (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    locUnit F v a = localIdele F v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) := rfl

end GlobalTheory.NormCompat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyAndNormOfPowEqUniformizer
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.TameEis

open Polynomial

theorem two_le_normV (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    2 ≤ normV v := by
  have h : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h' => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h')
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h' => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h')
  omega

theorem minpoly_and_norm_of_pow_eq_uniformizer : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E)) (ϖ : 𝓞 E),
    ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
      minpoly E π = Polynomial.X ^ (normV v - 1) - Polynomial.C (ϖ : E) ∧
      Algebra.norm E (IntermediateField.AdjoinSimple.gen E π) = (-1) ^ normV v * (ϖ : E) := by
  intro E Ω _ _ _ _ v ϖ hmem hnot π hπ
  have hq := two_le_normV E v
  set n := normV v - 1 with hn
  have hn1 : 0 < n := by omega
  have hmon : (X ^ n - C ϖ : (𝓞 E)[X]).Monic := monic_X_pow_sub_C ϖ hn1.ne'
  have hdeg : (X ^ n - C ϖ : (𝓞 E)[X]).natDegree = n := natDegree_X_pow_sub_C _
  have hEis : (X ^ n - C ϖ : (𝓞 E)[X]).IsEisensteinAt v.asIdeal := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro m hm
      rw [hdeg] at hm
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hm.ne]
      by_cases h0 : m = 0
      · subst h0; simpa using v.asIdeal.neg_mem_iff.2 hmem
      · simp [h0]
    · rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hn1.ne, if_pos rfl, zero_sub]
      rwa [Ideal.neg_mem_iff]
  have hirr : Irreducible (X ^ n - C ϖ : (𝓞 E)[X]) :=
    hEis.irreducible v.isPrime hmon.isPrimitive (by rw [hdeg]; exact hn1)
  have hmap : (X ^ n - C ϖ : (𝓞 E)[X]).map (algebraMap (𝓞 E) E) = X ^ n - C (ϖ : E) := by
    simp [Polynomial.map_sub]
  have hirrE : Irreducible (X ^ n - C (ϖ : E)) := by
    rw [← hmap]; exact (hmon.irreducible_iff_irreducible_map_fraction_map (K := E)).1 hirr
  have hmonE : (X ^ n - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hn1.ne'
  have hroot : aeval π (X ^ n - C (ϖ : E)) = 0 := by
    simp [hπ]
  have hmin : minpoly E π = X ^ n - C (ϖ : E) :=
    (minpoly.eq_of_irreducible_of_monic hirrE hroot hmonE).symm
  refine ⟨hmin, ?_⟩
  have hx : IsIntegral E π := ⟨_, hmonE, hroot⟩
  rw [← IntermediateField.adjoin.powerBasis_gen hx,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hx,
    IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim, hmin, natDegree_X_pow_sub_C _]
  rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hn1.ne, if_pos rfl, zero_sub]
  have : normV v = n + 1 := by omega
  rw [this, pow_succ]; ring

end GlobalTheory.TameEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceEqOfContEmbCompEq
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.HeckeGal.norm_lt_one_of_contEmb {E : Type} [Field E] [NumberField E]
    {l : ℕ} [Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 E)) (j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (hj : Continuous j)
    (a : 𝓞 E) (ha : a ∈ v.asIdeal) :
    ‖j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a))‖ < 1 := by
  set x := algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a) with hx
  have hx1 : ‖x‖ < 1 := by
    rw [hx, Valued.toNormedField.norm_lt_one_iff]
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) v a
    erw [h]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact ha
  have hlim : Filter.Tendsto (fun n : ℕ => j x ^ n) Filter.atTop (nhds 0) := by
    have h0 := (hj.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx1)
    simpa [Function.comp_def, map_pow] using h0
  by_contra hge
  push_neg at hge
  have hball : ∀ᶠ n : ℕ in Filter.atTop, ‖j x ^ n‖ < 1 :=
    (tendsto_norm_zero.comp hlim).eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨n, hn⟩ := hball.exists
  rw [norm_pow] at hn
  exact absurd hn (not_lt.mpr (one_le_pow₀ hge))


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.HeckeGal.place_eq_of_contEmb_comp_eq :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (v v' : HeightOneSpectrum (𝓞 E))
      (j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (j' : v'.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l),
      Continuous j → Continuous j' →
      j.comp (algebraMap E (v.adicCompletion E)) = j'.comp (algebraMap E (v'.adicCompletion E)) →
      v = v' := by
  intro E _ _ l _ v v' j j' hj hj' hcomp
  by_contra hne
  have hideal : v.asIdeal ≠ v'.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have htop : v.asIdeal ⊔ v'.asIdeal = ⊤ := v.isMaximal.coprime_of_ne v'.isMaximal hideal
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ _)
  have hna := _root_.GlobalTheory.HeckeGal.norm_lt_one_of_contEmb v j hj a ha
  have hnb := _root_.GlobalTheory.HeckeGal.norm_lt_one_of_contEmb v' j' hj' b hb
  have hb' : j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E b)) =
      j' (algebraMap E (v'.adicCompletion E) (algebraMap (𝓞 E) E b)) :=
    RingHom.congr_fun hcomp _
  rw [← hb'] at hnb
  have hsum : j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a)) +
      j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E b)) = 1 := by
    rw [← map_add (f := _), ← map_add (f := _), ← map_add (f := _), hab, map_one, map_one, map_one]
  have hle := IsUltrametricDist.norm_add_le_max
    (j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a)))
    (j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E b)))
  rw [hsum, norm_one] at hle
  exact absurd (hle.trans_lt (max_lt hna hnb)) (lt_irrefl 1)

end GlobalTheory.HeckeGal
end

