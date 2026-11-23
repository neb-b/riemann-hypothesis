module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SplitPlace
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem norm_not_mem_sq {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (hd : u.asIdeal.inertiaDeg ℤ = 1) (he : u.asIdeal.ramificationIdx ℤ = 1) :
    ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 := by
  classical
  have hprime : Nat.Prime (Ideal.absNorm u.asIdeal) :=
    ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 u).2 hd
  haveI : Fact (Nat.Prime (Ideal.absNorm u.asIdeal)) := ⟨hprime⟩
  have hmemZ : ((Ideal.absNorm u.asIdeal : ℕ) : ℤ) ∈ u.asIdeal.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap]
    simpa using Ideal.absNorm_mem u.asIdeal
  have hspan : u.asIdeal.under ℤ = Ideal.span {((Ideal.absNorm u.asIdeal : ℕ) : ℤ)} :=
    ((Int.ideal_span_isMaximal_of_prime (Ideal.absNorm u.asIdeal)).eq_of_le
      Ideal.IsPrime.ne_top' ((Ideal.span_singleton_le_iff_mem _).2 hmemZ)).symm
  have hp0 : u.asIdeal.under ℤ ≠ ⊥ := by
    rw [hspan, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hprime.ne_zero
  have he' : (u.asIdeal.under ℤ).ramificationIdx' u.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (u.asIdeal.under ℤ) u.asIdeal hp0]
    exact he
  have hmap : (u.asIdeal.under ℤ).map (algebraMap ℤ (𝓞 F)) ≤ u.asIdeal := Ideal.map_comap_le
  intro hmem
  refine (Ideal.ramificationIdx'_ne_one_iff hmap).2 ?_ he'
  rw [hspan, Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
  simpa using hmem

private theorem dec_le {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {N : Subgroup (G F Ω)} (hNo : IsOpen (N : Set (G F Ω))) {B : ValuationSubring Ω}
    {u : HeightOneSpectrum (𝓞 F)} (hB : IsPlaceOver B u) (hI : Ine (F := F) B ≤ N) {σ : G F Ω}
    (hσ : IsFrob B (normV u) σ) (hσN : σ ∈ N) : Dec (F := F) B ≤ N := by
  intro d hd
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω B u hB ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((N.subgroupOf (Dec (F := F) B) : Subgroup (Dec (F := F) B)) : Set (Dec (F := F) B)) :=
    (N.isClosed_of_isOpen hNo).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) B) ⊔ (Ine (F := F) B).subgroupOf (Dec (F := F) B))
    (sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 hσN))
      (fun x hx => Subgroup.mem_subgroupOf.2 (hI (Subgroup.mem_subgroupOf.1 hx)))) hc
  rw [h] at h2
  exact Subgroup.mem_subgroupOf.1 (h2 (Subgroup.mem_top (⟨d, hd⟩ : Dec (F := F) B)))

theorem splitPlace : SplitPlace := by
  intro F Ω _ _ _ _ _ U hU T hT
  obtain ⟨N, hNn, hNo, -, hNU⟩ := _root_.GlobalTheory.OpenNormal.exists_open_normal_le Ω F U hU
  have hc : GlobalTheory.TwSys.Cheb :=
    GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 GlobalTheory.Published.chebotarevDegreeOne'
  unfold GlobalTheory.TwSys.Cheb at hc
  obtain ⟨v, hvA, hd, he, B, hB, hIB, σ, hσ, hσN⟩ := hc F Ω N hNo hNn 1 hT.toFinset
  have hvT : v ∉ T := fun h => hvA (hT.mem_toFinset.2 h)
  have hσN' : σ ∈ N := by simpa using hσN
  have hdec := dec_le hNo hB hIB hσ hσN'
  have hnorm : normV v = Ideal.absNorm v.asIdeal := by
    simp [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine ⟨v, hvT, ?_, ?_, ?_, ?_⟩
  · rw [hnorm]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd
  · rw [hnorm]
    exact Ideal.absNorm_mem _
  · rw [hnorm]
    exact norm_not_mem_sq v hd he
  · intro A hA ρ hρ
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver hB hA
    apply hNU
    have h1 : τ⁻¹ * ρ * τ ∈ Dec (F := F) B := by
      rw [mem_Dec] at hρ ⊢
      rw [← hτ] at hρ
      rw [mul_smul, mul_smul, hρ, ← mul_smul, inv_mul_cancel, one_smul]
    have h2 := hNn.conj_mem _ (hdec h1) τ
    simpa [mul_assoc] using h2

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SqrtFix
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.sqrtFix :
    SqrtFix := by
  intro F Ω _ _ _ _ A x a hx
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hsq : ∀ g : G F Ω, g x = x ∨ g x = -x := by
    intro g
    have hgx : (g x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_intCast]
    have h0 : (g x - x) * (g x + x) = 0 := by linear_combination hgx
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hint : ∀ k : ℤ, A.valuation (k : Ω) ≤ 1 := fun k => by
    exact_mod_cast A.valuation_le_one (k : A)
  refine ⟨?_, ?_⟩
  · intro t _ hvt hdiv g hg
    rcases hsq g with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hdiv
      have hk' : (a : Ω) - 1 = 8 * (t : Ω) * (k : Ω) := by
        have hc := congrArg (fun z : ℤ => (z : Ω)) hk
        push_cast at hc
        linear_combination hc
      set y : Ω := (x - 1) / 2 with hy
      set y' : Ω := (-x - 1) / 2 with hy'
      have hgy : g y = y' := by
        rw [hy, hy', map_div₀, map_sub, map_one, map_ofNat, h]
      have hsum : y + y' = -1 := by
        rw [hy, hy']
        ring
      have hprod : y * y' = ((-2 * k : ℤ) : Ω) * (t : Ω) := by
        rw [hy, hy']
        push_cast
        linear_combination (-1 / 4 : Ω) * hx - (1 / 4 : Ω) * hk'
      have hvp : A.valuation (y * y') < 1 := by
        rw [hprod, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint _)) hvt
      have hvs : A.valuation (y + y') = 1 := by
        rw [hsum, Valuation.map_neg, Valuation.map_one]
      have hiff := valuation_apply_lt_one_iff hg y
      rw [hgy] at hiff
      by_cases hyl : A.valuation y < 1
      · have hs := Valuation.map_add_lt A.valuation hyl (hiff.2 hyl)
        rw [hvs] at hs
        exact lt_irrefl _ hs
      · have hyl' : ¬ A.valuation y' < 1 := fun h' => hyl (hiff.1 h')
        push_neg at hyl hyl'
        have hge : 1 ≤ A.valuation (y * y') := by
          rw [map_mul]
          exact one_le_mul hyl hyl'
        exact absurd hvp (not_lt.2 hge)
  · intro h2a τ hτ
    obtain ⟨-, hI⟩ : τ ∈ ValuationSubring.decompositionSubgroup F A ∧
        ∀ (y : Ω), A.valuation y ≤ 1 → A.valuation (τ y - y) < 1 := hτ
    rcases hsq τ with h | h
    · exact h
    · exfalso
      have hv2 : A.valuation (2 : Ω) ≤ 1 := by simpa using hint 2
      have hva : A.valuation (a : Ω) ≤ 1 := hint a
      have e2a : A.valuation (2 : Ω) * A.valuation (a : Ω) = 1 := by
        rw [← map_mul]
        push_cast at h2a
        exact h2a
      have hv2' : A.valuation (2 : Ω) = 1 :=
        le_antisymm hv2 (e2a ▸ mul_le_of_le_one_right' hva)
      have hva' : A.valuation (a : Ω) = 1 :=
        le_antisymm hva (e2a ▸ mul_le_of_le_one_left' hv2)
      have hvx2 : A.valuation x ^ 2 = 1 := by
        rw [← Valuation.map_pow, hx, hva']
      have hvx : A.valuation x = 1 := by
        rcases lt_trichotomy (A.valuation x) 1 with hl | he | hg
        · exact absurd hvx2 (ne_of_lt (pow_lt_one' hl two_ne_zero))
        · exact he
        · exact absurd hvx2 (ne_of_gt (one_lt_pow' hg two_ne_zero))
      have key := hI x hvx.le
      rw [h, show -x - x = -(2 * x) by ring, Valuation.map_neg, map_mul, hv2', hvx, one_mul] at key
      exact lt_irrefl _ key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def QuadDisj : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (T : Set (HeightOneSpectrum (𝓞 F)))
    (N : Subgroup (G F Ω)), (∀ u ∉ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Ine (F := F) A ≤ N) →
    ∀ Q : QCM F Ω, RamOff T Q → GlobalTheory.AboveL.SolvDisj ↥Q.K N

def AllUnr : Prop :=
  ∀ (Y Ω : Type) [Field Y] [NumberField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω] (T : Set (HeightOneSpectrum (𝓞 Y)))
    (Q : QCM Y Ω), Step1 T Q → ∀ w : HeightOneSpectrum (𝓞 ↥Q.K),
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield ↥Q.K)) w.asIdeal

def Double : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (T : Set (HeightOneSpectrum (𝓞 E))) (Q : QCM E Ω), Step0 T Q → ∀ t ∈ T,
    ∃ w₁ w₂ : HeightOneSpectrum (𝓞 ↥Q.K), w₁.under (𝓞 E) = t ∧ w₂.under (𝓞 E) = t ∧ GlobalTheory.Cong.Apart w₁ w₂

def ApartUp : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M],
    (∀ w₁ w₂ : HeightOneSpectrum (𝓞 M), GlobalTheory.Cong.Apart (w₁.under (𝓞 K)) (w₂.under (𝓞 K)) → GlobalTheory.Cong.Apart w₁ w₂) ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v

def ThreeApart : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (T₁ : Set (HeightOneSpectrum (𝓞 E))) (Q₁ : QCM E Ω), Step0 T₁ Q₁ →
    ∀ (T₂ : Set (HeightOneSpectrum (𝓞 ↥Q₁.K))) (Q₂ : QCM ↥Q₁.K Ω), Step0 T₂ Q₂ → ∀ t ∈ T₁,
    (∀ w : HeightOneSpectrum (𝓞 ↥Q₁.K), w.under (𝓞 E) = t → w ∈ T₂) →
    ∀ (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra ↥Q₂.K M],
    ∃ w : Fin 3 → HeightOneSpectrum (𝓞 M), (∀ i, (((w i).under (𝓞 ↥Q₂.K)).under (𝓞 ↥Q₁.K)).under (𝓞 E) = t) ∧
      ∀ i j, i ≠ j → GlobalTheory.Cong.Apart (w i) (w j)

def SatSplit : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra K M]
    [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)), IsPlaceOver A v → IsPlaceOver A w →
    (∀ g ∈ Dec (F := K) A, Fixes M g) → ∀ (a : ℕ) (π : CuspSub K a) (P : CuspSub M a),
    UpperTheory.CBC.SplitLift (UpperTheory.CBC.Cusp.cx π) (UpperTheory.CBC.Cusp.cx P) → ∀ B, (CG.mk π).HasSat v B → (CG.mk P).HasSat w B

theorem threeApart_of (h1 : Double) (h2 : ApartUp) : ThreeApart := by
  intro E Ω _ _ _ _ _ _ T₁ Q₁ s₁ T₂ Q₂ s₂ t ht hT M _ _ _ _
  obtain ⟨a, b, ha, hb, hab⟩ := h1 E Ω T₁ Q₁ s₁ t ht
  obtain ⟨x, y, hx, hy, hxy⟩ := h1 ↥Q₁.K Ω T₂ Q₂ s₂ a (hT a ha)
  obtain ⟨z, hz⟩ := (h2 ↥Q₁.K ↥Q₂.K).2 b
  have hxz : GlobalTheory.Cong.Apart x z := (h2 ↥Q₁.K ↥Q₂.K).1 x z (by rw [hx, hz]; exact hab)
  have hyz : GlobalTheory.Cong.Apart y z := (h2 ↥Q₁.K ↥Q₂.K).1 y z (by rw [hy, hz]; exact hab)
  choose up hup using (h2 ↥Q₂.K M).2
  refine ⟨fun i => up (![x, y, z] i), fun i => ?_, fun i j hij => (h2 ↥Q₂.K M).1 _ _ ?_⟩
  · rw [hup]
    fin_cases i
    · simpa [hx] using ha
    · simpa [hy] using ha
    · simpa [hz] using hb
  · rw [hup, hup]
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | exact hxy | exact hxz | exact hyz | exact hxy.symm | exact hxz.symm | exact hyz.symm

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.TwoPrimes
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_conj (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic ℚ Ω] :
    ∃ (j : Ω →+* ℂ) (c : Ω ≃+* Ω), ∀ z, j (c z) = starRingEnd ℂ (j z) := by
  haveI : Normal ℚ Ω := normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩
  haveI : IsGalois ℚ Ω := ⟨⟩
  let j : Ω →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Ω) : Ω →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j
    (ComplexEmbedding.conjugate j) (Subsingleton.elim _ _)
  exact ⟨j, σ.symm.toRingEquiv, fun x => DFunLike.congr_fun hσ x⟩

private theorem conj_of_sq {w : ℂ} {q : ℕ} (hq : 0 < q) (h : w ^ 2 = (q : ℂ)) :
    starRingEnd ℂ w = w :=
  _root_.UpperTheory.Reformulated.B.Qh56.conj_of_sq hq h

private theorem sq_fix {E Y Ω : Type} [Field E] [Field Y] [Field Ω] [Algebra E Y] [Algebra Y Ω]
    (δ : Y) (q : ℕ) (hq : δ ^ 2 = (q : Y))
    (hspan : ∀ y : Y, ∃ a b : E, y = algebraMap E Y a + algebraMap E Y b * δ)
    (g : Ω ≃+* Ω) (hδ : g (algebraMap Y Ω δ) = -algebraMap Y Ω δ)
    (hE : ∀ (j : E →+* Ω) (x : E), g (g (j x)) = j x) (j : Y →+* Ω) (y : Y) :
    g (g (j y)) = j y := by
  have h2 : (j δ) ^ 2 = (algebraMap Y Ω δ) ^ 2 := by
    rw [← map_pow, ← map_pow, hq, map_natCast, map_natCast]
  have hfix : g (g (j δ)) = j δ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp [hδ]
  obtain ⟨a, b, rfl⟩ := hspan y
  have ha := hE (j.comp (algebraMap E Y)) a
  have hb := hE (j.comp (algebraMap E Y)) b
  simp only [RingHom.comp_apply] at ha hb
  simp only [map_add (f := _), map_mul, ha, hb, hfix]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.twoPrimes :
    PrimeWith → TwoPrimes := by
  intro PW E Y Ω _ _ _ _ _ _ _ _ δ hδ M B hM
  obtain ⟨⟨q, hq0, hq⟩, hspan, s, hsE, hsδ⟩ := hδ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Y
  haveI : Algebra.IsAlgebraic Y Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ Y Ω
  obtain ⟨j0, c, hc⟩ := exists_conj Ω
  have hδ2 : (algebraMap Y Ω δ) ^ 2 = (q : Ω) := by rw [← map_pow, hq, map_natCast]
  have hcc : ∀ z, c (c z) = z := fun z => j0.injective (by rw [hc, hc, Complex.conj_conj])
  have hcδ : c (algebraMap Y Ω δ) = algebraMap Y Ω δ := j0.injective (by
    rw [hc]
    exact conj_of_sq hq0 (by rw [← map_pow, hδ2, map_natCast]))
  have hcroot : ∀ ξ : Ω, ξ ^ M = 1 → c ξ = ξ⁻¹ := fun ξ h => j0.injective (by
    have h1 : (j0 ξ) ^ M = 1 := by rw [← map_pow, h, map_one]
    rw [hc, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 hM.ne')])
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hsc : ∀ (j : E →+* Ω) (x : E), s (c (j x)) = c (j x) :=
    fun j x => hsE ((c : Ω →+* Ω).comp j) x
  have hsinv : ∀ (j : E →+* Ω) (x : E), s.symm (j x) = j x := fun j x => by
    rw [RingEquiv.symm_apply_eq, hsE]
  have hsinvδ : s.symm (algebraMap Y Ω δ) = -algebraMap Y Ω δ := by
    rw [RingEquiv.symm_apply_eq, map_neg, hsδ, neg_neg]
  have h1δ : (s.trans c) (algebraMap Y Ω δ) = -algebraMap Y Ω δ := by
    show c (s _) = _
    rw [hsδ, map_neg, hcδ]
  have h11 : ∀ (j : Y →+* Ω) (y : Y), (s.trans c) ((s.trans c) (j y)) = j y :=
    sq_fix (E := E) δ q hq hspan (s.trans c) h1δ (fun j x => by
      show c (s (c (s (j x)))) = j x
      rw [hsE j x, hsc j x, hcc])
  have h22 : ∀ (j : Y →+* Ω) (y : Y), s.symm (s.symm (j y)) = j y :=
    sq_fix (E := E) δ q hq hspan s.symm hsinvδ (fun j x => by rw [hsinv, hsinv])
  obtain ⟨p₁, hp₁, hB, hz₁, hA₁⟩ := PW Y Ω (algebraMap Y Ω δ) q hq0 hδ2 (s.trans c) h1δ h11 M ζ hM hζ B
  obtain ⟨p₂, hp₂, hB₂, hz₂, hA₂⟩ := PW Y Ω (algebraMap Y Ω δ) q hq0 hδ2 s.symm hsinvδ h22 M ζ hM hζ p₁
  have hsζ : (s ζ) ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have e1 : (s ζ)⁻¹ = ζ ^ p₁ := by rw [← hcroot _ hsζ]; exact hz₁
  have e2 : ζ = (s ζ) ^ p₂ := by
    rw [← map_pow, ← hz₂, RingEquiv.apply_symm_apply]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have hdvd : M ∣ p₁ * p₂ + 1 := by
    refine hζ.dvd_of_pow_eq_one _ ?_
    rw [pow_succ, pow_mul, ← e1, inv_pow, ← e2, inv_mul_cancel₀ hζ0]
  refine ⟨p₁, p₂, hp₁, hp₂, hB, hB₂, hdvd, fun A hA h hh hδh y => ?_⟩
  have hle : ∀ n : ℕ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).2 (natCast_mem A n)
  rw [Nat.cast_mul, map_mul] at hA
  by_cases h₁ : A.valuation (p₁ : Ω) < 1
  · exact hA₁ A h₁ h hh hδh y
  · have e : A.valuation (p₁ : Ω) = 1 := le_antisymm (hle _) (not_lt.1 h₁)
    rw [e, one_mul] at hA
    exact hA₂ A hA h hh hδh y
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharAtOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def RamSplit (E : Type) {Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (H : Subgroup (G (maximalRealSubfield E) Ω)) : Prop :=
  ∀ (t : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (A : ValuationSubring Ω), IsPlaceOver A t →
    Ine (F := maximalRealSubfield E) A ≤ H ∨ ∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g

def MoveRoot : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    ∀ ℓ : ℕ, ℓ.Prime → ∃ (b : ℕ) (σ : G ℚ Ω), σ ∈ U ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ (ℓ ^ b) → σ ζ ≠ ζ

def NormVal : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    ∀ q : ℕ, 1 < q → ∃ D : ℕ, 0 < D ∧ ∀ (z : Ω) (n c : ℕ), (∀ τ ∈ U, τ z = z) → z ^ n * (q : Ω) ^ c = 1 → n ∣ c * D

def KumMove : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    ∀ ℓ q : ℕ, ℓ.Prime → 1 < q → ∃ j : ℕ, ∀ k, j ≤ k → ∀ ζ y : Ω, IsPrimitiveRoot ζ (ℓ ^ k) → y ^ ℓ ^ j = (q : Ω) →
      ∃ σ ∈ U, σ ζ = ζ ∧ σ y ≠ y

def OrdPrime : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ℓ k q B : ℕ), ℓ.Prime → 1 < q →
    ∃ p : ℕ, p.Prime ∧ B < p ∧ ℓ ^ k ∣ orderOf (q : ZMod p) ∧ ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 →
      ∀ h : Ω ≃+* Ω, (∀ z, h z ∈ A ↔ z ∈ A) → ∀ y : E, h (algebraMap E Ω y) = algebraMap E Ω y

def CharOrd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ℓ k : ℕ) (a : (ZMod p)ˣ), ℓ.Prime → ℓ ^ (k + 1) ∣ orderOf a →
    ∃ lam : (ZMod p)ˣ →* ℂˣ, lam (-1) = 1 ∧ orderOf (lam a) = ℓ ^ k

def UnrCharAt (f : ℕ) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
    ∃ r : G (maximalRealSubfield E) Ω →* ℂˣ, Good r.ker ∧ RamSplit E r.ker ∧
      ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := maximalRealSubfield E) A ≤ r.ker ∧
        ∀ φ : G (maximalRealSubfield E) Ω, IsFrob A (normV v) φ → orderOf (r φ) = f

def UnrCharPP : Prop := ∀ ℓ k : ℕ, ℓ.Prime → UnrCharAt (ℓ ^ k)

def FreshSplit : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (U : Subgroup (G (maximalRealSubfield E) Ω)),
    IsOpen (U : Set (G (maximalRealSubfield E) Ω)) →
    ∀ T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), T.Finite → ∀ n : ℕ, 0 < n →
    ∃ ψ : G (maximalRealSubfield E) Ω →* ℂˣ, Good ψ.ker ∧ RamSplit E ψ.ker ∧ ψ ^ n = 1 ∧
      (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := maximalRealSubfield E) A, ψ g = 1) ∧
      ∃ u ∉ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := maximalRealSubfield E) A ≤ U ∧
        ∃ τ ∈ Ine (F := maximalRealSubfield E) A, orderOf (ψ τ) = n

theorem RamSplit.inf {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {H H' : Subgroup (G (maximalRealSubfield E) Ω)} (h : RamSplit E H) (h' : RamSplit E H') : RamSplit E (H ⊓ H') := by
  intro t A hA
  rcases h t A hA with h1 | h1
  · rcases h' t A hA with h2 | h2
    · exact Or.inl (le_inf h1 h2)
    · exact Or.inr h2
  · exact Or.inr h1

theorem RamSplit.mono {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {H H' : Subgroup (G (maximalRealSubfield E) Ω)} (hle : H ≤ H') (h : RamSplit E H) : RamSplit E H' := by
  intro t A hA
  rcases h t A hA with h1 | h1
  · exact Or.inl (h1.trans hle)
  · exact Or.inr h1

theorem unrCharAt_of (h : UnrCharPP) (f : ℕ) (hf : 0 < f) : UnrCharAt f := by
  induction f using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp _ => exact h p n hp
  | zero => exact absurd hf (lt_irrefl 0)
  | one => simpa using h 2 0 Nat.prime_two
  | coprime a b ha hb hab iha ihb =>
    intro E Ω _ _ _ _ _ _ v
    obtain ⟨r, h1, h2, h3⟩ := iha (by omega) E Ω v
    obtain ⟨s, k1, k2, k3⟩ := ihb (by omega) E Ω v
    have hle : r.ker ⊓ s.ker ≤ (r * s).ker := fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mem_ker.1 hg.1, MonoidHom.mem_ker.1 hg.2, one_mul]
    refine ⟨r * s, (h1.inf k1).mono hle, (h2.inf k2).mono hle, fun A hA =>
      ⟨(le_inf (h3 A hA).1 (k3 A hA).1).trans hle, fun φ hφ => ?_⟩⟩
    have e1 := (h3 A hA).2 φ hφ
    have e2 := (k3 A hA).2 φ hφ
    rw [MonoidHom.mul_apply, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime (by rwa [e1, e2]), e1, e2]

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrLarge
section
noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem natCast_notMem_sq {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr K) (w : HeightOneSpectrum (𝓞 K)) : (p : 𝓞 K) ∉ w.asIdeal ^ 2 := by
  intro h
  have hv : (p : 𝓞 K) ∈ w.asIdeal := Ideal.pow_le_self two_ne_zero h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hP := w.isPrime
  have hlo : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hpz).2 (by simpa using hv)
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have hun := (not_dvd_discr_iff_forall_mem K (𝓞 K) hpz).1 hd w.asIdeal hP (by simpa using hv)
  have hu : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := hlo.over.symm
  have : Finite (ℤ ⧸ w.asIdeal.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ (hu ▸ hb)
  have : (w.asIdeal.under ℤ).IsMaximal := hu ▸ hmax
  have : Finite (w.asIdeal.under ℤ).ResidueField := inferInstance
  have he : w.asIdeal.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 K)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) w.asIdeal hb] at he
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h

theorem unrLarge : UnrLarge := by
  intro K _ _
  refine ⟨(discr K).natAbs, fun p hp hB w => natCast_notMem_sq hp (fun hd => ?_) w⟩
  have h1 : p ∣ (discr K).natAbs := Int.natCast_dvd.mp hd
  have h2 : 0 < (discr K).natAbs := Int.natAbs_pos.mpr (discr_ne_zero K)
  exact absurd (Nat.le_of_dvd h2 h1) (not_le.mpr hB)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

