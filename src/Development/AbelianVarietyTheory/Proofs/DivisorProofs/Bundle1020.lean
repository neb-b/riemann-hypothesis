module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugacyClassPartEqWeightMulKottwitzPointSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0984
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDataOfCongruentHeckeSystem
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open Polynomial ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.CharpolyFrobDense

namespace GlobalTheory.ExpFrame.CongrBlock

theorem norm_le_one_of_compact {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (t : Γ →* Kˣ) (ht : Continuous t) (g : Γ) : ‖((t g : Kˣ) : K)‖ ≤ 1 := by
  have hc : Continuous fun g => ‖((t g : Kˣ) : K)‖ := (Units.continuous_val.comp ht).norm
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hc.continuousOn
  have hpow : ∀ k : ℕ, ‖((t g : Kˣ) : K)‖ ^ k ≤ M := fun k => by
    have := hM ⟨g ^ k, Set.mem_univ _, rfl⟩
    simpa [map_pow, Units.val_pow_eq_pow_val, norm_pow] using this
  by_contra h
  push_neg at h
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop M).exists
  exact absurd (hpow k) (not_le.2 hk)

theorem continuous_character_of_rankOneRep_continuous {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    (χ : Γ →* Kˣ) (h : Continuous (GlobalTheory.TripleGal.rk1 χ)) : Continuous fun g => ((χ g : Kˣ) : K) := by
  have h1 : Continuous fun g => ((GlobalTheory.TripleGal.rk1 χ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0 :=
    (Units.continuous_val.comp h).matrix_elem 0 0
  convert h1 using 1
  funext g
  simp [GlobalTheory.TripleGal.rk1]

theorem coeff_heckePolyOf {L : Type} [Field L] (n q : ℕ) (a : ℕ → L) (j : ℕ) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff j =
      if j ≤ n then (-1) ^ j * (q : L) ^ (j * (j - 1) / 2) * a j else 0 := by
  simp only [Formalism.L2.Col.heckePolyOf, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_iff]

theorem coeff_sub_eq_reverse {K : Type} [Field K] {p q : K[X]} {n : ℕ} (hp : p.natDegree = n)
    (hq : q.natDegree = n) (k : ℕ) (hk : k ≤ n) :
    (p - q).coeff k = (p.reverse - q.reverse).coeff (n - k) := by
  simp only [coeff_sub, coeff_reverse, hp, hq, revAt_le (Nat.sub_le n k), Nat.sub_sub_self hk]

theorem norm_sysOf_sub_lt {l : ℕ} [Fact l.Prime] {Pl I : Type} (n : ℕ) (pt : Pl → Fin n → I) {θ θ0 : I → Qbar l}
    (h : ∀ i, ‖θ i - θ0 i‖ < 1) (P : Pl) (k : ℕ) : ‖sysOf n pt θ P k - sysOf n pt θ0 P k‖ < 1 := by
  unfold sysOf
  split_ifs
  · exact h _
  · simp

theorem norm_coeff_hecke_sub_lt {l : ℕ} [Fact l.Prime] (n q : ℕ) (a b : ℕ → Qbar l) (w : Qbar l) (hw : ‖w‖ ≤ 1)
    (hab : ∀ k, ‖a k - b k‖ < 1) (j : ℕ) :
    ‖(Formalism.L2.Col.heckePolyOf n q (fun k => a k * w ^ k) -
      Formalism.L2.Col.heckePolyOf n q (fun k => b k * w ^ k)).coeff j‖ < 1 := by
  rw [coeff_sub, coeff_heckePolyOf, coeff_heckePolyOf]
  split_ifs
  · have e : (-1) ^ j * (q : Qbar l) ^ (j * (j - 1) / 2) * (a j * w ^ j) -
        (-1) ^ j * (q : Qbar l) ^ (j * (j - 1) / 2) * (b j * w ^ j) =
        (-1) ^ j * ((q : Qbar l) ^ (j * (j - 1) / 2) * w ^ j) * (a j - b j) := by ring
    rw [e, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_pow, norm_pow]
    have h1 : ‖(q : Qbar l)‖ ^ (j * (j - 1) / 2) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
    have h2 : ‖w‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hw
    calc _ ≤ ‖a j - b j‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ h1 (pow_nonneg (norm_nonneg _) _) h2)
      _ < 1 := hab j
  · simp

theorem blockFor_of_congr : GlobalTheory.Published.ChebotarevDegreeOne → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (P : Par) (W : Wts ι) (F : Frame l ι P.Nr) (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (mu : ι → ℕ → ℕ) (θ θ0 : F.I → PadicAlgCl l), (∀ τ, Antitone (res P.Nr (mu τ))) → F.IsEig mu θ → F.IsEig W.lam θ0 → Bk θ0 → (∀ i, ‖θ i - θ0 i‖ < 1) → BlockFor Ω inc P W mu := by
  intro hC E Ω _ _ _ _ _ _ l _ ι _ inc P W F Bk hG mu θ θ0 hmu hθ hθ0 hBk hcl
  obtain ⟨Pl, pt, Fn, ep, hep, h1, h2⟩ := hG
  obtain ⟨r, J, hJ, hr, hrR⟩ := h1 mu θ hmu hθ
  obtain ⟨a, ρ, χ, bot, hat, hρ, hχ, hbot, hρR⟩ := h2 θ0 hθ0 hBk
  refine ⟨ep, J, bot, hep, ⟨r, a, ρ, χ, hat, hr, hρ, hχ, ?_⟩, fun τ => ⟨fun b => hJ τ b, hbot τ⟩⟩

  set p : G E Ω → Polynomial (Qbar l) := fun σ => (r σ).val.charpoly with hp
  set q : G E Ω → Polynomial (Qbar l) := fun σ =>
    (ρ σ).val.charpoly * ∏ s, (X - C ((χ s σ : (Qbar l)ˣ) : Qbar l)) with hq
  have dp : ∀ σ, (p σ).natDegree = P.Nr := fun σ => by
    simp [hp, Matrix.charpoly_natDegree_eq_dim]
  have dq : ∀ σ, (q σ).natDegree = P.Nr := fun σ => by
    simp only [hq]
    rw [(Matrix.charpoly_monic _).natDegree_mul (monic_prod_of_monic _ _ fun s _ => monic_X_sub_C _),
      Matrix.charpoly_natDegree_eq_dim, natDegree_finsetProd_X_sub_C_eq_card, Fintype.card_fin,
      Finset.card_univ, Fintype.card_fin, hat]

  have cp : CoeffCont p := fun k =>
    (GlobalTheory.TypeLeaf.continuous_charpoly_coeff_of_matrix P.Nr k).comp (Units.continuous_val.comp hr.1)
  have cq : CoeffCont q := by
    have c1 : CoeffCont fun σ : G E Ω => (ρ σ).val.charpoly := fun k =>
      (GlobalTheory.TypeLeaf.continuous_charpoly_coeff_of_matrix a k).comp (Units.continuous_val.comp hρ)
    have c2 := coeffCont_prod Finset.univ (fun s (σ : G E Ω) => (X - C ((χ s σ : (Qbar l)ˣ) : Qbar l)))
      (fun s _ => coeffCont_X_sub_C (continuous_character_of_rankOneRep_continuous (χ s) (hχ s).1))
    exact c1.mul c2

  set good : G E Ω → Prop := fun σ => ∀ k, ‖(p σ - q σ).coeff k‖ < 1 with hgood
  have hclosed : IsClosed {σ : G E Ω | good (σ ^ (Fn.sgn : ℤ))} := by
    have : {σ : G E Ω | good (σ ^ (Fn.sgn : ℤ))} =
        ⋂ k, (fun σ : G E Ω => (p (σ ^ (Fn.sgn : ℤ)) - q (σ ^ (Fn.sgn : ℤ))).coeff k) ⁻¹' Metric.ball 0 1 := by
      ext σ; simp [hgood]
    rw [this]
    refine isClosed_iInter fun k => (IsUltrametricDist.isClosed_ball (0 : Qbar l) 1).preimage ?_
    have hz := continuous_zpow (G := G E Ω) (Fn.sgn : ℤ)
    simp only [coeff_sub]
    exact ((cp k).comp hz).sub ((cq k).comp hz)

  have hS := Fn.cofin
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) hC hS
  have hsub : {σ : G E Ω | ∃ v : HeightOneSpectrum (𝓞 E),
      v ∉ {v : HeightOneSpectrum (𝓞 E) | (Ideal.absNorm v.asIdeal).Prime ∧ v ∉ Set.range Fn.lab} ∧
      v.asIdeal.inertiaDeg ℤ = 1 ∧ ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ IsFrob B (normV v) σ} ⊆
      {σ : G E Ω | good (σ ^ (Fn.sgn : ℤ))} := by
    rintro σ ⟨v, hv, hd, B, hB, hσ⟩
    have hpr : (Ideal.absNorm v.asIdeal).Prime := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd
    have hv' : v ∈ Set.range Fn.lab := by
      by_contra h; exact hv ⟨hpr, h⟩
    obtain ⟨P0, rfl⟩ := hv'
    have e1 := hrR P0 B σ hB hσ
    have e2 := hρR P0 B σ hB hσ
    have hw := norm_le_one_of_compact Fn.tw Fn.cont (σ ^ (Fn.sgn : ℤ))
    intro k
    by_cases hk : k ≤ P.Nr
    · rw [coeff_sub_eq_reverse (dp _) (dq _) k hk]
      simp only [hp, hq]
      rw [e1, e2]
      exact norm_coeff_hecke_sub_lt _ _ _ _ _ hw (norm_sysOf_sub_lt P.Nr pt hcl P0) _
    · push_neg at hk
      rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (by rw [dp]; exact hk),
        coeff_eq_zero_of_natDegree_lt (by rw [dq]; exact hk)]
      simp
  have hall : ∀ σ : G E Ω, good (σ ^ (Fn.sgn : ℤ)) := fun σ => by
    have h := closure_minimal hsub hclosed
    rw [hD.closure_eq] at h
    exact h (Set.mem_univ σ)
  intro σ k
  have h := hall (σ ^ (Fn.sgn : ℤ)) k
  have e : (σ ^ (Fn.sgn : ℤ)) ^ (Fn.sgn : ℤ) = σ := by
    rw [← zpow_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, zpow_one]
  rw [e] at h
  exact h

end GlobalTheory.ExpFrame.CongrBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderEqTopOfEtale
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinPtsAway

theorem supp_compact (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) :
    ∃ Q : Set G.GAf, IsCompact Q ∧ ∀ g, f g ≠ 0 → g ∈ Q := by
  obtain ⟨-, -, -, S, hS⟩ := hf
  refine ⟨⋃ s ∈ S, (fun k : G.GAf × G.GAf => k.1 * s * k.2) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)), ?_, ?_⟩
  · exact S.isCompact_biUnion fun s _ => (L.compact.prod L.compact).image (by fun_prop)
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_iUnion₂.2 ⟨s, hs, (k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

theorem coeff_continuous (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ) :
    Continuous fun g : G.GAf => (LinearMap.charpoly (LinearMap.mulLeft (AfP p)
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C))).coeff k :=
  GlobalTheory.T.continuous_charpoly_coeff_mulLeft_finiteAdeles_awayP p G k

theorem bdd_at_places (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)) (hQ : IsCompact Q) :
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ :=
  GlobalTheory.T.compact_finiteAdelesAwayP_bounded_denominators p Q hQ

theorem rat_of_integral_away (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : ∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) :
    ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z :=
  GlobalTheory.T.exists_prime_pow_mul_rat_eq_int_of_integral_away p q hq

theorem bdd_denom (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)) (hQ : IsCompact Q) :
    ∃ D : ℕ, 0 < D ∧ ∀ q : ℚ, algebraMap ℚ (AfP p) q ∈ Q → ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * D * q = z := by
  obtain ⟨D, hD, hQD⟩ := bdd_at_places p Q hQ
  refine ⟨D, hD, fun q hq => ?_⟩
  obtain ⟨m, z, hz⟩ := rat_of_integral_away p (D * q) fun v => by
    have := hQD _ hq v
    rwa [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, (AfP.eval v).commutes] at this
  exact ⟨m, z, by rw [← hz, mul_assoc]⟩

theorem charpoly_conj_tmul (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (A : Type) [CommRing A]
    [Algebra ℚ A] (y : C) (u : (A ⊗[ℚ] C)ˣ) :
    LinearMap.charpoly (LinearMap.mulLeft A ((u : A ⊗[ℚ] C) * ((1 : A) ⊗ₜ[ℚ] y) * ((u⁻¹ : (A ⊗[ℚ] C)ˣ) : A ⊗[ℚ] C))) =
      (LinearMap.charpoly (LinearMap.mulLeft ℚ y)).map (algebraMap ℚ A) := by
  let e : (A ⊗[ℚ] C) ≃ₗ[A] (A ⊗[ℚ] C) :=
    { LinearMap.mulLeft A (u : A ⊗[ℚ] C) with
      invFun := fun z => ((u⁻¹ : (A ⊗[ℚ] C)ˣ) : A ⊗[ℚ] C) * z
      left_inv := fun z => by simp [← mul_assoc]
      right_inv := fun z => by simp [← mul_assoc] }
  have h1 : LinearMap.mulLeft A ((u : A ⊗[ℚ] C) * ((1 : A) ⊗ₜ[ℚ] y) * ((u⁻¹ : (A ⊗[ℚ] C)ˣ) : A ⊗[ℚ] C)) =
      e.conj (LinearMap.mulLeft A ((1 : A) ⊗ₜ[ℚ] y)) := by
    ext z
    simp [e, LinearEquiv.conj_apply, mul_assoc]
  have h2 : LinearMap.mulLeft A ((1 : A) ⊗ₜ[ℚ] y) = (LinearMap.mulLeft ℚ y).baseChange A := by
    ext c
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [h1, LinearEquiv.charpoly_conj, h2, LinearMap.charpoly_baseChange]

theorem integral_of_charpoly (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (y : C) (p D : ℕ)
    (h : ∀ i, ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * D * (LinearMap.charpoly (LinearMap.mulLeft ℚ y)).coeff i = z) :
    ∃ m : ℕ, IsIntegral ℤ ((p : C) ^ m * D * y) := by
  choose m z hz using h
  set χ := LinearMap.charpoly (LinearMap.mulLeft ℚ y) with hχ
  set N := χ.natDegree
  set M := ∑ i ∈ Finset.range N, m i
  refine ⟨M, ?_⟩
  set s : ℚ := (p : ℚ) ^ M * D with hs
  have hχy : Polynomial.aeval y χ = 0 := by
    have e := LinearMap.aeval_self_charpoly (LinearMap.mulLeft ℚ y)
    have e2 : Polynomial.aeval (LinearMap.mulLeft ℚ y) χ = Algebra.lmul ℚ C (Polynomial.aeval y χ) := by
      rw [← Polynomial.aeval_algHom_apply]; rfl
    rw [e2] at e
    have := congrArg (fun f : Module.End ℚ C => f 1) e
    simpa using this
  have hlift : χ.scaleRoots s ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i N with hi | hi | hi
    · have hmi : m i ≤ M := Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_range.2 hi)
      refine ⟨(p : ℤ) ^ (M - m i) * z i * ((p : ℤ) ^ M * D) ^ (N - i - 1), ?_⟩
      have e1 : s ^ (N - i) = s * s ^ (N - i - 1) := by
        rw [← pow_succ']; congr 1; omega
      have e2 : s * χ.coeff i = (p : ℚ) ^ (M - m i) * z i := by
        rw [← hz i, hs, ← mul_assoc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hmi]
      simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [e1, ← mul_assoc, mul_comm (χ.coeff i) s, e2, hs]
    · subst hi
      refine ⟨1, ?_⟩
      rw [Nat.sub_self, pow_zero, mul_one, ← Polynomial.leadingCoeff, LinearMap.charpoly_monic]; simp
    · refine ⟨0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi]; simp
  obtain ⟨P, hP, hPdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift
    ((Polynomial.monic_scaleRoots_iff s).2 (LinearMap.charpoly_monic _))
  refine ⟨P, hPm, ?_⟩
  have e3 : Polynomial.eval₂ (algebraMap ℤ C) ((p : C) ^ M * D * y) P =
      Polynomial.aeval ((p : C) ^ M * D * y) (χ.scaleRoots s) := by
    rw [← hP, Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]
  rw [e3, Polynomial.aeval_def]
  have e4 : (p : C) ^ M * D * y = algebraMap ℚ C s * y := by
    rw [hs]; simp
  rw [e4, Polynomial.scaleRoots_eval₂_mul_of_commute _ _ _ (Algebra.commutes _ _) (fun a b => Algebra.commutes _ _),
    ← Polynomial.aeval_def, hχy, mul_zero]

theorem minpoly_coeff_integral (F : Type) [Field F] (S : Type) [Ring S] [Algebra F S] (y : S) (c : F)
    (hc : IsIntegral ℤ (algebraMap F S c * y)) (hy : IsIntegral F y) (k : ℕ) :
    IsIntegral ℤ (c ^ ((minpoly F y).natDegree - k) * (minpoly F y).coeff k) := by
  by_cases hc0 : c = 0
  · subst hc0
    rcases lt_trichotomy k (minpoly F y).natDegree with hk | hk | hk
    · rw [zero_pow (by omega), zero_mul]; exact isIntegral_zero
    · rw [hk, Nat.sub_self, pow_zero, one_mul, ← Polynomial.leadingCoeff, minpoly.monic hy, ]; exact isIntegral_one
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk, mul_zero]; exact isIntegral_zero
  obtain ⟨P, hPm, hP⟩ := hc
  set Pm := P.map (algebraMap ℤ F)
  have hPz : Polynomial.eval₂ (algebraMap F S) (algebraMap F S c * y) Pm = 0 := by
    rw [Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]; exact hP
  have h1 : Polynomial.aeval y (Pm.scaleRoots c⁻¹) = 0 := by
    have e := Polynomial.scaleRoots_eval₂_mul_of_commute (p := Pm) (algebraMap F S) (algebraMap F S c * y) c⁻¹
      (Algebra.commutes _ _) (fun a b => Algebra.commutes _ _)
    rw [hPz, mul_zero, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul] at e
    rw [Polynomial.aeval_def]; exact e
  have h2 : minpoly F y ∣ Pm.scaleRoots c⁻¹ := minpoly.dvd F y h1
  have h3 : (minpoly F y).scaleRoots c ∣ Pm := by
    have := Polynomial.scaleRoots_dvd _ _ (r := c) h2
    rwa [← Polynomial.scaleRoots_mul, inv_mul_cancel₀ hc0, Polynomial.scaleRoots_one] at this
  have h4 := Polynomial.isIntegral_coeff_of_dvd P _ hPm ((Polynomial.monic_scaleRoots_iff c).2 (minpoly.monic hy)) h3 k
  rw [Polynomial.coeff_scaleRoots, mul_comm] at h4
  exact h4

theorem exists_den_minpoly_coeff : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∃ D : ℕ, 0 < D ∧ ∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → ∀ k : ℕ, ∃ m : ℕ, IsIntegral ℤ ((p : G.F) ^ m * D * (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k) := by
  intro p _ G L f hf β x t hx
  obtain ⟨Q, hQc, hQ⟩ := supp_compact p G L f hf
  set N := Module.finrank ℚ G.C
  let cf : ℕ → G.GAf → AfP p := fun k g => (LinearMap.charpoly (LinearMap.mulLeft (AfP p)
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C))).coeff k
  have hQ'c : IsCompact (⋃ k ∈ Finset.range (N + 1), cf k '' Q) :=
    (Finset.range (N + 1)).isCompact_biUnion fun k _ => hQc.image (coeff_continuous p G k)
  obtain ⟨D', hD'0, hD'⟩ := bdd_denom p _ hQ'c
  refine ⟨D' ^ Module.finrank G.F G.C, pow_pos hD'0 _, ?_⟩
  intro y h hfy k
  set yc : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hyc
  have hg := hQ _ hfy

  set u : (AfP p ⊗[ℚ] G.C)ˣ := ((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * x with hu
  have hrep : ((((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) =
      (u : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] yc) * ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by
    have e : (((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
        u * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * u⁻¹ := by
      have e0 : (((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
          ((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * x⁻¹) *
            (h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 := rfl
      rw [e0, hu]; group
    rw [e]; simp only [Units.val_mul]; rfl
  have hchar : LinearMap.charpoly (LinearMap.mulLeft (AfP p)
      ((((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) =
      (LinearMap.charpoly (LinearMap.mulLeft ℚ yc)).map (algebraMap ℚ (AfP p)) := by
    rw [hrep]; exact charpoly_conj_tmul G.C (AfP p) yc u
  have hcoef : ∀ i, ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * D' * (LinearMap.charpoly (LinearMap.mulLeft ℚ yc)).coeff i = z := by
    intro i
    by_cases hi : i ≤ N
    · apply hD'
      refine Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le hi), _, hg, ?_⟩
      simp only [cf]
      rw [hchar, Polynomial.coeff_map]
    · refine ⟨0, 0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]
      simp
  obtain ⟨M, hM⟩ := integral_of_charpoly G.C yc p D' hcoef
  have hint : IsIntegral ℤ (algebraMap G.F G.C ((p : G.F) ^ M * D') * yc) := by
    convert hM using 2
    simp [map_mul, map_pow, map_natCast]
  have hI := minpoly_coeff_integral G.F G.C yc _ hint (Algebra.IsIntegral.isIntegral _) k
  set d := (minpoly G.F yc).natDegree
  have hd : d ≤ Module.finrank G.F G.C := minpoly.natDegree_le yc
  by_cases hk : k ≤ d
  · refine ⟨M * (d - k), ?_⟩
    have e : (p : G.F) ^ (M * (d - k)) * ((D' ^ Module.finrank G.F G.C : ℕ) : G.F) * (minpoly G.F yc).coeff k =
        (D' : G.F) ^ (Module.finrank G.F G.C - (d - k)) *
          (((p : G.F) ^ M * D') ^ (d - k) * (minpoly G.F yc).coeff k) := by
      rw [mul_pow, ← pow_mul, Nat.cast_pow]
      have : Module.finrank G.F G.C = (Module.finrank G.F G.C - (d - k)) + (d - k) := by omega
      conv_lhs => rw [this, pow_add]
      ring
    rw [e]
    have hD : IsIntegral ℤ (D' : G.F) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ G.F (D' : ℤ)))
    exact (hD.pow _).mul hI
  · refine ⟨0, ?_⟩
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
    exact isIntegral_zero

end GlobalTheory.FinPtsAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralCharacterSubquotientProductIrreducibles
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul

theorem centralChar_subquotient_prodIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x : IrrGL (k := k), ∃ ω : kˣ →* ℂˣ, HasCentralChar x.rep ω) ∧ ∀ (t m : ℕ) (x : Fin t → IrrGL (k := k)) (hd : ∑ a, (x a).1 = m) (ω : Fin t → kˣ →* ℂˣ), (∀ a, HasCentralChar (x a).rep (ω a)) → ∀ (τ : IrrRep (GL (Fin m) k)) (ω' : kˣ →* ℂˣ), IsSubquotient τ.ρ (prodIrr x hd) → HasCentralChar τ.ρ ω' → ω' = ∏ a, ω a := by
  intro k _ _ _ _
  refine ⟨fun y => ?_, fun t m x hd ω hω τ ω' hsub hω' => ?_⟩
  · obtain ⟨f, _, hf⟩ := LocGL.exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
    exact ⟨f, hf⟩
  · have hcen : HasCentralChar (prodIrr x hd) (∏ a, ω a) :=
      CentralSupport.hasCentralChar_multiProd_prod _ (fun a => (x a).rep) ω hω
    have := Model.nontrivial_of_isIrreducible τ.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : τ.V)
    ext z
    have h1 := Model.scalar_of_isSubquotient hsub (hcen z) v
    rw [hω'] at h1
    exact smul_left_injective ℂ hv h1

end GlobalTheory.GamMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassScalarValueCore
section
namespace GlobalTheory.ClassScalarValueCore

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
open GlobalTheory.ClassScalarValue
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 800000 in
theorem class_scalar_value_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (k : O.Cl' t) (h : GA D (Vc D i)) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), IsIdemSum e P → (∀ PP ∈ P, ((O.bad t : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h y → O.Lh t k = Bridge.hLat (Vc D i) (fin (Vc D i) h) → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → ((O.bad t : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → inC O.c' (O.ep t k * (((O.La t k).mIdx (O.Nc t k) D.R.r : O.c'.F))⁻¹ * ((O.La t k).zCard (O.Nc t k) D.R.r : O.c'.F)) = (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ * (Real.sqrt (((((O.La t k).La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.La t k).La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup O hO t k h e P y he hP hs hy hLh hbad
  have hL := hC.lev
  obtain ⟨r1, r2, -, r4, -, r6⟩ := (hO.reps t).1 k
  have hcj := (GlobalTheory.ClassScalarCompare.latPin_iff_conjLat _ _).1 (hO.reps t).2 k
  have g := GlobalTheory.ClassScalarCompare.guard_conjLat (H := T.Q.H) (L := (O.La t k).La) ⟨r1, r2, r6⟩
  rw [hcj, GlobalTheory.ClassScalarCompare.conjLat_conjLat] at g
  have hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q :=
    (hT.laws.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀).1
  have hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := exists_ideal (Vc D i) hO.lift.std.1 hO.lift.std.2 h e P y he hs hy (O.bad t) hP _ _
    (chrEq_mul_inv (hL.mu0 i) (hL.xi (tup t)) hL.eta)
    (fun Q hQ x hx => by
      have a1 : (R.C.mu0 i).UnrAt Q := (R.C.isMu0 i).unr Q fun j hj => hQ (by
        obtain ⟨u, hu⟩ := (Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans
          ((Fin.prod_univ_two D.host.g).symm ▸ (hO.bad t).2.2.2.2)
        rw [hu, Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hj)
      have a2 : (R.xiH (tup t)).UnrAt Q := by
        by_contra hn
        rcases (hL.Q_ram (tup t) Q).1 hn with a | ⟨Q', a, a'⟩
        · exact hQ (hbad Q (Or.inr a))
        · rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast] at hQ
          exact hQ (hbad Q' (Or.inr a))
      change (R.C.mu0 i).loc Q x * (R.xiH (tup t)).loc Q x * ((R.C.eta).loc Q x)⁻¹ = 1
      rw [a1 x hx, a2 x hx, R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])
    (fun Q hQ x => by
      rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
        (R.C.isMu0 i).triv.1, (hL.xi_triv (tup t)).1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, above_eq,
        Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul])
  rw [← hbar] at c1 c3
  rw [← hLh] at c3
  obtain ⟨q, q0, q1, q2⟩ := (hO.ep t).2 (O.Lh t k) cc g.1 g.2.1 g.2.2 c1 c3
  have hB := (hO.tuple t).B cc c0 c2
  have hi := GlobalTheory.ClassScalarCompare.stdIndex_conjLat (O.Lh t k)
  rw [← hcj] at hi
  rw [← hpq, ← Nat.cast_pow] at q1
  have := value_calc (x := (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)) q0
    (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0))
    (mIdx_ne_zero (O.La t k) D.R.r (fun h0 : O.Nc t k = 0 => by simpa [h0] using r4.1)) q1
  rw [(hO.ep t).1 k, q2, zCard_eq _ _ _ r4.2.2, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, hB, ← c4, map_ratCast,
    map_natCast, map_natCast, ← Nat.cast_pow]
  have hi' : ((O.La t k).Ln.toAddSubgroup.addSubgroupOf (O.La t k).La.toAddSubgroup).index =
      ((O.Lh t k ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.Lh t k).toAddSubgroup).index := hi
  rw [← hi'] at this
  exact this

end GlobalTheory.ClassScalarValueCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugacyClassPartEqWeightMulKottwitzPointSumStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugacyClassPart_eq_weight_mul_kottwitzPointSum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y₀ : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re → FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z) → ∀ y₀ : grp G β, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {y₀}) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K'), ((Nat.card (MulAction.stabilizer (grp G β) (Quotient.out o) ⊓ Subgroup.centralizer {y₀} : Subgroup (grp G β)) : ℕ) : ℂ)⁻¹ * GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y₀ = if (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y₀ z) then wt (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * pointSum ((toAfF G β x t hx).comp (Subgroup.centralizer {y₀}).subtype) ((toP1 G β).comp (Subgroup.centralizer {y₀}).subtype) (MonoidHom.id (Gr G 1)) Kf K' (toAfF G β x t hx y₀) (toP1 G β y₀) f f' else 0 := by
  first | (exact @GlobalTheory.CxUnfoldGen.cls_eq_of_uniq) | (exact GlobalTheory.CxUnfoldGen.cls_eq_of_uniq) | (intros; apply GlobalTheory.CxUnfoldGen.cls_eq_of_uniq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormReadingEquivariantNotGoodEmbeddingStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormReading_equivariant_not_good_embedding : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → (∀ σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → ∀ (ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)), (∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))) → ∀ σ : D.what₂.LL →+* ℂ, ¬ GoodEmb T.Q.c (res T σ) → ∀ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρC g f)) = σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f)) := by
  first | exact @GlobalTheory.ReadingConjEquiv.reading_equiv_of_not_good | exact GlobalTheory.ReadingConjEquiv.reading_equiv_of_not_good | (intros; apply GlobalTheory.ReadingConjEquiv.reading_equiv_of_not_good <;> assumption)
end

