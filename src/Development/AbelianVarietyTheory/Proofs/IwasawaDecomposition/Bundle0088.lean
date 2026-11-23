module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0082
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NegOneNormFromCmFieldFiniteAdeles
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem cm_fixed_integer (cm : CMData F E) (x : 𝓞 E) (hx : star (x : E) = (x : E)) :
    ∃ t : 𝓞 F, (x : E) = algebraMap F E t := by
  obtain ⟨t, ht⟩ := (cm.fixed x).1 hx
  have hi : IsIntegral ℤ t := by
    have h1 : IsIntegral ℤ (algebraMap F E t) := by
      rw [ht]; exact RingOfIntegers.isIntegral_coe x
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 h1
  exact ⟨⟨t, hi⟩, ht.symm⟩

theorem cm_exists_unit_disc (cm : CMData F E) (M : Ideal (𝓞 F)) (hM : M.IsMaximal) :
    ∃ θ : 𝓞 E, ∃ t : 𝓞 F, ∃ n : 𝓞 F, (θ : E) + star (θ : E) = algebraMap F E t ∧
      (θ : E) * star (θ : E) = algebraMap F E n ∧ t ^ 2 - 4 * n ∉ M := by
  obtain ⟨P, hP, hPM⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) M (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact bot_le)
  obtain ⟨θ, s, hs, hθ⟩ := cm.cmUnram.2.2 P hP
  have hs' : (s : E) = star (θ : E) := hs
  obtain ⟨t, ht⟩ := cm_fixed_integer cm (θ + s) (by
    change star ((θ : E) + s) = (θ : E) + s
    rw [hs', star_add, star_star, add_comm])
  obtain ⟨n, hn⟩ := cm_fixed_integer cm (θ * s) (by
    change star ((θ : E) * s) = (θ : E) * s
    rw [hs', star_mul, star_star])
  change (θ : E) + s = _ at ht
  change (θ : E) * s = _ at hn
  refine ⟨θ, t, n, hs' ▸ ht, hs' ▸ hn, fun h => hθ ?_⟩
  rw [← hPM, Ideal.mem_comap] at h
  have e : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) = (θ - s) ^ 2 := by
    apply RingOfIntegers.coe_injective
    have h1 : ∀ z : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z) = algebraMap F E (z : F) :=
      fun z => rfl
    rw [h1]
    simp only [map_sub, map_pow, map_mul, map_ofNat]
    change algebraMap F E t ^ 2 - 4 * algebraMap F E n = ((θ : E) - s) ^ 2
    rw [← ht, ← hn]; ring
  rw [e] at h
  exact hP.isPrime.mem_of_pow_mem 2 h

theorem cm_exists_coords (cm : CMData F E) (θ : E) (hθ : θ - star θ ≠ 0) (x : E) :
    ∃ p q : F, x = algebraMap F E p + algebraMap F E q * θ := by
  have hθ' : star θ - θ ≠ 0 := fun h => hθ (by linear_combination -h)
  have hq : star ((x - star x) / (θ - star θ)) = (x - star x) / (θ - star θ) := by
    rw [star_div₀, star_sub, star_sub, star_star, star_star]
    field_simp
    ring
  obtain ⟨q, hq'⟩ := (cm.fixed _).1 hq
  have hp : star (x - (x - star x) / (θ - star θ) * θ) = x - (x - star x) / (θ - star θ) * θ := by
    rw [star_sub, star_mul, hq]
    field_simp
    ring
  obtain ⟨p, hp'⟩ := (cm.fixed _).1 hp
  exact ⟨p, q, by rw [hp', hq']; ring⟩

theorem cm_local_neg_one (cm : CMData F E) (θ : 𝓞 E) (t n : 𝓞 F)
    (ht : (θ : E) + star (θ : E) = algebraMap F E t) (hn : (θ : E) * star (θ : E) = algebraMap F E n)
    (hθ : (θ : E) - star (θ : E) ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A B : v.adicCompletion F,
      A ^ 2 + A * B * algebraMap F (v.adicCompletion F) t + B ^ 2 * algebraMap F (v.adicCompletion F) n = -1 ∧
      (t ^ 2 - 4 * n ∉ v.asIdeal → A ∈ v.adicCompletionIntegers F ∧ B ∈ v.adicCompletionIntegers F) := by
  have key : ∀ (a b : v.adicCompletionIntegers F) (t n : 𝓞 F),
      a ^ 2 + a * b * algebraMap (𝓞 F) (v.adicCompletionIntegers F) t +
        b ^ 2 * algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = -1 →
      (a : v.adicCompletion F) ^ 2 + a * b * algebraMap F (v.adicCompletion F) t +
        b ^ 2 * algebraMap F (v.adicCompletion F) n = -1 := by
    intro a b t n h
    have h2 := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) h
    have h1 : ∀ z : 𝓞 F, ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) z : v.adicCompletionIntegers F) :
        v.adicCompletion F) = algebraMap F (v.adicCompletion F) (z : F) := fun z => rfl
    push_cast at h2
    rw [h1, h1] at h2
    exact h2
  by_cases hd : t ^ 2 - 4 * n ∈ v.asIdeal
  · obtain ⟨θ', h⟩ := cm_exists_unit_disc cm v.asIdeal v.isMaximal
    obtain ⟨a, b, t', n', ht', hn', h⟩ := GlobalTheory.LocalNormNegOne.main F E cm v θ' h
    have h := key a b t' n' h
    obtain ⟨p, q, hpq⟩ := cm_exists_coords cm θ hθ θ'
    have hs : ∀ z : F, star (algebraMap F E z) = algebraMap F E z := fun z => (cm.fixed _).2 ⟨z, rfl⟩
    have hst : star (θ' : E) = algebraMap F E p + algebraMap F E q * star (θ : E) := by
      rw [hpq, star_add, star_mul, hs, hs, mul_comm]
    have e1 : (t' : F) = 2 * p + q * t := by
      apply (algebraMap F E).injective
      simp only [map_add (f := _), map_mul, map_ofNat]
      rw [← ht', ← ht, hst, hpq]; ring
    have e2 : (n' : F) = p ^ 2 + p * q * t + q ^ 2 * n := by
      apply (algebraMap F E).injective
      simp only [map_add (f := _), map_mul, map_pow]
      rw [← hn', ← ht, ← hn, hst, hpq]; ring
    rw [e1, e2] at h
    simp only [map_add (f := _), map_mul, map_pow, map_ofNat] at h
    refine ⟨a + b * algebraMap F _ p, b * algebraMap F _ q, ?_, fun h => (h hd).elim⟩
    linear_combination h
  · obtain ⟨a, b, t', n', ht', hn', h⟩ := GlobalTheory.LocalNormNegOne.main F E cm v θ ⟨t, n, ht, hn, hd⟩
    have h := key a b t' n' h
    have e1 : (t' : F) = t := (algebraMap F E).injective (ht'.symm.trans ht)
    have e2 : (n' : F) = n := (algebraMap F E).injective (hn'.symm.trans hn)
    rw [e1, e2] at h
    exact ⟨a, b, h, fun _ => ⟨a.2, b.2⟩⟩

end

theorem neg_one_norm_finiteAdele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1 := by
  intro F E _ _ _ _ _ _ cm
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  obtain ⟨θ, t, n, ht, hn, hd⟩ := cm_exists_unit_disc cm M hM
  have hd0 : t ^ 2 - 4 * n ≠ 0 := fun h => hd (h ▸ M.zero_mem)
  have hθ : (θ : E) - star (θ : E) ≠ 0 := by
    intro h
    apply hd0
    apply RingOfIntegers.coe_injective
    apply (algebraMap F E).injective
    simp only [map_sub, map_pow, map_mul, map_ofNat, map_zero]
    change algebraMap F E t ^ 2 - 4 * algebraMap F E n = 0
    rw [← ht, ← hn]
    linear_combination ((θ : E) - star (θ : E)) * h
  choose A B hAB hint using cm_local_neg_one cm θ t n ht hn hθ
  have hfin : {v : HeightOneSpectrum (𝓞 F) | t ^ 2 - 4 * n ∈ v.asIdeal}.Finite := by
    have := Ideal.finite_factors (R := 𝓞 F) (I := Ideal.span {t ^ 2 - 4 * n})
      (by simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hd0)
    simpa only [Ideal.dvd_span_singleton] using this
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, t ^ 2 - 4 * n ∉ v.asIdeal := by
    simpa only [Filter.eventually_cofinite, not_not] using hfin
  let a : FiniteAdeleRing (𝓞 F) F := ⟨A, hev.mono fun v hv => (hint v hv).1⟩
  let b : FiniteAdeleRing (𝓞 F) F := ⟨B, hev.mono fun v hv => (hint v hv).2⟩
  have hab : a ^ 2 + a * b * algebraMap F (FiniteAdeleRing (𝓞 F) F) t +
      b ^ 2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) n = -1 := by
    apply FiniteAdeleRing.ext
    intro v
    have := hAB v
    rw [sq, sq] at this ⊢
    exact this
  let L : E →ₐ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F := Algebra.TensorProduct.includeLeft
  let Rr : FiniteAdeleRing (𝓞 F) F →ₐ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
    Algebra.TensorProduct.includeRight
  refine ⟨Rr a + L θ * Rr b, ?_⟩
  have hL : ∀ x, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) (L x) = L (star x) := fun x => by
    simp [Formalism.UG.sigR, L, CMData.sig, starRingEnd_apply]
  have hR : ∀ x, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) (Rr x) = Rr x := fun x => by
    simp [Formalism.UG.sigR, Rr]
  have h1 := congrArg L ht
  have h2 := congrArg L hn
  have h3 := congrArg Rr hab
  simp only [map_add (f := _), map_mul, map_pow, map_neg, map_one, AlgHom.commutes] at h1 h2 h3
  rw [map_add (f := _), map_mul, hL, hR, hR]
  rw [← h1, ← h2] at h3
  linear_combination h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubOneMemMapOfEq
section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG Formalism.UG.P Formalism.EigenvalueLevelCeiling GlobalTheory.AdeleBaseChange
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwistPlaces

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valued_int {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) :
    Valued.v (algebraMap K (P.adicCompletion K) (algebraMap (𝓞 K) K b)) = P.intValuation b := by
  rw [levelaf_valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

theorem intValuation_eq_one {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K}
    (h : b ∉ P.asIdeal) : P.intValuation b = 1 :=
  le_antisymm (P.intValuation_le_one b) (not_lt.1 fun h' => h ((P.intValuation_lt_one_iff_mem b).1 h'))


variable (F E) in
abbrev toId : (RInt F E)ˣ →* (AfE F E)ˣ := Units.map (RInt F E).subtype.toMonoidHom

theorem exists_toId_eq {x : (AfE F E)ˣ} (hx : x ∈ intU F E) : ∃ u, toId F E u = x :=
  ⟨⟨⟨x, hx.1⟩, ⟨(x⁻¹ : (AfE F E)ˣ), hx.2⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩, Units.ext rfl⟩

section
variable {ι : AfE F E →+* FiniteAdeleRing (𝓞 E) E}
  (hι : ∀ x a, ι (x ⊗ₜ[F] a) = algebraMap E _ x * adMap F E a)
include hι

theorem mem_suppAt (v : HeightOneSpectrum (𝓞 F)) (y : (AfE F E)ˣ) :
    y ∈ suppAt E v ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ≠ v → ι (y : AfE F E) P = 1 := by
  have h1 : y ∈ suppAt E v ↔ ∀ v', v' ≠ v → prV (E := E) v' (y : AfE F E) = 1 := by
    simp only [suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  rw [h1]
  simp only [prV_eq_one_iff hι]
  exact ⟨fun h P hP => h _ hP P rfl, fun h v' hv P hP => h P (hP ▸ hv)⟩

end

theorem inertAt_le_congN {v : HeightOneSpectrum (𝓞 F)} {N : ℕ} (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    inertAt E v ≤ congN F E N := by
  obtain ⟨ι, hι⟩ := exists_toAd F E
  rintro x ⟨h1, h2⟩
  obtain ⟨u, rfl⟩ := exists_toId_eq h1
  have hN0 : (N : E) ≠ 0 := by
    rintro h
    obtain rfl : N = 0 := by exact_mod_cast h
    exact hN (by simp)
  refine ⟨u, (mem_kerRed _ u).2 (Ideal.mem_span_singleton'.2
    ⟨⟨((N : E)⁻¹ ⊗ₜ[F] 1 : AfE F E) * (((u : RInt F E) - 1 : RInt F E) : AfE F E), mem_int_of_map hι fun P => ?_⟩, Subtype.ext ?_⟩), rfl⟩
  · rw [map_mul, map_tmul_one hι, afsplit_mul_apply, HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hP : P.under (𝓞 F) = v
    · have hNP : (N : 𝓞 E) ∉ P.asIdeal := fun h => hN (by
        rw [← hP]
        change algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
        rwa [map_natCast])
      have h3 : Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) P) = 1 := by
        change Valued.v (algebraMap E (P.adicCompletion E) (N : E)⁻¹) = 1
        rw [map_inv₀, map_inv₀, ← map_natCast (algebraMap (𝓞 E) E), valued_int, intValuation_eq_one P hNP, inv_one]
      rw [map_mul, h3, one_mul]
      exact map_mem_int hι ((u : RInt F E) - 1).2 P
    · have h3 : ι ((u : RInt F E) : AfE F E) P = 1 := (mem_suppAt hι v _).1 h2 P hP
      rw [AddSubgroupClass.coe_sub, map_sub, afsplit_sub_apply, h3, OneMemClass.coe_one, map_one, afsplit_one_apply, sub_self,
        mul_zero, map_zero]
      exact zero_le_one
  · apply map_injective hι
    rw [Subring.coe_mul, SubringClass.coe_natCast, map_mul, map_mul, map_natCast, map_tmul_one hι, mul_right_comm,
      ← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)), ← map_mul, inv_mul_cancel₀ hN0, map_one, one_mul]

variable {L : Type} [Field L]

theorem finite_Qprime {ξ : Chr F E L} (h : ξ ∈ openChr F E L) : (Qprime ξ).Finite := by
  obtain ⟨N, hN, hk⟩ := h
  have h0 : (Ideal.span {(N : 𝓞 F)}) ≠ ⊥ := by simpa using hN.ne'
  refine (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 (by_contra fun hn => hv ?_)
  exact (inertAt_le_congN hn).trans hk

end Local

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem under_eq_iff {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)} :
    P.under (𝓞 F) = v ↔ P.asIdeal.under (𝓞 F) = v.asIdeal :=
  ⟨fun h => h ▸ rfl, fun h => HeightOneSpectrum.ext h⟩

end Res

section Datum

open Formalism.L2.Col

variable {X : Fields}

theorem exists_of_conj_eq (hX : X.Ok) {a : 𝓞 X.E} (ha : X.conjO a = a) :
    ∃ r : 𝓞 X.F, algebraMap (𝓞 X.F) (𝓞 X.E) r = a := by
  let c : X.E →ₐ[X.F] X.E := { starRingEnd X.E with commutes' := hX.star_F }
  let M : IntermediateField X.F X.E :=
    (AlgHom.equalizer c (AlgHom.id _ _)).toIntermediateField fun x hx => by
      have hx' : star x = x := hx
      change star x⁻¹ = x⁻¹
      rw [star_inv₀, hx']
  have hM : M = ⊥ := by
    have := IntermediateField.isSimpleOrder_of_finrank_prime X.F X.E (by rw [hX.rankE]; exact Nat.prime_two)
    refine (eq_bot_or_eq_top M).resolve_right fun e => ?_
    obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hX.f_pos
    refine hX.emb_ne τ τ (RingHom.ext fun x => ?_)
    have h1 : x ∈ M := e ▸ IntermediateField.mem_top
    exact congrArg (X.emb τ) (show star x = x from h1).symm
  have h2 : (a : X.E) ∈ M := congrArg (fun z : 𝓞 X.E => (z : X.E)) ha
  rw [hM, IntermediateField.mem_bot] at h2
  obtain ⟨x, hx⟩ := h2
  have h3 : IsIntegral ℤ x := by
    rw [← isIntegral_algebraMap_iff (B := X.E), hx]
    exact RingOfIntegers.isIntegral_coe _
  exact ⟨⟨x, h3⟩, RingOfIntegers.ext hx⟩

variable {S : Set ℕ} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}

theorem mem_QE_iff (hsel : IsSel X sel) (ξ : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)} :
    P ∈ QE sel (ξ : Chr X.F X.E X.K) ↔
      P.under (𝓞 X.F) ∈ Qprime (ξ : Chr X.F X.E X.K) ∧ sel (P.under (𝓞 X.F)) = P := by
  classical
  have hf := finite_Qprime (ξ := (ξ : Chr X.F X.E X.K)) ξ.2.1.1.1.1.2
  rw [QE, dite_eq_left hf, Finset.mem_image]
  simp only [Set.Finite.mem_toFinset]
  refine ⟨?_, fun h => ⟨_, h.1, h.2⟩⟩
  rintro ⟨v, hv, rfl⟩
  rw [under_eq_iff.2 (hsel v)]
  exact ⟨hv, rfl⟩

end Datum

end GlobalTheory.TwistPlaces
end
end

