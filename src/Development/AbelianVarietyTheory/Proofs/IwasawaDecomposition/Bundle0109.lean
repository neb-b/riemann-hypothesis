module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Formalism.LocalToGlobal.HermitianForms.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Formalism.GL3MeanSquares.Bundle0002
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.CyclotomicNorms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0009
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0100

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdSOfResSEqZero
section
open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.SplitResidue

open Formalism.L2.DIV HeightOneSpectrum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_maximalIdeal_iff (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔
      Valued.v (x : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := (x : Valued.integer (v.adicCompletion F)))

theorem integral_image (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (b : 𝓞 E) :
    φ ((algebraMap (𝓞 E) E b) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ v.adicCompletionIntegers F := by
  have h0 : IsIntegral ℤ b := Algebra.IsIntegral.isIntegral b
  let ψ : 𝓞 E →+* v.adicCompletion F :=
    φ.comp ((inclE (F := F) (v.adicCompletion F)).comp (algebraMap (𝓞 E) E))
  have h1 : IsIntegral (v.adicCompletionIntegers F) (ψ b) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) ψ (RingHom.ext_int _ _) h0
  exact (adicCompletionIntegers.integers F v).mem_of_integral h1

theorem comp_mem (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (hφ : ∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = a) (s : Formalism.L2.Herm.intAf F E) :
    φ (prV (E := E) v s.1) ∈ v.adicCompletionIntegers F := by
  have hle : Formalism.L2.Herm.intAf F E ≤
      Subring.comap (φ.comp (prV (E := E) v)) (v.adicCompletionIntegers F).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨b, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨b0, hb0⟩ := b.2
      show φ (prV (E := E) v ((b : E) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F))) ∈ v.adicCompletionIntegers F
      rw [Formalism.UG.P.afsplit_prV_tmul, ← hb0]
      exact integral_image v φ b0
    · show φ (prV (E := E) v ((1 : E) ⊗ₜ[F] (y : Formalism.L2.Herm.Af F))) ∈ v.adicCompletionIntegers F
      rw [Formalism.UG.P.afsplit_prV_tmul, hφ]
      exact y.2 v
  exact hle s.2

theorem mem_idS_of_resS_eq_zero (w : HeightOneSpectrum (𝓞 E)) {t : Formalism.L2.Herm.intAf F E}
    (h : resS F w t = 0) : t ∈ idS F w.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  unfold resS at h
  rw [RingHom.comp_apply] at h
  exact (map_eq_zero_iff _ (RingEquiv.injective _)).1 h

theorem exists_residue_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (p : 𝓞 E),
    (∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = a) →
    Valued.v (φ (inclE (F := F) (v.adicCompletion F) (p : E))) < 1 →
    (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → p ∈ P.asIdeal → P = w) →
    ∃ (ρ : Formalism.L2.Herm.intAf F E →+* v.adicCompletionIntegers F)
      (e : (𝓞 E ⧸ w.asIdeal) ≃+* Formalism.L2.Forms.kv F v),
      (∀ s, ((ρ s : v.adicCompletionIntegers F) : v.adicCompletion F) = φ (prV (E := E) v s.1)) ∧
      ∀ s, IsLocalRing.residue _ (ρ s) = e (Formalism.L2.DIV.resS F w s) := by
  intro F E _ _ _ _ _ v w φ p hφ hp hw
  let ρ : Formalism.L2.Herm.intAf F E →+* v.adicCompletionIntegers F :=
    (φ.comp ((prV (E := E) v).comp (Formalism.L2.Herm.intAf F E).subtype)).codRestrict
      (v.adicCompletionIntegers F) (fun s => comp_mem v φ hφ s)
  have hρ : ∀ s, ((ρ s : v.adicCompletionIntegers F) : v.adicCompletion F) = φ (prV (E := E) v s.1) :=
    fun _ => rfl
  let r : Formalism.L2.Herm.intAf F E →+* Formalism.L2.Forms.kv F v := (IsLocalRing.residue _).comp ρ
  let g : 𝓞 E →+* Formalism.L2.Forms.kv F v := r.comp (oToS F E)
  have hg0 : ∀ b : 𝓞 E, Valued.v (φ (inclE (F := F) (v.adicCompletion F) (b : E))) < 1 → g b = 0 := by
    intro b hb
    show IsLocalRing.residue _ (ρ (oToS F E b)) = 0
    rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff, hρ]
    exact hb
  have hv : ∀ x ∈ v.asIdeal, g (algebraMap (𝓞 F) (𝓞 E) x) = 0 := by
    intro x hx
    refine hg0 _ ?_
    have e1 : ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E) = algebraMap F E (algebraMap (𝓞 F) F x) := by
      show algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) x) = _
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have e2 : inclE (F := F) (v.adicCompletion F) (algebraMap F E (algebraMap (𝓞 F) F x)) =
        (1 : E) ⊗ₜ[F] (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) := by
      show (algebraMap F E (algebraMap (𝓞 F) F x)) ⊗ₜ[F] (1 : v.adicCompletion F) = _
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
    rw [e1, e2, hφ]
    refine lt_of_eq_of_lt (valuedAdicCompletion_eq_valuation' v _) ?_
    exact (valuation_lt_one_iff_mem v x).2 hx
  have hne : RingHom.ker g ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hb
    have h1 : algebraMap (𝓞 F) (𝓞 E) x ∈ RingHom.ker g := hv x hx
    rw [hb, Ideal.mem_bot] at h1
    exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E) (h1.trans (map_zero _).symm))
  let P : HeightOneSpectrum (𝓞 E) := ⟨RingHom.ker g, RingHom.ker_isPrime g, hne⟩
  have hunder : P.under (𝓞 F) = v := by
    refine HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 F)).isPrime.ne_top ?_).symm
    intro x hx
    exact hv x hx
  have hk : RingHom.ker g = w.asIdeal := congrArg HeightOneSpectrum.asIdeal (hw P hunder (hg0 p hp))
  have hz : idS F w.asIdeal ≤ RingHom.ker r := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    rw [← hk] at ha
    exact ha
  have hfac : ∀ s (b : 𝓞 E), resS F w s = Ideal.Quotient.mk w.asIdeal b → r s = g b := by
    intro s b h
    have h0 : resS F w (s - oToS F E b) = 0 := by rw [map_sub, resS_oToS, h, sub_self]
    have h1 : r (s - oToS F E b) = 0 := hz (mem_idS_of_resS_eq_zero w h0)
    rw [map_sub] at h1
    exact sub_eq_zero.1 h1
  have hs : Function.Surjective g := by
    intro κ
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective κ
    let s : Formalism.L2.Herm.intAf F E := ⟨(1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (a : v.adicCompletion F),
      Subring.subset_closure (Or.inr ⟨⟨_, Formalism.UG.P.afsplitI_mem_intAd v _ a.2⟩, rfl⟩)⟩
    have hρs : ρ s = a := Subtype.ext (by
      rw [hρ]
      show φ (prV (E := E) v ((1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (a : v.adicCompletion F))) = _
      rw [Formalism.UG.P.afsplit_prV_tmul, Formalism.UG.P.afsplitI_self, hφ])
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (resS F w s)
    refine ⟨b, (hfac s b hb.symm).symm.trans ?_⟩
    show IsLocalRing.residue _ (ρ s) = _
    rw [hρs]
  refine ⟨ρ, (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs), hρ, ?_⟩
  intro s
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (resS F w s)
  rw [← hb]
  exact hfac s b hb.symm

end GlobalTheory.SplitResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneIffOfSqrt
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem half_int_coords {E : Type} [Field E] [NumberField E] (d : ℕ) (hd : d.Prime) (h4 : d % 4 = 3)
    (s : E) (hs : s ^ 2 = -(d : E)) (c : E ≃ₐ[ℚ] E) (hc : c s = -s) (a b : ℚ)
    (hy : IsIntegral ℤ ((a : E) + (b : E) * s)) :
    ∃ t u : ℤ, (2 : ℤ) ∣ t - u ∧ 2 * a = t ∧ 2 * b = u := by
  have hcy : IsIntegral ℤ ((a : E) - (b : E) * s) := by
    have := hy.map (c.toRingEquiv.toRingHom.toIntAlgHom)
    simpa [hc, sub_eq_add_neg] using this
  have key : ∀ q : ℚ, IsIntegral ℤ (q : E) → ∃ n : ℤ, q = n := by
    intro q hq
    have h1 : IsIntegral ℤ q := by
      have : (q : E) = algebraMap ℚ E q := by simp
      rw [this] at hq
      exact (isIntegral_algebraMap_iff ).1 hq
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
    exact ⟨n, by simpa using hn.symm⟩
  obtain ⟨t, ht⟩ := key (2 * a) (by
    have e : ((2 * a : ℚ) : E) = ((a : E) + (b : E) * s) + ((a : E) - (b : E) * s) := by
      push_cast; ring
    rw [e]; exact hy.add hcy)
  obtain ⟨n, hn⟩ := key (a ^ 2 + d * b ^ 2) (by
    have e : ((a ^ 2 + d * b ^ 2 : ℚ) : E) = ((a : E) + (b : E) * s) * ((a : E) - (b : E) * s) := by
      push_cast; linear_combination (b : E) ^ 2 * hs
    rw [e]; exact hy.mul hcy)
  have hm : (d : ℚ) * (2 * b) ^ 2 = ((4 * n - t ^ 2 : ℤ) : ℚ) := by
    push_cast; rw [← ht, ← hn]; ring
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℚ) * (2 * b) = k := by
    have h1 : IsIntegral ℤ (((d : ℚ) * (2 * b)) ^ 2) := by
      have : ((d : ℚ) * (2 * b)) ^ 2 = algebraMap ℤ ℚ (d * (4 * n - t ^ 2)) := by
        rw [eq_intCast, Int.cast_mul, ← hm]; push_cast; ring
      rw [this]; exact isIntegral_algebraMap
    have h2 := IsIntegral.of_pow (by norm_num : 0 < 2) h1
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact ⟨n, by simpa using hn.symm⟩
  have hk2 : k ^ 2 = (d : ℤ) * (4 * n - t ^ 2) := by
    have : (k : ℚ) ^ 2 = (d : ℚ) * ((4 * n - t ^ 2 : ℤ) : ℚ) := by
      rw [← hm, ← hk]; ring
    exact_mod_cast this
  have hdk : (d : ℤ) ∣ k := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (hk2 ▸ dvd_mul_right _ _)
  obtain ⟨u, rfl⟩ := hdk
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hu : 2 * b = u := by
    apply mul_left_cancel₀ hd0
    rw [hk]; push_cast; ring
  refine ⟨t, u, ?_, ht, hu⟩
  have h5 : (d : ℤ) * u ^ 2 = 4 * n - t ^ 2 := by
    rw [hu] at hm; exact_mod_cast hm
  obtain ⟨e, he⟩ : ∃ e : ℤ, (d : ℤ) = 4 * e + 3 := ⟨(d : ℤ) / 4, by omega⟩
  have h6 : (2 : ℤ) ∣ (t - u) ^ 2 := ⟨2 * n - (2 * e + 1) * u ^ 2 - t * u, by
    rw [he] at h5; linear_combination h5⟩
  exact Int.prime_two.dvd_of_dvd_pow h6

theorem exists_rat_coords {E : Type} [Field E] [NumberField E] (d : ℕ)
    (s : E) (hs : s ^ 2 = -(d : E)) {x : E} (hx : x ∈ IntermediateField.adjoin ℚ {s}) :
    ∃ a b : ℚ, x = (a : E) + (b : E) * s :=
  _root_.GlobalTheory.RatCoordsAdjoin.exists_rat_add_mul_of_mem_adjoin d s hs hx

theorem normOne_iff_of_sqrt {E : Type} [Field E] [NumberField E] (d : ℕ) (hd : d.Prime) (h4 : d % 4 = 3)
    (s : E) (hs : s ^ 2 = -(d : E)) (c : E ≃ₐ[ℚ] E) (hc : c s = -s) (M p : ℕ) :
    NormOne d M p ↔ ∃ π : 𝓞 E, (π : E) ∈ IntermediateField.adjoin ℚ {s} ∧ (π : E) * c (π : E) = (p : E) ∧
      (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 E)} := by
  have hsK : s ∈ IntermediateField.adjoin ℚ {s} := IntermediateField.mem_adjoin_simple_self ℚ _
  constructor
  · rintro ⟨A, B, hN, ⟨u, hu⟩, ⟨v, hv⟩⟩
    obtain ⟨e, he⟩ : ∃ e : ℤ, (d : ℤ) + 1 = 4 * e := ⟨((d : ℤ) + 1) / 4, by omega⟩
    have heE : (d : E) + 1 = 4 * e := by exact_mod_cast congrArg (Int.cast : ℤ → E) he
    have hω : IsIntegral ℤ ((1 + s) / 2) := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C e, by monicity!, ?_⟩
      rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, eq_intCast]
      linear_combination (1 / 4 : E) * hs - (1 / 4 : E) * heE
    let ω : 𝓞 E := ⟨(1 + s) / 2, hω⟩
    have hA : (A : E) = 2 + M * u + 2 * M * v := by
      have : A = 2 + M * u + 2 * M * v := by linear_combination hv + hu
      rw [this]; push_cast; ring
    have hB : (B : E) = M * u := by rw [hu]; push_cast; ring
    have hπ : ((1 + (M : 𝓞 E) * ((v : 𝓞 E) + (u : 𝓞 E) * ω) : 𝓞 E) : E) = ((A : E) + B * s) / 2 := by
      have h0 : algebraMap (𝓞 E) E ω = (1 + s) / 2 := rfl
      change algebraMap (𝓞 E) E _ = _
      simp only [map_add (f := _), map_mul, map_one, map_natCast, map_intCast]
      rw [h0, hA, hB]; ring
    refine ⟨1 + (M : 𝓞 E) * ((v : 𝓞 E) + (u : 𝓞 E) * ω), ?_, ?_, ?_⟩
    · rw [hπ]
      exact div_mem (add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hsK)) (ofNat_mem _ 2)
    · rw [hπ]
      have hNE : (A : E) ^ 2 + d * B ^ 2 = 4 * p := by exact_mod_cast congrArg (Int.cast : ℤ → E) hN
      rw [map_div₀, map_add (f := _), map_mul, map_intCast, map_intCast, hc, map_ofNat]
      linear_combination (1 / 4 : E) * hNE - (B : E) ^ 2 / 4 * hs
    · rw [add_sub_cancel_left]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rintro ⟨π, hK, hN, hM⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hM
    have hyE : (π : E) = 1 + M * (y : E) := by
      have : π = 1 + M * y := by linear_combination hy
      rw [this]; push_cast; rfl
    rcases Nat.eq_zero_or_pos M with rfl | hM0
    · rw [hyE] at hN
      simp only [Nat.cast_zero, zero_mul, add_zero, map_one, mul_one] at hN
      have : p = 1 := by exact_mod_cast hN.symm
      exact ⟨2, 0, by simp [this], by simp, by simp⟩
    · have hME : (M : E) ≠ 0 := by exact_mod_cast hM0.ne'
      have hyK : (y : E) ∈ IntermediateField.adjoin ℚ {s} := by
        have : (y : E) = ((π : E) - 1) / M := by rw [hyE]; field_simp; ring
        rw [this]
        exact div_mem (sub_mem hK (one_mem _)) (natCast_mem _ _)
      obtain ⟨a, b, hab⟩ := exists_rat_coords d s hs hyK
      obtain ⟨t, u, ⟨w, hw⟩, ht, hu⟩ := half_int_coords d hd h4 s hs c hc a b (hab ▸ y.isIntegral_coe)
      have htE : 2 * (a : E) = t := by exact_mod_cast congrArg (Rat.cast : ℚ → E) ht
      have huE : 2 * (b : E) = u := by exact_mod_cast congrArg (Rat.cast : ℚ → E) hu
      refine ⟨2 + M * t, M * u, ?_, dvd_mul_right _ _, ⟨w, by linear_combination (M : ℤ) * hw⟩⟩
      rw [hyE, hab] at hN
      simp only [map_add (f := _), map_mul, map_one, map_natCast, map_ratCast, hc] at hN
      have : (2 + M * t : E) ^ 2 + d * (M * u) ^ 2 = 4 * p := by
        rw [← htE, ← huE]
        linear_combination 4 * hN + 4 * (M : E) ^ 2 * (b : E) ^ 2 * hs
      exact_mod_cast this

theorem normOne_iff_host : ∀ (R : Ranks) (H : Host R) (M p : ℕ), NormOne H.d M p ↔ ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)} := by
  intro R H M p
  have hs : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hc : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
    apply H.φ₀.injective
    have h1 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
    have h2 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) :=
      H.conjE_apply _ _
    rw [h2, map_neg, h1]
    simp
  exact normOne_iff_of_sqrt H.d H.hyp.2.1 (by have := H.hyp.2.2.2.1; omega) H.sqrtMinusD hs H.conj hc M p

end GlobalTheory.Mem.An
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeLatticeDeterminantClassLaws
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.RelDet

open IdlFact

section General

variable {L : Type} [Field L] [NumberField L]

def ordI (w : HeightOneSpectrum (𝓞 L)) (a : Neutral.B1.Ideles L) : ℤ := -WithZero.log (valAt w a)

theorem valAt_eq (w : HeightOneSpectrum (𝓞 L)) (a : Neutral.B1.Ideles L) : valAt w a = WithZero.exp (-ordI w a) := by
  rw [ordI, neg_neg, WithZero.exp_log (valAt_ne_zero w a)]

theorem ordI_mul (w : HeightOneSpectrum (𝓞 L)) (a b : Neutral.B1.Ideles L) : ordI w (a * b) = ordI w a + ordI w b := by
  unfold ordI
  rw [map_mul, WithZero.log_mul (valAt_ne_zero w a) (valAt_ne_zero w b)]
  ring

theorem ordI_inv (w : HeightOneSpectrum (𝓞 L)) (a : Neutral.B1.Ideles L) : ordI w a⁻¹ = -ordI w a := by
  unfold ordI
  rw [map_inv, WithZero.log_inv]

theorem ordI_diag (w : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : ordI w (Neutral.B1.diagUnits L k) = Formalism.L2.Host.ordF w k := by
  have h : valAt w (Neutral.B1.diagUnits L k) = w.valuation L (k : L) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : L)
  rw [ordI, h, Formalism.L2.Host.ordF]

def powI (n : HeightOneSpectrum (𝓞 L) → ℕ) : Neutral.B1.Ideles L :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 L), Neutral.B1.localIdele L w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)) ^ n w

theorem ordI_powI (n : HeightOneSpectrum (𝓞 L) → ℕ) (hn : {w | n w ≠ 0}.Finite) (w : HeightOneSpectrum (𝓞 L)) :
    ordI w (powI n) = n w := by
  classical
  have e : powI n = ∏ v ∈ hn.toFinset, Neutral.B1.localIdele L v (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v)) ^ (n v : ℤ) := by
    unfold powI
    rw [finprod_eq_prod_of_mulSupport_subset (s := hn.toFinset)]
    · simp only [zpow_natCast]
    · intro v hv
      by_contra h
      have h0 : n v = 0 := by simpa using h
      exact hv (by simp [h0])
  have h := valAt_prod hn.toFinset (fun v => (n v : ℤ)) w
  rw [ordI, e, h, WithZero.log_exp, neg_neg]
  split_ifs with hw
  · rfl
  · have h0 : n w = 0 := by simpa using hw
    simp [h0]

end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem mk_mk_eq {a b : Neutral.B1.Ideles H.E}
    (h : ∀ w w', IsConjPl H w w' → ordI w a - ordI w' a = ordI w b - ordI w' b) :
    (QuotientGroup.mk (QuotientGroup.mk a) : DtT H ⧸ UOT H) = QuotientGroup.mk (QuotientGroup.mk b) := by
  have h1 : a⁻¹ * b ∈ KD H ⊔ unitIdl H.E := by
    refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H _).2 fun w w' hw => ?_
    rw [← valAt_apply, ← valAt_apply, valAt_eq, valAt_eq, ordI_mul, ordI_mul, ordI_inv, ordI_inv]
    have := h w w' hw
    congr 1
    omega
  obtain ⟨k, hk, u, hu, e⟩ := Subgroup.mem_sup.1 h1
  refine QuotientGroup.eq.2 ⟨u, hu, ?_⟩
  have hk1 : (QuotientGroup.mk k : DtT H) = 1 := (QuotientGroup.eq_one_iff k).2 hk
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← e, QuotientGroup.mk_mul, hk1, one_mul]
  rfl

def repI (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) : Neutral.B1.Ideles H.E :=
  powI fun w => (ordSub w (detSub M') - ordSub w (detSub M)).toNat

theorem relDetT_eq (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) :
    relDetT H N M M' = QuotientGroup.mk (QuotientGroup.mk (repI H N M M')) := rfl

theorem ordI_repI (N : ℕ) : letI := H.cmStar; ∀ (M M' : SDLat H.E N) (w w' : HeightOneSpectrum (𝓞 H.E)),
    IsConjPl H w w' → ordI w (repI H N M.1 M'.1) - ordI w' (repI H N M.1 M'.1) =
      ordSub w (detSub M'.1) - ordSub w (detSub M.1) := by
  letI := H.cmStar
  intro M M' w w' hw
  have f1 := (ordSub_detSub_lattice H.E N M.1 M.2.1 M.2.2.1).1
  have f2 := (ordSub_detSub_lattice H.E N M'.1 M'.2.1 M'.2.2.1).1
  have hf : {w | (ordSub w (detSub M'.1) - ordSub w (detSub M.1)).toNat ≠ 0}.Finite := by
    refine (f1.union f2).subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
    exact hv (by simp [hn.1, hn.2])
  have h1 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N M w w' hw
  have h2 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N M' w w' hw
  unfold repI
  rw [ordI_powI _ hf, ordI_powI _ hf]
  omega

end GlobalTheory.Mem.Chr.RelDet

namespace GlobalTheory.Mem.Chr

open RelDet


open Classical in
theorem relDetT_laws : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; (∀ L : SDLat H.E N, relDetT H N L.1 L.1 = 1) ∧ (∀ L L' L'' : SDLat H.E N, relDetT H N L.1 L'.1 * relDetT H N L'.1 L''.1 = relDetT H N L.1 L''.1) ∧ ∀ (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E), L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → relDetT H N L.1 L'.1 = QuotientGroup.mk (e1T H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩) := by
  intro R H N
  letI := H.cmStar
  refine ⟨fun L => relDetT_self H N L.1, fun L L' L'' => ?_, fun L L' γ hγ => ?_⟩
  · rw [relDetT_eq, relDetT_eq, relDetT_eq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    refine mk_mk_eq H fun w w' hw => ?_
    have h1 := ordI_repI H N L L' w w' hw
    have h2 := ordI_repI H N L' L'' w w' hw
    have h3 := ordI_repI H N L L'' w w' hw
    rw [ordI_mul, ordI_mul]
    omega
  · obtain ⟨he, hk⟩ := GlobalTheory.Mem.RatPts.rat_points R H
    obtain ⟨k, hk⟩ := hk ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩
    rw [← he k _ hk, relDetT_eq]
    refine mk_mk_eq H fun w w' hw => ?_
    have hk' : (γ : Matrix (Fin N) (Fin N) H.E).det * H.conj (k : H.E) = k := hk
    have hd : (γ : Matrix (Fin N) (Fin N) H.E).det ≠ 0 := fun h0 => k.ne_zero (by rw [← hk', h0, zero_mul])
    have hc : H.conj (k : H.E) ≠ 0 := fun h0 => k.ne_zero (by rw [← hk', h0, mul_zero])
    have e : k = Units.mk0 _ hd * Units.mk0 _ hc := Units.ext hk'.symm
    have h1 : Formalism.L2.Host.ordF w' k = Formalism.L2.Host.ordF w' (Units.mk0 _ hd) + Formalism.L2.Host.ordF w' (Units.mk0 _ hc) := by
      rw [← DetOrd.ordF_mul', ← e]
    have h2 : Formalism.L2.Host.ordF w' (Units.mk0 _ hc) = Formalism.L2.Host.ordF w k := by
      have := (conjPl_main.2.1 R H w w').1 hw (k : H.E)
      unfold Formalism.L2.Host.ordF
      rw [← this]
      rfl
    have h3 := (ordSub_detSub_lattice H.E N L.1 L.2.1 L.2.2.1).2.2 (γ : Matrix (Fin N) (Fin N) H.E)
      (Units.mk0 _ hd) rfl w'
    have h4 : ordSub w' (detSub L'.1) = Formalism.L2.Host.ordF w' (Units.mk0 _ hd) + ordSub w' (detSub L.1) := by
      rw [hγ]
      exact h3
    have h5 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N L w w' hw
    have h6 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N L' w w' hw
    rw [ordI_repI H N L L' w w' hw, ordI_diag, ordI_diag]
    omega

end GlobalTheory.Mem.Chr
end
end

