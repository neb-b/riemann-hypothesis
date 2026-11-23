module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0013
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001

@[expose] public section

noncomputable section

namespace GlobalTheory.Mass.OnePlace

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.P GlobalTheory.NormSum.RepAt
open scoped TensorProduct Matrix

theorem unitary_transpose {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J g : Matrix (Fin n) (Fin n) A) :
    cT σ g * J * g = J ↔ gᵀ * Jᵀ * g.map σ = Jᵀ := by
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, cT, Matrix.transpose_transpose,
    Matrix.mul_assoc]

section Ad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] 𝔸
local notation "𝒮" => tensInt (F := F) 𝔸 (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) 𝔸

theorem mat_denom {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝒜) : ∃ d : ℕ, 0 < d ∧ d • M ∈ matIn 𝒮 n := by
  have cast_level (m : ℕ) : levelafC (F := F) E (m : 𝓞 F) = (m : 𝒜) := by
    rw [levelafC, map_natCast]
    exact map_natCast (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜) m
  have denom_entry (x : 𝒜) : ∃ m : ℕ, 0 < m ∧ (m : 𝒜) * x ∈ 𝒮 := by
    obtain ⟨d, hd, hx⟩ := levelaf_denom x
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
    refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rwa [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    · rw [← cast_level, ← hq, levelafC_mul, mul_assoc]
      exact mul_mem (levelafC_mem q) hx
  choose m hm0 hm using fun ij : Fin n × Fin n => denom_entry (M ij.1 ij.2)
  refine ⟨∏ ij, m ij, Finset.prod_pos fun ij _ => hm0 ij, fun i j => ?_⟩
  rw [Matrix.smul_apply, nsmul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul,
    mul_assoc]
  exact mul_mem (natCast_mem _ _) (hm (i, j))

theorem skew_approx (c : E →ₐ[F] E) {n : ℕ} (G M : Matrix (Fin n) (Fin n) 𝒜) (D : ℕ) (hD : 0 < D) :
    ∃ M₀ : Matrix (Fin n) (Fin n) E, ∃ X ∈ matIn 𝒮 n,
      (M - (G * M.map (sigR c 𝔸) * G⁻¹)ᵀ) -
        (M₀.map ιA - (G * (M₀.map ιA).map (sigR c 𝔸) * G⁻¹)ᵀ) = D • X := by
  obtain ⟨d1, hd1, h1⟩ := mat_denom G
  obtain ⟨d2, hd2, h2⟩ := mat_denom G⁻¹
  obtain ⟨m, hm, hM⟩ := mat_denom M
  have modulus_pos : 0 < m * (D * (d1 * d2)) := by positivity
  have approx_entry (i j : Fin n) :
      ∃ y : E, ∃ o ∈ 𝒮, M i j = ιA y + ((D * (d1 * d2) : ℕ) : 𝒜) * o := by
    have hx := hM i j
    rw [Matrix.smul_apply, nsmul_eq_mul] at hx
    obtain ⟨b, t, ht, e⟩ := csGlob_approx csGlob_intAdApprox
      ((m * (D * (d1 * d2)) : ℕ) : 𝓞 F) (Nat.cast_ne_zero.mpr modulus_pos.ne') _ hx
    refine ⟨(m : E)⁻¹ * algebraMap (𝓞 E) E b, t, ht, ?_⟩
    have hinv : ιA (m : E)⁻¹ * (m : 𝒜) = 1 := by
      rw [← map_natCast ιA, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm.ne'), map_one]
    have cast_level (k : ℕ) : levelafC (F := F) E (k : 𝓞 F) = (k : 𝒜) := by
      rw [levelafC, map_natCast]
      exact map_natCast (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜) k
    rw [cast_level, Nat.cast_mul] at e
    rw [map_mul]
    linear_combination (ιA (m : E)⁻¹) * e +
      (((D * (d1 * d2) : ℕ) : 𝒜) * t - M i j) * hinv
  choose y o ho hyo using approx_entry
  set Y : Matrix (Fin n) (Fin n) 𝒜 := Matrix.of o with hY
  have hYO : Y ∈ matIn 𝒮 n := ho
  have hYσ : Y.map (sigR c 𝔸) ∈ matIn 𝒮 n := fun a b => csScale_sigR_mem c (ho a b)
  have h3 := mul_mem (mul_mem h1 hYσ) h2
  have h4 : ((d1 • G) * Y.map (sigR c 𝔸) * (d2 • G⁻¹))ᵀ ∈ matIn 𝒮 n := fun a b => h3 b a
  refine ⟨Matrix.of y, (d1 * d2) • Y - ((d1 • G) * Y.map (sigR c 𝔸) * (d2 • G⁻¹))ᵀ,
    sub_mem (nsmul_mem hYO _) h4, ?_⟩
  have e : M - (Matrix.of y).map ιA = (D * (d1 * d2)) • Y := by
    ext a b
    simp only [hY, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    rw [hyo a b]
    ring
  have e2 := (map_sub (GlobalTheory.UnRep.WeakApprox.skewPart (sigR c 𝔸) G) M ((Matrix.of y).map ιA)).symm
  rw [e, map_nsmul] at e2
  refine e2.trans ?_
  rw [mul_smul]
  congr 1
  change (d1 * d2) • (Y - (G * Y.map (sigR c 𝔸) * G⁻¹)ᵀ) = _
  simp only [smul_sub, smul_mul_assoc, mul_smul_comm, Matrix.transpose_smul, smul_smul, mul_comm d2 d1]

theorem exists_lam (c : E →ₐ[F] E) (hc : ∀ x, c (c x) = x) (hne : ∃ z, c z ≠ z)
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (h : Matrix (Fin n) (Fin n) 𝒜) :
    ∃ lam : E, lam * c lam = 1 ∧ IsUnit (1 + ιA lam • (afsplitEps E v • h +
      (1 - afsplitEps E v) • (1 : Matrix (Fin n) (Fin n) 𝒜))).det := by
  have : IsArtinianRing (E ⊗[F] v.adicCompletion F) := by
    have : IsArtinianRing (v.adicCompletion F ⊗[F] E) := IsArtinianRing.of_finite (v.adicCompletion F) _
    exact (Algebra.TensorProduct.comm F (v.adicCompletion F) E).surjective.isArtinianRing
  obtain ⟨lam, ⟨hl1, hl2⟩, hu⟩ := exists_unit_det (inclE (F := F) (E := E) (v.adicCompletion F))
    (h.map (prV (E := E) v)) _ (normOne_infinite (c : E →+* E) hc hne)
  refine ⟨lam, hl1, ?_⟩
  have e : 1 + ιA lam • (afsplitEps E v • h + (1 - afsplitEps E v) • (1 : Matrix (Fin n) (Fin n) 𝒜)) =
      afsplitC v (1 + inclE (F := F) (E := E) (v.adicCompletion F) lam • h.map (prV (E := E) v))
        (ιA (1 + lam) • 1) := by
    have e1 : 1 + inclE (F := F) (E := E) (v.adicCompletion F) lam • h.map (prV (E := E) v) =
        (1 + ιA lam • h).map (prV (E := E) v) := by
      rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _),
        GlobalTheory.UnRep.WeakApprox.map_smul'', afsplit_prV_inclE]
    ext i j
    rw [e1, afsplitC_apply, Matrix.map_apply, afsplit_decomp, map_add (f := _), map_one]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e]
  refine Matrix.isUnit_det_of_right_inverse (B := afsplitC v
    (1 + inclE (F := F) (E := E) (v.adicCompletion F) lam • h.map (prV (E := E) v))⁻¹ (ιA (1 + lam)⁻¹ • 1)) ?_
  rw [afsplitC_mul, Matrix.mul_nonsing_inv _ hu, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← map_mul,
    mul_inv_cancel₀ hl2, map_one, one_smul, mul_one, afsplitC_one]

end Ad

theorem weak_approx_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → (∃ z, σ z ≠ z) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (σ : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (D : ℕ), 0 < D → ∀ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ γ ∈ UJ (σ : E →+* E) J, ∃ X : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), (∀ i j, X i j ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) ∧ afsplitEps E v • ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g).1 - 1) = D • X := by
  intro F E _ _ _ _ _ c hc hne n J hJ hdet v D hD g hg
  have hσσ : ∀ x, sigR c (FiniteAdeleRing (𝓞 F) F) (sigR c (FiniteAdeleRing (𝓞 F) F) x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a y => simp [sigR, hc]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have : Nontrivial (E ⊗[F] v.adicCompletion F) :=
    (Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := v.adicCompletion F)
      (algebraMap F E).injective).nontrivial
  obtain ⟨lam, hl1, hu⟩ := exists_lam c hc hne v (g⁻¹).1
  have hp : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hpv := Ideal.absNorm_mem v.asIdeal
  obtain ⟨γ, hγ, X, hX, e⟩ := GlobalTheory.UnRep.WeakApprox.core (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F))
    (c : E →+* E) (sigR c (FiniteAdeleRing (𝓞 F) F)) (csScale_sigR_incl c) hc hσσ Jᵀ
    (by rw [Matrix.transpose_map]; exact congrArg Matrix.transpose hJ) (by rwa [Matrix.det_transpose])
    two_ne_zero (matIn (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) n) mat_denom
    (afsplitEps E v) (afsplit_eps_idem v) (afsplit_sigR_eps c v)
    (fun h0 => by
      have := afsplit_prV_eps (E := E) v
      rw [h0, map_zero] at this
      exact zero_ne_one this)
    (fun X hX i j => mul_mem (afsplit_eps_int v) (hX i j)) _ hp
    (fun X hX => by
      let p := Ideal.absNorm v.asIdeal
      let Af := FiniteAdeleRing (𝓞 F) F
      let S := tensInt (F := F) Af (intOE E) (intAd F)
      let inc : intAd F →+* S :=
        (((Algebra.TensorProduct.includeRight : Af →ₐ[F] E ⊗[F] Af) : Af →+* E ⊗[F] Af).comp
          (intAd F).subtype).codRestrict _ (fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩))
      have hinc : inc.IsIntegral := by
        rintro ⟨x, hx⟩
        refine Subring.closure_induction (p := fun x hx => inc.IsIntegralElem ⟨x, hx⟩)
          ?_ ?_ ?_ ?_ ?_ ?_ hx
        · rintro x (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨y, rfl⟩)
          · let ψ : 𝓞 E →+* S := ((inclE (F := F) Af).comp (algebraMap (𝓞 E) E)).codRestrict _
              (fun z => Subring.subset_closure (Or.inl ⟨⟨_, ⟨z, rfl⟩⟩, rfl⟩))
            have hz : IsIntegral ℤ (ψ b) := map_isIntegral_int ψ (Algebra.IsIntegral.isIntegral b)
            let algebra := inc.toAlgebra
            exact hz.tower_top (A := intAd F)
          · exact RingHom.isIntegralElem_map inc (x := y)
        · exact RingHom.isIntegralElem_zero _
        · exact RingHom.isIntegralElem_one _
        · intro x y _ _ hx hy; exact hx.add _ hy
        · intro x _ hx; exact hx.neg _
        · intro x y _ _ hx hy; exact hx.mul _ hy
      let a : intAd F := ⟨afsplitI v (p : ℕ), afsplitI_mem_intAd v _ (natCast_mem _ _)⟩
      have ha (b : intAd F) : IsUnit (1 + a * b) := by
        let u := 1 + (p : v.adicCompletion F) * (b : Af) v
        have hv : Valued.v (p : v.adicCompletion F) = v.valuation F (algebraMap (𝓞 F) F p) := by
          rw [← levelaf_valued_algebraMap, map_natCast (algebraMap (𝓞 F) F), map_natCast (algebraMap F _)]
        have hu : Valued.v u = 1 := by
          apply Valuation.map_one_add_of_lt
          rw [Valuation.map_mul, hv]
          exact mul_lt_one_of_lt_of_le ((v.valuation_lt_one_iff_mem _).2 hpv)
            ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (b.2 v))
        have hu0 : u ≠ 0 := by
          intro h
          rw [h, map_zero] at hu
          exact zero_ne_one hu
        refine IsUnit.of_mul_eq_one ⟨1 - afsplitI v 1 + afsplitI v u⁻¹,
          add_mem (sub_mem (one_mem _) (afsplitI_mem_intAd v _ (one_mem _))) (afsplitI_mem_intAd v _ ?_)⟩ ?_
        · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, inv_one]
        · apply Subtype.ext
          change (1 + afsplitI v (p : ℕ) * (b : Af)) * _ = 1
          ext w : 1
          by_cases hw : w = v
          · subst w
            simp only [afsplit_add_apply, afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply,
              afsplitI_self, sub_self, zero_add]
            exact mul_inv_cancel₀ hu0
          · simp only [afsplit_add_apply, afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply,
              afsplitI_ne v w hw, zero_mul, add_zero, sub_zero, mul_one]
      obtain ⟨W, hW, e⟩ := mat_inv S (inc a) (unit_of_integral _ hinc a ha) X hX
      refine ⟨W, hW, ?_⟩
      have heps : afsplitEps E v * (p : E ⊗[F] Af) = (1 : E) ⊗ₜ[F] afsplitI v p := by
        rw [← afsplit_decomp, map_natCast, ← afsplitIE_tmul]
        congr 1
        exact (map_natCast (Algebra.TensorProduct.includeRight :
          v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F) p).symm
      rw [← Nat.cast_smul_eq_nsmul (E ⊗[F] FiniteAdeleRing (𝓞 F) F), smul_smul, heps]
      exact e)
    (skew_approx c _) g.1 (g⁻¹).1 g.inv_mul
    (by rw [Matrix.transpose_map]; exact (unitary_transpose _ _ _).1 (inv_mem hg))
    lam hl1 hu D hD
  have hγdet : γ.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hγ
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul, Matrix.det_transpose] at this
    exact hdet this.symm
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γ hγdet, (unitary_transpose _ _ _).2 hγ, X, hX, e⟩

end GlobalTheory.Mass.OnePlace
