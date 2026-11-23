module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartBetween
section
noncomputable section

namespace PIW.AdelClassFin

open NumberField

theorem partBetween : PartBetween := by
  intro E _ _ m N hN δ hδ
  obtain ⟨k, n, hn⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hN
  have hne : Ideal.span {δ} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  haveI : Finite ((𝓞 E) ⧸ Ideal.span {δ}) := by
    first
      | exact (Ideal.absNorm_ne_zero_iff _).mp (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hne)
      | exact Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have hδE : algebraMap (𝓞 E) E δ ≠ 0 := by
    intro h
    apply hδ
    exact IsFractionRing.injective (𝓞 E) E (by rw [h, map_zero])
  let g := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {δ}))
  let T : Set (Fin m → E) := Set.range (fun c : Fin k → ((𝓞 E) ⧸ Ideal.span {δ}) =>
    (algebraMap (𝓞 E) E δ)⁻¹ • ∑ i, (algebraMap (𝓞 E) E (g (c i))) • n i)
  have hT : T.Finite := Set.finite_range _
  have key : ∀ x : Fin m → E, δ • x ∈ N → ∃ t ∈ T, x - t ∈ N := by
    intro x hx
    rw [← hn] at hx
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hx
    have hq : ∀ i, ∃ q : 𝓞 E, algebraMap (𝓞 E) E (a i) -
        algebraMap (𝓞 E) E (g (Ideal.Quotient.mk (Ideal.span {δ}) (a i))) =
        algebraMap (𝓞 E) E δ * algebraMap (𝓞 E) E q := by
      intro i
      have h := Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {δ}))
        (Ideal.Quotient.mk (Ideal.span {δ}) (a i))
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
      obtain ⟨c, hc⟩ := h
      refine ⟨-c, ?_⟩
      rw [← map_sub, ← map_mul, mul_neg, ← hc, neg_sub]
    choose q hq using hq
    refine ⟨_, ⟨fun i => Ideal.Quotient.mk (Ideal.span {δ}) (a i), rfl⟩, ?_⟩
    have hx2 : x = (algebraMap (𝓞 E) E δ)⁻¹ • ∑ i, a i • n i := by
      rw [ha, ← algebraMap_smul E δ x, smul_smul, inv_mul_cancel₀ hδE, one_smul]
    have e1 : ∀ i, a i • n i - (algebraMap (𝓞 E) E (g (Ideal.Quotient.mk (Ideal.span {δ}) (a i)))) • n i =
        (algebraMap (𝓞 E) E δ) • (q i • n i) := by
      intro i
      rw [← algebraMap_smul E (a i), ← algebraMap_smul E (q i), smul_smul, ← sub_smul, hq i]
    have hdiff : x - (algebraMap (𝓞 E) E δ)⁻¹ • ∑ i, (algebraMap (𝓞 E) E
        (g (Ideal.Quotient.mk (Ideal.span {δ}) (a i)))) • n i = ∑ i, q i • n i := by
      rw [hx2, ← smul_sub, ← Finset.sum_sub_distrib]
      simp_rw [e1]
      rw [← Finset.smul_sum, smul_smul, inv_mul_cancel₀ hδE, one_smul]
    show x - (algebraMap (𝓞 E) E δ)⁻¹ • ∑ i, (algebraMap (𝓞 E) E
        (g (Ideal.Quotient.mk (Ideal.span {δ}) (a i)))) • n i ∈ N
    rw [hdiff, ← hn]
    exact (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mpr ⟨q, rfl⟩
  apply Set.Finite.subset (hT.powerset.image (fun S => N ⊔ Submodule.span (𝓞 E) S))
  intro M hM
  obtain ⟨hNM, hMδ⟩ := hM
  refine ⟨(M : Set (Fin m → E)) ∩ T, Set.inter_subset_right, ?_⟩
  apply le_antisymm
  · exact sup_le hNM (Submodule.span_le.mpr Set.inter_subset_left)
  · intro x hx
    obtain ⟨t, htT, hxt⟩ := key x (hMδ x hx)
    have htM : t ∈ M := by
      have h := M.sub_mem hx (hNM hxt)
      rwa [sub_sub_cancel] at h
    have e : x = (x - t) + t := by abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hxt)
      (Submodule.mem_sup_right (Submodule.subset_span ⟨htM, htT⟩))

end PIW.AdelClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartShortOf
section
noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix ComplexOrder

section Defs

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def gramTr {m N : ℕ} (J : Matrix (Fin m) (Fin m) E) (e : Fin N → Fin m → E) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun i j => Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (e j))

def IsMajFam {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ φ : E →+* ℂ, (H φ).PosDef ∧ (H φ).det = ((‖(J.map φ).det‖ : ℝ) : ℂ) ∧
    (∀ z : Fin m → ℂ, ‖star z ⬝ᵥ (J.map φ *ᵥ z)‖ ≤ (star z ⬝ᵥ (H φ *ᵥ z)).re) ∧
    H (ComplexEmbedding.conjugate φ) = (H φ).map (starRingEnd ℂ)

end Defs

def SvCodiffAt (E : Type) [Field E] [NumberField E] (δ : ℕ) : Prop :=
  ∀ y : E, (∀ a : 𝓞 E, Algebra.trace ℚ E (algebraMap (𝓞 E) E a * y) ∈ (algebraMap ℤ ℚ).range) →
    (δ : E) * y ∈ (algebraMap (𝓞 E) E).range

def SvCodiff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], ∃ δ : ℕ, 1 ≤ δ ∧ SvCodiffAt E δ

def SvMaj : Prop :=
  ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), J.IsHermitian → J.det ≠ 0 →
    ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ H.det = ((‖J.det‖ : ℝ) : ℂ) ∧
      ∀ z : Fin n → ℂ, ‖star z ⬝ᵥ (J *ᵥ z)‖ ≤ (star z ⬝ᵥ (H *ᵥ z)).re

def SvMajE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), IsHerm (starRingEnd E) J → J.det ≠ 0 →
      ∃ H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, IsMajFam J H

def SvBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (M : Submodule (𝓞 E) (Fin m → E)),
    M.FG → Submodule.span E (M : Set (Fin m → E)) = ⊤ →
      ∃ e : Fin (m * Module.finrank ℚ E) → Fin m → E, LinearIndependent ℚ e ∧ (∀ i, e i ∈ M) ∧
        ∀ x ∈ M, ∃ c : Fin (m * Module.finrank ℚ E) → ℤ, x = ∑ i, (c i : E) • e i

def SvGramDet : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ m d δ : ℕ, 1 ≤ d → 1 ≤ δ → SvCodiffAt E δ → ∀ p ∈ Lat E m d,
      ∀ e : Fin (m * Module.finrank ℚ E) → Fin m → E, LinearIndependent ℚ e → (∀ i, e i ∈ p.2) →
        (∀ x ∈ p.2, ∃ c : Fin (m * Module.finrank ℚ E) → ℤ, x = ∑ i, (c i : E) • e i) →
          (gramTr p.1 e).det ≠ 0 ∧ |(gramTr p.1 e).det| ≤ ((d * δ : ℕ) : ℚ) ^ (m * Module.finrank ℚ E)

def SvReal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), IsHerm (starRingEnd E) J →
      ∀ H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, IsMajFam J H →
        ∀ e : Fin (m * Module.finrank ℚ E) → Fin m → E, (gramTr J e).det ≠ 0 →
          ∃ R : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℝ,
            R.PosDef ∧ R.det = |((gramTr J e).det : ℝ)| ∧
              ∀ c : Fin (m * Module.finrank ℚ E) → ℤ,
                ∑ φ : E →+* ℂ, ‖φ (hform (starRingEnd E) J (∑ i, (c i : E) • e i) (∑ i, (c i : E) • e i))‖ ≤
                  (fun i => (c i : ℝ)) ⬝ᵥ (R *ᵥ fun i => (c i : ℝ))

theorem partShort_of (hM : PartMink) (hMaj : SvMajE) (hCod : SvCodiff) (hB : SvBasis)
    (hD : SvGramDet) (hR : SvReal) : PartShort := by
  intro F E _ _ _ _ _ _ hCM m d hm hd
  obtain ⟨δ, hδ1, hδ⟩ := hCod E
  have hn1 : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hN1 : 1 ≤ m * Module.finrank ℚ E :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨Kc, hK⟩ := hM _ hN1
  set S : ℝ := max Kc 0 * ((d * δ : ℕ) : ℝ) with hS
  refine ⟨((⌈S ^ Module.finrank ℚ E⌉₊ : ℕ) : ℚ), fun p hp => ?_⟩
  obtain ⟨hherm, hdet, hfg, hspan, -, -⟩ := id hp
  obtain ⟨H, hH⟩ := hMaj F E hCM m p.1 hherm hdet
  obtain ⟨e, hlin, hemem, hegen⟩ := hB E m p.2 hfg hspan
  obtain ⟨hgd, hgb⟩ := hD F E hCM m d δ hd hδ1 hδ p hp e hlin hemem hegen
  obtain ⟨R, hRpd, hRdet, hRle⟩ := hR F E hCM m p.1 hherm H hH e hgd
  obtain ⟨c, hc0, hcR⟩ := hK R hRpd
  set x : Fin m → E := ∑ i, (c i : E) • e i with hx
  have hxmem : x ∈ p.2 := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul E]
    exact p.2.toAddSubgroup.zsmul_mem (hemem i) (c i)
  have hx0 : x ≠ 0 := by
    intro h0
    apply hc0
    funext i
    have h0' : ∑ i, (c i : ℚ) • e i = 0 := by
      rw [← h0, hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul ℚ, Int.cast_smul_eq_zsmul E]
    exact_mod_cast Fintype.linearIndependent_iff.1 hlin _ h0' i
  refine ⟨x, hxmem, hx0, ?_⟩
  set a := hform (starRingEnd E) p.1 x x with ha
  have hsumle : ∑ φ : E →+* ℂ, ‖φ a‖ ≤ S := by
    have h1 := hRle c
    have hdetR : R.det ≤ ((d * δ : ℕ) : ℝ) ^ (m * Module.finrank ℚ E) := by
      rw [hRdet]
      have h' : ((|(gramTr p.1 e).det| : ℚ) : ℝ) ≤
          ((((d * δ : ℕ) : ℚ) ^ (m * Module.finrank ℚ E) : ℚ) : ℝ) := by exact_mod_cast hgb
      rw [Rat.cast_abs, Rat.cast_pow, Rat.cast_natCast] at h'
      exact h'
    have hR0 : 0 ≤ R.det := hRpd.det_pos.le
    have hroot : R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) ≤ ((d * δ : ℕ) : ℝ) := by
      calc R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ))
          ≤ (((d * δ : ℕ) : ℝ) ^ (m * Module.finrank ℚ E)) ^
              ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) :=
            Real.rpow_le_rpow hR0 hdetR (by positivity)
        _ = ((d * δ : ℕ) : ℝ) := by
            rw [one_div]; exact Real.pow_rpow_inv_natCast (by positivity) (by omega)
    have hroot0 : 0 ≤ R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) := Real.rpow_nonneg hR0 _
    calc ∑ φ : E →+* ℂ, ‖φ a‖ ≤ _ := h1
      _ ≤ Kc * R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) := hcR
      _ ≤ max Kc 0 * R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hroot0
      _ ≤ S := mul_le_mul_of_nonneg_left hroot (le_max_right _ _)
  have hnorm : ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ S ^ Module.finrank ℚ E := by
    have h2 := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ a)
    simp only [norm_prod] at h2
    rw [show ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ a)‖ = |((Algebra.norm ℚ a : ℚ) : ℝ)| by simp] at h2
    rw [Rat.cast_abs, h2]
    calc ∏ σ : E →ₐ[ℚ] ℂ, ‖σ a‖ ≤ ∏ σ : E →ₐ[ℚ] ℂ, S :=
          Finset.prod_le_prod₀ (fun σ _ => norm_nonneg _) (fun σ _ =>
            (Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ a‖) (fun φ _ => norm_nonneg _)
              (Finset.mem_univ (σ : E →+* ℂ))).trans hsumle)
      _ = S ^ Module.finrank ℚ E := by rw [Finset.prod_const, Finset.card_univ, AlgHom.card ℚ E ℂ]
  have hfin : ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ ((⌈S ^ Module.finrank ℚ E⌉₊ : ℕ) : ℝ) :=
    hnorm.trans (Nat.le_ceil _)
  exact_mod_cast hfin

end PIW.AdelClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartSplitOfOne
section
noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

def SpComp : Prop :=
  ∀ (E : Type) [Field E] (k m : ℕ) (P : Matrix (Fin k) (Fin m) E) (R : Matrix (Fin m) (Fin k) E), P * R = 1 →
    k ≤ m ∧ ∃ U : Matrix (Fin m) (Fin (m - k)) E, P * U = 0 ∧ Function.Injective U.mulVec ∧
      ∀ w : Fin m → E, P *ᵥ w = 0 → ∃ y, U *ᵥ y = w

def SpDen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (X : Matrix (Fin k) (Fin k) E), ∃ D : ℕ, 1 ≤ D ∧
    ∀ i j, (D : E) * X i j ∈ (algebraMap (𝓞 E) E).range

def SpLat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (m k n d D : ℕ) (J : Matrix (Fin m) (Fin m) E)
    (M : Submodule (𝓞 E) (Fin m → E)) (V : Matrix (Fin m) (Fin k) E) (U : Matrix (Fin m) (Fin n) E),
    (J, M) ∈ Lat E m d → (∀ i, (fun r => V r i) ∈ M) → 1 ≤ D →
    (cT (starRingEnd E) V * J * V).det ≠ 0 →
    (∀ i j, (D : E) * (cT (starRingEnd E) V * J * V)⁻¹ i j ∈ (algebraMap (𝓞 E) E).range) →
    cT (starRingEnd E) V * J * U = 0 → Function.Injective U.mulVec →
    (∀ w : Fin m → E, (cT (starRingEnd E) V * J) *ᵥ w = 0 → ∃ y, U *ᵥ y = w) →
    (cT (starRingEnd E) U * J * U, M.comap ((Matrix.mulVecLin U).restrictScalars (𝓞 E))) ∈ Lat E n (d * D) ∧
    ∀ z ∈ M, ∃ c : Fin k → E, (∀ i, c i ∈ (algebraMap (𝓞 E) E).range) ∧ ∃ y : Fin n → E, U *ᵥ y ∈ M ∧
      (D : E) • z = V *ᵥ c + U *ᵥ y

def SpOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (m k : ℕ), 1 ≤ k → (∀ j < m, HL E j) →
    ∀ d : ℕ, 1 ≤ d → ∀ Γ : Matrix (Fin k) (Fin k) E, Γ.det ≠ 0 → FinCl (SplitSet E m k d {Γ})

theorem partSplit_of_one (h : SpOne) : PartSplit := by
  unfold PartSplit
  unfold SpOne at h
  intro F E _ _ _ _ _ _ _ m k hk hHL d hd G hG hdet

  have h1 : ∀ Γ ∈ G, FinCl (SplitSet E m k d {Γ}) := fun Γ hΓ => h E m k hk hHL d hd Γ (hdet Γ hΓ)
  choose T hTfin hT using h1
  refine ⟨⋃ (Γ) (hΓ : Γ ∈ G), T Γ hΓ, hG.biUnion' hTfin, ?_⟩
  rintro p ⟨hpL, v, hv, hvG⟩
  obtain ⟨q, hq, hiso⟩ := hT _ hvG p ⟨hpL, v, hv, Set.mem_singleton _⟩
  exact ⟨q, Set.mem_iUnion₂.mpr ⟨_, hvG, hq⟩, hiso⟩

end PIW.AdelClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.UnitsModSq
section
noncomputable section

namespace PIW.AdelClassFin

open NumberField NumberField.Units

theorem units_mod_sq (F : Type) [Field F] [NumberField F] :
    ∃ U : Set F, U.Finite ∧ ∀ c : (𝓞 F)ˣ, ∃ w ∈ U, ∃ v : (𝓞 F)ˣ,
      algebraMap (𝓞 F) F (c : 𝓞 F) = w * algebraMap (𝓞 F) F (v : 𝓞 F) ^ 2 := by
  classical
  let g : torsion F × (Fin (rank F) → Fin 2) → F := fun p =>
    algebraMap (𝓞 F) F (((p.1 : (𝓞 F)ˣ) * ∏ i, fundSystem F i ^ (((p.2 i : ℕ) : ℤ)) : (𝓞 F)ˣ) : 𝓞 F)
  refine ⟨Set.range g, Set.finite_range g, fun c => ?_⟩
  obtain ⟨⟨ζ, e⟩, he, -⟩ := exist_unique_eq_mul_prod F c
  dsimp only at he
  let f : Fin (rank F) → Fin 2 := fun i => ⟨(e i % 2).toNat, by omega⟩
  refine ⟨g (ζ, f), Set.mem_range_self _, ∏ i, fundSystem F i ^ (e i / 2), ?_⟩
  have key : c = ((ζ : (𝓞 F)ˣ) * ∏ i, fundSystem F i ^ (((f i : ℕ) : ℤ))) *
      (∏ i, fundSystem F i ^ (e i / 2)) ^ 2 := by
    rw [he, mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sq, ← zpow_add, ← zpow_add]
    congr 1
    have h2 : (((f i : ℕ) : ℤ)) = e i % 2 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
    omega
  rw [key, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow]

theorem partUnits : PartUnits := by
  intro F E _ _ _ _ _ _ hc C
  classical
  obtain ⟨U, hUf, hU⟩ := units_mod_sq F
  let S : Set (Ideal (𝓞 E)) := {I | Ideal.absNorm I ≤ ⌊C⌋₊}
  have hSf : S.Finite := Ideal.finite_setOfPred_absNorm_le _
  let P : Ideal (𝓞 E) → Prop := fun I => ∃ y : 𝓞 E, I = Ideal.span {y} ∧
    star (algebraMap (𝓞 E) E y) = algebraMap (𝓞 E) E y ∧ y ≠ 0
  let rep : Ideal (𝓞 E) → E := fun I => if h : P I then algebraMap (𝓞 E) E h.choose else 1
  refine ⟨Set.image2 (fun w I => algebraMap F E w * rep I) U S \ {0}, (hUf.image2 _ hSf).sdiff,
    fun h => h.2 rfl, ?_⟩
  rintro a ⟨x, rfl⟩ hstar ha hN
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := RingOfIntegers.coe_injective
  have hx0 : x ≠ 0 := by rintro rfl; exact ha (map_zero _)
  have hxS : Ideal.span {x} ∈ S := by
    show Ideal.absNorm _ ≤ _
    rw [Ideal.absNorm_span_singleton]
    apply Nat.le_floor
    have h1 := Algebra.coe_norm_int x
    rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h1]
    exact hN
  have hP : P (Ideal.span {x}) := ⟨x, rfl, hstar, hx0⟩
  obtain ⟨hyI, hys, hy0⟩ := hP.choose_spec
  have hrep : rep (Ideal.span {x}) = algebraMap (𝓞 E) E hP.choose := dif_pos hP
  obtain ⟨w, hw⟩ : Associated hP.choose x := Ideal.span_singleton_eq_span_singleton.mp hyI.symm
  have hyE : algebraMap (𝓞 E) E hP.choose ≠ 0 := fun h => hy0 (hinj (h.trans (map_zero _).symm))
  have h1 : algebraMap (𝓞 E) E x =
      algebraMap (𝓞 E) E hP.choose * algebraMap (𝓞 E) E (w : 𝓞 E) := by
    rw [← map_mul]
    exact congrArg _ hw.symm
  have hWs : star (algebraMap (𝓞 E) E (w : 𝓞 E)) = algebraMap (𝓞 E) E (w : 𝓞 E) := by
    refine mul_left_cancel₀ hyE ?_
    calc algebraMap (𝓞 E) E hP.choose * star (algebraMap (𝓞 E) E (w : 𝓞 E))
        = star (algebraMap (𝓞 E) E hP.choose) * star (algebraMap (𝓞 E) E (w : 𝓞 E)) := by
          rw [hys]
      _ = star (algebraMap (𝓞 E) E hP.choose * algebraMap (𝓞 E) E (w : 𝓞 E)) :=
          (star_mul' _ _).symm
      _ = _ := by rw [← h1, hstar, h1]
  obtain ⟨c, hcW⟩ := (hc.fixed _).1 hWs
  have hWW' : algebraMap (𝓞 E) E (w : 𝓞 E) * algebraMap (𝓞 E) E ((w⁻¹ : (𝓞 E)ˣ) : 𝓞 E) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hcW, map_zero, zero_mul] at hWW'
    exact zero_ne_one hWW'
  have hW' : algebraMap (𝓞 E) E ((w⁻¹ : (𝓞 E)ˣ) : 𝓞 E) = algebraMap F E c⁻¹ := by
    rw [map_inv₀, hcW]
    exact eq_inv_of_mul_eq_one_right hWW'
  have hci : IsIntegral ℤ c := by
    refine (isIntegral_algebraMap_iff (B := E) ).mp ?_
    rw [hcW]
    exact (w : 𝓞 E).2
  have hci' : IsIntegral ℤ c⁻¹ := by
    refine (isIntegral_algebraMap_iff (B := E) ).mp ?_
    rw [← hW']
    exact ((w⁻¹ : (𝓞 E)ˣ) : 𝓞 E).2
  let cu : (𝓞 F)ˣ :=
    { val := ⟨c, hci⟩
      inv := ⟨c⁻¹, hci'⟩
      val_inv := RingOfIntegers.ext (show c * c⁻¹ = 1 from mul_inv_cancel₀ hc0)
      inv_val := RingOfIntegers.ext (show c⁻¹ * c = 1 from inv_mul_cancel₀ hc0) }
  obtain ⟨w0, hw0U, v, hv⟩ := hU cu
  have hcv : c = w0 * algebraMap (𝓞 F) F (v : 𝓞 F) ^ 2 := hv
  let u : (𝓞 E)ˣ := Units.map (RingOfIntegers.mapRingHom (algebraMap F E)).toMonoidHom v
  have hu : algebraMap (𝓞 E) E (u : 𝓞 E) = algebraMap F E (algebraMap (𝓞 F) F (v : 𝓞 F)) := rfl
  have hus : star (algebraMap (𝓞 E) E (u : 𝓞 E)) = algebraMap (𝓞 E) E (u : 𝓞 E) :=
    (hc.fixed _).2 ⟨_, hu.symm⟩
  have main : algebraMap (𝓞 E) E x = star (algebraMap (𝓞 E) E (u : 𝓞 E)) *
      algebraMap (𝓞 E) E (u : 𝓞 E) * (algebraMap F E w0 * rep (Ideal.span {x})) := by
    rw [hus, hrep, h1, ← hcW, hcv, map_mul, map_pow, hu]
    ring
  refine ⟨u, algebraMap F E w0 * rep (Ideal.span {x}),
    ⟨Set.mem_image2_of_mem hw0U hxS, fun h0 => ha ?_⟩, main⟩
  rw [main]
  rw [Set.mem_singleton_iff.mp h0, mul_zero]

end PIW.AdelClassFin
end
end

