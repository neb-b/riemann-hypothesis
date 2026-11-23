module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0014

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.BordMulSM
section
noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def sM {a : ℕ} (π : Fin a → Fin a) (z : Fin a) (g : Fv F v ⊗[F] E) :
    Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E) :=
  Fin.snoc (α := fun _ => Fin (a + 1) → Fv F v ⊗[F] E)
    (fun k => Fin.snoc (α := fun _ => Fv F v ⊗[F] E)
      (fun j => if k = z ∨ j = z then 0 else if j = π k then 1 else 0) (if k = z then 1 else 0))
    (Fin.snoc (α := fun _ => Fv F v ⊗[F] E) (fun j => if j = z then 1 else 0) (-g))

theorem bord_mul_sM {a : ℕ} (G : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (π : Fin a → Fin a)
    (hπ : Function.Involutive π) (z : Fin a) (hπz : π z = z) (g : Fv F v ⊗[F] E) (d : Fin a → Fv F v ⊗[F] E)
    (hd : ∀ i, i ≠ z → d i = 1) (hdz : d z = g) (hG : ∀ i k, G i k = if k = π i then d i else 0) :
    bordM v G z * sM v π z g = 1 := by
  have hπz' : ∀ i, π i = z ↔ i = z := fun i => ⟨fun h => by rw [← hπ i, h, hπz], fun h => h ▸ hπz⟩
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.one_apply] <;>
    simp only [bordM, sM, Fin.snoc_castSucc, Fin.snoc_last, hG]
  all_goals simp [hπz', hπ _, (Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).ne', Fin.castSucc_inj]
  · refine Finset.sum_eq_zero (fun x _ => ?_)
    split_ifs <;> first | rfl | (exfalso; tauto)
  · rcases eq_or_ne i z with rfl | hi
    · simp [hπz, hdz]
    · have : z ≠ π i := fun h => hi ((hπz' i).1 h.symm)
      simp [this, hi]
  · rw [Finset.sum_eq_single (π i) (fun x _ hx => by simp [hx]) (by simp)]
    simp only [hπ i, hπz', if_true]
    rcases eq_or_ne i z with rfl | hi
    · by_cases hj : j = i
      · simp [hj]
      · simp [hj, Ne.symm hj]
    · rcases eq_or_ne j z with rfl | hj
      · simp [hi]
      · simp [hi, hj, hd i hi, eq_comm]

end PI.OmVf
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LeftInvOOf
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  Topology Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def LeftInvRes (a : ℕ) : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
  ∀ M : Matrix (Fin n) (Fin a) (Fv F v ⊗[F] E), (∀ k i, M k i ∈ OEv (E := E) v) →
    (∀ c : Fin a → Fv F v ⊗[F] E, (∀ k, Matrix.mulVec M c k ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v) →
    ∃ N0 : Matrix (Fin a) (Fin n) (Fv F v ⊗[F] E), ∃ B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E),
      (∀ i k, N0 i k ∈ OEv (E := E) v) ∧ (∀ i j, B i j ∈ OEv (E := E) v) ∧
      N0 * M = 1 + sc (E := E) v ϖ • B

theorem near_mulVec {a : ℕ} (ϖ : Fv F v) (B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (x : Fin a → Fv F v ⊗[F] E)
    (i : Fin a) :
    Matrix.mulVec (1 + sc (E := E) v ϖ • B) x i = x i + sc (E := E) v ϖ * ∑ j, B i j * x j := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem leftInvO_of (a : ℕ) (hR : LeftInvRes σ J ψ v (n := n) a) : LeftInvO σ J ψ v (n := n) a := by
  intro hS hUn M hM hsat
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  obtain ⟨h0, hπ, -⟩ := unif_spec v ϖ hϖ
  obtain ⟨N0, B, hN0, hB, hNB⟩ := hR hS hUn ϖ hϖ M hM hsat
  set C : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := 1 + sc (E := E) v ϖ • B with hCdef

  have hker : ∀ d : Fin a → Fv F v ⊗[F] E, Matrix.mulVec C d = 0 → d = 0 := by
    intro d hd
    funext i
    have hm : ∀ m : ℕ, sc (E := E) v (ϖ ^ m)⁻¹ * d i ∈ OEv (E := E) v := by
      intro m
      refine near_int v ϖ hϖ B hB (fun j => sc (E := E) v (ϖ ^ m)⁻¹ * d j) (fun j => ?_) i
      have := near_mulVec v ϖ B (sc (E := E) v (ϖ ^ m)⁻¹ • d) j
      rw [Matrix.mulVec_smul, ← hCdef, hd, smul_zero] at this
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [← this]
      exact oEv_zero v
    by_contra hne
    have hN : {x : Fv F v ⊗[F] E | x ≠ d i} ∈ 𝓝 (0 : Fv F v ⊗[F] E) := isOpen_ne.mem_nhds (Ne.symm hne)
    obtain ⟨k, hk⟩ := PI.VolStabSW.eventually_smul_sub (OEv (E := E) v) (isCompact_oEv v) (fun k => ϖ ^ k) hπ _ hN
    apply hk _ (hm k)
    show ϖ ^ k • (sc (E := E) v (ϖ ^ k)⁻¹ * d i) = d i
    rw [smul_eq_sc, ← mul_assoc, sc_mul, mul_inv_cancel₀ (pow_ne_zero _ h0), sc_one, one_mul]
  have hinj : Function.Injective (Matrix.mulVecLin C) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun d hd => hker d hd
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hsurj : Function.Surjective (Matrix.mulVecLin C) := by
    have hinj' : Function.Injective ((Matrix.mulVecLin C).restrictScalars (Fv F v)) := hinj
    exact (LinearMap.injective_iff_surjective (f := (Matrix.mulVecLin C).restrictScalars (Fv F v))).1 hinj'
  have hCu : IsUnit C := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hCd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hCu

  have hCi : ∀ i j, C⁻¹ i j ∈ OEv (E := E) v := by
    intro i j
    have hcol : ∀ l, (fun k => C⁻¹ k j) l + sc (E := E) v ϖ * ∑ k, B l k * (fun k => C⁻¹ k j) k ∈ OEv (E := E) v := by
      intro l
      rw [← near_mulVec v ϖ B (fun k => C⁻¹ k j) l, ← hCdef]
      have e : Matrix.mulVec C (fun k => C⁻¹ k j) l = (C * C⁻¹) l j := by
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [e, Matrix.mul_nonsing_inv C hCd, Matrix.one_apply]
      split_ifs
      · exact one_mem_O v
      · exact oEv_zero v
    exact near_int v ϖ hϖ B hB _ hcol i
  refine ⟨C⁻¹ * N0, fun i k => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    exact oEv_sum v _ _ fun l _ => oEv_mul v (hCi i l) (hN0 l k)
  · rw [Matrix.mul_assoc, hNB, Matrix.nonsing_inv_mul C hCd]

end PI.OmVd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Root
section
noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd IsLocalRing
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem exists_integral_root_of_quadratic (β γ ν : Fv F v) (hβ : β ∈ v.adicCompletionIntegers F) (hγ : γ ∈ v.adicCompletionIntegers F)
    (hγm : Valued.v γ < 1) (hν : ν ∈ v.adicCompletionIntegers F) :
    ∃ s ∈ v.adicCompletionIntegers F, β + (1 - γ * β) * s - γ * (1 - γ * β) * ν * s ^ 2 = 0 := by
  set b : v.adicCompletionIntegers F := ⟨β, hβ⟩
  set g : v.adicCompletionIntegers F := ⟨γ, hγ⟩
  set m : v.adicCompletionIntegers F := ⟨ν, hν⟩
  have hg : g ∈ maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨w, hw⟩
    have h1 : ((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) * g = 1 := by
      rw [← hw]; simp
    have h2 : ((((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v)) * γ = 1 := by
      have := congrArg (fun x : v.adicCompletionIntegers F => (x : Fv F v)) h1
      simpa using this
    have h3 : Valued.v ((((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 (Subtype.property _)
    have h4 := congrArg Valued.v h2
    rw [map_mul, map_one] at h4
    have : Valued.v ((((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v)) * Valued.v γ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' h3) hγm
    rw [h4] at this
    exact lt_irrefl _ this
  have hu : IsUnit (1 - g * b) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((maximalIdeal _).mul_mem_right b hg)
  open scoped WithZero Topology in
  open HeightOneSpectrum Filter in
  have hcomplete : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := by
    let R := 𝓞 F
    let L := F
    let w := v
    let Ow := v.adicCompletionIntegers F
    let Lw := v.adicCompletion F
    have lt_one_iff_le (g : ℤᵐ⁰) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
      induction g using WithZero.expRecOn with
      | zero => simp
      | exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

    have v_algebraMap (l : L) : Valued.v (algebraMap L Lw l) = w.valuation L l :=
      valuedAdicCompletion_eq_valuation' w l

    have exists_unif : ∃ π : Ow, Valued.v (π : Lw) = WithZero.exp (-1 : ℤ) := by
      obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
      have h : Valued.v (algebraMap L Lw π) = WithZero.exp (-1 : ℤ) := by
        rw [v_algebraMap, hπ]
      refine ⟨⟨algebraMap L Lw π, ?_⟩, h⟩
      rw [mem_adicCompletionIntegers, h]
      exact ((lt_one_iff_le _).2 le_rfl).le

    have mem_max_iff (x : Ow) :
        x ∈ IsLocalRing.maximalIdeal Ow ↔ Valued.v (x : Lw) < 1 := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        adicCompletionIntegers.isUnit_iff_valued_eq_one]
      have : Valued.v (x : Lw) ≤ 1 := (mem_adicCompletionIntegers R L w).1 x.2
      exact ⟨fun h => lt_of_le_of_ne this h, fun h => h.ne⟩

    have max_eq_span {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) :
        IsLocalRing.maximalIdeal Ow = Ideal.span {π} := by
      ext x
      rw [mem_max_iff, Ideal.mem_span_singleton, lt_one_iff_le, ← hπ]
      exact (adicCompletionIntegers.integers L w).le_iff_dvd

    have mem_max_pow_iff {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) (x : Ow) (n : ℕ) :
        x ∈ IsLocalRing.maximalIdeal Ow ^ n ↔ Valued.v (x : Lw) ≤ Valued.v (π : Lw) ^ n := by
      rw [max_eq_span hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      have := (adicCompletionIntegers.integers L w).le_iff_dvd (x := x) (y := π ^ n)
      rw [map_pow, map_pow] at this
      exact this.symm

    obtain ⟨π, hπ⟩ := exists_unif
    have hπ1 : ‖(π : Lw)‖ < 1 := by
      rw [Valued.toNormedField.norm_lt_one_iff]
      exact (lt_one_iff_le _).2 hπ.le
    have hπ0 : (π : Lw) ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hr0 : 0 < ‖(π : Lw)‖ := norm_pos_iff.mpr hπ0
    have key : ∀ (n : ℕ) (x y : Ow),
        x ≡ y [SMOD ((IsLocalRing.maximalIdeal Ow) ^ n • ⊤ : Submodule Ow Ow)] ↔
          ‖(x : Lw) - y‖ ≤ ‖(π : Lw)‖ ^ n := by
      intro n x y
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_max_pow_iff hπ,
        ← map_pow, ← Valued.toNormedField.norm_le_iff]
      simp only [norm_pow]
      rfl
    refine { haus' := ?_, prec' := ?_ }
    · intro x hx
      have h : ∀ n : ℕ, ‖(x : Lw)‖ ≤ ‖(π : Lw)‖ ^ n := fun n => by
        simpa using (key n x 0).mp (hx n)
      have hx0 : ‖(x : Lw)‖ ≤ 0 :=
        ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hπ1) h
      exact Subtype.ext (norm_le_zero_iff.mp hx0)
    · intro f hf
      have hc : ∀ n : ℕ, dist (f n : Lw) (f (n + 1)) ≤ 1 * ‖(π : Lw)‖ ^ n := fun n => by
        rw [dist_eq_norm, one_mul]
        exact (key n _ _).mp (hf n.le_succ)
      obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ 1 hπ1 hc)
      have hl1 : ‖l‖ ≤ 1 := le_of_tendsto' hl.norm (fun n =>
        Valued.toNormedField.norm_le_one_iff.mpr (f n).2)
      refine ⟨⟨l, Valued.toNormedField.norm_le_one_iff.mp hl1⟩, fun n => ?_⟩
      rw [key]
      have ht : Tendsto (fun m => ‖(f n : Lw) - f m‖) atTop (𝓝 ‖(f n : Lw) - l‖) :=
        (tendsto_const_nhds.sub hl).norm
      exact le_of_tendsto ht (eventually_atTop.mpr ⟨n, fun m hm => (key n _ _).mp (hf hm)⟩)

  letI := hcomplete
  haveI : HenselianLocalRing (v.adicCompletionIntegers F) := ⟨fun f hf a h₁ h₂ => HenselianRing.is_henselian f hf a h₁ (h₂.map _)⟩
  obtain ⟨s, hs⟩ := PI.OmVf.quad_root (-(g * (1 - g * b) * m)) (1 - g * b) b
    (neg_mem ((maximalIdeal _).mul_mem_right m ((maximalIdeal _).mul_mem_right _ hg))) hu
  refine ⟨s, s.property, ?_⟩
  have := congrArg (fun x : v.adicCompletionIntegers F => (x : Fv F v)) hs
  simp only [b, g, m] at this
  push_cast at this
  linear_combination this
end PI.OmVf
end
end

