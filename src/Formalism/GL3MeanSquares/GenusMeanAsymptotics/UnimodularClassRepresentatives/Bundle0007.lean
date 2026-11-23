module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassSt
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomScale
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0004
public import Mathlib

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CovolumeIntegerLatticeEq
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem nrComplexPlaces_eq_fDeg (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    InfinitePlace.nrComplexPlaces K = Formalism.HermitianLatticesTheory.fDeg K := by
  have h0 : InfinitePlace.nrRealPlaces K = 0 := by
    classical
    unfold InfinitePlace.nrRealPlaces
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h0, zero_add]

theorem finrank_eq_two_fDeg (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
  rw [← nrComplexPlaces_eq_fDeg hK]
  have h0 : InfinitePlace.nrRealPlaces K = 0 := by
    classical
    unfold InfinitePlace.nrRealPlaces
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  have := InfinitePlace.card_add_two_mul_card_eq_rank K
  omega

theorem vInv_pos (K : Type) [Field K] [NumberField K] : 0 < Formalism.HermitianLatticesTheory.vInv K := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have hd : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero K)
  exact div_pos (Real.rpow_pos_of_pos hd _) two_pos

theorem covolume_integerLattice_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| =
      Formalism.HermitianLatticesTheory.vInv K ^ Formalism.HermitianLatticesTheory.fDeg K := by
  rw [nrComplexPlaces_eq_fDeg hK]
  unfold Formalism.HermitianLatticesTheory.vInv
  have hpos : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos
  have hf : (Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [div_pow, ← Real.rpow_natCast (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg K))),
    ← Real.rpow_mul (abs_nonneg _), Real.sqrt_eq_rpow]
  have e : (1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg K) * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) = 1 / 2 := by
    field_simp
  rw [e, inv_pow]
  ring

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthTransfer
section
noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA Module

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem finrank_cutW_lt {W : Submodule K V} {x : V} (hx : x ∈ W) (hxx : h x x ≠ 0) :
    finrank K (cutW h W x) < finrank K W := by
  unfold cutW
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne inf_le_left fun heq => hxx ?_
  have hmem : x ∈ W ⊓ LinearMap.ker (h x) := by
    rw [heq]
    exact hx
  exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2

theorem sd_main (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) (n : ℕ) :
    ∀ (W₁ W₂ : Submodule K V) (M N : AddSubgroup V) (φ : V ≃ₗ[K] V), finrank K W₁ ≤ n →
      IsSD S h W₁ M → IsSD S h W₂ N → φ ∈ Formalism.HermitianLatticesTheory.isom h → (∀ v, v ∈ W₁ ↔ φ v ∈ W₂) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  induction n with
  | zero =>
    intro W₁ W₂ M N φ hn hM hN hφ hW
    have hbot : W₁ = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)
    refine ⟨φ, hφ, fun _ _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · have : v = 0 := by
        have := hM.le v hv
        rwa [hbot, Submodule.mem_bot] at this
      rw [this, map_zero]
      exact N.zero_mem
    · have : v = 0 := by
        have := (hW v).mpr (hN.le _ hv)
        rwa [hbot, Submodule.mem_bot] at this
      rw [this]
      exact M.zero_mem
  | succ n ih =>
    intro W₁ W₂ M N φ hn hM hN hφ hW
    by_cases hbot : W₁ = ⊥
    · exact ih W₁ W₂ M N φ (by rw [hbot]; simp) hM hN hφ hW
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hφ' : ∀ a b, h (φ a) (φ b) = h a b := hφ
    obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0
    obtain ⟨X, hX, hXu⟩ := hN.exists_norm hS hπ hs hd ((hW x).mp (hM.le x hx)) hu (hφ' x x)
    obtain ⟨φ', hφ'i, hφ'x, hφ'W, hφ'fix⟩ := exists_prep hs hd hφ hW (hM.le x hx) (hN.le X hX)
      hXu.symm
    obtain ⟨g, hg, hgfix, hgM⟩ := ih _ _ _ _ φ'
      (by have := finrank_cutW_lt (h := h) (hM.le x hx) hu.1; omega)
      (hM.cut hx hu) (hN.cut hX (by rw [hXu]; exact hu)) hφ'i hφ'W
    have hgx : g x = X := by
      rw [hgfix x fun w hw => symm_zero hs (mem_cutW.mp hw).2, hφ'x]
    refine ⟨g, hg, fun v hv => ?_, mem_iff_of_cut hM.toIsLatIn hN.toIsLatIn hx hX hu hg hgx hgM⟩
    rw [hgfix v fun w hw => hv w (mem_cutW.mp hw).1, hφ'fix v hv]

theorem exists_orth_transfer (hd : ∀ x, h x x = 0 → x = 0) {W₁ W₂ : Submodule K V}
    {ψ : V ≃ₗ[K] V} (hψ : ∀ a b, h (ψ a) (ψ b) = h a b) (hW : ∀ v ∈ W₁, ψ v ∈ W₂) {z₁ z₂ ξ : V}
    (hz₁ : z₁ ∈ W₁) (hz₁0 : z₁ ≠ 0) (hz₂ : z₂ ∈ W₂) (hz₂0 : z₂ ≠ 0) (hξ : ξ ∈ W₁) (hξ0 : ξ ≠ 0)
    (hzξ : h z₁ ξ = 0) : ∃ η ∈ W₂, η ≠ 0 ∧ h z₂ η = 0 := by
  have ha : ψ z₁ ∈ W₂ := hW z₁ hz₁
  have hb : ψ ξ ∈ W₂ := hW ξ hξ
  have haa : h (ψ z₁) (ψ z₁) ≠ 0 := by
    rw [hψ]
    exact fun h0 => hz₁0 (hd z₁ h0)
  have hb0 : ψ ξ ≠ 0 := fun h0 => hξ0 (ψ.injective (h0.trans (map_zero ψ).symm))
  have hab : h (ψ z₁) (ψ ξ) = 0 := by
    rw [hψ]
    exact hzξ
  by_cases h0 : h z₂ (ψ z₁) = 0
  · exact ⟨ψ z₁, ha, fun ha0 => haa (by simp [ha0]), h0⟩
  · refine ⟨(h z₂ (ψ ξ)) • ψ z₁ - (h z₂ (ψ z₁)) • ψ ξ,
      W₂.sub_mem (W₂.smul_mem _ ha) (W₂.smul_mem _ hb), ?_, ?_⟩
    · intro heq
      have hc := congrArg (h (ψ z₁)) heq
      simp only [map_sub, map_smul, smul_eq_mul, hab, mul_zero, sub_zero, map_zero] at hc
      rcases mul_eq_zero.mp hc with hb' | hb'
      · rw [hb', zero_smul, zero_sub, neg_eq_zero, smul_eq_zero] at heq
        exact heq.elim h0 hb0
      · exact haa hb'
    · simp only [map_sub, map_smul, smul_eq_mul]
      ring

theorem IsASD.z_ne {W : Submodule K V} {M : AddSubgroup V} {z : V} (hM : IsASD S π h W M z) :
    z ≠ 0 := by
  intro hz
  exact hM.z_norm_ne (by simp [hz])

theorem IsASD.mem_iff_of_line (hπ : IsUnif S π) {W : Submodule K V} {M : AddSubgroup V} {z : V}
    (hM : IsASD S π h W M z) (hline : ¬ ∃ ξ ∈ W, ξ ≠ 0 ∧ h z ξ = 0) :
    (∀ v ∈ W, v = (h z v * (h z z)⁻¹) • z) ∧ ∀ v, v ∈ M ↔ ∃ c ∈ S, v = c • z := by
  have hζ := hM.z_norm_ne
  have h1 : ∀ v ∈ W, v = (h z v * (h z z)⁻¹) • z := by
    intro v hv
    by_contra hne
    apply hline
    refine ⟨v - (h z v * (h z z)⁻¹) • z, W.sub_mem hv (W.smul_mem _ (hM.le z hM.z_mem)),
      sub_ne_zero.mpr hne, ?_⟩
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  refine ⟨h1, fun v => ⟨fun hv => ?_, ?_⟩⟩
  · exact ⟨_, mul_inv_mem_of_dv hπ (hM.z_rad v hv) hM.z_norm, h1 v (hM.le v hv)⟩
  · rintro ⟨c, hc, rfl⟩
    exact hM.smul_mem c hc z hM.z_mem

theorem asd_base (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    {W₁ W₂ : Submodule K V} {M N : AddSubgroup V} {z₁ z₂ : V} {φ : V ≃ₗ[K] V}
    (hM : IsASD S π h W₁ M z₁) (hN : IsASD S π h W₂ N z₂) (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h)
    (hW : ∀ v, v ∈ W₁ ↔ φ v ∈ W₂) (h1 : ¬ ∃ ξ ∈ W₁, ξ ≠ 0 ∧ h z₁ ξ = 0)
    (h2 : ¬ ∃ ξ ∈ W₂, ξ ≠ 0 ∧ h z₂ ξ = 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  have hφ' : ∀ a b, h (φ a) (φ b) = h a b := hφ
  obtain ⟨-, hMl⟩ := hM.mem_iff_of_line hπ h1
  obtain ⟨hW₂l, hNl⟩ := hN.mem_iff_of_line hπ h2
  have hζ₂ := hN.z_norm_ne
  obtain ⟨l, hl⟩ : ∃ l : K, φ z₁ = l • z₂ := ⟨_, hW₂l _ ((hW z₁).mp (hM.le _ hM.z_mem))⟩
  have hnorm : h z₁ z₁ = star l * l * h z₂ z₂ := by
    rw [← hφ', hl]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
    ring
  have hNl' : IsUnitIn S (star l * l) := by
    have e : star l * l = h z₁ z₁ * π⁻¹ * (h z₂ z₂ * π⁻¹)⁻¹ := by
      rw [hnorm]
      have := hπ.ne
      field_simp
    rw [e]
    exact unit_mul hM.z_norm (unit_inv hN.z_norm)
  obtain ⟨b, hb, hlb⟩ := exists_norm_one_mul_mem hS hNl'.2.1
  have hlbu : IsUnitIn S (l * b) := by
    apply isUnitIn_of_mul (hS.star_mem _ hlb) hlb
    have e : star (l * b) * (l * b) = star l * l := by
      rw [star_mul']
      linear_combination (star l * l) * hb
    rw [e]
    exact hNl'
  obtain ⟨ψ, hψ, hψz, hψfix⟩ := exists_isom_scale hs hζ₂ hb
  have hgz : ψ (φ z₁) = (l * b) • z₂ := by rw [hl, map_smul, hψz, smul_smul]
  refine ⟨ψ * φ, mul_mem hψ hφ, fun v hv => ?_, fun v => ?_⟩
  · change ψ (φ v) = φ v
    apply hψfix
    have h3 : φ.symm z₂ ∈ W₁ := by rw [hW, φ.apply_symm_apply]; exact hN.le _ hN.z_mem
    have := hv _ h3
    rwa [← hφ', φ.apply_symm_apply] at this
  · change v ∈ M ↔ ψ (φ v) ∈ N
    rw [hMl, hNl]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c * (l * b), S.mul_mem hc hlb, by rw [map_smul, map_smul, hgz, smul_smul]⟩
    · rintro ⟨c, hc, hv⟩
      refine ⟨c * (l * b)⁻¹, S.mul_mem hc hlbu.2.2, ?_⟩
      apply φ.injective
      apply ψ.injective
      rw [hv, map_smul, map_smul, hgz, smul_smul, mul_assoc, inv_mul_cancel₀ hlbu.1, mul_one]

theorem asd_main (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) (n : ℕ) :
    ∀ (W₁ W₂ : Submodule K V) (M N : AddSubgroup V) (z₁ z₂ : V) (φ : V ≃ₗ[K] V),
      finrank K W₁ ≤ n → IsASD S π h W₁ M z₁ → IsASD S π h W₂ N z₂ → φ ∈ Formalism.HermitianLatticesTheory.isom h →
      (∀ v, v ∈ W₁ ↔ φ v ∈ W₂) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  induction n with
  | zero =>
    intro W₁ W₂ M N z₁ z₂ φ hn hM hN hφ hW
    exfalso
    have hbot : W₁ = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)
    have := hM.le _ hM.z_mem
    rw [hbot, Submodule.mem_bot] at this
    exact hM.z_ne this
  | succ n ih =>
    intro W₁ W₂ M N z₁ z₂ φ hn hM hN hφ hW
    have hφ' : ∀ a b, h (φ a) (φ b) = h a b := hφ
    by_cases h1 : ∃ ξ ∈ W₁, ξ ≠ 0 ∧ h z₁ ξ = 0
    · obtain ⟨ξ, hξ, hξ0, hzξ⟩ := h1
      obtain ⟨η, hη, hη0, hzη⟩ := exists_orth_transfer hd hφ' (fun v hv => (hW v).mp hv)
        (hM.le _ hM.z_mem) hM.z_ne (hN.le _ hN.z_mem) hN.z_ne hξ hξ0 hzξ
      obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0 hzξ
      obtain ⟨w₀, hw₀, hw₀u⟩ := hN.exists_unit_norm hS hπ hs hd hη hη0 hzη
      obtain ⟨X, hX, hXu⟩ := hN.exists_norm hS hπ hs hd ((hW x).mp (hM.le x hx)) hu (hφ' x x)
        hw₀ hw₀u
      obtain ⟨φ', hφ'i, hφ'x, hφ'W, hφ'fix⟩ := exists_prep hs hd hφ hW (hM.le x hx) (hN.le X hX)
        hXu.symm
      obtain ⟨g, hg, hgfix, hgM⟩ := ih _ _ _ _ _ _ φ'
        (by have := finrank_cutW_lt (h := h) (hM.le x hx) hu.1; omega)
        (hM.cut hS hπ hs hx hu) (hN.cut hS hπ hs hX (by rw [hXu]; exact hu)) hφ'i hφ'W
      have hgx : g x = X := by
        rw [hgfix x fun w hw => symm_zero hs (mem_cutW.mp hw).2, hφ'x]
      refine ⟨g, hg, fun v hv => ?_, mem_iff_of_cut hM.toIsLatIn hN.toIsLatIn hx hX hu hg hgx hgM⟩
      rw [hgfix v fun w hw => hv w (mem_cutW.mp hw).1, hφ'fix v hv]
    · refine asd_base hS hπ hs hM hN hφ hW h1 ?_
      rintro ⟨η, hη, hη0, hzη⟩
      apply h1
      have hsym : ∀ a b, h (φ.symm a) (φ.symm b) = h a b := by
        intro a b
        rw [← hφ', φ.apply_symm_apply, φ.apply_symm_apply]
      exact exists_orth_transfer hd hsym
        (fun v hv => by rw [hW, φ.apply_symm_apply]; exact hv)
        (hN.le _ hN.z_mem) hN.z_ne (hM.le _ hM.z_mem) hM.z_ne hη hη0 hzη

end Formalism.HermitianLattices.Ext.L3.U0
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

section NoF

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem conjO_coe (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  rw [conjO_coe, conjO_coe, star_star]

theorem conjIdeal_eq_comap (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.comap (conjO K) := by
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro r ⟨s, hs, hrs⟩
    have hr : conjO K r = s := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      have h2 : (r : K) = star (s : K) := hrs
      rw [h2, star_star]
    show conjO K r ∈ P
    rw [hr]
    exact hs
  · intro x hx
    apply Ideal.subset_span
    refine ⟨conjO K x, hx, ?_⟩
    show (x : K) = star ((conjO K x : 𝓞 K) : K)
    rw [conjO_coe, star_star]

theorem exists_sub_conjO_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ θ : 𝓞 K, θ - conjO K θ ∉ P := by
  obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
  refine ⟨θ, ?_⟩
  have hθt : conjO K θ = t := by
    apply RingOfIntegers.ext
    rw [conjO_coe]
    exact ht.symm
  rwa [hθt]

omit [StarRing K] in
theorem absNorm_eq_card (I : Ideal (𝓞 K)) : Ideal.absNorm I = Nat.card (𝓞 K ⧸ I) := by
  first
  | rfl
  | (rw [Ideal.absNorm_apply]; rfl)
  | (rw [Ideal.absNorm_apply, Submodule.cardQuot_apply])

theorem conjIdeal_isMaximal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).IsMaximal := by
  rw [conjIdeal_eq_comap]
  haveI := hP
  exact Ideal.comap_isMaximal_of_surjective (conjO K) (fun y => ⟨conjO K y, conjO_conjO y⟩)

theorem conjIdeal_conjIdeal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = P := by
  ext x
  simp only [conjIdeal_eq_comap, Ideal.mem_comap, conjO_conjO]

theorem conjIdeal_eq_map (P : Ideal (𝓞 K)) : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.map (conjO K) := by
  rw [conjIdeal_eq_comap]
  apply le_antisymm
  · intro x hx
    have h := Ideal.mem_map_of_mem (conjO K) (show conjO K x ∈ P from hx)
    rwa [conjO_conjO] at h
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simpa only [Ideal.mem_comap, conjO_conjO] using hx

theorem absNorm_conjIdeal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (P : Ideal (𝓞 K)) :
    Ideal.absNorm (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = Ideal.absNorm P := by
  rw [absNorm_eq_card, absNorm_eq_card]
  let e : 𝓞 K ≃+* 𝓞 K :=
    { conjO K with
      invFun := conjO K
      left_inv := fun x => conjO_conjO x
      right_inv := fun x => conjO_conjO x }
  have h : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [conjIdeal_eq_map]
    rfl
  exact (Nat.card_congr (Ideal.quotientEquiv P _ e h).toEquiv).symm

theorem exists_sq_absNorm_of_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    ∃ q : ℕ, Ideal.absNorm P = q ^ 2 := by
  rw [conjIdeal_eq_comap] at hc
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [absNorm_eq_card]
  exact SplitPrimeIdeals.exists_sq_card_quot conjO_conjO hP hc hθ

end NoF

section WithF

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem conjO_eq_iff_mem_range (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (x : 𝓞 K) :
    conjO K x = x ↔ x ∈ Set.range (algebraMap (𝓞 F) (𝓞 K)) := by
  constructor
  · intro hx
    have hfix : star (x : K) = x := by rw [← conjO_coe, hx]
    obtain ⟨a, ha⟩ := (hF _).1 hfix
    have hint : IsIntegral ℤ (algebraMap F K a) := by
      rw [ha]
      first
      | exact RingOfIntegers.isIntegral_coe x
      | exact x.2
    have ha' : IsIntegral ℤ a := (isIntegral_algebraMap_iff ).1 hint
    refine ⟨⟨a, ha'⟩, ?_⟩
    apply RingOfIntegers.ext
    show algebraMap F K a = (x : K)
    exact ha
  · rintro ⟨y, rfl⟩
    apply RingOfIntegers.ext
    rw [conjO_coe]
    have hy : ((algebraMap (𝓞 F) (𝓞 K) y : 𝓞 K) : K) = algebraMap F K (y : F) := rfl
    rw [hy]
    exact (hF _).2 ⟨_, rfl⟩

theorem comap_eq_comap_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P Q : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hQ : Q.IsMaximal) :
    P.comap (algebraMap (𝓞 F) (𝓞 K)) = Q.comap (algebraMap (𝓞 F) (𝓞 K)) ↔ Q = P ∨ Q = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  rw [conjIdeal_eq_comap]
  exact SplitPrimeIdeals.comap_eq_comap_iff conjO_conjO (conjO_eq_iff_mem_range hF) hP hQ

theorem exists_maximal_over (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 := by
  haveI := h𝔭
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 K)) := by
    first
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
    | exact FaithfulSMul.algebraMap_injective _ _
    | (intro a b hab
       apply RingOfIntegers.ext
       apply (algebraMap F K).injective
       exact congrArg (fun z : 𝓞 K => (z : K)) hab)
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔭 := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
    exact bot_le
  exact Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭 hker

theorem absNorm_comap_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 = Ideal.absNorm P := by
  rw [conjIdeal_eq_comap] at hc
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [absNorm_eq_card, absNorm_eq_card]
  exact SplitPrimeIdeals.card_quot_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ

theorem absNorm_comap_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) = Ideal.absNorm P := by
  rw [conjIdeal_eq_comap] at hc
  rw [absNorm_eq_card, absNorm_eq_card]
  exact SplitPrimeIdeals.card_quot_split conjO_conjO (conjO_eq_iff_mem_range hF) hP hc

theorem etaF_comap (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    etaF K F (P.comap (algebraMap (𝓞 F) (𝓞 K))) = if Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P then -1 else 1 := by
  rw [conjIdeal_eq_comap]
  unfold etaF
  by_cases hc : P.comap (conjO K) = P
  · obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
    rw [SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ, if_pos hP.isPrime,
      if_pos hc]
  · rw [if_neg (SplitPrimeIdeals.not_isPrime_map_of_split conjO_conjO (conjO_eq_iff_mem_range hF) hP hc),
      if_neg hc]

end WithF

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

def TotPos {K : Type*} [Field K] (a : K) : Prop :=
  ∀ φ : K →+* ℂ, 0 < (φ a).re

def gram {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {n : ℕ}
    (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin n → V) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => h (e i) (e j)

def HermRepUnram : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ a b n : K, star a = a → star b = b → star n = n → TotPos a → TotPos b → TotPos n →
      ∃ s t : K, a * (s * star s) + b * (t * star t) = n

def OrthBasisPos : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
      h.IsSymm → IsTotPosDef h →
      ∃ e : Basis (Fin (finrank K V)) K V, (∀ i j, i ≠ j → h (e i) (e j) = 0) ∧
        ∀ i, star (h (e i) (e i)) = h (e i) (e i) ∧ TotPos (h (e i) (e i))

end Formalism.HermitianLattices.Ext.L3
end
end

