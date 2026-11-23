module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0015
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0016
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0018

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormLeOfMemIdeal
section
open NumberField Module
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxCube

open BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem absNorm_le_of_mem_ideal {b : Ideal (𝓞 F)} {n : 𝓞 F} (hn : n ∈ b) (h0 : n ≠ 0) :
    (Ideal.absNorm b : ℝ) ≤ (Ideal.absNorm (Ideal.span {n}) : ℝ) := by
  have h1 : Ideal.absNorm b ∣ Ideal.absNorm (Ideal.span {n}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem b).2 hn)
  have h2 : Ideal.absNorm (Ideal.span {n}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h0
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1

theorem absNorm_le_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {T : ℝ}
    {n : 𝓞 F} (hn : n ∈ boxSet K F T) (hb : n ∈ b) :
    (Ideal.absNorm b : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K :=
  (absNorm_le_of_mem_ideal hb (ne_zero_of_mem_boxSet hn)).trans (absNorm_le_of_mem hK hF hn)

theorem eq_of_close (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {δ : ℝ}
    (hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K ≤ (Ideal.absNorm b : ℝ)) {n n' : 𝓞 F} (hn : n ∈ b) (hn' : n' ∈ b)
    (hc : ∀ w : {w : InfinitePlace F // w.IsReal}, |rEmb w n - rEmb w n'| < δ) : n = n' := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  by_contra hne
  have h0 : n - n' ≠ 0 := sub_ne_zero.2 hne
  have h1 := absNorm_le_of_mem_ideal (b.sub_mem hn hn') h0
  rw [absNorm_eq_prod] at h1
  have hne' : (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}).Nonempty := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact ⟨⟨w, IsTotallyReal.isReal w⟩, Finset.mem_univ _⟩
  have h2 : ∏ w : {w : InfinitePlace F // w.IsReal}, |rEmb w (n - n')| <
      ∏ _w : {w : InfinitePlace F // w.IsReal}, δ := by
    refine Finset.prod_lt_prod_of_nonempty₀ (fun w _ => ?_) (fun w _ => ?_) hne'
    · rw [abs_pos]
      intro h3
      apply h0
      have : (InfinitePlace.embedding_of_isReal w.2) ((n - n' : 𝓞 F) : F) = 0 := h3
      rw [map_eq_zero] at this
      exact RingOfIntegers.coe_injective (by simpa using this)
    · rw [map_sub]
      exact hc w
  rw [Finset.prod_const, Finset.card_univ, card_real hK hF] at h2
  linarith

theorem abs_sub_lt_of_floor_eq {δ a a' : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (h : ⌊a / δ⌋₊ = ⌊a' / δ⌋₊) : |a - a'| < δ := by
  have h1 := Nat.floor_le (div_nonneg ha hδ.le)
  have h2 := Nat.lt_floor_add_one (a / δ)
  have h3 := Nat.floor_le (div_nonneg ha' hδ.le)
  have h4 := Nat.lt_floor_add_one (a' / δ)
  rw [h] at h1 h2
  have h5 : a / δ - a' / δ < 1 := by linarith
  have h6 : a' / δ - a / δ < 1 := by linarith
  rw [← sub_div, div_lt_one hδ] at h5 h6
  rw [abs_lt]
  constructor <;> linarith

theorem card_le_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {δ T : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K ≤ (Ideal.absNorm b : ℝ)) :
    Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} ≤ (⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K := by
  let W := {w : InfinitePlace F // w.IsReal}
  let g : {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} → (W → Fin (⌊T / δ⌋₊ + 1)) := fun n w =>
    ⟨⌊rEmb w n.1 / δ⌋₊, Nat.lt_succ_of_le (Nat.floor_le_floor
      (div_le_div_of_nonneg_right (((mem_boxSet_iff hK hF).1 n.2.1) w).2 hδ0.le))⟩
  have hg : Function.Injective g := by
    intro n n' h
    refine Subtype.ext (eq_of_close hK hF hδ n.2.2 n'.2.2 fun w => ?_)
    have h1 : ⌊rEmb w n.1 / δ⌋₊ = ⌊rEmb w n'.1 / δ⌋₊ := congrArg Fin.val (congrFun h w)
    exact abs_sub_lt_of_floor_eq hδ0 (((mem_boxSet_iff hK hF).1 n.2.1) w).1.le
      (((mem_boxSet_iff hK hF).1 n'.2.1) w).1.le h1
  have h1 := Nat.card_le_card_of_injective g hg
  have h2 : Nat.card (W → Fin (⌊T / δ⌋₊ + 1)) = (⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, card_real hK hF]
  rwa [h2] at h1

theorem fDeg_pos : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos

theorem card_box_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)}
    (hb : b ≠ ⊥) {T : ℝ} (hT0 : 0 ≤ T) :
    (Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} : ℝ) ≤
      2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm b : ℝ) := by
  have hf : Formalism.HermitianLatticesTheory.fDeg K ≠ 0 := (fDeg_pos (K := K)).ne'
  have hN : (0 : ℝ) < (Ideal.absNorm b : ℝ) := by
    have : Ideal.absNorm b ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.pos_of_ne_zero this
  by_cases he : IsEmpty {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b}
  · rw [Nat.card_of_isEmpty, Nat.cast_zero, ← mul_pow]
    positivity
  rw [not_isEmpty_iff] at he
  obtain ⟨n, hn, hnb⟩ := he
  have hT : 0 < T := by
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    exact (hn φ).1.trans_le (hn φ).2
  set δ : ℝ := (Ideal.absNorm b : ℝ) ^ ((Formalism.HermitianLatticesTheory.fDeg K : ℝ)⁻¹) with hδdef
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hN _
  have hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K = (Ideal.absNorm b : ℝ) := Real.rpow_inv_natCast_pow hN.le hf
  have hδT : δ ≤ T := by
    have := absNorm_le_pow hK hF hn hnb
    rw [← hδ] at this
    exact (pow_le_pow_iff_left₀ hδ0.le hT.le hf).1 this
  have h1 := card_le_pow hK hF (T := T) hδ0 hδ.le
  have h2 : ((⌊T / δ⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T / δ := by
    have h3 := Nat.floor_le (div_nonneg hT.le hδ0.le)
    have h4 : 1 ≤ T / δ := (one_le_div hδ0).2 hδT
    push_cast
    rw [mul_div_assoc]
    linarith
  calc (Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} : ℝ)
      ≤ (((⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((⌊T / δ⌋₊ + 1 : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K := by push_cast; rfl
    _ ≤ (2 * T / δ) ^ Formalism.HermitianLatticesTheory.fDeg K := pow_le_pow_left₀ (by positivity) h2 _
    _ = _ := by rw [div_pow, mul_pow, hδ]

end Formalism.HermitianLattices.Ext.L3.BoxCube
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ConjOMemConjIdeal
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

structure IsStep (P : Ideal (𝓞 K)) (A B : Submodule (𝓞 K) V) (y : V) : Prop where
  le : A ≤ B
  mem : y ∈ B
  notMem : y ∉ A
  smul : ∀ π ∈ P, π • y ∈ A
  gen : ∀ x ∈ B, ∃ c : 𝓞 K, x - c • y ∈ A

def col (I : Ideal (𝓞 K)) (z : 𝓞 K) : Ideal (𝓞 K) where
  carrier := {c | c * z ∈ I}
  add_mem' := fun {a c} ha hc => by
    change (a + c) * z ∈ I
    rw [add_mul]; exact I.add_mem ha hc
  zero_mem' := by change (0 : 𝓞 K) * z ∈ I; rw [zero_mul]; exact I.zero_mem
  smul_mem' := fun c a ha => by
    change (c • a) * z ∈ I
    rw [smul_eq_mul, mul_assoc]; exact I.mul_mem_left c ha

omit [StarRing K] in
theorem mem_col {I : Ideal (𝓞 K)} {z c : 𝓞 K} : c ∈ col I z ↔ c * z ∈ I := Iff.rfl

omit [StarRing K] in
theorem mem_of_col_eq_top {I : Ideal (𝓞 K)} {z : 𝓞 K} (h : col I z = ⊤) : z ∈ I := by
  have h1 : (1 : 𝓞 K) ∈ col I z := by
    rw [h]; exact Submodule.mem_top
  simpa using (mem_col.1 h1)

namespace IsStep

variable {P : Ideal (𝓞 K)} {A B : Submodule (𝓞 K) V} {y : V}

omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem mem_of_smul_mem (S : IsStep P A B y) (hP : P.IsMaximal) {c : 𝓞 K} (hc : c • y ∈ A) :
    c ∈ P := by
  by_contra hcP
  obtain ⟨r, π, hπ, hrc⟩ := hP.exists_inv hcP
  apply S.notMem
  have e : y = r • (c • y) + π • y := by
    rw [smul_smul, ← add_smul, hrc, one_smul]
  rw [e]
  exact A.add_mem (A.smul_mem r hc) (S.smul π hπ)

omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem change (S : IsStep P A B y) (hP : P.IsMaximal) {x₀ : V} (hx : x₀ ∈ B) (hn : x₀ ∉ A) :
    IsStep P A B x₀ := by
  obtain ⟨c, hc⟩ := S.gen x₀ hx
  have hcP : c ∉ P := by
    intro hcP
    apply hn
    have h0 := A.add_mem hc (S.smul c hcP)
    simpa using h0
  obtain ⟨r, π, hπ, hrc⟩ := hP.exists_inv hcP
  refine ⟨S.le, hx, hn, ?_, ?_⟩
  · intro p hp
    have h1 : p • x₀ = p • (x₀ - c • y) + c • (p • y) := by
      rw [smul_sub, smul_comm p c y, sub_add_cancel]
    rw [h1]
    exact A.add_mem (A.smul_mem p hc) (A.smul_mem c (S.smul p hp))
  · intro x hxB
    obtain ⟨d, hd⟩ := S.gen x hxB
    refine ⟨d * r, ?_⟩
    have key : d • y = (d * r * c) • y + (d * π) • y := by
      rw [← add_smul, show d * r * c + d * π = d * (r * c + π) by ring, hrc, mul_one]
    have h2 : x - (d * r) • x₀ = (x - d • y) - (d * r) • (x₀ - c • y) + d • (π • y) := by
      rw [smul_sub, smul_smul (d * r) c y, smul_smul d π y, key]
      abel
    rw [h2]
    exact A.add_mem (A.sub_mem hd (A.smul_mem _ hc)) (A.smul_mem d (S.smul π hπ))

end IsStep

omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem det_add_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (x : ι → V)
    (e : ι → K) (i₀ : ι) (he : e i₀ = 0) : b.det (fun k => x k + e k • x i₀) = b.det x := by
  rw [Basis.det_apply, Basis.det_apply, ← Matrix.det_transpose,
    ← Matrix.det_transpose (b.toMatrix x)]
  refine Matrix.det_eq_of_forall_row_eq_smul_add_const (fun k => e k) i₀ he ?_
  intro i j
  simp [Matrix.transpose_apply, Basis.toMatrix_apply, map_add (f := _), map_smul]

theorem conjO_mem_conjIdeal {P : Ideal (𝓞 K)} {π : 𝓞 K} (hπ : π ∈ P) :
    conjO K π ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  apply Ideal.subset_span
  exact ⟨π, hπ, by first | rfl | simp [conjO]⟩

theorem term_mem {P I : Ideal (𝓞 K)} {p₁ p₂ z : 𝓞 K} (h₁ : p₁ ∈ P) (h₂ : p₂ ∈ P) (hz : z ∈ I) :
    conjO K p₁ * p₂ * z ∈ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * I := by
  have h3 := Ideal.mul_mem_mul (Ideal.mul_mem_mul h₂ (conjO_mem_conjIdeal h₁)) hz
  rwa [mul_comm p₂ (conjO K p₁)] at h3

theorem step_ge (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {A B : Submodule (𝓞 K) V} {y : V} (S : IsStep P A B y)
    (hB : Formalism.HermitianLatticesTheory.IsIntegralLat h B) (b : Basis (Fin (finrank K V)) K V) :
    P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * discrIdeal h B ≤ discrIdeal h A := by
  have hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A := fun x hx w hw => hB x (S.le hx) w (S.le hw)
  have key : ∀ π ∈ P, ∀ ρ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P, ∀ z ∈ discrIdeal h B,
      π * ρ * z ∈ discrIdeal h A := by
    intro π hπ ρ hρ
    rw [conjIdeal_eq_comap, Ideal.mem_comap] at hρ
    suffices hle : discrIdeal h B ≤ Submodule.comap (LinearMap.mulLeft (𝓞 K) (π * ρ))
        (discrIdeal h A) from fun z hz => hle hz
    refine discrIdeal_le b fun x hx z hz => ?_
    change π * ρ * z ∈ discrIdeal h A
    by_cases hall : ∀ i, x i ∈ A
    · exact Ideal.mul_mem_left _ _ (mem_discrIdeal b hall hz)
    · push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have S' := S.change hP (hx i₀) hi₀
      choose c hc using fun k => S'.gen (x k) (hx k)
      let e : Fin (finrank K V) → K := fun k => if k = i₀ then 0 else - algebraMap (𝓞 K) K (c k)
      let x' : Fin (finrank K V) → V := fun k => x k + e k • x i₀
      have hdet : b.det x' = b.det x := det_add_smul b x e i₀ (by simp [e])
      have hx'0 : x' i₀ = x i₀ := by simp [x', e]
      have hx' : ∀ k, k ≠ i₀ → x' k ∈ A := by
        intro k hk
        have : x' k = x k - c k • x i₀ := by
          simp only [x', e, if_neg hk, neg_smul, algebraMap_smul]
          abel
        rw [this]; exact hc k
      have hup : ∀ a : 𝓞 K, b.det (Function.update x' i₀ (a • x i₀)) =
          algebraMap (𝓞 K) K a * b.det x := by
        intro a
        rw [← algebraMap_smul K a (x i₀), AlternatingMap.map_update_smul, ← hx'0,
          Function.update_eq_self, hdet, smul_eq_mul]
      refine mixed_mem hK hA b hx' (S'.smul _ hρ) (S'.smul _ hπ) ?_
      rw [hup, hup, map_mul, map_mul, hz, algebraMap_conjO, star_mul', star_star]
      ring
  rw [Ideal.mul_le]
  intro r hr z hz
  induction hr using Submodule.mul_induction_on' with
  | mem_mul_mem π hπ ρ hρ => exact key π hπ ρ hρ z hz
  | add a _ c _ ha hc => rw [add_mul]; exact Ideal.add_mem _ ha hc

end Formalism.HermitianLattices.Ext.L3.BallB
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNeZeroOfIsLattice
section
open NumberField Module nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem exists_ne_zero_of_isLattice {A : Submodule (𝓞 K) K} (hA : Submodule.IsFullLattice K A) :
    ∃ a ∈ A, a ≠ 0 := by
  by_contra hne
  push Not at hne
  have h2 : Submodule.span K (A : Set K) = ⊥ := by
    rw [Submodule.span_eq_bot]; exact hne
  have h3 : (1 : K) ∈ Submodule.span K (A : Set K) := by
    rw [hA.span_eq_top]; exact Submodule.mem_top
  rw [h2, Submodule.mem_bot] at h3
  exact one_ne_zero h3

theorem span_eq_top_of_ne_zero {A : Submodule (𝓞 K) K} {a : K} (ha : a ∈ A) (h0 : a ≠ 0) :
    Submodule.span K (A : Set K) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x = (x * a⁻¹) • a := by rw [smul_eq_mul, mul_assoc, inv_mul_cancel₀ h0, mul_one]
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ha)

theorem isLattice_mul {A B : Submodule (𝓞 K) K} (hA : Submodule.IsFullLattice K A)
    (hB : Submodule.IsFullLattice K B) : Submodule.IsFullLattice K (A * B) := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_isLattice hA
  obtain ⟨b, hb, hb0⟩ := exists_ne_zero_of_isLattice hB
  have := Submodule.IsLattice.of_fg K (hA.toIsLattice.fg.mul hB.toIsLattice.fg)
  exact ⟨span_eq_top_of_ne_zero (Submodule.mul_mem_mul ha hb) (mul_ne_zero ha0 hb0)⟩

theorem exists_inv {A : Submodule (𝓞 K) K} (hA : Submodule.IsFullLattice K A) :
    ∃ A' : Submodule (𝓞 K) K, Submodule.IsFullLattice K A' ∧ A' * A = 1 := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_isLattice hA
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨A, FractionalIdeal.isFractional_of_fg hA.toIsLattice.fg⟩
  have hI : I ≠ 0 := by
    intro h
    have h' : a ∈ (I : Submodule (𝓞 K) K) := ha
    rw [h, FractionalIdeal.coeToSubmodule_zero, Submodule.mem_bot] at h'
    exact ha0 h'
  have hmul : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) * A = 1 := by
    have e := congrArg (fun J : FractionalIdeal (𝓞 K)⁰ K => (J : Submodule (𝓞 K) K))
      (inv_mul_cancel₀ hI)
    have e2 : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) * (I : Submodule (𝓞 K) K) = 1 := by
      simpa only [FractionalIdeal.coeToSubmodule_mul, FractionalIdeal.coeToSubmodule_one] using e
    exact e2
  have := Submodule.IsLattice.of_fg K (FractionalIdeal.fg_of_isNoetherianRing le_rfl I⁻¹)
  refine ⟨_, ⟨?_⟩, hmul⟩
  have hne : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥ := by
    intro hb
    rw [hb, Submodule.bot_mul] at hmul
    have h1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.one_le.1 le_rfl
    rw [← hmul, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact span_eq_top_of_ne_zero hc hc0

def mulE (I J : Submodule (𝓞 K) K) (hJI : J * I = 1) :
    Submodule (𝓞 K) K ≃ Submodule (𝓞 K) K where
  toFun M := I * M
  invFun M := J * M
  left_inv M := by change J * (I * M) = M; rw [← mul_assoc, hJI, one_mul]
  right_inv M := by change I * (J * M) = M; rw [← mul_assoc, mul_comm I J, hJI, one_mul]

theorem gmap_mul (g : K ≃ₗ[K] K) (I M : Submodule (𝓞 K) K) : I * gmap g M = gmap g (I * M) := by
  have key : ∀ x y : K, g (x * y) = x * g y := fun x y => by
    simpa only [smul_eq_mul] using g.map_smul x y
  unfold gmap
  apply le_antisymm
  · refine Submodule.mul_le.2 fun i hi y hy => ?_
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨i * m, Submodule.mul_mem_mul hi hm, ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]
  · refine Submodule.map_le_iff_le_comap.2 (Submodule.mul_le.2 fun i hi m hm => ?_)
    rw [Submodule.mem_comap]
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]
    exact Submodule.mul_mem_mul hi (Submodule.mem_map_of_mem hm)

theorem ne_zero_of_mem_hcompl {p : Ideal (𝓞 K)} (hp : p.IsMaximal) {s : 𝓞 K}
    (hs : s ∈ hcompl (K := K) p) : s ≠ 0 := by
  intro h0
  exact Formalism.HermitianLatticesTheory.genusBasic_hS (K := K) p hp s hs (by rw [h0]; exact p.zero_mem)

theorem loc_mul {p : Ideal (𝓞 K)} (hp : p.IsMaximal) (I M : Submodule (𝓞 K) K) :
    I * loc (K := K) p M = loc (K := K) p (I * M) := by
  apply le_antisymm
  · refine Submodule.mul_le.2 fun i hi y hy => ?_
    have hy' : ∃ s ∈ hcompl (K := K) p, s • y ∈ M := hy
    obtain ⟨s, hs, hsy⟩ := hy'
    show ∃ s ∈ hcompl (K := K) p, s • (i * y) ∈ I * M
    refine ⟨s, hs, ?_⟩
    have e : s • (i * y) = i * (s • y) := by rw [Algebra.smul_def, Algebra.smul_def]; ring
    rw [e]
    exact Submodule.mul_mem_mul hi hsy
  · intro x hx
    have hx' : ∃ s ∈ hcompl (K := K) p, s • x ∈ I * M := hx
    obtain ⟨s, hs, hsx⟩ := hx'
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact ne_zero_of_mem_hcompl hp hs
    have hle : I * M ≤ (I * loc (K := K) p M).comap
        (LinearMap.mulLeft (𝓞 K) (algebraMap (𝓞 K) K s)⁻¹) := by
      refine Submodule.mul_le.2 fun i hi m hm => ?_
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
      have e : (algebraMap (𝓞 K) K s)⁻¹ * (i * m) = i * ((algebraMap (𝓞 K) K s)⁻¹ * m) := by ring
      rw [e]
      refine Submodule.mul_mem_mul hi ?_
      show ∃ t ∈ hcompl (K := K) p, t • ((algebraMap (𝓞 K) K s)⁻¹ * m) ∈ M
      refine ⟨s, hs, ?_⟩
      rw [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
      exact hm
    have h2 := hle hsx
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, Algebra.smul_def, ← mul_assoc,
      inv_mul_cancel₀ hs0, one_mul] at h2
    exact h2

theorem form_eq (h : K →ₗ⋆[K] K →ₗ[K] K) (x y : K) : h x y = star x * y * h 1 1 := by
  rw [show h x y = h (x • (1 : K)) (y • (1 : K)) by simp only [smul_eq_mul, mul_one],
    LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply]
  simp only [smul_eq_mul]
  ring

theorem mem_isom_iff {h : K →ₗ⋆[K] K →ₗ[K] K} (h1 : h 1 1 ≠ 0) (g : K ≃ₗ[K] K) :
    g ∈ isom h ↔ star (g 1) * g 1 = 1 := by
  have hg : ∀ x, g x = x * g 1 := fun x => by
    rw [show g x = g (x • (1 : K)) by rw [smul_eq_mul, mul_one], LinearEquiv.map_smul, smul_eq_mul]
  constructor
  · intro hm
    have hm' : ∀ x y, h (g x) (g y) = h x y := hm
    have e := hm' 1 1
    rw [form_eq h (g 1) (g 1)] at e
    exact mul_right_cancel₀ h1 (by rw [one_mul]; exact e)
  · intro he
    show ∀ x y, h (g x) (g y) = h x y
    intro x y
    rw [form_eq h (g x) (g y), form_eq h x y, hg x, hg y, star_mul']
    calc star x * star (g 1) * (y * g 1) * h 1 1 = star x * y * (star (g 1) * g 1) * h 1 1 := by ring
      _ = star x * y * h 1 1 := by rw [he, mul_one]

theorem mass_eq_of_lattices {h₁ h₂ : K →ₗ⋆[K] K →ₗ[K] K} (hn₁ : h₁ 1 1 ≠ 0) (hn₂ : h₂ 1 1 ≠ 0)
    {A B : Submodule (𝓞 K) K} (hA : Submodule.IsFullLattice K A) (hB : Submodule.IsFullLattice K B)
    (hex : ∃ s, IsClassReps h₁ A s) : mass h₂ B = mass h₁ A := by
  obtain ⟨A', hA', hA'A⟩ := exists_inv hA
  obtain ⟨B', hB', hB'B⟩ := exists_inv hB
  have hJC : (A * B') * (B * A') = 1 := by
    calc (A * B') * (B * A') = (A' * A) * (B' * B) := by ring
      _ = 1 := by rw [hA'A, hB'B, one_mul]
  have t1 : ∀ g : K ≃ₗ[K] K, (Equiv.refl (K ≃ₗ[K] K)) g ∈ isom h₂ ↔ g ∈ isom h₁ := fun g => by
    rw [Equiv.refl_apply, mem_isom_iff hn₂, mem_isom_iff hn₁]
  have t2 : ∀ (g : K ≃ₗ[K] K) (M : Submodule (𝓞 K) K),
      mulE (B * A') (A * B') hJC (gmap g M) =
        gmap ((Equiv.refl (K ≃ₗ[K] K)) g) (mulE (B * A') (A * B') hJC M) := fun g M =>
    gmap_mul g (B * A') M
  have t3 : ∀ (p : Ideal (𝓞 K)), p.IsMaximal → ∀ (M : Submodule (𝓞 K) K),
      mulE (B * A') (A * B') hJC (loc p M) = loc p (mulE (B * A') (A * B') hJC M) :=
    fun p hp M => loc_mul hp (B * A') M
  have t4 : ∀ (M : Submodule (𝓞 K) K),
      Submodule.IsFullLattice K (mulE (B * A') (A * B') hJC M) ↔ Submodule.IsFullLattice K M := by
    intro M
    change Submodule.IsFullLattice K (B * A' * M) ↔ Submodule.IsFullLattice K M
    constructor
    · intro hM
      have e := isLattice_mul (isLattice_mul hA hB') hM
      rwa [← mul_assoc, hJC, one_mul] at e
    · intro hM
      exact isLattice_mul (isLattice_mul hB hA') hM
  have hΦA : mulE (B * A') (A * B') hJC A = B := by
    show B * A' * A = B
    rw [mul_assoc, hA'A, mul_one]
  have he := (mass_transfer (mulE (B * A') (A * B') hJC) (Equiv.refl _) t1 t2 t3 t4 hex).2
  rw [hΦA] at he
  exact he

end Formalism.HermitianLattices.Ext.L3.RankOne
end
end

