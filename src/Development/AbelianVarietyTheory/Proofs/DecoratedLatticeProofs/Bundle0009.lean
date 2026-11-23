module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixFieldStableRangeOneDetNeZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero : ∀ (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ), c * p + d * q = 1 → ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 := by
  first | exact @GlobalTheory.matrix_stableRange_one' | exact GlobalTheory.matrix_stableRange_one' | (intros; apply GlobalTheory.matrix_stableRange_one' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegersModNatFinite
section
open ValuativeRel GlobalTheory.SplitWeil Matrix

namespace GlobalTheory

theorem exists_finite_integer_residues (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (hn : 0 < n) :
    ∃ (ι : Type) (_ : Finite ι) (x : ι → k), (∀ i, x i ∈ 𝒪[k]) ∧
      ∀ y ∈ 𝒪[k], ∃ i, ∃ u ∈ 𝒪[k], y = x i + (n : k) * u := by
  let U : Set k := ((𝒪[k] : Subring k) : Set k)
  have hUo : IsOpen U := Valuation.isOpen_integer
  have hUc : IsCompact U := isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[k])
  have hc : (n : k) ≠ 0 := by exact_mod_cast hn.ne'
  let V : U → Set k := fun x => (fun y => (y - (x : k)) * (n : k)⁻¹) ⁻¹' U
  have hVo : ∀ x, IsOpen (V x) := fun x =>
    hUo.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  have hcov : U ⊆ ⋃ x, V x := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    show (y - y) * (n : k)⁻¹ ∈ U
    rw [sub_self, zero_mul]
    exact (𝒪[k]).zero_mem
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover V hVo hcov
  refine ⟨t, inferInstance, fun i => ((i : U) : k), fun i => (i : U).2, ?_⟩
  intro y hy
  have := ht hy
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hxt, hyx⟩ := this
  refine ⟨⟨x, hxt⟩, (y - (x : k)) * (n : k)⁻¹, hyx, ?_⟩
  field_simp
  ring

theorem matrix_integers_mod_nat_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (n : ℕ), 0 < n →
    ∃ R : Set (Matrix Y Y' k), R.Finite ∧ ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) →
      ∃ s ∈ R, ∃ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) ∧ t = s + n • u := by
  intro k _ _ _ _ _ Y Y' _ _ n hn
  obtain ⟨ι, hι, x, -, hx⟩ := exists_finite_integer_residues k n hn
  refine ⟨Set.range (fun f : Y → Y' → ι => Matrix.of fun r q => x (f r q)), Set.finite_range _, ?_⟩
  intro t ht
  have key := fun r q => hx (t r q) (ht r q)
  choose f u hu hf using key
  refine ⟨Matrix.of fun r q => x (f r q), ⟨f, rfl⟩, Matrix.of fun r q => u r q, hu, ?_⟩
  ext r q
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
  exact hf r q

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
section
open ValuativeRel GlobalTheory.SplitWeil Matrix

noncomputable section
namespace GlobalTheory.CharDualMat

open ValuativeRel Matrix in
private lemma half_lt_re_of_norm_eq_one_of_norm_sub_one_lt {w : ℂ} (hw : ‖w‖ = 1) (h : ‖w - 1‖ < 1) :
    1 / 2 < w.re := by
  have h1 : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at this
    nlinarith
  have h2 : (w.re - 1) ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.sq_norm (w - 1)
    rw [Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at this
    have h0 : ‖w - 1‖ ^ 2 < 1 := by
      have := norm_nonneg (w - 1)
      nlinarith
    nlinarith
  nlinarith


open ValuativeRel Matrix in
theorem _root_.GlobalTheory.CharDualMat.circle_eq_one_of_pow_near (z : Circle) (h : ∀ n : ℕ, ‖(z : ℂ) ^ n - 1‖ < 1) :
    z = 1 := by
  have hnorm : ∀ m : ℕ, ‖(z : ℂ) ^ (2 ^ m)‖ = 1 := fun m => by
    rw [norm_pow, Circle.norm_coe, one_pow]
  have hre : ∀ m : ℕ, 1 / 2 < ((z : ℂ) ^ (2 ^ m)).re := fun m =>
    half_lt_re_of_norm_eq_one_of_norm_sub_one_lt (hnorm m) (h _)
  have hsq : ∀ m : ℕ, ((z : ℂ) ^ (2 ^ m)).re ^ 2 + ((z : ℂ) ^ (2 ^ m)).im ^ 2 = 1 := fun m => by
    have := Complex.sq_norm ((z : ℂ) ^ (2 ^ m))
    rw [hnorm m, Complex.normSq_apply] at this
    nlinarith
  have hstep : ∀ m : ℕ, ((z : ℂ) ^ (2 ^ (m + 1))).re =
      ((z : ℂ) ^ (2 ^ m)).re ^ 2 - ((z : ℂ) ^ (2 ^ m)).im ^ 2 := fun m => by
    rw [pow_succ, pow_mul, sq, Complex.mul_re]
    ring
  have hgrow : ∀ m : ℕ, 3 ^ m * (1 - (z : ℂ).re) ≤ 1 - ((z : ℂ) ^ (2 ^ m)).re := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [hstep m, pow_succ]
      have hr := hre m
      have hs := hsq m
      have hle : ((z : ℂ) ^ (2 ^ m)).re ≤ 1 := by nlinarith [sq_nonneg ((z : ℂ) ^ (2 ^ m)).im]
      nlinarith
  have hd0 : (z : ℂ).re = 1 := by
    have hle : (z : ℂ).re ≤ 1 := by
      have := hsq 0
      simp only [pow_zero, pow_one] at this
      nlinarith [sq_nonneg (z : ℂ).im]
    by_contra hne
    have hpos : 0 < 1 - (z : ℂ).re := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · linarith
      · exact absurd heq hne
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (1 - (z : ℂ).re)) (by norm_num : (1 : ℝ) < 3)
    have h1 := hgrow n
    have h2 := hre n
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have him : (z : ℂ).im = 0 := by
    have := hsq 0
    simp only [pow_zero, pow_one, hd0] at this
    nlinarith [sq_nonneg (z : ℂ).im]
  apply Circle.ext_iff.mpr
  apply Complex.ext <;> simp [hd0, him]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.CharDualMat.valuation_nsmul_le (t : k) (n : ℕ) : valuation k (n • t) ≤ valuation k t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul]
    exact ((valuation k).map_add _ _).trans (max_le ih le_rfl)


open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.CharDualMat.exists_ball_trivial (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ t : k, valuation k t < γ → ψ t = 1 := by
  have hopen : IsOpen (ψ ⁻¹' {w : Circle | ‖(w : ℂ) - 1‖ < 1}) :=
    (isOpen_lt (by fun_prop) continuous_const).preimage hψ
  have hzero : (0 : k) ∈ ψ ⁻¹' {w : Circle | ‖(w : ℂ) - 1‖ < 1} := by
    simp [AddChar.map_zero_eq_one]
  obtain ⟨γ, hγ, hsub⟩ :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 (hopen.mem_nhds hzero)
  refine ⟨γ, hγ, fun t ht => ?_⟩
  apply _root_.GlobalTheory.CharDualMat.circle_eq_one_of_pow_near
  intro n
  have hmem : n • t ∈ ψ ⁻¹' {w : Circle | ‖(w : ℂ) - 1‖ < 1} :=
    hsub (lt_of_le_of_lt (_root_.GlobalTheory.CharDualMat.valuation_nsmul_le t n) ht)
  rw [Set.mem_preimage, AddChar.map_nsmul_eq_pow] at hmem
  simpa using hmem


open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.CharDualMat.mem_integer_of_dual (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (a : k)
    (h : ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) → ψ (s * a) = 1) : a ∈ 𝒪[k] := by
  by_contra ha
  have hva : 1 < valuation k a := by
    rw [Valuation.mem_integer_iff] at ha
    exact not_le.1 ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hva
  obtain ⟨γ, hγ, hball⟩ := _root_.GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hmul : ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) →
      ∀ u : k, u ∈ 𝒪[k] → ψ (s * a * u) = 1 := by
    intro s hs u hu
    have := h (s * u) (fun u' hu' => by rw [mul_assoc]; exact hs _ (mul_mem hu hu'))
    rw [mul_right_comm]
    exact this
  have hpow : ∀ n : ℕ, ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) →
      ∀ u : k, u ∈ 𝒪[k] → ψ (s * a ^ n * u) = 1 := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih => intro s hs; rw [pow_succ, ← mul_assoc]; exact hmul _ (ih s hs)
  apply hne
  ext t
  obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation k t * γ⁻¹) hva
  have hlt : valuation k t * γ⁻¹ < valuation k a ^ (n + 1) :=
    lt_of_le_of_lt hn (pow_lt_pow_right₀ hva n.lt_succ_self)
  have hapos : valuation k a ^ (n + 1) ≠ 0 := pow_ne_zero _ (by simpa using ha0)
  have hlt' : valuation k t < γ * valuation k a ^ (n + 1) := by
    calc valuation k t = valuation k t * γ⁻¹ * γ := (inv_mul_cancel_right₀ hγ _).symm
      _ < valuation k a ^ (n + 1) * γ := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 hγ)
      _ = γ * valuation k a ^ (n + 1) := mul_comm _ _
  have hs : ∀ u : k, u ∈ 𝒪[k] → ψ (t * (a ^ (n + 1))⁻¹ * u) = 1 := by
    intro u hu
    apply hball
    rw [Valuation.mem_integer_iff] at hu
    rw [map_mul, map_mul, map_inv₀, map_pow]
    calc valuation k t * (valuation k a ^ (n + 1))⁻¹ * valuation k u
        ≤ valuation k t * (valuation k a ^ (n + 1))⁻¹ := mul_le_of_le_one_right' hu
      _ < γ := mul_inv_lt_of_lt_mul₀ hlt'
  have := hpow (n + 1) _ hs 1 (one_mem _)
  rw [mul_one, inv_mul_cancel_right₀ (pow_ne_zero _ ha0)] at this
  rw [this, AddChar.one_apply]


open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.CharDualMat.integral_of_dual (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (ψk : AddChar k Circle)
    (hψ : Continuous ψk) (hne : ψk ≠ 1) (x : Matrix Y Y' k)
    (hx : ∀ b : Matrix Y Y' k, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) →
      ψk (∑ r, ∑ q, b r q * u r q) = 1) → ψk (∑ r, ∑ q, b r q * x r q) = 1)
    (r₀ : Y) (q₀ : Y') : x r₀ q₀ ∈ 𝒪[k] := by
  classical
  refine _root_.GlobalTheory.CharDualMat.mem_integer_of_dual ψk hψ hne (x r₀ q₀) (fun s hs => ?_)
  let b : Matrix Y Y' k := fun r q => if r = r₀ ∧ q = q₀ then s else 0
  have key : ∀ y : Matrix Y Y' k, ∑ r, ∑ q, b r q * y r q = s * y r₀ q₀ := by
    intro y
    rw [Finset.sum_eq_single r₀ (fun r _ hr => Finset.sum_eq_zero fun q _ => by simp [b, hr])
      (by simp), Finset.sum_eq_single q₀ (fun q _ hq => by simp [b, hq]) (by simp)]
    simp [b]
  have := hx b (fun u hu => by rw [key]; exact hs _ (hu r₀ q₀))
  rwa [key] at this

end GlobalTheory.CharDualMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
section
open GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LocFlat.CFac

def prodFn {X Y : Type} (f : X → ℂ) (g : Y → ℂ) : X × Y → ℂ := fun p => f p.1 * g p.2

theorem prodFn_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f : X → ℂ} {g : Y → ℂ}
    (hf : f ∈ SB X) (hg : g ∈ SB Y) : prodFn f g ∈ SB (X × Y) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul (hg.1.comp_continuous continuous_snd), ?_⟩
  refine HasCompactSupport.intro' (IsCompact.prod hf.2 hg.2) ((isClosed_tsupport _).prod (isClosed_tsupport _)) ?_
  intro p hp
  simp only [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · simp [prodFn, image_eq_zero_of_notMem_tsupport h]
  · simp [prodFn, image_eq_zero_of_notMem_tsupport h]

def prodSB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : SB X) (g : SB Y) : SB (X × Y) :=
  ⟨prodFn f.1 g.1, prodFn_mem_SB f.2 g.2⟩

@[simp] theorem prodSB_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : SB X) (g : SB Y) (p : X × Y) :
    (prodSB f g).1 p = f.1 p.1 * g.1 p.2 := rfl

def comapH {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) : SB Y →ₗ[ℂ] SB X where
  toFun F := ⟨fun x => F.1 (e x), F.2.1.comp_continuous e.continuous, F.2.2.comp_homeomorph e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem comapH_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (F : SB Y) (x : X) :
    (comapH e F).1 x = F.1 (e x) := rfl

def mulLC {X : Type} [TopologicalSpace X] (φ : X → ℂ) (hφ : IsLocallyConstant φ) : SB X →ₗ[ℂ] SB X where
  toFun F := ⟨fun x => φ x * F.1 x, hφ.mul F.2.1, F.2.2.mul_left⟩
  map_add' F G := by ext x; simp [mul_add]
  map_smul' c F := by ext x; simp; ring

@[simp] theorem mulLC_apply {X : Type} [TopologicalSpace X] (φ : X → ℂ) (hφ : IsLocallyConstant φ) (F : SB X) (x : X) :
    (mulLC φ hφ F).1 x = φ x * F.1 x := rfl

end GlobalTheory.LocFlat.CFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelSetEntryBoundOfLatticeMin
section
open Matrix GlobalTheory.ClassFin

namespace GlobalTheory

theorem siegelSet_entry_bound_of_lattice_min (N : ℕ) (C : ℝ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ) (hS : IsSiegel C k a n) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hmin : ∀ z : Fin N → ℤ, z ≠ 0 → t ≤ ‖(k * diagonal a * n) *ᵥ fun i => (z i : ℝ)‖)
    (i j : Fin N) : |(k * diagonal a * n) i j| * t ^ N ≤ N * C ^ N := by
  have hN : 0 < N := Fin.pos i
  set i0 : Fin N := ⟨0, hN⟩ with hi0

  have hk : ∀ p q, |k p q| ≤ 1 := by
    intro p q
    have h := congrFun (congrFun hS.orth q) q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    have : k p q * k p q ≤ ∑ x, k x q * k x q :=
      Finset.single_le_sum (f := fun x => k x q * k x q) (fun x _ => mul_self_nonneg _) (Finset.mem_univ p)
    rw [h] at this
    have h2 : |k p q| ^ 2 ≤ 1 := by rw [sq_abs, sq]; exact this
    nlinarith [abs_nonneg (k p q)]
  have hC1 : 1 ≤ C := by
    have := hS.bdd i i
    rw [hS.diag i, abs_one] at this
    exact this

  have hg : ∀ p q, (k * diagonal a * n) p q = ∑ l, k p l * a l * n l q := by
    intro p q
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]

  have hcol : ∀ p, (k * diagonal a * n) p i0 = k p i0 * a i0 := by
    intro p
    rw [hg, Finset.sum_eq_single i0]
    · rw [hS.diag i0, mul_one]
    · intro l _ hl
      have : i0 < l := by
        rcases lt_or_gt_of_ne hl with h | h
        · exact absurd h (by simp [hi0, Fin.lt_def])
        · exact h
      rw [hS.lower l i0 this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have ha0 : t ≤ a i0 := by
    have h := hmin (Pi.single i0 1) (by
      intro h; have := congrFun h i0; simp at this)
    refine h.trans ?_
    refine (pi_norm_le_iff_of_nonneg (le_of_lt (hS.pos i0))).2 ?_
    intro p
    have : ((k * diagonal a * n) *ᵥ fun i => (((Pi.single i0 (1:ℤ) : Fin N → ℤ) i : ℤ) : ℝ)) p
        = (k * diagonal a * n) p i0 := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, hcol, Real.norm_eq_abs, abs_mul, abs_of_pos (hS.pos i0)]
    exact mul_le_of_le_one_left (le_of_lt (hS.pos i0)) (hk p i0)
  have hlow : ∀ l, t ≤ C * a l := by
    intro l
    by_cases hl : l = i0
    · subst hl
      nlinarith [hS.pos i0]
    · have : i0 < l := by
        rcases lt_or_gt_of_ne hl with h | h
        · exact absurd h (by simp [hi0, Fin.lt_def])
        · exact h
      exact ha0.trans (hS.le i0 l this)
  have hup : ∀ l, a l * t ^ (N - 1) ≤ C ^ (N - 1) := by
    intro l
    have hprod : ∏ x ∈ Finset.univ.erase l, t ≤ ∏ x ∈ Finset.univ.erase l, (C * a x) :=
      Finset.prod_le_prod₀ (fun _ _ => le_of_lt ht0) (fun x _ => hlow x)
    rw [Finset.prod_const, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin] at hprod
    have h1 : a l * ∏ x ∈ Finset.univ.erase l, a x = 1 := by
      rw [Finset.mul_prod_erase _ _ (Finset.mem_univ l)]; exact hS.prod_eq
    have hal := le_of_lt (hS.pos l)
    calc a l * t ^ (N - 1) ≤ a l * (C ^ (N - 1) * ∏ x ∈ Finset.univ.erase l, a x) :=
          mul_le_mul_of_nonneg_left hprod hal
      _ = C ^ (N - 1) * (a l * ∏ x ∈ Finset.univ.erase l, a x) := by ring
      _ = C ^ (N - 1) := by rw [h1, mul_one]
  have hent : |(k * diagonal a * n) i j| ≤ ∑ l, a l * C := by
    rw [hg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul, abs_mul, abs_of_pos (hS.pos l)]
    have h1 := hk i l
    have h2 := hS.bdd l j
    have hal := le_of_lt (hS.pos l)
    calc |k i l| * a l * |n l j| ≤ 1 * a l * C := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hal) h2 (abs_nonneg _) (by positivity)
      _ = a l * C := by ring
  have htN : t ^ N = t ^ (N - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  have htpow : 0 ≤ t ^ N := by positivity
  calc |(k * diagonal a * n) i j| * t ^ N ≤ (∑ l, a l * C) * t ^ N :=
        mul_le_mul_of_nonneg_right hent htpow
    _ = ∑ l, (a l * t ^ (N - 1)) * C * t := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => ?_; rw [htN]; ring
    _ ≤ ∑ l : Fin N, C ^ (N - 1) * C * 1 := by
        refine Finset.sum_le_sum fun l _ => ?_
        apply mul_le_mul (mul_le_mul_of_nonneg_right (hup l) (by linarith)) ht1 (le_of_lt ht0)
        positivity
    _ = N * C ^ N := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← pow_succ,
          Nat.sub_add_cancel hN]

theorem siegel_entry_bound : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ t : ℝ, 0 < t → t ≤ 1 →
    (∀ z : Fin N → ℤ, z ≠ 0 → t ≤ ‖(k * diagonal a * n) *ᵥ fun i => (z i : ℝ)‖) →
    ∀ i j, |(k * diagonal a * n) i j| * t ^ N ≤ C' :=
  fun N C => ⟨N * C ^ N, fun k a n hS t ht0 ht1 hmin i j =>
    siegelSet_entry_bound_of_lattice_min N C k a n hS t ht0 ht1 hmin i j⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothOfLimitClassStableUnderDirectionalDerivs
section
open scoped ContDiff Topology

namespace GlobalTheory

theorem contDiff_of_class_tendstoLocallyUniformly : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by
  intro E _ _ A _ v c hc P hP
  have key : ∀ φ, P φ → Differentiable ℝ φ ∧ ∃ (α χ : A → E → ℂ), (∀ a, ContDiff ℝ ∞ (α a)) ∧
      (∀ a, P (χ a)) ∧ fderiv ℝ φ =
        fun y => ∑ a, (α a y * φ y + χ a y) • ((c a).smulRight (1 : ℂ)) := by
    intro φ hφ
    obtain ⟨g, hg, hlim, hd⟩ := hP φ hφ
    choose α hα χ hχ hlim' using hd
    have h := _root_.GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional v c hc φ g (fun a y => α a y * φ y + χ a y) hg hlim hlim'
    refine ⟨fun y => (h y).1, α, χ, hα, hχ, ?_⟩
    funext y
    ext x
    conv_lhs => rw [← hc x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, (h y).2, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  have main : ∀ n : ℕ, ∀ φ, P φ → ContDiff ℝ n φ := by
    intro n
    induction n with
    | zero =>
      intro φ hφ
      simpa using (key φ hφ).1.continuous
    | succ n ih =>
      intro φ hφ
      obtain ⟨hd, α, χ, hα, hχ, hf⟩ := key φ hφ
      have : ContDiff ℝ ((n : WithTop ℕ∞) + 1) φ := by
        rw [contDiff_succ_iff_fderiv]
        refine ⟨hd, by simp, ?_⟩
        rw [hf]
        refine ContDiff.sum fun a _ => ?_
        have h1 : ContDiff ℝ n (α a) := (hα a).of_le (by exact_mod_cast le_top)
        exact ((h1.mul (ih φ hφ)).add (ih _ (hχ a))).smul contDiff_const
      exact_mod_cast this
  intro φ hφ
  exact contDiff_infty.2 fun n => main n φ hφ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentUpperInvUpperTriangularBounded
section
open Matrix GlobalTheory.ClassFin

namespace GlobalTheory

theorem unipotent_upper_inv_bounded : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ n : Matrix (Fin N) (Fin N) ℝ, (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (∀ i j, |n i j| ≤ C) → ∃ m : Matrix (Fin N) (Fin N) ℝ, m * n = 1 ∧ n * m = 1 ∧ (∀ i j, j < i → m i j = 0) ∧ ∀ i j, |m i j| ≤ C' := by
  intro N C
  refine ⟨(Nat.factorial N : ℝ) * (max C 1) ^ N, ?_⟩
  intro n hd hl hb
  have htri : n.BlockTriangular id := fun i j h => hl i j h
  have hdet : n.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]; simp [hd]
  have hu : IsUnit n.det := by rw [hdet]; exact isUnit_one
  refine ⟨n⁻¹, Matrix.nonsing_inv_mul n hu, Matrix.mul_nonsing_inv n hu, ?_, ?_⟩
  · intro i j h
    letI := Matrix.invertibleOfIsUnitDet n hu
    exact Matrix.blockTriangular_inv_of_blockTriangular htri h
  · intro i j
    have hinv : n⁻¹ = n.adjugate := by rw [Matrix.inv_def, hdet]; simp
    rw [hinv, Matrix.adjugate_apply]
    have key := Matrix.det_le (abv := AbsoluteValue.abs) (x := max C 1)
      (A := n.updateRow j (Pi.single i 1)) ?_
    · simpa using key
    · intro k l
      by_cases hk : k = j
      · subst hk
        simp only [Matrix.updateRow_self, Pi.single_apply]
        split_ifs <;> simp
      · rw [Matrix.updateRow_ne hk]
        exact le_trans (hb k l) (le_max_left _ _)

end GlobalTheory
end

