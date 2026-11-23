module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusRecursionDifferencesDecayGaussNorm
section
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK.FrobDecay

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def CoeffBd (ρ b : ℝ) (f : K⟦X⟧) : Prop := ∀ m, ‖coeff m f‖ * ρ ^ m ≤ b

theorem bd_mul {ρ a b : ℝ} {f g : K⟦X⟧} (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : CoeffBd ρ a f) (hg : CoeffBd ρ b g) : CoeffBd ρ (a * b) (f * g) := fun m =>
  norm_coeff_mul_le (w := fun m => ρ ^ m) (fun n => pow_nonneg hρ n)
    (fun i j => (pow_add ρ i j).le) ha hb hf hg m

theorem bd_add {ρ b : ℝ} {f g : K⟦X⟧} (hρ : 0 ≤ ρ) (hf : CoeffBd ρ b f) (hg : CoeffBd ρ b g) :
    CoeffBd ρ b (f + g) := fun m =>
  (norm_coeff_add_le (w := fun m => ρ ^ m) (fun n => pow_nonneg hρ n) f g m).trans
    (max_le (hf m) (hg m))

theorem bd_zero {ρ b : ℝ} (hb : 0 ≤ b) : CoeffBd ρ b (0 : K⟦X⟧) := fun m => by simp [hb]

theorem bd_sum {α : Type} (s : Finset α) (f : α → K⟦X⟧) {ρ b : ℝ} (hρ : 0 ≤ ρ) (hb : 0 ≤ b)
    (h : ∀ i ∈ s, CoeffBd ρ b (f i)) : CoeffBd ρ b (∑ i ∈ s, f i) :=
  Finset.sum_induction f (CoeffBd ρ b) (fun _ _ => bd_add hρ) (bd_zero hb) h

theorem bd_C {ρ : ℝ} (x : K) : CoeffBd ρ ‖x‖ (C x) := fun m => by
  rw [coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

theorem bd_le {ρ b b' : ℝ} {f : K⟦X⟧} (hbb : b ≤ b') (hf : CoeffBd ρ b f) : CoeffBd ρ b' f :=
  fun m => (hf m).trans hbb

theorem bd_mono {ρ ρ' b : ℝ} {f : K⟦X⟧} (hρ : 0 ≤ ρ') (h : ρ' ≤ ρ) (hf : CoeffBd ρ b f) :
    CoeffBd ρ' b f := fun m =>
  (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ h m) (norm_nonneg _)).trans (hf m)

theorem bd_frob (l : ℕ) [Fact l.Prime] {ρ b : ℝ} {f : K⟦X⟧} (hb : 0 ≤ b)
    (hf : CoeffBd (ρ ^ l) b f) : CoeffBd ρ b (frob K l f) := fun m => by
  rw [coeff_frob]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Fact.out : l.Prime).pos, pow_mul]
    exact hf q
  · simpa using hb

theorem bd_of_coeff_zero {r ρ N : ℝ} {f : K⟦X⟧} (hr : 0 < r) (hρ : 0 ≤ ρ) (hρr : ρ ≤ r)
    (hf : CoeffBd r N f) (h0 : coeff 0 f = 0) : CoeffBd ρ (N / r * ρ) f := fun m => by
  have hN : 0 ≤ N := (mul_nonneg (norm_nonneg _) (pow_nonneg hr.le 0)).trans (hf 0)
  cases m with
  | zero => simpa [h0] using mul_nonneg (div_nonneg hN hr.le) hρ
  | succ m =>
    have key : ρ ^ (m + 1) * r ≤ r ^ (m + 1) * ρ := by
      have h1 := pow_le_pow_left₀ hρ hρr m
      calc ρ ^ (m + 1) * r = ρ ^ m * (ρ * r) := by ring
        _ ≤ r ^ m * (ρ * r) := mul_le_mul_of_nonneg_right h1 (mul_nonneg hρ hr.le)
        _ = r ^ (m + 1) * ρ := by ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    calc ‖coeff (m + 1) f‖ * ρ ^ (m + 1) * r = ‖coeff (m + 1) f‖ * (ρ ^ (m + 1) * r) := by ring
      _ ≤ ‖coeff (m + 1) f‖ * (r ^ (m + 1) * ρ) := mul_le_mul_of_nonneg_left key (norm_nonneg _)
      _ = (‖coeff (m + 1) f‖ * r ^ (m + 1)) * ρ := by ring
      _ ≤ N * ρ := mul_le_mul_of_nonneg_right (hf _) hρ

end GlobalTheory.BK.FrobDecay

open GlobalTheory.BK.FrobDecay

theorem GlobalTheory.BK.frob_recursion_decay : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j) → ∃ M β : ℝ, 0 ≤ β ∧ ∀ n τ i j, Z n τ i j ∈ R O K l k ∧ normR l k (Z (n + 1) τ i j - Z n τ i j) ≤ M * β ^ n * rad l k ^ (l ^ n) := by
  intro O K _ _ _ _ _ l a _ _ ι _ _ k hk B c Z hB h0 hrec hX
  have hr : 0 < rad l k := rad_pos l k
  have hr1 : rad l k ≤ 1 := rad_le_one l hk.le
  have hmem : ∀ n τ i j, Z n τ i j ∈ R O K l k := by
    intro n
    induction n with
    | zero =>
      intro τ i j
      rw [h0, Matrix.map_apply]
      exact HasK.C_mem _
    | succ n ih =>
      intro τ i j
      rw [hrec, Matrix.mul_apply]
      refine Subalgebra.sum_mem _ fun q _ => mul_mem ?_ (by rw [Matrix.map_apply]; exact HasK.C_mem _)
      rw [Matrix.mul_apply]
      exact Subalgebra.sum_mem _ fun p _ => mul_mem (hB _ _ _)
        (by rw [Matrix.map_apply]; exact frob_mem_R l hk.le (ih _ _ _))
  have hnn : ∀ f ∈ R O K l k, 0 ≤ normR l k f := fun f hf =>
    (mul_nonneg (norm_nonneg _) (pow_nonneg hr.le 0)).trans (le_normR hf 0)
  let D : ℕ → ZMod a → Matrix ι ι K⟦X⟧ := fun n τ => Z (n + 1) τ - Z n τ
  have hD : ∀ n τ i j, D (n + 1) τ i j =
      ∑ q, (∑ p, B τ i p * frob K l (D n (τ - 1) p q)) * C (c τ q j) := by
    intro n τ i j
    simp only [D, Matrix.sub_apply]
    rw [hrec (n + 1) τ, hrec n τ]
    simp only [Matrix.mul_apply, Matrix.map_apply, ← Finset.sum_sub_distrib, ← sub_mul, ← mul_sub,
      map_sub, Matrix.sub_apply]
  obtain ⟨β, hβ0, hBbd⟩ : ∃ β : ℝ, 0 ≤ β ∧ ∀ τ i j, CoeffBd (rad l k) β (B τ i j) :=
    ⟨∑ x : ZMod a × ι × ι, normR l k (B x.1 x.2.1 x.2.2),
      Finset.sum_nonneg fun x _ => hnn _ (hB _ _ _), fun τ i j m =>
      (le_normR (hB τ i j) m).trans (Finset.single_le_sum
        (f := fun x : ZMod a × ι × ι => normR l k (B x.1 x.2.1 x.2.2))
        (fun x _ => hnn _ (hB _ _ _)) (Finset.mem_univ (τ, i, j)))⟩
  obtain ⟨γ, hγ0, hcbd⟩ : ∃ γ : ℝ, 0 ≤ γ ∧ ∀ τ i j, ‖c τ i j‖ ≤ γ :=
    ⟨∑ x : ZMod a × ι × ι, ‖c x.1 x.2.1 x.2.2‖, Finset.sum_nonneg fun x _ => norm_nonneg _,
      fun τ i j => Finset.single_le_sum (f := fun x : ZMod a × ι × ι => ‖c x.1 x.2.1 x.2.2‖)
        (fun x _ => norm_nonneg _) (Finset.mem_univ (τ, i, j))⟩
  have hD0mem : ∀ τ i j, D 0 τ i j ∈ R O K l k := fun τ i j =>
    sub_mem (hmem 1 τ i j) (hmem 0 τ i j)
  obtain ⟨N, hN0, hNbd⟩ : ∃ N : ℝ, 0 ≤ N ∧ ∀ τ i j, CoeffBd (rad l k) N (D 0 τ i j) :=
    ⟨∑ x : ZMod a × ι × ι, normR l k (D 0 x.1 x.2.1 x.2.2),
      Finset.sum_nonneg fun x _ => hnn _ (hD0mem _ _ _), fun τ i j m =>
      (le_normR (hD0mem τ i j) m).trans (Finset.single_le_sum
        (f := fun x : ZMod a × ι × ι => normR l k (D 0 x.1 x.2.1 x.2.2))
        (fun x _ => hnn _ (hD0mem _ _ _)) (Finset.mem_univ (τ, i, j)))⟩
  have key : ∀ n, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ rad l k → ∀ τ i j,
      CoeffBd ρ (N / rad l k * (β * γ) ^ n * ρ ^ (l ^ n)) (D n τ i j) := by
    intro n
    induction n with
    | zero =>
      intro ρ hρ hρr τ i j
      simp only [pow_zero, mul_one, pow_one]
      refine bd_of_coeff_zero hr hρ hρr (hNbd τ i j) ?_
      rw [coeff_zero_eq_constantCoeff_apply]
      exact X_dvd_iff.1 (hX τ i j)
    | succ n ih =>
      intro ρ hρ hρr τ i j
      rw [hD]
      have hρl : ρ ^ l ≤ rad l k :=
        (pow_le_of_le_one hρ (hρr.trans hr1) (Fact.out : l.Prime).ne_zero).trans hρr
      have hM0 : 0 ≤ N / rad l k * (β * γ) ^ n * (ρ ^ l) ^ (l ^ n) :=
        mul_nonneg (mul_nonneg (div_nonneg hN0 hr.le) (pow_nonneg (mul_nonneg hβ0 hγ0) _))
          (pow_nonneg (pow_nonneg hρ _) _)
      have bnd : N / rad l k * (β * γ) ^ (n + 1) * ρ ^ (l ^ (n + 1)) =
          (β * (N / rad l k * (β * γ) ^ n * (ρ ^ l) ^ (l ^ n))) * γ := by
        rw [← pow_mul, ← pow_succ']
        ring
      rw [bnd]
      refine bd_sum _ _ hρ (mul_nonneg (mul_nonneg hβ0 hM0) hγ0) fun q _ =>
        bd_mul hρ (mul_nonneg hβ0 hM0) hγ0 ?_ (bd_le (hcbd τ q j) (bd_C (c τ q j)))
      exact bd_sum _ _ hρ (mul_nonneg hβ0 hM0) fun p _ =>
        bd_mul hρ hβ0 hM0 (bd_mono hρ hρr (hBbd τ i p))
          (bd_frob l hM0 (ih (ρ ^ l) (pow_nonneg hρ _) hρl (τ - 1) p q))
  refine ⟨N / rad l k, β * γ, mul_nonneg hβ0 hγ0, fun n τ i j => ⟨hmem n τ i j, ?_⟩⟩
  exact ciSup_le fun m => key n (rad l k) hr.le le_rfl τ i j m
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralizedEigenPartProjectorMemHeckeAlgebra
section
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory

open Polynomial Module.End

theorem part_projector_mem_adjoin :
    ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
      [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
      [FiniteDimensional K V] (S : Set (Module.End K V)), (∀ a ∈ S, ∀ b ∈ S, Commute a b) →
      (∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) →
      (∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) →
      ∀ (L : Submodule O V), L.FG → Submodule.span K (L : Set V) = ⊤ → (∀ a ∈ S, ∀ x ∈ L, a x ∈ L) →
      ∀ 𝔪 : Ideal (Algebra.adjoin O S), ∃ t ∈ Algebra.adjoin O S,
        (∀ x ∈ NCov.part (Algebra.adjoin O S) 𝔪, t x = x) ∧
          ∀ x ∈ NCov.off (Algebra.adjoin O S) 𝔪, t x = 0 := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ S hS hsplit hint L _ _ _ 𝔪
  classical
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨F, hF, -⟩ := NCov.exists_finset_pts hinj hS hsplit hint
  by_cases hA : ∃ ψ0 : Algebra.adjoin O S →ₐ[O] O, NCov.cls ψ0 = 𝔪
  swap
  · push_neg at hA
    refine ⟨0, Subalgebra.zero_mem _, fun x hx => ?_, fun x _ => rfl⟩
    have : NCov.part (Algebra.adjoin O S) 𝔪 = ⊥ := by
      unfold NCov.part
      exact iSup₂_eq_bot.2 fun ψ h => absurd h (hA ψ)
    rw [this, Submodule.mem_bot] at hx
    simp [hx]
  obtain ⟨ψ0, rfl⟩ := hA
  have hmax := NCov.cls_isMaximal ψ0
  have hs : ∀ φ : Algebra.adjoin O S →ₐ[O] O, ∃ s : Algebra.adjoin O S,
      (NCov.cls φ ≠ NCov.cls ψ0 → s ∈ NCov.cls φ) ∧ s ∉ NCov.cls ψ0 := by
    intro φ
    by_cases h : NCov.cls φ = NCov.cls ψ0
    · exact ⟨1, fun h' => absurd h h', fun h1 => hmax.ne_top ((Ideal.eq_top_iff_one _).2 h1)⟩
    · have : ¬ NCov.cls φ ≤ NCov.cls ψ0 := fun hle =>
        h ((NCov.cls_isMaximal φ).eq_of_le hmax.ne_top hle)
      obtain ⟨s, hs1, hs2⟩ := SetLike.not_le_iff_exists.1 this
      exact ⟨s, fun _ => hs1, hs2⟩
  choose s hsin hsout using hs
  set FA := F.filter (fun ψ => NCov.cls ψ = NCov.cls ψ0)
  set FB := F.filter (fun ψ => NCov.cls ψ ≠ NCov.cls ψ0)
  letI : IsMulCommutative (Algebra.adjoin O S) :=
    Algebra.isMulCommutative_adjoin O (fun a ha b hb _ => hS a ha b hb)
  open scoped IsMulCommutative in
  obtain ⟨f, hfdef⟩ : ∃ f : Algebra.adjoin O S, f = ∏ φ ∈ FB, s φ := ⟨_, rfl⟩
  have hres : ∀ ψ : Algebra.adjoin O S →ₐ[O] O, ∀ u, u ∈ NCov.cls ψ ↔ IsLocalRing.residue O (ψ u) = 0 :=
    fun ψ u => Iff.rfl
  have hfA : ∀ ψ, NCov.cls ψ = NCov.cls ψ0 → IsLocalRing.residue O (ψ f) ≠ 0 := by
    intro ψ hψ
    rw [hfdef, map_prod, map_prod]
    refine Finset.prod_ne_zero_iff.2 fun φ _ => ?_
    have := hsout φ
    rw [← hψ, hres] at this
    exact this
  have hfB : ∀ φ ∈ FB, IsLocalRing.residue O (φ f) = 0 := by
    intro φ hφ
    rw [hfdef, map_prod, map_prod]
    exact Finset.prod_eq_zero hφ ((hres φ _).1 (hsin φ (Finset.mem_filter.1 hφ).2))
  let d : (Algebra.adjoin O S →ₐ[O] O) → ℕ := fun ψ =>
    (f : End K V).maxGenEigenspaceIndex (NCov.pt ψ f)
  let g : O[X] := ∏ ψ ∈ FA, (X - C (ψ f)) ^ d ψ
  let h : O[X] := ∏ φ ∈ FB, (X - C (φ f)) ^ d φ
  have hcop : IsCoprime g h := by
    refine IsCoprime.prod_left fun ψ hψ => IsCoprime.prod_right fun φ hφ => IsCoprime.pow ?_
    refine isCoprime_X_sub_C_of_isUnit_sub ?_
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_
    rw [map_sub, hfB φ hφ, sub_zero]
    exact hfA ψ (Finset.mem_filter.1 hψ).2
  obtain ⟨p, q, hpq⟩ := hcop
  have hkill : ∀ (G : Finset (Algebra.adjoin O S →ₐ[O] O)) (ψ) (_ : ψ ∈ G) (x : V),
      x ∈ NCov.W _ (NCov.pt ψ) → aeval (f : End K V) (∏ φ ∈ G, (X - C (φ f)) ^ d φ) x = 0 := by
    intro G ψ hψ x hx
    rw [show (∏ φ ∈ G, (X - C (φ f)) ^ d φ) =
        (∏ φ ∈ G.erase ψ, (X - C (φ f)) ^ d φ) * (X - C (ψ f)) ^ d ψ from
      (Finset.prod_erase_mul _ _ hψ).symm]
    rw [map_mul, Module.End.mul_apply, map_pow, map_sub, aeval_X, aeval_C]
    rw [NCov.pow_sub_apply_eq_zero ψ f hx, map_zero]
  have hval : ((aeval f (q * h) : Algebra.adjoin O S) : End K V) = aeval (f : End K V) (q * h) := by
    have e := aeval_algHom_apply (Algebra.adjoin O S).val f (q * h)
    simpa using e.symm
  refine ⟨_, (aeval f (q * h)).2, ?_, ?_⟩
  · intro x hx
    rw [hval]
    have hle : NCov.part (Algebra.adjoin O S) (NCov.cls ψ0) ≤
        LinearMap.ker (aeval (f : End K V) (q * h) - 1) := by
      unfold NCov.part
      refine iSup₂_le fun ψ hψ => ?_
      intro y hy
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      by_cases hW : NCov.W _ (NCov.pt ψ) = ⊥
      · rw [hW, Submodule.mem_bot] at hy
        rw [hy, map_zero]
      have hψA : ψ ∈ FA := Finset.mem_filter.2 ⟨hF ψ hW, hψ⟩
      have e1 := congrArg (fun P => aeval (f : End K V) P y) hpq
      simp only [map_add (f := _), map_mul, LinearMap.add_apply, Module.End.mul_apply, map_one,
        Module.End.one_apply] at e1
      rw [hkill FA ψ hψA y hy, map_zero, zero_add] at e1
      simpa [map_mul, Module.End.mul_apply] using e1
    have := hle hx
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  · intro x hx
    rw [hval]
    have hle : NCov.off (Algebra.adjoin O S) (NCov.cls ψ0) ≤
        LinearMap.ker (aeval (f : End K V) (q * h)) := by
      unfold NCov.off
      refine iSup₂_le fun φ hφ => ?_
      intro y hy
      rw [LinearMap.mem_ker]
      by_cases hW : NCov.W _ (NCov.pt φ) = ⊥
      · rw [hW, Submodule.mem_bot] at hy
        rw [hy, map_zero]
      have hφB : φ ∈ FB := Finset.mem_filter.2 ⟨hF φ hW, hφ⟩
      rw [map_mul, Module.End.mul_apply, hkill FB φ hφB y hy, map_zero]
    exact hle hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteTwistedInvariantLattice
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

section Lim

variable {K : Type} [NormedField K]

theorem exists_lim_of_norm_sub_le_pow [CompleteSpace K] {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    {c : ℕ → K} (h : ∀ m n, m ≤ n → ‖c n - c m‖ ≤ r ^ m) : ∃ x, ∀ n, ‖c n - x‖ ≤ r ^ n := by
  have hc : CauchySeq c := by
    refine cauchySeq_of_le_tendsto_0 (fun N => r ^ N) (fun n m N hn hm => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr)
    rw [dist_eq_norm]
    rcases le_total n m with hnm | hnm
    · rw [norm_sub_rev]
      exact (h n m hnm).trans (pow_le_pow_of_le_one hr0 hr.le hn)
    · exact (h m n hnm).trans (pow_le_pow_of_le_one hr0 hr.le hm)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨x, fun n => ?_⟩
  have ht : Tendsto (fun m => ‖c n - c m‖) atTop (𝓝 ‖c n - x‖) :=
    (tendsto_const_nhds.sub hx).norm
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [norm_sub_rev]
  exact h n m hm

theorem eq_zero_of_norm_le_pow_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) {x : K}
    (h : ∀ n, ‖x‖ ≤ r ^ n) : x = 0 :=
  norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr) h)

end Lim

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K]


omit [IsUltrametricDist K] [IsUnitBall O K] [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] in
theorem pow_l_smul_vec_eq (n : ℕ) (v : Vec K a ι) : ((l : O) ^ n) • v = ((l : K) ^ n) • v := by
  rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem norm_coeff_pow_l_smul_le {P : PhiMod O K l e a ι} {t : Vec K a ι} (ht : t ∈ P.M) (n : ℕ)
    (τ : ZMod a) (i : ι) (k : ℕ) : ‖coeff k ((((l : K) ^ n) • t) τ i)‖ ≤ ‖(l : K)‖ ^ n := by
  simp only [Pi.smul_apply, coeff_smul, smul_eq_mul, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (mem_A.1 (mem_vecs.1 (mem_tot.1 ht τ) i) k)

theorem pow_l_inv_smul_mem_M {P : PhiMod O K l e a ι} {v : Vec K a ι} {n : ℕ}
    (h : ∀ τ i k, ‖coeff k (v τ i)‖ ≤ ‖(l : K)‖ ^ n) : ((l : K) ^ n)⁻¹ • v ∈ P.M :=
  mem_tot.2 fun τ => mem_vecs.2 fun i => mem_A.2 fun k => by
    simp only [Pi.smul_apply, coeff_smul, smul_eq_mul, norm_mul, norm_inv, norm_pow]
    have hl : 0 < ‖(l : K)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l)) n
    rw [inv_mul_le_iff₀ hl, mul_one]
    exact h τ i k

variable [CompleteSpace K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

namespace BKDat

variable (D : BKDat O K l e a ι η H)

theorem mem_Y'_iff_coeff {v : Vec K a ι} : v ∈ D.Y' ↔ E K l e ^ η • v ∈ D.M ∧
    (∀ g, D.desc.act g v = v) ∧ ∀ τ i k, k < e → coeff k (v τ i) = 0 := by
  constructor
  · intro hv
    obtain ⟨y, hy, rfl⟩ := (Descent.mem_Y' _).1 hv
    have h2 := (Descent.mem_invOf _).1 (Descent.Y'_le_Y _ η hv)
    refine ⟨mem_divE.1 h2.1, h2.2, fun τ i k hk => ?_⟩
    show coeff k ((X : K⟦X⟧) ^ e * y τ i) = 0
    rw [coeff_X_pow_mul', if_neg (by omega)]
  · rintro ⟨h1, h2, h3⟩
    have hd : ∀ τ i, (X : K⟦X⟧) ^ e ∣ v τ i := fun τ i => X_pow_dvd_iff.2 fun k hk => h3 τ i k hk
    choose y hy using hd
    have hv : v = (X : K⟦X⟧) ^ e • (y : Vec K a ι) := funext fun τ => funext fun i => hy τ i
    have hXinj : ∀ w w' : Vec K a ι, (X : K⟦X⟧) ^ e • w = (X : K⟦X⟧) ^ e • w' → w = w' :=
      fun w w' h => funext fun τ => funext fun i =>
        mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) (congrFun (congrFun h τ) i)
    refine (Descent.mem_Y' _).2 ⟨y, (Descent.mem_invOf _).2 ⟨mem_divE.2 ?_, fun g => hXinj _ _ ?_⟩, hv.symm⟩
    · refine mem_tot.2 fun τ => mem_vecs.2 fun i => mem_A.2 fun k => ?_
      have := mem_A.1 (mem_vecs.1 (mem_tot.1 h1 τ) i) (k + e)
      have h4 : (E K l e ^ η • v) τ i = (X : K⟦X⟧) ^ e * (E K l e ^ η • y) τ i := by
        rw [hv]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rwa [h4, coeff_X_pow_mul] at this
    · rw [← D.desc.act_X_pow_smul, ← hv, h2 g]

theorem smodEq_Y'_iff (x y : D.Y') (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {(l : O)} ^ n • ⊤ : Submodule O D.Y')] ↔
      ∃ z ∈ D.Y', (x : Vec K a ι) - y = ((l : K) ^ n) • z := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, hb⟩
    refine ⟨b, b.2, ?_⟩
    rw [← pow_l_smul_vec_eq (O := O)]
    exact (congrArg Subtype.val hb).symm
  · rintro ⟨z, hz, h⟩
    refine ⟨⟨z, hz⟩, Submodule.mem_top, Subtype.ext ?_⟩
    show ((l : O) ^ n) • z = (x : Vec K a ι) - y
    rw [pow_l_smul_vec_eq, h]

theorem isHausdorff_Y' : IsHausdorff (Ideal.span {(l : O)}) D.Y' := ⟨fun x hx => by
  have hE : ∀ n τ i k, ‖coeff k ((E K l e ^ η • (x : Vec K a ι)) τ i)‖ ≤ ‖(l : K)‖ ^ n := by
    intro n
    obtain ⟨z, hz, h⟩ := (D.smodEq_Y'_iff x 0 n).1 (hx n)
    rw [ZeroMemClass.coe_zero, sub_zero] at h
    rw [h, smul_comm]
    exact norm_coeff_pow_l_smul_le ((D.mem_Y'_iff_coeff).1 hz).1 n
  have h0 : E K l e ^ η • (x : Vec K a ι) = 0 := funext fun τ => funext fun i => ext fun k =>
    eq_zero_of_norm_le_pow_of_lt_one (norm_nonneg _) (norm_l_lt_one l) fun n => hE n τ i k
  exact Subtype.ext (((isUnit_E (K := K) l e).pow η).smul_left_cancel.1 (h0.trans (smul_zero _).symm))⟩

theorem isPrecomplete_Y' : IsPrecomplete (Ideal.span {(l : O)}) D.Y' := ⟨fun f hf => by
  have hl0 : ∀ n, ((l : K) ^ n) ≠ 0 := fun n => pow_ne_zero _ (l_ne_zero l)
  have hr0 : (0 : ℝ) ≤ ‖(l : K)‖ := norm_nonneg _
  have hr1 : ‖(l : K)‖ < 1 := norm_l_lt_one l
  have hfY : ∀ n, _ := fun n => (D.mem_Y'_iff_coeff).1 (f n).2
  set s : ℕ → Vec K a ι := fun n => E K l e ^ η • (f n : Vec K a ι) with hs_def
  have hs : ∀ m n, m ≤ n → ∀ τ i k, ‖coeff k (s n τ i) - coeff k (s m τ i)‖ ≤ ‖(l : K)‖ ^ m := by
    intro m n hmn τ i k
    obtain ⟨z, hz, h⟩ := (D.smodEq_Y'_iff _ _ m).1 (hf hmn)
    have h' : s m - s n = ((l : K) ^ m) • (E K l e ^ η • z) := by
      simp only [hs_def]
      rw [← smul_sub, h, smul_comm]
    have := norm_coeff_pow_l_smul_le ((D.mem_Y'_iff_coeff).1 hz).1 m τ i k
    rw [← h', Pi.sub_apply, Pi.sub_apply, map_sub] at this
    rwa [norm_sub_rev]
  choose w hw using fun p : ZMod a × ι × ℕ =>
    exists_lim_of_norm_sub_le_pow hr0 hr1 (c := fun n => coeff p.2.2 (s n p.1 p.2.1))
      (fun m n hmn => hs m n hmn p.1 p.2.1 p.2.2)
  set W : Vec K a ι := fun τ i => PowerSeries.mk fun k => w (τ, i, k) with hW_def
  have hW : ∀ n τ i k, ‖coeff k ((s n - W) τ i)‖ ≤ ‖(l : K)‖ ^ n := fun n τ i k => by
    simpa [hW_def] using hw (τ, i, k) n

  have hsinv : ∀ n g, D.desc.act g (s n) = s n := fun n g => by
    simp only [hs_def]
    rw [D.desc.act_E_pow_smul, (hfY n).2.1 g]
  have hWinv : ∀ g, D.desc.act g W = W := fun g => by
    have hsm : ∀ n τ i k, ‖coeff k ((D.desc.act g W - W) τ i)‖ ≤ ‖(l : K)‖ ^ n := by
      intro n
      have hb : ∀ τ i k, ‖coeff k ((W - s n) τ i)‖ ≤ ‖(l : K)‖ ^ n := fun τ i k => by
        rw [Pi.sub_apply, Pi.sub_apply, map_sub, norm_sub_rev, ← map_sub, ← Pi.sub_apply,
          ← Pi.sub_apply]
        exact hW n τ i k
      have ht := pow_l_inv_smul_mem_M (P := D.toPhiMod) hb
      set t := ((l : K) ^ n)⁻¹ • (W - s n) with ht_def
      have hWt : W - s n = ((l : K) ^ n) • t := by rw [ht_def, smul_inv_smul₀ (hl0 n)]
      have : D.desc.act g W - W = ((l : K) ^ n) • (D.desc.act g t - t) := by
        rw [smul_sub, ← map_smul, ← hWt, map_sub, hsinv n g]
        abel
      rw [this]
      exact norm_coeff_pow_l_smul_le (sub_mem (D.desc.act_mem_M g t ht) ht) n
    exact sub_eq_zero.1 (funext fun τ => funext fun i => ext fun k =>
      eq_zero_of_norm_le_pow_of_lt_one hr0 hr1 fun n => hsm n τ i k)
  have hWlow : ∀ τ i, (X : K⟦X⟧) ^ e ∣ W τ i := fun τ i => X_pow_dvd_iff.2 fun k hk => by
    have h0 : coeff k (s 0 τ i) = 0 := by
      have hdv : (X : K⟦X⟧) ^ e ∣ s 0 τ i :=
        Dvd.dvd.mul_left (X_pow_dvd_iff.2 fun k hk => (hfY 0).2.2 τ i k hk) _
      exact X_pow_dvd_iff.1 hdv k hk
    refine eq_zero_of_norm_le_pow_of_lt_one hr0 hr1 fun n => ?_
    have h1 : coeff k (s n τ i) = 0 := by
      have hdv : (X : K⟦X⟧) ^ e ∣ s n τ i :=
        Dvd.dvd.mul_left (X_pow_dvd_iff.2 fun k hk => (hfY n).2.2 τ i k hk) _
      exact X_pow_dvd_iff.1 hdv k hk
    have := hW n τ i k
    rwa [Pi.sub_apply, Pi.sub_apply, map_sub, h1, zero_sub, norm_neg] at this

  obtain ⟨u, hu⟩ := (isUnit_E (K := K) l e).pow η
  set L : Vec K a ι := ((u⁻¹ : K⟦X⟧ˣ) : K⟦X⟧) • W with hL_def
  have hEL : E K l e ^ η • L = W := by
    rw [hL_def, smul_smul, ← hu, Units.mul_inv, one_smul]
  have hLinv : ∀ g, D.desc.act g L = L := fun g => by
    refine ((isUnit_E (K := K) l e).pow η).smul_left_cancel.1 ?_
    rw [← D.desc.act_E_pow_smul, hEL, hWinv g]
  have key : ∀ n, ((l : K) ^ n)⁻¹ • ((f n : Vec K a ι) - L) ∈ D.Y' := fun n => by
    refine (D.mem_Y'_iff_coeff).2 ⟨?_, fun g => ?_, fun τ i k hk => ?_⟩
    · rw [smul_comm, smul_sub, hEL]
      exact pow_l_inv_smul_mem_M (hW n)
    · rw [map_smul, map_sub, (hfY n).2.1 g, hLinv g]
    · have hdv : (X : K⟦X⟧) ^ e ∣ (((l : K) ^ n)⁻¹ • ((f n : Vec K a ι) - L)) τ i := by
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_C_mul]
        refine Dvd.dvd.mul_left (dvd_sub (X_pow_dvd_iff.2 fun k hk => (hfY n).2.2 τ i k hk) ?_) _
        simp only [hL_def, Pi.smul_apply, smul_eq_mul]
        exact Dvd.dvd.mul_left (hWlow τ i) _
      exact X_pow_dvd_iff.1 hdv k hk
  have hLmem : L ∈ D.Y' := by
    have := sub_mem (f 0).2 (key 0)
    rwa [pow_zero, inv_one, one_smul, sub_sub_cancel] at this
  refine ⟨⟨L, hLmem⟩, fun n => (D.smodEq_Y'_iff _ _ n).2 ⟨_, key n, ?_⟩⟩
  exact (smul_inv_smul₀ (hl0 n) _).symm⟩

end BKDat

theorem BKDat.isAdicComplete_Y' : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H),
    IsAdicComplete (Ideal.span {(l : O)}) D.Y' := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D
  exact { toIsHausdorff := D.isHausdorff_Y', toIsPrecomplete := D.isPrecomplete_Y' }

end GlobalTheory.BK
end
end

