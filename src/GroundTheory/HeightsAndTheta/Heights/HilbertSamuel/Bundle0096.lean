module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0044

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem LiftModel.ideal_eq_top_of_pow_mem {A : Type} [CommRing A] (J : Ideal A) {m : ℕ} (hm0 : m ≠ 0) (e : ℕ)
    (hm : (m : A) ^ e ∈ J) (hp : ∀ p ∈ m.primeFactors, J ⊔ Ideal.span {(p : A)} = ⊤) : J = ⊤ := by
  by_contra hJ
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
  have hmM : (m : A) ∈ M := hM.isPrime.mem_of_pow_mem e (hJM hm)
  rw [Nat.prod_primeFactors_pow_factorization hm0, Nat.cast_prod] at hmM
  obtain ⟨p, hp', hpM⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hM.isPrime)).mp hmM
  rw [Nat.cast_pow] at hpM
  have h1 : (p : A) ∈ M := hM.isPrime.mem_of_pow_mem _ hpM
  have hle : J ⊔ Ideal.span {(p : A)} ≤ M := sup_le hJM ((Ideal.span_singleton_le_iff_mem M).mpr h1)
  rw [hp p hp'] at hle
  exact hM.ne_top (top_le_iff.mp hle)

theorem LiftModel.mem_chartRingZ_of_mem_chartLat {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {n : K → ℤ} {x : Ω} (hx : x ∈ chartLat y n 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : x * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingZ y c := by
  have h := hx c hc
  simpa using h

theorem LiftModel.combine {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (n : K → ℤ) {m : ℕ} (hm0 : m ≠ 0) {r₁ : ℕ} (x₁ : Fin r₁ → Ω)
    (hx₁ : ∀ j, x₁ j ∈ chartLat y n 1)
    (hg₁ : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (e : ℕ) (u : Fin r₁ → Ω), (∀ j, u j ∈ chartRingZ y c) ∧
      ∑ j, u j * (x₁ j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) = (m : Ω) ^ e)
    (rP : ℕ → ℕ) (xP : ∀ p, Fin (rP p) → Ω) (hxP : ∀ p ∈ m.primeFactors, ∀ j, xP p j ∈ chartLat y n 1)
    (hgP : ∀ p ∈ m.primeFactors, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin (rP p) → Ω) (v : Ω),
      (∀ j, u j ∈ chartRingZ y c) ∧ v ∈ chartRingZ y c ∧
        ∑ j, u j * (xP p j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) + p * v = 1)
    {r₃ : ℕ} (x₃ : Fin r₃ → Ω) (hx₃ : ∀ j, x₃ j ∈ chartLat y n 1) :
    ∃ F : Finset Ω, (∀ f ∈ F, f ∈ chartLat y n 1) ∧ KH.GeneratesOn y n (fun f : F => (f : Ω)) ∧
      ∀ j, x₃ j ∈ F := by
  classical
  let F : Finset Ω := Finset.univ.image x₁ ∪ m.primeFactors.biUnion (fun p => Finset.univ.image (xP p)) ∪
    Finset.univ.image x₃
  have h₁F : ∀ j, x₁ j ∈ F := fun j => by simp [F]
  have hPF : ∀ p ∈ m.primeFactors, ∀ j, xP p j ∈ F := by
    intro p hp j
    simp only [F, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inr ⟨p, hp, j, rfl⟩)
  have h₃F : ∀ j, x₃ j ∈ F := fun j => by simp [F]
  have hFmem : ∀ f ∈ F, f ∈ chartLat y n 1 := by
    intro f hf
    simp only [F, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hf
    rcases hf with (⟨j, rfl⟩ | ⟨p, hp, j, rfl⟩) | ⟨j, rfl⟩
    · exact hx₁ j
    · exact hxP p hp j
    · exact hx₃ j
  refine ⟨F, hFmem, fun c hc => ?_, h₃F⟩
  let v : F → chartRingZ y c := fun f =>
    ⟨(f : Ω) * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem f f.2) c hc⟩
  have hv : ∀ f (hf : f ∈ F), (⟨f * ∏ k, y ⟨k, c k⟩ ^ (-n k),
      LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem f hf) c hc⟩ : chartRingZ y c) ∈ Ideal.span (Set.range v) :=
    fun f hf => Ideal.subset_span ⟨⟨f, hf⟩, rfl⟩
  obtain ⟨e, u, hu, hsum⟩ := hg₁ c hc
  have htop : Ideal.span (Set.range v) = ⊤ := by
    refine LiftModel.ideal_eq_top_of_pow_mem _ hm0 e ?_ fun p hp => ?_
    · have heq : ((m : chartRingZ y c) ^ e) = ∑ j, (⟨u j, hu j⟩ : chartRingZ y c) *
          ⟨x₁ j * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem _ (h₁F j)) c hc⟩ := by
        apply Subtype.val_injective
        push_cast
        exact hsum.symm
      rw [heq]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv _ (h₁F j))
    · obtain ⟨u', w, hu', hw, hsum'⟩ := hgP p hp c hc
      rw [Ideal.eq_top_iff_one]
      have heq : (1 : chartRingZ y c) = ∑ j, (⟨u' j, hu' j⟩ : chartRingZ y c) *
          ⟨xP p j * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem _ (hPF p hp j)) c hc⟩ +
          (p : chartRingZ y c) * ⟨w, hw⟩ := by
        apply Subtype.val_injective
        push_cast
        exact hsum'.symm
      rw [heq]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv _ (hPF p hp j))))
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
  have h1 : (1 : chartRingZ y c) ∈ Ideal.span (Set.range v) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  refine ⟨fun f => (a f : Ω), fun f => (a f).2, ?_⟩
  have h := congrArg Subtype.val ha
  push_cast at h
  exact h

theorem LiftModel.isMultiHomog_rename {κ κ' : Type} [Fintype κ] [Fintype κ']
    (φ : (Σ _ : Unit, κ) → (Σ _ : Unit, κ')) {g : MRing (fun _ : Unit => κ)} {d : Unit → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename φ g) d := by
  have hdeg : ∀ {τ : Type} [Fintype τ] (m : (Σ _ : Unit, τ) →₀ ℕ), m.degree = ∑ i, m ⟨(), i⟩ := by
    intro τ _ m
    classical
    rw [Finsupp.degree_apply, Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
      simpa using hx), Fintype.sum_sigma, Fintype.sum_unique]
  have hw : ∀ {τ : Type} (m : τ →₀ ℕ), Finsupp.weight 1 m = m.degree := by
    intro τ m
    rw [Finsupp.degree_eq_weight_one]
    rfl
  have hH : g.IsHomogeneous (d ()) := by
    intro m hm
    rw [hw, hdeg]
    exact hg m (mem_support_iff.mpr hm) ()
  have h := hH.rename_isHomogeneous (f := φ)
  intro m hm k
  have := h (mem_support_iff.mp hm)
  rw [hw, hdeg] at this
  exact this

theorem LiftModel.birational_of_subfamily {Ω : Type} [Field Ω] {r : ℕ} (x₃ : Fin r → Ω) (F : Finset Ω)
    (h : ∀ j, x₃ j ∈ F) (hb : Birational (fun p : Σ _ : Unit, Fin r => x₃ p.2)) :
    Birational (fun p : Σ _ : Unit, F => (p.2 : Ω)) := by
  intro s
  obtain ⟨d, g, g', hg, hg', hg0, hgs⟩ := hb s
  let φ : (Σ _ : Unit, Fin r) → (Σ _ : Unit, F) := fun p => ⟨(), ⟨x₃ p.2, h p.2⟩⟩
  have hev : ∀ f : MRing (fun _ : Unit => Fin r), aeval (fun p : Σ _ : Unit, F => (p.2 : Ω)) (rename φ f) =
      aeval (fun p : Σ _ : Unit, Fin r => x₃ p.2) f := fun f => by
    rw [aeval_rename]
    rfl
  refine ⟨d, rename φ g, rename φ g', LiftModel.isMultiHomog_rename φ hg, LiftModel.isMultiHomog_rename φ hg', ?_, ?_⟩
  · rw [hev]
    exact hg0
  · rw [hev, hev]
    exact hgs

theorem LiftModel.core {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω)
    (N : K → ℤ) (B : ∀ r : ℕ, (Fin r → Ω) → Prop) {q₁ m t₁ : ℕ} (hq₁ : 1 ≤ q₁) (hm : 1 ≤ m)
    (h₁ : ∀ t : ℕ, t₁ ≤ t → ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q₁) • N) 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (e : ℕ) (u : Fin r → Ω), (∀ j, u j ∈ chartRingZ y c) ∧
        ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * q₁) • N) k)) = (m : Ω) ^ e)
    (qP tP : ℕ → ℕ) (hqP : ∀ p ∈ m.primeFactors, 1 ≤ qP p)
    (hP : ∀ p ∈ m.primeFactors, ∀ t : ℕ, tP p ≤ t → ∃ (r : ℕ) (x' : Fin r → Ω),
      (∀ j, x' j ∈ chartLat y ((t * qP p) • N) 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin r → Ω) (v : Ω), (∀ j, u j ∈ chartRingZ y c) ∧
        v ∈ chartRingZ y c ∧ ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * qP p) • N) k)) + p * v = 1)
    {q₃ t₃ : ℕ} (hq₃ : 1 ≤ q₃)
    (h₃ : ∀ t : ℕ, t₃ ≤ t → ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q₃) • N) 1) ∧ B r x') :
    ∃ (a : ℕ) (F : Finset Ω), 1 ≤ a ∧ (∀ f ∈ F, f ∈ chartLat y (a • N) 1) ∧
      KH.GeneratesOn y (a • N) (fun f : F => (f : Ω)) ∧ ∃ (r : ℕ) (x₃ : Fin r → Ω), (∀ j, x₃ j ∈ F) ∧ B r x₃ := by
  classical
  have hprod : ∀ s ⊆ m.primeFactors, 1 ≤ ∏ p ∈ s, qP p := fun s hs =>
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp => by have := hqP p (hs hp); omega)
  have hprodS := hprod m.primeFactors subset_rfl
  set t := t₁ + t₃ + ∑ p ∈ m.primeFactors, tP p + 1 with ht
  set Q := q₁ * q₃ * ∏ p ∈ m.primeFactors, qP p with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have ht1 : 1 ≤ t := by omega

  have hT₁ : t₁ ≤ t * (q₃ * ∏ p ∈ m.primeFactors, qP p) :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ (by positivity))
  obtain ⟨r₁, x₁, hx₁, hg₁⟩ := h₁ _ hT₁
  have e₁ : t * (q₃ * ∏ p ∈ m.primeFactors, qP p) * q₁ = t * Q := by rw [hQ]; ring
  rw [e₁] at hx₁ hg₁

  have hT₃ : t₃ ≤ t * (q₁ * ∏ p ∈ m.primeFactors, qP p) :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ (by positivity))
  obtain ⟨r₃, x₃, hx₃, hB₃⟩ := h₃ _ hT₃
  have e₃ : t * (q₁ * ∏ p ∈ m.primeFactors, qP p) * q₃ = t * Q := by rw [hQ]; ring
  rw [e₃] at hx₃

  have hP' : ∀ p ∈ m.primeFactors, ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * Q) • N) 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin r → Ω) (v : Ω), (∀ j, u j ∈ chartRingZ y c) ∧
        v ∈ chartRingZ y c ∧ ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * Q) • N) k)) + p * v = 1 := by
    intro p hp
    have hprodp := hprod (m.primeFactors.erase p) (Finset.erase_subset _ _)
    have htp : tP p ≤ t := by
      have := Finset.single_le_sum (f := tP) (fun _ _ => Nat.zero_le _) hp
      omega
    have hTp : tP p ≤ t * (q₁ * q₃ * ∏ p' ∈ m.primeFactors.erase p, qP p') :=
      le_trans htp (Nat.le_mul_of_pos_right _ (by positivity))
    obtain ⟨r, x', hx, hg⟩ := hP p hp _ hTp
    have ep : t * (q₁ * q₃ * ∏ p' ∈ m.primeFactors.erase p, qP p') * qP p = t * Q := by
      rw [hQ, ← Finset.mul_prod_erase m.primeFactors qP hp]
      ring
    rw [ep] at hx hg
    exact ⟨r, x', hx, hg⟩
  choose! rP xP hxP hgP using hP'
  obtain ⟨F, hFmem, hFgen, hF₃⟩ :=
    LiftModel.combine y ((t * Q) • N) (by omega) x₁ hx₁ hg₁ rP xP hxP hgP x₃ hx₃
  exact ⟨t * Q, F, Nat.one_le_iff_ne_zero.mpr (by positivity), hFmem, hFgen, r₃, x₃, hF₃, hB₃⟩

theorem LiftModel.proof (hS : LiftSpread.Statement) (hA : LiftAtPrime.Statement)
    (hB : LiftBirationalAmple.Statement) : LiftModel.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D N hV hbir hQ hcQ hF
  classical
  obtain ⟨c, hc1, hcQ⟩ := hcQ
  obtain ⟨q₁, m, t₁, hq₁, hm, h₁⟩ := hS K ι Ω y D N hV hQ
  have hP := fun p (hp : p ∈ m.primeFactors) =>
    hA K ι Ω y D N p hV (Nat.prime_of_mem_primeFactors hp) (hF p (Nat.prime_of_mem_primeFactors hp))
  choose! qP tP hqP hP using hP
  obtain ⟨q₃, t₃, hq₃, h₃⟩ := hB K ι Ω y D N c hV hbir hc1 hcQ
  obtain ⟨a, F, ha, hmem, hgen, r, x₃, hx₃F, hbir₃⟩ :=
    LiftModel.core y N (fun r x => Birational (fun p : Σ _ : Unit, Fin r => x p.2)) hq₁ hm h₁ qP tP hqP hP hq₃ h₃
  exact ⟨a, {x // x ∈ F}, inferInstance, Subtype.val, ha, fun j => hmem j j.2, hgen,
    LiftModel.birational_of_subfamily x₃ F hx₃F hbir₃⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocIdealKer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace LocIdealKer

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {𝓜 : (K → ℤ) → Submodule S M}

def degProducts (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (D : K → ℤ) : Set M :=
  {x | ∃ (p : MRingOver S ι) (b : K → ℕ) (n : M), p ∈ P ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p b ∧
    n ∈ 𝓜 (D - fun k => (b k : ℤ)) ∧ x = p • n}

theorem span_degProducts_le (h𝓜 : KH.IsMGraded S ι 𝓜) (P : Ideal (MRingOver S ι)) (D : K → ℤ) :
    Submodule.span S (degProducts 𝓜 P D) ≤ 𝓜 D := by
  rw [Submodule.span_le]
  rintro _ ⟨p, b, n, -, hp, hn, rfl⟩
  have := h𝓜.2 b _ p n hp hn
  rwa [sub_add_cancel] at this

theorem exists_near (h𝓜 : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)} (hP : IsMultiHomogIdeal P)
    (D : K → ℤ) {x : M} (hx : x ∈ (P • ⊤ : Submodule (MRingOver S ι) M)) :
    ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
  classical
  obtain ⟨G, hG, hPG⟩ := hP
  have hadd : ∀ x₁ x₂ : M,
      (∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₁ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) →
      (∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₂ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) →
      ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₁ + x₂ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
    rintro x₁ x₂ ⟨y₁, hy₁, e₁⟩ ⟨y₂, hy₂, e₂⟩
    refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
    rw [add_sub_add_comm]
    exact add_mem e₁ e₂
  have hzero : ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), (0 : M) - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j :=
    ⟨0, zero_mem _, by rw [sub_zero]; exact zero_mem _⟩

  have hgen : ∀ g ∈ G, ∀ n : M,
      ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), g • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
    intro g hg n
    obtain ⟨b, hb⟩ := hG g hg
    have hgP : g ∈ P := by rw [hPG]; exact Ideal.subset_span hg
    have hn : n ∈ ⨆ j, 𝓜 j := by
      rw [h𝓜.1.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (motive := fun n => ∃ y ∈ Submodule.span S (degProducts 𝓜 P D),
      g • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) 𝓜 hn ?_ ?_ ?_
    · intro j n hn
      have hgn := h𝓜.2 b j g n hb hn
      by_cases hj : (j + fun k => (b k : ℤ)) = D
      · refine ⟨g • n, Submodule.subset_span ⟨g, b, n, hgP, hb, ?_, rfl⟩, ?_⟩
        · rw [← hj, add_sub_cancel_right]
          exact hn
        · rw [sub_self]
          exact zero_mem _
      · refine ⟨0, zero_mem _, ?_⟩
        rw [sub_zero]
        exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hj hgn)
    · rw [smul_zero]
      exact hzero
    · intro n₁ n₂ h₁ h₂
      rw [smul_add]
      exact hadd _ _ h₁ h₂

  have hP' : ∀ p ∈ P, ∀ n : M,
      ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), p • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
    intro p hp
    rw [hPG] at hp
    induction hp using Submodule.span_induction with
    | mem g hg => exact hgen g hg
    | zero =>
      intro n
      rw [zero_smul]
      exact hzero
    | add p q _ _ hp hq =>
      intro n
      rw [add_smul]
      exact hadd _ _ (hp n) (hq n)
    | smul r p _ hp =>
      intro n
      rw [smul_eq_mul, mul_comm, mul_smul]
      exact hp (r • n)
  exact Submodule.smul_induction_on hx (fun p hp n _ => hP' p hp n) (fun x₁ x₂ h₁ h₂ => hadd _ _ h₁ h₂)

theorem mem_span_degProducts (h𝓜 : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)} (hP : IsMultiHomogIdeal P)
    {D : K → ℤ} {x : M} (hx : x ∈ (P • ⊤ : Submodule (MRingOver S ι) M)) (hxD : x ∈ 𝓜 D) :
    x ∈ Submodule.span S (degProducts 𝓜 P D) := by
  obtain ⟨y, hy, hd⟩ := exists_near h𝓜 hP D hx
  have hc : x - y ∈ 𝓜 D := sub_mem hxD (span_degProducts_le h𝓜 P D hy)
  have h0 : x - y = 0 := Submodule.disjoint_def.mp (h𝓜.1.submodule_iSupIndep D) _ hc hd
  rw [sub_eq_zero] at h0
  rw [h0]
  exact hy

theorem proof : LocIdealKer.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 P T d h𝓜 hP hT w hw
  classical
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  set N := (P • ⊤ : Submodule (MRingOver S ι) M) with hN
  set L := IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M)
    (LocalizedModule.mkLinearMap T (M ⧸ N)) N.mkQ with hL
  have hLmk : ∀ (m : M) (t : T), L (LocalizedModule.mk m t) = LocalizedModule.mk (N.mkQ m) t := by
    intro m t
    rw [hL, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']
  constructor
  ·
    have hkill : ∀ p ∈ P, ∀ z : LocalizedModule T (M ⧸ N), p • z = 0 := by
      intro p hp z
      induction z using LocalizedModule.induction_on with
      | h q t =>
        obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective N q
        rw [LocalizedModule.smul'_mk, ← map_smul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2
          (Submodule.smul_mem_smul hp Submodule.mem_top), LocalizedModule.zero_mk]
    intro hwP
    clear hw
    induction hwP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, a, y, hp, -, -, rfl⟩ := hx
      rw [map_smul]
      exact hkill p hp _
    | zero => exact map_zero L
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul s x _ hx =>
      rw [← algebraMap_smul (MRingOver S ι) s x, map_smul, hx, smul_zero]
  · intro h0
    obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hw
    rw [hLmk, ← LocalizedModule.zero_mk (1 : T), LocalizedModule.mk_eq] at h0
    obtain ⟨u, hu⟩ := h0
    rw [one_smul, smul_zero, smul_zero, Submonoid.smul_def, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hu
    obtain ⟨e, he⟩ := hT u u.2
    set D : K → ℤ := (d + fun k => (a k : ℤ)) + fun k => (e k : ℤ) with hD
    have humD : (u : MRingOver S ι) • m ∈ 𝓜 D := h𝓜.2 e _ _ m he hm
    have hspan := mem_span_degProducts h𝓜 hP hu humD
    have hut : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog ((u * t : T) : MRingOver S ι) (e + a) := GenSESStep.isMultiHomog_mul he ht
    rw [← LocalizedModule.mk_cancel_common_left u t m, Submonoid.smul_def]
    generalize (u : MRingOver S ι) • m = x at hspan ⊢
    induction hspan using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, b, n, hp, hpb, hn, rfl⟩ := hx
      rw [← LocalizedModule.smul'_mk]
      refine Submodule.subset_span ⟨p, b, _, hp, hpb, GenSESStep.mk_mem_locPart n (u * t) (e + a) hut ?_, rfl⟩
      have edeg : ((d - fun k => (b k : ℤ)) + fun k => ((e + a) k : ℤ)) = D - fun k => (b k : ℤ) := by
        funext k
        simp only [hD, Pi.add_apply, Pi.sub_apply, Nat.cast_add]
        ring
      rw [edeg]
      exact hn
    | zero =>
      rw [LocalizedModule.zero_mk]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_add, ← IsLocalizedModule.mk_eq_mk',
        ← IsLocalizedModule.mk_eq_mk']
      exact add_mem hx hy
    | smul s x _ hx =>
      rw [← LocalizedModule.smul'_mk]
      exact Submodule.smul_mem _ s hx

end LocIdealKer

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbSemipos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace PerturbedSemipositivity

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem blocks_mem_nhds {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    {y : (Σ k, ι k) → ℂ | ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0} ∈ 𝓝 z := by
  have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
      fun y hy => ⟨i, hy⟩
  exact Filter.eventually_all.mpr hopen

theorem contDiffAt_log_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z := by
  have h := hA.contDiffAt (blocks_mem_nhds hz)
  exact (h.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)).log (A.pos z hz).ne'

theorem levi_const_mul {f : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z)
    (w : (Σ k, ι k) → ℂ) :
    ReciprocityTheory.AnForm.levi (fun y => c * f y) z w = c * ReciprocityTheory.AnForm.levi f z w := by
  have h := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ)) (g := f) c contDiffAt_const hf w
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : (Σ k, ι k) → ℂ => (0 : ℝ)) z w = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  simp only [zero_add] at h
  rw [h, h0, zero_add]

end PerturbedSemipositivity


open PerturbedSemipositivity in
theorem PerturbSemipos.proof : PerturbSemipos.Statement := by
  intro K _ ι _ P0 P M b a hM hb ha
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  have hfun : (HermLine.zcomb M (fsH ι) m n).h = fun y => M.h y ^ m * (fsH ι).h y ^ n := by
    funext y
    simp [HermLine.zcomb]
  refine ⟨?_, fun z hz w hw => ?_⟩
  · have hMs : IsSmoothHerm M := hM.1
    unfold IsSmoothHerm at hMs hH ⊢
    rw [hfun]
    exact (hMs.pow m).mul (hH.pow n)
  · have hz' := hz.1
    have hev : (fun y => Real.log ((HermLine.zcomb M (fsH ι) m n).h y)) =ᶠ[𝓝 z]
        fun y => (m : ℝ) * Real.log (M.h y) + (n : ℝ) * Real.log ((fsH ι).h y) := by
      filter_upwards [blocks_mem_nhds hz'] with y hy
      rw [hfun, Real.log_mul (pow_ne_zero _ (M.pos y hy).ne') (pow_ne_zero _ ((fsH ι).pos y hy).ne'),
        Real.log_pow, Real.log_pow]
    have hfM := contDiffAt_log_h M hM.1 hz'
    have hfH := contDiffAt_log_h (fsH ι) hH hz'
    have hadd := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => (m : ℝ) * Real.log (M.h y))
      (g := fun y => Real.log ((fsH ι).h y)) (n : ℝ) (contDiffAt_const.mul hfM) hfH w
    beta_reduce at hadd
    have h1 : 0 ≤ leviForm (fun y => Real.log (M.h y)) z w := hM.2 z hz w hw
    have h2 : 0 ≤ leviForm (fun y => Real.log ((fsH ι).h y)) z w := FsLineLevi.proof K ι z w hz'
    change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
    rw [ReciprocityTheory.AnForm.levi_congr hev, hadd, levi_const_mul (m : ℝ) hfM w]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg m) h1) (mul_nonneg (Nat.cast_nonneg n) h2)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

