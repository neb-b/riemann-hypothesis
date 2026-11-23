module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemRationalConeOfPerturbation
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section SegCone

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι]

theorem exists_indep_rep (v : ι → V) (n : ℕ) : ∀ (t : ι → ℝ), (∀ i, 0 ≤ t i) →
    (by classical exact (Finset.univ.filter (fun i => t i ≠ 0)).card) = n →
    ∃ (S : Finset ι) (s : ι → ℝ), LinearIndepOn ℝ v (S : Set ι) ∧ (∀ i, 0 ≤ s i) ∧ (∀ i, i ∉ S → s i = 0) ∧
      ∑ i, s i • v i = ∑ i, t i • v i := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t ht hn
  set S := Finset.univ.filter (fun i => t i ≠ 0) with hS
  have hSt : ∀ i, i ∉ S → t i = 0 := fun i hi => by simpa [hS] using hi
  by_cases hli : LinearIndepOn ℝ v (S : Set ι)
  · exact ⟨S, t, hli, ht, hSt, rfl⟩
  rw [linearIndepOn_finset_iff] at hli
  push_neg at hli
  obtain ⟨f, hf0, i₀, hi₀, hfi₀⟩ := hli
  obtain ⟨g, hg0, hgS, hgpos⟩ : ∃ g : ι → ℝ, (∑ i, g i • v i = 0) ∧ (∀ i, i ∉ S → g i = 0) ∧ 0 < g i₀ := by
    refine ⟨fun i => if i ∈ S then f i * f i₀ else 0, ?_, fun i hi => by simp [hi], ?_⟩
    · have : ∑ i, (if i ∈ S then f i * f i₀ else 0) • v i = ∑ i ∈ S, (f i * f i₀) • v i := by
        rw [← Finset.sum_subset (Finset.subset_univ S)
          (fun i _ hi => by simp [hi])]
        exact Finset.sum_congr rfl fun i hi => by simp [hi]
      rw [this]
      have h2 : ∑ i ∈ S, (f i * f i₀) • v i = f i₀ • ∑ i ∈ S, f i • v i := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
      rw [h2, hf0, smul_zero]
    · simp only [hi₀, if_true]
      exact mul_self_pos.mpr hfi₀
  have hP : (S.filter (fun i => 0 < g i)).Nonempty := ⟨i₀, by simp [hi₀, hgpos]⟩
  obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image _ (fun i => t i / g i) hP
  have hjS : j ∈ S := (Finset.mem_filter.mp hjP).1
  have hgj : 0 < g j := (Finset.mem_filter.mp hjP).2
  set l := t j / g j with hl
  have hl0 : 0 ≤ l := div_nonneg (ht j) hgj.le
  have ht' : ∀ i, 0 ≤ t i - l * g i := fun i => by
    by_cases hgi : 0 < g i
    · have hiS : i ∈ S := by
        by_contra hi
        rw [hgS i hi] at hgi
        exact lt_irrefl _ hgi
      have := hjmin i (Finset.mem_filter.mpr ⟨hiS, hgi⟩)
      have h3 : l * g i ≤ t i := (le_div_iff₀ hgi).mp this
      linarith
    · have : l * g i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl0 (not_lt.mp hgi)
      linarith [ht i]
  have hlt : (Finset.univ.filter (fun i => t i - l * g i ≠ 0)).card < n := by
    rw [← hn]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j, hjS, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rw [hl, div_mul_cancel₀ _ hgj.ne', sub_self]
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hiS
      apply hi
      rw [hSt i hiS, hgS i hiS]
      simp
  obtain ⟨S', s, h1, h2, h3, h4⟩ := ih _ hlt (fun i => t i - l * g i) ht' (by congr)
  refine ⟨S', s, h1, h2, h3, h4.trans ?_⟩
  have : ∑ i, (t i - l * g i) • v i = ∑ i, t i • v i - l • ∑ i, g i • v i := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [sub_smul, mul_smul]
  rw [this, hg0, smul_zero, sub_zero]

theorem seg_mem_cone (v : ι → V) (B B₀ : V)
    (h : ∀ ε : ℝ, 0 < ε → ∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ B + ε • B₀ = ∑ i, t i • v i) :
    ∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ B = ∑ i, t i • v i := by
  classical
  have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have h' : ∀ k : ℕ, ∃ (S : Finset ι) (s : ι → ℝ), LinearIndepOn ℝ v (S : Set ι) ∧ (∀ i, 0 ≤ s i) ∧
      (∀ i, i ∉ S → s i = 0) ∧ B + (1 / ((k : ℝ) + 1)) • B₀ = ∑ i, s i • v i := fun k => by
    obtain ⟨t, ht, hx⟩ := h _ (hpos k)
    obtain ⟨S, s, h1, h2, h3, h4⟩ := exists_indep_rep v _ t ht rfl
    exact ⟨S, s, h1, h2, h3, hx.trans h4.symm⟩
  choose S s hli hs hS hx using h'
  obtain ⟨S₀, hinf⟩ := Finite.exists_infinite_fiber S
  have hI : (S ⁻¹' {S₀}).Infinite := Set.infinite_coe_iff.mp hinf
  obtain ⟨k₁, hk₁, k₂, hk₂, hne⟩ := hI.nontrivial
  have hk₁' : S k₁ = S₀ := hk₁
  have hk₂' : S k₂ = S₀ := hk₂
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hε
  have hd : ε k₁ - ε k₂ ≠ 0 := by
    intro h0
    apply hne
    have h1 : ε k₁ = ε k₂ := sub_eq_zero.mp h0
    simp only [hε] at h1
    have h2 : (k₁ : ℝ) + 1 ≠ 0 := by positivity
    have h3 : (k₂ : ℝ) + 1 ≠ 0 := by positivity
    field_simp at h1
    have : (k₂ : ℝ) = k₁ := by linarith
    exact_mod_cast this.symm
  set b : ι → ℝ := fun i => (s k₁ i - s k₂ i) / (ε k₁ - ε k₂) with hb
  set a : ι → ℝ := fun i => s k₁ i - ε k₁ * b i with ha
  have hB₀ : B₀ = ∑ i, b i • v i := by
    have h1 : (ε k₁ - ε k₂) • B₀ = ∑ i, (s k₁ i - s k₂ i) • v i := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hx k₁, ← hx k₂]
      simp only [hε]
      abel
    have h2 : B₀ = (ε k₁ - ε k₂)⁻¹ • ∑ i, (s k₁ i - s k₂ i) • v i := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [h2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hb]
    congr 1
    simp only
    rw [div_eq_mul_inv, mul_comm]
  have hB : B = ∑ i, a i • v i := by
    have h1 : ∑ i, a i • v i = ∑ i, s k₁ i • v i - ε k₁ • ∑ i, b i • v i := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [ha]; simp only; rw [sub_smul, mul_smul]
    rw [h1, ← hB₀, ← hx k₁]
    simp only [hε]
    abel
  have hb0 : ∀ i, i ∉ S₀ → b i = 0 := fun i hi => by
    simp only [hb]
    rw [hS k₁ i (hk₁' ▸ hi), hS k₂ i (hk₂' ▸ hi)]
    simp
  have ha0 : ∀ i, i ∉ S₀ → a i = 0 := fun i hi => by
    simp only [ha]
    rw [hb0 i hi, hS k₁ i (hk₁' ▸ hi)]
    simp
  have hcoord : ∀ k, S k = S₀ → ∀ i ∈ S₀, 0 ≤ a i + ε k * b i := fun k hk i hi => by
    have hz : ∑ j ∈ S₀, (a j + ε k * b j - s k j) • v j = 0 := by
      rw [Finset.sum_subset (Finset.subset_univ S₀) (fun j _ hj => by
        rw [ha0 j hj, hb0 j hj, hS k j (hk ▸ hj)]; simp)]
      have h1 : ∑ j, (a j + ε k * b j - s k j) • v j =
          ∑ j, a j • v j + ε k • ∑ j, b j • v j - ∑ j, s k j • v j := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [sub_smul, add_smul, mul_smul]
      rw [h1, ← hB, ← hB₀, ← hx k]
      simp only [hε]
      abel
    have hl := hli k
    rw [hk, linearIndepOn_finset_iff] at hl
    have := hl _ hz i hi
    have h0 := hs k i
    linarith
  refine ⟨a, fun i => ?_, hB⟩
  by_cases hi : i ∈ S₀
  · by_contra hneg
    have hai : a i < 0 := not_le.mp hneg
    obtain ⟨N, hN⟩ := exists_nat_gt (|b i| / (-a i))
    obtain ⟨k, hk, hNk⟩ := hI.exists_gt N
    have hc := hcoord k hk i hi
    have hna : 0 < -a i := by linarith
    have h1 : |b i| < N * (-a i) := (div_lt_iff₀ hna).mp hN
    have h2 : (N : ℝ) < (k : ℝ) + 1 := by
      have : (N : ℝ) < k := by exact_mod_cast hNk
      linarith
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h3 : |b i| < ((k : ℝ) + 1) * (-a i) := lt_trans h1 (mul_lt_mul_of_pos_right h2 hna)
    have h4 : ε k * b i < -a i := by
      simp only [hε]
      rw [one_div, inv_mul_lt_iff₀ hk1]
      exact lt_of_le_of_lt (le_abs_self _) h3
    linarith
  · rw [ha0 i hi]

end SegCone

theorem rcone_closed_seg (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (B B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ)
    (h : ∀ ε : ℝ, 0 < ε → B + ε • B₀ ∈ rcone γ) : B ∈ rcone γ :=
  seg_mem_cone (fun i => toReal (γ i)) B B₀ h

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeAddMem
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section Orth

variable {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂]

def orthSum (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (B₂ : X₂ →ₗ[ℤ] X₂ →ₗ[ℤ] ℝ) :
    (X₁ × X₂) →ₗ[ℤ] (X₁ × X₂) →ₗ[ℤ] ℝ :=
  B₁.compl₁₂ (LinearMap.fst ℤ X₁ X₂) (LinearMap.fst ℤ X₁ X₂) +
    B₂.compl₁₂ (LinearMap.snd ℤ X₁ X₂) (LinearMap.snd ℤ X₁ X₂)

theorem sum_basis_nonneg {K : Type} [Fintype K] (e : Module.Basis K ℤ X₁) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (h : IsPosDef B)
    (c : K → ℝ) : 0 ≤ ∑ k, ∑ l, c k * c l * B (e k) (e l) := by
  by_cases hc : c = 0
  · simp [hc]
  · exact ((isPosDef_iff_basis e B).1 h c hc).le

theorem isPosDef_orthSum {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (e₁ : Module.Basis K₁ ℤ X₁)
    (e₂ : Module.Basis K₂ ℤ X₂) {B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {B₂ : X₂ →ₗ[ℤ] X₂ →ₗ[ℤ] ℝ}
    (h₁ : IsPosDef B₁) (h₂ : IsPosDef B₂) : IsPosDef (orthSum B₁ B₂) := by
  rw [isPosDef_iff_basis (e₁.prod e₂)]
  intro c hc
  have key : ∑ i, ∑ j, c i * c j * orthSum B₁ B₂ ((e₁.prod e₂) i) ((e₁.prod e₂) j) =
      (∑ k, ∑ l, c (Sum.inl k) * c (Sum.inl l) * B₁ (e₁ k) (e₁ l)) +
        ∑ k, ∑ l, c (Sum.inr k) * c (Sum.inr l) * B₂ (e₂ k) (e₂ l) := by
    simp [Fintype.sum_sum_type, Finset.sum_add_distrib, orthSum]
  rw [key]
  by_cases h0 : (fun k => c (Sum.inl k)) = 0
  · have h3 : (fun k => c (Sum.inr k)) ≠ 0 := fun h3 => hc (by
      ext (k | k)
      · exact congrFun h0 k
      · exact congrFun h3 k)
    exact add_pos_of_nonneg_of_pos (sum_basis_nonneg e₁ h₁ _) ((isPosDef_iff_basis e₂ B₂).1 h₂ _ h3)
  · exact add_pos_of_pos_of_nonneg ((isPosDef_iff_basis e₁ B₁).1 h₁ _ h0) (sum_basis_nonneg e₂ h₂ _)

theorem isPosDef_compl_injective {Y : Type} [AddCommGroup Y] {C : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (h : IsPosDef C)
    (j : Y →ₗ[ℤ] X₁) (hj : Function.Injective j) : IsPosDef (C.compl₁₂ j j) := fun n x hx c hc => by
  simpa using h n (fun i => j (x i)) (hx.map' j (LinearMap.ker_eq_bot.2 hj)) c hc

end Orth

section DedekindLFunctions

variable (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]

theorem free_int_of_torsion_eq_bot (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M]
    (ht : Submodule.torsion O M = ⊥) : Module.Free ℤ M := by
  have : Module.Finite ℤ M := Module.Finite.trans O M
  have : HasUniqueDiv M := by
    refine ⟨fun n hn a b hab => ?_⟩
    change n • a = n • b at hab
    have h0 : ((n : ℕ) : O) ≠ 0 := by exact_mod_cast hn
    have h1 : ((n : ℕ) : O) • (a - b) = 0 := by
      rw [Nat.cast_smul_eq_nsmul, smul_sub, hab, sub_self]
    have h2 : a - b ∈ Submodule.torsion O M :=
      (Submodule.mem_torsion_iff _).2 ⟨⟨_, mem_nonZeroDivisors_of_ne_zero h0⟩, h1⟩
    rw [ht] at h2
    exact sub_eq_zero.1 h2
  exact Module.free_of_finite_type_torsion_free'

end DedekindLFunctions

theorem add_mem_psdCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B ∈ psdCone (bar := bar) (X := X) → B' ∈ psdCone (bar := bar) (X := X) → B + B' ∈ psdCone (bar := bar) (X := X) := by
  intro O _ _ _ _ bar X _ _ _ B B' hB hB'
  obtain ⟨X₁, _, _, _, r₁, B₁, hr₁, hb₁, hd₁, he₁⟩ := hB
  obtain ⟨X₂, _, _, _, r₂, B₂, hr₂, hb₂, hd₂, he₂⟩ := hB'
  have : Module.Finite O X₁ := Module.Finite.of_surjective r₁ hr₁
  have : Module.Finite O X₂ := Module.Finite.of_surjective r₂ hr₂
  have ht₁ : Submodule.torsion O X₁ = ⊥ := IsDedekindDomain.flat_iff_torsion_eq_bot.1 inferInstance
  have ht₂ : Submodule.torsion O X₂ = ⊥ := IsDedekindDomain.flat_iff_torsion_eq_bot.1 inferInstance
  have : Module.Free ℤ X₁ := free_int_of_torsion_eq_bot O X₁ ht₁
  have : Module.Free ℤ X₂ := free_int_of_torsion_eq_bot O X₂ ht₂
  have : Module.Finite ℤ X₁ := Module.Finite.trans O X₁
  have : Module.Finite ℤ X₂ := Module.Finite.trans O X₂
  have hdef := isPosDef_orthSum (Module.Free.chooseBasis ℤ X₁) (Module.Free.chooseBasis ℤ X₂) hd₁ hd₂
  let r : X →ₗ[O] X₁ × X₂ := r₁.prod r₂
  let P := LinearMap.range r
  have htP : Submodule.torsion O P = ⊥ := by
    have ht : Submodule.torsion O (X₁ × X₂) = ⊥ := IsDedekindDomain.flat_iff_torsion_eq_bot.1 inferInstance
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨a, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    have h1 : (u : X₁ × X₂) ∈ Submodule.torsion O (X₁ × X₂) :=
      (Submodule.mem_torsion_iff _).2 ⟨a, by simpa using congrArg Subtype.val hau⟩
    rw [ht] at h1
    exact Subtype.ext h1
  have : Module.Flat O P := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htP
  have : Module.FinitePresentation O P := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective O P := Module.Flat.projective_of_finitePresentation
  let j : P →ₗ[ℤ] X₁ × X₂ := P.subtype.toAddMonoidHom.toIntLinearMap
  refine ⟨P, inferInstance, inferInstance, hproj, r.rangeRestrict, (orthSum B₁ B₂).compl₁₂ j j,
    r.surjective_rangeRestrict, ⟨fun y z => ?_, fun a y z => ?_⟩,
    isPosDef_compl_injective hdef j Subtype.val_injective, fun a b => ?_⟩
  · change B₁ _ _ + B₂ _ _ = B₁ _ _ + B₂ _ _
    rw [hb₁.1, hb₂.1]
  · change B₁ (a • _) _ + B₂ (a • _) _ = B₁ _ (bar a • _) + B₂ _ (bar a • _)
    rw [hb₁.2, hb₂.2]
    rfl
  · change B a b + B' a b = B₁ (r₁ a) (r₁ b) + B₂ (r₂ a) (r₂ b)
    rw [he₁, he₂]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeDescendsAlongSurjection
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem eq_zero_of_zsmul_eq_zero_of_projective {O : Type} [CommRing O] [IsDomain O] [CharZero O] {P : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P] {n : ℤ} (hn : n ≠ 0) {z : P} (h : n • z = 0) : z = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O P)
  have hs' : ∀ x, Finsupp.linearCombination O (id : P → P) (s x) = x := fun x => LinearMap.congr_fun hs x
  have h0 : s z = 0 := by
    ext i
    have h1 : n • s z = 0 := by rw [← map_zsmul, h, map_zero]
    have h2 : (n : O) * s z i = 0 := by
      have := DFunLike.congr_fun h1 i
      simpa [zsmul_eq_mul] using this
    have h3 : (n : O) ≠ 0 := by exact_mod_cast hn
    simpa using (mul_eq_zero.1 h2).resolve_left h3
  rw [← hs' z, h0, map_zero]

theorem IsPosDef.eq_zero_of_apply_self {O : Type} [CommRing O] [IsDomain O] [CharZero O] {P : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P] {B : P →ₗ[ℤ] P →ₗ[ℤ] ℝ} (h : IsPosDef B) {z : P}
    (hz : B z z = 0) : z = 0 := by
  by_contra hne
  have hli : LinearIndependent ℤ ![z] := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    by_contra hi
    exact hne (eq_zero_of_zsmul_eq_zero_of_projective (O := O) hi (by simpa using hg))
  have := h 1 _ hli ![1] (by simp)
  simp [hz] at this

theorem exists_psdCone_descend (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X X₁ : Type) [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁] (r : X →ₗ[O] X₁)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hr : Function.Surjective r) (hB : B ∈ psdCone (bar := bar) (X := X))
    (hk : ∀ y, r y = 0 → B y y = 0) : ∃ B₁ ∈ psdCone (bar := bar) (X := X₁), B = pullR r B₁ := by
  obtain ⟨X', _, _, _, r', B', hr', h1, h2, h3⟩ := hB
  have hker : LinearMap.ker r ≤ LinearMap.ker r' := fun y hy =>
    IsPosDef.eq_zero_of_apply_self (O := O) h2 (by rw [← h3]; exact hk y hy)
  let s : X₁ →ₗ[O] X' := ((LinearMap.ker r).liftQ r' hker) ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap
  have hs : ∀ x, s (r x) = r' x := fun x => by
    have : (r.quotKerEquivOfSurjective hr).symm (r x) = (LinearMap.ker r).mkQ x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  have hsurj : Function.Surjective s := fun z => by
    obtain ⟨x, rfl⟩ := hr' z
    exact ⟨r x, hs x⟩
  refine ⟨pullR s B', ⟨X', _, _, inferInstance, s, B', hsurj, h1, h2, fun _ _ => rfl⟩, ?_⟩
  ext a b
  simp [h3, hs]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeExistsMaximalSupport
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_smul_mem_of_le_of_finrank_le {M : Type} [AddCommGroup M] [Module.Finite ℤ M] {P Q : Submodule ℤ M}
    (h : P ≤ Q) (hr : Module.finrank ℤ Q ≤ Module.finrank ℤ P) {y : M} (hy : y ∈ Q) :
    ∃ n : ℤ, n ≠ 0 ∧ n • y ∈ P := by
  have e : (P.comap Q.subtype) ≃ₗ[ℤ] P := Submodule.comapSubtypeEquivOfLe h
  have h1 := Submodule.finrank_quotient_add_finrank (P.comap Q.subtype)
  rw [e.finrank_eq] at h1
  have h2 : Module.finrank ℤ (Q ⧸ P.comap Q.subtype) = 0 := by omega
  obtain ⟨n, hn, hz⟩ := Module.finrank_eq_zero_iff.1 h2 (Submodule.Quotient.mk ⟨y, hy⟩)
  refine ⟨n, hn, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
  simpa using hz

theorem diag_eq_zero_iff_of_isPosDef {X₁ : Type} [AddCommGroup X₁] {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (h : IsPosDef B) (z : X₁) :
    B z z = 0 ↔ z ∈ Submodule.torsion ℤ X₁ := by
  constructor
  · intro h0
    by_contra hz
    have hy : LinearIndependent ℤ ![z] := by
      refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
      obtain rfl : i = 0 := Subsingleton.elim _ _
      by_contra hi
      have hg' : g 0 • z = 0 := by simpa using hg
      exact hz ((Submodule.mem_torsion_iff _).2 ⟨⟨g 0, mem_nonZeroDivisors_of_ne_zero hi⟩, hg'⟩)
    have := h 1 _ hy ![1] (by simp)
    simp [h0] at this
  · intro hz
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hz
    have ha' : (a : ℤ) • z = 0 := ha
    have h1 : ((a : ℤ) : ℝ) * B z z = 0 := by
      rw [← zsmul_eq_mul, ← map_smul, ha', map_zero]
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast nonZeroDivisors.ne_zero a.2)

theorem exists_radical_of_mem_psdCone {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]
    {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone (bar := bar) (X := X)) : ∃ N : Submodule ℤ X, ∀ y, y ∈ N ↔ B y y = 0 := by
  obtain ⟨X₁, _, _, _, r, B₁, -, -, h1, h2⟩ := hB
  refine ⟨(Submodule.torsion ℤ X₁).comap r.toAddMonoidHom.toIntLinearMap, fun y => ?_⟩
  rw [h2, diag_eq_zero_iff_of_isPosDef h1]
  rfl

theorem exists_least_radical : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (K : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ)),
    K.Nonempty → K ⊆ psdCone (bar := bar) (X := X) → (∀ B ∈ K, ∀ B' ∈ K, B + B' ∈ K) →
      ∃ B₁ ∈ K, ∀ B ∈ K, ∀ y, B₁ y y = 0 → B y y = 0 := by
  intro O _ _ _ _ bar X _ _ _ K hne hK hadd
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  choose! N hN using fun B (hB : B ∈ K) => exists_radical_of_mem_psdCone (hK hB)
  have hnn : ∀ B ∈ K, ∀ y, 0 ≤ B y y := fun B hB y => nonneg_of_mem_psdCone (hK hB) y
  obtain ⟨B₁, hB₁, hmin⟩ : ∃ B₁ ∈ K, ∀ B ∈ K, Module.finrank ℤ (N B₁) ≤ Module.finrank ℤ (N B) :=
    ⟨Function.argminOn (fun B => Module.finrank ℤ (N B)) K hne, Function.argminOn_mem _ _ hne,
      fun B hB => Function.argminOn_le (fun B => Module.finrank ℤ (N B)) K hB⟩
  refine ⟨B₁, hB₁, fun B hB y hy => ?_⟩
  have hsum := hadd B hB B₁ hB₁
  have hle : N (B + B₁) ≤ N B₁ := fun z hz => by
    have h0 : B z z + B₁ z z = 0 := by simpa using (hN _ hsum z).1 hz
    exact (hN _ hB₁ z).2 (by linarith [hnn B hB z, hnn B₁ hB₁ z])
  obtain ⟨n, hn, hny⟩ := exists_smul_mem_of_le_of_finrank_le hle (hmin _ hsum) ((hN _ hB₁ y).2 hy)
  have h0 : B (n • y) (n • y) + B₁ (n • y) (n • y) = 0 := by simpa using (hN _ hsum _).1 hny
  have h1 : B (n • y) (n • y) = 0 := by linarith [hnn B hB (n • y), hnn B₁ hB₁ (n • y)]
  have h2 : ((n : ℝ) * (n : ℝ)) * B y y = 0 := by
    rw [← h1]
    simp only [map_smul, LinearMap.smul_apply, zsmul_eq_mul]
    ring
  exact (mul_eq_zero.1 h2).resolve_left (mul_ne_zero (by exact_mod_cast hn) (by exact_mod_cast hn))

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VorFunHomogSuperadd
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem evalR_vorFun_eq (O : Type) [CommRing O] [Module.Finite ℤ O] (g : ℕ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Finite ℤ X] {d : ℕ} {s : (Fin d → ℤ) →ₗ[ℤ] X} (hs : Function.Surjective s)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalR (vorFun O g) B = (fineDen g {1} : ℝ) *
      ((((1 : ℕ) : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin 1 (fun a b => B (s a) (s b)) y := by
  have h0 : zeroFun.eval X (fun a b => B a b) = 0 := by
    rw [zeroFun.eval_eq hs]
    rfl
  rw [evalR, vorFun, eval_baseFun, h0, Finset.sum_singleton, fineMean_eval_eq 1 hs, zero_add, mul_assoc]

theorem vorFun_homog_superadd : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (g : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X],
    (∀ B ∈ psdCone (bar := bar) (X := X), ∀ t : ℝ, 0 ≤ t → evalR (vorFun O g) (t • B) = t * evalR (vorFun O g) B) ∧
    ∀ B ∈ psdCone (bar := bar) (X := X), ∀ B' ∈ psdCone (bar := bar) (X := X),
      evalR (vorFun O g) B + evalR (vorFun O g) B' ≤ evalR (vorFun O g) (B + B') := by
  intro O _ _ _ _ bar g X _ _ _
  have : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨d, s, hs⟩ := Module.Finite.exists_fin' ℤ X
  have hc : (0 : ℝ) ≤ (fineDen g {1} : ℝ) * ((((1 : ℕ) : ℝ) + 1) ^ d)⁻¹ := by positivity
  refine ⟨fun B _ t ht => ?_, fun B hB B' hB' => ?_⟩
  · rw [evalR_vorFun_eq O g hs, evalR_vorFun_eq O g hs]
    simp only [LinearMap.smul_apply, smul_eq_mul, classMin_smul ht, ← Finset.mul_sum]
    ring
  · rw [evalR_vorFun_eq O g hs, evalR_vorFun_eq O g hs, evalR_vorFun_eq O g hs, ← mul_add,
      ← Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) hc
    simp only [LinearMap.add_apply]
    exact classMin_add_le (fun a => nonneg_of_mem_psdCone hB _) (fun a => nonneg_of_mem_psdCone hB' _) y

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

