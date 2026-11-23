module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0033
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0039
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0018
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FormRightMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0037
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardEqRelIndex
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsEquivOfMemEndL

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormLeOfMemBoxSet
section
open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem boxSet_finite (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) :
    (boxSet K F T).Finite := by
  refine Set.Finite.of_finite_image (f := fun n : 𝓞 F => algebraMap F K (n : F)) ?_
    (fun a _ b _ hab => RingOfIntegers.ext ((algebraMap F K).injective hab))
  refine (NumberField.Embeddings.finite_of_norm_le K ℂ T).subset ?_
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨map_isIntegral_int (algebraMap F K) (RingOfIntegers.isIntegral_coe n), fun φ => ?_⟩
  have hst : star (algebraMap F K (n : F)) = algebraMap F K (n : F) := (hF _).mpr ⟨_, rfl⟩
  have hc := hK.2.1 φ (algebraMap F K (n : F))
  rw [hst] at hc
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hc.symm
  have h1 := hn φ
  simp only at h1 ⊢
  rw [hr] at h1 ⊢
  rw [Complex.ofReal_re] at h1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1.1]
  exact h1.2

theorem ne_zero_of_mem_boxSet {T : ℝ} {n : 𝓞 F} (hn : n ∈ boxSet K F T) : n ≠ 0 := by
  rintro rfl
  obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
  have := (hn φ).1
  simp at this

theorem absNorm_le_of_mem_boxSet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K := by
  by_contra hlt
  have := box_inter_eq_empty hK hF (b := Ideal.span {n}) (not_le.mp hlt)
  have hmem : n ∈ {n' : 𝓞 F | n' ∈ boxSet K F T ∧ n' ∈ Ideal.span {n}} :=
    ⟨hn, Ideal.mem_span_singleton_self n⟩
  rw [this] at hmem
  exact hmem

def eFac (K : Type) {F : Type} [Field K] [Field F] [NumberField F] [Algebra F K] (m : ℕ)
    (𝔭 : Ideal (𝓞 F)) : ℝ :=
  1 - etaF K F 𝔭 ^ m * (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ))

theorem eFac_pos {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {m : ℕ} (hm : 1 ≤ m) : 0 < eFac K m 𝔭 := by
  have hq : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by exact_mod_cast two_le_absNorm h𝔭
  have h1 := IdealNormInequalities.zpow_neg_lt_one hq hm
  have h0 : 0 ≤ (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) := zpow_nonneg (by linarith) _
  have hη : |etaF K F 𝔭 ^ m| = 1 := by
    rw [abs_pow]
    unfold etaF
    split_ifs <;> simp
  have h2 : etaF K F 𝔭 ^ m * (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) ≤
      (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) := by
    calc _ ≤ |etaF K F 𝔭 ^ m| * (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ = _ := by rw [hη, one_mul]
  unfold eFac
  linarith

theorem alphaN_eq_stage (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) :
    ∃ k : ℕ, alphaN h L 𝔭 n =
      (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    have := two_le_absNorm h𝔭
    exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)
  set k0 := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2
  refine ⟨k0, ?_⟩
  refine Tendsto.limUnder_eq (tendsto_atTop_of_eventually_const (i₀ := k0) fun k hk => ?_)
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih, nkCount_succ hK hF hs hd hL hLi h𝔭 hn hk]
    generalize 2 * finrank K V - 1 = r
    rw [add_mul, one_mul, pow_add]
    push_cast
    field_simp

theorem alphaN_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ C : ℝ, ∀ n : 𝓞 F, n ≠ 0 → 0 ≤ alphaN h L 𝔭 n ∧ alphaN h L 𝔭 n ≤ C := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    have := two_le_absNorm h𝔭
    exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)
  obtain ⟨C, hC⟩ := nkCount_le hK hF hs hd hL hLi hm h𝔭
  refine ⟨C, fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := alphaN_eq_stage hK hF hs hd hL hLi h𝔭 hn
  rw [hk]
  exact ⟨by positivity, (div_le_iff₀ (by positivity)).mpr (hC k n)⟩

end Formalism.HermitianLattices.Ext.L3.A5
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ApplyMemSmulOfMemAutSub
section
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem pow_smul_anti (𝔭 : Ideal (𝓞 F)) (A : Submodule (𝓞 K) V) {i j : ℕ} (hij : i ≤ j) :
    ((extP K 𝔭) ^ j • A : Submodule (𝓞 K) V) ≤ (extP K 𝔭) ^ i • A := Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)

theorem exists_pow_smul_le {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, ((extP K 𝔭) ^ r • locF 𝔭 M₁ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₂ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM₁ hM₂
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := D2.exists_mul_dvd h𝔭 hc
  refine ⟨r, ?_⟩
  have key : extP K 𝔭 ^ r ≤ (locF 𝔭 M₂).colon (locF 𝔭 M₁ : Set V) := by
    unfold extP
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Submodule.mem_colon]
    intro x hx
    obtain ⟨s, hs, hsx⟩ := (LocalSpans.mem_locF 𝔭 M₁ x).1 hx
    obtain ⟨d, hd⟩ := hdvd a ha
    refine (LocalSpans.mem_locF 𝔭 M₂ _).2
      ⟨u * s, fun h => (h𝔭.isPrime.mem_or_mem h).elim hu hs, ?_⟩
    have e : algebraMap (𝓞 F) (𝓞 K) (u * s) • algebraMap (𝓞 F) (𝓞 K) a • x =
        algebraMap (𝓞 F) (𝓞 K) d • (n • (algebraMap (𝓞 F) (𝓞 K) s • x)) := by
      rw [← LocF.algebraMap_intCast_smul (F := F) (K := K) n]
      simp only [smul_smul, ← map_mul]
      congr 2
      linear_combination s * hd
    rw [e]
    exact M₂.smul_mem _ (hnx _ hsx)
  rw [Submodule.smul_le]
  intro a ha x hx
  exact Submodule.mem_colon.1 (key ha) x hx

set_option linter.unusedVariables false in
theorem locF_inf {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A B : Submodule (𝓞 K) V}
    (hA : locF 𝔭 A = A) (hB : locF 𝔭 B = B) : locF 𝔭 (A ⊓ B) = A ⊓ B := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · exact (LocF.locF_mono 𝔭 inf_le_left).trans hA.le
    · exact (LocF.locF_mono 𝔭 inf_le_right).trans hB.le
  · exact LocF.le_locF 𝔭 _

theorem locF_inf_locF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A B : Submodule (𝓞 K) V) :
    locF 𝔭 (A ⊓ B) = locF 𝔭 A ⊓ locF 𝔭 B := by
  have := h𝔭.isPrime
  apply le_antisymm
  · exact le_inf (LocF.locF_mono 𝔭 inf_le_left) (LocF.locF_mono 𝔭 inf_le_right)
  · rintro x ⟨h1, h2⟩
    obtain ⟨s, hs, hsx⟩ := (LocalSpans.mem_locF 𝔭 A x).1 h1
    obtain ⟨t, ht, htx⟩ := (LocalSpans.mem_locF 𝔭 B x).1 h2
    refine (LocalSpans.mem_locF 𝔭 _ x).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, ?_, ?_⟩
    · rw [mul_comm, map_mul, mul_smul]
      exact A.smul_mem _ hsx
    · rw [map_mul, mul_smul]
      exact B.smul_mem _ htx

theorem isLattice_inf {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) : Submodule.IsLattice K (M₁ ⊓ M₂) := by
  have := hM₁
  exact Submodule.IsLattice.inf_left K M₁ M₂

theorem finite_quot_inf {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Finite (↥(locF 𝔭 M₁ ⊓ locF 𝔭 M₂) ⧸
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁ ⊓ locF 𝔭 M₂))) := by
  rw [← locF_inf_locF h𝔭]
  exact finite_quot (isLattice_inf hM₁ hM₂) h𝔭 k

theorem apply_mem_of_mem_autSub {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V}
    (hg : g ∈ autSub h A) {z : V} (hz : z ∈ A) : g z ∈ A := by
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg.2
  rw [← h2]
  exact Submodule.mem_map_of_mem hz

theorem apply_mem_smul_of_mem_autSub {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V}
    {g : V ≃ₗ[K] V} (hg : g ∈ autSub h A) (I : Ideal (𝓞 K)) {z : V} (hz : z ∈ I • A) :
    g z ∈ I • A := by
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg.2
  have h1 : g z ∈ (I • A).map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hz
  rwa [Submodule.map_smul'', h2] at h1

theorem congr_apply_mem {M₁ M₂ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {r₁ r₂ j : ℕ} (h1 : ((extP K 𝔭) ^ r₁ • locF 𝔭 M₁ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₂)
    (h2 : ((extP K 𝔭) ^ r₂ • locF 𝔭 M₂ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₁) (hj : r₂ + r₁ ≤ j)
    (g : V ≃ₗ[K] V)
    (hg : ∀ z ∈ locF 𝔭 M₁, g z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V))
    {z : V} (hz : z ∈ locF 𝔭 M₂) : g z ∈ locF 𝔭 M₂ := by
  obtain ⟨π, hπ, hπ'⟩ := D2.exists_unif h𝔭
  have hz1 : algebraMap F K (π : F) ^ r₂ • z ∈ locF 𝔭 M₁ :=
    h2 ((D2.mem_smul_iff_unif h𝔭 hπ hπ' M₂).2 ⟨z, hz, rfl⟩)
  have h3 := pow_smul_anti 𝔭 (locF 𝔭 M₁) hj (hg _ hz1)
  rw [pow_add, Submodule.mul_smul] at h3
  have h4 := Submodule.smul_mono (le_refl (extP K 𝔭 ^ r₂)) h1 h3
  obtain ⟨w, hw, e⟩ := (D2.mem_smul_iff_unif h𝔭 hπ hπ' M₂).1 h4
  rw [map_smul, ← smul_sub] at e
  have e' : g z - z = w :=
    smul_right_injective V (pow_ne_zero r₂ (D2.unif_ne_zero (K := K) hπ')) e
  have : g z = w + z := by rw [← e']; abel
  rw [this]
  exact add_mem hw hz

theorem exists_congr_mem_autSub (h : V →ₗ⋆[K] V →ₗ[K] K) {M₁ M₂ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsFullLattice K M₁) (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ g ∈ autSub h (locF 𝔭 M₁),
      (∀ z ∈ locF 𝔭 M₁, g z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V)) →
      g ∈ autSub h (locF 𝔭 M₂) := by
  obtain ⟨r₁, h1⟩ := exists_pow_smul_le hM₁.toIsLattice hM₂ h𝔭
  obtain ⟨r₂, h2⟩ := exists_pow_smul_le hM₂.toIsLattice hM₁ h𝔭
  refine ⟨r₂ + r₁, fun j hj g hg hc => ⟨hg.1, ?_⟩⟩
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact congr_apply_mem h𝔭 h1 h2 hj g hc hz
  · intro x hx
    have hc' : ∀ z ∈ locF 𝔭 M₁,
        g.symm z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V) := by
      intro z hz
      have hz' : g.symm z ∈ locF 𝔭 M₁ := apply_mem_of_mem_autSub (inv_mem hg) hz
      have := neg_mem (hc _ hz')
      rwa [LinearEquiv.apply_symm_apply, neg_sub] at this
    exact ⟨g.symm x, congr_apply_mem h𝔭 h1 h2 hj g.symm hc' hx, by simp⟩

theorem orbCount_eq_relIndex (h : V →ₗ⋆[K] V →ₗ[K] K) (A B : Submodule (𝓞 K) V) :
    orbCount h A B = (autSub h B).relIndex (autSub h A) := by
  let _ : MulAction (V ≃ₗ[K] V) (Submodule (𝓞 K) V) :=
    { smul := fun g L => Formalism.HermitianLatticesTheory.gmap g L
      one_smul := autSub_gmap_one
      mul_smul := autSub_gmap_mul }
  have hst : MulAction.stabilizer ↥(autSub h A) B = (autSub h B).subgroupOf (autSub h A) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      exact ⟨g.2.1, hg⟩
    · intro hg
      exact hg.2
  rw [Subgroup.relIndex, ← hst, Subgroup.index_eq_card,
    ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ B)]
  unfold orbCount
  refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro C
  constructor
  · rintro ⟨g, hg, hA, hB⟩
    exact ⟨⟨g, hg, hA⟩, hB⟩
  · rintro ⟨⟨g, hg, hA⟩, hB⟩
    exact ⟨g, hg, hA, hB⟩

theorem relIndex_ne_zero_of_map {G X : Type*} [Group G] [Finite X] (H Γ : Subgroup G) (f : H → X)
    (hf : ∀ a b : H, f a = f b → (a : G)⁻¹ * b ∈ Γ) : Γ.relIndex H ≠ 0 := by
  classical
  show (Γ.subgroupOf H).index ≠ 0
  have hfin : Finite (H ⧸ Γ.subgroupOf H) := by
    let g : Set.range f → H ⧸ Γ.subgroupOf H := fun x => QuotientGroup.mk x.2.choose
    apply Finite.of_surjective g
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      refine ⟨⟨f a, a, rfl⟩, ?_⟩
      show QuotientGroup.mk _ = QuotientGroup.mk a
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hf _ _ (⟨f a, a, rfl⟩ : Set.range f).2.choose_spec
  exact Subgroup.index_ne_zero_of_finite

def resA {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (g : autSub h A) : ↥A →ₗ[𝓞 K] ↥A :=
  (((g : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict
    (fun _ hz => apply_mem_of_mem_autSub g.2 hz)

def redA {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (I : Ideal (𝓞 K)) (g : autSub h A) :
    (↥A ⧸ (I • ⊤ : Submodule (𝓞 K) ↥A)) →ₗ[𝓞 K] (↥A ⧸ (I • ⊤ : Submodule (𝓞 K) ↥A)) :=
  Submodule.mapQ _ _ (resA g) (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

theorem sub_mem_of_redA_eq {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (I : Ideal (𝓞 K))
    {a b : autSub h A} (e : redA I a = redA I b) {z : V} (hz : z ∈ A) :
    (b : V ≃ₗ[K] V) z - (a : V ≃ₗ[K] V) z ∈ I • A := by
  have h1 := congrArg (fun φ => φ (Submodule.Quotient.mk (⟨z, hz⟩ : ↥A))) e
  simp only [redA, Submodule.mapQ_apply] at h1
  rw [eq_comm, Submodule.Quotient.eq] at h1
  have h2 := Submodule.mem_map_of_mem (f := A.subtype) h1
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at h2
  simp only [Submodule.subtype_apply] at h2
  exact h2

theorem relIndex_autSub_ne_zero (h : V →ₗ⋆[K] V →ₗ[K] K) {M₁ M₂ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsFullLattice K M₁) (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    (autSub h (locF 𝔭 M₂)).relIndex (autSub h (locF 𝔭 M₁)) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_congr_mem_autSub h hM₁ hM₂ h𝔭
  have := finite_quot hM₁.toIsLattice h𝔭 j
  have : Finite ((↥(locF 𝔭 M₁) ⧸ ((extP K 𝔭) ^ j • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁))) →ₗ[𝓞 K]
      (↥(locF 𝔭 M₁) ⧸ ((extP K 𝔭) ^ j • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁)))) :=
    Finite.of_injective _ DFunLike.coe_injective
  refine relIndex_ne_zero_of_map _ _ (redA (extP K 𝔭 ^ j)) fun a b e => ?_
  refine hj j le_rfl _ (mul_mem (inv_mem a.2) b.2) fun z hz => ?_
  have h1 := apply_mem_smul_of_mem_autSub (inv_mem a.2) _ (sub_mem_of_redA_eq _ e hz)
  have h2 : ((a : V ≃ₗ[K] V)⁻¹ * (b : V ≃ₗ[K] V)) z - z =
      (a : V ≃ₗ[K] V)⁻¹ ((b : V ≃ₗ[K] V) z - (a : V ≃ₗ[K] V) z) := by
    rw [map_sub]
    change _ = (a : V ≃ₗ[K] V).symm _ - (a : V ≃ₗ[K] V).symm _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [h2]
  exact h1

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardQuotInfNeZero
section
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem card_quot_inf_ne_zero {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) ≠ 0 := by
  obtain ⟨r, hr⟩ := IA.exists_pow_smul h𝔭 hM₁ hM₂
  rw [IA.card_eq_relIndex h𝔭 hr]
  exact IA.relIndex_ne_zero hM₁ hM₂ 𝔭

theorem card_quot_inf_mul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsFullLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁)
    (hM₂ : Submodule.IsFullLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₁) 𝔭 =
      Nat.card (↥(locF 𝔭 M₂) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₂)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₂) 𝔭 := by
  obtain ⟨r₁, hr₁⟩ := IA.exists_pow_smul h𝔭 hM₁.toIsLattice hM₂
  obtain ⟨r₂, hr₂⟩ := IA.exists_pow_smul h𝔭 hM₂.toIsLattice hM₁
  have e₁ := IA.card_eq_relIndex h𝔭 hr₁
  have e₂ := IA.card_eq_relIndex h𝔭 hr₂
  rw [inf_comm (locF 𝔭 M₂) (locF 𝔭 M₁)] at e₂
  have hAB : vd h (M₁ ⊓ locF 𝔭 M₂) 𝔭 = vd h (M₂ ⊓ locF 𝔭 M₁) 𝔭 := by
    rw [← localizedQuotients.vd_locF hF h (M₁ ⊓ locF 𝔭 M₂) h𝔭,
      ← localizedQuotients.vd_locF hF h (M₂ ⊓ locF 𝔭 M₁) h𝔭,
      IA.locF_inf 𝔭 h𝔭.isPrime M₁ M₂, IA.locF_inf 𝔭 h𝔭.isPrime M₂ M₁, inf_comm]
  rw [e₁, e₂, localizedQuotients.vd_locF hF h M₁ h𝔭, localizedQuotients.vd_locF hF h M₂ h𝔭,
    IA.vd_mul hF hK hs hd hM₁ hM₁i hM₂ h𝔭, IA.vd_mul hF hK hs hd hM₂ hM₂i hM₁ h𝔭, hAB]

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsDualBound
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem nondegenerate {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) : h.Nondegenerate := by
  have key : ∀ x : V, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have h1 := hd x hne φ
    rw [hx, map_zero, Complex.zero_re] at h1
    exact lt_irrefl _ h1
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩

theorem exists_dual_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ e : ℕ, ∀ (k : ℕ) (x : V), (∀ y ∈ locF 𝔭 A₀, h y x ∈ pK K 𝔭 (k + e)) →
      x ∈ extP K 𝔭 ^ k • locF 𝔭 A₀ := by
  classical
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨b, hb, -⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  have hnd := nondegenerate hd
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis h hnd b
  choose n hn using fun j => (by
    first | exact exists_pow_smul_mem hA₀ h𝔭 hπ (bs j)
          | exact exists_pow_smul_mem hA₀.toIsLattice h𝔭 hπ (bs j))
  refine ⟨∑ j, n j, fun k x hx => ?_⟩
  rw [Formalism.HermitianLatticesTheory.dualLattice_expand h hnd b bs hbs x]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨c, hc, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 (hx (b j) (LocF.le_locF 𝔭 A₀ (hb j)))
  rw [e]
  have hle : n j ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2
    ⟨(c * algebraMap F K (π : F) ^ (∑ j, n j - n j)) • (algebraMap F K (π : F) ^ n j • bs j),
      smul_mem_locF h𝔭 A₀ (by simpa using mul_mem_pK h𝔭 hc (unif_pow_mem_pK_zero hπ _)) (hn j), ?_⟩
  rw [smul_smul, smul_smul]
  congr 1
  have : k + ∑ j, n j = k + (∑ j, n j - n j) + n j := by omega
  rw [this, pow_add, pow_add]; ring

theorem exists_endL_le {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsFullLattice K A₀)
    (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, ∀ d : ℕ, endL (locF 𝔭 A₀) (extP K 𝔭 ^ (d + r) • locF 𝔭 A₀) ≤
      endL (locF 𝔭 B₀) (extP K 𝔭 ^ d • locF 𝔭 B₀) := by
  obtain ⟨r1, h1⟩ := (by
    first | exact exists_smul_le hA₀.toIsLattice hB₀ h𝔭
          | exact exists_smul_le hA₀.toIsLattice hB₀.toIsLattice h𝔭)
  obtain ⟨r2, h2⟩ := (by
    first | exact exists_smul_le hB₀.toIsLattice hA₀ h𝔭
          | exact exists_smul_le hB₀.toIsLattice hA₀.toIsLattice h𝔭)
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 := unif_ne_zero (K := K) hπ'
  refine ⟨r1 + r2, fun d D hD y hy => ?_⟩
  have hy' := h2 ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨y, hy, rfl⟩)
  obtain ⟨z, hz, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 (hD _ hy')
  have hz' := h1 ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨z, hz, rfl⟩)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, hz', ?_⟩
  apply smul_right_injective V (pow_ne_zero r2 hπ0)
  show algebraMap F K (π : F) ^ r2 • D y = algebraMap F K (π : F) ^ r2 • _
  rw [← map_smul, e, smul_smul, smul_smul]
  congr 1
  rw [pow_add, pow_add]; ring

theorem nSub_le_sSub (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    nSub (locF 𝔭 A₀) 𝔭 k ≤ sSub h (locF 𝔭 A₀) 𝔭 k := by
  rintro X ⟨hX, hX'⟩
  refine ⟨hX, fun x hx y hy => ?_⟩
  have hx0 : x ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := by rwa [pow_zero_smul]
  have hy0 : y ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := by rwa [pow_zero_smul]
  have e : h (X x) (X y) - h x y = h (X x - x) y + h x (X y - y) + h (X x - x) (X y - y) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  rw [e]
  refine add_mem (add_mem ?_ ?_) ?_
  · simpa using form_mem_pK hF hA₀i h𝔭 (hX' x hx) hy0
  · simpa using form_mem_pK hF hA₀i h𝔭 hx0 (hX' y hy)
  · exact pK_anti 𝔭 (Nat.le_add_right k k) (form_mem_pK hF hA₀i h𝔭 (hX' x hx) (hX' y hy))

theorem nSub_le_glSub {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsFullLattice K A₀)
    (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, nSub (locF 𝔭 A₀) 𝔭 k ≤ glSub (locF 𝔭 B₀) := by
  obtain ⟨r, hr⟩ := exists_endL_le hA₀ hB₀ h𝔭
  refine ⟨1 + r, fun k hk X hX => ?_⟩
  apply (by
    first | exact mem_glSub_of_sub_mem (X := X) hB₀ h𝔭
          | exact mem_glSub_of_sub_mem (X := X) hB₀.toIsLattice h𝔭)
  intro y hy
  have h1 : ((X : V →ₗ[K] V) - LinearMap.id) ∈ endL (locF 𝔭 A₀) (extP K 𝔭 ^ (1 + r) • locF 𝔭 A₀) :=
    fun x hx => smul_anti 𝔭 _ hk (hX.2 x hx)
  have := hr 1 h1 y hy
  rwa [pow_one] at this

end Formalism.HermitianLattices.Ext.L3.D2
end
end

