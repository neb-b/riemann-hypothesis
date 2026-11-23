module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0015
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0001
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0003
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FinitePrimesOfMem
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {F : Type} [Field F] [NumberField F]

theorem ne_bot_of_max {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)

theorem two_le_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 2 ≤ Ideal.absNorm 𝔭 :=
  (IdealNormInequalities.resChar_prime h𝔭).two_le.trans (IdealNormInequalities.resChar_le_absNorm h𝔭)

theorem summable_inv_absNorm_sq :
    Summable fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => ((Ideal.absNorm 𝔭.1 : ℝ) ^ 2)⁻¹ := by
  refine Summable.of_nonneg_of_le (fun 𝔭 => by positivity) (fun 𝔭 => ?_)
    (IdealNormInequalities.summable_resChar_sq (K := F))
  have h1 : (0 : ℝ) < (IdealNormInequalities.resChar 𝔭.1 : ℝ) := by
    exact_mod_cast (IdealNormInequalities.resChar_prime 𝔭.2).pos
  have h2 : (IdealNormInequalities.resChar 𝔭.1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
    exact_mod_cast IdealNormInequalities.resChar_le_absNorm 𝔭.2
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le h2 2)

theorem absNorm_span_ne_zero {n : 𝓞 F} (hn : n ≠ 0) : Ideal.absNorm (Ideal.span {n}) ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hn

theorem lt_of_mem_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {e : ℕ}
    (he : n ∈ 𝔭 ^ e) : e < Ideal.absNorm (Ideal.span {n}) := by
  have h1 : Ideal.span {n} ≤ 𝔭 ^ e := (Ideal.span_singleton_le_iff_mem _).mpr he
  have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_span_ne_zero hn))
    (Ideal.absNorm_dvd_absNorm_of_le h1)
  rw [map_pow] at h2
  calc e < 2 ^ e := Nat.lt_two_pow_self
    _ ≤ Ideal.absNorm 𝔭 ^ e := Nat.pow_le_pow_left (two_le_absNorm h𝔭) e
    _ ≤ _ := h2

theorem mem_pow_iff_le_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (e : ℕ) :
    n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := by
  have hb : BddAbove {e : ℕ | n ∈ 𝔭 ^ e} :=
    ⟨Ideal.absNorm (Ideal.span {n}), fun e he => (lt_of_mem_pow h𝔭 hn he).le⟩
  constructor
  · intro he
    exact le_csSup hb he
  · intro he
    have hm : vF 𝔭 n ∈ {e : ℕ | n ∈ 𝔭 ^ e} := Nat.sSup_mem ⟨0, by simp⟩ hb
    exact Ideal.pow_le_pow_right he hm

theorem finite_primes_of_mem {n : 𝓞 F} (hn : n ≠ 0) :
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | n ∈ 𝔭.1}.Finite := by
  refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  refine (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) (Ideal.absNorm (Ideal.span {n}))).subset ?_
  rintro _ ⟨𝔭, h𝔭, rfl⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_span_ne_zero hn))
    (Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr h𝔭))


open scoped Classical in
def valF (n : 𝓞 F) : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ :=
  if hn : n ≠ 0 then
    Finsupp.onFinset (finite_primes_of_mem hn).toFinset (fun 𝔭 => vF 𝔭.1 n) (fun 𝔭 h => by
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      have := (mem_pow_iff_le_vF 𝔭.2 hn 1).mpr (Nat.one_le_iff_ne_zero.mpr h)
      simpa using this)
  else 0

theorem valF_apply {n : 𝓞 F} (hn : n ≠ 0) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    valF n 𝔭 = vF 𝔭.1 n := by
  unfold valF
  rw [dite_eq_left hn]
  rfl

def bId (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) : Ideal (𝓞 F) := v.prod fun 𝔭 e => 𝔭.1 ^ e

theorem bId_ne_bot (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) : bId v ≠ ⊥ := by
  unfold bId Finsupp.prod
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  exact fun 𝔭 _ => pow_ne_zero _ (ne_bot_of_max 𝔭.2)

theorem absNorm_bId (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    (Ideal.absNorm (bId v) : ℝ) = nrm (fun 𝔭 => (Ideal.absNorm 𝔭.1 : ℝ)) v := by
  unfold bId nrm Finsupp.prod
  rw [map_prod]
  push_cast
  simp only [map_pow, Nat.cast_pow]

theorem mem_bId_iff {n : 𝓞 F} (hn : n ≠ 0) (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    n ∈ bId v ↔ v ≤ valF n := by
  unfold bId Finsupp.prod
  rw [← IsDedekindDomain.inf_pow_eq_prod_of_prime v.support (fun 𝔭 => 𝔭.1) v
    (fun 𝔭 _ => Ideal.prime_of_isPrime (ne_bot_of_max 𝔭.2) 𝔭.2.isPrime)
    (fun 𝔭 _ 𝔮 _ h => fun h' => h (Subtype.ext h')), Submodule.mem_finsetInf]
  constructor
  · intro h 𝔭
    by_cases h𝔭 : 𝔭 ∈ v.support
    · rw [valF_apply hn]
      exact (mem_pow_iff_le_vF 𝔭.2 hn _).mp (h 𝔭 h𝔭)
    · rw [Finsupp.notMem_support_iff.mp h𝔭]; exact Nat.zero_le _
  · intro h 𝔭 _
    have := h 𝔭
    rw [valF_apply hn] at this
    exact (mem_pow_iff_le_vF 𝔭.2 hn _).mpr this

theorem bId_sup_eq_top {v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ}
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}} (h𝔭 : 𝔭 ∉ v.support) : bId v ⊔ 𝔭.1 = ⊤ := by
  by_contra hne
  have hle : bId v ≤ 𝔭.1 := by
    have h1 : 𝔭.1 ≤ bId v ⊔ 𝔭.1 := le_sup_right
    have h2 := 𝔭.2.eq_of_le hne h1
    rw [h2]
    exact le_sup_left
  unfold bId Finsupp.prod at hle
  obtain ⟨𝔮, h𝔮, hle'⟩ := (Ideal.IsPrime.prod_le 𝔭.2.isPrime).mp hle
  have := 𝔭.2.isPrime
  have h3 : 𝔮.1 ≤ 𝔭.1 := Ideal.IsPrime.le_of_pow_le hle'
  have h4 : 𝔮.1 = 𝔭.1 := 𝔮.2.eq_of_le 𝔭.2.ne_top h3
  exact h𝔭 (Subtype.ext h4 ▸ h𝔮)

theorem exists_vF_eq {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (j : ℕ) :
    ∃ n : 𝓞 F, n ≠ 0 ∧ vF 𝔭 n = j := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hn'⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow (ne_bot_of_max h𝔭) j)
  have h0 : n ≠ 0 := fun h => hn' (h ▸ Ideal.zero_mem _)
  refine ⟨n, h0, le_antisymm ?_ ((mem_pow_iff_le_vF h𝔭 h0 j).mp hn)⟩
  by_contra hlt
  exact hn' ((mem_pow_iff_le_vF h𝔭 h0 (j + 1)).mpr (by omega))

end Formalism.HermitianLattices.Ext.L3.A5
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsClassRepsMap
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem mass_eq_sum (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (s : Finset (Submodule (𝓞 K) V)) (hs : IsClassReps h L s) :
    mass h L = ∑ M ∈ s, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ := by
  have hex : ∃ s, IsClassReps h L s := ⟨s, hs⟩
  rw [massBasic_mass_eq h L hex]
  apply Complex.ofReal_injective
  rw [massBasic_sum_cast, massBasic_sum_cast]
  exact latLiftIndep K V h L _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs

section Transfer

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
  (Φ : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V') (τ : (V ≃ₗ[K] V) ≃ (V' ≃ₗ[K] V'))
  (hτ : ∀ g, τ g ∈ isom h' ↔ g ∈ isom h)
  (hg : ∀ g M, Φ (gmap g M) = gmap (τ g) (Φ M))
  (hloc : ∀ p : Ideal (𝓞 K), p.IsMaximal → ∀ M, Φ (loc (K := K) p M) = loc (K := K) p (Φ M))
  (hlat : ∀ M, Submodule.IsFullLattice K (Φ M) ↔ Submodule.IsFullLattice K M)

include hτ hg hloc hlat

theorem mem_genus_iff (L M : Submodule (𝓞 K) V) : Φ M ∈ genus h' (Φ L) ↔ M ∈ genus h L := by
  unfold genus SameGenus
  simp only [Set.mem_ofPred_eq, hlat]
  refine and_congr_right fun _ => forall₂_congr fun p hp => ?_
  constructor
  · rintro ⟨g', hg', e⟩
    obtain ⟨g, rfl⟩ := τ.surjective g'
    refine ⟨g, (hτ g).1 hg', Φ.injective ?_⟩
    rw [hg, hloc p hp, hloc p hp, e]
  · rintro ⟨g, hg₁, e⟩
    refine ⟨τ g, (hτ g).2 hg₁, ?_⟩
    rw [← hloc p hp, ← hg, e, hloc p hp]

theorem isClassReps_map {L : Submodule (𝓞 K) V} {s : Finset (Submodule (𝓞 K) V)}
    (hs : IsClassReps h L s) : IsClassReps h' (Φ L) (s.map Φ.toEmbedding) := by
  constructor
  · intro N hN
    obtain ⟨M, hM, rfl⟩ := Finset.mem_map.1 hN
    exact (mem_genus_iff Φ τ hτ hg hloc hlat L M).2 (hs.1 M hM)
  · intro N hN
    obtain ⟨M, rfl⟩ := Φ.surjective N
    obtain ⟨M₀, ⟨hM₀, g, hg₀, e⟩, huniq⟩ := hs.2 M ((mem_genus_iff Φ τ hτ hg hloc hlat L M).1 hN)
    refine ⟨Φ M₀, ⟨Finset.mem_map.2 ⟨M₀, hM₀, rfl⟩, τ g, (hτ g).2 hg₀, by rw [← hg, e]⟩, ?_⟩
    rintro N₁ ⟨hN₁, g', hg', e'⟩
    obtain ⟨M₁, hM₁, rfl⟩ := Finset.mem_map.1 hN₁
    obtain ⟨g₁, rfl⟩ := τ.surjective g'
    have : M₁ = M₀ := huniq M₁ ⟨hM₁, g₁, (hτ g₁).1 hg', Φ.injective (by rw [hg]; exact e')⟩
    rw [this]; rfl

theorem card_autL_eq (M : Submodule (𝓞 K) V) :
    Nat.card (autL h' (Φ M)) = Nat.card (autL h M) := by
  refine (Nat.card_congr (τ.subtypeEquiv fun g => ?_)).symm
  change (g ∈ isom h ∧ gmap g M = M) ↔ (τ g ∈ isom h' ∧ gmap (τ g) (Φ M) = Φ M)
  rw [hτ, ← hg, Φ.injective.eq_iff]

theorem mass_transfer {L : Submodule (𝓞 K) V} (hex : ∃ s, IsClassReps h L s) :
    (∃ s', IsClassReps h' (Φ L) s') ∧ mass h' (Φ L) = mass h L := by
  obtain ⟨s, hs⟩ := hex
  have hs' := isClassReps_map Φ τ hτ hg hloc hlat hs
  refine ⟨⟨_, hs'⟩, ?_⟩
  rw [mass_eq_sum h L s hs, mass_eq_sum h' _ _ hs', Finset.sum_map]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Equiv.coe_toEmbedding, card_autL_eq Φ τ hτ hg hloc hlat M]

end Transfer

def mapE (φ : V ≃ₗ[K] V') : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V' :=
  (Submodule.orderIsoMapComap (φ.restrictScalars (𝓞 K))).toEquiv

theorem mem_mapE (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) (y : V') :
    y ∈ mapE φ M ↔ φ.symm y ∈ M := by
  change y ∈ M.map ((φ.restrictScalars (𝓞 K)) : V →ₗ[𝓞 K] V') ↔ _
  rw [Submodule.mem_map_equiv]; rfl

def conjE (φ : V ≃ₗ[K] V') : (V ≃ₗ[K] V) ≃ (V' ≃ₗ[K] V') where
  toFun g := (φ.symm.trans g).trans φ
  invFun g := (φ.trans g).trans φ.symm
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp

theorem conjE_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') :
    conjE φ g y = φ (g (φ.symm y)) := rfl

theorem mem_gmap (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) (y : V) :
    y ∈ gmap g M ↔ g.symm y ∈ M := by
  change y ∈ M.map ((g.restrictScalars (𝓞 K)) : V →ₗ[𝓞 K] V) ↔ _
  rw [Submodule.mem_map_equiv]; rfl

theorem isLattice_mapE (φ : V ≃ₗ[K] V') {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (mapE φ M) := by
  constructor
  · exact hM.fg.map _
  · exact fun _ _ hli => (LinearIndependent.iff_fractionRing _ _).mp hli

theorem isFullLattice_mapE (φ : V ≃ₗ[K] V') {M : Submodule (𝓞 K) V}
    (hM : Submodule.IsFullLattice K M) : Submodule.IsFullLattice K (mapE φ M) := by
  refine { toIsLattice := isLattice_mapE φ hM.toIsLattice, span_eq_top := ?_ }
  change Submodule.span K ((φ : V →ₗ[K] V') '' (M : Set V)) = ⊤
  rw [Submodule.span_image, hM.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact φ.surjective

theorem mapE_symm_mapE (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : mapE φ.symm (mapE φ M) = M := by
  ext x; simp [mem_mapE]

theorem mass_mapE (φ : V ≃ₗ[K] V') {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L : Submodule (𝓞 K) V}
    (hex : ∃ s, IsClassReps h L s) :
    (∃ s', IsClassReps h' (mapE φ L) s') ∧ mass h' (mapE φ L) = mass h L := by
  refine mass_transfer (mapE φ) (conjE φ) ?_ ?_ ?_ ?_ hex
  · intro g
    constructor
    · intro H x y
      have := H (φ x) (φ y)
      simpa [conjE_apply, hφ] using this
    · intro H x y
      obtain ⟨x, rfl⟩ := φ.surjective x
      obtain ⟨y, rfl⟩ := φ.surjective y
      simp only [conjE_apply, LinearEquiv.symm_apply_apply, hφ]
      exact H x y
  · intro g M
    ext y
    rw [mem_mapE, mem_gmap, mem_gmap, mem_mapE]
    have e : (conjE φ g).symm y = φ (g.symm (φ.symm y)) := rfl
    rw [e, LinearEquiv.symm_apply_apply]
  · intro p _ M
    ext y
    rw [mem_mapE]
    change (∃ s ∈ hcompl (K := K) p, s • φ.symm y ∈ M) ↔ (∃ s ∈ hcompl (K := K) p, s • y ∈ mapE φ M)
    refine exists_congr fun s => and_congr_right fun _ => ?_
    rw [mem_mapE]
    have : φ.symm (s • y) = s • φ.symm y := (φ.symm.restrictScalars (𝓞 K)).map_smul s y
    rw [this]
  · intro M
    refine ⟨fun H => ?_, isFullLattice_mapE φ⟩
    have := isFullLattice_mapE φ.symm H
    rwa [mapE_symm_mapE] at this

end Formalism.HermitianLattices.Ext.L3.RankOne
end
end

