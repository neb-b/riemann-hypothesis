module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0022
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0031
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0033
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MulEqZeroIff

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AkCountEqRedCountMul
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_isom_lift (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k)
    (X : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀))))
    (hX : ∀ x y x' y' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) :
    ∃ g ∈ autSub h (locF 𝔭 A₀), ∀ x x' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      g x - x' ∈ ((extP K 𝔭) ^ (k - eA h (locF 𝔭 A₀) 𝔭) • (locF 𝔭 A₀) : Submodule (𝓞 K) V) := by
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  obtain ⟨H, hH, -⟩ := LocF.exists_gram hA₀i b hbL
  have hd' := LocF.aniso_of_totPosDef hd
  have key : ∀ A : Submodule (𝓞 K) V, A = locF 𝔭 (integralBasisSpans.spanO b) → ∀ k : ℕ, eA h A 𝔭 + 1 ≤ k →
      ∀ X : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)),
      (∀ x y x' y' : ↥A, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
        Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
        CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) →
      ∃ g ∈ autSub h A, ∀ x x' : ↥A, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
        g x - x' ∈ ((extP K 𝔭) ^ (k - eA h A 𝔭) • A : Submodule (𝓞 K) V) := by
    rintro _ rfl k hk X hX
    exact HU.exists_isom_lift_basis hK hF hs hd' b hH h𝔭 (HU.isE_eA hK hF hd' b h𝔭) hk X hX
  exact key _ hb.symm k hk X hX

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscrIdealSmulLeIff
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] in
theorem isIntegralLat_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (c : 𝓞 F) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (algebraMap F K (c : F) • h) L := by
  intro x hx y hy
  have h1 : algebraMap F K (c : F) ∈ (1 : Submodule (𝓞 K) K) :=
    Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 K) c, rfl⟩
  have h2 := Submodule.mul_mem_mul h1 (hLi x hx y hy)
  rw [one_mul] at h2
  exact h2

theorem akCount_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    akCount (algebraMap F K (c : F) • h) L 𝔭 k =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V ^ 2) * akCount h L 𝔭 (k - vF 𝔭 c) := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hL h𝔭
  obtain ⟨H, hH, _⟩ := LocF.exists_gram hLi b hbL
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.akCount_eq _ h𝔭 b hb hH', integralBasisSpans.akCount_eq h h𝔭 b hb hH, PinAA.akM_smul hK h𝔭 hc hk,
    Fintype.card_fin]

theorem nkCount_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (n : 𝓞 F) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V) * nkCount h L 𝔭 (k - vF 𝔭 c) n := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hL h𝔭
  obtain ⟨H, hH, _⟩ := LocF.exists_gram hLi b hbL
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.nkCount_eq _ h𝔭 b hb hH', integralBasisSpans.nkCount_eq h h𝔭 b hb hH, PinAA.nkM_smul hK h𝔭 hc n hk,
    Fintype.card_fin]

omit [NumberField K] [StarRing K] [Algebra F K] in
theorem pow_notMem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} {j : ℕ} (hc : c ∉ 𝔭 ^ (j + 1))
    (m : ℕ) : c ^ m ∉ 𝔭 ^ (m * j + 1) := by
  induction m with
  | zero =>
    rw [pow_zero, zero_mul, zero_add, pow_one]
    exact fun e => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 e)
  | succ m ih =>
    rw [show (m + 1) * j + 1 = m * j + j + 1 by ring, pow_succ c]
    exact idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) ih hc

theorem gram_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 F) (x : Fin (finrank K V) → V) :
    (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)).det =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V)) *
        (Matrix.of fun i j => h (x i) (x j)).det := by
  have e : (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)) =
      algebraMap F K (c : F) • Matrix.of fun i j => h (x i) (x j) := by
    ext i j
    rfl
  rw [e, Matrix.det_smul, Fintype.card_fin]
  congr 1
  simp only [map_pow]
  rfl

theorem discrIdeal_smul_le_iff {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0)
    (e : ℕ) :
    discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ (finrank K V * vF 𝔭 c + e) ↔
      discrIdeal h L ≤ extP K 𝔭 ^ e := by
  constructor
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    let d := c ^ finrank K V
    let v := finrank K V * vF 𝔭 c
    have hd : d ∉ 𝔭 ^ (v + 1) :=
      pow_notMem h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hc) (finrank K V)
    have hz : algebraMap (𝓞 F) (𝓞 K) d * z ∈ extP K 𝔭 ^ (v + e) := by
      apply hle
      exact Ideal.subset_span ⟨x, hx, by rw [gram_smul, map_mul, ez]⟩
    have hspan : extP K 𝔭 ^ v ≤
        Ideal.span {algebraMap (𝓞 F) (𝓞 K) d} ⊔ extP K 𝔭 ^ (v + e) := by
      have h := idealPowerSpanBounds.pow_le_span_sup h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) hd (v + e)
      simpa only [extP, Ideal.map_pow, Ideal.map_sup, Ideal.map_span, Set.image_singleton] using
        (Ideal.map_mono (f := algebraMap (𝓞 F) (𝓞 K)) h)
    have hmul : extP K 𝔭 ^ v * Ideal.span {z} ≤ extP K 𝔭 ^ (v + e) := by
      refine (Ideal.mul_mono_left hspan).trans ?_
      rw [Ideal.sup_mul, Ideal.span_singleton_mul_span_singleton]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hz) Ideal.mul_le_left
    have hne : extP K 𝔭 ^ v ≠ 0 :=
      pow_ne_zero _ (idealPowerSpanBounds.map_ne_bot_of_isMaximal (K := K) h𝔭)
    have hdiv : extP K 𝔭 ^ v * extP K 𝔭 ^ e ∣ extP K 𝔭 ^ v * Ideal.span {z} := by
      rw [← pow_add]
      exact Ideal.dvd_iff_le.mpr hmul
    exact Ideal.dvd_span_singleton.mp ((mul_dvd_mul_iff_left hne).mp hdiv)
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    obtain ⟨g, -, hdet⟩ := LocF.exists_gram hLi x hx
    have hz : z = algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) * g.det := by
      apply RingOfIntegers.coe_injective
      show algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K _
      rw [ez, gram_smul, map_mul, hdet]
    have h1 : g.det ∈ extP K 𝔭 ^ e := hle (Ideal.subset_span ⟨x, hx, hdet⟩)
    have h2 : algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) ∈ extP K 𝔭 ^ (finrank K V * vF 𝔭 c) := by
      rw [extP, ← Ideal.map_pow]
      apply Ideal.mem_map_of_mem
      rw [mul_comm, pow_mul]
      exact Ideal.pow_mem_pow (localValuationFiltration.mem_pow_vF h𝔭 hc) _
    show z ∈ _
    rw [hz, pow_add]
    exact Ideal.mul_mem_mul h2 h1

theorem vd_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) :
    vd (algebraMap F K (c : F) • h) L 𝔭 = vd h L 𝔭 + finrank K V * vF 𝔭 c := by
  have hD : discrIdeal h L ≠ ⊥ := by
    obtain ⟨b, hbL, _⟩ := LocalSpans.exists_basis_locF hL h𝔭
    obtain ⟨g, _, hdet⟩ := LocF.exists_gram hLi b hbL
    intro hbot
    have hmem : g.det ∈ discrIdeal h L := Ideal.subset_span ⟨b, hbL, hdet⟩
    rw [hbot, Ideal.mem_bot] at hmem
    apply LocF.gram_det_ne_zero h (LocF.aniso_of_totPosDef hd) b b.linearIndependent
    rw [← hdet, hmem, map_zero]
  have hE : extP K 𝔭 ≠ ⊤ := by
    intro e
    apply h𝔭.ne_top
    have h : Ideal.comap (algebraMap (𝓞 F) (𝓞 K)) (extP K 𝔭) = 𝔭 :=
      Ideal.comap_map_eq_self_of_faithfullyFlat 𝔭
    rw [e, Ideal.comap_top] at h
    exact h.symm
  have hb : BddAbove {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    apply hD
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isDomain (extP K 𝔭) hE]
    refine le_iInf fun k => ?_
    obtain ⟨e, he, hke⟩ := hnb k
    exact he.trans (Ideal.pow_le_pow_right hke.le)
  have hmem : vd h L 𝔭 ∈ {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} :=
    Nat.sSup_mem ⟨0, by simp⟩ hb
  have hg : IsGreatest {e : ℕ | discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ e}
      (vd h L 𝔭 + finrank K V * vF 𝔭 c) := by
    constructor
    · rw [add_comm]
      exact (discrIdeal_smul_le_iff hLi h𝔭 hc _).2 hmem
    · intro e' he'
      by_cases hlt : e' ≤ finrank K V * vF 𝔭 c
      · omega
      · obtain ⟨e, rfl⟩ : ∃ e, e' = finrank K V * vF 𝔭 c + e := ⟨e' - finrank K V * vF 𝔭 c, by omega⟩
        have h1 : e ≤ vd h L 𝔭 := le_csSup hb ((discrIdeal_smul_le_iff hLi h𝔭 hc e).1 he')
        omega
  exact hg.csSup_eq

end Formalism.HermitianLattices.Ext.L3.PinA
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralLatOfForall
section
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization GoodPrimeTerms SplitBAux

theorem gmap_inj (g : V ≃ₗ[K] V) {A B : Submodule (𝓞 K) V} :
    Formalism.HermitianLatticesTheory.gmap g A = Formalism.HermitianLatticesTheory.gmap g B ↔ A = B :=
  (gmap_injective g).eq_iff

theorem fibLoc_gmap (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h') (T : Submodule (𝓞 K) V') :
    fibLoc S L 𝔭 (Formalism.HermitianLatticesTheory.gmap g' T) = fibLoc S L 𝔭 T := by
  have hG : extOf S g' ∈ Formalism.HermitianLatticesTheory.isom h := extOf_mem_isom hs S hg'
  let e : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V :=
    { toFun := Formalism.HermitianLatticesTheory.gmap (extOf S g')
      invFun := Formalism.HermitianLatticesTheory.gmap (extOf S g').symm
      left_inv := fun Λ => Formalism.HermitianLatticesTheory.isomAct_gmap_symm _ Λ
      right_inv := fun Λ => Formalism.HermitianLatticesTheory.isomAct_gmap_symm (extOf S g').symm Λ }
  unfold fibLoc
  refine (Nat.card_congr (Equiv.subtypeEquiv e ?_)).symm
  intro Λ
  change _ ↔ (locF 𝔭 (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∧
    (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) ∧
    S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∧
    S.cut (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g' T))
  rw [← LocalizedFibreSets.gmap_locF, gmap_inj, StabilizerLattices.cut_gmap_extOf, ← LocalizedFibreSets.gmap_locF, gmap_inj,
    Formalism.HermitianLatticesTheory.isomAct_mem_gmap, symm_fix (extOf_x₀ S g')]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨extOf S g' * g, Subgroup.mul_mem _ hG hg, autSub_gmap_mul _ _ _⟩
  · rintro ⟨g, hg, e1⟩
    refine ⟨(extOf S g')⁻¹ * g, Subgroup.mul_mem _ (Subgroup.inv_mem _ hG) hg, ?_⟩
    rw [autSub_gmap_mul, e1, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]

theorem fibLoc_eq_of_rel (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} {M M₁ : Submodule (𝓞 K) V'}
    (H : ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 M) = locF 𝔭 M₁) :
    fibLoc S L 𝔭 M₁ = fibLoc S L 𝔭 M := by
  obtain ⟨g, hg, e⟩ := H
  rw [← fibLoc_locF S L 𝔭 M₁, ← e, fibLoc_gmap hs S L 𝔭 hg, fibLoc_locF]

theorem sameGenus_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (A B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.SameGenus h A B ↔ ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭.1 A) = locF 𝔭.1 B := by
  constructor
  · rintro H ⟨𝔭, h𝔭⟩
    obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
    rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact H P hP
  · intro H P hP
    have hm : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) P
    have := H ⟨_, hm⟩
    rwa [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP] at this

theorem isIntegralLat_of_forall {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {h₀ : W →ₗ⋆[K] W →ₗ[K] K} {M : Submodule (𝓞 K) W}
    (H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, IsIntegralAt 𝔭.1 h₀ (locF 𝔭.1 M)) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h₀ M := by
  intro x hx y hy
  rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
  exact fun 𝔭 => H 𝔭 x (LocF.le_locF _ _ hx) y (LocF.le_locF _ _ hy)

theorem isIntegralAt_gmap {𝔭 : Ideal (𝓞 F)} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    {T : Submodule (𝓞 K) V} (hT : IsIntegralAt 𝔭 h T) : IsIntegralAt 𝔭 h (Formalism.HermitianLatticesTheory.gmap g T) := by
  intro x hx y hy
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hx hy
  rw [← isom_apply (symm_mem_isom hg)]
  exact hT _ hx _ hy

theorem tprod_natCast_ne_zero {ι : Type*} (f : ι → ℕ) (hf : ∀ i, f i ≠ 0) :
    (∏' i, (f i : ℝ)) ≠ 0 := by
  by_cases hm : Multipliable fun i => (f i : ℝ)
  · have h1 : (1 : ℝ) ≤ ∏' i, (f i : ℝ) := by
      refine ge_of_tendsto hm.hasProd (Filter.Eventually.of_forall fun s => ?_)
      have : (1 : ℝ) ≤ ((∏ i ∈ s, f i : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hf i)
      simpa using this
    linarith
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact one_ne_zero

def Good (F : Type) [Field F] [NumberField F] [Algebra F K] (S : VecSplit h h')
    (L : Submodule (𝓞 K) V) (M : Submodule (𝓞 K) V') : Prop :=
  Submodule.IsLattice K M ∧ ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibLoc S L 𝔭.1 M ≠ 0

theorem Good.integral (hF : IsFixF K F) {S : VecSplit h h'} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) : Formalism.HermitianLatticesTheory.IsIntegralLat h' M := by
  apply isIntegralLat_of_forall (F := F)
  intro 𝔭
  obtain ⟨C, -, hCi, e⟩ := exists_lattice_of_fibLoc_ne_zero S hL hLi (hM.2 𝔭)
  rw [← e]
  exact isIntegralAt_locF 𝔭.2.isPrime hF hCi

private theorem exists_full_lattice_of_fibLoc_ne_zero (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) {𝔭 : Ideal (𝓞 F)}
    {T : Submodule (𝓞 K) V'} (hT : fibLoc S L 𝔭 T ≠ 0) :
    ∃ C : Submodule (𝓞 K) V', Submodule.IsFullLattice K C ∧ locF 𝔭 C = locF 𝔭 T := by
  obtain ⟨g, -, -, e⟩ := exists_of_fibLoc_ne_zero S hT
  have hLg : Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
    refine { toIsLattice := Submodule.IsLattice.of_fg K (hL.fg.map _), span_eq_top := ?_ }
    change Submodule.span K ((g : V →ₗ[K] V) '' (L : Set V)) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact g.surjective
  exact ⟨_, StabilizerLattices.isFullLattice_cut S hLg, e⟩

theorem Good.isFullLattice {S : VecSplit h h'} {L : Submodule (𝓞 K) V}
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) (hL : Submodule.IsFullLattice K L) :
    Submodule.IsFullLattice K M := by
  obtain ⟨𝔭, h𝔭⟩ := Ideal.exists_maximal (α := 𝓞 F)
  obtain ⟨C, hC, e⟩ := exists_full_lattice_of_fibLoc_ne_zero S hL (hM.2 ⟨𝔭, h𝔭⟩)
  refine { toIsLattice := hM.1, span_eq_top := ?_ }
  rw [eq_top_iff, ← hC.span_eq_top, Submodule.span_le]
  intro x hx
  have hx' : x ∈ locF 𝔭 M := e ▸ LocF.le_locF 𝔭 C hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime M x).mp hx'
  have htK : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    rw [map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K),
      map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
    exact fun e₀ => ht (e₀ ▸ 𝔭.zero_mem)
  apply ((Submodule.span K (M : Set V')).smul_mem_iff htK).mp
  rw [algebraMap_smul]
  exact Submodule.subset_span htx

theorem Good.nonempty (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) {S : VecSplit h h'} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) : (fibG S L M).Nonempty := by
  letI := hL
  letI := hM.isFullLattice hL
  have h1 := card_fibG_eq_prod (F := F) (L := L) (Λ' := M) hK hF hs hd S inferInstance hLi inferInstance
  have h2 := tprod_natCast_ne_zero _ hM.2
  rw [← h1] at h2
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  apply h2
  rw [hne]
  simp

theorem Good.of_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    {S : VecSplit h h'} {L : Submodule (𝓞 K) V} {M M₁ : Submodule (𝓞 K) V'}
    (hM : Good F S L M) (h1 : M₁ ∈ Formalism.HermitianLatticesTheory.genus h' M) : Good F S L M₁ :=
  ⟨h1.1.toIsLattice, fun 𝔭 => by
    rw [fibLoc_eq_of_rel hs S L ((sameGenus_iff hK hF M M₁).mp h1.2 𝔭)]
    exact hM.2 𝔭⟩

theorem exists_patch (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L)
    {A : Submodule (𝓞 K) V'} (hA : Submodule.IsFullLattice K A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (τ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V')
    (hτ : ∀ 𝔭 ∈ Z, locF 𝔭.1 (τ 𝔭) = τ 𝔭 ∧ fibLoc S L 𝔭.1 (τ 𝔭) ≠ 0)
    (hZ : ∀ 𝔭 ∉ Z, fibLoc S L 𝔭.1 A ≠ 0) :
    ∃ M, Good F S L M ∧ (∀ 𝔭 ∈ Z, locF 𝔭.1 M = τ 𝔭) ∧ ∀ 𝔭 ∉ Z, locF 𝔭.1 M = locF 𝔭.1 A := by
  obtain ⟨M, ⟨hMl, h1, h2⟩, -⟩ := exists_unique_patch hK hF hA Z τ (fun 𝔭 h𝔭 => by
    obtain ⟨C, hC, e⟩ := exists_full_lattice_of_fibLoc_ne_zero S hL (hτ 𝔭 h𝔭).2
    exact ⟨(hτ 𝔭 h𝔭).1, C, hC, e.trans (hτ 𝔭 h𝔭).1⟩)
  refine ⟨M, ⟨hMl, fun 𝔭 => ?_⟩, h1, h2⟩
  by_cases h𝔭 : 𝔭 ∈ Z
  · rw [fibLoc_congr S L (T' := τ 𝔭) (by rw [h1 𝔭 h𝔭, (hτ 𝔭 h𝔭).1])]
    exact (hτ 𝔭 h𝔭).2
  · rw [fibLoc_congr S L (h2 𝔭 h𝔭)]
    exact hZ 𝔭 h𝔭

open scoped Formalism.HermitianLattices.Ext.L3.StabilizerLattices in
theorem exists_locReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M₀ : Submodule (𝓞 K) V'} (hM₀ : Good F S L M₀) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∃ s, IsLocReps S L 𝔭.1 s := by
  classical
  letI := hL
  obtain ⟨s', hs'⟩ := exists_fibReps (L := L) hK hs hd S inferInstance hLi
  let A : Set (Submodule (𝓞 K) V') :=
    {T | locF 𝔭.1 T = T ∧ IsIntegralAt 𝔭.1 h' T ∧ fibLoc S L 𝔭.1 T ≠ 0}
  have hA : ∀ g : Formalism.HermitianLatticesTheory.isom h', ∀ T ∈ A, g • T ∈ A := by
    rintro g T ⟨h1, h2, h3⟩
    refine ⟨?_, isIntegralAt_gmap g.2 h2, ?_⟩
    · change locF 𝔭.1 (Formalism.HermitianLatticesTheory.gmap g.1 T) = Formalism.HermitianLatticesTheory.gmap g.1 T
      rw [← LocalizedFibreSets.gmap_locF, h1]
    · change fibLoc S L 𝔭.1 (Formalism.HermitianLatticesTheory.gmap g.1 T) ≠ 0
      rwa [fibLoc_gmap hs S L 𝔭.1 g.2]
  obtain ⟨s, hs1, hs2⟩ := OrbSum.exists_reps_of_cover (G := Formalism.HermitianLatticesTheory.isom h') A hA
    {T | T ∈ A ∧ T ∈ s'.image (locF 𝔭.1)}
    ((s'.image (locF 𝔭.1)).finite_toSet.subset fun T hT => hT.2) (fun c hc => hc.1) (by
      intro T hT
      obtain ⟨M, hM, h1, -⟩ := exists_patch hK hF S hL (hM₀.isFullLattice hL) {𝔭} (fun _ => T)
        (fun 𝔮 h𝔮 => by
          rw [Finset.mem_singleton] at h𝔮
          subst h𝔮
          exact ⟨hT.1, hT.2.2⟩) (fun 𝔮 _ => hM₀.2 𝔮)
      obtain ⟨Λ₀, ⟨hΛ₀, g, hg, e⟩, -⟩ := hs'.2 M (hM.nonempty hK hF hs hd hL hLi)
      have e2 : (⟨g, hg⟩ : Formalism.HermitianLatticesTheory.isom h') • locF 𝔭.1 Λ₀ = T := by
        change Formalism.HermitianLatticesTheory.gmap g (locF 𝔭.1 Λ₀) = T
        rw [LocalizedFibreSets.gmap_locF, e, h1 𝔭 (Finset.mem_singleton_self _)]
      refine ⟨locF 𝔭.1 Λ₀, ⟨?_, Finset.mem_image_of_mem _ hΛ₀⟩, ⟨g, hg⟩, e2⟩
      have := hA (⟨g, hg⟩ : Formalism.HermitianLatticesTheory.isom h')⁻¹ T hT
      rwa [← e2, inv_smul_smul] at this)
  refine ⟨s, hs1, fun T h1 h2 h3 => ?_⟩
  obtain ⟨T₀, ⟨hT₀, g, hg⟩, hu⟩ := hs2 T ⟨h1, h2, h3⟩
  exact ⟨T₀, ⟨hT₀, g.1, g.2, hg⟩, fun T₁ ⟨h4, g₁, hg₁, e₁⟩ => hu T₁ ⟨h4, ⟨g₁, hg₁⟩, e₁⟩⟩

theorem isClassReps_filter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M)
    [DecidablePred fun Λ' : Submodule (𝓞 K) V' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'] :
    Formalism.ThetaLiftIndependence.IsClassReps h' M (s'.filter fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ') := by
  obtain ⟨he, hi, -⟩ :=
    Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V' h' (S.isSymm hs) Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  constructor
  · intro Λ' hΛ'
    rw [Finset.mem_filter] at hΛ'
    obtain ⟨Λ, hΛ, -, rfl⟩ := hs'.1 Λ' hΛ'.1
    exact ⟨StabilizerLattices.isFullLattice_cut S hΛ.1, hΛ'.2⟩
  · intro M₁ hM₁
    obtain ⟨Λ₀, ⟨hΛ₀, g, hg, e⟩, hu⟩ :=
      hs'.2 M₁ ((hM.of_genus hK hF hs hM₁).nonempty hK hF hs hd hL hLi)
    refine ⟨Λ₀, ⟨Finset.mem_filter.mpr ⟨hΛ₀, ?_⟩, g, hg, e⟩, ?_⟩
    · have h1 := hi Λ₀ g hg
      rw [e] at h1
      exact he.trans hM₁.2 (he.symm h1)
    · rintro Λ₁ ⟨h1, h2⟩
      exact hu Λ₁ ⟨(Finset.mem_filter.mp h1).1, h2⟩

end Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits
end
end

