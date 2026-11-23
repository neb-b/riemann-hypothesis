module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0032
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0016
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFibGEqProd
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLiftBasis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0022
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0031
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0027
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0030

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscrIdealLeIff
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem map_mem_extP {𝔭 : Ideal (𝓞 F)} {k : ℕ} {s : 𝓞 F} (hs : s ∈ 𝔭 ^ k) :
    algebraMap (𝓞 F) (𝓞 K) s ∈ extP K 𝔭 ^ k := by
  rw [← Ideal.mem_comap, MeanB.comap_extP_pow]
  exact hs

theorem mem_extP_of_mul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) {k : ℕ}
    {z : 𝓞 K} (hz : algebraMap (𝓞 F) (𝓞 K) t * z ∈ extP K 𝔭 ^ k) : z ∈ extP K 𝔭 ^ k := by
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  have e : z = algebraMap (𝓞 F) (𝓞 K) u * (algebraMap (𝓞 F) (𝓞 K) t * z) -
      algebraMap (𝓞 F) (𝓞 K) (u * t - 1) * z := by
    rw [map_sub, map_mul, map_one]
    ring
  rw [e]
  exact sub_mem (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_right _ _ (map_mem_extP hu))

theorem conjO_mem_extP (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {z : 𝓞 K}
    (hz : z ∈ extP K 𝔭 ^ k) : conjO K z ∈ extP K 𝔭 ^ k := by
  obtain ⟨z', hz', e⟩ := MeanB.star_mem_extP hF 𝔭 k hz
  have : conjO K z = z' := RingOfIntegers.ext e.symm
  rw [this]
  exact hz'

theorem ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def IsGen (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (e : V) : Prop :=
  e ∈ L ∧ e ≠ 0 ∧ ∀ x ∈ L, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ a : 𝓞 K, algebraMap (𝓞 F) (𝓞 K) t • x = a • e

theorem exists_isGen {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L)
    (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ e, IsGen L 𝔭 e := by
  obtain ⟨b, hb, hloc⟩ := LocalSpans.exists_basis_locF hL h𝔭
  have hsub : Subsingleton (Fin (finrank K V)) := by
    rw [h1]
    infer_instance
  let i0 : Fin (finrank K V) := ⟨0, by omega⟩
  refine ⟨b i0, hb i0, b.ne_zero i0, fun x hx => ?_⟩
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hloc]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, hm⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ _).1 hx'
  have hr : Set.range b = {b i0} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      rw [Subsingleton.elim i i0]
      rfl
    · rintro rfl
      exact ⟨i0, rfl⟩
  rw [hr, Submodule.mem_span_singleton] at hm
  obtain ⟨a, ha⟩ := hm
  exact ⟨t, ht, a, ha.symm⟩

theorem discrIdeal_le_iff (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : V} (he : IsGen L 𝔭 e)
    {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F)) (j : ℕ) :
    discrIdeal h L ≤ extP K 𝔭 ^ j ↔ n ∈ 𝔭 ^ j := by
  have hsub : Subsingleton (Fin (finrank K V)) := by
    rw [h1]
    infer_instance
  let i0 : Fin (finrank K V) := ⟨0, by omega⟩
  constructor
  · intro hle
    rw [← MeanB.comap_extP_pow (K := K), Ideal.mem_comap]
    apply hle
    refine Ideal.subset_span ⟨fun _ => e, fun _ => he.1, ?_⟩
    rw [Matrix.det_eq_elem_of_subsingleton _ i0, Matrix.of_apply, hn]
    rfl
  · intro hnj
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, hz⟩
    rw [Matrix.det_eq_elem_of_subsingleton _ i0, Matrix.of_apply] at hz
    obtain ⟨t, ht, a, ha⟩ := he.2.2 (x i0) (hx i0)
    apply mem_extP_of_mul h𝔭 ht
    apply mem_extP_of_mul h𝔭 ht
    have : algebraMap (𝓞 F) (𝓞 K) t * (algebraMap (𝓞 F) (𝓞 K) t * z) =
        conjO K a * a * algebraMap (𝓞 F) (𝓞 K) n := by
      apply RingOfIntegers.coe_injective
      have e1 : h (algebraMap (𝓞 F) (𝓞 K) t • x i0) (algebraMap (𝓞 F) (𝓞 K) t • x i0) =
          h (a • e) (a • e) := by rw [ha]
      rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right,
        Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hn, ← hz,
        MeanB.algebraMap_comp, MeanB.star_algebraMap hF] at e1
      simp only [map_mul]
      rw [MeanB.algebraMap_comp, MeanB.algebraMap_comp]
      change _ = star (algebraMap (𝓞 K) K a) * _ * _
      rw [e1]
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (map_mem_extP hnj)

theorem vd_spec (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : V}
    (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F)) :
    n ∈ 𝔭 ^ vd h L 𝔭 ∧ n ∉ 𝔭 ^ (vd h L 𝔭 + 1) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply he.2.1
    apply LocF.aniso_of_totPosDef hd
    rw [hn]
    simp
  have hset : {j : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ j} = {j : ℕ | n ∈ 𝔭 ^ j} := by
    ext j
    exact discrIdeal_le_iff hF h1 h𝔭 he hn j
  have hinf : (⨅ j : ℕ, 𝔭 ^ j) = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top
  obtain ⟨j0, hj0⟩ : ∃ j0, n ∉ 𝔭 ^ j0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hn0
    have : n ∈ (⨅ j : ℕ, 𝔭 ^ j) := (Submodule.mem_iInf _).2 hcon
    rwa [hinf] at this
  have hbdd : BddAbove {j : ℕ | n ∈ 𝔭 ^ j} := by
    refine ⟨j0, fun j hj => ?_⟩
    by_contra hlt
    exact hj0 (Ideal.pow_le_pow_right (not_le.1 hlt).le hj)
  have hne : {j : ℕ | n ∈ 𝔭 ^ j}.Nonempty := ⟨0, by simp⟩
  unfold vd
  rw [hset]
  refine ⟨Nat.sSup_mem hne hbdd, fun hcon => ?_⟩
  have := le_csSup hbdd (show sSup {j : ℕ | n ∈ 𝔭 ^ j} + 1 ∈ {j : ℕ | n ∈ 𝔭 ^ j} from hcon)
  omega

end Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralAtLocF
section
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization

theorem good_term (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) {T : Submodule (𝓞 K) V'} (hTl : locF 𝔭 T = T)
    (hT : fibLoc S L 𝔭 T ≠ 0) : fibLoc S L 𝔭 T = 1 ∧ lamP h' T 𝔭 = 1 := by
  obtain ⟨C, hC, hCi, hvC, e⟩ :=
    exists_lattice_of_fibLoc_ne_zero_good hK hF hs hd S hL hLi h𝔭 hn hvL hvn hT
  constructor
  · rw [← fibLoc_congr S L e]
    exact fibLoc_eq_one hK hF hs hd S hL hLi hC hCi h𝔭 hn hvL hvn hvC
  · rw [← hTl, ← e, localFactor_localField hK hF (S.isSymm hs) (S.isTotPosDef hd) hC.toIsLattice hCi h𝔭]
    exact localMassFactor_of_valuation_eq_zero hK hF (S.isSymm hs) (S.isTotPosDef hd) hC hCi h𝔭 hvC

theorem good_orbit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) {T T' : Submodule (𝓞 K) V'}
    (hT : fibLoc S L 𝔭 T ≠ 0) (hT' : fibLoc S L 𝔭 T' ≠ 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 T) = locF 𝔭 T' := by
  obtain ⟨C, hC, hCi, hvC, e⟩ :=
    exists_lattice_of_fibLoc_ne_zero_good hK hF hs hd S hL hLi h𝔭 hn hvL hvn hT
  obtain ⟨C', hC', hCi', hvC', e'⟩ :=
    exists_lattice_of_fibLoc_ne_zero_good hK hF hs hd S hL hLi h𝔭 hn hvL hvn hT'
  rw [← e, ← e']
  exact exists_isom_locF_of_vd_zero hK hF (S.isSymm hs) (S.isTotPosDef hd) hC hC' hCi hCi' h𝔭
    hvC hvC'

theorem isIntegralAt_locF {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {h₀ : W →ₗ⋆[K] W →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime)
    (hF : IsFixF K F) {C : Submodule (𝓞 K) W}
    (hCi : Formalism.HermitianLatticesTheory.IsIntegralLat h₀ C) : IsIntegralAt 𝔭 h₀ (locF 𝔭 C) := by
  intro x hx y hy
  obtain ⟨s, hs, hx⟩ := (LocF.mem_locF_iff h𝔭 _ _).mp hx
  obtain ⟨t, ht, hy⟩ := (LocF.mem_locF_iff h𝔭 _ _).mp hy
  refine (LocF.mem_locF_iff h𝔭 _ _).mpr ⟨s * t, fun e => (h𝔭.mem_or_mem e).elim hs ht, ?_⟩
  have h1 := hCi _ hx _ hy
  have e : conjO K (algebraMap (𝓞 F) (𝓞 K) s) = algebraMap (𝓞 F) (𝓞 K) s :=
    (conjO_eq_iff_mem_range hF _).mpr ⟨s, rfl⟩
  have h2 : h₀ (algebraMap (𝓞 F) (𝓞 K) s • x) (algebraMap (𝓞 F) (𝓞 K) t • y) =
      (conjO K (algebraMap (𝓞 F) (𝓞 K) s) * algebraMap (𝓞 F) (𝓞 K) t) • h₀ x y := by
    have e' : algebraMap (𝓞 K) K (conjO K (algebraMap (𝓞 F) (𝓞 K) s)) =
      starRingEnd K (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) s)) := rfl
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) s) x,
      ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y, map_smul, map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, Algebra.smul_def, map_mul, e']
    ring
  rw [h2, e, ← map_mul] at h1
  exact h1

theorem psiP_eq_one' (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) : psiP S L 𝔭 = 1 := by
  classical
  obtain ⟨C, hC, hCi, hvC⟩ := exists_unimod_lattice_good hK hF hs hd S hL hLi h𝔭 hn hvL hvn
  have hfC : fibLoc S L 𝔭 (locF 𝔭 C) ≠ 0 := by
    rw [fibLoc_locF, fibLoc_eq_one hK hF hs hd S hL hLi hC hCi h𝔭 hn hvL hvn hvC]
    exact one_ne_zero
  have hex : ∃ s, IsLocReps S L 𝔭 s := by
    refine ⟨{locF 𝔭 C}, ?_, ?_⟩
    · intro T hT
      rw [Finset.mem_singleton] at hT
      subst hT
      exact ⟨LocF.locF_idem _ _, isIntegralAt_locF h𝔭.isPrime hF hCi, hfC⟩
    · intro T hTl _ hT
      obtain ⟨g, hg, e⟩ := good_orbit hK hF hs hd S hL hLi h𝔭 hn hvL hvn hfC hT
      rw [LocF.locF_idem, hTl] at e
      refine ⟨locF 𝔭 C, ⟨Finset.mem_singleton_self _, g, hg, e⟩, ?_⟩
      rintro T₀ ⟨h1, -⟩
      exact Finset.mem_singleton.mp h1
  unfold psiP
  rw [dite_eq_left hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set s := hex.choose
  obtain ⟨T₀, ⟨hT₀, -⟩, -⟩ := h2 (locF 𝔭 C) (LocF.locF_idem _ _)
    (isIntegralAt_locF h𝔭.isPrime hF hCi) hfC
  have hs1 : s = {T₀} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨hT₀, fun T hT => ?_⟩
    obtain ⟨g, hg, e⟩ := good_orbit hK hF hs hd S hL hLi h𝔭 hn hvL hvn (h1 T hT).2.2
      (h1 T₀ hT₀).2.2
    rw [(h1 T hT).1, (h1 T₀ hT₀).1] at e
    obtain ⟨T₁, -, hu⟩ := h2 T₀ (h1 T₀ hT₀).1 (h1 T₀ hT₀).2.1 (h1 T₀ hT₀).2.2
    rw [hu T ⟨hT, g, hg, e⟩, hu T₀ ⟨hT₀, 1, Subgroup.one_mem _, autSub_gmap_one _⟩]
  obtain ⟨e1, e2⟩ := good_term hK hF hs hd S hL hLi h𝔭 hn hvL hvn (h1 T₀ hT₀).1 (h1 T₀ hT₀).2.2
  rw [hs1, Finset.sum_singleton, e1, e2]
  simp

end Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCountPosBasis
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem exists_arch {S : Subring K} {ϖ : K} (hS : IsLocUnif S ϖ) {α : Type*} [Fintype α] (f : α → K) :
    ∃ l : ℕ, ∀ a, ϖ ^ l * f a ∈ S := by
  classical
  choose l hl using fun a => hS.arch (f a)
  refine ⟨∑ a, l a, fun a => ?_⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), add_comm, pow_add, mul_assoc]
  exact S.mul_mem (pow_mem hS _) (hl a)

theorem exists_isE (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ e, IsE h (locF 𝔭 (spanO b)) 𝔭 e := by
  classical
  have : 𝔭.IsPrime := h𝔭.isPrime
  let f := algebraMap (𝓞 F) (𝓞 K)
  let g := algebraMap (𝓞 K) K
  let a := (gramK h b)⁻¹
  have hdet : IsUnit (gramK h b).det := isUnit_iff_ne_zero.2 (gramK_det_ne_zero hd b)
  -- Clear the denominators of all entries of the inverse Gram matrix at once.
  obtain ⟨n, hn, ha⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun p : κ × κ => a p.1 p.2))
  have hentry (i j : κ) : ∃ z : 𝓞 K, g z = (n : K) * a i j := by
    have hi := ha (a i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    exact ⟨⟨n • a i j, hi⟩, by simp [g, zsmul_eq_mul]⟩
  have hnspan : Ideal.span {(n : 𝓞 F)} ≠ 0 := by
    simpa using (Int.cast_ne_zero.mpr hn : (n : 𝓞 F) ≠ 0)
  have hpunit : ¬ IsUnit 𝔭 := fun hunit => h𝔭.ne_top (Ideal.isUnit_iff.mp hunit)
  -- Factor out the power of 𝔭 in the denominator ideal.
  obtain ⟨J, hJ, hJp⟩ :=
    (FiniteMultiplicity.of_not_isUnit hpunit hnspan).exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hJp
  obtain ⟨u, huJ, hu⟩ := IsConcreteLE.not_le_iff_exists.mp hJp
  generalize multiplicity 𝔭 (Ideal.span {(n : 𝓞 F)}) = l at hJ
  refine ⟨l, fun x hx t ht => ?_⟩
  have htu : t * u ∈ Ideal.span {(n : 𝓞 F)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ht huJ
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp htu
  let v := gramK h b *ᵥ b.equivFun x
  have hv : ∀ j, v j ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro j
    have h1 := hx (b j) (le_locF 𝔭 _ (Submodule.subset_span ⟨j, rfl⟩))
    rw [form_repr h b] at h1
    have hb1 : b.equivFun (b j) = Pi.single j 1 := by
      funext j'
      rw [Basis.equivFun_self, Pi.single_apply]
      simp only [eq_comm]
    have hb2 : star (Pi.single j (1 : K) : κ → K) = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [hl]
    rwa [hb1, hb2, single_one_dotProduct] at h1
  have hx' : b.equivFun x = a *ᵥ v := by
    change b.equivFun x = (gramK h b)⁻¹ *ᵥ (gramK h b *ᵥ b.equivFun x)
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, one_mulVec]
  change f t • x ∈ locF 𝔭 (spanO b)
  rw [← b.sum_equivFun x, hx', Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨s, hs, hsj⟩ := (mem_locF 𝔭 _ _).mp (hv j)
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp hsj
  obtain ⟨z, hz⟩ := hentry i j
  refine (mem_locF 𝔭 _ _).mpr ⟨u * s, fun hm => (h𝔭.isPrime.mem_or_mem hm).elim hu hs, ?_⟩
  have hprod : g (f (u * s)) * g (f t) * (a i j * v j) = g (f w * z * y) := by
    have hw' : g (f w) * (n : K) = g (f t) * g (f u) := by
      simpa [map_mul, f, g] using congrArg (fun r => g (f r)) hw
    have hy' : g y = g (f s) * v j := hy
    calc
      _ = (g (f t) * g (f u)) * (a i j * (g (f s) * v j)) := by
        simp only [map_mul]
        ring
      _ = _ := by
        rw [map_mul, map_mul, hz, hy', ← hw']
        ring
  change f (u * s) • f t • (a i j * v j) • b i ∈ spanO b
  rw [← algebraMap_smul K (f (u * s)), ← algebraMap_smul K (f t), smul_smul, smul_smul]
  change (g (f (u * s)) * g (f t) * (a i j * v j)) • b i ∈ spanO b
  rw [hprod, show g (f w * z * y) • b i = (f w * z * y) • b i from algebraMap_smul K _ _]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isE_eA (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    IsE h (locF 𝔭 (spanO b)) 𝔭 (eA h (locF 𝔭 (spanO b)) 𝔭) :=
  Nat.sInf_mem (s := {e | IsE h (locF 𝔭 (spanO b)) 𝔭 e}) (exists_isE hK hF hd b h𝔭)

end Formalism.HermitianLattices.Ext.L3.HU
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumBoxIdeal
section
open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_abs_alphaN_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ C : ℝ, ∀ n : 𝓞 F, |alphaN h L 𝔭 n| ≤ C := by
  obtain ⟨C, hC⟩ := nkCount_le hK hF hs hd hL hLi hm h𝔭
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := zero_lt_one.trans (BoxSum.one_lt_absNorm h𝔭)
  refine ⟨max C |alphaN h L 𝔭 0|, fun n => ?_⟩
  by_cases hn : n = 0
  · rw [hn]; exact le_max_right _ _
  refine le_trans ?_ (le_max_left _ _)
  set u : ℕ → ℝ := fun k => (nkCount h L 𝔭 k n : ℝ) /
    (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) with hu
  set k₀ := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 with hk₀
  have hstep : ∀ k, k₀ ≤ k → u k = u k₀ := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [← ih]
      simp only [hu]
      rw [nkCount_succ hK hF hs hd hL hLi h𝔭 hn hk, add_mul, one_mul, pow_add]
      push_cast
      field_simp
  have hlim : Tendsto u atTop (𝓝 (u k₀)) :=
    tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => hstep k hk
  have hα : alphaN h L 𝔭 n = u k₀ := hlim.limUnder_eq
  rw [hα, abs_of_nonneg (by simp only [hu]; positivity)]
  simp only [hu]
  rw [div_le_iff₀ (by positivity)]
  exact hC _ _

theorem tendsto_sum_box_ideal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S) {b : Ideal (𝓞 F)} (hb : b ≠ ⊥)
    (hbS : ∀ 𝔭 ∈ S, b ⊔ 𝔭.1 = ⊤) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) *
            ∏ 𝔭 ∈ S, alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
              (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ))))
      atTop (𝓝 ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm b : ℝ) *
          ∏ 𝔭 ∈ S, (1 - etaF K F 𝔭.1 ^ finrank K V *
            (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))⁻¹)) := by
  choose C hC using fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
    exists_abs_alphaN_le hK hF hs hd hL hLi hm 𝔭.2
  have key := BoxSum.tendsto_sum_of_mean hK hF (m := finrank K V) (by omega) S
    (fun 𝔭 n => alphaN h L 𝔭.1 n) C (fun 𝔭 => 2 * vd h L 𝔭.1 + 2) (fun 𝔭 _ n => hC 𝔭 n)
    (fun 𝔭 _ n n' k hn hk hc => alphaN_congr hK hF hs hd hL hLi 𝔭.2 hn (by omega) hc)
    (fun 𝔭 _ => tendsto_mean_alphaN hK hF hs hd hL hLi hm 𝔭.2) hb hbS
  refine (key.mul_const (∏ 𝔭 ∈ S, (1 - etaF K F 𝔭.1 ^ finrank K V *
            (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))⁻¹)).congr fun j => ?_
  rw [mul_assoc, finsum_mem_mul]
  congr 1
  refine finsum_mem_congr rfl fun n _ => ?_
  simp only [div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, mul_assoc]

end Formalism.HermitianLattices.Ext.L3
end
end

