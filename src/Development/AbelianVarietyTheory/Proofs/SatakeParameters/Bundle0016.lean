module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalSubringMonicRootsResidueStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_subring_monic_roots_residue : ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] (φ : k →+* K) (R : Subring K) (𝔪 : Ideal R),
    φ.range ≤ R → 𝔪.IsMaximal → (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) →
    (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) → (∀ x : K, IsIntegral R x → x ∈ R) →
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  first | (exact @GlobalTheory.LocInField.exists_local_subring) | (exact GlobalTheory.LocInField.exists_local_subring) | (intros; apply GlobalTheory.LocInField.exists_local_subring  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaElementEqOneOrLiesAboveFinitePlace
section
open NumberField IsDedekindDomain Neutral.HilbertClassField

namespace GlobalTheory

theorem inertiaEl_eq_one_or_liesAbove : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω),
    ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → g = 1 ∨ ∃ v : HeightOneSpectrum (𝓞 E), LiesAbove A v := by
  intro E Ω _ _ _ _ _ A g hg
  have hint : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A := fun x =>
    ReciprocityTheory.ChartRestriction.L1.mem_of_isIntegral A ((NumberField.RingOfIntegers.isIntegral_coe x).algebraMap)
  let φ : 𝓞 E →+* A := RingHom.codRestrict ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)) A hint
  let I : Ideal (𝓞 E) := Ideal.comap φ (IsLocalRing.maximalIdeal A)
  have hI : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A.nonunits ↔ x ∈ I := by
    intro x
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal, Ideal.mem_comap]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hint x, h⟩
  by_cases hbot : I = ⊥
  · left
    have hE : ∀ y : E, algebraMap E Ω y ∈ A := by
      intro y
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      have hbn : algebraMap E Ω (algebraMap (𝓞 E) E b) ∉ A.nonunits := by
        rw [show algebraMap (𝓞 E) E b = (b : E) from rfl, hI, hbot, Ideal.mem_bot]; exact hb0
      have hbinv : (algebraMap E Ω (algebraMap (𝓞 E) E b))⁻¹ ∈ A := by
        rw [ValuationSubring.mem_nonunits_iff_or] at hbn
        push_neg at hbn; exact hbn.2
      rw [map_div₀, div_eq_mul_inv]
      exact mul_mem (hint a) hbinv
    have hall : ∀ x : Ω, x ∈ A := by
      intro x
      have hx : IsIntegral E x := ((IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic x).isIntegral
      obtain ⟨p, hpm, hp⟩ := hx
      let ψ : E →+* A := RingHom.codRestrict (algebraMap E Ω) A hE
      have hcomp : (algebraMap A Ω).comp ψ = algebraMap E Ω := by ext; rfl
      have h1 : IsIntegral A x := ⟨p.map ψ, hpm.map ψ, by rw [Polynomial.eval₂_map, hcomp]; exact hp⟩
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
      rw [← hy]; exact y.2
    ext x
    have h := hg.2 x (hall x)
    rw [ValuationSubring.mem_nonunits_iff_or] at h
    rcases h with h | h
    · simpa [sub_eq_zero] using h
    · exact absurd (hall _) h
  · right
    exact ⟨⟨I, Ideal.IsPrime.comap φ, hbot⟩, fun x => hI x⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthIntegralCocyclesRationalCoboundariesLe
section
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

namespace GlobalTheory

theorem cocycle_bound_length_le : ∀ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (Z : Submodule O (G → V)), (∀ c ∈ Z, ∀ g, c g ∈ L.T) → Module.length O (↥(Z ⊓ (B1 ρ).restrictScalars O) ⧸ (latticeCoboundaries L).comap (Z ⊓ (B1 ρ).restrictScalars O).subtype) ≤ Module.length O ↥(Representation.invariants (repD L)) := by
  intro G _ LL _ O _ _ V _ _ _ _ ρ L Z hZ
  set M := Z ⊓ (B1 ρ).restrictScalars O with hM
  set K := (latticeCoboundaries L).comap M.subtype with hK

  let χ : V →ₗ[O] (G → V) ⧸ latticeCoboundaries L := (latticeCoboundaries L).mkQ ∘ₗ (cob ρ).restrictScalars O
  have hχ : L.T ≤ LinearMap.ker χ := by
    intro t ht
    simp only [LinearMap.mem_ker, χ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨t, ht, rfl⟩
  let ψ : ↥(Representation.invariants (repD L)) →ₗ[O] (G → V) ⧸ latticeCoboundaries L :=
    (L.T.liftQ χ hχ) ∘ₗ (Representation.invariants (repD L)).subtype
  let ι : M →ₗ[O] (G → V) ⧸ latticeCoboundaries L := (latticeCoboundaries L).mkQ ∘ₗ M.subtype
  have hKι : K ≤ LinearMap.ker ι := by
    intro x hx
    simpa [ι, K, Submodule.Quotient.mk_eq_zero] using hx
  let f : (M ⧸ K) →ₗ[O] (G → V) ⧸ latticeCoboundaries L := K.liftQ ι hKι
  have hfinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K x
    simp only [LinearMap.mem_ker, f, Submodule.liftQ_apply, ι, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hx
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, K, Submodule.mem_comap,
      Submodule.coe_subtype]
    exact hx
  have hrange : LinearMap.range f ≤ LinearMap.range ψ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨⟨c, hcM⟩, rfl⟩ := Submodule.Quotient.mk_surjective K x
    obtain ⟨hcZ, hcB⟩ := hcM
    obtain ⟨v, hv⟩ := hcB
    have hinv : L.T.mkQ v ∈ Representation.invariants (repD L) := by
      intro g
      change (Submodule.Quotient.mk ((ρ g) v) : V ⧸ L.T) = Submodule.Quotient.mk v
      rw [Submodule.Quotient.eq]
      have := hZ c hcZ g
      rw [← hv] at this
      simpa [cob] using this
    refine ⟨⟨_, hinv⟩, ?_⟩
    simp [ψ, f, ι, χ, hv]
  calc Module.length O (M ⧸ K) ≤ Module.length O (LinearMap.range ψ) :=
        Module.length_le_of_injective ((Submodule.inclusion hrange).comp f.rangeRestrict) (by
          intro a b hab
          apply hfinj
          have := congrArg Subtype.val hab
          simpa using this)
    _ ≤ _ := Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumAlternatingCardElementarySublatticesAbove
section
open GlobalTheory.LatHecke

namespace GlobalTheory.LatHecke

theorem sum_alt_card_subElem_ge : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (n : ℕ)
    (L M : Lat O K r), 1 ≤ n → M ∈ subIdx n L →
    ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) *
      (({M' | M' ∈ subElem k L ∧ M.1 ≤ M'.1} : Set (Lat O K r)).ncard : ℂ) = 0 := by
  intro O K _ _ _ _ _ _ _ r n L M hn hM
  classical
  set m := IsLocalRing.maximalIdeal O with hm
  set A : Submodule O (Fin r → K) := M.1 ⊔ m • L.1 with hA
  have hML : M.1 ≤ L.1 := hM.1
  have hAL : A ≤ L.1 := sup_le hML Submodule.smul_le_right
  set P : Submodule O L.1 := A.comap L.1.subtype with hP
  have hPA : P.map L.1.subtype = A := by rw [Submodule.map_comap_subtype, inf_eq_right.2 hAL]
  have htor : Module.IsTorsionBySet O (L.1 ⧸ P) (m : Set O) := by
    intro x a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact Submodule.mem_sup_right (Submodule.smul_mem_smul a.2 y.2)
  letI : Module (IsLocalRing.ResidueField O) (L.1 ⧸ P) := htor.module
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) (L.1 ⧸ P) := htor.isScalarTower
  have hq2 : 2 ≤ qRes O := two_le_qRes
  have hqn : 0 < qRes O ^ n := pow_pos (by omega) _
  have hcardV : Nat.card (L.1 ⧸ P) = A.toAddSubgroup.relIndex L.1.toAddSubgroup := rfl
  have hmul := AddSubgroup.relIndex_mul_relIndex M.1.toAddSubgroup A.toAddSubgroup L.1.toAddSubgroup
    ((Submodule.toAddSubgroup_le _ _).2 le_sup_left) ((Submodule.toAddSubgroup_le _ _).2 hAL)
  have hdvd : Nat.card (L.1 ⧸ P) ∣ qRes O ^ n := ⟨M.1.toAddSubgroup.relIndex A.toAddSubgroup, by
    rw [hcardV, mul_comm, hmul, hM.2]⟩
  haveI : Finite (L.1 ⧸ P) := Nat.finite_of_card_ne_zero (Nat.pos_of_dvd_of_pos hdvd hqn).ne'
  haveI : FiniteDimensional (IsLocalRing.ResidueField O) (L.1 ⧸ P) := Module.Finite.of_finite
  set d := Module.finrank (IsLocalRing.ResidueField O) (L.1 ⧸ P) with hd
  have hcardq : Nat.card (L.1 ⧸ P) = qRes O ^ d :=
    Module.natCard_eq_pow_finrank (K := IsLocalRing.ResidueField O)
  have hdn : d ≤ n := (Nat.pow_dvd_pow_iff_le_right (by omega)).1 (hcardq ▸ hdvd)
  have hd1 : 1 ≤ d := by
    by_contra h0
    have h0' : d = 0 := by omega
    have h1 : A.toAddSubgroup.relIndex L.1.toAddSubgroup = 1 := by
      rw [← hcardV, hcardq, h0', pow_zero]
    have h2 : L.1 ≤ M.1 ⊔ m • L.1 := (Submodule.toAddSubgroup_le _ _).1 (AddSubgroup.relIndex_eq_one.1 h1)
    have h3 : L.1 ≤ M.1 := Submodule.le_of_le_smul_of_le_jacobson_bot L.2.fg
      (by rw [hm, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) h2
    have h4 : M.1.toAddSubgroup.relIndex L.1.toAddSubgroup = 1 :=
      AddSubgroup.relIndex_eq_one.2 ((Submodule.toAddSubgroup_le _ _).2 h3)
    rw [hM.2] at h4
    have := Nat.one_lt_pow (by omega : n ≠ 0) (by omega : 1 < qRes O)
    omega

  set k := IsLocalRing.ResidueField O
  set V := L.1 ⧸ P
  have hdV : Module.finrank k V = d := rfl
  let Φ : Submodule k V → Submodule O (Fin r → K) := fun W =>
    ((W.restrictScalars O).comap P.mkQ).map L.1.subtype
  have hPC : ∀ W : Submodule k V, P ≤ (W.restrictScalars O).comap P.mkQ := fun W x hx => by
    rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hx]
    exact zero_mem _
  have hΦA : ∀ W, A ≤ Φ W := fun W => hPA ▸ Submodule.map_mono (hPC W)
  have hΦL : ∀ W, Φ W ≤ L.1 := fun W => Submodule.map_subtype_le _ _
  have hlat : ∀ W, (Φ W).IsFullLattice K := fun W => by
    haveI := (maxMul L).2
    exact Submodule.IsLattice.of_le_of_isLattice_of_fg K
      (show (maxMul L).1 ≤ Φ W from le_trans le_sup_right (hΦA W)) (L.2.fg.of_le (hΦL W))
  let f : Submodule k V → Lat O K r := fun W => ⟨Φ W, hlat W⟩
  have hinj : Function.Injective f := by
    intro W W' h
    have h1 : Φ W = Φ W' := congrArg Subtype.val h
    have h2 := Submodule.map_injective_of_injective L.1.injective_subtype h1
    have h3 := Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective P) h2
    exact Submodule.restrictScalars_injective O k V h3
  have hidx : ∀ W : Submodule k V,
      (Φ W).toAddSubgroup.relIndex L.1.toAddSubgroup = qRes O ^ Module.finrank k (V ⧸ W) := by
    intro W
    change Nat.card (L.1 ⧸ (Φ W).comap L.1.subtype) = _
    rw [Submodule.comap_map_eq_of_injective L.1.injective_subtype,
      ← Nat.card_congr (Submodule.quotientQuotientEquivQuotient P _ (hPC W)).toEquiv,
      Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective P),
      Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv O W).toEquiv,
      Module.natCard_eq_pow_finrank (K := k)]
    rfl
  have hset : ∀ j, ({M' | M' ∈ subElem j L ∧ M.1 ≤ M'.1} : Set (Lat O K r)) =
      f '' {W | Module.finrank k (V ⧸ W) = j} := by
    intro j
    ext M'
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨⟨hle, hi⟩, hmL⟩, hMM⟩
      set C := M'.1.comap L.1.subtype
      have hPC' : P ≤ C := Submodule.comap_mono (sup_le hMM hmL)
      let Wk : Submodule k V :=
        { (C.map P.mkQ).toAddSubmonoid with
          smul_mem' := fun c x hx => by
            obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
            have e : (IsLocalRing.residue O a) • x = a • x := htor.mk_smul a x
            rw [e]
            exact (C.map P.mkQ).smul_mem a hx }
      have hWr : Wk.restrictScalars O = C.map P.mkQ := rfl
      have heq : Φ Wk = M'.1 := by
        change ((Wk.restrictScalars O).comap P.mkQ).map L.1.subtype = M'.1
        rw [hWr, Submodule.comap_map_mkQ, sup_eq_right.2 hPC', Submodule.map_comap_subtype,
          inf_eq_right.2 hle]
      refine ⟨Wk, ?_, Subtype.ext heq⟩
      have h := hidx Wk
      rw [heq, hi] at h
      exact (Nat.pow_right_injective hq2 h).symm
    · rintro ⟨W, hW, rfl⟩
      exact ⟨⟨⟨hΦL W, (hidx W).trans (by rw [hW])⟩, le_trans le_sup_right (hΦA W)⟩,
        le_trans le_sup_left (hΦA W)⟩
  have hcount : ∀ j, (({M' | M' ∈ subElem j L ∧ M.1 ≤ M'.1} : Set (Lat O K r)).ncard : ℂ) =
      (Nat.card {W : Submodule k V // Module.finrank k (V ⧸ W) = j} : ℂ) := by
    intro j
    rw [hset j, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
    rfl
  have hI := _root_.GlobalTheory.qBinomial_subspaces k V 1
  rw [Finset.prod_eq_zero (Finset.mem_range.2 (by rw [hdV]; omega : 0 < Module.finrank k V)) (by simp)] at hI
  have hqk : (Nat.card k : ℂ) = (qRes O : ℂ) := rfl
  simp only [one_pow, mul_one, hqk, hdV] at hI
  have hzero : ∀ x ∈ Finset.range (n + 1), x ∉ Finset.range (d + 1) →
      (-1 : ℂ) ^ x * (qRes O : ℂ) ^ (x * (x - 1) / 2) *
        (({M' | M' ∈ subElem x L ∧ M.1 ≤ M'.1} : Set (Lat O K r)).ncard : ℂ) = 0 := by
    intro x _ hx
    rw [Finset.mem_range] at hx
    haveI : IsEmpty {W : Submodule k V // Module.finrank k (V ⧸ W) = x} :=
      ⟨fun ⟨W, hW⟩ => by have := Submodule.finrank_quotient_le W; rw [hdV] at this; omega⟩
    rw [hcount, Nat.card_of_isEmpty]
    simp
  rw [← Finset.sum_subset (fun x hx => Finset.mem_range.2 (by have := Finset.mem_range.1 hx; omega)) hzero]
  simp only [hcount]
  exact hI

end GlobalTheory.LatHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionHeisenbergInvariant
section
namespace GlobalTheory.UnipNormalTrace

open Module

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem isNilpotent_of_trace_pow_eq_zero {K : Type} [Field K] [CharZero K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : Module.End K V)
    (h : ∀ k, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) : IsNilpotent f := by
  first
  | exact @_root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow
  | exact _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow
  | (apply _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow ..)

end GlobalTheory.UnipNormalTrace
end

