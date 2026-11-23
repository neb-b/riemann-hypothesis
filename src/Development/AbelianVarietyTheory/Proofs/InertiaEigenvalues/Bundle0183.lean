module

public import Mathlib
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionPairingEqInvUniformizer
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

theorem linK_smul {O : Type} [CommRing O] [IsDomain O] {V : Type} [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    (φ : V →ₗ[O] FractionRing O) (c : FractionRing O) (v : V) : φ (c • v) = c * φ v :=
  (LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O) φ).map_smul c v

theorem exists_pairKO_eq_inv_unif : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), ∀ ϖ : O, Irreducible ϖ → ∀ (n : ℕ) (f : ↥D.T'), f ∉ powSub (M := ↥D.T') ϖ n → ∃ x : VT ⧸ D.T, ϖ ^ n • x = 0 ∧ pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ D ϖ hϖ n f hf
  set π : (FractionRing O) := algebraMap O (FractionRing O) ϖ with hπ
  have hπ0 : π ≠ 0 := by
    rw [hπ]; exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ.ne_zero
  have hpn : ∀ y : VT', ϖ ^ n • y = π ^ n • y := fun y => by
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) y, map_pow]
  have hpnT : ∀ y : VT, ϖ ^ n • y = π ^ n • y := fun y => by
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) y, map_pow]
  set f' : VT' := (π ^ n)⁻¹ • (f : VT') with hf'
  have hff' : ϖ ^ n • f' = f := by
    rw [hpn, hf', smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_smul]
  clear_value f' π
  have hnot : f' ∉ D.T' := by
    intro h
    apply hf
    refine mem_powSub.2 ⟨⟨f', h⟩, ?_⟩
    ext
    simp [hff']
  have hnot' : ¬ ∀ x ∈ D.T, D.bT x f' ∈ (1 : Submodule O (FractionRing O)) := hnot
  push_neg at hnot'
  obtain ⟨v, hvT, hu⟩ := hnot'
  set u := D.bT v f' with hu_def
  have hu0 : u ≠ 0 := by
    intro h; apply hu; rw [h]; exact Submodule.zero_mem _
  have hnotint : ¬ IsLocalization.IsInteger O u := by
    rintro ⟨o, ho⟩; exact hu (Submodule.mem_one.2 ⟨o, ho⟩)
  obtain ⟨w, hw⟩ : IsLocalization.IsInteger O u⁻¹ :=
    (ValuationRing.isInteger_or_isInteger O u).resolve_left hnotint
  have hwnu : w ∉ nonunits O → False := by
    intro h
    rw [mem_nonunits_iff, not_not] at h
    obtain ⟨w', hw'⟩ := h
    apply hnotint
    refine ⟨(w'⁻¹ : Oˣ), ?_⟩
    have : algebraMap O (FractionRing O) (w' : O) * u = 1 := by
      rw [hw', hw, inv_mul_cancel₀ hu0]
    have h2 : algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) * algebraMap O (FractionRing O) (w' : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) = algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) * (algebraMap O (FractionRing O) (w' : O) * u) := by rw [this, mul_one]
      _ = u := by rw [← mul_assoc, h2, one_mul]
  have hwm : w ∈ IsLocalRing.maximalIdeal O := by
    by_contra h
    exact hwnu h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at hwm
  obtain ⟨o, ho⟩ := hwm
  have hkey : D.bT (o • v) f' = π⁻¹ := by
    rw [D.bT.map_smul o v, LinearMap.smul_apply, Algebra.smul_def, ← hu_def]
    have h1 : algebraMap O (FractionRing O) o * π = u⁻¹ := by rw [hπ, ← map_mul, ho, hw]
    have : algebraMap O (FractionRing O) o = u⁻¹ * π⁻¹ := by
      rw [← h1, mul_assoc, mul_inv_cancel₀ hπ0, mul_one]
    rw [this, mul_comm u⁻¹, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
  refine ⟨Submodule.Quotient.mk ((π ^ n)⁻¹ • (o • v)), ?_, ?_⟩
  · rw [← Submodule.Quotient.mk_smul, hpnT, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_smul,
      Submodule.Quotient.mk_eq_zero]
    exact D.T.smul_mem o hvT
  · rw [pairKO_mk, ← hkey]
    congr 1
    have e1 : D.bT ((π ^ n)⁻¹ • (o • v)) f = (π ^ n)⁻¹ * D.bT (o • v) f :=
      linK_smul (D.bT.flip (f : VT')) ((π ^ n)⁻¹) (o • v)
    have e2 : D.bT (o • v) ((π ^ n)⁻¹ • (f : VT')) = (π ^ n)⁻¹ * D.bT (o • v) f :=
      linK_smul (D.bT (o • v)) ((π ^ n)⁻¹) (f : VT')
    rw [e1, hf', e2]

end GlobalTheory.LocDualInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePowSmulTorsionLatticeQuotient
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LatTorsFinite

theorem finite_quot_of_isOpen {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] (I : Ideal O) (hI : IsOpen (I : Set O)) : Finite (O ⧸ I) := by
  have hU : ∀ x : O, IsOpen ((fun y => y - x) ⁻¹' (I : Set O)) := fun x =>
    hI.preimage (continuous_id.sub continuous_const)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : O => (fun y => y - x) ⁻¹' (I : Set O))
    hU (fun y _ => Set.mem_iUnion.2 ⟨y, by simp [I.zero_mem]⟩)
  refine Finite.of_surjective (fun x : t => Ideal.Quotient.mk I (x : O)) ?_
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨⟨x, hx⟩, ?_⟩
  exact (Ideal.Quotient.eq.2 hyx).symm

theorem finite_quot_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] (hO : IsTopologicalRing O) (hc : CompactSpace O)
    (hA : IsAdic (IsLocalRing.maximalIdeal O)) {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite (O ⧸ Ideal.span {ϖ ^ n}) := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hopen : IsOpen (((IsLocalRing.maximalIdeal O) ^ n : Ideal O) : Set O) :=
    (isAdic_iff.1 hA).1 n
  rw [hm, Ideal.span_singleton_pow] at hopen
  exact finite_quot_of_isOpen _ hopen

theorem finite_ker_pow_smul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (T : Submodule O V) (hO : IsTopologicalRing O)
    (hc : CompactSpace O) (hA : IsAdic (IsLocalRing.maximalIdeal O)) (hT : IsLatticeIn T)
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite ↥(LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n))) := by
  haveI := finite_quot_pow hO hc hA hϖ n
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hT.1
  haveI : Module.Finite (O ⧸ Ideal.span {ϖ ^ n})
      (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Finite (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) :=
    Module.finite_of_finite (O ⧸ Ideal.span {ϖ ^ n})

  let rep : V ⧸ T → V := fun q => Classical.choose (Submodule.Quotient.mk_surjective T q)
  have hrep : ∀ q, Submodule.Quotient.mk (p := T) (rep q) = q := fun q =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective T q)
  have hmem : ∀ x : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)),
      ϖ ^ n • rep (x : V ⧸ T) ∈ T := by
    intro x
    have hx : (ϖ ^ n) • (x : V ⧸ T) = 0 := x.2
    rw [← hrep (x : V ⧸ T), ← Submodule.Quotient.mk_smul] at hx
    exact (Submodule.Quotient.mk_eq_zero T).1 hx

  have hinj : ∀ v w : V, ϖ ^ n • v = ϖ ^ n • w → v = w := by
    intro v w h
    have h0 : algebraMap O (FractionRing O) (ϖ ^ n) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact pow_ne_zero _ hϖ.ne_zero
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) v,
      ← algebraMap_smul (FractionRing O) (ϖ ^ n) w] at h
    exact smul_right_injective V h0 h
  let f : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)) →
      T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T) :=
    fun x => Submodule.Quotient.mk ⟨ϖ ^ n • rep (x : V ⧸ T), hmem x⟩
  refine Finite.of_injective f ?_
  intro x y hxy
  rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hxy
  obtain ⟨t, -, ht⟩ := hxy
  have ht' : ϖ ^ n • (t : V) = ϖ ^ n • (rep (x : V ⧸ T) - rep (y : V ⧸ T)) := by
    rw [smul_sub]
    exact congrArg Subtype.val ht
  have hd := hinj _ _ ht'
  apply Subtype.ext
  rw [← hrep (x : V ⧸ T), ← hrep (y : V ⧸ T), Submodule.Quotient.eq, ← hd]
  exact t.2

end GlobalTheory.LatTorsFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleSpanAfterMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem _root_.GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top {k Γ : Type} [Field k] [Group Γ] {L : Type}
    [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k))
    (hW : _root_.Formalism.MainNotions.N.Stable (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ)) W) (hne : W ≠ ⊥)
    (hsp : Submodule.span k (Set.range fun g =>
      (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤) :
    _root_.Formalism.MainNotions.N.IsIrrSub (_root_.Formalism.MainNotions.N.mapRep f ρ)
      (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) := by
  classical
  have hmul : ∀ (g : Γ) (w : Fin a → k),
      ((_root_.Formalism.MainNotions.N.mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec (f ∘ w) =
        f ∘ ((ρ g : Matrix (Fin a) (Fin a) k).mulVec w) := by
    intro g w
    funext i
    exact (RingHom.map_mulVec f _ w i).symm
  let T : Γ → (Fin a → L) →ₗ[L] (Fin a → L) := fun g =>
    Matrix.toLin' ((_root_.Formalism.MainNotions.N.mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)
  let A := Submodule.span L (Set.range T)
  let P : Submodule k (Module.End k W) :=
    { carrier := {E | ∃ M ∈ A, ∀ w : W, M (f ∘ (w : Fin a → k)) = f ∘ ((E w : W) : Fin a → k)}
      add_mem' := by
        rintro E₁ E₂ ⟨M₁, hM₁, h₁⟩ ⟨M₂, hM₂, h₂⟩
        refine ⟨M₁ + M₂, A.add_mem hM₁ hM₂, fun w => ?_⟩
        rw [LinearMap.add_apply, h₁, h₂]
        funext i
        simp
      zero_mem' := ⟨0, A.zero_mem, fun w => by funext i; simp⟩
      smul_mem' := by
        rintro c E ⟨M, hM, h⟩
        refine ⟨f c • M, A.smul_mem _ hM, fun w => ?_⟩
        rw [LinearMap.smul_apply, h]
        funext i
        simp }
  have hP : ∀ E, E ∈ P := by
    have hle : Submodule.span k (Set.range fun g =>
        (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) ≤ P := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      refine ⟨T g, Submodule.subset_span ⟨g, rfl⟩, fun w => ?_⟩
      rw [LinearMap.restrict_coe_apply]
      exact hmul g w
    intro E
    apply hle
    rw [hsp]
    exact Submodule.mem_top
  have hA : ∀ W' : Submodule L (Fin a → L), _root_.Formalism.MainNotions.N.IsInv (_root_.Formalism.MainNotions.N.mapRep f ρ) W' →
      ∀ M ∈ A, ∀ v ∈ W', M v ∈ W' := by
    intro W' hW' M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      exact hW' g v hv
    | zero => intro v _; simpa using W'.zero_mem
    | add x y _ _ hx hy => intro v hv; exact W'.add_mem (hx v hv) (hy v hv)
    | smul c x _ hx => intro v hv; exact W'.smul_mem c (hx v hv)
  unfold _root_.Formalism.MainNotions.N.IsIrrSub
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    intro h
    apply hw0
    have hfw : f ∘ w ∈ Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))) :=
      Submodule.subset_span ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at hfw
    funext i
    simpa using congrFun hfw i
  · intro g v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [hmul]
      exact Submodule.subset_span ⟨_, hW g w hw, rfl⟩
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx
  · intro W' hle hst
    by_cases h0 : W' = ⊥
    · exact Or.inl h0
    right
    apply le_antisymm hle
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (funext h)
    rw [Submodule.span_le]
    rintro _ ⟨w₀, hw₀, rfl⟩
    show f ∘ w₀ ∈ W'
    let φ : W →ₗ[k] k := (LinearMap.proj i : (Fin a → k) →ₗ[k] k).comp W.subtype
    let E : Module.End k W := φ.smulRight ⟨w₀, hw₀⟩
    obtain ⟨M, hMA, hM⟩ := hP E
    have key : ∀ y ∈ Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))),
        M y = y i • (f ∘ w₀) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        rw [hM ⟨w, hw⟩]
        funext j
        simp [E, φ]
      | zero => simp
      | add y z _ _ hy hz => rw [map_add (f := _), hy, hz, Pi.add_apply, add_smul]
      | smul c y _ hy => rw [map_smul, hy, Pi.smul_apply, smul_eq_mul, mul_smul]
    have hmem : M x ∈ W' := hA W' hst M hMA x hx
    rw [key x (hle hx)] at hmem
    have hsm := W'.smul_mem (x i)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at hsm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHausdorffInvariantsQuotientOfFiniteFree
section
namespace GlobalTheory.InertiaEigenvalues.FreeHausdorff

open PowerSeries GlobalTheory.BK

theorem eq_zero_of_mem_pow {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] {l : ℕ} (hl : ‖(l : K)‖ < 1) {y : O}
    (hy : ∀ n : ℕ, y ∈ Ideal.span {(l : O)} ^ n) : y = 0 := by
  have hb : ∀ n : ℕ, ‖algebraMap O K y‖ ≤ ‖(l : K)‖ ^ n := by
    intro n
    have h := hy n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
    obtain ⟨a, rfl⟩ := h
    have ha : ‖algebraMap O K a‖ ≤ 1 :=
      (IsUnitBall.mem_range_iff (O := O) (algebraMap O K a)).1 ⟨a, rfl⟩
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    calc ‖algebraMap O K a‖ * ‖(l : K)‖ ^ n ≤ 1 * ‖(l : K)‖ ^ n :=
          mul_le_mul_of_nonneg_right ha (pow_nonneg (norm_nonneg _) n)
      _ = ‖(l : K)‖ ^ n := one_mul _
  have h0 : ‖algebraMap O K y‖ ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl) hb
  have h1 : algebraMap O K y = 0 := norm_le_zero_iff.1 h0
  exact IsUnitBall.inj (K := K) (h1.trans (map_zero _).symm)

theorem isHausdorff_ring {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] {l : ℕ} (hl : ‖(l : K)‖ < 1) : IsHausdorff (Ideal.span {(l : O)}) O := by
  refine ⟨fun x hx => eq_zero_of_mem_pow (K := K) hl fun n => ?_⟩
  have h := SModEq.sub_mem.1 (hx n)
  simpa [smul_eq_mul, Ideal.mul_top] using h

theorem isHausdorff_of_free {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] (I : Ideal R) [h : IsHausdorff I R] : IsHausdorff I M := by
  refine ⟨fun x hx => ?_⟩
  let b := Module.Free.chooseBasis R M
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine h.haus _ fun n => ?_
  have hxn : x ∈ I ^ n • (⊤ : Submodule R M) := by simpa using SModEq.sub_mem.1 (hx n)
  have hle : (I ^ n • (⊤ : Submodule R M)).map (b.coord i) ≤ I ^ n • (⊤ : Submodule R R) := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.smul_le.2 fun r hr m _ => ?_
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  have := hle (Submodule.mem_map_of_mem hxn)
  rw [SModEq.sub_mem, sub_zero]
  simpa using this

end GlobalTheory.InertiaEigenvalues.FreeHausdorff

namespace GlobalTheory.InertiaEigenvalues

open PowerSeries GlobalTheory.BK

theorem isHausdorff_Z_of_finiteFree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D → IsHausdorff (Ideal.span {(l : O)}) D.Z := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hD
  haveI : Module.Free O D.Z := hD.1
  haveI : IsHausdorff (Ideal.span {(l : O)}) O :=
    FreeHausdorff.isHausdorff_ring (K := K) (norm_l_lt_one (K := K) l)
  exact FreeHausdorff.isHausdorff_of_free _

end GlobalTheory.InertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAnalyticFiltrationIffLatticeFiltrationAdd
section
noncomputable section

open PowerSeries Matrix

namespace GlobalTheory.BK.FilAn

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι)

theorem E_pow_smul_mem_extRpi {β : ℕ} (hβ : ∀ v ∈ P.M, E K l e ^ β • v ∈ P.L) {m : Vec K a ι}
    (hm : m ∈ P.Mext (Rpi O K l e)) : E K l e ^ β • m ∈ P.ext (Rpi O K l e) :=
  P.smul_mem_ext_of_basis (fun i => hβ _ (P.bas_mem_M i)) (A_le_Rpi l e) hm

theorem mem_extInvL_of_Ezpow_smul {i : ℤ} {y : Vec K a ι} (hy : y ∈ P.ext (Rpi O K l e))
    (hg : Ezpow K l e i • y ∈ P.Mext (invL l (A O K))) : y ∈ P.ext (invL l (A O K)) := by
  refine mem_tot.2 fun τ => P.mem_extc_iff.2 fun j => ?_
  have hc : (P.mxInv τ *ᵥ y τ) j ∈ Rpi O K l e := P.mem_extc_iff.1 (mem_tot.1 hy τ) j
  have hB : invE l e (A O K) ≤ invE l e (invL l (A O K)) := away_mono (le_away _ _) rfl
  have h1 : (P.mxInv τ *ᵥ (Ezpow K l e i • y) τ) j ∈ invE l e (invL l (A O K)) := by
    simp only [Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun k _ => mul_mem (hB (P.mxInv_mem τ j k))
      (le_away _ _ (mem_tot.1 hg τ k))
  obtain ⟨n, hn⟩ := h1
  have h2 : Ezpow K l e (n + i) * (P.mxInv τ *ᵥ y τ) j ∈ invL l (A O K) := by
    rw [Ezpow_add, Ezpow_natCast, mul_assoc]
    simpa [Matrix.mulVec_smul] using hn
  have h3 := mul_mem ((Ezpow_mem_invL_A_iff (O := O) (K := K) (l := l) (e := e)
    (i := ((-(n + i)).toNat : ℤ))).2 (by omega)) h2
  rw [← mul_assoc, ← Ezpow_add,
    show (((-(n + i)).toNat : ℕ) : ℤ) + (n + i) = ((n + i).toNat : ℕ) by omega, Ezpow_natCast] at h3
  exact mem_invL_A_of_E_pow_mul l e _ hc h3

omit [IsUltrametricDist K] [CompleteSpace K] [IsUnitBall O K] [Fintype ι] [DecidableEq ι] in
theorem Ezpow_zero' : Ezpow K l e 0 = 1 := by
  simpa using Ezpow_natCast (K := K) l e 0

omit [CompleteSpace K] in
theorem mem_extRpi_of_mem_shiftE_one {z : Vec K a ι} (hz : z ∈ shiftE l e 1 (P.ext (Rpi O K l e))) :
    z ∈ P.ext (Rpi O K l e) := by
  have h := P.smul_tot_mem_ext (f := fun _ => E K l e) (fun _ => E_mem l e _) (mem_shiftE.1 hz)
  have h1 : E K l e * Ezpow K l e (-1) = 1 := by
    simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
  have h2 : ((fun _ : ZMod a => E K l e) • Ezpow K l e (-1) • z) = z := by
    ext τ j
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, h1, one_mul]
  rwa [h2] at h

theorem exists_mem_filL_of_mem_inf [NeZero a] (i : ℤ) {x : Vec K a ι}
    (hx : x ∈ P.ext (Rpi O K l e) ⊓ shiftE l e i (P.Mext (Rpi O K l e))) :
    ∃ y ∈ P.filL i, x - y ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
  obtain ⟨hxL, hxM⟩ := Submodule.mem_inf.1 hx
  obtain ⟨-, β, -, hβ⟩ := P.exists_exponents
  set N : ℕ := (β + 1 - i).toNat with hN
  choose g hg h hh hgh using fun τ k => exists_div_E_pow l e N (mem_tot.1 (mem_shiftE.1 hxM) τ k)
  have hgM : g ∈ P.Mext (invL l (A O K)) := mem_tot.2 fun τ k => hg τ k
  have hhM : h ∈ P.Mext (Rpi O K l e) := mem_tot.2 fun τ k => hh τ k
  have hx' : Ezpow K l e (-i) • x = g + E K l e ^ N • h := by
    funext τ k
    exact hgh τ k
  have hxe : x = Ezpow K l e i • g + Ezpow K l e i • E K l e ^ N • h := by
    rw [← smul_add, ← hx', smul_smul, ← Ezpow_add, add_neg_cancel, Ezpow_zero', one_smul]
  have hsub : x - Ezpow K l e i • g ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
    rw [mem_shiftE]
    have h1 := E_pow_smul_mem_extRpi P hβ (P.smul_tot_mem_Mext (f := fun _ => E K l e ^ (i - 1 + N - β).toNat)
      (fun _ => pow_mem (E_mem l e _) _) hhM)
    convert h1 using 1
    have hs : Ezpow K l e (-1) * (Ezpow K l e i * E K l e ^ N) =
        E K l e ^ β * E K l e ^ (i - 1 + N - β).toNat := by
      simp only [← Ezpow_natCast, ← Ezpow_add]
      congr 1
      omega
    rw [hxe, add_sub_cancel_left]
    funext τ k
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul]
    linear_combination (h τ k) * hs
  refine ⟨Ezpow K l e i • g, Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨?_, ?_⟩), hsub⟩
  · refine mem_extInvL_of_Ezpow_smul P (i := -i) ?_ ?_
    · have := sub_mem hxL (mem_extRpi_of_mem_shiftE_one P hsub)
      rwa [sub_sub_cancel] at this
    · rwa [smul_smul, ← Ezpow_add, neg_add_cancel, Ezpow_zero', one_smul]
  · rwa [mem_shiftE, smul_smul, ← Ezpow_add, neg_add_cancel, Ezpow_zero', one_smul]

end GlobalTheory.BK.FilAn


open GlobalTheory.BK in
theorem GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (i : ℤ) (x : Vec K a ι), x ∈ (P.ext (Rpi O K l e) ⊓ shiftE l e i (P.Mext (Rpi O K l e))) ⊔ shiftE l e 1 (P.ext (Rpi O K l e)) ↔ ∃ y ∈ P.filL i, x - y ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P i x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y, hy, hxy⟩ := FilAn.exists_mem_filL_of_mem_inf P i hx₁
    refine ⟨y, hy, ?_⟩
    rw [add_sub_right_comm]
    exact add_mem hxy hx₂
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨hy₁L, hy₁M⟩ := Submodule.mem_inf.1 hy₁
    refine Submodule.mem_sup.2 ⟨y₁, Submodule.mem_inf.2 ⟨P.ext_mono (invL_A_le_Rpi l e) hy₁L,
      mem_shiftE.2 (P.Mext_mono (invL_A_le_Rpi l e) (mem_shiftE.1 hy₁M))⟩, y₂ + (x - (y₁ + y₂)),
      add_mem (mem_shiftE.2 (P.ext_mono (invL_A_le_Rpi l e) (mem_shiftE.1 hy₂))) hxy, by abel⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRigidFunctionsClosedDiscOfAdicLimitStatement
section
open PowerSeries GlobalTheory.BK Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rigidFunctionsClosedDisc_of_adic_limit : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) (k : ℝ) (f : K⟦X⟧) (s : ℕ → K⟦X⟧), (∀ n, s n ∈ R O K l k) → (∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ f - s n) → Tendsto (fun n => normR l k (s (n + 1) - s n)) atTop (𝓝 0) → f ∈ R O K l k := by
  first | exact @GlobalTheory.mem_R_of_adic_limit | exact GlobalTheory.mem_R_of_adic_limit | (intros; apply GlobalTheory.mem_R_of_adic_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentCharactersEqAndFrobeniusStableStatement
section
open GlobalTheory.BK PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameDescent_characters_eq_and_frobenius_stable : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P), (∀ τ σ, Δ.chars τ = Δ.chars σ) ∧ ∀ τ, ∀ c ∈ Δ.chars τ, (l : ZMod e) * c ∈ Δ.chars τ := by
  first | exact @GlobalTheory.BK.chars_eq_and_mul_mem | exact GlobalTheory.BK.chars_eq_and_mul_mem | (intros; apply GlobalTheory.BK.chars_eq_and_mul_mem <;> assumption)
end

