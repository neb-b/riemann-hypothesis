module

public import Mathlib
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualLatticePairingEqInvUniformizer
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

section PerfL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
  [IsScalarTower O (FractionRing O) V]

theorem exists_form_of_not_mem {T : Submodule O V} (hT : IsLatticeIn T) {v : V} (hv : v ∉ T) :
    ∃ ψ : V →ₗ[FractionRing O] FractionRing O,
      (∀ t ∈ T, ψ t ∈ (1 : Submodule O (FractionRing O))) ∧
        ψ v ∉ (1 : Submodule O (FractionRing O)) := by
  classical
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hT.1
  haveI : Module.IsTorsionFree O T := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    have h1 : (algebraMap O (FractionRing O) r) • (m : V) = 0 := by
      rw [algebraMap_smul]
      exact congrArg Subtype.val h
    rcases smul_eq_zero.1 h1 with h2 | h2
    · left
      exact (IsFractionRing.injective O (FractionRing O)) (by rw [h2, map_zero])
    · right
      exact Subtype.ext h2
  haveI : Module.Free O T := Module.free_of_finite_type_torsion_free'
  let e := Module.Free.chooseBasis O T
  let w : Module.Free.ChooseBasisIndex O T → V := fun i => (e i : V)
  have hliO : LinearIndependent O w := e.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hli : LinearIndependent (FractionRing O) w :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hliO
  have hspO : Submodule.span O (Set.range w) = T := by
    have h := congrArg (Submodule.map T.subtype) e.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
  have hsp : ⊤ ≤ Submodule.span (FractionRing O) (Set.range w) := by
    rw [← hT.2]
    apply Submodule.span_le.2
    intro t ht
    rw [← hspO] at ht
    exact Submodule.span_subset_span O (FractionRing O) (Set.range w) ht
  let bK := Module.Basis.mk hli hsp
  have hbK : ∀ i, bK i = w i := fun i => Module.Basis.mk_apply hli hsp i

  have hint : ∀ t ∈ T, ∀ j, bK.repr t j ∈ (1 : Submodule O (FractionRing O)) := by
    intro t ht
    rw [← hspO] at ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro j
      rw [← hbK, bK.repr_self, Finsupp.single_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact Submodule.zero_mem _
    | zero => intro j; simp
    | add x y _ _ hx hy => intro j; rw [map_add (f := _), Finsupp.add_apply]; exact Submodule.add_mem _ (hx j) (hy j)
    | smul a x _ hx =>
      intro j
      rw [← algebraMap_smul (FractionRing O) a x, map_smul, Finsupp.smul_apply, algebraMap_smul]
      exact Submodule.smul_mem _ a (hx j)
  have hex : ∃ j, bK.repr v j ∉ (1 : Submodule O (FractionRing O)) := by
    by_contra hne
    push Not at hne
    apply hv
    rw [← bK.linearCombination_repr v, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hne j)
    rw [← ha, algebraMap_smul, hbK]
    exact Submodule.smul_mem _ a (e j).2
  obtain ⟨j, hj⟩ := hex
  exact ⟨bK.coord j, fun t ht => hint t ht j, hj⟩

theorem exists_mul_eq_inv_unif {ϖ : O} (hϖ : Irreducible ϖ) {u : FractionRing O}
    (hu : u ∉ (1 : Submodule O (FractionRing O))) :
    ∃ o : O, algebraMap O (FractionRing O) o * u = (algebraMap O (FractionRing O) ϖ)⁻¹ := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Submodule.zero_mem _)
  rcases ValuationRing.isInteger_or_isInteger O u with h | ⟨w, hw⟩
  · exact absurd (Submodule.mem_one.2 h) hu
  have hwu : ¬ IsUnit w := by
    intro hw'
    apply hu
    refine Submodule.mem_one.2 ⟨((hw'.unit⁻¹ : Oˣ) : O), ?_⟩
    have h1 : algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O) * u⁻¹ = 1 := by
      rw [← hw, ← map_mul, IsUnit.val_inv_mul, map_one]
    calc algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O)
        = algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O) * (u⁻¹ * u) := by
          rw [inv_mul_cancel₀ hu0, mul_one]
      _ = u := by rw [← mul_assoc, h1, one_mul]
  have hwm : w ∈ IsLocalRing.maximalIdeal O := hwu
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hwm
  obtain ⟨o, rfl⟩ := hwm
  refine ⟨o, ?_⟩
  rw [map_mul] at hw
  symm
  apply inv_eq_of_mul_eq_one_right
  calc algebraMap O (FractionRing O) ϖ * (algebraMap O (FractionRing O) o * u)
      = (algebraMap O (FractionRing O) ϖ * algebraMap O (FractionRing O) o) * u := by ring
    _ = 1 := by rw [hw, inv_mul_cancel₀ hu0]

end PerfL

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT]
  [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT']
  [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  {G : Type} [Group G] [TopologicalSpace G]

theorem exists_dual_pairKO_eq_inv_unif (D : LatData O G VT VT') (hT : IsLatticeIn D.T)
    (hP : PerfectRight D.bT) (ϖ : O) (hϖ : Irreducible ϖ) (x : VT ⧸ D.T) (hx : x ≠ 0) :
    ∃ f : ↥D.T', pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective D.T x
  have hv : v ∉ D.T := fun h => hx ((Submodule.Quotient.mk_eq_zero _).2 h)
  obtain ⟨ψ, hψT, hψv⟩ := exists_form_of_not_mem hT hv
  obtain ⟨f, hf, -⟩ := hP ψ
  have hfT : f ∈ D.T' := fun t ht => by rw [hf]; exact hψT t ht
  obtain ⟨o, ho⟩ := exists_mul_eq_inv_unif hϖ (u := D.bT v f) (by rw [hf]; exact hψv)
  refine ⟨⟨o • f, D.T'.smul_mem o hfT⟩, ?_⟩
  rw [pairKO_mk]
  congr 1
  show D.bT v (o • f) = _
  rw [map_smul, Algebra.smul_def, ho]

end Main

end GlobalTheory.LocDualInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntRingHomCongrToZModPow
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

namespace GlobalTheory.ZpHomAdic

open IsLocalRing Filter Topology

theorem isPrecomplete_of_compact {O : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] (hA : IsAdic (maximalIdeal O)) :
    IsPrecomplete (maximalIdeal O) O := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, -, hL⟩ := (isCompact_univ (X := O)).exists_clusterPt (f := Filter.map f atTop)
    (le_principal_iff.2 univ_mem)
  refine ⟨L, fun n => ?_⟩
  have hopen : IsOpen ((maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.1 hA).1 n
  have hclosed : IsClosed ((maximalIdeal O ^ n : Ideal O) : Set O) :=
    AddSubgroup.isClosed_of_isOpen ((maximalIdeal O ^ n).toAddSubgroup) hopen
  have hS : IsClosed {y : O | f n - y ∈ maximalIdeal O ^ n} :=
    hclosed.preimage (continuous_const.sub continuous_id)
  have hmem : {y : O | f n - y ∈ maximalIdeal O ^ n} ∈ Filter.map f atTop := by
    refine Filter.mem_map.2 (Filter.mem_atTop_sets.2 ⟨n, fun k hk => ?_⟩)
    have := hf hk
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this
  have hL' : L ∈ closure {y : O | f n - y ∈ maximalIdeal O ^ n} :=
    mem_closure_iff_clusterPt.2 (hL.mono (le_principal_iff.2 hmem))
  rw [hS.closure_eq] at hL'
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact hL'

theorem isHausdorff_dvr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    IsHausdorff (maximalIdeal O) O := by
  refine ⟨fun x hx => ?_⟩
  rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal O)
    (maximalIdeal.isMaximal O).ne_top, Ideal.mem_iInf]
  intro n
  have := hx n
  rwa [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this

theorem ringHom_zmod_apply {N : ℕ} [NeZero N] {R : Type*} [Ring R] (ψ : ZMod N →+* R) (z : ZMod N) :
    ψ z = ((z.val : ℕ) : R) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact map_natCast ψ _

theorem val_toZModPow_sub_mem {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {m n : ℕ} (h : m ≤ n)
    (x : ℤ_[p]) :
    ((PadicInt.toZModPow n x).val : O) - ((PadicInt.toZModPow m x).val : O) ∈
      Ideal.span {(p : O) ^ m} := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero _ hp⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp⟩
  have h1 : (((PadicInt.toZModPow n x).val : ℕ) : ZMod (p ^ m)) =
      (((PadicInt.toZModPow m x).val : ℕ) : ZMod (p ^ m)) := by
    rw [ZMod.natCast_val, ZMod.natCast_zmod_val, PadicInt.cast_toZModPow m n h]
  rw [ZMod.natCast_eq_natCast_iff] at h1
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd.1 h1.symm)
  rw [Ideal.mem_span_singleton]
  refine ⟨(c : O), ?_⟩
  have := congrArg (fun t : ℤ => (t : O)) hc
  push_cast at this
  exact this

end GlobalTheory.ZpHomAdic

namespace GlobalTheory.ZpHomAdic
open IsLocalRing

noncomputable def zmodToQuot (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (hp : (p : O) ∈ maximalIdeal O) (n : ℕ) : ZMod (p ^ n) →+* O ⧸ maximalIdeal O ^ n :=
  (Ideal.Quotient.lift (Ideal.span {((p ^ n : ℕ) : ℤ)}) (Int.castRingHom _) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_natCast, Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk (maximalIdeal O ^ n)) p,
      ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hp n), mul_zero])).comp
    (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom

theorem exists_ringHom_padicInt {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] (hT : IsTopologicalRing O)
    (_hC : CompactSpace O) (_hH : T2Space O) (hA : IsAdic (maximalIdeal O))
    (hp : (p : O) ∈ maximalIdeal O) :
    ∃ ι : ℤ_[p] →+* O, ∀ (x : ℤ_[p]) (k : ℕ),
      ι x - ((PadicInt.toZModPow k x).val : O) ∈ Ideal.span {(p : O) ^ k} := by
  haveI := hT
  haveI : IsAdicComplete (maximalIdeal O) O :=
    { toIsHausdorff := isHausdorff_dvr, toIsPrecomplete := isPrecomplete_of_compact hA }
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI hNZ : ∀ n, NeZero (p ^ n) := fun n => ⟨pow_ne_zero _ hp0⟩
  let f : (n : ℕ) → ℤ_[p] →+* O ⧸ maximalIdeal O ^ n := fun n =>
    (zmodToQuot p O hp n).comp (PadicInt.toZModPow n)
  have hfx : ∀ n x, f n x = Ideal.Quotient.mk _ ((PadicInt.toZModPow n x).val : O) := by
    intro n x
    show zmodToQuot p O hp n _ = _
    rw [ringHom_zmod_apply, map_natCast]
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal O) hle).comp (f n) = f m := by
    intro m n hle
    ext x
    rw [RingHom.comp_apply, hfx, hfx, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
    exact Ideal.span_singleton_le_iff_mem _ |>.2 (Ideal.pow_mem_pow hp m)
      (val_toZModPow_sub_mem hle x)
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal O) f hf, fun x k => ?_⟩
  set ι := IsAdicComplete.liftRingHom (maximalIdeal O) f hf
  have hι : ∀ n, ι x - ((PadicInt.toZModPow n x).val : O) ∈ maximalIdeal O ^ n := by
    intro n
    rw [← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom, hfx]
  set J : Ideal O := Ideal.span {(p : O) ^ k}
  rw [← Submodule.Quotient.mk_eq_zero (p := J), ← Submodule.mem_bot O,
    ← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := O ⧸ J) (maximalIdeal O)
      (maximalIdeal.isMaximal O).ne_top, Submodule.mem_iInf]
  intro n
  have hle : maximalIdeal O ^ max n k • (⊤ : Submodule O (O ⧸ J)) ≤ maximalIdeal O ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_left n k))
  refine hle ?_
  have hsplit : ι x - ((PadicInt.toZModPow k x).val : O) =
      (ι x - ((PadicInt.toZModPow (max n k) x).val : O)) +
      (((PadicInt.toZModPow (max n k) x).val : O) - ((PadicInt.toZModPow k x).val : O)) := by ring
  rw [hsplit, Submodule.Quotient.mk_add,
    (Submodule.Quotient.mk_eq_zero J).2 (val_toZModPow_sub_mem (le_max_right n k) x), add_zero,
    ← mul_one (ι x - _), ← smul_eq_mul, Submodule.Quotient.mk_smul]
  exact Submodule.smul_mem_smul (hι _) Submodule.mem_top

theorem zp_ringHom : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → ∃ ι : ℤ_[p] →+* O, ∀ (x : ℤ_[p]) (k : ℕ), ι x - ((PadicInt.toZModPow k x).val : O) ∈ Ideal.span {(p : O) ^ k} :=
  fun hT hC hH hA hp => exists_ringHom_padicInt hT hC hH hA hp

end GlobalTheory.ZpHomAdic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPreimageInvertedPrimeBreuilOfExactTriple
section
noncomputable section

namespace GlobalTheory.BK.ExtExact

open PowerSeries GlobalTheory.BK Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] {ι κ μ : Type} [Fintype ι]
  [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}

theorem exists_pow_of_coker (G : Hom Q T) (h : IsFiniteLength (A O K) G.coker) :
    ∃ n : ℕ, ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y := by
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isFiniteLength (l : A O K)
    (isUnit_one_sub_mul_l l) _ h
  refine ⟨n, fun y hy => ?_⟩
  have h1 := hn (Submodule.Quotient.mk ⟨y, hy⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  change _ ∈ (G.imM).comap T.M.subtype at h1
  rw [Submodule.mem_comap, Hom.imM, Submodule.mem_map] at h1
  obtain ⟨x, hx, hxy⟩ := h1
  refine ⟨x, hx, ?_⟩
  rw [LinearMap.restrictScalars_apply] at hxy
  rw [hxy]
  ext τ i
  simp [Algebra.smul_def]


open IntegralLeftInverseExactTriple in
theorem exists_split (F : Hom P Q) (G : Hom Q T) (hFG : IsExactTriple F G) (n : ℕ)
    (hG : ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y) (τ : ZMod a) :
    ∃ (W : Matrix ι κ K⟦X⟧) (Xm : Matrix κ μ K⟦X⟧), (∀ i k, W i k ∈ A O K) ∧
      (∀ k j, Xm k j ∈ A O K) ∧
      F.mat τ * W + Xm * G.mat τ = (l : K) ^ n • (1 : Matrix κ κ K⟦X⟧) := by
  have h1 : ∀ j : μ, ∃ x ∈ Q.M, G.app x = ((l : K) ^ n) • (Pi.single τ (Pi.single j 1) : Vec K a μ) :=
    fun j => hG _ (mem_M_single T τ _ fun i => by
      by_cases h : i = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
  choose x hxM hx using h1
  let Xm : Matrix κ μ K⟦X⟧ := Matrix.of fun k j => x j τ k
  have hXA : ∀ k j, Xm k j ∈ A O K := fun k j => mem_vecs.1 (mem_tot.1 (hxM j) τ) k
  have hGX : G.mat τ * Xm = ((l : K) ^ n) • (1 : Matrix μ μ K⟦X⟧) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hx j) τ) i
    rw [Hom.app_apply, Pi.smul_apply, Pi.single_eq_same] at this
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simpa [Matrix.mulVec, dotProduct, Xm, Pi.single_apply, eq_comm] using this
  let Z : Matrix κ κ K⟦X⟧ := ((l : K) ^ n) • (1 : Matrix κ κ K⟦X⟧) - Xm * G.mat τ
  have hZA : ∀ k k', Z k k' ∈ A O K := fun k k' => sub_mem (smul_one_mem κ n k k')
    (Subalgebra.sum_mem _ fun j _ => mul_mem (hXA _ _) (G.mem _ _ _))
  have hGZ : G.mat τ * Z = 0 := by
    simp only [Z, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hGX,
      Matrix.smul_mul, Matrix.one_mul, sub_self]
  have h2 : ∀ k : κ, ∃ w ∈ P.M, F.app w = Pi.single τ (fun k' => Z k' k) := by
    intro k
    have hm := mem_M_single Q τ (fun k' => Z k' k) fun k' => hZA k' k
    have hz : G.mat τ *ᵥ (fun k' => Z k' k) = 0 := by
      funext i
      have := congrFun (congrFun hGZ i) k
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    obtain ⟨w, hw, h⟩ := (hFG.exact _ hm).1 (by rw [app_single, hz, Pi.single_zero])
    exact ⟨w, hw, h⟩
  choose w hwM hw using h2
  let W : Matrix ι κ K⟦X⟧ := Matrix.of fun i k => w k τ i
  have hWA : ∀ i k, W i k ∈ A O K := fun i k => mem_vecs.1 (mem_tot.1 (hwM k) τ) i
  have hFW : F.mat τ * W = Z := by
    refine Matrix.ext fun i k => ?_
    have := congrFun (congrFun (hw k) τ) i
    rw [Hom.app_apply, Pi.single_eq_same] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
  refine ⟨W, Xm, hWA, hXA, ?_⟩
  rw [hFW, sub_add_cancel]

theorem map_frob_smul_one (n : ℕ) :
    ((l : K) ^ n • (1 : Matrix κ κ K⟦X⟧)).map (frob K l) = (l : K) ^ n • (1 : Matrix κ κ K⟦X⟧) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.BK.ExtExact

namespace GlobalTheory.BK.ExtExact

open PowerSeries GlobalTheory.BK Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] {ι κ μ : Type} [Fintype ι]
  [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}

theorem exists_comp [NeZero e] (F : Hom P Q) (G : Hom Q T) (hFG : IsExactTriple F G)
    {v : Vec K a κ} (hv : v ∈ Q.ext (invL l (S O K e))) (hGv : G.app v = 0) (τ : ZMod a) :
    ∃ c' ∈ vecs ι (invL l (S O K e)), v τ = F.mat τ *ᵥ (P.mx τ *ᵥ c') := by
  obtain ⟨n, hn⟩ := exists_pow_of_coker G hFG.finiteLength
  have hAB : ∀ f ∈ A O K, f ∈ invL l (S O K e) := fun f hf => le_away _ _ (A_le_S l e hf)
  obtain ⟨c, hc, hvc⟩ := Q.mem_extc.1 (mem_tot.1 hv τ)
  obtain ⟨W, Xm, hWA, -, hsplit⟩ := exists_split F G hFG n hn (τ - 1)
  have hGc : (G.mat (τ - 1)).map (frob K l) *ᵥ c = 0 := by
    have h1 := congrFun hGv τ
    rw [Pi.zero_apply, Hom.app_apply, hvc, Matrix.mulVec_mulVec, G.comm,
      ← Matrix.mulVec_mulVec] at h1
    have h2 : (T.mxInv τ * T.mx τ) *ᵥ ((G.mat (τ - 1)).map (frob K l) *ᵥ c) = 0 := by
      rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
    rwa [T.mxInv_mul_mx, Matrix.one_mulVec] at h2
  have hs : (F.mat (τ - 1)).map (frob K l) * W.map (frob K l) +
      Xm.map (frob K l) * (G.mat (τ - 1)).map (frob K l) = (l : K) ^ n • (1 : Matrix κ κ K⟦X⟧) := by
    have : (F.mat (τ - 1) * W + Xm * G.mat (τ - 1)).map (frob K l).toRingHom =
        ((l : K) ^ n • (1 : Matrix κ κ K⟦X⟧)).map (frob K l).toRingHom := by rw [hsplit]
    rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul] at this
    rw [← map_frob_smul_one]
    exact this
  have hc2 : (l : K) ^ n • c = (F.mat (τ - 1)).map (frob K l) *ᵥ (W.map (frob K l) *ᵥ c) := by
    have := congrArg (· *ᵥ c) hs
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGc, Matrix.mulVec_zero,
      add_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    exact this.symm
  refine ⟨((l : K) ^ n)⁻¹ • (W.map (frob K l) *ᵥ c), fun i => ?_, ?_⟩
  · rw [Pi.smul_apply, PowerSeries.smul_eq_C_mul]
    refine mul_mem (HasK.C_mem _) (Subalgebra.sum_mem _ fun k _ => mul_mem ?_ (hc k))
    exact hAB _ (frob_mem_A l (hWA i k))
  · rw [hvc, Matrix.mulVec_mulVec, F.comm, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, ← hc2,
      inv_smul_smul₀ (pow_ne_zero _ (l_ne_zero l))]

end GlobalTheory.BK.ExtExact


open PowerSeries GlobalTheory.BK Matrix in
theorem GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NeZero e]
    [NormedAlgebra ℚ_[l] K] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ)
    (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G →
    ∀ v ∈ Q.ext (invL l (S O K e)), G.app v = 0 → ∃ w ∈ P.ext (invL l (S O K e)), F.app w = v := by
  intro O K _ _ _ _ _ l e a _ _ _ ι κ μ _ _ _ _ _ _ P Q T F G hFG v hv hGv
  choose c' hc' hvc' using fun τ => ExtExact.exists_comp F G hFG hv hGv τ
  refine ⟨fun τ => P.mx τ *ᵥ c' τ, mem_tot.2 fun τ => P.mem_extc.2 ⟨_, hc' τ, rfl⟩, ?_⟩
  funext τ
  rw [Hom.app_apply]
  exact (hvc' τ).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsVariablePowSmulEqZeroOfFiniteLength
section
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.UPow

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem isUnit_one_add_mul_uIn (f : A O K) : IsUnit (1 + f * uIn (A O K)) := by
  set g := (equivA O K).symm (1 + f * uIn (A O K))
  have hg : equivA O K g = 1 + f * uIn (A O K) := by simp [g]
  have hc : constantCoeff g = 1 := by
    apply IsUnitBall.inj (O := O) (K := K)
    have h1 := congrArg (fun x : A O K => constantCoeff (x : K⟦X⟧)) hg
    simp only [coe_equivA] at h1
    rw [map_one]
    have h2 : algebraMap O K (constantCoeff g) = constantCoeff ((PowerSeries.map (algebraMap O K)) g) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_map]
    rw [h2, h1]
    simp
  have hu : IsUnit g := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hc]
    exact isUnit_one
  rw [← hg]
  exact hu.map (equivA O K)

theorem exists_uIn_pow_smul_eq_zero : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (M : Type) [AddCommGroup M] [Module (A O K) M], IsFiniteLength (A O K) M →
    ∃ n : ℕ, ∀ x : M, (uIn (A O K)) ^ n • x = 0 := by
  intro O K _ _ _ _ _ M _ _ hM
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hM
  set I : Ideal (A O K) := Ideal.span {uIn (A O K)}
  let F : ℕ →o (Submodule (A O K) M)ᵒᵈ :=
    ⟨fun k => OrderDual.toDual (I ^ k • (⊤ : Submodule (A O K) M)), fun i j hij =>
      Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes F
  have hstab : I ^ n • (⊤ : Submodule (A O K) M) = I • (I ^ n • (⊤ : Submodule (A O K) M)) := by
    have : I ^ n • (⊤ : Submodule (A O K) M) = I ^ (n + 1) • (⊤ : Submodule (A O K) M) :=
      OrderDual.toDual_inj.1 (hn (n + 1) (Nat.le_succ n))
    rw [← Submodule.mul_smul, ← pow_succ', ← this]
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
    (I ^ n • (⊤ : Submodule (A O K) M)) (IsNoetherian.noetherian _) hstab.le
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1 hr
  have hru : IsUnit r := by
    have : r = 1 + f * uIn (A O K) := by rw [hf]; ring
    rw [this]
    exact isUnit_one_add_mul_uIn f
  refine ⟨n, fun x => ?_⟩
  have hmem : (uIn (A O K)) ^ n • x ∈ I ^ n • (⊤ : Submodule (A O K) M) :=
    Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) trivial
  have h0 := hr0 _ hmem
  obtain ⟨v, rfl⟩ := hru
  have := congrArg (fun y => ((v⁻¹ : (A O K)ˣ) : A O K) • y) h0
  simpa [smul_smul] using this

end GlobalTheory.UPow
end

