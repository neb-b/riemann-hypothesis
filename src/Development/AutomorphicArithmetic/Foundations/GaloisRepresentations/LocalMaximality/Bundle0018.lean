module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.FixZOf
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.fixZ_of :
    ValBasic → RYBasic → FixZ := by
  intro hV hR F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A h e he
  have hmem : ∀ b ∈ rB ℂ K (xv x) {0}, algebraMap K K' b ∈ rB ℂ K' (xv x) {0} :=
    fun b hb => ((hR F K K' d x j2 h.toY0).2.2.2.1 {0} b hb).1
  let ι : rB ℂ K (xv x) {0} →ₐ[ℂ] rB ℂ K' (xv x) {0} :=
    ((IsScalarTower.toAlgHom ℂ K K').comp (rB ℂ K (xv x) {0}).val).codRestrict _ fun b => hmem b b.2
  have hι : ∀ (b : K) (hb : b ∈ rB ℂ K (xv x) {0}), (e.1.comp ι) ⟨b, hb⟩ = e.1 ⟨_, hmem b hb⟩ :=
    fun _ _ => rfl
  refine ⟨⟨e.1.comp ι, fun j => ?_⟩, ?_⟩
  · rw [hι]
    refine Eq.trans ?_ (e.2 j)
    congr 2
    exact (IsScalarTower.algebraMap_apply F K K' _).symm
  rintro v c ⟨b, hb, hbv, hzb, hz⟩
  rw [hι] at hzb
  rw [hι, hι] at hz
  have h1b := hmem b hb
  have h1bv := hmem _ hbv
  constructor
  · have hm : algebraMap K K' b * algebraMap K K' v ∈ rB ℂ K' (xv x) {0} := by
      rw [← map_mul]; exact h1bv
    refine ⟨_, h1b, hm, hzb, ?_⟩
    rw [← hz]
    congr 2
    exact (map_mul _ _ _).symm
  · have fix := (h.fx e).1 he
    obtain ⟨-, ⟨ev, hev⟩, -, hinv⟩ := hV K' (rB ℂ K' (xv x) {0}) e.1
    have v1 := fix b hb h1b
    have v2 := fix _ hbv h1bv
    obtain ⟨m1, hm1⟩ := (hev _ _).1 v1
    obtain ⟨m2, hm2⟩ := (hev _ _).1 v2
    obtain ⟨hne, hi⟩ := hinv _ _ v1 hzb
    have hv : j2 v = (j2 b)⁻¹ * j2 (b * v) := by
      rw [map_mul, inv_mul_cancel_left₀ hne]
    have hl : j2 v ∈ loc (rB ℂ K' (xv x) {0}) e.1 := by
      rw [hv]; exact mul_mem hi m2
    refine (hev _ _).2 ⟨hl, ?_⟩
    have hmul : (⟨j2 b, m1⟩ : loc (rB ℂ K' (xv x) {0}) e.1) * ⟨j2 v, hl⟩ = ⟨j2 (b * v), m2⟩ :=
      Subtype.ext (map_mul j2 b v).symm
    have := congrArg ev hmul
    rw [map_mul, hm1, hm2, hz] at this
    exact mul_left_cancel₀ hzb this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.IntegralClosureFiniteGenerated
section
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system


open scoped IntermediateField.algebraAdjoinAdjoin in
private theorem tb_F {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) :
    IsTranscendenceBasis ℂ (fun j : Fin d => x j.succ / x 0) := by
  refine pd.indep.isTranscendenceBasis_iff_isAlgebraic.mpr ⟨fun a => ?_⟩
  refine (IsFractionRing.isAlgebraic_iff (Algebra.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0))
    (IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0)) F).mpr ?_
  have ha : a ∈ IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0) := by
    rw [pd.gen]; trivial
  exact isAlgebraic_algebraMap (⟨a, ha⟩ : IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0))

private theorem algHom_finite_of_proper {F K L : Type} [Field F] [Field K] [Field L] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ L]
    [Algebra F K] [IsScalarTower ℂ F K] [Algebra F L] [IsScalarTower ℂ F L] {d : ℕ} {x : Fin (d + 1) → F}
    (pd : IsPd ℂ x) [FiniteDimensional F K] [FiniteDimensional F L] (j2 : K →ₐ[ℂ] L) :
    j2.toRingHom.Finite := by
  have hF := tb_F pd
  set t : Fin d → F := fun j => x j.succ / x 0 with ht
  have hL : IsTranscendenceBasis ℂ (algebraMap F L ∘ t) := hF.algebraMap_comp
  have hK : IsTranscendenceBasis ℂ (algebraMap F K ∘ t) := hF.algebraMap_comp
  letI : Algebra K L := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  have hw : AlgebraicIndependent ℂ (algebraMap K L ∘ (algebraMap F K ∘ t)) :=
    hK.1.map' (f := IsScalarTower.toAlgHom ℂ K L) (algebraMap K L).injective
  have hwb : IsTranscendenceBasis ℂ (algebraMap K L ∘ (algebraMap F K ∘ t)) :=
    hw.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [← hL.cardinalMk_eq_trdeg])
  have halg : Algebra.IsAlgebraic K L := hwb.isAlgebraic_iff.2 fun i => isAlgebraic_algebraMap _
  obtain ⟨s, hs⟩ := (Module.finite_def (R := F) (M := L)).1 inferInstance
  let S : Set L := (s : Set L) ∪ Set.range (algebraMap F L ∘ t)
  have hSfin : S.Finite := s.finite_toSet.union (Set.finite_range _)
  haveI : Finite S := hSfin
  have htop : IntermediateField.adjoin K S = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    let P : IntermediateField ℂ L := (IntermediateField.adjoin K S).restrictScalars ℂ
    have hP : ∀ f : F, algebraMap F L f ∈ P := by
      have hle : IntermediateField.adjoin ℂ (Set.range t) ≤ P.comap (IsScalarTower.toAlgHom ℂ F L) := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨j, rfl⟩
        exact IntermediateField.subset_adjoin K S (Or.inr ⟨j, rfl⟩)
      rw [pd.gen] at hle
      exact fun f => hle (IntermediateField.mem_top)
    have hy : y ∈ Submodule.span F (s : Set L) := by rw [hs]; trivial
    induction hy using Submodule.span_induction with
    | mem z hz => exact IntermediateField.subset_adjoin K S (Or.inl hz)
    | zero => exact zero_mem _
    | add a c _ _ ha hc => exact add_mem ha hc
    | smul r a _ ha =>
      rw [Algebra.smul_def]
      exact mul_mem (hP r) ha
  haveI : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral
  rw [htop] at this
  change Module.Finite K L
  exact (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv.finiteDimensional

private theorem fg_rB {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) [FiniteDimensional F L]
    (J : Finset (Fin (d + 1))) : (rB ℂ L x J).FG := by
  rcases J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · have hbot : rB ℂ L x ∅ = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      haveI : Algebra.IsIntegral ℂ (rA ℂ x ∅) := Algebra.IsIntegral.adjoin (by simp)
      have h : IsIntegral ℂ y := isIntegral_trans (A := rA ℂ x ∅) y hy
      have := minpoly.mem_range_of_degree_eq_one ℂ y
        (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible h))
      exact Algebra.mem_bot.2 this
    rw [hbot]
    exact Subalgebra.fg_bot
  · haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℂ F).injective
    haveI : IsFractionRing (rA ℂ x J) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x pd J ⟨i, hi⟩).1
    haveI : IsNoetherianRing (rA ℂ x J) := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x pd J ⟨i, hi⟩).2
    haveI := rA_isIntegrallyClosed pd hi
    set_option synthInstance.maxHeartbeats 200000 in
      haveI : Module.Finite (rA ℂ x J) (integralClosure (rA ℂ x J) L) :=
        IsIntegralClosure.finite (rA ℂ x J) F L (integralClosure (rA ℂ x J) L)
    have hfg : (rA ℂ x J).FG := by
      refine Subalgebra.fg_def.2 ⟨_, ?_, rfl⟩
      refine ((J.finite_toSet.prod (Set.finite_univ (α := Fin (d + 1)))).image
        fun p => x p.2 / x p.1).subset ?_
      rintro _ ⟨i', hi', j, rfl⟩
      exact ⟨(i', j), ⟨hi', trivial⟩, rfl⟩
    haveI : Algebra.FiniteType ℂ (rA ℂ x J) := (Subalgebra.fg_iff_finiteType _).1 hfg
    set_option synthInstance.maxHeartbeats 200000 in
      have hft : Algebra.FiniteType ℂ (integralClosure (rA ℂ x J) L) :=
        Algebra.FiniteType.trans (S := rA ℂ x J) inferInstance inferInstance
    exact (Subalgebra.fg_iff_finiteType (rB ℂ L x J)).2 hft

private theorem integralClosure_finiteGenerated {F K L : Type} [Field F] [Field K] [Field L] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ L]
    [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) [FiniteDimensional F K]
    (j2 : K →ₐ[ℂ] L) (hf : j2.toRingHom.Finite) (J : Finset (Fin (d + 1))) : (R2 x j2 J).FG := by
  letI : Algebra K L := j2.toRingHom.toAlgebra
  letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  haveI : IsScalarTower ℂ F L := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap ℂ L c = algebraMap K L (algebraMap F K (algebraMap ℂ F c))
    rw [← IsScalarTower.algebraMap_apply ℂ F K c]
    exact (j2.commutes c).symm
  haveI : Module.Finite K L := hf
  haveI : FiniteDimensional F L := Module.Finite.trans K L
  let A := rA ℂ x J
  let B := (rB ℂ K x J).map j2
  let φ : A →+* B :=
    { toFun := fun a => ⟨algebraMap K L (algebraMap F K a),
        Subalgebra.mem_map.2 ⟨algebraMap F K a, (integralClosure A K).algebraMap_mem a, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  letI : Algebra A B := φ.toAlgebra
  haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral A B := ⟨fun b => by
    obtain ⟨c, hc, hb⟩ := Subalgebra.mem_map.1 b.2
    have h1 : IsIntegral A (algebraMap K L c) := IsIntegral.algebraMap hc
    have h2 : algebraMap B L b = algebraMap K L c := hb.symm
    rw [← h2] at h1
    exact (isIntegral_algebraMap_iff ).1 h1⟩
  have e : R2 x j2 J = rB ℂ L x J := by
    ext y
    constructor
    · intro hy
      exact isIntegral_trans (A := B) y hy
    · intro hy
      exact IsIntegral.tower_top (A := B) hy
  rw [e]
  exact fg_rB pd J

theorem rYFT_of :
    RYFT := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h I J hI
  have pd := h.covZ.pd
  haveI := h.covZ.fin
  haveI := h.covY.fin
  have h1 : (rB ℂ K' (xv x) I).FG := fg_rB h.covY.pd I
  have h2 : (R2 (xv x) j2 J).FG := integralClosure_finiteGenerated pd j2 (algHom_finite_of_proper pd j2) J
  exact (Subalgebra.fg_iff_finiteType _).1 (h1.sup h2)

end UpperTheory.Gal.productCup_of_system

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PDtBasic
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

private theorem dt_eq (b : Module.Basis (Fin d) K Ω[K⁄ℂ]) (hb : ∀ j, b j = D ℂ K (tt K x j)) (S : Finset (Fin d)) :
    dtS K x S = b.ExteriorAlgebra S := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (rfl : S.card = S.card)]
  simp only [dtS, ExteriorAlgebra.ιMulti_family]
  congr 1
  ext a
  simp [hb, Set.powersetCard.ofFinEmbEquiv_symm_apply]

private theorem dt_univ : dtS K x Finset.univ = ExteriorAlgebra.ιMulti K d fun j => D ℂ K (tt K x j) := by
  have h : (Finset.univ : Finset (Fin d)).card = d := by simp
  have key : ∀ (n : ℕ) (hn : (Finset.univ : Finset (Fin d)).card = n) , n = d →
      (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (tt K x ((Finset.univ : Finset (Fin d)).orderEmbOfFin hn a))) =
      ExteriorAlgebra.ιMulti K d fun j => D ℂ K (tt K x j) := by
    intro n hn e
    subst e
    congr 1
    ext a
    have : (Finset.univ : Finset (Fin n)).orderEmbOfFin hn a = a := by
      have := Finset.orderEmbOfFin_unique' (s := (Finset.univ : Finset (Fin n))) hn (f := (OrderIso.refl (Fin n)).toOrderEmbedding) (by simp)
      rw [← this]; rfl
    rw [this]
  exact key _ rfl h

end

theorem UpperTheory.Gal.productCup_of_system.dtBasic_of :
    DtBasic := by
  intro F K _ _ _ _ _ _ d x hc τ hτ
  obtain ⟨b0, hb0⟩ := hc.exists_basis
  have hb : ∀ j, b0 j = D ℂ K (tt K x j) := hb0
  have hfun : dtS K x = b0.ExteriorAlgebra := funext (dt_eq x b0 hb)
  have hprod : algebraMap F K (omG x 0) = ∏ l, tt K x l := by
    unfold omG
    rw [Fin.prod_univ_succ, div_self (x 0).ne_zero, one_mul, map_prod]
    rfl
  refine ⟨?_, ?_, ?_, hprod, ?_⟩
  · rw [hfun]
    exact b0.ExteriorAlgebra.linearIndependent
  · intro S
    refine Submodule.subset_span ⟨1, one_mem _, fun a => tt K x (S.orderEmbOfFin rfl a),
      fun j => tco_mem ℂ K (xv x) _, ?_⟩
    rw [one_smul]
    rfl
  · have hne : ∀ j, tt K x j ≠ 0 := fun j =>
      (map_ne_zero _).2 (div_ne_zero (x j.succ).ne_zero (x 0).ne_zero)
    have hv : vol0 ℂ K (xv x) = (∏ j, (tt K x j)⁻¹) • ExteriorAlgebra.ιMulti K d fun j => D ℂ K (tt K x j) := by
      rw [← AlternatingMap.map_smul_univ]
      rfl
    rw [dt_univ, hprod, hv, smul_smul, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl fun j _ => mul_inv_cancel₀ (hne j), Finset.prod_const_one, one_smul]
  · have hd : ∀ S : Finset (Fin d), Disjoint (Sᶜ) S := fun S => disjoint_compl_left
    refine ⟨fun S => (Set.powersetCard.permOfDisjoint
      (s := (⟨Sᶜ, rfl⟩ : Set.powersetCard (Fin d) Sᶜ.card))
      (t := (⟨S, rfl⟩ : Set.powersetCard (Fin d) S.card)) (hd S)).sign, fun U S hUS => ?_⟩
    rw [hfun]
    split_ifs with h
    · subst h
      have e := ExteriorAlgebra.basis_mul_of_disjoint b0
        (⟨Sᶜ, rfl⟩ : Set.powersetCard (Fin d) Sᶜ.card) (⟨S, rfl⟩ : Set.powersetCard (Fin d) S.card) (hd S)
      have hu : ((Set.powersetCard.disjUnion (s := (⟨Sᶜ, rfl⟩ : Set.powersetCard (Fin d) Sᶜ.card))
          (t := (⟨S, rfl⟩ : Set.powersetCard (Fin d) S.card)) (hd S) : Set.powersetCard (Fin d) (Sᶜ.card + S.card)) : Finset (Fin d)) = Finset.univ := by
        ext i
        simp [Set.powersetCard.disjUnion]
      rw [hu] at e
      exact e
    · have hnd : ¬ Disjoint U S := by
        intro hUd
        apply h
        have hc2 : (U ∪ S).card = Fintype.card (Fin d) := by
          rw [Finset.card_union_of_disjoint hUd, hUS, Fintype.card_fin]
        have huniv : U ∪ S = Finset.univ := (Finset.card_eq_iff_eq_univ _).1 hc2
        ext i
        have := Finset.ext_iff.1 huniv i
        have h2 : i ∈ U → i ∉ S := fun a => Finset.disjoint_left.1 hUd a
        simp at this ⊢
        tauto
      exact ExteriorAlgebra.basis_mul_of_not_disjoint b0
        (⟨U, rfl⟩ : Set.powersetCard (Fin d) U.card) (⟨S, rfl⟩ : Set.powersetCard (Fin d) S.card) hnd
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PDtPull
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem alt_expand {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] {d q : ℕ} (f : M [⋀^Fin q]→ₗ[R] N) (a : Fin q → Fin d → R) (v : Fin d → M) :
    f (fun i => ∑ l, a i l • v l) =
      ∑ S : {S : Finset (Fin d) // S.card = q},
        (Matrix.of fun i j => a i (S.1.orderEmbOfFin S.2 j)).det •
          f (fun j => v (S.1.orderEmbOfFin S.2 j)) := by
  classical
  have h1 : f (fun i => ∑ l, a i l • v l) =
      ∑ φ : Fin q → Fin d, (∏ i, a i (φ i)) • f (fun i => v (φ i)) := by
    have h := f.toMultilinearMap.map_sum (fun i l => a i l • v l)
    refine h.trans (Finset.sum_congr rfl fun φ _ => ?_)
    exact f.toMultilinearMap.map_smul_univ _ _
  let e : {S : Finset (Fin d) // S.card = q} → Fin q → Fin d := fun S j => S.1.orderEmbOfFin S.2 j
  have he : ∀ S, Function.Injective (e S) := fun S => (S.1.orderEmbOfFin S.2).injective
  have hr : ∀ S, Set.range (e S) = S.1 := fun S => Finset.range_orderEmbOfFin S.1 S.2
  let Φ : (Σ _ : {S : Finset (Fin d) // S.card = q}, Equiv.Perm (Fin q)) →
      {φ : Fin q → Fin d // Function.Injective φ} :=
    fun p => ⟨e p.1 ∘ p.2, (he p.1).comp p.2.injective⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨S, σ⟩ ⟨S', σ'⟩ h
      have h' : e S ∘ σ = e S' ∘ σ' := congrArg Subtype.val h
      have hS : S = S' := by
        apply Subtype.ext
        apply Finset.coe_injective
        rw [← hr S, ← hr S', ← σ.surjective.range_comp (e S), ← σ'.surjective.range_comp (e S'), h']
      subst hS
      have : σ = σ' := by
        ext i
        exact congrArg _ (he S (congrFun h' i))
      rw [this]
    · rintro ⟨φ, hφ⟩
      have hc : (Finset.univ.image φ).card = q := by
        rw [Finset.card_image_of_injective _ hφ]; simp
      let S : {S : Finset (Fin d) // S.card = q} := ⟨_, hc⟩
      have hm : ∀ i, ∃ j, e S j = φ i := fun i => by
        have : φ i ∈ Set.range (e S) := by rw [hr]; simp [S]
        exact this
      choose s hs using hm
      have hsi : Function.Injective s := fun i i' h => hφ (by rw [← hs, ← hs, h])
      refine ⟨⟨S, Equiv.ofBijective s (Finite.injective_iff_bijective.1 hsi)⟩, ?_⟩
      apply Subtype.ext
      funext i
      exact hs i
  rw [h1, ← Fintype.sum_subtype_add_sum_subtype (fun φ : Fin q → Fin d => Function.Injective φ)]
  have h0 : ∑ φ : {φ : Fin q → Fin d // ¬ Function.Injective φ},
      (∏ i, a i (φ.1 i)) • f (fun i => v (φ.1 i)) = 0 := by
    refine Finset.sum_eq_zero fun φ _ => ?_
    have : ¬ Function.Injective (fun i => v (φ.1 i)) := fun h => φ.2 fun i i' hi => h (by simp [hi])
    rw [f.map_eq_zero_of_not_injective _ this, smul_zero]
  rw [h0, add_zero, ← hΦ.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Matrix.det_transpose, Matrix.det_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hp := f.map_perm (fun j => v (e S j)) σ
  have hp' : f (fun i => v (e S (σ i))) = Equiv.Perm.sign σ • f (fun j => v (e S j)) := hp
  change (∏ i, a i (e S (σ i))) • f (fun i => v (e S (σ i))) = _
  rw [hp']
  have hq : ∏ i, (Matrix.of fun i j => a i (S.1.orderEmbOfFin S.2 j)).transpose (σ i) i =
      ∏ i, a i (e S (σ i)) := by
    rfl
  rw [hq]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, e]

private theorem mapDR_iM (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] (n : ℕ) (v : Fin n → K) :
    mapDR ℂ K L (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (v a)) =
      ExteriorAlgebra.ιMulti L n fun a => D ℂ L (algebraMap K L (v a)) := by
  simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext a
  simp [mapDR, map1, KaehlerDifferential.map_D]

private theorem pullback_kahler_iMulti {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] (j2 : K →ₐ[ℂ] L)
    (n : ℕ) (v : Fin n → K) :
    pr2L j2 (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (v a)) =
      ExteriorAlgebra.ιMulti L n fun a => D ℂ L (j2 (v a)) := by
  letI : Algebra K L := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_iM K L n v

private theorem iM_cast {L : Type} [Field L] [Algebra ℂ L] {d : ℕ} (S : Finset (Fin d)) (q : ℕ)
    (h : S.card = q) (w : Fin d → Ω[L⁄ℂ]) :
    ExteriorAlgebra.ιMulti L q (fun j => w (S.orderEmbOfFin h j)) =
      ExteriorAlgebra.ιMulti L S.card (fun j => w (S.orderEmbOfFin rfl j)) := by
  subst h; rfl

theorem UpperTheory.Gal.productCup_of_system.dtPull_of :
    LocOne → ValBasic → DtPull := by
  intro hLO hVB F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY e he T
  refine ⟨?_, ?_⟩
  · refine (mapDR_iM K K' _ _).trans ?_
    unfold dtS
    congr 1
    funext a
    rw [tt, tt, IsScalarTower.algebraMap_apply F K K']
  · obtain ⟨hle, ⟨ev, hev⟩, hbv, -⟩ := hVB K' (rB ℂ K' (xv x) {0}) e.1
    have hLoc := hLO F K' d x hY.covY hY.red e
    have htB : ∀ l, tt K' x l ∈ rB ℂ K' (xv x) {0} := fun l => tco_mem ℂ K' (xv x) l
    have ht0 : ∀ l, ev ⟨tt K' x l, hle (htB l)⟩ = 0 := fun l => by
      obtain ⟨h, hh⟩ := (hev _ _).1 (hbv ⟨tt K' x l, htB l⟩)
      exact hh.trans (e.2 l)
    choose g hgv hgt using hY.tan e he
    have hg : ∀ m l, ∃ h : g m l ∈ loc (rB ℂ K' (xv x) {0}) e.1, ev ⟨g m l, h⟩ = A e m l :=
      fun m l => (hev _ _).1 (hgv m l)
    choose hgl hge using hg
    choose c hcl hcD using fun m l => hLoc (g m l) (hgl m l)
    let ah : Matrix (Fin d) (Fin d) (loc (rB ℂ K' (xv x) {0}) e.1) := fun m l =>
      ⟨g m l, hgl m l⟩ + ∑ l', ⟨tt K' x l', hle (htB l')⟩ * ⟨c m l' l, hcl m l' l⟩
    have hah : ∀ m l, (ah m l : K') = g m l + ∑ l', tt K' x l' * c m l' l := fun m l => by
      simp [ah]
    have hAh : ev.mapMatrix ah = A e := by
      ext m l
      change ev (⟨g m l, hgl m l⟩ + ∑ l', ⟨tt K' x l', hle (htB l')⟩ * ⟨c m l' l, hcl m l' l⟩) = A e m l
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, hge]
      simp only [map_mul, ht0, zero_mul, Finset.sum_const_zero, add_zero]
    have hD : ∀ m, D ℂ K' (j2 (tt K x m)) = ∑ l, (ah m l : K') • D ℂ K' (tt K' x l) := by
      intro m
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hgt m, map_sum]
      simp_rw [hah, add_smul, Finset.sum_add_distrib, Derivation.leibniz, hcD, Finset.smul_sum,
        Finset.sum_smul, smul_smul]
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm
    refine ⟨fun S => if hS : S.card = T.card then
      (((ah.submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin hS)).det :
        loc (rB ℂ K' (xv x) {0}) e.1) : K') else 0, ?_, ?_⟩
    · have h1 : pr2L j2 (dtS K x T) = ExteriorAlgebra.ιMulti K' T.card (fun a =>
          ∑ l, (ah (T.orderEmbOfFin rfl a) l : K') • D ℂ K' (tt K' x l)) := by
        unfold dtS
        rw [pullback_kahler_iMulti]
        congr 1
        funext a
        exact hD _
      rw [h1, alt_expand (ExteriorAlgebra.ιMulti K' T.card)
        (fun a l => (ah (T.orderEmbOfFin rfl a) l : K')) (fun l => D ℂ K' (tt K' x l)),
        Finset.sum_subtype (Finset.univ.powersetCard T.card) (p := fun S => S.card = T.card)
          (by simp [Finset.mem_powersetCard])]
      refine Finset.sum_congr rfl fun S _ => ?_
      simp only [dif_pos S.2]
      rw [iM_cast S.1 T.card S.2 (fun l => D ℂ K' (tt K' x l))]
      unfold dtS
      congr 1
      exact ((loc (rB ℂ K' (xv x) {0}) e.1).val.map_det
        (ah.submatrix (T.orderEmbOfFin rfl) (S.1.orderEmbOfFin S.2))).symm
    · intro S hS
      simp only [dif_pos hS]
      refine (hev _ _).2 ⟨SetLike.coe_mem _, ?_⟩
      change ev (ah.submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin hS)).det = _
      rw [AlgHom.map_det, ← hAh]
      rfl
end

