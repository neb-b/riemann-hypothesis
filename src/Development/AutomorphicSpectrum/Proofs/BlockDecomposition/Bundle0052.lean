module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0024
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedPolynomialSplitsStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolutely_closed_polynomial_splits : ∀ {S : Type} [CommRing S] , Aic (S := S) → ∀ P : Polynomial S, P.Monic → ∃ s : Multiset S, P = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  first | exact @GlobalTheory.CompanionTheory.MonicSplit.monic_splits | exact GlobalTheory.CompanionTheory.MonicSplit.monic_splits | (intros; apply GlobalTheory.CompanionTheory.MonicSplit.monic_splits <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyIntegrallyClosedOfNewtonStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolutely_integrally_closed_of_newton : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Step ϖ → (∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z) → Aic (S := S) := by
  first | exact @GlobalTheory.CompanionTheory.AicLimit.aic_of_step | exact GlobalTheory.CompanionTheory.AicLimit.aic_of_step | (intros; apply GlobalTheory.CompanionTheory.AicLimit.aic_of_step <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AltAlt
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.WpCoface

theorem alt_alt (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type)
    [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n))
    (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))) (hwp : ∀ n, IsWP (ι n))
    (hδ : ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) (n : ℕ) (z : K n) :
    alt (δ (n + 1)) (alt (δ n) z) = 0 := by
  have hrel : ∀ (j : Fin (n + 2)) (i : Fin (n + 1)),
      δ (n + 1) (j.succAbove i) (δ n (i.predAbove j) z) = δ (n + 1) j (δ n i z) := fun j i =>
    DFunLike.congr_fun (coface_rel A B K ι δ hwp hδ n j i) z
  have hexp : alt (δ (n + 1)) (alt (δ n) z) = ∑ p : Fin (n + 2) × Fin (n + 1),
      ((-1 : ℤ) ^ (p.1 : ℕ) * (-1 : ℤ) ^ (p.2 : ℕ)) • δ (n + 1) p.1 (δ n p.2 z) := by
    rw [Fintype.sum_prod_type]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum,
      map_zsmul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [hexp]
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ _
    dsimp only
    rw [hrel, GlobalTheory.CatH.DSq.sign_swap, neg_smul, add_neg_cancel]
  · rintro ⟨j, i⟩ _ _ h
    exact Fin.succAbove_ne j i (congrArg Prod.fst h)
  · intro _ _; exact Finset.mem_univ _
  · rintro ⟨j, i⟩ _
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

end GlobalTheory.CompanionTheory.WpCoface
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnalyticGermFiniteProjection
section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

namespace GlobalTheory.CompanionTheory.AnalyticGermSlice

theorem isAnalyticNear_zeros_inter {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ}
    (hX : IsAnalyticNear X w) {m : ℕ} (g : Fin m → (σ → ℂ) → ℂ)
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) Set.univ) :
    IsAnalyticNear {z | z ∈ X ∧ ∀ i, g i z = 0} w := by
  obtain ⟨N, k, f, hN, hwN, hf, hXN⟩ := hX
  refine ⟨N, k + m, Fin.append f g, hN, hwN, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left j => rw [Fin.append_left]; exact hf j
    | right j => rw [Fin.append_right]; exact (hg j).mono (Set.subset_univ N)
  · ext z
    have hz := Set.ext_iff.1 hXN z
    constructor
    · rintro ⟨⟨hzX, hg0⟩, hzN⟩
      refine ⟨hzN, (Fin.forall_fin_add _).2 ⟨fun j => ?_, fun j => ?_⟩⟩
      · rw [Fin.append_left]; exact (hz.1 ⟨hzX, hzN⟩).2 j
      · rw [Fin.append_right]; exact hg0 j
    · rintro ⟨hzN, hall⟩
      have h2 := (Fin.forall_fin_add _).1 hall
      refine ⟨⟨(hz.2 ⟨hzN, fun j => ?_⟩).1, fun j => ?_⟩, hzN⟩
      · have := h2.1 j
        rwa [Fin.append_left] at this
      · have := h2.2 j
        rwa [Fin.append_right] at this

private theorem exists_eventually_eq_zero_of_prod_analyticAt {n : ℕ} (a : ℂ) (f : Fin n → ℂ → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) a) (hP : ∀ᶠ t in 𝓝 a, ∏ i, f i t = 0) :
    ∃ i, ∀ᶠ t in 𝓝 a, f i t = 0 := by
  by_contra hcon
  have hcon' : ∀ i, ¬ ∀ᶠ t in 𝓝 a, f i t = 0 := fun i hi => hcon ⟨i, hi⟩
  have hne : ∀ i, ∀ᶠ t in 𝓝[≠] a, f i t ≠ 0 := fun i =>
    ((hf i).eventually_eq_zero_or_eventually_ne_zero).resolve_left (hcon' i)
  have hall : ∀ᶠ t in 𝓝[≠] a, ∀ i, f i t ≠ 0 := Filter.eventually_all.2 hne
  have hP' : ∀ᶠ t in 𝓝[≠] a, ∏ i, f i t = 0 := nhdsWithin_le_nhds hP
  obtain ⟨t, ht1, ht2⟩ := (hall.and hP').exists
  exact (Finset.prod_ne_zero_iff.2 fun i _ => ht1 i) ht2

theorem exists_irreducible_slice :
    FiniteGermProjectionOpenAt.Statement → GermFiniteProjection.Statement → AnalyticGermComponents.Statement → ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w → AccPt w (𝓟 X) → ∃ (Y W : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), W ∈ 𝓝 w ∧ Y ∩ W ⊆ X ∧ IsAnalyticNear Y w ∧ GermIrreducibleAt Y w ∧ (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) ∧ ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) → ∀ᶠ y in 𝓝 (A w), h y = 0 := by
  intro hFG hGF hAC σ _ X w hX hirr hacc
  obtain ⟨d, A, ⟨W0, hW0, hfib⟩, hdom⟩ := hGF σ X w hX hirr
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      obtain ⟨y, ⟨hyW, hyX⟩, hyw⟩ := (accPt_iff_nhds.1 hacc) W0 hW0
      exact absurd (hfib y ⟨hyX, hyW⟩ (Subsingleton.elim _ _)) hyw
    · exact h0
  let i0 : Fin d := ⟨0, hd⟩
  let g : Fin d → (σ → ℂ) → ℂ := fun j z => if j = i0 then 0 else A z j - A w j
  have hgan : ∀ j, AnalyticOnNhd ℂ (g j) Set.univ := by
    intro j
    by_cases hj : j = i0
    · simp only [g, hj, if_true]
      exact analyticOnNhd_const
    · simp only [g, hj, if_false]
      exact (((ContinuousLinearMap.proj j).comp A).analyticOnNhd _).sub analyticOnNhd_const
  let S : Set (σ → ℂ) := {z | z ∈ X ∧ ∀ j, g j z = 0}
  have hSan : IsAnalyticNear S w := isAnalyticNear_zeros_inter hX g hgan
  have hwS : w ∈ S := ⟨hirr.1, fun j => by by_cases hj : j = i0 <;> simp [g, hj]⟩
  obtain ⟨n, Y, hYi, W1, hW1, hYeq⟩ := hAC σ S w hSan hwS
  let A1 : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ) :=
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.proj i0).comp A
  have hA1 : ∀ z k, A1 z k = A z i0 := fun z k => rfl
  have hfibS : ∀ x ∈ S ∩ W0, A1 x = A1 w → x = w := by
    rintro x ⟨⟨hxX, hxg⟩, hxW⟩ hx
    refine hfib x ⟨hxX, hxW⟩ (funext fun j => ?_)
    by_cases hj : j = i0
    · subst hj
      have := congrFun hx 0
      simpa [hA1] using this
    · have := hxg j
      simp only [g, hj, if_false, sub_eq_zero] at this
      exact this
  have himg : ∀ V ∈ 𝓝 w, A1 '' (S ∩ V) ∈ 𝓝 (A1 w) := by
    intro V hV
    have hbig := hFG σ X w d A hX ⟨W0, hW0, hfib⟩ hdom V hV
    let ψ : (Fin 1 → ℂ) → (Fin d → ℂ) := fun y j => if j = i0 then y 0 else A w j
    have hψc : Continuous ψ := by
      refine continuous_pi fun j => ?_
      by_cases hj : j = i0
      · simp only [ψ, hj, if_true]
        exact continuous_apply 0
      · simp only [ψ, hj, if_false]
        exact continuous_const
    have hψw : ψ (A1 w) = A w := by
      funext j
      by_cases hj : j = i0
      · subst hj
        simp [ψ, hA1]
      · simp [ψ, hj]
    have hpre : ψ ⁻¹' (A '' (X ∩ V)) ∈ 𝓝 (A1 w) := by
      apply hψc.continuousAt.preimage_mem_nhds
      rw [hψw]
      exact hbig
    refine Filter.mem_of_superset hpre ?_
    rintro y ⟨x, ⟨hxX, hxV⟩, hxy⟩
    refine ⟨x, ⟨⟨hxX, fun j => ?_⟩, hxV⟩, ?_⟩
    · by_cases hj : j = i0
      · simp [g, hj]
      · have := congrFun hxy j
        simp only [ψ, hj, if_false] at this
        simp [g, hj, this]
    · funext k
      have := congrFun hxy i0
      simp only [ψ, if_true] at this
      rw [hA1, this, Subsingleton.elim k 0]
  have hdomi : ∃ i, ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A1 w) →
      (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A1 z) = 0) → ∀ᶠ y in 𝓝 (A1 w), h y = 0 := by
    by_contra hcon
    have hcon' : ∀ i, ∃ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A1 w) ∧
        (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A1 z) = 0) ∧ ¬ ∀ᶠ y in 𝓝 (A1 w), h y = 0 := by
      intro i
      by_contra hi
      exact hcon ⟨i, fun h ha hz => by
        by_contra hy
        exact hi ⟨h, ha, hz, hy⟩⟩
    choose h hha hhz hhnz using hcon'
    let c : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ
    let a : ℂ := A w i0
    have hca : c a = A1 w := by
      funext k
      rfl
    have hback : ∀ φ : (Fin 1 → ℂ) → ℂ, (∀ᶠ t in 𝓝 a, φ (c t) = 0) → ∀ᶠ y in 𝓝 (A1 w), φ y = 0 := by
      intro φ hφ
      have hev : Tendsto (fun y : Fin 1 → ℂ => y 0) (𝓝 (A1 w)) (𝓝 a) :=
        (continuous_apply 0).tendsto' _ _ rfl
      filter_upwards [hev.eventually hφ] with y hy
      have hyc : c (y 0) = y := by
        funext k
        rw [Subsingleton.elim k 0]
        rfl
      rwa [hyc] at hy
    have hfan : ∀ i, AnalyticAt ℂ (fun t => h i (c t)) a := by
      intro i
      have h1 : AnalyticAt ℂ (h i) (c a) := by
        rw [hca]
        exact hha i
      exact h1.comp (c.analyticAt a)
    have hPz : ∀ᶠ t in 𝓝 a, ∏ i, h i (c t) = 0 := by
      have hV : ∀ᶠ z in 𝓝 w, ∀ i, z ∈ Y i → h i (A1 z) = 0 := Filter.eventually_all.2 hhz
      have hV' : {z | ∀ i, z ∈ Y i → h i (A1 z) = 0} ∩ W1 ∈ 𝓝 w := Filter.inter_mem hV hW1
      have hI := himg _ hV'
      have hy : ∀ᶠ y in 𝓝 (A1 w), ∏ i, h i y = 0 := by
        filter_upwards [hI] with y hy
        obtain ⟨x, ⟨hxS, hxV, hxW⟩, rfl⟩ := hy
        have hxU : x ∈ (⋃ i, Y i) ∩ W1 := by
          rw [← hYeq]
          exact ⟨hxS, hxW⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hxU.1
        exact Finset.prod_eq_zero (Finset.mem_univ i) (hxV i hi)
      have hev : Tendsto c (𝓝 a) (𝓝 (A1 w)) := by
        rw [← hca]
        exact c.continuous.tendsto a
      exact hev.eventually hy
    obtain ⟨i, hi⟩ := exists_eventually_eq_zero_of_prod_analyticAt a (fun i t => h i (c t)) hfan hPz
    exact hhnz i (hback (h i) hi)
  obtain ⟨i, hi⟩ := hdomi
  refine ⟨Y i, W1, A1, hW1, ?_, (hYi i).1, (hYi i).2, ⟨W1 ∩ W0, Filter.inter_mem hW1 hW0, ?_⟩, hi⟩
  · rintro z ⟨hzY, hzW⟩
    have hzU : z ∈ (⋃ j, Y j) ∩ W1 := ⟨Set.mem_iUnion.2 ⟨i, hzY⟩, hzW⟩
    rw [← hYeq] at hzU
    exact hzU.1.1
  · rintro x ⟨hxY, hxW1, hxW0⟩ hx
    have hxU : x ∈ (⋃ j, Y j) ∩ W1 := ⟨Set.mem_iUnion.2 ⟨i, hxY⟩, hxW1⟩
    rw [← hYeq] at hxU
    exact hfibS x ⟨hxU.1, hxW0⟩ hx

end GlobalTheory.CompanionTheory.AnalyticGermSlice
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorIntersectionCard
section
namespace GlobalTheory.CompanionTheory.PairCount

theorem card_comap_subtype {R X : Type} [Ring R] [AddCommGroup X] [Module R X]
    (p q : Submodule R X) :
    Nat.card ↥(q.comap p.subtype) = Nat.card ↥(p ⊓ q) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_sup_mul_card_inf {R X : Type} [Ring R] [AddCommGroup X] [Module R X] [Finite X]
    (I L : Submodule R X) :
    Nat.card ↥(I ⊔ L) * Nat.card ↥(I ⊓ L) = Nat.card ↥I * Nat.card ↥L := by
  have e := Nat.card_congr (LinearMap.quotientInfEquivSupQuotient I L).toEquiv
  have hq : I.comap I.subtype ⊓ L.comap I.subtype = L.comap I.subtype := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  rw [hq] at e
  have h1 := Submodule.card_eq_card_quotient_mul_card (L.comap I.subtype)
  have h2 := Submodule.card_eq_card_quotient_mul_card (L.comap (I ⊔ L).subtype)
  rw [card_comap_subtype] at h1 h2
  rw [inf_eq_right.2 (le_sup_right : L ≤ I ⊔ L)] at h2
  rw [h1, h2, e]
  ring

theorem bijective_of_injective (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) : Function.Bijective B := by
  have : Finite (X →ₗ[ZMod n] ZMod n) := Finite.of_injective _ DFunLike.coe_injective
  have hd : Nat.card (X →ₗ[ZMod n] ZMod n) = Nat.card X := GlobalTheory.ZModDual.card_dual_eq n X
  have hd' : Nat.card (Y →ₗ[ZMod n] ZMod n) = Nat.card Y := GlobalTheory.ZModDual.card_dual_eq n Y
  have : Finite (Y →ₗ[ZMod n] ZMod n) := Finite.of_injective _ DFunLike.coe_injective
  have h1 : Nat.card X ≤ Nat.card Y := hd' ▸ Nat.card_le_card_of_injective _ hB'
  exact hB.bijective_of_nat_card_le (hd ▸ h1)

theorem card_annihilator_mul_card (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) (U : Submodule (ZMod n) X) :
    Nat.card ↥(⨅ x ∈ U, LinearMap.ker (B.flip x)) * Nat.card ↥U = Nat.card X := by
  let e : Y ≃ (X →ₗ[ZMod n] ZMod n) :=
    Equiv.ofBijective B (bijective_of_injective n X Y B hB hB')
  have h1 : Nat.card ↥(⨅ x ∈ U, LinearMap.ker (B.flip x)) = Nat.card ↥U.dualAnnihilator := by
    refine Nat.card_congr (Equiv.subtypeEquiv e fun y => ?_)
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      Submodule.mem_dualAnnihilator]
    rfl
  have : Finite (X ⧸ U) := Finite.of_surjective _ (Submodule.mkQ_surjective U)
  have h2 : Nat.card ↥U.dualAnnihilator = Nat.card (X ⧸ U) := by
    rw [← Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator U).toEquiv]
    exact GlobalTheory.ZModDual.card_dual_eq n (X ⧸ U)
  rw [h1, h2]
  rw [mul_comm]
  exact (Submodule.card_eq_card_quotient_mul_card U).symm

theorem annihilator_inf (n : ℕ) (X Y : Type) [AddCommGroup X] [Module (ZMod n) X]
    [AddCommGroup Y] [Module (ZMod n) Y] (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n)
    (I L : Submodule (ZMod n) X) :
    (⨅ x ∈ I, LinearMap.ker (B.flip x)) ⊓ (⨅ x ∈ L, LinearMap.ker (B.flip x)) =
      ⨅ x ∈ I ⊔ L, LinearMap.ker (B.flip x) := by
  ext y
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
  refine ⟨fun h x hx => ?_, fun h => ⟨fun x hx => h x (Submodule.mem_sup_left hx),
    fun x hx => h x (Submodule.mem_sup_right hx)⟩⟩
  obtain ⟨i, hi, l, hl, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _), h.1 i hi, h.2 l hl, add_zero]

theorem card_annihilator_inf (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) (I L : Submodule (ZMod n) X) :
    Nat.card ↥((⨅ x ∈ I, LinearMap.ker (B.flip x)) ⊓ (⨅ x ∈ L, LinearMap.ker (B.flip x))) *
        Nat.card ↥I * Nat.card ↥L = Nat.card X * Nat.card ↥(I ⊓ L) := by
  rw [annihilator_inf, mul_assoc, ← card_sup_mul_card_inf, ← mul_assoc,
    card_annihilator_mul_card n X Y B hB hB']

end GlobalTheory.CompanionTheory.PairCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralContinuousStatement
section
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_orbital_integral_continuous : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ)
  (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  Continuous (coreC J μ (fun X => f (e X))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariantRightTranslation
section
noncomputable section

open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.AvgRight

theorem avgK_right_invariant : ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (ϖ : O) (φ : GL (Ix n) O → ℂ),
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∀ j : GL (Ix n) O,
      avgK ϖ (fun κ => φ (κ * j)) = avgK ϖ φ := by
  intro O _ _ n ϖ φ hφ j
  have hout : ∀ x : GL (Ix n) O,
      φ (Quotient.out (QuotientGroup.mk x : GL (Ix n) O ⧸ Gam2 (n := n) ϖ)) = φ x := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Gam2 (n := n) ϖ) x
    rw [hh]
    exact hφ x h.1 h.2
  have hshift : ∀ u : GL (Ix n) O ⧸ Gam2 (n := n) ϖ,
      φ (Quotient.out u * j) =
        φ (Quotient.out (u * (QuotientGroup.mk j : GL (Ix n) O ⧸ Gam2 (n := n) ϖ))) := by
    intro u
    rw [← hout (Quotient.out u * j)]
    congr 2
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  unfold avgK
  congr 1
  rw [finsum_congr hshift]
  exact finsum_comp_equiv (Equiv.mulRight (QuotientGroup.mk j : GL (Ix n) O ⧸ Gam2 (n := n) ϖ))
    (f := fun u => φ (Quotient.out u))

end GlobalTheory.CompanionTheory.Jp.AvgRight

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpEx
section
open MeasureTheory PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.Bump

theorem bumpEx : BumpEx := by
  intro X W hW
  obtain ⟨N, hNn, hNW, hNc⟩ := local_compact_nhds hW
  have h1 : (1 : X.G) ∈ interior N := mem_interior_iff_mem_nhds.mpr hNn
  obtain ⟨b, hb1, hb0, hbc, hbI⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : X.G))) isOpen_interior.isClosed_compl
    (Set.disjoint_singleton_left.mpr (fun h => h h1))
  have hbnn : ∀ z, 0 ≤ b z := fun z => (hbI z).1
  have hb11 : b 1 = 1 := hb1 (Set.mem_singleton _)
  have hsupp : Function.support b ⊆ N := by
    intro x hx
    by_contra hxN
    exact hx (hb0 (fun hi => hxN (interior_subset hi)))
  have hts : tsupport b ⊆ N := closure_minimal hsupp hNc.isClosed
  have hcc : Continuous fun z : X.G => b z⁻¹ := b.continuous.comp continuous_inv
  have hcs : HasCompactSupport fun z : X.G => b z⁻¹ :=
    hbc.comp_homeomorph (Homeomorph.inv X.G)
  have hI : 0 < ∫ z, b z⁻¹ ∂X.μ :=
    hcc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun z => hbnn _)
      (x := 1) (by simp [hb11])
  set I := ∫ z, b z⁻¹ ∂X.μ with hIdef
  have hnorm : ∀ z, ‖((b z / I : ℝ) : ℂ)‖ = b z / I := fun z => by
    rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hbnn z) hI.le)]
  have hsub : Function.support (fun z => ((b z / I : ℝ) : ℂ)) ⊆ Function.support b := by
    intro x hx h0
    apply hx
    simp [h0]
  refine ⟨fun z => ((b z / I : ℝ) : ℂ), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact Complex.continuous_ofReal.comp (b.continuous.div_const I)
  · exact hbc.mono hsub
  · intro z
    simp only [hnorm]
  · simp only [hnorm]
    rw [integral_div, ← hIdef, div_self hI.ne']
  · exact (closure_mono hsub).trans (hts.trans hNW)

end GlobalTheory.CompanionTheory.Bump
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardAffineHyperplane
section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpCount

theorem card_dotProduct_eq_one :
    ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a : Fin (n + 1) → k), a ≠ 0 →
  Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  intro k _ _ n a ha
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (funext h)
  have hax₀ : a ⬝ᵥ Pi.single i (a i)⁻¹ = 1 := by
    rw [dotProduct_single, mul_inv_cancel₀ hi]
  have hfib : ∀ c : k, (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = c)).card =
      (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card := by
    intro c
    apply Finset.card_bij' (fun x _ => x + (1 - c) • Pi.single i (a i)⁻¹)
      (fun x _ => x - (1 - c) • Pi.single i (a i)⁻¹)
    case hi =>
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [dotProduct_add, dotProduct_smul, hax₀, hx, smul_eq_mul, mul_one]
      ring
    case hj =>
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [dotProduct_sub, dotProduct_smul, hax₀, hx, smul_eq_mul, mul_one]
      ring
    case left_inv =>
      intro x _
      simp
    case right_inv =>
      intro x _
      simp
  have htot : (Finset.univ : Finset (Fin (n + 1) → k)).card =
      ∑ c : k, (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (a ⬝ᵥ x))
  have hcard : (Finset.univ : Finset (Fin (n + 1) → k)).card = Fintype.card k ^ (n + 1) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [← hcard, htot, Finset.sum_congr rfl (fun c _ => hfib c), Finset.sum_const,
    Finset.card_univ, smul_eq_mul]

end GlobalTheory.CompanionTheory.GapOpCount
end

