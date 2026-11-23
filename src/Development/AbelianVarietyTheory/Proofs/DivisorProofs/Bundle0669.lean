module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGaloisPairingEqPmOnePrimeDegree
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.PairPM

theorem rootSum_zero {K : Type} [Field K] (θ : AlgebraicClosure K →* ℂ) (P : K[X]) :
    rootSum θ 0 P = (P.natDegree : ℂ) := by
  simp only [rootSum, pow_zero, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

theorem natCard_ext (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] :
    Nat.card F' = Nat.card F ^ Module.finrank F F' := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI := Fintype.ofFinite F; haveI := Fintype.ofFinite F'
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := F')]

theorem sum_cusp_eq_zero {K : Type} [Field K] [Finite K] (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (m e : ℕ) (hm : 0 < m)
    (h : ∀ a, ¬ e * Nat.card K ^ a ≡ 0 [MOD Nat.card K ^ m - 1]) :
    ∑ᶠ x, cusp θ m e x = 0 := by
  have H := finsum_cusp_mul_star_chG K θ hθ m e 0 hm
  have hf : (Finset.range m).filter (fun i => e * Nat.card K ^ i ≡ 0 [MOD Nat.card K ^ m - 1]) = ∅ := by
    ext i; simp [h i]
  rw [hf] at H
  have hc : ∀ x : GL (Fin m) K, star (chG (rootSum θ 0) m x) = (m : ℂ) := by
    intro x; simp [chG, rootSum_zero, Matrix.charpoly_natDegree_eq_dim]
  simp only [hc, Finset.card_empty, Nat.cast_zero, mul_zero] at H
  rw [← finsum_mul] at H
  exact (mul_eq_zero.1 H).resolve_right (by exact_mod_cast hm.ne')

theorem gram_lift {K : Type} [Field K] [Finite K] (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (q l m k : ℕ) (hq : 2 ≤ q)
    (hl : 0 < l) (hm : 0 < m) (hK : Nat.card K = q ^ l) (hreg : Reg q (l * m) k) :
    ∀ i j, i < l → j < l → ∑ᶠ x, cusp θ m (k * q ^ i) x * star (chG (rootSum θ (k * q ^ j)) m x) =
      if i = j then (((-1 : ℤ) ^ (m - 1) : ℤ) : ℂ) * (Nat.card (GL (Fin m) K) : ℂ) else 0 := by
  intro i j hi hj
  rw [finsum_cusp_mul_star_chG K θ hθ m _ _ hm, hK]
  have h3 := (reg_step_of_dvd q l m k hq hl hm hreg).2.2 i j
  have hf : (Finset.range m).filter (fun a => k * q ^ i * (q ^ l) ^ a ≡ k * q ^ j [MOD (q ^ l) ^ m - 1]) =
      if i = j then {0} else ∅ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨ha, h⟩
      obtain ⟨rfl, rfl⟩ := (h3 a hi hj ha).1 h
      simp
    · intro h
      by_cases hij : i = j
      · rw [if_pos hij, Finset.mem_singleton] at h
        subst h; subst hij
        exact ⟨hm, (h3 0 hi hi hm).2 ⟨rfl, rfl⟩⟩
      · rw [if_neg hij] at h
        simp at h
  rw [hf]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

theorem hfree_J {K : Type} [Field K] [Finite K] (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) :
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card K) p.1 p.2 ∧
      (2 ≤ p.1 ∨ ¬ p.2 ≡ 0 [MOD Nat.card K - 1])) → HFree (J θ L (deg L))
  | [], _ => by intro h; simp [deg] at h
  | p :: L, hL => by
    have hp := hL p (List.mem_cons_self ..)
    have hL' : ∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card K) p.1 p.2 ∧
        (2 ≤ p.1 ∨ ¬ p.2 ≡ 0 [MOD Nat.card K - 1]) := fun p' h' => hL p' (List.mem_cons_of_mem _ h')
    rw [J_cons]
    have hdeg : deg (p :: L) = p.1 + deg L := by simp [deg]
    exact GlobalTheory.T.hyperplaneFixerSumVanishes_harishChandraInduction K p.1 (deg L) (deg (p :: L)) hdeg _ _
      (GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular K θ hθ p.1 p.2 hp.1 hp.2.1).1
      (GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular K θ hθ L (fun p' h' => ⟨(hL' p' h').1, (hL' p' h').2.1⟩) _ rfl)
      (GlobalTheory.T.hyperplaneFixerSumVanishes_cuspidalCharacterGLFiniteField K θ hθ p.1 p.2 hp.2.2) (hfree_J θ hθ L hL')

end GlobalTheory.Shin.PairPM

namespace GlobalTheory.Shin.PairPM

theorem pairing_pm_one : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ m k n : ℕ, 0 < m → n = Module.finrank F F' * m → Reg (Nat.card F) n k → ∃ z : ℤ, (z = 1 ∨ z = -1) ∧
    ∑ᶠ x, psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n x *
      star (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n x) = z * (Nat.card (GL (Fin n) F') : ℂ) := by
  intro F F' _ _ _ _ s hl _ ι θ hθ m k n hm hn hreg
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have hK : Nat.card F' = Nat.card F ^ Module.finrank F F' := natCard_ext F F'
  set l := Module.finrank F F' with hl_def
  set q := Nat.card F with hq_def
  have hq : 2 ≤ q := Finite.one_lt_card
  have hl0 : 0 < l := hl.pos
  have hl2 : 2 ≤ l := hl.two_le
  have hreg' : Reg q (l * m) k := hn ▸ hreg
  have hR := reg_step_of_dvd q l m k hq hl0 hm hreg'
  have hLL : liftL q l [(n, k)] = (List.range l).map (fun i => (m, k * q ^ i)) := by
    simp [liftL, hn, Nat.mul_div_cancel_left _ hl0]
  obtain ⟨hdeg, hmem⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [(n, k)] hq hl0 (by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact ⟨by rw [hn]; exact Nat.mul_pos hl0 hm, by rw [hn]; exact dvd_mul_right _ _, hreg⟩)
  have hdeg' : deg (liftL q l [(n, k)]) = n := by rw [hdeg]; simp [deg]
  have hY := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ (liftL q l [(n, k)]) (fun p hp => by rw [hK]; exact hmem p hp) n hdeg'.symm
  have hF := hfree_J θ hθ (liftL q l [(n, k)]) (by
    intro p hp
    refine ⟨(hmem p hp).1, by rw [hK]; exact (hmem p hp).2, ?_⟩
    rw [hLL, List.mem_map] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases h2 : 2 ≤ m
    · exact Or.inl h2
    · right
      have h1 : m = 1 := by omega
      have := hR.2.1 (by nlinarith) i
      rw [h1, mul_one] at this
      rw [hK]
      exact this)
  rw [hdeg'] at hF
  refine ⟨((-1 : ℤ) ^ (m - 1)) ^ l, ?_, ?_⟩
  · rw [← pow_mul]
    exact neg_one_pow_eq_or ℤ _
  · rw [GlobalTheory.T.finsum_psiG_mul_star_eq_chG F' _ n _ hY hF]
    have hS : chG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n =
        chG (fun P => ∏ j ∈ Finset.range l, rootSum θ (k * q ^ j) P) n := by
      funext x
      simp only [chG]
      exact GlobalTheory.T.prod_rootPowerSum_map_galois_eq F F' θ k _
    rw [hS]
    have hZ := GlobalTheory.T.pairing_cuspidalCharacterGL_rootPowerSumCharacter F' θ m (fun i => k * q ^ i) ((-1) ^ (m - 1))
      (fun i => sum_cusp_eq_zero θ hθ m _ hm (by
        intro a
        rw [hK, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
        exact hR.2.1 (by nlinarith) _))
      l (gram_lift θ hθ q l m k hq hl0 hm hK hreg') (List.range l) (Finset.range l) List.nodup_range
      (fun i hi => List.mem_range.1 hi) (fun j hj => Finset.mem_range.1 hj) (by simp) n
      (by rw [hn, List.length_range, mul_comm])
    rw [List.toFinset_range, if_pos rfl, List.length_range, ← hLL] at hZ
    have hst : ∀ (a b : GL (Fin n) F' → ℂ), ∑ᶠ x, a x * star (b x) = star (∑ᶠ x, b x * star (a x)) := by
      intro a b
      rw [show star (∑ᶠ x, b x * star (a x)) = starAddEquiv (∑ᶠ x, b x * star (a x)) from rfl,
        map_finsum _ (Set.toFinite _)]
      refine finsum_congr fun x => ?_
      simp [star_mul]
    rw [hst, hZ]
    push_cast
    simp [star_pow]

end GlobalTheory.Shin.PairPM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsFlatNormalStageAtOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsOfConstants_flat_normal_stage_at_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (sA : A), sA ≠ 0 →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsIntegrallyClosed B') (_ : Algebra A' B') (_ : Module.Flat A' B')
      (ι : A →+* A') (α : A' →+* T) (β : Localization.AtPrime QA →+* B') (γ : B' →+* O),
      (algebraMap A' B').comp ι = β.comp (algebraMap A (Localization.AtPrime QA)) ∧
      γ.comp β = jA ∧ γ.comp (algebraMap A' B') = (algebraMap T O).comp α ∧ ι sA ≠ 0 ∧
      ∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → ι sA ∈ 𝔭 →
        (𝔭.map (algebraMap A' B')).IsPrime := by
  first | (exact @GlobalTheory.GoodStageOrigin.good_stage) | (exact GlobalTheory.GoodStageOrigin.good_stage) | (intros; apply GlobalTheory.GoodStageOrigin.good_stage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqOneAddOfSq
section
set_option autoImplicit false

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer

theorem dpExp_eq_one_add_of_sq {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type}
    [CommRing C] {J : Ideal C} (δ : DividedPowers J) (ρ : Hol W →+* C) {x : C} (hx : x ∈ J)
    (hx2 : x * x = 0) : dpExp δ x = 1 + x := by
  have hv : ∀ n, 2 ≤ n → δ.dpow n x = 0 := by
    intro n hn
    have hu : IsUnit ((n.factorial : ℕ) : C) := by
      have h1 : IsUnit ((n.factorial : ℕ) : Hol W) := by
        rw [← map_natCast (algebraMap ℂ (Hol W))]
        exact (IsUnit.mk0 _ (by exact_mod_cast (Nat.factorial_ne_zero n))).map _
      simpa using h1.map ρ
    have hp : x ^ n = 0 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, sq, hx2, zero_mul]
    have := δ.factorial_mul_dpow_eq_pow hx (n := n)
    rw [hp] at this
    exact (hu.mul_right_eq_zero).1 this
  rw [dpExp_eq_sum_range_of_vanish δ x 2 hv]
  simp [Finset.sum_range_succ, δ.dpow_zero hx, δ.dpow_one hx]

theorem step_exp {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C]
    {J : Ideal C} {ρ ρ' : Hol W →+* C} (s : Step J ρ ρ') (e l : Hol W)
    (he : ∀ a, dw a e = dw a l * e) :
    ρ' l - ρ l ∈ J ∧ (ρ' l - ρ l) * (ρ' l - ρ l) = 0 ∧ ρ' e = ρ e * (1 + (ρ' l - ρ l)) := by
  obtain ⟨n, h1, h2, h3⟩ := s
  have hx : ρ' l - ρ l = ∑ a, ρ (dw a l) * n a := by rw [h3 l]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hx]; exact J.sum_mem fun a _ ↦ J.mul_mem_left _ (h1 a)
  · rw [hx, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
    rw [mul_mul_mul_comm, h2, mul_zero]
  · rw [hx, h3 e, mul_add, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [he, map_mul]; ring

theorem close_exp : ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C]
    (J : Ideal C) (δ : DividedPowers J), IsNilDP δ → ∀ (ρ₁ ρ₂ : Hol W →+* C) (e l : Hol W),
    (∀ a, dw a e = dw a l * e) → Close J ρ₁ ρ₂ → ρ₂ e = ρ₁ e * dpExp δ (ρ₂ l - ρ₁ l) := by
  intro I _ g W C _ J δ hδ ρ₁ ρ₂ e l he hc
  induction hc with
  | refl => rw [sub_self, dpExp_zero, mul_one]
  | @tail ρ ρ' hc' s ih =>
    obtain ⟨hxJ, hx2, hρ'⟩ := step_exp s e l he
    have hyJ : ρ l - ρ₁ l ∈ J := Close.sub_mem hc' l
    rw [show ρ' l - ρ₁ l = (ρ l - ρ₁ l) + (ρ' l - ρ l) by ring,
      hδ.dpExp_add_eq_mul hyJ hxJ, dpExp_eq_one_add_of_sq δ ρ₁ hxJ hx2, hρ', ih, mul_assoc]

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DwComapLinear
section
open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem AnPer.dw_comap_linear : ∀ {I I' : Type} [Fintype I] [Fintype I'] {g g' : ℕ} {W : Opens (Tot I g)} {W' : Opens (Tot I' g')} (b : (I' → ℂ) → I → ℂ) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ p ∈ W', AnalyticAt ℂ b p.1) → ∀ (hΦ : AnalyticOnNhd ℂ (fun p : Tot I' g' ↦ ((b p.1, M p.2) : Tot I g)) W') (h : ∀ p ∈ W', ((b p.1, M p.2) : Tot I g) ∈ W) (a : Fin g') (f : Hol W), dw a (Hol.comap _ hΦ h f) = ∑ c, M (Pi.single a 1) c • Hol.comap _ hΦ h (dw c f) := by
  intro I I' _ _ g g' W W' b M hb hΦ h a f
  refine Hol.ext_fn fun p hp ↦ ?_
  have e : HasFDerivAt (fun p : Tot I' g' ↦ ((b p.1, M p.2) : Tot I g))
      (((fderiv ℂ b p.1).comp (ContinuousLinearMap.fst ℂ _ _)).prod
        ((LinearMap.toContinuousLinearMap M).comp (ContinuousLinearMap.snd ℂ _ _))) p :=
    ((hb p hp).differentiableAt.hasFDerivAt.comp p hasFDerivAt_fst).prodMk
      ((LinearMap.toContinuousLinearMap M).hasFDerivAt.comp p hasFDerivAt_snd)
  have hv : ((0 : I → ℂ), M (Pi.single a 1)) = ∑ c, M (Pi.single a 1) c • (((0 : I → ℂ), Pi.single c 1) : Tot I g) := by
    ext i
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  change (Hol.der _ (Hol.comap _ hΦ h f)).fn p = _
  rw [Hol.fn_der_comap _ _ _ _ f hp, e.fderiv]
  have e2 : (((fderiv ℂ b p.1).comp (ContinuousLinearMap.fst ℂ _ _)).prod
        ((LinearMap.toContinuousLinearMap M).comp (ContinuousLinearMap.snd ℂ _ _)))
        (((0 : I' → ℂ), Pi.single a 1) : Tot I' g') = ((0 : I → ℂ), M (Pi.single a 1)) := by
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, hv, map_sum, ← Hol.ev_apply p hp, map_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, Hol.ev_apply p hp, Hol.fn_comap _ _ _ _ hp]
  change _ = _ * (Hol.der _ f).fn _
  rw [Hol.fn_der _ _ (h p hp)]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEnlargeByUniformiserRootsStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_enlarge_by_uniformiser_roots : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.etale_enlarge) | (exact GlobalTheory.KeyOriginEnlarge.etale_enlarge) | (intros; apply GlobalTheory.KeyOriginEnlarge.etale_enlarge  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfFilteredColimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_filtered_colimit : ∀ (q : ℕ) [NeZero q] (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ j, IsUnit (q : D.obj j)) → (∀ j, HInv q (D.obj j)) → HInv q c.pt := by
  first | (exact @GlobalTheory.EtC.hInv_of_filtered_colimit) | (exact GlobalTheory.EtC.hInv_of_filtered_colimit) | (intros; apply GlobalTheory.EtC.hInv_of_filtered_colimit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtFnEqValAt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem evalAt_fn_eq_valAt' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}
    (x : Sp (Hol W) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (p : E) (hp : p ∈ W) :
    ⊤ ≤ (spMap (Hol.ev p hp).toRingHom ≫ x) ⁻¹ᵁ U ∧
      (evalAt x U h f).fn p = valAt' (spMap (Hol.ev p hp).toRingHom ≫ x) U f := by
  set φ : Hol W →+* ℂ := (Hol.ev p hp).toRingHom
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun q _ ↦ h (Set.mem_univ ((spMap φ) q))
  refine ⟨h', ?_⟩
  have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom =
      x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (Hol W))).hom ≫ CommRingCat.ofHom φ := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
    congr 2
  have e2 := congrArg (fun t ↦ t.hom f) e
  rw [valAt', dite_eq_left h', valAt, ← Hol.ev_apply p hp]
  exact e2.symm

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtNatural
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvalNat

theorem evalAt_natural : ∀ {X : Scheme.{0}} {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U), ∃ h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U, (∀ f : Γ(X, U), evalAt (spMap φ ≫ x) U h' f = φ (evalAt x U h f)) ∧ ∀ (U' : X.Opens) (i : U ≤ U') (h'' : ⊤ ≤ x ⁻¹ᵁ U') (f : Γ(X, U')), evalAt x U' h'' f = evalAt x U h ((X.presheaf.map (homOfLE i).op).hom f) := by
  intro X C C' _ _ φ x U h
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ ↦ h (Set.mem_univ ((spMap φ) p))
  refine ⟨h', fun f ↦ ?_, fun U' i h'' f ↦ ?_⟩
  · have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C')).hom =
        x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom ≫ CommRingCat.ofHom φ := by
      rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
      congr 2
    exact congrArg (fun t ↦ t.hom f) e
  · have e : x.appLE U' ⊤ h'' = X.presheaf.map (homOfLE i).op ≫ x.appLE U ⊤ h := by
      rw [Scheme.Hom.map_appLE]
    unfold evalAt
    rw [e]
    rfl

end GlobalTheory.EvalNat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePrimesOverPrimeCoprimalityEquiv
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.PrimesOverL

theorem primes_over_l : ∀ {F : Type} [Field F] [NumberField F] (l : ℕ), l.Prime →
    ∃ P : Finset (Ideal (𝓞 F)), (∀ 𝔭 ∈ P, 𝔭.IsMaximal ∧ 𝔭 ≠ ⊥ ∧ l ∣ Ideal.absNorm 𝔭) ∧
      ∀ I : Ideal (𝓞 F), CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔ CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I := by
  first
  | exact @_root_.GlobalTheory.PrimesAboveExistence.exists_primes_above
  | exact _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above
  | (apply _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above ..)

end GlobalTheory.PrimesOverL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianEtaleStalkOverPointStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strictlyHenselianEtaleStalk_over_point : ∀ (S : Scheme.{0}) (U : Over S), Etale U.hom → ∀ u : U.left, ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ S) (g : Over.mk s ⟶ U), IsStalk O s ∧ ∃ v, g.left v = u := by
  first | (exact @GlobalTheory.EtC.exists_isStalk_over_point) | (exact GlobalTheory.EtC.exists_isStalk_over_point) | (intros; apply GlobalTheory.EtC.exists_isStalk_over_point  <;> assumption)
end

