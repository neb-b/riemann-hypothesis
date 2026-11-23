module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionIntegralJ
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.WpInt

theorem isIntegral_int_of_closure (y : ℂ)
    (hy : IsIntegral (integralClosure ℤ ℂ).toSubring y) : IsIntegral ℤ y := by
  set R : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  haveI : Algebra.IsIntegral ℤ R := ⟨fun r => by
    have h : IsIntegral ℤ (r : ℂ) := r.2
    exact (isIntegral_algHom_iff (R.subtype.toIntAlgHom) Subtype.coe_injective).mp h⟩
  exact isIntegral_trans (R := ℤ) (A := R) y hy

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ →
    ∀ x : Fin 2 → ZMod N, IsIntegral ℤ (12 * (N : ℂ) ^ 2 * wp N x τ / ω ^ 2) ∧
      IsIntegral ℤ ((N : ℂ) ^ 3 * wpd N x τ / ω ^ 3) := by
  intro N _ τ ω hj hω x
  set R : Subring ℂ := (integralClosure ℤ ℂ).toSubring with hR
  have hjR : IsIntegral R (jT τ) := hj.tower_top
  have hbij : ActBij (vact N) := (_root_.GlobalTheory.WpFam.Act.rightActions N).1.actBij
  have hfam := _root_.GlobalTheory.WpFam.isFam_wp_wpd N
  have halg := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure (Fin 2 → ZMod N) (vact N)
  have hlin := _root_.GlobalTheory.QFam.hasQ_linear N
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNx : ∀ y : Fin 2 → ZMod N, N • y = 0 := fun y => by
    funext i; simp [nsmul_eq_mul]
  constructor
  · have hF : IsFam (vact N) ((2 : ℕ) : ℤ) (fun y t => (12 * (N : ℂ) ^ 2) * wp N y t) :=
      halg.2.2.1 2 _ (wp N) hfam.1
    have hQ : ∀ y, QAll (· ∈ R) N ((fun y t => (12 * (N : ℂ) ^ 2) * wp N y t) y) := fun y =>
      ⟨fun k => 12 * (N : ℂ) ^ 2 * cP N y k, hlin.2.2.1 _ _ _ (_root_.GlobalTheory.WpFam.ExpP.main N y),
        fun k => (_root_.GlobalTheory.WpFam.isIntegral_coefficients N N y k hN (hNx y)).2.2.1⟩
    have h := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow _ (vact N) 2 N _ R τ ω hN hbij hF hQ hjR hω x
    exact isIntegral_int_of_closure _ h
  · have hF : IsFam (vact N) ((3 : ℕ) : ℤ) (fun y t => ((N : ℂ) ^ 3) * wpd N y t) :=
      halg.2.2.1 3 _ (wpd N) hfam.2
    have hQ : ∀ y, QAll (· ∈ R) N ((fun y t => ((N : ℂ) ^ 3) * wpd N y t) y) := fun y =>
      ⟨fun k => (N : ℂ) ^ 3 * cD N y k, hlin.2.2.1 _ _ _ (_root_.GlobalTheory.WpFam.DerivExpansion.main N y),
        fun k => (_root_.GlobalTheory.WpFam.isIntegral_coefficients N N y k hN (hNx y)).2.1⟩
    have h := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow _ (vact N) 3 N _ R τ ω hN hbij hF hQ hjR hω x
    exact isIntegral_int_of_closure _ h

end GlobalTheory.WpInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeQuotientCorrespondenceOfTorsionTranspor
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
open IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.WpFam.TrIs

theorem main : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → IsTr ι Λ₀ Λ₁ (Tr t) := by
  intro K _ _ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT
  obtain ⟨_, _, _, hL0, ⟨𝔞, h𝔞, hL1⟩, _, _, _⟩ := hT
  obtain ⟨hsub, _, hleft, hright⟩ := _root_.GlobalTheory.WpFam.TrAdd.main K t
  have hA : ∀ y : Af K, y ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (y v) ≤ 1 := fun y => GlobalTheory.Idele.mem_adelicIdeal_one_iff
  have hone : ∀ x : K, x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      algebraMap K (Af K) x ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x =>
    (GlobalTheory.Idele.algebraMap_mem_adelicIdeal (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) x).symm
  have hmem𝔞 : ∀ a' : K, a' ∈ 𝔞 ↔ (t : Af K) * algebraMap K (Af K) a' ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a'
    rw [h𝔞, hA]
  have hL0' : ∀ z, z ∈ Λ₀.lattice ↔ z ∈ ι '' ((1 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL0 z
  have hL1' : ∀ z, z ∈ Λ₁.lattice ↔ z ∈ ι '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL1 z
  have h0 : ∀ a : K, ι a ∈ Λ₀.lattice ↔ a ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a
    rw [hL0']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← ι.injective e]
    · intro h; exact ⟨a, h, rfl⟩
  have h1 : ∀ a' : K, ι a' ∈ Λ₁.lattice ↔ a' ∈ 𝔞 := by
    intro a'
    rw [hL1']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← ι.injective e]
    · intro h; exact ⟨a', h, rfl⟩
  have hTr : ∀ x x' : K, Tr t x x' ↔ (t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x x' => (hA _).symm
  refine ⟨hsub, ?_, ?_, hleft, hright, ?_, ?_⟩
  · intro x x' h
    have hd := (hTr x x').1 h
    rw [h0, h1, hone, hmem𝔞]
    constructor
    · intro hx
      have := add_mem hd hx
      rwa [sub_add_cancel] at this
    · intro hx
      have := sub_mem hx hd
      rwa [sub_sub_cancel] at this
  · intro x x' hx hx'
    rw [hTr]
    exact sub_mem ((hmem𝔞 x').1 ((h1 x').1 hx')) ((hone x).1 ((h0 x).1 hx))
  · intro z hz
    obtain ⟨k, -, e⟩ := (hL0' z).1 hz
    exact ⟨k, e⟩
  · intro z hz
    obtain ⟨k, -, e⟩ := (hL1' z).1 hz
    exact ⟨k, e⟩

end GlobalTheory.WpFam.TrIs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfComponentsIntoGroupSchemeProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.Serre

theorem isMonHom_of_components : ∀ (T : Scheme.{0}) (A' B' C : Over T) [GrpObj A'] [GrpObj B'] [GrpObj C] (r : ℕ) (pr' : Fin r → (B' ⟶ A')), (∀ u, IsMonHom (pr' u)) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ Φ : C ⟶ B', (∀ u, IsMonHom (Φ ≫ pr' u)) → IsMonHom Φ := by
  intro T A' B' C _ _ _ r pr' hpr huniv Φ hΦ
  have hcomp : ∀ u, IsMonHom (pr' u) := hpr
  have hΦu : ∀ u, IsMonHom (Φ ≫ pr' u) := hΦ
  refine ⟨?_, ?_⟩
  · obtain ⟨x, -, hx⟩ := huniv (𝟙_ (Over T)) (fun u => η[C] ≫ Φ ≫ pr' u)
    have h1 : η[C] ≫ Φ = x := hx _ (fun u => by simp)
    have h2 : (η[B'] : 𝟙_ (Over T) ⟶ B') = x := hx _ (fun u => by
      haveI := hcomp u; haveI := hΦu u
      rw [IsMonHom.one_hom, IsMonHom.one_hom (Φ ≫ pr' u)])
    rw [h1, h2]
  · obtain ⟨x, -, hx⟩ := huniv (C ⊗ C) (fun u => μ[C] ≫ Φ ≫ pr' u)
    have h1 : μ[C] ≫ Φ = x := hx _ (fun u => by simp)
    have h2 : (Φ ⊗ₘ Φ) ≫ μ[B'] = x := hx _ (fun u => by
      haveI := hcomp u; haveI := hΦu u
      rw [Category.assoc, IsMonHom.mul_hom (Φ ≫ pr' u), IsMonHom.mul_hom (pr' u),
        ← Category.assoc, tensorHom_comp_tensorHom])
    rw [h1, h2]

end GlobalTheory.Serre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentDualFrobeniusOfBlock
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.DualFrobNilMat

theorem mulVec_transpose_inv_blk_apply {B : Type} [CommRing B] (σ : B →+* B) (p : ℕ) {d k : ℕ}
    (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B) (w : Fin d ⊕ Fin k → B) (r : Fin d ⊕ Fin k) :
    ((U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j)) r =
      (∑ j : Fin d, U⁻¹ (Sum.inl j) r * σ (w (Sum.inl j))) +
      (p : B) * ∑ j : Fin k, U⁻¹ (Sum.inr j) r * σ (w (Sum.inr j)) := by
  have hU : ∀ r s, U.transpose⁻¹ r s = U⁻¹ s r := fun r s => by
    rw [← Matrix.transpose_nonsing_inv]; rfl
  simp only [Matrix.mulVec, dotProduct, blk, Matrix.mul_diagonal, hU, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_one, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem isNil_of_block : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O) (σ : B →+* B) (p : ℕ) (m : Ideal O), θ (p : B) ∈ m → m ≠ ⊤ → (∀ b, ∃ c, σ b - b ^ p = p * c) → ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B) (c : Fin d → Fin d → B), (∀ a j, ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b) → (∃ N : ℕ, ∀ w : Fin d → O ⧸ m, (fun w : Fin d → O ⧸ m => fun a => ∑ j, Ideal.Quotient.mk m (θ (c a j)) * w j ^ p)^[N] w = 0) → IsNil θ σ (U.transpose⁻¹ * blk d k 1 (p : B)) := by
  intro B O _ _ θ σ p m hp hm hσ d k U c hc hS
  obtain ⟨N, hN⟩ := hS
  set ρ : B →+* O ⧸ m := (Ideal.Quotient.mk m).comp θ with hρ
  have hρp : ρ (p : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hp
  have hρσ : ∀ b, ρ (σ b) = ρ b ^ p := by
    intro b
    obtain ⟨e, he⟩ := hσ b
    have h := congrArg ρ he
    rw [map_sub, map_mul, map_pow, hρp, zero_mul, sub_eq_zero] at h
    exact h
  have hp0 : p ≠ 0 := by
    rintro rfl
    apply hm
    obtain ⟨e, he⟩ := hσ 0
    simp only [map_zero, pow_zero, zero_sub, Nat.cast_zero, zero_mul, neg_eq_zero] at he
    have h1 : (1 : O) = 0 := by rw [← map_one θ, he, map_zero]
    rw [Ideal.eq_top_iff_one, h1]
    exact m.zero_mem
  have hT : ∀ (w : Fin d ⊕ Fin k → B) r,
      ρ (((U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j)) r) =
        ∑ j, ρ (U⁻¹ (Sum.inl j) r) * ρ (w (Sum.inl j)) ^ p := by
    intro w r
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mulVec_transpose_inv_blk_apply, map_add (f := _), map_mul, hρp, zero_mul, add_zero, map_sum]
    simp only [map_mul, hρσ]
  have hinl : ∀ a j, ρ (U⁻¹ (Sum.inl j) (Sum.inl a)) = ρ (c a j) := by
    intro a j
    obtain ⟨e, he⟩ := hc a j
    have h := congrArg ρ he
    rw [map_sub, map_mul, hρp, zero_mul, sub_eq_zero] at h
    exact h.symm
  have hiter : ∀ (t : ℕ) (v : Fin d ⊕ Fin k → B),
      (fun a => ρ (((fun w : Fin d ⊕ Fin k → B =>
        (U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j))^[t] v) (Sum.inl a))) =
      (fun w : Fin d → O ⧸ m => fun a => ∑ j, Ideal.Quotient.mk m (θ (c a j)) * w j ^ p)^[t]
        (fun a => ρ (v (Sum.inl a))) := by
    intro t
    induction t with
    | zero => intro v; rfl
    | succ t ih =>
      intro v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      funext a
      rw [hT]
      exact Finset.sum_congr rfl fun j _ => by rw [hinl]; rfl
  refine ⟨N + 1, fun v r hu => hm ?_⟩
  rw [Function.iterate_succ_apply'] at hu
  have h0 : ρ (((U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ
      (((fun w : Fin d ⊕ Fin k → B =>
        (U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j))^[N] v) j)) r) = 0 := by
    rw [hT]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h := congrFun (hiter N v) j
    rw [hN] at h
    simp only [Pi.zero_apply] at h
    rw [h, zero_pow hp0, mul_zero]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.Quotient.eq_zero_iff_mem.1 h0) hu

end GlobalTheory.DualFrobNilMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmModIdealTopLinearCombination
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem ql_comb_top : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → ∀ w : ι → B, QL μ ⊤ (comb w e) := by
  intro B O Q _ _ _ _ θ d μ hμ ι _ e he w
  have hc : ∀ i, constantCoeff (up Q μ i) = 0 := by
    intro i
    simp [up, hμ.const i]
  have hzero : QL μ ⊤ (0 : MvPowerSeries (Fin d) Q) := by
    refine ⟨by simp, fun i => ⟨0, Submodule.mem_top, by simp [lin]⟩, fun α => ⟨0, Submodule.mem_top, ?_⟩⟩
    have := formalCoboundary_smul hc (0 : Q) 0
    rw [zero_smul, zero_smul] at this
    rw [this]; simp
  have hadd : ∀ f g : MvPowerSeries (Fin d) Q, QL μ ⊤ f → QL μ ⊤ g → QL μ ⊤ (f + g) := by
    rintro f g ⟨hf0, hf1, hf2⟩ ⟨hg0, hg1, hg2⟩
    refine ⟨by simp [hf0, hg0], fun i => ?_, fun α => ?_⟩
    · obtain ⟨a, -, ha⟩ := hf1 i
      obtain ⟨b, -, hb⟩ := hg1 i
      exact ⟨a + b, Submodule.mem_top, by simp only [lin, map_add (f := _)] at ha hb ⊢; rw [ha, hb]⟩
    · obtain ⟨a, -, ha⟩ := hf2 α
      obtain ⟨b, -, hb⟩ := hg2 α
      exact ⟨a + b, Submodule.mem_top, by rw [formalCoboundary_add hc, map_add (f := _), ha, hb, map_add (f := _)]⟩
  have hsmul : ∀ (c : B) (f : MvPowerSeries (Fin d) Q), QL μ ⊤ f → QL μ ⊤ (algebraMap B Q c • f) := by
    rintro c f ⟨hf0, hf1, hf2⟩
    refine ⟨by simp [hf0], fun i => ?_, fun α => ?_⟩
    · obtain ⟨a, -, ha⟩ := hf1 i
      refine ⟨c * a, Submodule.mem_top, ?_⟩
      simp only [lin, map_smul, smul_eq_mul] at ha ⊢
      rw [ha, map_mul]
    · obtain ⟨a, -, ha⟩ := hf2 α
      refine ⟨c * a, Submodule.mem_top, ?_⟩
      rw [formalCoboundary_smul hc, map_smul, smul_eq_mul, ha, map_mul]
  unfold comb
  exact Finset.sum_induction _ (QL μ ⊤) hadd hzero fun i _ => hsmul (w i) (e i) (he i)

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrameIntegers

theorem isFrame_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → IsFrame p C (RingHom.id O) := by
  intro p hp C _ _ _ v O _ _ hnu _ _ hv
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hmapp : algebraMap O C (p : O) = (p : C) := map_natCast _ _
  have hvp1 : v (p : C) < 1 := by
    have h1 := hv.map_le_one (p : O)
    rw [hmapp] at h1
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exact absurd (hv.isUnit_of_one (by rw [hmapp]; exact Ne.isUnit hpC) (by rw [hmapp]; exact h)) hnu.out
  have hint : ∀ z : ℤ, v (z : C) ≤ 1 := by
    intro z
    have := hv.map_le_one (z : O)
    rwa [map_intCast] at this
  refine ⟨Function.surjective_id, hv.hom_inj, ?_, Ne.isUnit hpC, ?_, ?_, ?_, inferInstance⟩
  · intro q
    obtain ⟨k, hk⟩ : ∃ k : ℕ, v (p : C) ^ k * v q ≤ 1 := by
      by_cases hq : v q = 0
      · exact ⟨0, by simp [hq]⟩
      · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr (pos_iff_ne_zero.mpr hq)) hvp1
        refine ⟨k, ?_⟩
        calc v (p : C) ^ k * v q ≤ (v q)⁻¹ * v q := mul_le_mul_of_nonneg_right hk.le zero_le
          _ = 1 := inv_mul_cancel₀ hq
    have hle : v ((p : C) ^ k * q) ≤ 1 := by rw [map_mul, map_pow]; exact hk
    obtain ⟨b, hb⟩ := hv.exists_of_le_one hle
    exact ⟨k, b, hb.symm⟩
  · intro n hn
    have hB : (n : C) * (Nat.gcdA n p : C) + (p : C) * (Nat.gcdB n p : C) = 1 := by
      have h := Nat.gcd_eq_gcd_ab n p
      rw [Nat.Coprime.gcd_eq_one hn] at h
      exact_mod_cast h.symm
    have hvn : v (n : C) = 1 := by
      have h1 : v (n : C) ≤ 1 := by exact_mod_cast hint n
      by_contra hne
      have hlt : v (n : C) < 1 := lt_of_le_of_ne h1 hne
      have a1 : v ((n : C) * (Nat.gcdA n p : C)) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hlt
      have a2 : v ((p : C) * (Nat.gcdB n p : C)) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hvp1
      have := Valuation.map_add_lt v a1 a2
      rw [hB, map_one] at this
      exact lt_irrefl _ this
    have hnC : (n : C) ≠ 0 := by
      intro h; rw [h, map_zero] at hvn; exact zero_ne_one hvn
    have hmapn : algebraMap O C (n : O) = (n : C) := map_natCast _ _
    exact hv.isUnit_of_one (by rw [hmapn]; exact Ne.isUnit hnC) (by rw [hmapn]; exact hvn)
  · intro x hx
    simp only [RingHom.id_apply] at hx
    subst hx
    exact ⟨0, rfl, by simp [hp0]⟩
  · intro a ha
    have hpO : (p : O) ≠ 0 := by
      intro h; apply hpC; rw [← hmapp, h, map_zero]
    exact (mul_eq_zero.mp ha).resolve_left hpO

end GlobalTheory.FrameIntegers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoLBCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixUniq

open GlobalTheory.HomFixMat

theorem psi_unique {Rg : Type} [CommRing Rg] {A : Over (Sp Rg)} [GrpObj A] {X : Scheme.{0}} (ψ ψ₂ : X ⟶ (topS Rg ⊗ A).left)
    (h : ψ ≫ (snd (topS Rg) A).left = ψ₂ ≫ (snd (topS Rg) A).left) : ψ = ψ₂ := by
  haveI : Mono (topS Rg).hom := by
    show Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
  have e : ψ ≫ (fst (topS Rg) A).left = ψ₂ ≫ (fst (topS Rg) A).left := by
    rw [← cancel_mono (topS Rg).hom]
    simp only [Category.assoc, Over.w]
    rw [← Over.w (snd (topS Rg) A), ← Category.assoc, h, Category.assoc]
  exact pullback.hom_ext e h

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B]


variable (L : LB A.left) (M : LB B.left) in
def RigEq (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) {R : Type} [CommRing R]
    (t : Sp R ⟶ Sp Rg) {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B')
    (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left)
    (α : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) : Prop :=
  ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (α.s p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k

theorem isoLB_cover {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left}
    {M : LB B.left} (hL : L.IsLB) (hM : M.IsLB) (k : ℕ) {R : Type} [CommRing R] {A' B' : Over (Sp R)}
    (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (x : A'.left) :
    ∃ p, x ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p := by
  have hc : ∀ {X : Scheme.{0}} (N : LB X), N.IsLB → ∀ y : X, ∃ i, y ∈ N.U i := fun N hN y =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [hN.cover]; trivial)
  obtain ⟨iM, hiM⟩ := hc M hM ((((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left)).base x)
  obtain ⟨iL, hiL⟩ := hc L hL (((ψA ≫ (snd (topS Rg) A).left)).base x)
  exact ⟨(fun _ => iM, fun _ => iL), Set.mem_iInter.2 fun _ => hiM, Set.mem_iInter.2 fun _ => hiL⟩

end GlobalTheory.HomFixUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectSectionRes
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem defectSec_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  intro Q q _ hqQ U u hQ V g
  have hQV : IsUnit (Q : Γ(V, ⊤)) := by
    have := hQ.map g.appTop.hom
    simpa using this
  apply (_root_.GlobalTheory.EtC.sec_ext_glue _ _ V).1
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.2 hQV (Units.map g.appTop.hom.toMonoidHom u)) ?_
  rintro W h ⟨v, hv⟩
  have hres : Sec.res h (Sec.res g (defectSec Q q U u)) = Sec.res (h ≫ g) (defectSec Q q U u) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hres, GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ V _ hQV W h v hv]
  refine GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ W (h ≫ g) v ?_
  rw [hv]
  ext
  simp [Scheme.Hom.comp_appTop] <;> rfl

end GlobalTheory.EtC.RedChern
end

