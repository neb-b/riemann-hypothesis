module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleTwistOfGeneratedAndVeryAmple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldEquivOpenImmersionSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConsecutiveVeryAmplePowersRelAmple
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg.ConsecPowers

theorem units_identity {G : Type*} [CommGroup G] (u P Q R β γ ε : G) (d t : ℤ) :
    (u * P * β⁻¹) * (u * Q * γ⁻¹) ^ (d * t) * (u * R * ε⁻¹) ^ d =
      u ^ (d * (t + 1) + 1) * (β * (γ ^ d) ^ t * (ε ^ d) ^ (1 : ℤ))⁻¹ * (P * Q ^ (d * t) * R ^ d) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
  module

theorem pw_pw {X : Scheme.{0}} (L : LB X) (a b : ℤ) : pw (pw L a) b = pw L (a * b) := by
  show (⟨L.ι, L.U, fun i j => (L.g i j ^ a) ^ b⟩ : LB X) = ⟨L.ι, L.U, fun i j => L.g i j ^ (a * b)⟩
  congr 1
  funext i j
  exact (zpow_mul _ _ _).symm

theorem lbIso_tw_tw {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (d t : ℤ) :
    LBIso (tw (tw L (pw L d) t) (pw L d) 1) (pw L (d * (t + 1) + 1)) := by
  refine GlobalTheory.LBAlg.lbIso_of_germs
    (A := tw (tw L (pw L d) t) (pw L d) 1) (B := pw L (d * (t + 1) + 1))
    (fun p => res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.1.1 from fun _ hx => ⟨hx.1, hx.2.1.1⟩) (L.g p.1 p.2.1.1) *
      res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.1.2 from fun _ hx => ⟨hx.1, hx.2.1.2⟩) (L.g p.1 p.2.1.2) ^ (d * t) *
      res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.2 from fun _ hx => ⟨hx.1, hx.2.2⟩) (L.g p.1 p.2.2) ^ d) ?_
  rintro x ⟨a, ⟨b, c⟩, e⟩ ⟨a', ⟨b', c'⟩, e'⟩ ha hp ha' hq
  have hb : x ∈ L.U b := hp.1.1
  have hc : x ∈ L.U c := hp.1.2
  have he : x ∈ L.U e := hp.2
  have hb' : x ∈ L.U b' := hq.1.1
  have hc' : x ∈ L.U c' := hq.1.2
  have he' : x ∈ L.U e' := hq.2
  have inv : ∀ {j j' : L.ι}, x ∈ L.U j → x ∈ L.U j' →
      gm (𝟙 X) x (L.U j' ⊓ L.U j) (L.g j' j) = (gm (𝟙 X) x (L.U j ⊓ L.U j') (L.g j j'))⁻¹ :=
    fun hj hj' => eq_inv_of_mul_eq_one_right
      ((gm_cocycle hL (𝟙 X) x hj hj' hj).trans (gm_self hL (𝟙 X) x hj))
  have rel : ∀ {i i' j j' : L.ι}, x ∈ L.U i → x ∈ L.U i' → x ∈ L.U j → x ∈ L.U j' →
      gm (𝟙 X) x (L.U i ⊓ L.U j) (L.g i j) = gm (𝟙 X) x (L.U i ⊓ L.U i') (L.g i i') *
        gm (𝟙 X) x (L.U i' ⊓ L.U j') (L.g i' j') * (gm (𝟙 X) x (L.U j ⊓ L.U j') (L.g j j'))⁻¹ := by
    intro i i' j j' hi hi' hj hj'
    rw [← gm_cocycle hL (𝟙 X) x hi hi' hj, ← gm_cocycle hL (𝟙 X) x hi' hj' hj, inv hj hj', mul_assoc]
  have sec : ∀ (a₀ b₀ c₀ e₀ : L.ι) (h : (𝟙 X : X ⟶ X) x ∈ (pw L (d * (t + 1) + 1)).U a₀ ⊓
      (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀)),
      gm (𝟙 X) x ((pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀))
        (res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U b₀ from fun _ hx => ⟨hx.1, hx.2.1.1⟩) (L.g a₀ b₀) *
        res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U c₀ from fun _ hx => ⟨hx.1, hx.2.1.2⟩) (L.g a₀ c₀) ^ (d * t) *
        res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U e₀ from fun _ hx => ⟨hx.1, hx.2.2⟩) (L.g a₀ e₀) ^ d) =
      gm (𝟙 X) x (L.U a₀ ⊓ L.U b₀) (L.g a₀ b₀) * gm (𝟙 X) x (L.U a₀ ⊓ L.U c₀) (L.g a₀ c₀) ^ (d * t) *
        gm (𝟙 X) x (L.U a₀ ⊓ L.U e₀) (L.g a₀ e₀) ^ d := by
    intro a₀ b₀ c₀ e₀ h
    rw [map_mul, map_mul, map_zpow, map_zpow, gm_res _ x _ h, gm_res _ x _ h, gm_res _ x _ h]
  have eB : gm (𝟙 X) x ((pw L (d * (t + 1) + 1)).U a ⊓ (pw L (d * (t + 1) + 1)).U a')
      ((pw L (d * (t + 1) + 1)).g a a') = gm (𝟙 X) x (L.U a ⊓ L.U a') (L.g a a') ^ (d * (t + 1) + 1) :=
    map_zpow (gm (𝟙 X) x (L.U a ⊓ L.U a')) (L.g a a') _
  have eA : gm (𝟙 X) x ((tw (tw L (pw L d) t) (pw L d) 1).U ((b, c), e) ⊓
      (tw (tw L (pw L d) t) (pw L d) 1).U ((b', c'), e'))
      ((tw (tw L (pw L d) t) (pw L d) 1).g ((b, c), e) ((b', c'), e')) =
      gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b') * (gm (𝟙 X) x (L.U c ⊓ L.U c') (L.g c c') ^ d) ^ t *
        (gm (𝟙 X) x (L.U e ⊓ L.U e') (L.g e e') ^ d) ^ (1 : ℤ) := by
    have g1 : gm (𝟙 X) x ((pw L d).U c ⊓ (pw L d).U c') ((pw L d).g c c') =
        gm (𝟙 X) x (L.U c ⊓ L.U c') (L.g c c') ^ d := map_zpow _ _ _
    have g2 : gm (𝟙 X) x ((pw L d).U e ⊓ (pw L d).U e') ((pw L d).g e e') =
        gm (𝟙 X) x (L.U e ⊓ L.U e') (L.g e e') ^ d := map_zpow _ _ _
    refine (GlobalTheory.LBAlg.gm_tw (tw L (pw L d) t) (pw L d) 1 (𝟙 X) x ((b, c), e) ((b', c'), e') ⟨hp, hq⟩).trans ?_
    exact congrArg₂ (· * ·) ((GlobalTheory.LBAlg.gm_tw L (pw L d) t (𝟙 X) x (b, c) (b', c') ⟨hp.1, hq.1⟩).trans
      (congrArg₂ (· * ·) rfl (congrArg (· ^ t) g1))) (congrArg (· ^ (1 : ℤ)) g2)
  refine (sec a b c e ⟨ha, hp⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·) eB.symm
    (congrArg (·⁻¹) eA.symm)) (sec a' b' c' e' ⟨ha', hq⟩).symm))
  rw [rel ha ha' hb hb', rel ha ha' hc hc', rel ha ha' he he']
  exact units_identity _ _ _ _ _ _ _ d t

end GlobalTheory.FormalAlg.ConsecPowers

namespace GlobalTheory.FormalAlg.ConsecPowers

theorem exists_veryAmpleBy_pw_and_succ : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∀ c : ℕ, c = d ∨ c = d + 1 → ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw L c)), VeryAmpleBy X.hom (GlobalTheory.AbLaw.pw L c) s := by
  intro R _ X L hL hA
  obtain ⟨d₁, hd₁, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R X L hL).1 hA
  have isLB_pw {Y : Scheme.{0}} {H : LB Y} (hH : H.IsLB) (t : ℤ) :
      (AbLaw.pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have hH := isLB_pw hL (d₁ : ℤ)
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.TwistGen.twist_generated R X.left X.hom _ n s hH hs L hL
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t₀ ≤ (t : ℤ) := ⟨t₀.toNat, Int.self_le_toNat t₀⟩
  obtain ⟨m, u, hu⟩ := ht₀ (t : ℤ) ht
  refine ⟨d₁ * (t + 1), Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), fun c hc => ?_⟩
  rcases hc with rfl | rfl
  · obtain ⟨n', s', hs'⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw R X.left X.hom _ n s hH hs (t + 1) (by omega)
    have e : GlobalTheory.AbLaw.pw L ((d₁ * (t + 1) : ℕ) : ℤ) = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) ((t + 1 : ℕ) : ℤ) := by
      rw [pw_pw]
      push_cast
      rfl
    rw [e]
    exact ⟨n', s', hs'⟩
  · obtain ⟨n', s', hs'⟩ := _root_.GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated R X.left X.hom (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) (tw L (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) (t : ℤ))
      n m s u hH (isLB_tw hL hH _) hs hu
    obtain ⟨s'', hs''⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (isLB_tw (isLB_tw hL hH _) hH 1) (isLB_pw hL _)
      (lbIso_tw_tw hL (d₁ : ℤ) (t : ℤ)) hs'
    have e : ((d₁ * (t + 1) + 1 : ℕ) : ℤ) = (d₁ : ℤ) * ((t : ℤ) + 1) + 1 := by push_cast; ring
    rw [e]
    exact ⟨n', s'', hs''⟩

end GlobalTheory.FormalAlg.ConsecPowers
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLocalRingOfVarietyPointResidueC
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleCoordLocal

open IsLocalRing KaehlerDifferential

theorem linearIndependent_one_tmul_D {k A : Type} [CommRing k] [CommRing A] [IsLocalRing A]
    [Algebra k A] [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k (ResidueField A)]
    {J : Type} (f : J → A) (hf : ∀ j, f j ∈ maximalIdeal A)
    (h : LinearIndependent (ResidueField A) (fun j =>
      ((maximalIdeal A).toCotangent ⟨f j, hf j⟩ : CotangentSpace A))) :
    LinearIndependent (ResidueField A) (fun j => (1 : ResidueField A) ⊗ₜ[A] D k A (f j)) := by
  have hs : Function.Surjective (algebraMap A (ResidueField A)) := residue_surjective
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := k) hs).mpr
    inferInstance
  have hker : maximalIdeal A = RingHom.ker (algebraMap A (ResidueField A)) := ker_residue.symm
  let c := Ideal.Cotangent.equivOfEq _ _ hker
  let e : CotangentSpace A →ₗ[A] ResidueField A ⊗[A] Ω[A⁄k] :=
    kerCotangentToTensor k A (ResidueField A) ∘ₗ c.toLinearMap
  have he : Function.Injective (e.extendScalarsOfSurjective hs) := hinj.comp c.injective
  have := h.map' (e.extendScalarsOfSurjective hs) (LinearMap.ker_eq_bot.2 he)
  have key : ⇑(e.extendScalarsOfSurjective hs) ∘ (fun j =>
      ((maximalIdeal A).toCotangent ⟨f j, hf j⟩ : CotangentSpace A)) =
      fun j => (1 : ResidueField A) ⊗ₜ[A] D k A (f j) := by
    funext j
    simp only [Function.comp_apply, LinearMap.extendScalarsOfSurjective_apply, e,
      LinearMap.comp_apply, LinearEquiv.coe_coe, c]
    rw [Ideal.Cotangent.equivOfEq_toCotangent, kerCotangentToTensor_toCotangent]
    rfl
  rw [key] at this
  exact this

theorem span_one_tmul_D {k A : Type} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hres : Function.Surjective (algebraMap k (ResidueField A))) {r : ℕ} (τ : Fin r → A)
    (hspan : maximalIdeal A = Ideal.span (Set.range τ)) :
    Submodule.span (ResidueField A)
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] D k A (τ i)) = ⊤ := by
  set S := Submodule.span (ResidueField A)
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] D k A (τ i))
  have hτ0 : ∀ i, residue A (τ i) = 0 := fun i =>
    (residue_eq_zero_iff _).2 (hspan ▸ Ideal.subset_span ⟨i, rfl⟩)

  have h1 : ∀ a : A, (1 : ResidueField A) ⊗ₜ[A] D k A a ∈ S := by
    intro a
    obtain ⟨c, hc⟩ := hres (residue A a)
    have hm : a - algebraMap k A c ∈ Ideal.span (Set.range τ) := by
      rw [← hspan, ← residue_eq_zero_iff, map_sub, ← hc]
      rw [IsScalarTower.algebraMap_apply k A (ResidueField A)]
      exact sub_self _
    obtain ⟨β, hβ⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hm
    have hD : D k A a = ∑ i, (β i • D k A (τ i) + τ i • D k A (β i)) := by
      have : D k A a = D k A (a - algebraMap k A c) := by
        rw [map_sub, Derivation.map_algebraMap, sub_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, ← hβ, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Derivation.leibniz, add_comm]
    rw [hD, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      ← algebraMap_smul (ResidueField A) (τ i), ← algebraMap_smul (ResidueField A) (β i)]
    change _ + residue A (τ i) • _ ∈ S
    rw [hτ0, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have h2 : ∀ ω : Ω[A⁄k], (1 : ResidueField A) ⊗ₜ[A] ω ∈ S := by
    intro ω
    have hω : ω ∈ Submodule.span A (Set.range (D k A)) := by
      rw [span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h1 a
    | zero => rw [TensorProduct.tmul_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact S.add_mem hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (ResidueField A) a]
      exact S.smul_mem _ hx
  rw [eq_top_iff]
  intro x hx
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | tmul c ω =>
    have : c ⊗ₜ[A] ω = c • ((1 : ResidueField A) ⊗ₜ[A] ω) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact S.smul_mem _ (h2 ω)
  | add x y hx hy => exact S.add_mem hx hy

end GlobalTheory.EtaleCoordLocal

namespace GlobalTheory.EtaleCoordLocal

open IsLocalRing KaehlerDifferential

theorem exists_coords (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] [Algebra.EssFiniteType k A] [Algebra.FormallySmooth k A]
    (hres : Function.Surjective (algebraMap k (ResidueField A))) :
    ∃ (r : ℕ) (τ : Fin r → A), maximalIdeal A = Ideal.span (Set.range τ) ∧
      ∃ b : Module.Basis (Fin r) A Ω[A⁄k], ∀ i, b i = D k A (τ i) := by
  classical
  haveI : Algebra.FormallySmooth k (ResidueField A) :=
    Algebra.FormallySmooth.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId k (ResidueField A)) ⟨(algebraMap k _).injective, hres⟩)
  let b0 := Module.finBasis (ResidueField A) (CotangentSpace A)
  choose τ' hτ' using fun i => Ideal.toCotangent_surjective (maximalIdeal A) (b0 i)
  have hspan : maximalIdeal A = Ideal.span (Set.range fun i => (τ' i : A)) := by
    have h1 : Submodule.span (ResidueField A) ((maximalIdeal A).toCotangent '' Set.range τ') = ⊤ := by
      rw [← Set.range_comp, show (maximalIdeal A).toCotangent ∘ τ' = ⇑b0 from funext hτ', b0.span_eq]
    rw [CotangentSpace.span_image_eq_top_iff] at h1
    have h2 := congrArg (Submodule.map (maximalIdeal A).subtype) h1
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h2
    exact h2.symm
  refine ⟨_, fun i => (τ' i : A), hspan, ?_⟩
  have hli := linearIndependent_one_tmul_D (k := k) (fun i => (τ' i : A)) (fun i => (τ' i).2)
    (by
      have : (fun i => (maximalIdeal A).toCotangent ⟨(τ' i : A), (τ' i).2⟩) = ⇑b0 := funext hτ'
      rw [this]
      exact b0.linearIndependent)
  have hsp := span_one_tmul_D hres (fun i => (τ' i : A)) hspan
  haveI : Module.FinitePresentation A Ω[A⁄k] := Module.finitePresentation_of_finite A _
  exact Module.exists_basis_of_basis_baseChange (R := A) (fun i => D k A (τ' i : A)) hli hsp
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal A).subtype
      Subtype.val_injective)

theorem formallyEtale_eval₂Hom_of_basis (k A : Type) [CommRing k] [CommRing A] [Algebra k A]
    [Algebra.FormallySmooth k A] {r : ℕ} (τ : Fin r → A) (b : Module.Basis (Fin r) A Ω[A⁄k])
    (hb : ∀ i, b i = D k A (τ i)) : (MvPolynomial.eval₂Hom (algebraMap k A) τ).FormallyEtale := by
  letI := (MvPolynomial.eval₂Hom (algebraMap k A) τ).toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin r) k) A :=
    IsScalarTower.of_algebraMap_eq fun c => (MvPolynomial.eval₂Hom_C _ τ c).symm
  have hX (i : Fin r) : algebraMap (MvPolynomial (Fin r) k) A (MvPolynomial.X i) = τ i :=
    MvPolynomial.eval₂Hom_X' _ τ i
  have he : mapBaseChange k (MvPolynomial (Fin r) k) A =
      (((mvPolynomialBasis k (Fin r)).baseChange A).equiv b (Equiv.refl _)).toLinearMap := by
    refine ((mvPolynomialBasis k (Fin r)).baseChange A).ext fun i => ?_
    rw [EtaleCoordJacobian.mapBaseChange_basis, hX, ← hb]
    simp only [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
  have hbij : Function.Bijective (mapBaseChange k (MvPolynomial (Fin r) k) A) := by
    rw [he]; exact LinearEquiv.bijective _
  have h1 : Subsingleton Ω[A⁄MvPolynomial (Fin r) k] := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    obtain ⟨x, rfl⟩ := map_surjective k (MvPolynomial (Fin r) k) A y
    exact (exact_mapBaseChange_map k (MvPolynomial (Fin r) k) A x).2 (hbij.2 x)
  have h2 : Subsingleton (Algebra.H1Cotangent (MvPolynomial (Fin r) k) A) := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    have h3 : Algebra.H1Cotangent.δ k (MvPolynomial (Fin r) k) A y = 0 := by
      apply hbij.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange k (MvPolynomial (Fin r) k) A _).2 ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ k (MvPolynomial (Fin r) k) A y).1 h3
    rw [Subsingleton.elim x 0, map_zero]
  exact (⟨h1, h2⟩ : Algebra.FormallyEtale (MvPolynomial (Fin r) k) A)

end GlobalTheory.EtaleCoordLocal

namespace GlobalTheory.EtaleCoordLocal

open IsLocalRing

theorem exists_etaleCoords : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (B : Subring κ')
    (hB : IsLocModel (algebraMap ℂ κ') B),
    RatRes (algebraMap ℂ κ') B → ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth →
    ∃ (r : ℕ) (τ : Fin r → B),
      (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) ∧
      (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict B hB.const_mem) τ).FormallyEtale ∧
      TrBasis (algebraMap ℂ κ') (fun i => (τ i : κ')) := by
  intro κ' _ _ B hB hres hsm
  letI := hB.isLocalRing
  let c0 : ℂ →+* B := (algebraMap ℂ κ').codRestrict B hB.const_mem
  letI : Algebra ℂ B := c0.toAlgebra
  haveI : Algebra.EssFiniteType ℂ B := hB.essFiniteType
  haveI : Algebra.FormallySmooth ℂ B := hsm
  haveI : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing ℂ B
  have hres' : Function.Surjective (algebraMap ℂ (ResidueField B)) := by
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := hres x x.2
    refine ⟨a, ?_⟩
    have hn : ¬ IsUnit (x - c0 a) := (nonUnit_iff (R := B) (x - c0 a)).1 ha
    have hm : x - c0 a ∈ maximalIdeal B := (mem_maximalIdeal _).2 hn
    rw [IsScalarTower.algebraMap_apply ℂ B (ResidueField B)]
    have := (residue_eq_zero_iff _).2 hm
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  obtain ⟨r, τ, hspan, b, hb⟩ := exists_coords ℂ B hres'
  refine ⟨r, τ, hspan, formallyEtale_eval₂Hom_of_basis ℂ B τ b hb, ?_⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  ·
    have hmax : maximalIdeal B = ⊥ := by
      rw [hspan, Set.range_eq_empty, Ideal.span_empty]
    have hB0 : ∀ x : B, ∃ a : ℂ, x = c0 a := by
      intro x
      obtain ⟨a, ha⟩ := hres x x.2
      have hn : ¬ IsUnit (x - c0 a) := (nonUnit_iff (R := B) (x - c0 a)).1 ha
      have hm : x - c0 a ∈ maximalIdeal B := (mem_maximalIdeal _).2 hn
      rw [hmax, Ideal.mem_bot, sub_eq_zero] at hm
      exact ⟨a, hm⟩
    have halg : Algebra.IsAlgebraic ℂ κ' := by
      refine ⟨fun f => ?_⟩
      obtain ⟨p, hp, q, hq, hq0, e⟩ := hB.frac f
      obtain ⟨a, ha⟩ := hB0 ⟨p, hp⟩
      obtain ⟨d, hd⟩ := hB0 ⟨q, hq⟩
      have ha' : p = algebraMap ℂ κ' a := congrArg Subtype.val ha
      have hd' : q = algebraMap ℂ κ' d := congrArg Subtype.val hd
      have hf : f = algebraMap ℂ κ' (a / d) := by
        rw [map_div₀, ← ha', ← hd', eq_div_iff hq0, e]
      rw [hf]
      exact isAlgebraic_algebraMap _
    have e : (algebraMap ℂ κ').toAlgebra = (inferInstance : Algebra ℂ κ') :=
      Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [e]
    exact (algebraicIndependent_empty_type : AlgebraicIndependent ℂ fun i : Fin 0 => (τ i : κ')).isTranscendenceBasis_of_trdeg_le_of_finite
      (by rw [trdeg_eq_zero]; exact zero_le)
  · exact trBasis_of_isFreeGen_dForm (algebraMap ℂ κ') B hB r τ hr
      (TopForm.isFreeGen_dForm τ b hb)

end GlobalTheory.EtaleCoordLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteControllingPoints
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem exists_finite_controlling_points : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∃ S : Set X, S.Finite ∧ ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → ∀ τ g : X.functionField, RegAt x τ → (∀ z ∈ S, z ⤳ x → UnitAt z τ) → RegAt x g → RegAt x (g * τ / P.loc 0 1 s i j) → RegAt x (g / P.loc 0 1 s i j) := by
  intro k _ X _ p D hX P s hs hs0
  have : IsNoetherian X := hX.isNoetherian
  have hloc0 : ∀ (i : P.L.B.ι) (j : P.A.B.ι), P.loc 0 1 s i j = s * (P.r' j : X.functionField) := by
    intro i j; simp [Pair.loc]
  have hloc : ∀ x : X, ∃ (V : X.Opens) (j : P.A.B.ι) (_ : IsAffineOpen V) (hx : x ∈ V) (a : Γ(X, V)),
      V ≤ P.A.B.U j ∧ fnOf V (gen_mem hx) a = s * (P.r' j : X.functionField) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (P.L.isLB.cover ▸ Opens.mem_top x : x ∈ ⨆ i, P.L.B.U i)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (P.A.isLB.cover ▸ Opens.mem_top x : x ∈ ⨆ j, P.A.B.U j)
    obtain ⟨c, hc⟩ := hs x i j hi hj
    obtain ⟨U, hxU, f, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf c
    obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show x ∈ U ⊓ P.A.B.U j from ⟨hxU, hj⟩)
    refine ⟨V, j, hV, hxV, resG X (hVW.trans inf_le_left) f, hVW.trans inf_le_right, ?_⟩
    rw [fnOf_resG, ← algebraMap_germ hxU, hc, hloc0]
  choose V jj hV hxV a hVj ha using hloc
  have hne : ∀ y, fnOf (V y) (gen_mem (hxV y)) (a y) ≠ 0 := by
    intro y; rw [ha]; exact mul_ne_zero hs0 (P.r' (jj y)).ne_zero
  choose T hTfin hT using fun y => _root_.GlobalTheory.exists_finite_points_regAt_div_of_affine X (V y) (hV y) (gen_mem (hxV y)) (a y) (hne y)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set X)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hxV y⟩)
  refine ⟨⋃ y ∈ t, T y, t.finite_toSet.biUnion fun y _ => hTfin y, ?_⟩
  intro x i j hi hj τ g hτ hS hg hgτ
  obtain ⟨y, hyt, hxy⟩ : ∃ y ∈ t, x ∈ V y := by
    have := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, h⟩ := this
    exact ⟨y, hy, h⟩
  have hxj' : x ∈ P.A.B.U j ⊓ P.A.B.U (jj y) := ⟨hj, hVj y hxy⟩
  set w : X.functionField := fnOf _ (gen_mem hxj') (P.A.B.g j (jj y) : Γ(X, P.A.B.U j ⊓ P.A.B.U (jj y))) with hw
  have hwu : UnitAt x w := unitAt_fnOf hxj' _ _
  have hw0 : w ≠ 0 := hwu.ne_zero
  have hrel : P.loc 0 1 s i j = fnOf (V y) (gen_mem (hxV y)) (a y) * w := by
    rw [hloc0, ha, P.hr' j (jj y) (gen_mem hxj')]; ring
  rw [hrel] at hgτ ⊢
  set σ := fnOf (V y) (gen_mem (hxV y)) (a y)
  have h1 : RegAt x (g * τ / σ) := by
    have := hgτ.mul hwu.regAt
    convert this using 1
    field_simp
  have h2 := hT y x hxy τ g hτ (fun z hz hzx => hS z (Set.mem_biUnion hyt hz) hzx) hg h1
  have := h2.mul hwu.inv.regAt
  convert this using 1
  rw [div_mul_eq_div_div, div_eq_mul_inv (g / σ)]

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldEquivOpenImmersionSpecStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionFieldEquiv_openImmersionSpec : ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] (Y : Scheme.{0}) [IsIntegral Y]
    (p : Y ⟶ Sp ℂ) (j : Sp S ⟶ Y) [IsOpenImmersion j], j ≫ p = spMap (algebraMap ℂ S) →
    ∃ e : Y.functionField ≃+* FractionRing S,
      (∀ a : ℂ, e (GlobalTheory.Cartier.constFn p a) = algebraMap ℂ (FractionRing S) a) ∧
      ∀ (q : PrimeSpectrum S) (g : FractionRing S), g ∈ (locRing (j.base q)).map e.toRingHom ↔
        ∃ a b : S, b ∉ q.asIdeal ∧ g * algebraMap S (FractionRing S) b = algebraMap S (FractionRing S) a := by
  first | exact @GlobalTheory.OpenSpecField.exists_fieldEquiv | exact GlobalTheory.OpenSpecField.exists_fieldEquiv | (intros; apply GlobalTheory.OpenSpecField.exists_fieldEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMulZpowUniformiserTmulStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_mul_zpow_uniformiser_tmul : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  Function.Injective (algebraMap (K ⊗[ℂ] κ') L) → Irreducible t →
  ∀ g : K, g ≠ 0 → ∃ q : locAt (L := L) 𝔭, IsUnit q ∧
    algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ E.ord g := by
  first | exact @GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul | exact GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul | (intros; apply GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieOneParameterIsRealOneParamSubgroupAdelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lie_one_parameter_isRealOneParamSubgroupAdelic : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  first | exact @GlobalTheory.UAut.isRealLine_oneP | exact GlobalTheory.UAut.isRealLine_oneP | (intros; apply GlobalTheory.UAut.isRealLine_oneP <;> assumption)
end

