module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VirtualCharacterCosetNormOneSingle
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem int_comb_unit_norm_single {ι G : Type} [Fintype ι] [Fintype G] (l : ℕ) (hl : l.Prime)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ l) (f : ι → G → ℂ) (c : ι → ℤ) (R : ι → ι → Prop)
    (hR : Equivalence R) (hG : (Fintype.card G : ℂ) ≠ 0)
    (hnorm : ∀ i, ∑ g, f i g * star (f i g) = Fintype.card G)
    (horth : ∀ i j, ∑ g, f i g * star (f j g) ≠ 0 → R i j)
    (hrel : ∀ i j, R i j → ∃ a < l, ∀ g, f i g = ζ ^ a * f j g)
    (hsum : ∑ g, (∑ i, (c i : ℂ) * f i g) * star (∑ i, (c i : ℂ) * f i g) = Fintype.card G) :
    ∃ i₀ e, ∀ g, ∑ i, (c i : ℂ) * f i g = e * f i₀ g := by
  letI S : Setoid ι := ⟨R, hR⟩
  let rep : Quotient S → ι := Quotient.out
  have hrep : ∀ t : ι, R t (rep ⟦t⟧) := fun t => hR.symm (Quotient.mk_out t)
  choose a ha hfa using fun t => hrel t _ (hrep t)
  let n : Quotient S → ℕ → ℤ := fun i b => ∑ t, if (⟦t⟧ : Quotient S) = i ∧ a t = b then c t else 0
  let C : Quotient S → ℂ := fun i => ∑ b ∈ Finset.range l, (n i b : ℂ) * ζ ^ b
  have hF : ∀ g, ∑ t, (c t : ℂ) * f t g = ∑ i, C i * f (rep i) g := by
    intro g
    have h1 : ∀ i, C i * f (rep i) g =
        ∑ t, if (⟦t⟧ : Quotient S) = i then (c t : ℂ) * (ζ ^ a t * f (rep i) g) else 0 := by
      intro i
      simp only [C, n, Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h : (⟦t⟧ : Quotient S) = i
      · simp only [h, true_and, if_true]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_range, ha t, if_true]
        ring
      · simp [h]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq]
    simp [hfa t g]
  have hort : ∀ i j, i ≠ j → ∑ g, f (rep i) g * star (f (rep j) g) = 0 := by
    intro i j hij
    by_contra h
    apply hij
    rw [← Quotient.out_eq i, ← Quotient.out_eq j]
    exact Quotient.sound (horth _ _ h)
  have hexp : ∀ g, (∑ i, C i * f (rep i) g) * star (∑ i, C i * f (rep i) g) =
      ∑ i, ∑ j, C i * star (C j) * (f (rep i) g * star (f (rep j) g)) := by
    intro g
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
    ring
  have h2 : ∑ g, (∑ i, C i * f (rep i) g) * star (∑ i, C i * f (rep i) g) =
      (∑ i, C i * star (C i)) * Fintype.card G := by
    simp_rw [hexp]
    rw [Finset.sum_comm]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single i]
    · rw [← Finset.mul_sum, hnorm]
    · intro j _ hji
      rw [← Finset.mul_sum, hort i j (Ne.symm hji), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp_rw [hF] at hsum
  rw [h2] at hsum
  have h3 : ∑ i, C i * star (C i) = 1 := by
    have := hsum
    rw [← one_mul (Fintype.card G : ℂ)] at this
    exact mul_right_cancel₀ hG (by simpa using this)
  obtain ⟨i₀, -, hi₀⟩ := GlobalTheory.T.cyclotomic_sum_normSq_eq_one_single_nonzero l ζ hl hζ (Quotient S) Finset.univ n h3
  refine ⟨rep i₀, C i₀, fun g => ?_⟩
  rw [hF, Finset.sum_eq_single i₀]
  · intro i _ hi
    have : C i = 0 := hi₀ i (Finset.mem_univ i) hi
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i₀) h

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem virt_coset_norm_one_single : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ]
    (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ),
    ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) →
    ∃ (χ : G ⋊[φ] Γ → ℂ) (e : ℂ), IsIrrChar ℂ ℂ χ ∧ IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧
      ∀ δ, X (inl δ * inr s) = e * χ (inl δ * inr s) := by
  intro G Γ _ _ _ _ φ s hp hs X hX hXn
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Finite (G ⋊[φ] Γ) :=
    Finite.of_injective (fun x : G ⋊[φ] Γ => (x.left, x.right))
      (fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  obtain ⟨c, hirr, hXc, -⟩ := GlobalTheory.BI.virt_expand (G ⋊[φ] Γ) X hX
  let T := c.support.filter (fun χ : G ⋊[φ] Γ → ℂ => ¬ ∀ δ, χ (inl δ * inr s) = 0)
  have hT : ∀ t : T, IsIrrChar ℂ ℂ t.1 ∧ ¬ ∀ δ, t.1 (inl δ * inr s) = 0 := fun t =>
    ⟨hirr _ (Finset.mem_filter.1 t.2).1, (Finset.mem_filter.1 t.2).2⟩
  let f : T → G → ℂ := fun t g => t.1 (inl g * inr s)
  have hX' : ∀ g, X (inl g * inr s) = ∑ t : T, (c t.1 : ℂ) * f t g := by
    intro g
    rw [hXc, Finsupp.sum, Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
    rw [Finset.sum_coe_sort T (fun χ => (c χ : ℂ) * χ (inl g * inr s))]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ _ => ?_
    split_ifs with h
    · rw [h g, mul_zero]
    · rfl
  let R : T → T → Prop := fun t u => ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧
    ∀ x, t.1 x = u.1 x * (η x : ℂ)
  have hR : Equivalence R := by
    refine ⟨fun t => ⟨1, fun g => rfl, fun x => by simp⟩, ?_, ?_⟩
    · rintro t u ⟨η, h1, h2⟩
      refine ⟨η⁻¹, fun g => by simp [h1 g], fun x => ?_⟩
      rw [h2 x, MonoidHom.inv_apply, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        mul_one]
    · rintro t u v ⟨η, h1, h2⟩ ⟨η', h1', h2'⟩
      refine ⟨η' * η, fun g => by simp [h1 g, h1' g], fun x => ?_⟩
      rw [h2 x, h2' x, MonoidHom.mul_apply, Units.val_mul, mul_assoc]
  haveI : NeZero (Nat.card Γ) := ⟨hp.ne_zero⟩
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  have hnorm : ∀ t, ∑ g, f t g * star (f t g) = Fintype.card G := by
    intro t
    rcases GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter G Γ φ s hp hs t.1 (hT t).1 with h | ⟨-, h⟩
    · exact absurd h (hT t).2
    · rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card] at h
      exact h
  have horth : ∀ t u, ∑ g, f t g * star (f u g) ≠ 0 → R t u := by
    intro t u h
    rcases GlobalTheory.T.semidirect_coset_pairing_eq_zero_or_twist G Γ φ s hp hs t.1 u.1 (hT t).1 (hT u).1 with h' | h'
    · rw [finsum_eq_sum_of_fintype] at h'
      exact absurd h' h
    · exact h'
  have hrel : ∀ t u, R t u → ∃ a < Nat.card Γ, ∀ g,
      f t g = Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ)) ^ a * f u g := by
    rintro t u ⟨η, h1, h2⟩
    have hpow : ((η (inr s) : ℂˣ) : ℂ) ^ Nat.card Γ = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one,
        Units.val_one]
    obtain ⟨a, ha, hb⟩ := hζ.eq_pow_of_pow_eq_one hpow
    refine ⟨a, ha, fun g => ?_⟩
    simp only [f]
    rw [h2, map_mul, h1, one_mul, hb, mul_comm]
  have hsum : ∑ g, (∑ t : T, (c t.1 : ℂ) * f t g) * star (∑ t : T, (c t.1 : ℂ) * f t g) =
      Fintype.card G := by
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card] at hXn
    simp_rw [← hX']
    exact hXn
  obtain ⟨t₀, e, he⟩ := int_comb_unit_norm_single (Nat.card Γ) hp _ hζ f (fun t => c t.1) R hR
    (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hnorm horth hrel hsum
  refine ⟨t₀.1, e, (hT t₀).1, ?_, fun δ => by rw [hX', he]⟩
  rcases GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter G Γ φ s hp hs t₀.1 (hT t₀).1 with h | ⟨h, -⟩
  · exact absurd h (hT t₀).2
  · exact h

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgePropertyFromFibres
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.Wedge

def alt2 {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ x, f x x = 0) : M [⋀^Fin 2]→ₗ[R] N where
  toFun v := f (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp
  map_update_smul' v i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j <;> simp_all

theorem alt2_apply {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ x, f x x = 0) (v : Fin 2 → M) : alt2 f hf v = f (v 0) (v 1) := rfl

theorem bijective_of_fibres {R B C : Type} [CommRing R] [AddCommGroup B] [Module R B] [AddCommGroup C]
    [Module R C] [Module.Finite R B] [Module.Finite R C] [Module.Projective R C] (l : B →ₗ[R] C)
    (h : ∀ q : PrimeSpectrum R, Function.Bijective (l.baseChange q.asIdeal.ResidueField)) :
    Function.Bijective l := by
  have hlt : ∀ q : PrimeSpectrum R, Function.Bijective (l.lTensor q.asIdeal.ResidueField) := by
    intro q
    have e : ⇑(l.lTensor q.asIdeal.ResidueField) = ⇑(l.baseChange q.asIdeal.ResidueField) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    rw [e]; exact h q
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := GlobalTheory.split_injective_of_forall_lTensor_residueField_injective l
      (fun m hm => (hlt ⟨m, hm.isPrime⟩).1)
    exact Function.LeftInverse.injective (g := r) fun x => LinearMap.congr_fun hr x
  · have hQ : Subsingleton (C ⧸ LinearMap.range l) := by
      apply GlobalTheory.subsingleton_of_residueField_fibres R
      intro q
      have h2 := (hlt q).2
      have h3 : Function.Surjective ((LinearMap.range l).mkQ.lTensor q.asIdeal.ResidueField) :=
        LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
      refine ⟨fun a b => ?_⟩
      have key : ∀ a : q.asIdeal.ResidueField ⊗[R] (C ⧸ LinearMap.range l), a = 0 := by
        intro a
        obtain ⟨x, rfl⟩ := h3 a
        obtain ⟨y, rfl⟩ := h2 x
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.range_mkQ_comp]
        simp
      rw [key a, key b]
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    exact hQ

end GlobalTheory.AbCoh.Wedge

namespace GlobalTheory.AbCoh.Wedge

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

def wedgeMap (hsq : ∀ x : HO1 s, cup _ x x = 0) : ⋀[R]^2 (HO1 s) →ₗ[R] HO2 s :=
  exteriorPower.alternatingMapLinearEquiv (alt2 (cup _) hsq)

theorem wedgeMap_ιMulti (hsq : ∀ x : HO1 s, cup _ x x = 0) (v : Fin 2 → HO1 s) :
    wedgeMap s hsq (exteriorPower.ιMulti R 2 v) = cup _ (v 0) (v 1) := by
  simp only [wedgeMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, alt2_apply]

theorem baseChange_wedgeMap_bijective (hsq : ∀ x : HO1 s, cup _ x x = 0) (k : Type) [CommRing k]
    [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X)
    (hpb : φ ≫ s = s' ≫ spMap (algebraMap R k))
    (e1 : k ⊗[R] HO1 s ≃ₗ[k] HO1 s') (he1 : ∀ c, e1 (1 ⊗ₜ c) = pullHO1 hpb c)
    (e2 : k ⊗[R] HO2 s ≃ₗ[k] HO2 s') (he2 : ∀ c, e2 (1 ⊗ₜ c) = pullHO2 hpb c)
    (w : ⋀[k]^2 (CatCoh.H1 (OAff s')) ≃ₗ[k] CatCoh.H2 (OAff s'))
    (hw : ∀ a b, w (exteriorPower.ιMulti k 2 ![a, b]) = cup _ a b) :
    Function.Bijective ((wedgeMap s hsq).baseChange k) := by
  have hcup := ((_root_.GlobalTheory.AbCoh.pull_comp_cup_id).2.1 R k X X' s s' (algebraMap R k) φ hpb).1
  let β := (GlobalTheory.TopForm.isBaseChange_exteriorPower (TensorProduct.isBaseChange R (HO1 s) k) 2).equiv
  let T : k ⊗[R] ⋀[R]^2 (HO1 s) →ₗ[k] k ⊗[R] HO2 s :=
    e2.symm.toLinearMap ∘ₗ w.toLinearMap ∘ₗ exteriorPower.map 2 e1.toLinearMap ∘ₗ β.toLinearMap
  have hT : T = (wedgeMap s hsq).baseChange k := by
    refine TensorProduct.AlgebraTensorModule.ext fun c x => ?_
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul]
    congr 1
    have hl : (T.restrictScalars R) ∘ₗ TensorProduct.mk R k _ 1 =
        (((wedgeMap s hsq).baseChange k).restrictScalars R) ∘ₗ TensorProduct.mk R k _ 1 := by
      apply exteriorPower.linearMap_ext
      ext v
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply, TensorProduct.mk_apply, LinearMap.baseChange_tmul,
        wedgeMap_ιMulti, T, LinearEquiv.coe_coe, β, IsBaseChange.equiv_tmul, one_smul,
        GlobalTheory.exteriorPowerMapOver_ιMulti, exteriorPower.map_apply_ιMulti]
      have hv : (⇑e1 ∘ fun i => (1 : k) ⊗ₜ[R] v i) = ![pullHO1 hpb (v 0), pullHO1 hpb (v 1)] := by
        funext i; fin_cases i <;> simp [he1]
      rw [hv, hw, LinearEquiv.symm_apply_eq, he2, hcup]
    exact LinearMap.congr_fun hl x
  rw [← hT]
  have hm : Function.Bijective (exteriorPower.map 2 e1.toLinearMap) := by
    refine Function.bijective_iff_has_inverse.2 ⟨exteriorPower.map 2 e1.symm.toLinearMap, ?_, ?_⟩
    · intro x
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
      simp [exteriorPower.map_id]
    · intro x
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
      simp [exteriorPower.map_id]
  exact e2.symm.bijective.comp (w.bijective.comp (hm.comp β.bijective))

end GlobalTheory.AbCoh.Wedge

namespace GlobalTheory.AbCoh.Wedge

theorem wedgeO_of_fibres : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Module.Finite R (HO1 s) → Module.Projective R (HO1 s) → Module.Finite R (HO2 s) → Module.Projective R (HO2 s) → StructureSheafH1BaseChange s → StructureSheafH2BaseChange s → (∀ x : HO1 s, cup _ x x = 0) → (∀ (k : Type) [Field k] [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R k))), WedgeO (OAff s')) → WedgeO (OAff s) := by
  intro R _ X s hF1 hP1 hF2 hP2 hB1 hB2 hsq hfib
  have hbij : Function.Bijective (wedgeMap s hsq) := by
    refine bijective_of_fibres _ fun q => ?_
    obtain ⟨X', s', φ, hpb⟩ : ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp q.asIdeal.ResidueField) (φ : X' ⟶ X),
        IsPullback φ s' s (spMap (algebraMap R q.asIdeal.ResidueField)) :=
      ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
    obtain ⟨e1, he1⟩ := hB1 _ _ _ _ hpb
    obtain ⟨e2, he2⟩ := hB2 _ _ _ _ hpb
    obtain ⟨w, hw⟩ := hfib _ _ _ _ hpb
    exact baseChange_wedgeMap_bijective s hsq _ X' s' φ hpb.w e1 he1 e2 he2 w hw
  exact ⟨LinearEquiv.ofBijective _ hbij, fun a b => by
    rw [LinearEquiv.ofBijective_apply, wedgeMap_ιMulti]; rfl⟩

end GlobalTheory.AbCoh.Wedge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WpQTrivRight
section
noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex

namespace GlobalTheory.SympQ

variable {O : Type} [CommRing O] (N : NumD O)

def trivHom (k : ℕ) : Multiplicative N.X →* N.QT k where
  toFun z := N.qTriv k z.toAdd
  map_one' := Subtype.ext (Prod.ext (by simp [NumD.qTriv]) (by simp [NumD.qTriv, N.io_zero]))
  map_mul' a b := Subtype.ext (Prod.ext (by simp [NumD.qTriv, smul_add]) (by simp [NumD.qTriv, N.io_add]))

abbrev Qq (k : ℕ) : Type := N.QT k ⧸ (trivHom N k).range

theorem qEq_iff_mk_eq {k : ℕ} (p p' : N.QT k) : N.QEq p p' ↔ (QuotientGroup.mk p : Qq N k) = QuotientGroup.mk p' := by
  rw [N.qEq_iff, QuotientGroup.eq]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Multiplicative.ofAdd z, by simp [trivHom]⟩
  · rintro ⟨z, hz⟩
    refine ⟨z.toAdd, ?_⟩
    change N.qTriv k z.toAdd = p⁻¹ * p' at hz
    rw [hz, mul_inv_cancel_left]

def pushRep (M n : ℕ) : N.QT M →* N.QT n :=
  if h : n ∣ M then
    { toFun := fun p => ⟨(p.1.1, p.1.2 ^ (M / n)), by
        rw [NumD.mem_QT, ← pow_mul, Nat.div_mul_cancel h]
        exact p.2⟩
      map_one' := Subtype.ext (Prod.ext rfl (by simp))
      map_mul' := fun p q => Subtype.ext (Prod.ext rfl (by simp [mul_pow])) }
  else 1

theorem pushRep_fst {M n : ℕ} (h : n ∣ M) (p : N.QT M) : (pushRep N M n p).1.1 = p.1.1 := by
  simp [pushRep, h]

theorem pushRep_snd {M n : ℕ} (h : n ∣ M) (p : N.QT M) : (pushRep N M n p).1.2 = p.1.2 ^ (M / n) := by
  simp [pushRep, h]

theorem pushRep_triv (M n : ℕ) : (trivHom N M).range ≤ (trivHom N n).range.comap (pushRep N M n) := by
  rintro _ ⟨z, rfl⟩
  by_cases h : n ∣ M
  · refine ⟨Multiplicative.ofAdd ((M / n) • z.toAdd), Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp only [trivHom, MonoidHom.coe_mk, OneHom.coe_mk, NumD.qTriv, toAdd_ofAdd]
      rw [pushRep_fst N h, smul_smul, Nat.mul_div_cancel' h]
    · simp only [trivHom, MonoidHom.coe_mk, OneHom.coe_mk, NumD.qTriv, toAdd_ofAdd]
      rw [pushRep_snd N h, N.io_nsmul]
  · simp [pushRep, h]

def pushQ (M n : ℕ) : Qq N M →* Qq N n := QuotientGroup.map _ _ (pushRep N M n) (pushRep_triv N M n)

theorem pushQ_mk (M n : ℕ) (p : N.QT M) :
    pushQ N M n (QuotientGroup.mk p) = QuotientGroup.mk (pushRep N M n p) := rfl

theorem wp_qTriv_right {k : ℕ} (p : N.QT k) (z : N.X) : N.wp p (N.qTriv k z) = 1 := by
  rw [← inv_inj, ← NumD.wp_swap, WpPairing.wp_qTriv, inv_one]

theorem wp_congr {k : ℕ} {p p' q q' : N.QT k} (hp : N.QEq p p') (hq : N.QEq q q') : N.wp p q = N.wp p' q' := by
  obtain ⟨z, rfl⟩ := (N.qEq_iff _ _).1 hp
  obtain ⟨w, rfl⟩ := (N.qEq_iff _ _).1 hq
  rw [WpPairing.wp_mul_left, WpPairing.wp_mul_right, WpPairing.wp_mul_right, WpPairing.wp_qTriv,
    WpPairing.wp_qTriv, wp_qTriv_right]
  simp

def wpQ (k : ℕ) (x y : Qq N k) : Oˣ :=
  Quotient.liftOn₂' x y (fun p q => N.wp p q) fun p q p' q' hp hq =>
    wp_congr N ((qEq_iff_mk_eq N _ _).2 (Quotient.sound' hp)) ((qEq_iff_mk_eq N _ _).2 (Quotient.sound' hq))

theorem wpQ_mk (k : ℕ) (p q : N.QT k) : wpQ N k (QuotientGroup.mk p) (QuotientGroup.mk q) = N.wp p q := rfl

end GlobalTheory.SympQ
end
end

