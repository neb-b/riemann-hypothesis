module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0757

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.GroupStep
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem relIndex_ker_prime {Γ : Type} [Group Γ] (H H' : Subgroup Γ) (s : Γ →* ℂˣ) (p : ℕ) (hp : p.Prime)
    (hH' : ∀ g, g ∈ H' ↔ g ∈ H ∧ s g = 1) (hs : ∀ g ∈ H, s g ^ p = 1) (τ : Γ) (hτ : τ ∈ H) (hτs : s τ ≠ 1) :
    (H'.relIndex H).Prime := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let f : H →* ℂˣ := s.comp H.subtype
  have hker : f.ker = H'.subgroupOf H := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hH']
    simp [f]
  have hidx : H'.relIndex H = Nat.card f.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hle : f.range ≤ rootsOfUnity p ℂ := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    exact hs g g.2
  have hcard : Nat.card (rootsOfUnity p ℂ) = p := by
    exact Complex.card_rootsOfUnity p
  have hdvd : Nat.card f.range ∣ p := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hcard] at this
  have hne : Nat.card f.range ≠ 1 := by
    intro h1
    have hbot : f.range = ⊥ := by
      haveI : Finite (rootsOfUnity p ℂ) := inferInstance
      exact (Subgroup.eq_bot_iff_card _).2 h1
    have : f ⟨τ, hτ⟩ ∈ f.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hτs this
  rw [hidx]
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact absurd h hne
  · rwa [h]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.groupStep :
    GroupStep := by
  intro Γ _ Gd P D Pl Dc I hI hinf hmono hpsi hstep H₀ r hH₀ hP hr n hn hrn
  have hpowk : ∀ (s : Γ →* ℂˣ) (k : ℕ), Gd s.ker → Gd (s ^ k).ker := by
    intro s k hs
    refine hmono _ _ (fun g hg => ?_) hs
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.pow_apply, hg, one_pow]
  have key : ∀ n : ℕ, 0 < n → ∀ r : Γ →* ℂˣ, Gd r.ker → P (H₀ ⊓ (r ^ n).ker) →
      ∃ r' : Γ →* ℂˣ, Gd r'.ker ∧ (∀ g ∈ D, r' g = r g) ∧ P (H₀ ⊓ r'.ker) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn r hr hP
      rcases Nat.lt_or_ge 1 n with h1 | h1
      swap
      · have hn1 : n = 1 := by omega
        subst hn1
        exact ⟨r, hr, fun _ _ => rfl, by simpa using hP⟩
      obtain ⟨p, hp, n', rfl⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      have hn' : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hlt : n' < p * n' := by
        have := hp.two_le
        nlinarith
      obtain ⟨ψ, hψk, hψn, hψD, u, hDc, τ, hτ, hτo⟩ := hpsi (H₀ ⊓ r.ker) (hinf _ _ hH₀ hr) (p * n') hn
      have hr1 : Gd (r * ψ).ker := by
        refine hmono _ _ (fun g hg => ?_) (hinf _ _ hr hψk)
        have h1 : r g = 1 := hg.1
        have h2 : ψ g = 1 := hg.2
        rw [MonoidHom.mem_ker, MonoidHom.mul_apply, h1, h2, one_mul]
      have hr1n : (r * ψ) ^ (p * n') = r ^ (p * n') := by
        rw [mul_pow, hψn, mul_one]
      have hτU : τ ∈ H₀ ⊓ r.ker := hDc (hI u hτ)
      have hτr : r τ = 1 := hτU.2
      have hGH : Gd (H₀ ⊓ (r ^ (p * n')).ker) := hinf _ _ hH₀ (hpowk _ _ hr)
      have hGH' : Gd (H₀ ⊓ ((r * ψ) ^ n').ker) := hinf _ _ hH₀ (hpowk _ _ hr1)
      have hval : ∀ g, ((r * ψ) ^ n') g ^ p = (r ^ (p * n')) g := by
        intro g
        rw [← hr1n, MonoidHom.pow_apply, MonoidHom.pow_apply, ← pow_mul, mul_comm n' p]
      have hle : H₀ ⊓ ((r * ψ) ^ n').ker ≤ H₀ ⊓ (r ^ (p * n')).ker := by
        intro g hg
        refine ⟨hg.1, ?_⟩
        have h1 : ((r * ψ) ^ n') g = 1 := hg.2
        show (r ^ (p * n')) g = 1
        rw [← hval, h1, one_pow]
      have hUH : H₀ ⊓ r.ker ≤ H₀ ⊓ (r ^ (p * n')).ker := by
        intro g hg
        refine ⟨hg.1, ?_⟩
        have h1 : r g = 1 := hg.2
        show (r ^ (p * n')) g = 1
        rw [MonoidHom.pow_apply, h1, one_pow]
      have hτs : ((r * ψ) ^ n') τ ≠ 1 := by
        intro h
        rw [MonoidHom.pow_apply, MonoidHom.mul_apply, hτr, one_mul] at h
        have := Nat.le_of_dvd hn' (orderOf_dvd_of_pow_eq_one h)
        omega
      have hprime : ((H₀ ⊓ ((r * ψ) ^ n').ker).relIndex (H₀ ⊓ (r ^ (p * n')).ker)).Prime := by
        refine relIndex_ker_prime _ _ ((r * ψ) ^ n') p hp (fun g => ?_) (fun g hg => ?_) τ (hUH hτU) hτs
        · constructor
          · intro hg
            exact ⟨hle hg, hg.2⟩
          · rintro ⟨hg, hs⟩
            exact ⟨hg.1, hs⟩
        · have h1 : (r ^ (p * n')) g = 1 := hg.2
          rw [hval, h1]
      have hP' : P (H₀ ⊓ ((r * ψ) ^ n').ker) :=
        hstep _ _ u hGH hGH' hP hle hprime (fun x hx => hUH (hDc hx))
          ⟨τ, hτ, fun h => hτs h.2⟩
      obtain ⟨r', h1, h2, h3⟩ := ih n' hlt hn' (r * ψ) hr1 hP'
      refine ⟨r', h1, fun g hg => ?_, h3⟩
      rw [h2 g hg, MonoidHom.mul_apply, hψD g hg, mul_one]
  refine key n hn r hr ?_
  rw [hrn, MonoidHom.ker_one, inf_top_eq]
  exact hP
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InclOf
section
noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem fixingSubgroup_fieldRange {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (K : Type) [Field K]
    [Algebra E K] [Algebra K Ω] [IsScalarTower E K Ω] :
    (IsScalarTower.toAlgHom E K Ω).fieldRange.fixingSubgroup = fixGrp E Ω K := by
  ext g
  rw [mem_fixGrp, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x
    exact h _ ⟨x, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    exact h x

theorem inclOf : InclOf := by
  intro E Ω _ _ _ _ _ _ X Y hXY
  have hGal : IsGalois E Ω := inferInstance
  set f := IsScalarTower.toAlgHom E X.K Ω
  set g := IsScalarTower.toAlgHom E Y.K Ω
  have hX := fixingSubgroup_fieldRange (E := E) (Ω := Ω) X.K
  have hY := fixingSubgroup_fieldRange (E := E) (Ω := Ω) Y.K
  have hle : f.fieldRange ≤ g.fieldRange := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup f.fieldRange,
      ← InfiniteGalois.fixedField_fixingSubgroup g.fieldRange]
    apply IntermediateField.fixedField_le
    rw [hX, hY]
    exact hXY
  set eX := AlgEquiv.ofInjectiveField f
  set eY := AlgEquiv.ofInjectiveField g
  set φ : X.K →ₐ[E] Y.K := (eY.symm.toAlgHom.comp (IntermediateField.inclusion hle)).comp eX.toAlgHom
  have hφ : ∀ x : X.K, g (φ x) = f x := by
    intro x
    have h1 : (eY (φ x) : Ω) = g (φ x) := rfl
    rw [← h1]
    have h2 : eY (φ x) = IntermediateField.inclusion hle (eX x) := eY.apply_symm_apply _
    rw [h2]
    rfl
  letI alg : Algebra X.K Y.K := φ.toRingHom.toAlgebra
  have t1 : IsScalarTower E X.K Y.K := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  have t2 : IsScalarTower X.K Y.K Ω := IsScalarTower.of_algebraMap_eq (fun x => (hφ x).symm)
  refine ⟨alg, t1, t2, IsGalois.tower_top_of_isGalois E X.K Y.K, ?_⟩
  rw [← hX, ← hY]
  have iX := IntermediateField.finrank_eq_fixingSubgroup_index Ω f.fieldRange
  have iY := IntermediateField.finrank_eq_fixingSubgroup_index Ω g.fieldRange
  have fX : Module.finrank E X.K = Module.finrank E f.fieldRange := eX.toLinearEquiv.finrank_eq
  have fY : Module.finrank E Y.K = Module.finrank E g.fieldRange := eY.toLinearEquiv.finrank_eq
  have tw := Module.finrank_mul_finrank E X.K Y.K
  have hsub : g.fieldRange.fixingSubgroup ≤ f.fieldRange.fixingSubgroup := by
    rw [hX, hY]; exact hXY
  have rel := Subgroup.relIndex_mul_index hsub
  haveI : FiniteDimensional E X.K := Module.Finite.of_restrictScalars_finite ℚ E X.K
  have hpos : 0 < Module.finrank E X.K := Module.finrank_pos
  rw [fX, iX] at tw hpos
  rw [fY, iY, ← rel] at tw
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [mul_comm] at tw; exact tw)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGen
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

section

variable {Ω : Type} [Field Ω] (A : ValuationSubring Ω)

private theorem val_root (x : Ω) {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : A.valuation x = 1 := by
  have : A.valuation x ^ n = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le' hn).1 this

private theorem val_one_sub_pow_le {ζ : Ω} (hζ : A.valuation ζ ≤ 1) (j : ℕ) :
    A.valuation (1 - ζ ^ j) ≤ A.valuation (1 - ζ) := by
  rw [← mul_neg_geom_sum, map_mul]
  have : A.valuation (∑ i ∈ Finset.range j, ζ ^ i) ≤ 1 :=
    Valuation.map_sum_le _ (fun i _ => by rw [map_pow]; exact pow_le_one' hζ i)
  exact mul_le_of_le_one_right' this

private theorem val_p {p : ℕ} (hp : p.Prime) {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) :
    A.valuation (1 - ζ) ^ (p - 1) = A.valuation ((p : ℕ) : Ω) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hall : ∀ μ ∈ primitiveRoots p Ω, A.valuation (1 - μ) = A.valuation (1 - ζ) := by
    intro μ hμ
    rw [mem_primitiveRoots hp.pos] at hμ
    have hμ1 : A.valuation μ ≤ 1 := (val_root A μ hp.ne_zero hμ.pow_eq_one).le
    have hζ1 : A.valuation ζ ≤ 1 := (val_root A ζ hp.ne_zero hζ.pow_eq_one).le
    obtain ⟨k, _, hk⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
    obtain ⟨l, _, hl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    apply le_antisymm
    · rw [← hl]
      exact val_one_sub_pow_le A hζ1 l
    · rw [← hk]
      exact val_one_sub_pow_le A hμ1 k
  have hprod : ((p : ℕ) : Ω) = ∏ μ ∈ primitiveRoots p Ω, (1 - μ) := by
    have h := congrArg (Polynomial.eval (1 : Ω)) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at h
    simpa using h
  rw [hprod, map_prod, Finset.prod_congr rfl hall, Finset.prod_const, hζ.card_primitiveRoots,
    Nat.totient_prime hp]

private theorem val_pow_sub_pow_lt {x y : Ω} (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1)
    (h : A.valuation (x - y) < 1) (e : ℕ) : A.valuation (x ^ e - y ^ e) < 1 := by
  rw [← geom_sum₂_mul, map_mul]
  have : A.valuation (∑ i ∈ Finset.range e, x ^ i * y ^ (e - 1 - i)) ≤ 1 :=
    Valuation.map_sum_le _ (fun i _ => by
      rw [map_mul, map_pow, map_pow]; exact mul_le_one' (pow_le_one' hx _) (pow_le_one' hy _))
  exact lt_of_le_of_lt (mul_le_of_le_one_left' this) h

private theorem val_natCast_sub_lt {p i : ℕ} (hp : p.Prime) {ζ μ Y : Ω} (hζ : IsPrimitiveRoot ζ p)
    (hμ : μ ^ (p - 1) = 1) (hY : Y ^ (p - 1) = ((p : ℕ) : Ω)) (hp0 : ((p : ℕ) : Ω) ≠ 0)
    (hvp : A.valuation ((p : ℕ) : Ω) < 1) (f : Ω →+* Ω)
    (hf : ∀ x, A.valuation x ≤ 1 → A.valuation (f x - x) < 1)
    (hfY : f Y = μ * Y) (hfζ : f ζ = ζ ^ i) : A.valuation ((i : Ω) - μ) < 1 := by
  have hp1 : 1 ≤ p - 1 := by
    have := hp.two_le
    omega
  have hζ1 : A.valuation ζ = 1 := val_root A ζ hp.ne_zero hζ.pow_eq_one
  have hμ1 : A.valuation μ = 1 := val_root A μ (by omega) hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hμ1
    exact zero_ne_one hμ1
  have hY0 : Y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hY
    exact hp0 hY.symm
  have h4 := val_p A hp hζ
  have hvYpow : A.valuation Y ^ (p - 1) = A.valuation (1 - ζ) ^ (p - 1) := by
    rw [← map_pow, hY, h4]
  have hvY : A.valuation Y = A.valuation (1 - ζ) := pow_left_injective (by omega) hvYpow
  have hvπ : A.valuation (1 - ζ) < 1 := by
    by_contra hc
    have h5 := one_le_pow_of_one_le' (not_lt.mp hc) (p - 1)
    rw [h4] at h5
    exact absurd hvp (not_lt.mpr h5)
  have hvY0 : A.valuation Y ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact hY0
  have hw : A.valuation ((1 - ζ) / Y) = 1 := by
    rw [map_div₀, ← hvY, div_self hvY0]
  have hgeom : 1 - ζ ^ i = (1 - ζ) * ∑ k ∈ Finset.range i, ζ ^ k := (mul_neg_geom_sum ζ i).symm
  have hfw : f ((1 - ζ) / Y) = (1 - ζ) * (∑ k ∈ Finset.range i, ζ ^ k) / (μ * Y) := by
    rw [map_div₀, map_sub, map_one, hfζ, hfY, hgeom]
  have hdiff : f ((1 - ζ) / Y) - (1 - ζ) / Y
      = (1 - ζ) / Y * ((∑ k ∈ Finset.range i, ζ ^ k) - μ) * μ⁻¹ := by
    rw [hfw]
    field_simp
  have h1 := hf ((1 - ζ) / Y) hw.le
  rw [hdiff, map_mul, map_mul, hw, map_inv₀, hμ1, one_mul, inv_one, mul_one] at h1
  have h2 : A.valuation ((i : Ω) - ∑ k ∈ Finset.range i, ζ ^ k) < 1 := by
    have hsum : (i : Ω) - ∑ k ∈ Finset.range i, ζ ^ k = ∑ k ∈ Finset.range i, (1 - ζ ^ k) := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [hsum]
    exact lt_of_le_of_lt (Valuation.map_sum_le _ (fun k _ => val_one_sub_pow_le A hζ1.le k)) hvπ
  have h3 : (i : Ω) - μ = ((i : Ω) - ∑ k ∈ Finset.range i, ζ ^ k) + ((∑ k ∈ Finset.range i, ζ ^ k) - μ) := by
    ring
  rw [h3]
  exact Valuation.map_add_lt _ h2 h1

end

theorem inertiaGen : InertiaGen := by
  unfold InertiaGen
  intro F Ω _ _ _ _ _ A u hA p _ hpu hpu2 ζ hζ
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hm : 0 < p - 1 := by
    have := hp.two_le
    omega
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (((p - 1 : ℕ)) : Ω) := ⟨by exact_mod_cast hm.ne'⟩
  obtain ⟨Y, hY⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℕ) : Ω) hm
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p - 1)
  have hndvd : ¬ p ∣ p - 1 := fun h => absurd (Nat.le_of_dvd hm h) (by omega)
  obtain ⟨σ, hσ, hσY⟩ :=
    GlobalTheory.TameKummerInertia.tame_kummer_surj F Ω A u hA p hpu hpu2 (p - 1) hm hndvd Y μ hY hμ.pow_eq_one
  have hσζ : IsPrimitiveRoot (σ ζ) p := hζ.map_of_injective σ.injective
  obtain ⟨i, hi_lt, hi⟩ := hζ.eq_pow_of_pow_eq_one hσζ.pow_eq_one
  have hcop : i.Coprime p := (hζ.pow_iff_coprime hp.pos i).mp (hi ▸ hσζ)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hp.ne_one ((Nat.coprime_zero_left p).mp hcop)
  have hvp : A.valuation ((p : ℕ) : Ω) < 1 := GlobalTheory.TameCoupledEx.val_g_lt A u hA hpu
  have hp0 : ((p : ℕ) : Ω) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hσ' := mem_Ine.mp hσ
  unfold Inertia at hσ'
  have h6 : A.valuation ((i : Ω) - μ) < 1 :=
    val_natCast_sub_lt A hp hζ hμ.pow_eq_one hY hp0 hvp σ.toRingEquiv.toRingHom
      (fun x hx => hσ'.2 x hx) hσY hi.symm
  refine ⟨σ, hσ, ZMod.unitOfCoprime i hcop, ?_, ?_⟩
  · rw [orderOf_eq_iff hm]
    refine ⟨ZMod.units_pow_card_sub_one_eq_one p _, fun k hk hk0 hpow => ?_⟩
    have hzk : ((i ^ k : ℕ) : ZMod p) = 1 := by
      have h := congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) hpow
      simpa [ZMod.coe_unitOfCoprime] using h
    have hik : 1 ≤ i ^ k := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hi0)
    have hdvd : p ∣ i ^ k - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hik, hzk, Nat.cast_one, sub_self]
    obtain ⟨c, hc⟩ := hdvd
    have hv1 : A.valuation ((i : Ω) ^ k - 1) < 1 := by
      have hcast : (i : Ω) ^ k - 1 = ((p : ℕ) : Ω) * (c : Ω) := by
        have h := congrArg (Nat.cast : ℕ → Ω) hc
        push_cast [Nat.cast_sub hik] at h
        exact h
      rw [hcast, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (valuation_natCast_le_one A c)) hvp
    have hμv : A.valuation μ ≤ 1 := (val_root A μ hm.ne' hμ.pow_eq_one).le
    have h5 := val_pow_sub_pow_lt A (valuation_natCast_le_one A i) hμv h6 k
    have h7 : A.valuation (μ ^ k - 1) < 1 := by
      have hrw : μ ^ k - 1 = ((i : Ω) ^ k - 1) + -((i : Ω) ^ k - μ ^ k) := by ring
      rw [hrw]
      exact Valuation.map_add_lt _ hv1 (by rw [Valuation.map_neg]; exact h5)
    have hvpm : ¬ A.valuation (((p - 1 : ℕ)) : Ω) < 1 := by
      intro hlt
      have hone : (1 : Ω) = ((p : ℕ) : Ω) + -(((p - 1 : ℕ)) : Ω) := by
        rw [Nat.cast_sub hp.one_le]
        push_cast
        ring
      have h8 := Valuation.map_add_lt A.valuation hvp (by rw [Valuation.map_neg]; exact hlt)
      rw [← hone, map_one] at h8
      exact lt_irrefl _ h8
    have heq := eq_of_pow_eq_one A hvpm
      (by rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]) (one_pow _) h7
    exact hμ.pow_ne_one_of_pos_of_lt hk0.ne' hk heq
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi_lt]
    exact hi.symm

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InfOf
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.infOf :
    InfOf := by
  intro F Ω _ _ _ _ _ P hP hfin
  have hopen : ∀ Q : QCM F Ω, IsOpen ((Q.K.fixingSubgroup : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro Q
    haveI : FiniteDimensional F ↥Q.K :=
      Module.finite_of_finrank_pos (by rw [Q.two]; exact two_pos)
    exact IntermediateField.fixingSubgroup_isOpen Q.K
  have hS : (⋃ Q ∈ {Q | P Q}, {u : HeightOneSpectrum (𝓞 F) | ∃ A : ValuationSubring Ω,
      IsPlaceOver A u ∧ ¬ Ine (F := F) A ≤ Q.K.fixingSubgroup}).Finite :=
    Set.Finite.biUnion hfin fun Q _ => GlobalTheory.T.finite_places_inertia_not_le_openSubgroup Ω F Q.K.fixingSubgroup (hopen Q)
  obtain ⟨Q, hQ, u, hu, A, hA, τ, hτ, hfix⟩ := hP _ hS
  refine hu (Set.mem_biUnion (show Q ∈ {Q | P Q} from hQ) ⟨A, hA, fun hle => hfix ?_⟩)
  intro x
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hle hτ) _ x.2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.PowChar
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.powChar :
    PowChar := by
  intro p _ n hn hdvd
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨ω, hωc⟩ := hprim.isUnit hn.ne'
  have hωp : IsPrimitiveRoot ω n := by
    rw [← IsPrimitiveRoot.coe_units_iff, hωc]
    exact hprim
  have hωo : orderOf ω = n := hωp.eq_orderOf.symm
  have hnd : n ∣ p - 1 := Dvd.dvd.trans (Dvd.intro_left 2 rfl) hdvd
  have hd : orderOf ω ∣ orderOf g := by rw [hωo, hog]; exact hnd
  let lam : (ZMod p)ˣ →* ℂˣ := monoidHomOfForallMemZpowers hg hd
  have hlg : lam g = ω := monoidHomOfForallMemZpowers_apply_gen hg hd
  have hωn : ω ^ n = 1 := hωp.pow_eq_one
  have hpow : ∀ a, (lam a) ^ n = 1 := by
    intro a
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    rw [map_zpow, hlg, ← zpow_natCast, zpow_comm, zpow_natCast, hωn, one_zpow]
  refine ⟨lam, ?_, ?_, ?_⟩
  · ext1 a
    rw [MonoidHom.pow_apply, hpow, MonoidHom.one_apply]
  · obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h
        omega
      · exact h
    have hx2 : (g ^ (n * c)) ^ 2 = 1 := by
      rw [← pow_mul, show n * c * 2 = p - 1 by rw [hc]; ring, ← hog, pow_orderOf_eq_one]
    have hx1 : g ^ (n * c) ≠ 1 := by
      intro h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [hog, hc] at h1
      have h2 := Nat.le_of_dvd (Nat.mul_pos hn hcpos) h1
      have h3 : 0 < n * c := Nat.mul_pos hn hcpos
      nlinarith
    have hxm : g ^ (n * c) = -1 := by
      have h4 : (((g ^ (n * c) : (ZMod p)ˣ)) : ZMod p) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, hx2, Units.val_one]
      rw [sq] at h4
      rcases mul_self_eq_one_iff.mp h4 with h | h
      · exact absurd (Units.ext (by rw [h, Units.val_one])) hx1
      · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
    rw [← hxm, map_pow, hlg, pow_mul, hωn, one_pow]
  · intro a ha
    have htop : Subgroup.zpowers a = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, ha, hcard]
    have hga : g ∈ Subgroup.zpowers a := by rw [htop]; trivial
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hga
    have hωa : (lam a) ^ j = ω := by rw [← map_zpow, hlg]
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (hpow a))
    rw [← hωo]
    apply orderOf_dvd_of_pow_eq_one
    rw [← hωa, ← zpow_natCast, zpow_comm, zpow_natCast, pow_orderOf_eq_one, one_zpow]
end

