module

public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0634
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.DiscreteGroups.GlobalIrreducibility.MulMemBall
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0006

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzTameRec
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Neutral.B1
  GlobalTheory.HeckeGal

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Tame

variable {M Ω : Type} [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 M)}

theorem normV_mem (v : HeightOneSpectrum (𝓞 M)) : ((normV v : ℕ) : 𝓞 M) ∈ v.asIdeal := by
  have : Finite (𝓞 M ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let := Fintype.ofFinite (𝓞 M ⧸ v.asIdeal)
  have hc : ((Fintype.card (𝓞 M ⧸ v.asIdeal) : ℕ) : 𝓞 M ⧸ v.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card] at hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact hc


omit [IsAlgClosure M Ω] in
theorem weil_fix_root (h : IsPlaceOver A v) (s : Weil h) (ζ : Ω) (hζ : ζ ^ (normV v - 1) = 1) :
    (s : G M Ω) ζ = ζ := by
  have hq : 1 < normV v := one_lt_normV v
  have hζi : IsIntegral ℤ ζ := IsIntegral.of_pow (n := normV v - 1) (by omega) (by rw [hζ]; exact isIntegral_one)
  have hζA : A.valuation ζ ≤ 1 := (A.valuation_le_one_iff _).2 (ReciprocityTheory.Gal.mem_of_isIntegral_int A hζi)
  have hζ1 : ζ ^ normV v = ζ := by
    have : normV v = (normV v - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  have hpow : ∀ (y : Ω), y ^ normV v = y → ∀ k : ℕ, y ^ (normV v ^ k) = y := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, hy]
  have hsζ : ((s : G M Ω) ζ) ^ (normV v - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hsζ1 : ((s : G M Ω) ζ) ^ normV v = (s : G M Ω) ζ := by
    have : normV v = (normV v - 1) + 1 := by omega
    rw [this, pow_succ, hsζ, one_mul]
  obtain ⟨a, b, hab⟩ := s.2
  have hc := hab.2 ζ hζA
  rw [hpow _ hsζ1, hpow _ hζ1] at hc
  have hsA : A.valuation ((s : G M Ω) ζ) ≤ 1 := by
    rw [A.valuation_le_one_iff, ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hab.1, ← A.valuation_le_one_iff]
    exact hζA
  have hval1 : A.valuation ζ = 1 := by
    refine le_antisymm hζA (not_lt.1 fun hlt => ?_)
    have := pow_lt_one₀ zero_le hlt (show normV v - 1 ≠ 0 by omega)
    rw [← map_pow, hζ, map_one] at this
    exact lt_irrefl _ this
  have hqA : A.valuation ((normV v : ℕ) : Ω) < 1 := by
    have := (h ((normV v : ℕ) : 𝓞 M)).2 (normV_mem v)
    simpa using this
  have hd : ¬ A.valuation (aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X]))) < 1 := by
    have e : aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X])) =
        (((normV v - 1 : ℕ) : Ω)) * ζ ^ (normV v - 1 - 1) := by
      simp [derivative_X_pow]
    rw [e, map_mul, map_pow, hval1, one_pow, mul_one]
    have e2 : (((normV v - 1 : ℕ) : Ω)) = -1 + ((normV v : ℕ) : Ω) := by
      rw [Nat.cast_sub hq.le]; ring
    have h' : A.valuation ((normV v : ℕ) : Ω) < A.valuation (-1 : Ω) := by
      rw [Valuation.map_neg, map_one]; exact hqA
    rw [e2, Valuation.map_add_eq_of_lt_left _ h', Valuation.map_neg, map_one]
    exact lt_irrefl _
  exact (GlobalTheory.eq_of_root_congr_of_deriv_unit A (X ^ (normV v - 1) - 1) ζ ((s : G M Ω) ζ) hζA hsA
    (by simp [hζ]) (by simp [hsζ]) hd (by rw [Valuation.map_sub_swap]; exact hc)).symm

end Tame

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzTwFin
section
noncomputable section

open Polynomial GlobalTheory.GLq GlobalTheory.SmGL CategoryTheory

namespace DiscreteGroups.sglob.DzTw

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

def twFD (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) : FDRep ℂ (Gn g n) :=
  FDRep.of (twist τ.ρ (detChar (Fin n) χ₀))

theorem character_twFD (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) (y : Gn g n) :
    (twFD τ χ₀).character y = ((χ₀ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * τ.character y := by
  change LinearMap.trace ℂ τ (((detChar (Fin n) χ₀ y : ℂˣ) : ℂ) • τ.ρ y) =
    ((χ₀ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * LinearMap.trace ℂ τ (τ.ρ y)
  rw [map_smul, smul_eq_mul, detChar_apply]

theorem simple_of_char {G : Type} [Group G] [Fintype G] {V W : FDRep ℂ G} (hV : Simple V)
    (h : ∀ x, W.character x * W.character x⁻¹ = V.character x * V.character x⁻¹) : Simple W := by
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hc' : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_pos.ne'
  have := invertibleOfNonzero hc
  have := invertibleOfNonzero hc'
  rw [FDRep.simple_iff_char_is_norm_one] at hV ⊢
  simpa only [h] using hV

theorem char_twFD_mul (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) (x : Gn g n) :
    (twFD τ χ₀).character x * (twFD τ χ₀).character x⁻¹ = τ.character x * τ.character x⁻¹ := by
  have hu : ((χ₀ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * ((χ₀ (Matrix.GeneralLinearGroup.det x⁻¹) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Units.val_one]
  rw [character_twFD, character_twFD]
  calc _ = (((χ₀ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * ((χ₀ (Matrix.GeneralLinearGroup.det x⁻¹) : ℂˣ) : ℂ)) *
        (τ.character x * τ.character x⁻¹) := by ring
    _ = _ := by rw [hu, one_mul]

theorem det_eq_one_of_mem {N a : ℕ} {u : GL (Fin N) (ZMod g)}
    (hu : u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks N a)) : Matrix.GeneralLinearGroup.det u = 1 := by
  have hu' := GlobalTheory.FiniteGL.mem_unipRadical.1 hu
  have hmono : ∀ i j : Fin N, j < i → GlobalTheory.FiniteGL.twoBlocks N a j ≤ GlobalTheory.FiniteGL.twoBlocks N a i := by
    intro i j hij
    have : (j : ℕ) < i := hij
    simp only [GlobalTheory.FiniteGL.twoBlocks]
    split_ifs <;> omega
  have hT : (u : Matrix (Fin N) (Fin N) (ZMod g)).BlockTriangular id := by
    intro i j hij
    have h := hu' i j (hmono i j hij)
    have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h
  have hd : ∀ i, (u : Matrix (Fin N) (Fin N) (ZMod g)) i i = 1 := by
    intro i
    have h := hu' i i le_rfl
    rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular hT]
  simp [hd]

theorem res_twFD (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) {a : ℕ} (ha : a < n) :
    res a (n - a) (twFD τ χ₀).character 1 1 = res a (n - a) τ.character 1 1 := by
  unfold res
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = ((1 : Gn g a) : Mt g a) ∧
      br a (n - a) (x : Mt g n) = ((1 : Gn g (n - a)) : Mt g (n - a))
  · rw [if_pos hx, if_pos hx, character_twFD,
      det_eq_one_of_mem ((GlobalTheory.SerSys.TameGen.mem_unipRadical_iff ha x).2 hx), map_one, Units.val_one, one_mul]
  · rw [if_neg hx, if_neg hx]

theorem isCusp_twFD (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) (hτ : IsCusp τ.character) :
    IsCusp (twFD τ χ₀).character := by
  obtain ⟨hn, ⟨V, hV, hVc⟩, hres⟩ := hτ
  have hsτ : Simple τ := simple_of_char hV (fun x => by rw [hVc, hVc])
  refine ⟨hn, ⟨twFD τ χ₀, simple_of_char hsτ (fun x => char_twFD_mul τ χ₀ x), fun _ => rfl⟩, fun a h0 ha => ?_⟩
  rw [res_twFD τ χ₀ ha]
  exact hres a h0 ha

theorem det_eq_norm (K : Type) [Field K] [Algebra (ZMod g) K] (hK : Nat.card K = g ^ n) (hn : 0 < n) (y : Gn g n)
    (hy : Irreducible (y : Mt g n).charpoly) (z : Kˣ) (hz : aeval (z : K) (y : Mt g n).charpoly = 0) :
    Matrix.GeneralLinearGroup.det y = Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (by omega))
  letI : Fintype K := Fintype.ofFinite K
  haveI : Module.Finite (ZMod g) K := by
    first
    | exact Module.finite_of_finite (ZMod g)
    | exact inferInstance
  have hfr : Module.finrank (ZMod g) K = n := by
    have h1 : Fintype.card K = Fintype.card (ZMod g) ^ Module.finrank (ZMod g) K := by
      first
      | exact Module.card_eq_pow_finrank
      | exact card_eq_pow_finrank
    rw [ZMod.card] at h1
    have h2 : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
    exact Nat.pow_right_injective hg (h1.symm.trans h2)
  have hmon : ((y : Mt g n).charpoly).Monic := Matrix.charpoly_monic _
  have hdeg : ((y : Mt g n).charpoly).natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmin : (y : Mt g n).charpoly = minpoly (ZMod g) (z : K) := minpoly.eq_of_irreducible_of_monic hy hz hmon
  have hint : IsIntegral (ZMod g) (z : K) := Algebra.IsIntegral.isIntegral _
  have hfr2 : Module.finrank (IntermediateField.adjoin (ZMod g) {(z : K)}) K = 1 := by
    have h3 := IntermediateField.adjoin.finrank hint
    have h4 := (letI : Module.Free (IntermediateField.adjoin (ZMod g) {(z : K)}) K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank (ZMod g) (IntermediateField.adjoin (ZMod g) {(z : K)}) K)
    rw [h3, ← hmin, hdeg, hfr] at h4
    exact Nat.eq_of_mul_eq_mul_left hn (h4.trans (mul_one n).symm)
  have hnorm : Algebra.norm (ZMod g) (z : K) = (-1) ^ n * ((y : Mt g n).charpoly).coeff 0 := by
    rw [Algebra.norm_eq_norm_adjoin (ZMod g) (z : K), hfr2, pow_one]
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
      IntermediateField.minpoly_gen] at this
    rw [this, ← hmin, hdeg]
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]
  exact hnorm.symm

theorem units_pow_card_pow (u : (ZMod g)ˣ) (j : ℕ) : u ^ g ^ j = u :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, ZMod.pow_card_pow])

theorem nmChar_pow (K : Type) [Field K] [Algebra (ZMod g) K] (χ₀ : (ZMod g)ˣ →* ℂˣ) (j : ℕ) :
    (DiscreteGroups.sglob.DzType.nmChar K χ₀) ^ g ^ j = DiscreteGroups.sglob.DzType.nmChar K χ₀ := by
  refine MonoidHom.ext fun z => ?_
  rw [MonoidHom.pow_apply]
  show (χ₀ (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z)) ^ g ^ j =
    χ₀ (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z)
  rw [← map_pow, units_pow_card_pow]

theorem isRegularChar_mul (K : Type) [Field K] [Algebra (ZMod g) K] (χ₀ : (ZMod g)ˣ →* ℂˣ) {θ : Kˣ →* ℂˣ}
    (hθ : GlobalTheory.Published.IsRegularChar g n θ) : GlobalTheory.Published.IsRegularChar g n (θ * DiscreteGroups.sglob.DzType.nmChar K χ₀) := by
  intro i j hi hj h
  apply hθ i j hi hj
  rw [mul_pow, mul_pow, nmChar_pow, nmChar_pow] at h
  exact mul_right_cancel h

theorem char_twFD (K : Type) [Field K] [Algebra (ZMod g) K] (hK : Nat.card K = g ^ n) (hn : 0 < n)
    (χ₀ : (ZMod g)ˣ →* ℂˣ) (θ : Kˣ →* ℂˣ) (τ : FDRep ℂ (Gn g n))
    (hτ : ∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) :
    ∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
      (twFD τ χ₀).character y =
        (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, (((θ * DiscreteGroups.sglob.DzType.nmChar K χ₀) (z ^ g ^ j) : ℂˣ) : ℂ) := by
  intro y hy z hz
  have hN : ∀ j, DiscreteGroups.sglob.DzType.nmChar K χ₀ (z ^ g ^ j) = χ₀ (Matrix.GeneralLinearGroup.det y) := by
    intro j
    rw [det_eq_norm K hK hn y hy z hz, map_pow, ← MonoidHom.pow_apply, nmChar_pow]
    try rfl
  rw [character_twFD, hτ y hy z hz]
  simp only [MonoidHom.mul_apply, Units.val_mul, hN]
  rw [← Finset.sum_mul]
  ring

end DiscreteGroups.sglob.DzTw
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ExistsBallMem
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem psi_triv {ψ : AddChar k Circle} {c : kˣ} (hc : HasConductor ψ c) {s : kˣ} {ξ : k}
    (hξ : ξ ∈ ball (c * s⁻¹)) : ∀ h ∈ ball s, ψ (ξ * h) = 1 := by
  intro h hh
  have := mul_mem_ball hξ hh
  rw [inv_mul_cancel_right] at this
  exact hc.eq_one this

theorem psi_neg_triv {ψ : AddChar k Circle} {c : kˣ} (hc : HasConductor ψ c) {s : kˣ} {ξ : k}
    (hξ : ξ ∈ ball (c * s⁻¹)) {h : k} (hh : h ∈ ball s) : ψ (-(ξ * h)) = 1 := by
  have := mul_mem_ball hξ hh
  rw [inv_mul_cancel_right] at this
  exact hc.eq_one (neg_mem this)

theorem card_ne_zero (s t : kˣ) : ((Fintype.card (Q (k := k) s t) : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem exists_ball_mem (a : k) : ∃ t : kˣ, a ∈ ball t := by
  by_cases h : a = 0
  · exact ⟨1, by rw [h]; exact (ball 1).zero_mem⟩
  · exact ⟨Units.mk0 a h, mem_ball.2 le_rfl⟩

theorem exists_min (s1 s2 : kˣ) : ∃ s : kˣ, valuation k (s : k) ≤ valuation k (s1 : k) ∧
    valuation k (s : k) ≤ valuation k (s2 : k) := by
  rcases le_total (valuation k (s1 : k)) (valuation k (s2 : k)) with h | h
  · exact ⟨s1, le_rfl, h⟩
  · exact ⟨s2, h, le_rfl⟩

theorem exists_max (s1 s2 : kˣ) : ∃ s : kˣ, valuation k (s1 : k) ≤ valuation k (s : k) ∧
    valuation k (s2 : k) ≤ valuation k (s : k) := by
  rcases le_total (valuation k (s1 : k)) (valuation k (s2 : k)) with h | h
  · exact ⟨s2, h, le_rfl⟩
  · exact ⟨s1, le_rfl, h⟩

section Fourier

variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (hadd : ∀ a b, σ (a + b) = σ a * σ b)

theorem avg_of_eigen {s t : kˣ} {ξ : k} {z : V}
    (hz : ∀ b ∈ ball t, σ b z = ((ψ (ξ * b) : Circle) : ℂ) • z) :
    avg ψ σ s t ξ z = ((Fintype.card (Q s t) : ℕ) : ℂ) • z := by
  have h1 : ∀ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) •
      σ ((Quotient.out q : ↥(ball t)) : k) z = z := fun q => by
    rw [hz _ (out_mem q), smul_smul, ch_neg_mul, one_smul]
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply, h1, Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

include hadd

theorem avg_level {s s0 t : kˣ} {ξ : k} (hss0 : valuation k (s : k) ≤ valuation k (s0 : k))
    (hξ : ∀ h ∈ ball s0, ψ (ξ * h) = 1) {x : V} (hx : ∀ h ∈ ball s0, σ h x = x) :
    ((Fintype.card (Q s0 t) : ℕ) : ℂ) • avg ψ σ s t ξ x = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s0 t ξ x := by
  have hξs : ∀ h ∈ ball s, ψ (ξ * h) = 1 := fun h hh => hξ h (ball_mono hss0 hh)
  have hxs : ∀ h ∈ ball s, σ h x = x := fun h hh => hx h (ball_mono hss0 hh)
  have e1 : avg ψ σ s0 t ξ (avg ψ σ s t ξ x) = ((Fintype.card (Q s0 t) : ℕ) : ℂ) • avg ψ σ s t ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξs hxs hb)
  have e2 : avg ψ σ s t ξ (avg ψ σ s0 t ξ x) = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s0 t ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξ hx hb)
  rw [← e1, ← e2, ← Module.End.mul_apply, avg_comm_avg ψ σ hadd, Module.End.mul_apply]

theorem avg_mono_mem (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W) {s t t' : kˣ}
    (htt' : valuation k (t : k) ≤ valuation k (t' : k)) {ξ : k} (hξ : ∀ h ∈ ball s, ψ (ξ * h) = 1)
    {x : V} (hx : ∀ h ∈ ball s, σ h x = x) (h : avg ψ σ s t ξ x ∈ W) : avg ψ σ s t' ξ x ∈ W := by
  have e : avg ψ σ s t ξ (avg ψ σ s t' ξ x) = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s t' ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξ hx (ball_mono htt' hb))
  have hm : avg ψ σ s t ξ (avg ψ σ s t' ξ x) ∈ W := by
    rw [← Module.End.mul_apply, avg_comm_avg ψ σ hadd, Module.End.mul_apply]
    exact avg_mem ψ σ W hW _ _ _ h
  rw [e] at hm
  exact (W.smul_mem_iff (card_ne_zero s t)).1 hm

end Fourier

end DiscreteGroups.sglob.LConvGenF
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.KmatMulKinv
section
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands ValuativeRel Filter Topology

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] {m : ℕ}

def Kmat (jj : Fin (m + 1)) (a : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Matrix.of fun p q => if p = jj then a q else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q

def Kinv2 (jj : Fin (m + 1)) (z : (Fin (m + 1) → k) × k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Matrix.of fun p q => if p = jj then (if q = jj then z.2 else -(z.1 q) * z.2)
    else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q

def Kinv (jj : Fin (m + 1)) (a : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Kinv2 jj (a, (a jj)⁻¹)

theorem Kmat_mul_Kinv (jj : Fin (m + 1)) (a : Fin (m + 1) → k) (ha : a jj ≠ 0) :
    Kmat jj a * Kinv jj a = 1 := by
  ext p q
  rw [Matrix.mul_apply]
  by_cases hp : p = jj
  · subst hp
    have hs : ∀ r, Kmat p a p r * Kinv p a r q = a r * (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r q +
        (if r = p then a p * (Kinv p a p q - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q) else 0) := by
      intro r
      by_cases hr : r = p
      · rw [hr, if_pos rfl]; simp only [Kmat, Matrix.of_apply, ↓reduceIte]; ring
      · rw [if_neg hr, add_zero]
        simp only [Kmat, Kinv, Kinv2, Matrix.of_apply, ↓reduceIte, if_neg hr]
    rw [Finset.sum_congr rfl (fun r _ => hs r), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hq : q = p
    · subst hq
      simp only [Kinv, Kinv2, Matrix.of_apply, ↓reduceIte]
      field_simp
      ring
    · simp only [Kinv, Kinv2, Matrix.of_apply, ↓reduceIte, if_neg hq, if_neg (Ne.symm hq)]
      field_simp
      ring
  · rw [Finset.sum_eq_single p]
    · simp only [Kmat, Kinv, Kinv2, Matrix.of_apply, if_neg hp, Matrix.one_apply_eq, one_mul]
    · intro r _ hr
      simp only [Kmat, Matrix.of_apply, if_neg hp, Matrix.one_apply_ne (Ne.symm hr), zero_mul]
    · intro h; exact absurd (Finset.mem_univ p) h

theorem Kinv_mul_Kmat (jj : Fin (m + 1)) (a : Fin (m + 1) → k) (ha : a jj ≠ 0) :
    Kinv jj a * Kmat jj a = 1 :=
  mul_eq_one_comm.1 (Kmat_mul_Kinv jj a ha)

theorem Kmat_single (jj : Fin (m + 1)) : Kmat jj (Pi.single jj (1 : k)) = 1 := by
  ext p q
  by_cases hp : p = jj
  · subst hp; simp [Kmat, Matrix.one_apply, Pi.single_apply, eq_comm]
  · simp [Kmat, hp]

theorem Kinv_single (jj : Fin (m + 1)) : Kinv jj (Pi.single jj (1 : k)) = 1 := by
  ext p q
  by_cases hp : p = jj
  · subst hp
    by_cases hq : q = p
    · subst hq; simp [Kinv, Kinv2]
    · simp [Kinv, Kinv2, hq, Matrix.one_apply, Pi.single_apply, Ne.symm hq]
  · simp [Kinv, Kinv2, hp]

end DiscreteGroups.sglob.LConvKir
end
end

