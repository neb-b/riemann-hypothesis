module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardResidueFieldAdjoinUnitaryProd
section
noncomputable section

namespace GlobalTheory.UnitLemma.ResDeg

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing

theorem odd_of_involution {k₀ k : Type} [Field k₀] [Field k] [Fintype k₀] [Finite k] (ι : k₀ →+* k) (q d : ℕ)
    (h0 : Fintype.card k₀ = q ^ 2) (hk : Nat.card k = q ^ (2 * d)) (τ : k ≃+* k) (hτ : ∀ z, τ (τ z) = z)
    (x y : k₀) (hxy : τ (ι x) = ι y) (hne : x ≠ y) : Odd d := by
  classical
  have hfix : ∀ m : ℕ, τ (ι x) ≠ (ι x) ^ (q ^ (2 * m)) := by
    intro m h
    rw [← map_pow, pow_mul, ← h0, FiniteField.pow_card_pow, hxy] at h
    exact hne (ι.injective h).symm
  letI := Fintype.ofFinite k
  obtain ⟨p, hchar⟩ := CharP.exists k
  haveI := hchar
  haveI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let τA : k ≃ₐ[ZMod p] k := AlgEquiv.ofRingEquiv (f := τ) (fun r => by
    have := RingHom.ext_zmod ((τ : k →+* k).comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) k)
    exact DFunLike.congr_fun this r)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 τA
  have hord := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) k
  have hsq : τA ^ 2 = 1 := AlgEquiv.ext fun z => hτ z
  have hdvd : Module.finrank (ZMod p) k ∣ 2 * n.1 := by
    have := orderOf_dvd_iff_pow_eq_one.2
      (show FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k ^ (2 * n.1) = 1 by
        rw [pow_mul']; exact (congrArg (· ^ 2) hn).trans hsq)
    rwa [hord] at this
  have hcard : Fintype.card k = p ^ Module.finrank (ZMod p) k := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hτz : ∀ z, τ z = z ^ (p ^ n.1) := by
    intro z
    have h1 := DFunLike.congr_fun hn z
    simp only at h1
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card] at h1
    exact h1.symm
  have hN := n.2
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : c < 2 := by
    by_contra hh
    push_neg at hh
    nlinarith
  interval_cases c
  · exfalso
    have hn0 : n.1 = 0 := by omega
    apply hfix 0
    rw [hτz, hn0]; simp
  · have hpq : p ^ n.1 = q ^ d := by
      have e1 : p ^ (2 * n.1) = q ^ (2 * d) := by
        rw [← hk, Nat.card_eq_fintype_card, hcard, hc, mul_one]
      have e : (p ^ n.1) ^ 2 = (q ^ d) ^ 2 := by
        rw [← pow_mul, ← pow_mul, mul_comm n.1 2, mul_comm d 2]; exact e1
      exact Nat.pow_left_injective two_ne_zero e
    by_contra hodd
    obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hodd
    apply hfix m
    rw [hτz, hpq, hm, two_mul]

end GlobalTheory.UnitLemma.ResDeg

namespace GlobalTheory.UnitLemma.ResDeg

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing

variable {K : UQ}

def sigmaAdj (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g) :
    Algebra.adjoin K.O ({B.g} : Set B.A) ≃+* Algebra.adjoin K.O ({B.g} : Set B.A) where
  toFun y := ⟨B.σ (y : B.A), adjoin_stable B hu hi y.2⟩
  invFun y := ⟨B.σ (y : B.A), adjoin_stable B hu hi y.2⟩
  left_inv y := Subtype.ext (B.σ_σ (y : B.A))
  right_inv y := Subtype.ext (B.σ_σ (y : B.A))
  map_mul' x y := Subtype.ext (map_mul B.σ (x : B.A) (y : B.A))
  map_add' x y := Subtype.ext (map_add B.σ (x : B.A) (y : B.A))

theorem card_residueField (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) :
    ∃ d : ℕ, Odd d ∧
      Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) := by
  set_option synthInstance.maxHeartbeats 200000 in
  classical
  haveI := hl
  haveI : Module.Finite K.O (Algebra.adjoin K.O ({B.g} : Set B.A)) :=
    Module.Finite.iff_fg.mpr hi.fg_adjoin_singleton
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  haveI : Finite (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))) :=
    Module.finite_of_finite (ResidueField K.O)
  letI : Fintype (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))) := Fintype.ofFinite _
  set τ := ResidueField.mapEquiv (sigmaAdj B hu hi)
  have hτ : ∀ z, τ (τ z) = z := by
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    simp only [τ, ResidueField.mapEquiv_apply, ResidueField.map_residue]
    congr 1
    exact Subtype.ext (B.σ_σ r)
  obtain ⟨x, y, hxy, hne⟩ := K.c_res
  refine ⟨Module.finrank (ResidueField K.O) (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))),
    odd_of_involution (algebraMap (ResidueField K.O) _) K.q _ ?_ ?_ τ hτ (residue K.O x) (residue K.O y) ?_ ?_, ?_⟩
  · rw [← K.card_res, Nat.card_eq_fintype_card]
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ResidueField K.O), ← Nat.card_eq_fintype_card,
      K.card_res, pow_mul]
  · show ResidueField.map _ (residue _ (algebraMap K.O _ x)) = residue _ (algebraMap K.O _ y)
    rw [ResidueField.map_residue]
    congr 1
    apply Subtype.ext
    change B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hxy, ← IsScalarTower.algebraMap_apply]
  · intro h
    exact hne (Ideal.Quotient.eq.1 h)
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ResidueField K.O), ← Nat.card_eq_fintype_card,
      K.card_res, pow_mul]

theorem card_residueField_prod : ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 →
    B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g →
    ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)),
      ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField
        (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  intro K _ B₁ B₂ h₁ h₂ _ i₁ i₂ hl
  exact card_residueField (B₁.prod B₂) (Prod.ext h₁ h₂) (IsIntegral.pair i₁ i₂) hl

end GlobalTheory.UnitLemma.ResDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSubspacesSupEqTop
section
open scoped BigOperators

namespace GlobalTheory

theorem card_subspaces_sup_eq_top :
    ∀ (k : Type) [Field k] [Finite k] (r t : ℕ) (R : Submodule k (Fin (r + t) → k)),
      Module.finrank k R ≤ r →
      Nat.card {U : Submodule k (Fin (r + t) → k) // Module.finrank k U = t ∧ R ⊔ U = ⊤} =
        if Module.finrank k R = r then Nat.card k ^ (r * t) else 0 := by
  intro k _ _ r t R hR
  convert AdaptedLocalData.card_sup_eq_top r t R hR

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyDvdPowOfAevalEqZero
section
open Polynomial

namespace GlobalTheory.UnitLemma.Centraliser

theorem charpoly_dvd_pow_of_aeval_eq_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : R[X]) (hp : aeval M p = 0) : M.charpoly ∣ p ^ Fintype.card n := by
  set a : Matrix n n R[X] := algebraMap R[X] (Matrix n n R[X]) X with ha_def
  set b : Matrix n n R[X] := (Algebra.ofId R R[X]).mapMatrix M with hb_def
  have hab : Commute a b := Algebra.commutes X b
  have key : ∀ q : R[X], ∃ H, (a - b) * H = aeval a q - aeval b q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨H1, h1⟩ := hp
      obtain ⟨H2, h2⟩ := hq
      exact ⟨H1 + H2, by rw [mul_add, h1, h2, map_add (f := _), map_add (f := _)]; abel⟩
    | monomial k c =>
      refine ⟨algebraMap R (Matrix n n R[X]) c * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i), ?_⟩
      rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hab.mul_geom_sum₂,
        mul_sub]
  obtain ⟨H, hH⟩ := key p
  have hb : aeval b p = 0 := by
    rw [hb_def, aeval_algHom_apply, hp, map_zero]
  have ha : aeval a p = algebraMap R[X] (Matrix n n R[X]) p := by
    rw [ha_def, aeval_algebraMap_apply, aeval_X_left_apply]
  have hch : (a - b).det = M.charpoly := rfl
  refine ⟨H.det, ?_⟩
  rw [← hch, ← Matrix.det_mul, hH, hb, sub_zero, ha, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal]
  simp

theorem P_dvd_of_aeval_eq_zero {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (p : K.E[X])
    (hp : aeval B.g p = 0) : B.P ∣ p := by
  have h1 : aeval (Algebra.lmul K.E B.A B.g) p = 0 := by
    rw [aeval_algHom_apply, hp, map_zero]
  let bs := Module.finBasis K.E B.A
  have h2 : aeval (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul K.E B.A B.g)) p = 0 := by
    rw [aeval_algHom_apply, h1, map_zero]
  have h3 := charpoly_dvd_pow_of_aeval_eq_zero _ p h2
  have h4 : (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul K.E B.A B.g)).charpoly = B.P := by
        exact LinearMap.charpoly_toMatrix _ bs
  rw [h4] at h3
  exact hsep.squarefree.isRadical _ _ h3

theorem aeval_g_P {K : UQ} (B : InvAlg K) : aeval B.g B.P = 0 := by
  have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft K.E B.g)
  have h' : Algebra.lmul K.E B.A (aeval B.g B.P) = 0 := by
    rw [← aeval_algHom_apply]; exact h
  simpa using congrArg (fun f : Module.End K.E B.A => f 1) h'

theorem exists_aeval_eq {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (y : B.A) :
    ∃ p : K.E[X], aeval B.g p = y := by
  have hm : B.P.Monic := LinearMap.charpoly_monic _
  have hP : eval₂ (↑(Algebra.ofId K.E B.A)) B.g B.P = 0 := aeval_g_P B
  let φ := AdjoinRoot.liftAlgHom B.P (Algebra.ofId K.E B.A) B.g hP
  let pb := AdjoinRoot.powerBasis' hm
  haveI : Module.Finite K.E (AdjoinRoot B.P) := pb.finite
  have hrank : Module.finrank K.E (AdjoinRoot B.P) = Module.finrank K.E B.A := by
    rw [pb.finrank, AdjoinRoot.powerBasis'_dim]
    exact LinearMap.charpoly_natDegree _
  have hinj : Function.Injective φ.toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [AdjoinRoot.mk_eq_zero]
    apply P_dvd_of_aeval_eq_zero B hsep
    simpa [φ, AdjoinRoot.liftAlgHom_mk, aeval_def] using hz
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj y
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  exact ⟨p, by simpa [φ, AdjoinRoot.liftAlgHom_mk, aeval_def] using hz⟩

theorem eq_zero_of_isNilpotent {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (a : B.A)
    (ha : IsNilpotent a) : a = 0 := by
  obtain ⟨p, rfl⟩ := exists_aeval_eq B hsep a
  obtain ⟨m, hm⟩ := ha
  have h1 : B.P ∣ p ^ m := P_dvd_of_aeval_eq_zero B hsep _ (by rw [map_pow, hm])
  obtain ⟨q, rfl⟩ := hsep.squarefree.isRadical m p h1
  rw [map_mul, aeval_g_P, zero_mul]

theorem eq_zero_of_trace_mul {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (a : B.A)
    (ha : ∀ y, Algebra.trace K.E B.A (a * y) = 0) : a = 0 := by
  apply eq_zero_of_isNilpotent B hsep
  let bs := Module.finBasis K.E B.A
  have hN : IsNilpotent (Algebra.leftMulMatrix bs a) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace, pow_succ']
    exact ha _
  obtain ⟨m, hm⟩ := hN
  refine ⟨m, Algebra.leftMulMatrix_injective bs ?_⟩
  rw [map_pow, hm, map_zero]

end GlobalTheory.UnitLemma.Centraliser
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlacesOfSamePrimeBelow
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace GlobalTheory

theorem conj_places_of_same_prime_below : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A B : ValuationSubring Ω), (∀ x ∈ K, IsIntegral ℤ x → (A.valuation x < 1 ↔ B.valuation x < 1)) → ∃ ρ : G E Ω, (∀ x ∈ K, ρ x = x) ∧ ρ • A = B := by
  intro E Ω _ _ _ _ _ K _ A B h
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  haveI : NumberField K := ⟨⟩
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  letI : TopologicalSpace (IntCl K Ω) := ⊥
  haveI : DiscreteTopology (IntCl K Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl K Ω
  haveI := isInvariant_intCl K Ω
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 K)
    (G := Ω ≃ₐ[K] Ω) (primeBelow (F := K) A) (primeBelow (F := K) B) (by
      ext x
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
      have hK : ((algebraMap (𝓞 K) (IntCl K Ω) x : IntCl K Ω) : Ω) = ((x : K) : Ω) := rfl
      rw [hK]
      refine h _ (x : K).2 ?_
      exact (x.2.map (IsScalarTower.toAlgHom ℤ K Ω)))
  have hgA : g • A = B := by
    refine eq_of_valuation_lt_one_iff K fun b hb => ?_
    let b' : IntCl K Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := K) (g • A) ↔ b' ∈ primeBelow (F := K) B
    rw [primeBelow_smul, hg]
  refine ⟨g.restrictScalars E, fun x hx => ?_, ?_⟩
  · show g x = x
    exact g.commutes ⟨x, hx⟩
  · rw [← hgA]
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordApply
section
noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions GlobalTheory.NB

namespace GlobalTheory.WachTie

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

def piNorm : O⟦X⟧ := ∏ δ ∈ W.DelF, W.γ₀ δ X

def FrTie (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) : Prop :=
  Function.Injective j ∧
  (∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a) ∧
  (∀ a, j (R.φ a) = W.φ₀ (j a)) ∧
  (∀ a, j (R.γ a) = W.γ₀ W.gam (j a)) ∧
  R.χ = W.χΓ W.gam ∧
  R.s = W.DelF.card ∧
  Associated (j X) (X ^ R.s) ∧
  Associated (j R.E) W.q₀

def EETie (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) : Prop :=
  (∀ a : ZMod n → O⟦X⟧, jE (fun i => R.ι (a i)) = algebraMap (LetA O n) W.EE (fun i => j (a i))) ∧
  Function.Injective jE ∧
  (∀ y, (∃ x, jE x = y) ↔ ∀ δ ∈ W.DelF, W.γE δ y = y) ∧
  (∀ x, jE (fun i => R.φE (x (i - 1))) = W.φE (jE x)) ∧
  (∀ x, jE (fun i => R.γE (x i)) = W.γE W.gam (jE x))

def coord (R : Fr l O) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ}
    (b : Fin r → W.DD T) : DD R n r →ₗ[O] W.DD T where
  toFun x := ∑ k, jE (fun i => x i k) • b k
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul, ← map_add (f := _)]; rfl
  map_smul' c x := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_assoc, ← map_smul]; rfl

theorem coord_apply (R : Fr l O) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ}
    (b : Fin r → W.DD T) (x : DD R n r) :
    coord W R jE T b x = ∑ k, jE (fun i => x i k) • b k := rfl

def DDinv (T : LocLat G Qp LL O) : Submodule O (W.DD T) where
  carrier := {x | ∀ δ ∈ W.DelF, W.γD T δ x = x}
  zero_mem' := fun δ _ => map_zero _
  add_mem' := fun ha hb δ hδ => by rw [map_add (f := _), ha δ hδ, hb δ hδ]
  smul_mem' := fun c a ha δ hδ => by rw [map_smul, ha δ hδ]

def wachDeltaInvariantCoboundaries (T : LocLat G Qp LL O) : Submodule O (W.DD T × W.DD T) :=
  (DDinv W T).map ((W.φD T - LinearMap.id).prod (W.γD T W.gamK - LinearMap.id))

def SysTie (R : Fr l O) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (S : Sys R n r) : Prop :=
  let Θ := coord W R jE T (fun k => (b k : W.DD T))
  (∀ k, (b k : W.DD T) ∈ W.NΔ T) ∧
  Function.Injective Θ ∧
  LinearMap.range Θ = DDinv W T ∧
  (∀ x, Θ x ∈ W.NΔ T ↔ ∀ i, x i ∈ R.N0 r) ∧
  (∀ x, Θ (S.φD x) = W.φD T (Θ x)) ∧
  (∀ x, Θ (S.γD x) = W.γD T W.gam (Θ x)) ∧
  S.Z1.map (Θ.prodMap Θ) = W.wachCocyclesDelta T ∧
  S.B1.map (Θ.prodMap Θ) = wachDeltaInvariantCoboundaries W T

end GlobalTheory.WachTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrtApproxIntegral
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace GlobalTheory

theorem crt_approx_integral : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A : ValuationSubring Ω)
    (c : ℕ), c ≠ 0 →
    ∃ t ∈ K, IsIntegral ℤ t ∧ A.valuation (t - 1) ≤ A.valuation (c : Ω) ∧
      ∀ σ : G E Ω, (∃ x ∈ K, IsIntegral ℤ x ∧ ¬(A.valuation (σ x) < 1 ↔ A.valuation x < 1)) →
        A.valuation (σ t) ≤ A.valuation (c : Ω) := by
  intro E Ω _ _ _ _ _ K _ A c hc
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans E K }
  have hint : ∀ {y : Ω}, IsIntegral ℤ y → A.valuation y ≤ 1 := fun hy =>
    (A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A hy)
  by_cases hcP : A.valuation (c : Ω) < 1
  swap
  · have h1 : 1 ≤ A.valuation (c : Ω) := not_lt.mp hcP
    refine ⟨1, K.one_mem, isIntegral_one, ?_, fun σ _ => ?_⟩
    · rw [sub_self, map_zero]; exact zero_le'
    · rw [map_one, map_one]; exact h1
  set f : 𝓞 K →+* Ω := (algebraMap K Ω).comp (algebraMap (𝓞 K) K) with hf
  have fint : ∀ r : 𝓞 K, IsIntegral ℤ (f r) := fun r =>
    (RingOfIntegers.isIntegral_coe r).map (algebraMap K Ω).toIntAlgHom
  let Pg : (g : 𝓞 K →+* Ω) → (∀ r, IsIntegral ℤ (g r)) → Ideal (𝓞 K) := fun g hg =>
    (IsLocalRing.maximalIdeal A).comap (g.codRestrict A (fun r => mem_of_isIntegral_int A (hg r)))
  have memPg : ∀ g hg r, r ∈ Pg g hg ↔ A.valuation (g r) < 1 := fun g hg r => by
    simp only [Pg, Ideal.mem_comap]; exact A.valuation_lt_one_iff _
  have primePg : ∀ g hg, (Pg g hg).IsPrime := fun g hg => Ideal.comap_isPrime _ _
  have key : ∀ (g : 𝓞 K →+* Ω) (hg : ∀ r, IsIntegral ℤ (g r)) (s u : 𝓞 K), s ∉ Pg g hg →
      s * u ∈ Ideal.span {(c : 𝓞 K)} → A.valuation (g u) ≤ A.valuation (c : Ω) := by
    intro g hg s u hs hsu
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hsu
    have hs1 : A.valuation (g s) = 1 :=
      le_antisymm (hint (hg s)) (not_lt.mp fun h => hs ((memPg g hg s).2 h))
    have := congrArg (fun y => A.valuation (g y)) hw
    simp only [map_mul, map_natCast, hs1, one_mul] at this
    rw [← this]
    exact mul_le_of_le_one_left' (hint (hg w))
  have hcP' : (c : 𝓞 K) ∈ Pg f fint := (memPg f fint _).2 (by rwa [map_natCast])
  have hPne : Pg f fint ≠ ⊥ := fun h => by
    have h' := hcP'
    rw [h, Ideal.mem_bot] at h'
    exact hc (by exact_mod_cast h')
  haveI hPmax : (Pg f fint).IsMaximal := Ideal.IsPrime.isMaximal (primePg f fint) hPne
  have hI : Ideal.span {(c : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hc
  classical
  obtain ⟨J, hPJ, hIJ⟩ := Ideal.eq_prime_pow_mul_coprime hI (Pg f fint)
  set a := Multiset.count (Pg f fint)
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(c : 𝓞 K)})) with ha
  have hJP : J ⊔ Pg f fint ^ a = ⊤ := Ideal.sup_pow_eq_top (by rwa [sup_comm])
  have h1mem : (1 : 𝓞 K) ∈ J ⊔ Pg f fint ^ a := by rw [hJP]; exact Submodule.mem_top
  obtain ⟨z, hz, y, hy, hzy⟩ := Submodule.mem_sup.1 h1mem
  obtain ⟨s, hsJ, hsP⟩ : ∃ s ∈ J, s ∉ Pg f fint := by
    by_contra hcon
    push_neg at hcon
    rw [sup_eq_left.2 hcon] at hPJ
    exact hPmax.ne_top hPJ
  have hz1 : z - 1 ∈ Pg f fint ^ a := by
    have e : z - 1 = -y := by rw [← hzy]; ring
    rw [e]; exact neg_mem hy
  refine ⟨f z, (algebraMap (𝓞 K) K z).2, fint z, ?_, ?_⟩
  · have := key f fint s (z - 1) hsP (by rw [hIJ, mul_comm s]; exact Ideal.mul_mem_mul hz1 hsJ)
    simpa only [map_sub, map_one] using this
  · rintro σ ⟨x, hxK, hxint, hx⟩
    set g : 𝓞 K →+* Ω := (σ : Ω →+* Ω).comp f with hg
    have gint : ∀ r, IsIntegral ℤ (g r) := fun r => (fint r).map (σ : Ω →+* Ω).toIntAlgHom
    have hxK' : IsIntegral ℤ (⟨x, hxK⟩ : K) :=
      (isIntegral_algHom_iff (algebraMap K Ω).toIntAlgHom (algebraMap K Ω).injective).1 hxint
    let r : 𝓞 K := ⟨⟨x, hxK⟩, hxK'⟩
    have hne : Pg g gint ≠ Pg f fint := by
      intro heq
      apply hx
      have h1 := memPg g gint r
      have h2 := memPg f fint r
      rw [heq] at h1
      exact h1.symm.trans h2
    obtain ⟨s', hs'P, hs'Q⟩ : ∃ s' ∈ Pg f fint ^ a, s' ∉ Pg g gint := by
      by_contra hcon
      push_neg at hcon
      haveI := primePg g gint
      have h1 : Pg f fint ≤ Pg g gint := Ideal.IsPrime.le_of_pow_le hcon
      exact hne (hPmax.eq_of_le (primePg g gint).ne_top h1).symm
    have := key g gint s' z hs'Q (by rw [hIJ]; exact Ideal.mul_mem_mul hs'P hz)
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfMulLeftCharpolySeparable
section
open Polynomial

namespace GlobalTheory.SepGenElt

theorem exists_aeval_eq : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A),
    (LinearMap.mulLeft E g).charpoly.Separable → ∀ x : A, ∃ p : E[X], aeval g p = x := by
  intro E A _ _ _ _ g hs x
  have hx : x ∈ Algebra.adjoin E ({g} : Set A) := by
    rw [GlobalTheory.SepGen.adjoin_eq_top g hs]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  exact hx

end GlobalTheory.SepGenElt
end

