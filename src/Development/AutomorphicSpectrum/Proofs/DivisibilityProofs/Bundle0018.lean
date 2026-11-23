module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0016

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagM3FromLocal
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3

noncomputable section

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_support_finite (P : Ideal (MRing ι O)) (f : MRing ι O) :
    (Function.support (divCycle P f)).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  simp [divCycle, h]

theorem C_not_mem {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {a : O} (ha : a ≠ 0) :
    (C a : MRing ι O) ∉ P := by
  intro h
  have h' : a ∈ P.comap (C : O →+* MRing ι O) := h
  rw [hP.noTorsion] at h'
  exact ha (by simpa using h')

theorem laNum_eq (P : Ideal (MRing ι O)) (a : O) {r : ℕ} (x : Fin r → K → ℤ) (k : ℕ)
    (Q : List (K → ℤ)) :
    ((laNum P a x k Q : ℤ) : ℝ) =
      (k : ℝ) * cycNum (divCycle P (C a)) x (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ (k - 1)) Q := by
  have h := (cycNum_int_and_comb O K ι (Fin r) x Q).1 (divCycle P (C a))
    (divCycle_support_finite P (C a)) (psum (Fin r) ℤ (k - 1))
  have e : MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin r) ℤ (k - 1)) =
      ∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ (k - 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [psum, map_sum]
  rw [e] at h
  rw [h, laNum]
  push_cast
  rfl

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ]

theorem liePs_inl (j j' m : ℕ) (τ : Ψ) :
    (liePs (N := j + j') j m (Sum.inl τ) : MvPolynomial (Ψ × Fin (j + j')) ℝ) =
      rename (fun i : Fin j => (τ, Fin.castAdd j' i))
        (∑ i : Fin j, (X i : MvPolynomial (Fin j) ℝ) ^ m) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [liePs, map_sum, map_pow, rename_X, Finset.sum_filter, Fin.sum_univ_add]
  simp

theorem liePs_inr (j j' m : ℕ) (τ : Ψ) :
    (liePs (N := j + j') j m (Sum.inr τ) : MvPolynomial (Ψ × Fin (j + j')) ℝ) =
      rename (fun i : Fin j' => (τ, Fin.natAdd j i))
        (∑ i : Fin j', (-(X i : MvPolynomial (Fin j') ℝ)) ^ m) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [liePs, map_sum, map_pow, map_neg, rename_X, Finset.sum_filter, Fin.sum_univ_add]
  have h0 : ∀ x : Fin j, ¬ j ≤ (x : ℕ) := fun x => not_le.2 x.2
  simp [h0]

theorem cycNum_neg {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d)
    {a : O} (ha : a ≠ 0) {r : ℕ} (cls : Fin r → K → ℤ) (m : ℕ) (Q : List (K → ℤ))
    (hQ : m + Q.length = d) :
    cycNum (divCycle P (C a)) (fun i => -cls i) (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m) Q =
      cycNum (divCycle P (C a)) cls (∑ i : Fin r, (-(X i : MvPolynomial (Fin r) ℝ)) ^ m) Q := by
  have hC : IsMultiHomog (C a : MRing ι O) (0 : K → ℕ) := isWeightedHomogeneous_C _ a
  have hH : (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m).IsHomogeneous m :=
    IsHomogeneous.sum _ _ _ fun i _ => by
      simpa using (isHomogeneous_X ℝ i).pow m
  have h := (_root_.GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear_subst O ϖ hϖ K ι P d hP 0 0 (C a) (C a) hC hC (C_not_mem hP ha) (C_not_mem hP ha)
    (Fin r) (Fin r) cls (fun t i => if t = i then -1 else 0) _ m hH Q hQ).2
  have e1 : (fun t : Fin r => ∑ i, (if t = i then (-1 : ℤ) else 0) • cls i) = fun i => -cls i := by
    funext t
    simp
  have e2 : aeval (fun t : Fin r => ∑ i, (C (((if t = i then (-1 : ℤ) else 0 : ℤ)) : ℝ) * X i :
      MvPolynomial (Fin r) ℝ)) (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m) =
      ∑ i : Fin r, (-(X i : MvPolynomial (Fin r) ℝ)) ^ m := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, apply_ite]
  rw [e1, e2] at h
  exact h

end

end GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3

namespace GlobalTheory.CompanionTheory.Ar.Num


open GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3 in
theorem flag_m3_of_local_m3 : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (p : ℕ), (p : O) ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j j' : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair ι O (Ψ × Fin (j + j'))) (lie : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j) (fun _ : Ψ => j')) σ))) (om : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j') (fun _ : Ψ => j)) σ))), (∀ τ, lie (Sum.inl τ) = T.comp fun i : Fin j => (τ, Fin.castAdd j' i)) → (∀ τ, om (Sum.inl τ) = T.comp fun i : Fin j' => (τ, Fin.natAdd j i)) → (∀ τ k Q, Q.length + k = d + 1 → laNum P (p : O) (lie (Sum.inr τ)).x k Q = laNum P (p : O) (fun i : Fin j' => -T.x (τ, Fin.natAdd j i)) k Q) → LabelChernComparison P d p φ lie om → FlagChernComparison P d p j φ T := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP p hp Ψ _ _ j j' φ T lie om hl ho hr hM τ k hk Q hQ
  set Z := divCycle P (C (p : O)) with hZ
  have hm : k - 1 + Q.length = d := by omega

  have hlab : ∀ τ' : Ψ ⊕ Ψ, ((laNum P (p : O) (lie τ').x k Q : ℤ) : ℝ) =
      (k : ℝ) * cycNum Z T.x (liePs j (k - 1) τ') Q := by
    rintro (t | t)
    · have e : (lie (Sum.inl t)).x = fun i : Fin j => T.x (t, Fin.castAdd j' i) := by
        rw [hl t]; rfl
      have e' : ((laNum P (p : O) (lie (Sum.inl t)).x k Q : ℤ) : ℝ) =
          ((laNum P (p : O) (fun i : Fin j => T.x (t, Fin.castAdd j' i)) k Q : ℤ) : ℝ) :=
        congrArg (fun y : Fin j → K → ℤ => ((laNum P (p : O) y k Q : ℤ) : ℝ)) e
      rw [e', laNum_eq, liePs_inl, (_root_.GlobalTheory.CompanionTheory.Ar.Num.numbers_rename).1 O K ι _ _ _ Z T.x]
      rfl
    · rw [hr t k Q hQ, laNum_eq, cycNum_neg hϖ hP hp _ _ Q hm, liePs_inr,
        (_root_.GlobalTheory.CompanionTheory.Ar.Num.numbers_rename).1 O K ι _ _ _ Z T.x]
      rfl
  have hL := hM k hk Q hQ (Sum.inl τ)
  have e1 : (lie (Sum.inl τ)).ck P k Q = (T.comp fun i : Fin j => (τ, Fin.castAdd j' i)).ck P k Q :=
    congrArg (fun L : LocPair ι O (Fin j) => L.ck P k Q) (hl τ)
  have e2 : (om (Sum.inl τ)).ck P k Q = (T.comp fun i : Fin j' => (τ, Fin.natAdd j i)).ck P k Q :=
    congrArg (fun L : LocPair ι O (Fin j') => L.ck P k Q) (ho τ)
  have hadd := _root_.GlobalTheory.CompanionTheory.Ar.Num.CkAppend.ck_append O K ι j j' (T.comp fun i : Fin (j + j') => (τ, i)) P k Q
  have hlin := _root_.GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear O K ι (Ψ × Fin (j + j')) Z T.x Q
  rw [e1, e2] at hL
  have hleft : (((T.comp fun i : Fin (j + j') => (τ, i)).ck P k Q : ℤ) : ℝ) =
      (((T.comp fun i : Fin j => (τ, Fin.castAdd j' i)).ck P k Q : ℤ) : ℝ) +
      (((T.comp fun i : Fin j' => (τ, Fin.natAdd j i)).ck P k Q : ℤ) : ℝ) := by
    rw [hadd]
    push_cast
    rfl
  rw [hleft, hL, bracket]
  rw [hlin.2.1, hlin.2.2.1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ' _ => ?_
  rw [hlin.2.1, hlab τ']
  ring

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RhoCoeffGapDeltaOne
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffDelta

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem degree_prod_monic {σ ι : Type*} (m : MonomialOrder σ) (s : Finset ι)
    (P : ι → MvPolynomial σ ℝ) (d : ι → σ →₀ ℕ)
    (h : ∀ i ∈ s, m.degree (P i) = d i ∧ m.leadingCoeff (P i) = 1) :
    m.degree (∏ i ∈ s, P i) = ∑ i ∈ s, d i ∧ m.leadingCoeff (∏ i ∈ s, P i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [m.degree_one, m.leadingCoeff_one]
  | insert a s has ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨ha1, ha2⟩ := h a (Finset.mem_insert_self a s)
    have hne : ∀ f : MvPolynomial σ ℝ, m.leadingCoeff f = 1 → f ≠ 0 := fun f hf =>
      m.leadingCoeff_ne_zero_iff.mp (by rw [hf]; exact one_ne_zero)
    rw [Finset.prod_insert has, Finset.sum_insert has,
      m.degree_mul (hne _ ha2) (hne _ ih2), m.leadingCoeff_mul, ha1, ih1, ha2, ih2]
    simp

theorem lex_sum_Ico {σ : Type*} [LinearOrder σ] [WellFoundedGT σ] {n : ℕ} (v : Fin n → σ)
    (hv : StrictMono v) {a b : Fin n} (hab : a < b) :
    (MonomialOrder.lex : MonomialOrder σ).degree (∑ s ∈ Finset.Ico a b, (X (v s) : MvPolynomial σ ℝ))
        = Finsupp.single (v a) 1 ∧
      (MonomialOrder.lex : MonomialOrder σ).leadingCoeff
        (∑ s ∈ Finset.Ico a b, (X (v s) : MvPolynomial σ ℝ)) = 1 := by
  have hlt : ∀ s, a < s → (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v s) 1) <
      (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v a) 1) := fun s hs =>
    MonomialOrder.lex_lt_iff.mpr (Finsupp.Lex.single_strictAnti (hv hs))
  have hzero : (MonomialOrder.lex : MonomialOrder σ).toSyn 0 <
      (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v a) 1) := by
    rw [map_zero, ← MonomialOrder.bot_eq_zero]
    refine bot_lt_iff_ne_bot.mpr fun h => ?_
    rw [MonomialOrder.bot_eq_zero] at h
    have h0 := (MonomialOrder.lex : MonomialOrder σ).toSyn.injective (h.trans (map_zero _).symm)
    simp at h0
  have hdegX : (MonomialOrder.lex : MonomialOrder σ).degree (X (v a) : MvPolynomial σ ℝ)
      = Finsupp.single (v a) 1 := MonomialOrder.degree_X
  have hrest : (MonomialOrder.lex : MonomialOrder σ).toSyn
      ((MonomialOrder.lex : MonomialOrder σ).degree
        (∑ s ∈ Finset.Ioo a b, (X (v s) : MvPolynomial σ ℝ))) <
      (MonomialOrder.lex : MonomialOrder σ).toSyn
        ((MonomialOrder.lex : MonomialOrder σ).degree (X (v a) : MvPolynomial σ ℝ)) := by
    rw [hdegX, MonomialOrder.degree_lt_iff hzero]
    intro c hc
    obtain ⟨s, hs, hcs⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hc)
    rw [X, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hcs
    rw [hcs]
    exact hlt s (Finset.mem_Ioo.mp hs).1
  rw [← Finset.Ioo_insert_left hab, Finset.sum_insert (by simp)]
  refine ⟨?_, ?_⟩
  · rw [MonomialOrder.degree_add_of_lt hrest, hdegX]
  · rw [MonomialOrder.leadingCoeff_add_of_lt hrest, MonomialOrder.leadingCoeff_X]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffDelta

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem rhoM_eq_sum (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    (∑ τ : Ψ, ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, Finsupp.single (τ, a) 1 : (Ψ × Fin N) →₀ ℕ)
      = rhoM Ψ N := by
  ext ⟨τ, a⟩
  simp only [Finset.sum_apply', Finsupp.single_apply, Prod.mk.injEq]
  rw [Finset.sum_eq_single τ, Finset.sum_eq_single a]
  · simp [rhoM, Fin.card_Ioi]
  · intro b _ hb; simp [hb]
  · simp
  · intro τ' _ h; simp [h]
  · simp

theorem coeff_rhoM_gapDelta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    AddMonoidAlgebra.coeff (gapDelta Ψ N) (rhoM Ψ N) = 1 := by
  let e := Fintype.equivFin Ψ
  letI : LinearOrder (Ψ × Fin N) :=
    LinearOrder.lift' (fun p => toLex (e p.1, p.2)) (fun p q h => by
      have h' : (e p.1, p.2) = (e q.1, q.2) := toLex.injective h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h'
      exact Prod.ext (e.injective h1) h2)
  haveI : WellFoundedGT (Ψ × Fin N) := Finite.to_wellFoundedGT
  have hv : ∀ τ : Ψ, StrictMono (fun s : Fin N => (τ, s)) := fun τ s t hst => by
    show toLex (e τ, s) < toLex (e τ, t)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hst⟩)
  have key := CoeffDelta.degree_prod_monic (MonomialOrder.lex : MonomialOrder (Ψ × Fin N))
    Finset.univ
    (fun τ : Ψ => ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, ∑ s ∈ Finset.Ico a b, (X (τ, s) : MvPolynomial _ ℝ))
    (fun τ => ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, Finsupp.single (τ, a) 1)
    (fun τ _ => CoeffDelta.degree_prod_monic _ Finset.univ _ _ fun a _ =>
      CoeffDelta.degree_prod_monic _ _ _ _ fun b hb =>
        CoeffDelta.lex_sum_Ico (fun s => (τ, s)) (hv τ) (Finset.mem_Ioi.mp hb))
  have h2 := key.2
  rw [MonomialOrder.leadingCoeff, key.1, rhoM_eq_sum] at h2
  exact h2

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SymmetricFormPolynomialCoeff
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym

open MvPolynomial Finset

variable {σ : Type} [Fintype σ] [DecidableEq σ] {n : ℕ}

def letterCount (w : Fin n → σ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => (univ.filter fun r => w r = p).card

theorem letterCount_apply (w : Fin n → σ) (p : σ) :
    letterCount w p = (univ.filter fun r => w r = p).card := rfl

theorem prod_X_eq_monomial (w : Fin n → σ) :
    (∏ j, (X (w j) : MvPolynomial σ ℝ)) = monomial (letterCount w) 1 := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    ← Finset.prod_fiberwise univ w]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Finset.prod_congr rfl (g := fun _ => (X p : MvPolynomial σ ℝ))
    (fun j hj => by rw [(Finset.mem_filter.1 hj).2])]
  simp [letterCount_apply]

theorem letterCount_comp (w : Fin n → σ) (π : Equiv.Perm (Fin n)) :
    letterCount (w ∘ π) = letterCount w := by
  ext p
  rw [letterCount_apply, letterCount_apply]
  exact Finset.card_equiv π (fun r => by simp)

theorem exists_perm_of_letterCount_eq (w w₀ : Fin n → σ) (h : letterCount w = letterCount w₀) :
    ∃ π : Equiv.Perm (Fin n), w₀ ∘ π = w := by
  have e : ∀ p, {r // w r = p} ≃ {r // w₀ r = p} := fun p => Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact DFunLike.congr_fun h p)
  exact ⟨Equiv.ofFiberEquiv e, funext fun r => Equiv.ofFiberEquiv_map e r⟩

theorem card_letterCount_mul (w₀ : Fin n → σ) :
    (univ.filter fun w : Fin n → σ => letterCount w = letterCount w₀).card *
      ∏ p, (letterCount w₀ p).factorial = n.factorial := by
  have hst : Fintype.card {g : Equiv.Perm (Fin n) // w₀ ∘ g = w₀} =
      ∏ p, (letterCount w₀ p).factorial := by
    rw [DomMulAct.stabilizer_card]
    exact Finset.prod_congr rfl fun p _ => by rw [Fintype.card_subtype, letterCount_apply]
  have hcard : (univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
    simp [Finset.card_univ, Fintype.card_perm]
  have hfib : ∀ w ∈ univ.filter (fun w : Fin n → σ => letterCount w = letterCount w₀),
      (univ.filter fun π : Equiv.Perm (Fin n) => w₀ ∘ π = w).card =
        Fintype.card {g : Equiv.Perm (Fin n) // w₀ ∘ g = w₀} := by
    intro w hw
    obtain ⟨π₀, rfl⟩ := exists_perm_of_letterCount_eq w w₀ (Finset.mem_filter.1 hw).2
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.mulRight π₀⁻¹) fun g => ?_)
    constructor
    · intro h
      funext r
      have := congrFun h (π₀⁻¹ r)
      simpa using this
    · intro h
      funext r
      have := congrFun h (π₀ r)
      simpa using this
  rw [← hst, ← hcard, Finset.card_eq_sum_card_fiberwise (s := univ)
    (f := fun π : Equiv.Perm (Fin n) => w₀ ∘ π)
    (t := univ.filter fun w : Fin n → σ => letterCount w = letterCount w₀)
    (fun π _ => by simp [letterCount_comp]), Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

theorem coeff_formPoly_mul (σ : Type) [Fintype σ] [DecidableEq σ] (n : ℕ) (a : (Fin n → σ) → ℝ)
    (hsym : ∀ (π : Equiv.Perm (Fin n)) (w : Fin n → σ), a (w ∘ π) = a w) (w₀ : Fin n → σ) (m : σ →₀ ℕ)
    (hm : ∀ p, m p = (Finset.univ.filter fun r => w₀ r = p).card) :
    AddMonoidAlgebra.coeff (PB.formPoly n a) m * ∏ p, ((m p).factorial : ℝ) = (n.factorial : ℝ) * a w₀ := by
  obtain rfl : m = letterCount w₀ := Finsupp.ext fun p => by rw [hm, letterCount_apply]
  have hc : AddMonoidAlgebra.coeff (PB.formPoly n a) (letterCount w₀) =
      ((univ.filter fun w : Fin n → σ => letterCount w = letterCount w₀).card : ℝ) * a w₀ := by
    unfold PB.formPoly
    rw [coeff_sum, ← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [prod_X_eq_monomial, coeff_C_mul, coeff_monomial]
    by_cases h : letterCount w = letterCount w₀
    · obtain ⟨π, rfl⟩ := exists_perm_of_letterCount_eq w w₀ h
      simp [letterCount_comp, hsym]
    · simp [h]
  rw [hc, ← card_letterCount_mul w₀]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.WeightGapDeltaEqAntisymmetric
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

def xAt {Ψ : Type} {N : ℕ} (τ : Ψ) (i : ℕ) : MvPolynomial (Ψ × Fin N) ℝ :=
  if h : i < N then X (τ, ⟨i, h⟩) else 0

theorem xAt_val {Ψ : Type} {N : ℕ} (τ : Ψ) (a : Fin N) :
    (xAt τ (a : ℕ) : MvPolynomial (Ψ × Fin N) ℝ) = X (τ, a) := by
  simp [xAt]

theorem gapX_eq_xAt_sub {Ψ : Type} {N : ℕ} (τ : Ψ) (s : Fin N) :
    PB.gapX (τ, s) = xAt τ (s : ℕ) - xAt τ ((s : ℕ) + 1) := by
  simp [PB.gapX, xAt]

theorem sum_gapX_Ico {Ψ : Type} {N : ℕ} (τ : Ψ) {a b : Fin N} (hab : a ≤ b) :
    ∑ s ∈ Finset.Ico a b, PB.gapX (τ, s) = X (τ, a) - X (τ, b) := by
  have h1 : ∑ s ∈ Finset.Ico a b, PB.gapX (τ, s)
      = ∑ i ∈ Finset.Ico (a : ℕ) (b : ℕ),
          ((xAt τ i : MvPolynomial (Ψ × Fin N) ℝ) - xAt τ (i + 1)) := by
    rw [← Fin.map_valEmbedding_Ico, Finset.sum_map]
    exact Finset.sum_congr rfl fun s _ => gapX_eq_xAt_sub τ s
  have hle : (a : ℕ) ≤ b := hab
  have h2 : ∀ n : ℕ, ∑ i ∈ Finset.Ico (a : ℕ) ((a : ℕ) + n),
      ((xAt τ i : MvPolynomial (Ψ × Fin N) ℝ) - xAt τ (i + 1))
        = xAt τ (a : ℕ) - xAt τ ((a : ℕ) + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, Finset.sum_Ico_succ_top (Nat.le_add_right _ _), ih]
      ring
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hle
  rw [h1, hn, h2, ← hn, xAt_val, xAt_val]

theorem toWt_gapDelta_eq_antisymDelta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    PB.toWt (gapDelta Ψ N) = GroundTheory.Heights₂.Heights.antisymDelta Ψ N := by
  unfold gapDelta GroundTheory.Heights₂.Heights.antisymDelta
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_prod, map_sum]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun a _ =>
    Finset.prod_congr rfl fun b hb => ?_
  have hab : a ≤ b := (Finset.mem_Ioi.1 hb).le
  rw [← sum_gapX_Ico τ hab]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [PB.toWt]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.WeightMapInjective
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem aeval_tail_gapX {Ψ : Type} {N : ℕ} (p : Ψ × Fin N) :
    (aeval (fun q : Ψ × Fin N => ∑ s ∈ Finset.Ici q.2, (X (q.1, s) : MvPolynomial (Ψ × Fin N) ℝ)))
      (PB.gapX p) = X p := by
  obtain ⟨τ, i⟩ := p
  simp only [PB.gapX, map_sub, aeval_X]
  split_ifs with h
  · rw [aeval_X]
    have hI : Finset.Ici i = insert i (Finset.Ici (⟨(i : ℕ) + 1, h⟩ : Fin N)) := by
      ext s
      have := s.2
      simp only [Finset.mem_Ici, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
      omega
    rw [hI, Finset.sum_insert (by simp [Fin.le_def])]
    ring
  · have hI : Finset.Ici i = {i} := by
      ext s
      have := s.2
      simp only [Finset.mem_Ici, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    rw [map_zero, sub_zero, hI, Finset.sum_singleton]

theorem toWt_leftInverse_injective (Ψ : Type) (N : ℕ) :
    Function.Injective (PB.toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ) := by
  set T : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ := aeval (fun q : Ψ × Fin N => ∑ s ∈ Finset.Ici q.2, (X (q.1, s) : MvPolynomial (Ψ × Fin N) ℝ)) with hT
  have hli : T.comp PB.toWt = AlgHom.id ℝ _ := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, AlgHom.id_apply, PB.toWt, aeval_X, hT]
    exact aeval_tail_gapX p
  intro a b hab
  have ha : T (PB.toWt a) = a := by rw [← AlgHom.comp_apply, hli, AlgHom.id_apply]
  have hb : T (PB.toWt b) = b := by rw [← AlgHom.comp_apply, hli, AlgHom.id_apply]
  rw [← ha, ← hb, hab]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end

