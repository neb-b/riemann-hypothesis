module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DualWeightVectorApplyEqZeroOfNeNeg
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section pairing

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem dualOperators_apply (E : GLOps n K V) (a b : Fin n) (φ : Module.Dual K V) (x : V) :
    dualOps E a b φ x = -φ (E a b x) := rfl

theorem pow_dualOperators_apply (E : GLOps n K V) (a b : Fin n) (k : ℕ) (φ : Module.Dual K V) (x : V) :
    ((dualOps E a b) ^ k) φ x = (-1 : K) ^ k * φ (((E a b) ^ k) x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' (dualOps E a b), Module.End.mul_apply, dualOperators_apply, ih, pow_succ (E a b), Module.End.mul_apply]
    ring

theorem dividedPower_dualOperators_apply (E : GLOps n K V) (a b : Fin n) (k : ℕ) (φ : Module.Dual K V) (x : V) :
    divPowE (dualOps E) a b k φ x = (-1 : K) ^ k * φ (divPowE E a b k x) := by
  simp only [divPowE, LinearMap.smul_apply, smul_eq_mul, pow_dualOperators_apply, map_smul]
  ring

private theorem wt_apply_lemma_3 {m : ℕ} {L W : Type*} [Field L] [AddCommGroup W] [Module L W] {E : GLOps m L W}
    {nu : Fin m → ℤ} {x : W} (hx : x ∈ weightSp E nu) (a : Fin m) : E a a x = (nu a : L) • x := by
  have h := (Submodule.mem_iInf _).1 hx a
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h

private theorem prod_eval_lemma_2 {L W : Type*} [Field L] [AddCommGroup W] [Module L W] (D : Module.End L W)
    (ev : W → L) (hsub : ∀ w w', ev (w - w') = ev w - ev w') (hsmul : ∀ (c : L) w, ev (c • w) = c * ev w)
    (c : L) (hD : ∀ w, ev (D w) = c * ev w) (k : ℕ) (w : W) :
    ev (((List.range k).map fun j : ℕ => D - (j : L) • (1 : Module.End L W)).prod w) =
      ((List.range k).map fun j : ℕ => (c - j)).prod * ev w := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, _root_.mul_one]
    rw [Module.End.mul_apply, ih, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hsub, hsmul, hD]
    ring

private theorem binom_scalar_lemma {L : Type*} [Field L] [CharZero L] (m : ℤ) (k : ℕ) :
    (k.factorial : L)⁻¹ * ((List.range k).map fun j : ℕ => ((m : L) - j)).prod = ((Ring.choose m k : ℤ) : L) := by
  let E' : GLOps 1 L L := fun _ _ => (m : L) • 1
  have hw : (1 : L) ∈ weightSp E' (fun _ => m) := by
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker]
    intro a
    simp [E']
  have h1 := binomial_diagonal_on_weight hw 0 k
  have h2 := prod_eval_lemma_2 (E' 0 0) id (fun _ _ => rfl) (fun _ _ => rfl) (m : L) (fun w => by simp [E']) k 1
  simp only [binomE, LinearMap.smul_apply, smul_eq_mul, id] at h1 h2
  rw [h2] at h1
  simpa using h1

theorem binomialDual_apply_weightVector [CharZero K] (E : GLOps n K V) (a : Fin n) (k : ℕ) (φ : Module.Dual K V) {nu : Fin n → ℤ}
    {x : V} (hx : x ∈ weightSp E nu) :
    binomE (dualOps E) a k φ x = ((Ring.choose (-(nu a)) k : ℤ) : K) * φ x := by
  have e := wt_apply_lemma_3 hx a
  have hD : ∀ ψ : Module.Dual K V, (dualOps E a a ψ) x = ((-(nu a) : ℤ) : K) * ψ x := by
    intro ψ
    rw [dualOperators_apply, e, map_smul, smul_eq_mul]
    push_cast
    ring
  unfold binomE
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    prod_eval_lemma_2 (dualOps E a a) (fun ψ => ψ x) (fun _ _ => LinearMap.sub_apply _ _ _)
      (fun _ _ => LinearMap.smul_apply _ _ _) _ hD k φ, ← mul_assoc, binom_scalar_lemma]

theorem apply_binomial_of_dual_weightVector [CharZero K] (E : GLOps n K V) (a : Fin n) (k : ℕ) {nu : Fin n → ℤ} {φ : Module.Dual K V}
    (hφ : φ ∈ weightSp (dualOps E) nu) (x : V) :
    φ (binomE E a k x) = ((Ring.choose (-(nu a)) k : ℤ) : K) * φ x := by
  have e := wt_apply_lemma_3 hφ a
  have hD : ∀ y, φ (E a a y) = ((-(nu a) : ℤ) : K) * φ y := by
    intro y
    have h := congrArg (fun ψ : Module.Dual K V => ψ y) e
    simp only [dualOperators_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [neg_eq_iff_eq_neg] at h
    rw [h]
    push_cast
    ring
  unfold binomE
  rw [LinearMap.smul_apply, map_smul, smul_eq_mul,
    prod_eval_lemma_2 (E a a) φ (fun _ _ => map_sub _ _ _) (fun _ _ => map_smul _ _ _) _ hD k x, ← mul_assoc,
    binom_scalar_lemma]

end pairing

section weights

variable {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem dual_weightVector_apply_eq_zero_of_ne_neg (E : GLOps n K V) {nu' nu : Fin n → ℤ} {φ : Module.Dual K V} {x : V}
    (hφ : φ ∈ weightSp (dualOps E) nu') (hx : x ∈ weightSp E nu) (hne : nu' ≠ -nu) : φ x = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, nu' a ≠ -nu a := by
    by_contra h
    push_neg at h
    exact hne (funext fun a => by rw [h a, Pi.neg_apply])
  have e1 := wt_apply_lemma_3 hx a
  have e2 := wt_apply_lemma_3 hφ a
  have e3 := congrArg (fun ψ : Module.Dual K V => ψ x) e2
  simp only [dualOperators_apply, LinearMap.smul_apply, smul_eq_mul, e1, map_smul] at e3
  have h4 : ((nu a + nu' a : ℤ) : K) * φ x = 0 := by
    push_cast
    linear_combination -e3
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd h (Int.cast_ne_zero.2 (by omega))
  · exact h

end weights

section lattice

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def Oval (O : Type*) [CommRing O] [IsDomain O] (c : KK O) : Prop := c ∈ Set.range (algebraMap O (KK O))

theorem Oval.add {a b : KK O} (ha : Oval O a) (hb : Oval O b) : Oval O (a + b) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  exact ⟨a + b, map_add _ _ _⟩

theorem Oval.mul {a b : KK O} (ha : Oval O a) (hb : Oval O b) : Oval O (a * b) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  exact ⟨a * b, map_mul _ _ _⟩

theorem Oval.int (z : ℤ) : Oval O ((z : ℤ) : KK O) := ⟨z, map_intCast _ z⟩

theorem Oval.zero : Oval O (0 : KK O) := ⟨0, map_zero _⟩

theorem Oval.sum {ι : Type*} (s : Finset ι) (f : ι → KK O) (h : ∀ i ∈ s, Oval O (f i)) : Oval O (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (Oval O) (fun _ _ => Oval.add) Oval.zero h

theorem Oval.negOnePow (k : ℕ) : Oval O ((-1 : KK O) ^ k) := ⟨(-1) ^ k, by simp⟩

theorem stableLattice_weight_decomposition [CharZero (KK O)] (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤)
    (M : Submodule O V) (hM : UZStable (O := O) E M) {x : V} (hx : x ∈ M) :
    ∃ f : (Fin n → ℤ) →₀ V, (∀ nu, f nu ∈ weightSp E nu) ∧ (∀ nu, f nu ∈ M) ∧ x = ∑ nu ∈ f.support, f nu := by
  classical
  have hx' : x ∈ ⨆ mu, ⨆ (_ : True), weightSp E mu := by
    rw [show (⨆ mu, ⨆ (_ : True), weightSp E mu) = ⨆ mu, weightSp E mu by simp, hE]
    exact Submodule.mem_top
  obtain ⟨F, f, hf, rfl⟩ := mem_weight_sup_exists_finset_sum E (fun _ => True) hx'
  obtain ⟨P, hPM, hP1, hP0⟩ := exists_integral_weight_projections E F
  have hcomp : ∀ nu ∈ F, P nu (∑ mu ∈ F, f mu) = f nu := by
    intro nu hnu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single nu]
    · exact hP1 nu _ (hf nu hnu).2
    · intro mu hmu hne
      exact hP0 nu mu hmu hne _ (hf mu hmu).2
    · intro h
      exact absurd hnu h
  let g : (Fin n → ℤ) →₀ V := Finsupp.onFinset F (fun mu => if mu ∈ F then f mu else 0)
    (by intro a ha; by_contra h; exact ha (if_neg h))
  refine ⟨g, fun nu => ?_, fun nu => ?_, ?_⟩
  · simp only [g, Finsupp.onFinset_apply]
    split_ifs with h
    · exact (hf nu h).2
    · exact Submodule.zero_mem _
  · simp only [g, Finsupp.onFinset_apply]
    split_ifs with h
    · rw [← hcomp nu h]
      exact hPM nu M hM _ hx
    · exact Submodule.zero_mem _
  · show _ = g.sum fun _ v => v
    rw [Finsupp.onFinset_sum _ (fun _ => rfl)]
    exact Finset.sum_congr rfl fun mu hmu => (if_pos hmu).symm

theorem integral_dual_preserved_by_integralMonoid [CharZero (KK O)] (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤)
    (M : Submodule O V) (hM : UZStable (O := O) E M) {u' : Module.End (KK O) (Module.Dual (KK O) V)}
    (hu : u' ∈ UZmon (dualOps E)) :
    ∀ ψ : Module.Dual (KK O) V, (∀ x ∈ M, Oval O (ψ x)) → ∀ x ∈ M, Oval O (u' ψ x) := by
  unfold UZmon at hu
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · intro ψ hψ x hx
      rw [dividedPower_dualOperators_apply]
      exact Oval.mul (Oval.negOnePow k) (hψ _ (hM _ (Or.inl ⟨a, b, k, hab, rfl⟩) x hx))
    · intro ψ hψ x hx
      obtain ⟨f, hfw, hfM, rfl⟩ := stableLattice_weight_decomposition E hE M hM hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Oval.sum _ _ fun nu _ => by
        rw [binomialDual_apply_weightVector E a k ψ (hfw nu)]
        exact Oval.mul (Oval.int _) (hψ _ (hfM nu))
  | one =>
    intro ψ hψ x hx
    exact hψ x hx
  | mul u v _ _ ihu ihv =>
    intro ψ hψ x hx
    exact ihu (v ψ) (ihv ψ hψ) x hx

theorem dualLattice_comp_integralMonoid_mem [CharZero (KK O)] (E : GLOps n (KK O) V)
    (hE' : (⨆ mu : Fin n → ℤ, weightSp (dualOps E) mu) = ⊤)
    (M' : Submodule O (Module.Dual (KK O) V)) (hM' : UZStable (O := O) (dualOps E) M')
    {u : Module.End (KK O) V} (hu : u ∈ UZmon E) : ∀ ψ ∈ M', ψ ∘ₗ u ∈ M' := by
  unfold UZmon at hu
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · intro ψ hψ
      have h1 : divPowE (dualOps E) a b k ψ ∈ M' := hM' _ (Or.inl ⟨a, b, k, hab, rfl⟩) ψ hψ
      have h2 : ψ ∘ₗ divPowE E a b k = (-1 : KK O) ^ k • divPowE (dualOps E) a b k ψ := by
        ext y
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, dividedPower_dualOperators_apply]
        rw [← mul_assoc, ← mul_pow]
        simp
      rw [h2]
      rcases neg_one_pow_eq_or (KK O) k with h | h
      · rw [h, one_smul]
        exact h1
      · rw [h, neg_one_smul]
        exact M'.neg_mem h1
    · intro ψ hψ
      obtain ⟨f, hfw, hfM, rfl⟩ := stableLattice_weight_decomposition (dualOps E) hE' M' hM' hψ
      have h3 : (∑ nu ∈ f.support, f nu) ∘ₗ binomE E a k =
          ∑ nu ∈ f.support, (Ring.choose (-(nu a)) k : ℤ) • f nu := by
        ext y
        simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]
        refine Finset.sum_congr rfl fun nu _ => ?_
        rw [apply_binomial_of_dual_weightVector E a k (hfw nu) y, ← Int.cast_smul_eq_zsmul (KK O), LinearMap.smul_apply, smul_eq_mul]
      rw [h3]
      exact Submodule.sum_mem _ fun nu _ => zsmul_mem (hfM nu) _
  | one =>
    intro ψ hψ
    rw [Module.End.one_eq_id, LinearMap.comp_id]
    exact hψ
  | mul u v _ _ ihu ihv =>
    intro ψ hψ
    rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    exact ihv _ (ihu ψ hψ)

end lattice

end Formalism.MainNotions.G.ColumnFamilies
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ExistsDominantTopWeightNonzero
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases

section basic

variable {L : Type} [CommRing L] {n : ℕ}

theorem partialAct_eq_fullAct_of_vars_lt (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L)
    {P : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ P.vars, x.1 < i) :
    actI isVec i g gi P = actAll isVec g gi P := by
  refine MvPolynomial.hom_congr_vars (f₁ := (actI isVec i g gi).toRingHom)
    (f₂ := (actAll isVec g gi).toRingHom) ?_ ?_ rfl
  · ext r
    simp
  · intro x hx _
    have hxi := hv x hx
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, actI, actAll, MvPolynomial.aeval_X, if_pos hxi]
    split_ifs
    · simp [Matrix.vecMul, dotProduct]
    · simp [Matrix.vecMul, dotProduct]

theorem partialAct_fix_of_vars_ge (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L)
    {Q : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ Q.vars, i ≤ x.1) :
    actI isVec i g gi Q = Q := by
  conv_rhs => rw [← AlgHom.id_apply (R := L) Q]
  refine MvPolynomial.hom_congr_vars (f₁ := (actI isVec i g gi).toRingHom)
    (f₂ := (AlgHom.id L (MvPolynomial (ℕ × Fin n) L)).toRingHom) ?_ ?_ rfl
  · ext r
    simp
  · intro x hx _
    have hxi : ¬ x.1 < i := not_lt.mpr (hv x hx)
    simp [actI, hxi]

theorem partialWeight_eq_torusWeight_of_lt (isVec : ℕ → Bool) (i : ℕ) {e : ℕ × Fin n →₀ ℕ} (h : ∀ x ∈ e.support, x.1 < i) :
    Finsupp.weight (wtI isVec i) e = Finsupp.weight (torusW isVec) e := by
  simp only [Finsupp.weight_apply]
  refine Finsupp.sum_congr (fun x hx => ?_)
  simp [wtI, h x hx]

theorem partialWeight_eq_zero_of_ge (isVec : ℕ → Bool) (i : ℕ) {e : ℕ × Fin n →₀ ℕ} (h : ∀ x ∈ e.support, i ≤ x.1) :
    Finsupp.weight (wtI (n := n) isVec i) e = 0 := by
  simp only [Finsupp.weight_apply]
  refine (Finsupp.sum_congr (g2 := fun _ _ => (0 : Fin n → ℤ)) (fun x hx => ?_)).trans (by simp)
  have hx' : ¬ x.1 < i := not_lt.mpr (h x hx)
  simp [wtI, hx']

theorem fullAct_pathWord_support_dominated (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ) (i : ℕ) (I' : ℤ → Finset (Fin n))
    (g : (Matrix (Fin n) (Fin n) L)ˣ) (hp : IsPath n isVec B μ i) (hI : IsIndex (μ i) I') :
    ∀ e ∈ (actAll isVec (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L)
        (psiPath L isVec μ i I')).support, DomLe (Finsupp.weight (torusW isVec) e) (μ i) := by
  intro e he
  refine (Top.factEV L n i isVec B μ I' g hp hI).1 _ ?_
  intro h0
  have h1 := congrArg (AddMonoidAlgebra.coeff · e) h0
  rw [coeff_weightedHomogeneousComponent, if_pos rfl] at h1
  exact (mem_support_iff.1 he) (by simpa using h1)

end basic

theorem restWord : RestWord := by
  classical
  intro L _ n N i isVec B μ I g gi hg hp hI hi e he
  rcases subsingleton_or_nontrivial L with hs | hnt
  · exfalso
    have h0 : actI isVec i g gi (psiPath L isVec μ N I) = 0 := Subsingleton.elim _ _
    rw [h0] at he
    simp at he
  have hpi : IsPath n isVec B μ i :=
    ⟨hp.1, fun j hj => hp.2.1 j (hj.trans hi), fun j hj => hp.2.2 j (lt_of_lt_of_le hj hi)⟩
  let gu : (Matrix (Fin n) (Fin n) L)ˣ := ⟨g, gi, hg, mul_eq_one_comm.1 hg⟩
  obtain ⟨F1, hF1⟩ := A3ev.exists_cols hp
  obtain ⟨F2, hF2⟩ := A3ev.exists_cols hpi
  obtain ⟨F, hF⟩ : ∃ F, F = F1 ∪ F2 := ⟨_, rfl⟩
  have hFN : A3ev.Cols isVec μ N F := fun c hc => hF1 c (fun h => hc (hF ▸ Finset.mem_union_left _ h))
  have hFi : A3ev.Cols isVec μ i F := fun c hc => hF2 c (fun h => hc (hF ▸ Finset.mem_union_right _ h))
  choose Q hQ1 hQ2 using fun c : ℤ => A0.trunc L n i isVec μ c N hi (I c)
  have hexp : psiPath L isVec μ N I = ∑ p ∈ F.pi (fun _ => (univ : Finset (Finset (Fin n)))),
      (∏ c ∈ F, pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) L)) i (A3ev.extF F p c)) *
        (∏ c ∈ F, Q c (A3ev.extF F p c)) := by
    rw [A3ev.psi_eq_prod L hFN hI, Finset.prod_congr rfl (fun c _ => hQ2 c), Finset.prod_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.prod_mul_distrib, ← Finset.prod_attach F]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp [A3ev.extF, x.2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hexp, map_sum] at he
  obtain ⟨p, -, hpe⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum he)
  obtain ⟨I', hI'⟩ : ∃ I', I' = A3ev.extF F p := ⟨_, rfl⟩
  rw [← hI'] at hpe
  by_cases hidx : IsIndex (μ i) I'
  · have h1 : ∏ c ∈ F, pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) L)) i (I' c) =
        psiPath L isVec μ i I' := (A3ev.psi_eq_prod L hFi hidx).symm
    rw [h1, map_mul] at hpe
    have hv1 : ∀ x ∈ (psiPath L isVec μ i I').vars, x.1 < i := by
      refine DominanceOrderLemmas.vars_of_polB (N := i) (B := B) ?_
      rw [polB, Submodule.mem_iInf]
      intro j
      exact (pathProductDegrees L n i isVec B μ I' hpi hidx).2 j
    have hv2 : ∀ x ∈ (∏ c ∈ F, Q c (I' c)).vars, i ≤ x.1 := by
      intro x hx
      obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 (vars_prod _ hx)
      exact (mem_supported.1 (hQ1 c (I' c))) (Finset.mem_coe.2 hc)
    rw [partialAct_eq_fullAct_of_vars_lt _ _ _ _ hv1, partialAct_fix_of_vars_ge _ _ _ _ hv2] at hpe
    obtain ⟨e1, he1, e2, he2, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ hpe)
    have hw2 : Finsupp.weight (wtI (n := n) isVec i) e2 = 0 :=
      partialWeight_eq_zero_of_ge isVec i fun x hx => hv2 x ((mem_vars_iff_mem_support x).2 ⟨e2, he2, hx⟩)
    have hw1 : Finsupp.weight (wtI isVec i) e1 = Finsupp.weight (torusW isVec) e1 :=
      partialWeight_eq_torusWeight_of_lt isVec i fun x hx =>
        DominanceOrderLemmas.vars_act isVec g gi hv1 x ((mem_vars_iff_mem_support x).2 ⟨e1, he1, hx⟩)
    rw [map_add (f := _), hw2, add_zero, hw1]
    exact fullAct_pathWord_support_dominated isVec B μ i I' gu hpi hidx e1 he1
  · exfalso
    have hz : ∏ c ∈ F, pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) L)) i (I' c) = 0 := by
      obtain ⟨c, hc⟩ := not_forall.1 (show ¬ ∀ c : ℤ, (I' c).card =
        if 1 ≤ c then colHeight (μ i) c else n - colHeight (μ i) c from hidx)
      have hcF : c ∈ F := by
        by_contra hn
        apply hc
        have h1 : I' c = ∅ := by rw [hI']; exact dif_neg hn
        have h2 := A1hw.isIndex_can (μ i) c
        rw [(hFi c hn).2 _ (A1hw.isIndex_can (μ i))] at h2
        rw [h1]
        exact h2
      refine Finset.prod_eq_zero hcF ?_
      by_contra hne
      exact hc (A0.pathWord_card hpi c _ i le_rfl _ hne)
    rw [hz, zero_mul, map_zero] at hpe
    simp at hpe

open A3ev DominanceOrderLemmas in
theorem exists_dominant_top_weight_nonzero (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ)
    (c : PathIdx n N isVec B →₀ k) (x₁ : PathIdx n N isVec B) (hx₁ : x₁ ∈ c.support) :
    ∃ μ₀, Antitone μ₀ ∧ DomLe (x₁.1.1 N) μ₀ ∧
      evC k n isVec μ₀ (c.sum fun x a => a • psiPath k isVec x.1.1 N x.1.2) ≠ 0 := by
  classical
  have hEV : FactEV := Top.factEV
  have hT : (c.support.filter fun x => DomLe (x₁.1.1 N) (x.1.1 N)).Nonempty :=
    ⟨x₁, Finset.mem_filter.2 ⟨hx₁, domLe_refl _⟩⟩
  obtain ⟨x₀, hx₀, hmax⟩ := Finset.exists_max_image _
    (fun x : PathIdx n N isVec B => height (x.1.1 N)) hT
  rw [Finset.mem_filter] at hx₀
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, x₀.1.1 N = μ₀ := ⟨_, rfl⟩
  have hanti : Antitone μ₀ := hμ₀ ▸ x₀.2.1.2.1 N le_rfl
  have hd₀ : DomLe (x₁.1.1 N) μ₀ := hμ₀ ▸ hx₀.2
  refine ⟨μ₀, hanti, hd₀, fun h1 => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, map_sum] at h1
  simp_rw [map_smul] at h1
  have h2 : ∑ x ∈ c.support.filter (fun x => x.1.1 N = μ₀), c x • fam k x = 0 := by
    have h3 := Finset.sum_filter_of_ne (s := c.support)
      (p := fun x : PathIdx n N isVec B => x.1.1 N = μ₀)
      (f := fun x => c x • evC k n isVec μ₀ (psiPath k isVec x.1.1 N x.1.2)) ?_
    · rw [← h1, ← h3]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_filter] at hx
      rw [evC_psi k μ₀ x.2.1 x.2.2.2.1, ← hx.2, (ev_gen hEV k x.2.1 x.2.2.2.1).2]
      unfold fam
      rw [smul_eq_C_mul]
    · intro x hx hne
      have he : evC k n isVec μ₀ (psiPath k isVec x.1.1 N x.1.2) ≠ 0 :=
        fun h => hne (by rw [h, smul_zero])
      rw [evC_psi k μ₀ x.2.1 x.2.2.2.1] at he
      have hd : DomLe μ₀ (x.1.1 N) := (ev_gen hEV k x.2.1 x.2.2.2.1).1 μ₀ he
      refine domLe_eq hd ?_
      rw [← hμ₀]
      exact hmax x (Finset.mem_filter.2 ⟨hx, domLe_trans hd₀ hd⟩)
  exact (Finsupp.mem_support_iff.1 hx₀.1) (linearIndepOn_iff'.1 (fam_li fact_break k n N isVec B μ₀ hanti) _ c
    (fun x hx => (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2) h2 x₀
    (Finset.mem_filter.2 ⟨hx₀.1, hμ₀⟩))

theorem restTop : RestTop := by
  classical
  intro k _ n N isVec B pi G hpi hG hgood
  have hG' : G ∈ Submodule.span k
      (Set.range fun x : PathIdx n N isVec B => psiPath k isVec x.1.1 N x.1.2) := by
    rw [(Top.psiPath_basis n N isVec B k).2]
    exact hG
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hG'
  have key : ∀ x ∈ c.support, x.1.1 N ∈ pi := by
    intro x hx
    obtain ⟨μ₀, ha, hd, hne⟩ := exists_dominant_top_weight_nonzero k n N isVec B c x hx
    rw [hc] at hne
    have hne' : weightedHomogeneousComponent (torusW isVec) μ₀
        (actAll isVec (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
          (map (algebraMap k (GenField k n)) G)) ≠ 0 := hne
    obtain ⟨e, he⟩ := MvPolynomial.ne_zero_iff.1 hne'
    rw [coeff_weightedHomogeneousComponent] at he
    split_ifs at he with hw
    · have hvG : ∀ y ∈ (map (algebraMap k (GenField k n)) G).vars, y.1 < N :=
        fun y hy => DominanceOrderLemmas.vars_of_polB hG y (vars_map G (algebraMap k (GenField k n)) hy)
      have hmem : e ∈ (actI isVec N (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
          (map (algebraMap k (GenField k n)) G)).support := by
        rw [partialAct_eq_fullAct_of_vars_lt _ _ _ _ hvG]
        exact mem_support_iff.2 he
      have hwt : Finsupp.weight (wtI isVec N) e = μ₀ := by
        rw [partialWeight_eq_torusWeight_of_lt]
        · exact hw
        · intro y hy
          exact DominanceOrderLemmas.vars_act isVec _ _ hvG y ((mem_vars_iff_mem_support y).2 ⟨e, mem_support_iff.2 he, hy⟩)
      have h3 := hgood e hmem (by rw [hwt]; exact ha)
      rw [hwt] at h3
      exact hpi μ₀ h3 _ (x.2.1.2.1 N le_rfl) hd
    · exact absurd rfl he
  rw [← hc]
  exact Submodule.sum_mem _ fun x hx =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, key x hx, rfl⟩)

end Formalism.MainNotions.G.ColumnFamilies
end
end

