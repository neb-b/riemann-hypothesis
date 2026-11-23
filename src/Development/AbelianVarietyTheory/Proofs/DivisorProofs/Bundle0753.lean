module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0717
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0725
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PieriRecursionUnique
section
open scoped Classical

namespace GlobalTheory

theorem pieri_recursion_zero (n : ℕ) (c : ℕ → ℂ) (D : (Fin n → ℕ) → ℂ)
    (hD : ∀ l, ¬ Antitone l → D l = 0)
    (hr : ∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), D (l + (fun i => if i ∈ J then 1 else 0)) = c j * D l)
    (h0 : D 0 = 0) : ∀ μ, D μ = 0 := by
  have main : ∀ s k (μ : Fin n → ℕ), ∑ i, μ i = s →
      n - (Finset.univ.filter (fun i => μ i ≠ 0)).card = k → D μ = 0 := by
    intro s
    refine Nat.strong_induction_on s ?_
    intro s ihs k
    refine Nat.strong_induction_on k ?_
    intro k ihk μ hs hk
    by_cases hμ : Antitone μ
    swap
    · exact hD μ hμ
    by_cases hz : μ = 0
    · subst hz; exact h0
    set J0 : Finset (Fin n) := Finset.univ.filter (fun i => μ i ≠ 0) with hJ0
    set l : Fin n → ℕ := fun i => μ i - 1 with hl
    have hla : Antitone l := fun a b hab => Nat.sub_le_sub_right (hμ hab) 1
    have hj : J0.card ≤ n := by simpa using Finset.card_le_univ J0
    have hlμ : l + (fun i => if i ∈ J0 then 1 else 0) = μ := by
      funext i
      simp only [Pi.add_apply, hl, hJ0, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h <;> omega
    have hsum : ∀ J : Finset (Fin n),
        ∑ i, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) i = ∑ i, l i + J.card := by
      intro J
      simp [Finset.sum_add_distrib, Finset.sum_boole]
    have hDl : D l = 0 := by
      have hlt : ∑ i, l i < s := by
        rw [← hs]
        obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
          by_contra h
          push_neg at h
          exact hz (funext h)
        exact Finset.sum_lt_sum (fun i _ => Nat.sub_le _ _)
          ⟨i, Finset.mem_univ _, by simp only [hl]; omega⟩
      exact ihs _ hlt _ l rfl rfl
    have hsingle : ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = J0.card),
        D (l + (fun i => if i ∈ J then 1 else 0)) = D (l + (fun i => if i ∈ J0 then 1 else 0)) := by
      refine Finset.sum_eq_single_of_mem J0 (by simp) ?_
      intro J hJ hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ
      set ν : Fin n → ℕ := l + (fun i => if i ∈ J then 1 else 0) with hν
      by_cases hνa : Antitone ν
      swap
      · exact hD ν hνa
      have hnsub : ¬ J ⊆ J0 := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega))
      obtain ⟨i, hiJ, hiJ0⟩ := Finset.not_subset.mp hnsub
      have hμi : μ i = 0 := by simpa [hJ0] using hiJ0
      have hνi : 1 ≤ ν i := by simp [hν, hiJ]
      have hsub : insert i J0 ⊆ Finset.univ.filter (fun k => ν k ≠ 0) := by
        intro k hk
        rw [Finset.mem_insert] at hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hk with rfl | hk
        · omega
        · have hk' : μ k ≠ 0 := by simpa [hJ0] using hk
          have hki : k ≤ i := by
            by_contra h
            push_neg at h
            have := hμ h.le
            omega
          have := hνa hki
          omega
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hiJ0] at hcard
      have hcn : (Finset.univ.filter (fun k => ν k ≠ 0)).card ≤ n := by
        simpa using Finset.card_le_univ (Finset.univ.filter (fun k => ν k ≠ 0))
      refine ihk (n - (Finset.univ.filter (fun k => ν k ≠ 0)).card) ?_ ν ?_ rfl
      · omega
      · have h1 := hsum J
        have h2 := hsum J0
        rw [hlμ] at h2
        rw [hν, h1, hJ, ← h2, hs]
    have hrec := hr l hla J0.card hj
    rw [hsingle, hDl, mul_zero, hlμ] at hrec
    exact hrec
  intro μ
  exact main _ _ μ rfl rfl

theorem pieri_recursion_unique : ∀ (n : ℕ) (c : ℕ → ℂ) (V U : (Fin n → ℕ) → ℂ),
    (∀ l, ¬ Antitone l → V l = 0) → (∀ l, ¬ Antitone l → U l = 0) →
    (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), V (l + (fun i => if i ∈ J then 1 else 0)) = c j * V l) →
    (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), U (l + (fun i => if i ∈ J then 1 else 0)) = c j * U l) →
    V 0 = U 0 → V = U := by
  intro n c V U hV hU hrV hrU h0
  have h := pieri_recursion_zero n c (fun l => V l - U l)
    (fun l hl => by simp [hV l hl, hU l hl])
    (fun l hl j hj => by
      simp only [Finset.sum_sub_distrib, hrV l hl j hj, hrU l hl j hj, mul_sub])
    (by simp [h0])
  funext μ
  exact sub_eq_zero.mp (h μ)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationClosedUnderBoundedCombination
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.PresSum

theorem cj_mul_of_mem (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {a b : ℂ} (ha : a ∈ M) (hb : b ∈ M) :
    StandardLatticesGL3.cj M ρ (a * b) = StandardLatticesGL3.cj M ρ a * StandardLatticesGL3.cj M ρ b := by
  unfold StandardLatticesGL3.cj TaylorLogMetric.liftM
  rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left (mul_mem ha hb), ← map_mul]
  rfl

variable {D : D7} {T : TaylorLogMetric.Tor D} {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
  {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {F₀ : TaylorLogMetric.VC D a b → ℂ}

theorem pres_zero : Pres D T L L' F₀ (fun _ => 0) 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ => by simp, by
    funext z; simp [StandardLatticesGL3.comb]⟩

theorem pres_add {F G : TaylorLogMetric.VC D a b → ℂ} {n m : ℝ} (hF : Pres D T L L' F₀ F n) (hG : Pres D T L L' F₀ G m) :
    Pres D T L L' F₀ (fun z => F z + G z) (n + m) := by
  obtain ⟨k, r, y, h1, h2, h3, rfl⟩ := hF
  obtain ⟨k', r', y', h1', h2', h3', rfl⟩ := hG
  refine ⟨k + k', Fin.append r r', Fin.append y y', ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact h1 j
    · rw [Fin.append_right]; exact h1' j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact h2 j
    · rw [Fin.append_right]; exact h2' j
  · intro ρ
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact add_le_add (h3 ρ) (h3' ρ)
  · funext z
    simp only [StandardLatticesGL3.comb, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem pres_smul {F : TaylorLogMetric.VC D a b → ℂ} {n β : ℝ} {c : ℂ} (hβ : 0 ≤ β) (hF : Pres D T L L' F₀ F n)
    (hc : c ∈ TaylorLogMetric.Qbar) (hb : ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ c‖ ≤ β) :
    Pres D T L L' F₀ (fun z => c * F z) (β * n) := by
  obtain ⟨k, r, y, h1, h2, h3, rfl⟩ := hF
  refine ⟨k, fun i => c * r i, y, fun i => mul_mem hc (h1 i), h2, fun ρ => ?_, ?_⟩
  · simp only [fun i => cj_mul_of_mem TaylorLogMetric.Qbar ρ hc (h1 i), norm_mul]
    rw [← Finset.mul_sum]
    exact mul_le_mul (hb ρ) (h3 ρ) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hβ
  · funext z
    simp only [StandardLatticesGL3.comb, Finset.mul_sum, mul_assoc]

theorem pres_sum : ∀ (D : D7) (T : TaylorLogMetric.Tor D) (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (F₀ : TaylorLogMetric.VC D a b → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → TaylorLogMetric.VC D a b → ℂ) (n β : ℝ), 0 ≤ β → (∀ x ∈ R, Pres D T L L' F₀ (F x) n) → (∀ x ∈ R, c x ∈ TaylorLogMetric.Qbar ∧ ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (c x)‖ ≤ β) → Pres D T L L' F₀ (fun z => ∑ x ∈ R, c x * F x z) (R.card * β * n) := by
  intro D T a b L L' F₀ α R c F n β hβ hF hc
  classical
  induction R using Finset.induction_on with
  | empty => simpa using pres_zero
  | insert x s hx ih =>
    have h1 := pres_smul hβ (hF x (Finset.mem_insert_self _ _)) (hc x (Finset.mem_insert_self _ _)).1
      (hc x (Finset.mem_insert_self _ _)).2
    have h2 := ih (fun y hy => hF y (Finset.mem_insert_of_mem hy)) (fun y hy => hc y (Finset.mem_insert_of_mem hy))
    have h3 := pres_add h1 h2
    have e : ((insert x s).card : ℝ) * β * n = β * n + s.card * β * n := by
      rw [Finset.card_insert_of_notMem hx]; push_cast; ring
    rw [e]
    simpa only [Finset.sum_insert hx] using h3

end GlobalTheory.PresSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDerivWeierstrassPHalfPeriodsDiscriminant
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem prod_derivWeierstrassP_translates_eq_Δ : ∀ (L : PeriodPair) (a b t : ℂ),
    a ∉ L.lattice → b ∉ L.lattice → a + b ∉ L.lattice → 2 * a ∈ L.lattice →
    2 * b ∈ L.lattice → 2 * t ∉ L.lattice →
    L.derivWeierstrassP t * L.derivWeierstrassP (t + a) * L.derivWeierstrassP (t + b) *
      L.derivWeierstrassP (t + (a + b)) = (latticeCurve L).Δ := by
  intro L a b t ha hb hc h2a h2b h2t
  have h2c : 2 * (a + b) ∈ L.lattice := by
    rw [mul_add]; exact L.lattice.add_mem h2a h2b
  have hshift : ∀ u : ℂ, 2 * u ∈ L.lattice → t + u ∉ L.lattice := by
    intro u hu htu
    apply h2t
    have := L.lattice.sub_mem (L.lattice.add_mem htu htu) hu
    convert this using 1; ring
  have ht : t ∉ L.lattice := by simpa using hshift 0 (by simp)
  have hroot : ∀ u : ℂ, u ∉ L.lattice → 2 * u ∈ L.lattice →
      4 * L.weierstrassP u ^ 3 - L.g₂ * L.weierstrassP u - L.g₃ = 0 := by
    intro u hu h2u
    rw [← L.derivWeierstrassP_sq u hu,
      (derivWeierstrassP_eq_zero_iff L hu).2 (by rwa [← two_mul])]
    ring
  have hne : ∀ u v : ℂ, u ∉ L.lattice → v ∉ L.lattice → 2 * v ∈ L.lattice →
      u + v ∉ L.lattice → L.weierstrassP u ≠ L.weierstrassP v := by
    intro u v hu hv h2v huv h
    rcases (weierstrassP_eq_iff L hu hv).1 h with h' | h'
    · apply huv
      have := L.lattice.add_mem h' h2v
      convert this using 1; ring
    · exact huv h'
  have h12 := hne a b ha hb h2b hc
  have h13 := hne a (a + b) ha hc h2c (by
    intro h; apply hb
    have := L.lattice.sub_mem h h2a
    convert this using 1; ring)
  have h23 := hne b (a + b) hb hc h2c (by
    intro h; apply ha
    have := L.lattice.sub_mem h h2b
    convert this using 1; ring)
  obtain ⟨hfac, hdisc⟩ := GlobalTheory.T.cubic_factor_and_discriminant_of_three_distinct_roots L.g₂ L.g₃ _ _ _ (hroot a ha h2a) (hroot b hb h2b)
    (hroot _ hc h2c) h12 h13 h23
  have e1 := _root_.GlobalTheory.derivWeierstrassP_add_half_period L a t ha h2a ht (hshift a h2a)
  have e2 := _root_.GlobalTheory.derivWeierstrassP_add_half_period L b t hb h2b ht (hshift b h2b)
  have e3 := _root_.GlobalTheory.derivWeierstrassP_add_half_period L (a + b) t hc h2c ht (hshift _ h2c)
  have hsq := L.derivWeierstrassP_sq t ht
  rw [hfac] at hsq
  have hd : L.derivWeierstrassP t ≠ 0 := fun h =>
    h2t (by rw [two_mul]; exact (derivWeierstrassP_eq_zero_iff L ht).1 h)
  rw [latticeCurve_Δ]
  generalize L.derivWeierstrassP t = d at *
  generalize L.derivWeierstrassP (t + a) = d₁ at *
  generalize L.derivWeierstrassP (t + b) = d₂ at *
  generalize L.derivWeierstrassP (t + (a + b)) = d₃ at *
  generalize L.weierstrassP t = x at *
  generalize L.weierstrassP a = e₁ at *
  generalize L.weierstrassP b = e₂ at *
  generalize L.weierstrassP (a + b) = e₃ at *
  apply mul_left_cancel₀ (pow_ne_zero 3 hd)
  calc d ^ 3 * (d * d₁ * d₂ * d₃) = (d ^ 2) ^ 2 * (d₁ * d₂ * d₃) := by ring
    _ = 16 * ((d₁ * (x - e₁) ^ 2) * (d₂ * (x - e₂) ^ 2) * (d₃ * (x - e₃) ^ 2)) := by
        rw [hsq]; ring
    _ = -(16 * ((3 * e₁ ^ 2 - L.g₂ / 4) * (3 * e₂ ^ 2 - L.g₂ / 4) *
          (3 * e₃ ^ 2 - L.g₂ / 4))) * d ^ 3 := by
        rw [e1, e2, e3]; ring
    _ = d ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by rw [hdisc]; ring

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFieldExistsSqrtNegDiscr
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_sq_eq_neg_of_discr_eq_neg : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := by
  classical
  intro K _ _ d h2 hd
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  haveI : IsGalois ℚ K := inferInstance
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨σ, hσ, huniq⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[ℚ] K)).1 hcard
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, σ} := by
    ext y
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hy : y = 1
    · exact Or.inl hy
    · exact Or.inr (huniq y hy)
  have htr : ∀ x : K, algebraMap ℚ K (Algebra.trace ℚ K x) = x + σ x := by
    intro x
    rw [_root_.trace_eq_sum_automorphisms, huniv, Finset.sum_pair (Ne.symm hσ)]
    rfl
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 :=
    Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis (integralBasis K), h2])
  let b : Fin 2 → K := fun i => integralBasis K (e.symm i)
  have hb : ⇑(integralBasis K) ∘ ⇑e.symm = b := rfl
  have key : algebraMap ℚ K (discr K : ℚ) = (b 0 * σ (b 1) - b 1 * σ (b 0)) ^ 2 := by
    rw [coe_discr, ← Algebra.discr_reindex ℚ (integralBasis K) e, hb, Algebra.discr_def,
      Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, map_sub, map_mul, htr]
    ring
  refine ⟨b 0 * σ (b 1) - b 1 * σ (b 0), ?_⟩
  rw [← key, hd]
  push_cast
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionSplitOfIsotropicNorm
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA.Split

variable {F : Type} [Field F]

end GlobalTheory.QSA.Split

namespace GlobalTheory

theorem quaternion_split_of_isotropic : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 →
    (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) →
    ∃ φ : ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F, ∀ x, (φ x).det = nrm x := by
  first
  | exact @_root_.GlobalTheory.MatrixHomBijective.split_of_isotropic
  | exact _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic
  | (apply _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixHomBijective.split_of_isotropic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.RationalPoints

theorem Hf_nsmul (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (m n : ℕ) (y y' : TaylorLogMetric.VC D a b) :
    TaylorLogMetric.Hf D T (m • y) (n • y') = ((m * n : ℝ) : ℂ) * TaylorLogMetric.Hf D T y y' := by
  rw [GlobalTheory.ThetaLine.Hf_eq, GlobalTheory.ThetaLine.Hf_eq, ← Nat.cast_smul_eq_nsmul ℂ m,
    ← Nat.cast_smul_eq_nsmul ℂ n, GlobalTheory.ThetaLine.sq_smul_left, GlobalTheory.ThetaLine.sq_smul_right]
  simp only [map_natCast]
  push_cast
  ring

theorem rational_points : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ), StandardLatticesGL3.Crv D cc dl → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → (∀ x : Matrix (Fin b) (Fin a) D.host.E, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' (dl • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc dl) x)) ∧ ∀ y y', StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' y → StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' y' → (∃ q : ℚ, (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc dl) y y').im = q) ∧ ∃ q : ℚ, (Real.sqrt D.host.d / 2 : ℝ) * TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc dl) y y = ((q : ℝ) : ℂ) := by
  intro D cc dl hc a b L L' hL hL'
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hK : StandardLatticesGL3.KLat D (TaylorLogMetric.tor0 D cc dl) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc dl) L L') :=
    Or.inr ⟨_, _, hL, hL', rfl⟩
  obtain ⟨-, -, h1, -, -, -, h5⟩ := GlobalTheory.ThetaLine.theta_line D hG cc dl hc a b _ hK
  refine ⟨fun x => GlobalTheory.ThetaInter.klat_mul_mem hG.1 hc.1.1 hK x, ?_⟩
  rintro y y' ⟨m, hm, hy⟩ ⟨n, hn, hy'⟩
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  constructor
  · obtain ⟨k, hk⟩ := h1 _ hy _ hy'
    rw [Hf_nsmul, Complex.im_ofReal_mul] at hk
    refine ⟨k / (m * n), ?_⟩
    push_cast
    rw [← hk]
    field_simp
  · obtain ⟨k, hk⟩ := h5 _ hy
    rw [TaylorLogMetric.qH, Hf_nsmul, Complex.re_ofReal_mul] at hk
    refine ⟨k / (m * m), Complex.ext ?_ ?_⟩
    · rw [Complex.re_ofReal_mul, Complex.ofReal_re]
      push_cast
      rw [← hk]
      field_simp
    · rw [Complex.im_ofReal_mul, Complex.ofReal_im, GlobalTheory.ThetaLine.im_Hf, GlobalTheory.ThetaLine.sq_self_im]
      simp

end GlobalTheory.RationalPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDetIdealSelfDualNormOne
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.SelfDualDetNorm

theorem star_eq_conj (D : D7) (x : D.host.E) :
    (letI := D.host.cmStar; star x) = D.host.conj x := by
  letI := D.host.cmStar
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem isSdLat_of_isSDLat {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsSDLat E n L) : Formalism.L2.Col.IsSdLat (E := E) L := by
  obtain ⟨hfg, hsp, hd⟩ := hL
  refine ⟨Submodule.IsLattice.of_fg E hfg, ?_⟩
  ext y
  rw [hd y]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  rfl

theorem detId_normOne : ∀ (D : D7) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)),
    StandardLatticesGL3.SD D L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  intro D N L hL
  letI := D.host.cmStar
  obtain ⟨J, hJ, hIJ⟩ := GlobalTheory.CharValCompare.normOne_detI (isSdLat_of_isSDLat L hL)
  refine ⟨J, fun x => by rw [hJ, star_eq_conj]; exact Iff.rfl, ?_⟩
  exact hIJ

end GlobalTheory.SelfDualDetNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftKillsProductOfCuspForms
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_lift_kills_product_of_cusp_forms : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card F) p.1 p.2) → ∀ n, n = deg L → Kills (shLift s (J (pullθ ι θ) L n)) (J θ (liftAll (Nat.card F) (Module.finrank F F') L) n) := by
  first | (exact @GlobalTheory.Shin.DescentAll.kills_liftAll) | (exact GlobalTheory.Shin.DescentAll.kills_liftAll) | (intros; apply GlobalTheory.Shin.DescentAll.kills_liftAll  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedIdeleEqLocalIdele
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.Div.SuppIdele

theorem snd_apply_mul {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : AdeleRing (𝓞 K) K) : (a * b).2 v = a.2 v * b.2 v := rfl

theorem supported_eq_localIdele : ∀ {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {a : Ideles K},
    IsSupportedAt K a v → ∃ x : (v.adicCompletion K)ˣ, (x : v.adicCompletion K) = (a : AdeleRing (𝓞 K) K).2 v ∧
      localIdele K v x = a := by
  intro K _ _ v a ha
  classical
  let x : (v.adicCompletion K)ˣ :=
    { val := (a : AdeleRing (𝓞 K) K).2 v
      inv := ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v
      val_inv := by
        rw [← snd_apply_mul, Units.mul_inv]; rfl
      inv_val := by
        rw [← snd_apply_mul, Units.inv_mul]; rfl }
  refine ⟨x, rfl, ?_⟩
  apply Units.ext
  apply Prod.ext
  · funext w
    exact (ha.1 w).symm
  · apply RestrictedProduct.ext
    intro w
    by_cases hw : w = v
    · subst hw
      exact (localIdele_snd_self K w x).trans rfl
    · exact ((localIdele_isSupportedAt K v x).2 w hw).trans (ha.2 w hw).symm

end GlobalTheory.Div.SuppIdele
end

