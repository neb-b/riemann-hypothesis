module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0047
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0104
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0072
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareBaseIntersection
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.SqFirst

theorem isSmoothHerm_of_pull {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
    [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    {A : HermLine ι} {A' : HermLine ι'} (hb : IsBlockMap κ v) (hA : IsSmoothHerm A)
    (hp : IsPullHerm κ v A A') : IsSmoothHerm A' := by
  have hh : A'.h = A.h ∘ (fun (z' : (Σ k', ι' k') → ℂ) (p : Σ k, ι k) => z' (v p)) := funext hp.2
  unfold IsSmoothHerm
  rw [hh]
  refine ContDiffOn.comp hA ?_ ?_
  · exact (contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (v p)).contDiffOn
  · intro z hz k
    obtain ⟨i', hi'⟩ := hz (κ k)
    obtain ⟨⟨k₁, i⟩, hp'⟩ := hb.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have e : κ k₁ = κ k := by
      have := hb.2.2.1 ⟨k₁, i⟩
      rw [hp'] at this
      exact this.symm
    obtain rfl := hb.1 e
    exact ⟨i, by simpa [hp'] using hi'⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem pull_one_of_base {P : Ideal (MRing ι)} {d : ℕ} {k₀ : K} {xi2 : K → ℤ} (Q : AlgSq P d k₀ xi2)
    {A : HermLine ι} {A₀ : HermLine Q.ιW} (hb : FromBase k₀ A) (h : IsPullHerm (Q.κ 0) (Q.v 0) A A₀) :
    IsPullHerm (Q.κ 1) (Q.v 1) A A₀ := by
  have hκ : ∀ k, k ≠ k₀ → Q.κ 0 k = Q.κ 1 k := fun k hk => by
    obtain ⟨i, -⟩ := Q.arithY.2.1.2.2 k
    have := congrArg Sigma.fst (Q.same ⟨k, i⟩ hk)
    rwa [(Q.block 0).2.2.1, (Q.block 1).2.2.1] at this
  refine ⟨?_, fun z' => ?_⟩
  · rw [h.1]
    funext k'
    rcases Q.all k' with ⟨k, rfl⟩ | rfl
    · by_cases hk : k = k₀
      · subst hk
        have hn : ¬ ∃ k', Q.κ 1 k' = Q.κ 0 k := by
          rintro ⟨k', hk'⟩
          by_cases h' : k' = k
          · subst h'
            exact Q.new ⟨k', hk'.symm⟩
          · exact h' ((Q.block 0).1 ((hκ k' h').trans hk'))
        rw [pullDeg, pullDeg, (Q.block 0).1.extend_apply, hb.1, Function.extend_apply' _ _ _ hn]
        rfl
      · rw [pullDeg, pullDeg, (Q.block 0).1.extend_apply, hκ k hk, (Q.block 1).1.extend_apply]
    · have hn : ¬ ∃ k', Q.κ 0 k' = Q.κ 1 k₀ := Q.new
      rw [pullDeg, pullDeg, (Q.block 1).1.extend_apply, hb.1, Function.extend_apply' _ _ _ hn]
      rfl
  · rw [h.2]
    exact hb.2 _ _ fun p hp => by rw [Q.same p hp]

theorem swap_nat {V : Type*} {n : ℕ} (I : (Fin n → V) → ℝ) (S : V → Prop)
    (hI : ∀ L : Fin n → V, (∀ j, S (L j)) → ∀ σ : Equiv.Perm (Fin n), I (L ∘ σ) = I L)
    (f : ℕ → V) (hf : ∀ j, S (f j)) (a b : ℕ) (ha : a < n) (hb : b < n) :
    I (fun j => f j) = I (fun j => f (if (j : ℕ) = a then b else if (j : ℕ) = b then a else j)) := by
  rw [← hI (fun j => f j) (fun j => hf j) (Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩)]
  congr 1
  funext j
  simp [Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> rfl

theorem interp_mem {V : Type*} {S : V → Prop} {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a)
    (k i j : ℕ) : S (interp k i x₁ x₂ a j) := by
  unfold interp
  split_ifs <;> assumption

theorem consWord_mem {V : Type*} {S : V → Prop} {x x₁ x₂ a : V} (h₀ : S x) (h₁ : S x₁) (h₂ : S x₂)
    (h₃ : S a) (k i j : ℕ) : S (consWord k i x x₁ x₂ a j) := by
  unfold consWord
  split_ifs <;> assumption

theorem word_mem {V : Type*} {S : V → Prop} {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a)
    (D k i : ℕ) (j : Fin D) : S (word D k i x₁ x₂ a j) := by
  unfold word
  split_ifs <;> assumption

theorem consWord_left {V : Type*} {D : ℕ} (I : (Fin (D + 2) → V) → ℝ) (S : V → Prop)
    (hI : ∀ L : Fin (D + 2) → V, (∀ j, S (L j)) → ∀ σ : Equiv.Perm (Fin (D + 2)), I (L ∘ σ) = I L)
    (k i : ℕ) (hi : i < k) (hD : 2 * k ≤ D + 1) {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a) :
    I (fun j => consWord k i x₁ x₁ x₂ a j) = I (fun j => interp k (i + 1) x₁ x₂ a j) := by
  rw [swap_nat I S hI (consWord k i x₁ x₁ x₂ a) (consWord_mem h₁ h₁ h₂ h₃ k i) 0 2 (by omega) (by omega)]
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega | contradiction

theorem consWord_right {V : Type*} {D : ℕ} (I : (Fin (D + 2) → V) → ℝ) (S : V → Prop)
    (hI : ∀ L : Fin (D + 2) → V, (∀ j, S (L j)) → ∀ σ : Equiv.Perm (Fin (D + 2)), I (L ∘ σ) = I L)
    (k i : ℕ) (hi : i < k) (hD : 2 * k ≤ D + 1) {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a) :
    I (fun j => consWord k i x₂ x₁ x₂ a j) = I (fun j => interp k i x₁ x₂ a j) := by
  rw [swap_nat I S hI (consWord k i x₂ x₁ x₂ a) (consWord_mem h₂ h₁ h₂ h₃ k i) 1 (2 * i + 1)
      (by omega) (by omega),
    swap_nat I S hI (interp k i x₁ x₂ a) (interp_mem h₁ h₂ h₃ k i) 2 (2 * i + 2) (by omega) (by omega)]
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega | contradiction

theorem firstHalf : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2) (Xi : HermLine ι) (X₀ X₁ : HermLine Q.ιW), Xi.a = xi2 → IsSmoothHerm Xi → IsPullHerm (Q.κ 0) (Q.v 0) Xi X₀ → IsPullHerm (Q.κ 1) (Q.v 1) Xi X₁ → ∀ (A : HermLine ι) (A₀ : HermLine Q.ιW), IsSmoothHerm A → FromBase k₀ A → IsPullHerm (Q.κ 0) (Q.v 0) A A₀ → II K ι P (d + 2) (fun _ => A) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → II K ι P (d + 2) (mix (2 * k) Xi A) = -∑ i ∈ Finset.range k, (ptsIntegral Q.PW (pot (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) := by
  intro hIn II hII K _ ι _ P d k₀ xi2 Q Xi X₀ X₁ hxi hsm h0 h1 A A₀ hAs hAb hA0
  have hR := _root_.PositivityTheory.Xgp.t_sq_R hIn II hII K ι P d k₀ xi2 Q Xi X₀ X₁ hxi hsm h0 h1
  obtain ⟨hP1, hP0⟩ := _root_.GlobalTheory.CompanionTheory.Relay.algebraic_square_intersection_pullback hIn II hII K ι P d k₀ xi2 Q
  have hX0 : IsSmoothHerm X₀ := isSmoothHerm_of_pull (Q.block 0) hsm h0
  have hX1 : IsSmoothHerm X₁ := isSmoothHerm_of_pull (Q.block 1) hsm h1
  have hA0s : IsSmoothHerm A₀ := isSmoothHerm_of_pull (Q.block 0) hAs hA0
  have hA1 : IsPullHerm (Q.κ 1) (Q.v 1) A A₀ := pull_one_of_base Q hAb hA0
  have hdeg : ((X₁.a (Q.κ 1 k₀) : ℤ) : ℝ) = -2 := by
    rw [h1.1, pullDeg, (Q.block 1).1.extend_apply, hxi, Q.xi_two_base_eq_neg_two]
    norm_num
  have hsym : ∀ L : Fin (d + 3) → HermLine Q.ιW, (∀ j, IsSmoothHerm (L j)) →
      ∀ σ : Equiv.Perm (Fin (d + 3)), II Q.KW Q.ιW Q.PW (d + 3) (L ∘ σ) = II Q.KW Q.ιW Q.PW (d + 3) L :=
    fun L hL σ => (hII.1 Q.KW Q.ιW).1 Q.PW (d + 3) L σ Q.arithW hL
  have hrot : ∀ (L' : Fin (d + 2) → HermLine Q.ιW) (N : HermLine Q.ιW), (∀ j, IsSmoothHerm (L' j)) →
      IsSmoothHerm N → II Q.KW Q.ιW Q.PW (d + 3) (Fin.snoc L' N) =
        II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons N L') := by
    intro L' N hL' hN
    rw [Fin.snoc_eq_cons_rotate]
    refine hsym (Fin.cons N L') (fun j => ?_) (finRotate _)
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hN
    · simpa using hL' j
  refine ⟨?_, ?_⟩
  · have e1 := hP1 (fun _ => A) (fun _ => A₀) X₁ (fun _ => hAs) (fun _ => hA0) hX1
    have e2 := hP0 (Fin.snoc (α := fun _ => HermLine ι) (fun _ => A) Xi)
      (Fin.snoc (α := fun _ => HermLine Q.ιW) (fun _ => A₀) X₁)
      (fun j => by
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa using hsm
        · simpa using hAs)
      (fun j => by
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa using h1
        · simpa using hA1)
    rw [e2, hdeg] at e1
    linarith
  · intro k hk hkD
    set g : ℕ → ℝ := fun i =>
      II Q.KW Q.ιW Q.PW (d + 3) (fun j : Fin (d + 3) => interp k i X₀ X₁ A₀ j) with hg
    have hstep : ∀ i ∈ Finset.range k,
        2 * (ptsIntegral Q.PW (pot (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) = g (i + 1) - g i := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have e0 : (Fin.cons X₀ (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀)) : Fin (d + 3) → HermLine Q.ιW) =
          fun j : Fin (d + 3) => consWord k i X₀ X₀ X₁ A₀ j := cons_cons_word (d + 1) k i hk X₀ X₀ X₁ A₀
      have e1 : (Fin.cons X₁ (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀)) : Fin (d + 3) → HermLine Q.ιW) =
          fun j : Fin (d + 3) => consWord k i X₁ X₀ X₁ A₀ j := cons_cons_word (d + 1) k i hk X₁ X₀ X₁ A₀
      rw [← hR (word (d + 1) k i X₀ X₁ A₀) (word_mem hX0 hX1 hA0s _ _ _), e0, e1]
      have l := consWord_left (D := d + 1) (II Q.KW Q.ιW Q.PW (d + 3)) IsSmoothHerm hsym k i hi' (by omega) hX0 hX1 hA0s
      have r := consWord_right (D := d + 1) (II Q.KW Q.ιW Q.PW (d + 3)) IsSmoothHerm hsym k i hi' (by omega) hX0 hX1 hA0s
      rw [l, r]
    have h00 : g 0 = 0 := by
      rw [← hP0 (mix (1 + 2 * k) Xi A) (mix (1 + 2 * k) X₁ A₀)
        (fun j => by unfold mix; split_ifs <;> assumption)
        (fun j => by unfold mix; split_ifs <;> assumption)]
      simp only [hg]
      congr 1
      funext j
      simp only [interp, mix]
      split_ifs <;> first | rfl | omega | contradiction
    have hgk : g k = -2 * II K ι P (d + 2) (mix (2 * k) Xi A) := by
      have e := hP1 (mix (2 * k) Xi A) (mix (2 * k) X₀ A₀) X₁
        (fun j => by unfold mix; split_ifs <;> assumption)
        (fun j => by unfold mix; split_ifs <;> assumption) hX1
      rw [hrot _ X₁ (fun j => by unfold mix; split_ifs <;> assumption) hX1, hdeg] at e
      rw [← e]
      simp only [hg]
      congr 1
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [interp]
      simp only [Fin.cons_succ, interp, mix, Fin.val_succ]
      split_ifs <;> first | rfl | omega | contradiction
    have hsum := Finset.sum_range_sub g k
    rw [← Finset.sum_congr rfl hstep, ← Finset.mul_sum, h00, hgk] at hsum
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.SqFirst
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConePtsSubsetMcPtsOfMinimal
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

theorem conePts_subset_mcPts_of_minimal {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)}
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) : conePts Q ⊆ mcPts P := fun _ hz =>
  ⟨hz.1, fun f hf => hz.2 _ (hQ.1.2 (Ideal.mem_map_of_mem _ hf))⟩

theorem exists_minimal_of_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    ∃ Q ∈ (cxIdeal P).minimalPrimes, z ∈ conePts Q := by
  have hz' : z ∈ conePts (cxIdeal P) := by rw [← mcPts_eq_conePts]; exact hz
  have hle : cxIdeal P ≤ RingHom.ker (eval z : MRingOver ℂ ι →+* ℂ) :=
    fun f hf => RingHom.mem_ker.2 (hz'.2 f hf)
  have : (RingHom.ker (eval z : MRingOver ℂ ι →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨Q, hQ, hz'.1, fun f hf => RingHom.mem_ker.1 (hQle hf)⟩

theorem mem_conePts_of_segre_eq {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)} (hP : IsArithVar P (e + 1))
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (hs : segre z = segre z') : z' ∈ conePts Q := by
  classical
  choose i0 hi0 using hz.1
  obtain ⟨-, h4⟩ := eq_bsmul_of_segre_eq i0 hi0 hs
  have hJ := GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResBridge.isMultiHomogIdeal_of_mem_minimalPrimes hP hQ
  have h5 := ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hJ (fun k => z' ⟨k, i0 k⟩ / z ⟨k, i0 k⟩) z hz.2
  refine ⟨hz', fun f hf => ?_⟩
  rw [h4]
  exact h5 f hf

theorem isSheet_of_isSetSheet {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)}
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSetSheet (conePts Q) Ψ y w γ) : IsSheet P Ψ y w γ :=
  ⟨h.1, h.2.mono fun _ h' => ⟨h'.1, conePts_subset_mcPts_of_minimal hQ h'.2.1, h'.2.2⟩⟩

theorem isSetSheet_of_isSheet {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)} (hP : IsArithVar P (e + 1))
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (hone : ∀ Q' ∈ (cxIdeal P).minimalPrimes, ∀ z, z ∈ conePts Q → z ∈ conePts Q' →
      Ψ (segre z) = Fin.cons 1 y → Q' = Q)
    (hw : w ∈ setFibre (conePts Q) Ψ y) (h : IsSheet P Ψ y w γ) :
    IsSetSheet (conePts Q) Ψ y w γ := by
  obtain ⟨z, hz, hzw, -⟩ := hw
  obtain ⟨hd, hm, hΨγ⟩ := h.2.self_of_nhds
  have hγQ : γ y ∈ conePts Q := mem_conePts_of_segre_eq hP hQ hz hm.1 (hzw.trans h.1.symm)
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hev : ∀ᶠ y' in 𝓝 y, ∀ Q' ∈ (cxIdeal P).minimalPrimes, Q' ≠ Q → γ y' ∉ conePts Q' := by
    refine (Filter.eventually_all_finite hfin).2 fun Q' hQ' => ?_
    by_cases hne : Q' = Q
    · exact Eventually.of_forall fun _ h' => absurd hne h'
    have hnot : γ y ∉ conePts Q' := fun hc => hne (hone Q' hQ' _ hγQ hc hΨγ)
    obtain ⟨f, hf, hf0⟩ : ∃ f ∈ Q', eval (γ y) f ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hnot ⟨hm.1, hcon⟩
    have hc : ContinuousAt (fun y' => eval (γ y') f) y :=
      (MvPolynomial.continuous_eval f).continuousAt.comp hd.continuousAt
    filter_upwards [hc.eventually_ne hf0] with y' hy' _ hmem
    exact hy' (hmem.2 f hf)
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2, hev] with y' h1 h2
  obtain ⟨Q', hQ', hz'⟩ := exists_minimal_of_mem_mcPts h1.2.1
  by_cases hne : Q' = Q
  · subst hne
    exact ⟨h1.1, hz', h1.2.2⟩
  · exact absurd hz' (h2 Q' hQ' hne)

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceRateStatementHolds
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.Rate

theorem mInt_congr_φ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ Ψ : Fin e → LocPot X) (h : ∀ i, (Φ i).φ = (Ψ i).φ) (g : X → ℝ) :
    mInt A Φ g = mInt A Ψ g := by
  have hD : locDens A Φ = locDens A Ψ := by
    funext j y
    simp only [locDens, h]
  unfold mInt integralWith
  rw [hD]

theorem maMeasure_univ_eq {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ : LocPot X)
    (th : Fin e → LocPot X) (u : Fin e → X → ℝ) (hΘ : IsPotential A Θ)
    (hth : ∀ i, IsPotential A (th i)) (hu : ∀ i, A.Smooth (u i))
    (hP : ∀ i, IsPotential A (th i + LocPot.ofFun (u i) + Θ))
    (hPsh : ∀ i, IsPsh A (th i + LocPot.ofFun (u i) + Θ)) :
    maMeasure A (fun i => th i + LocPot.ofFun (u i) + Θ) Set.univ =
      ENNReal.ofReal (mInt A (fun i => th i + Θ) (fun _ => 1)) := by
  obtain ⟨hfin, hg⟩ := maMeasure_thm A (fun i => th i + LocPot.ofFun (u i) + Θ) hP hPsh
  have hI : Integrable (fun _ : X => (1 : ℝ)) (maMeasure A (fun i => th i + LocPot.ofFun (u i) + Θ)) :=
    integrable_const 1
  have hM := (hg _ measurable_const).1.2 hI
  have h2 := (hg _ measurable_const).2 hM
  have h3 : mInt A (fun i => th i + LocPot.ofFun (u i) + Θ) (fun _ => 1) =
      mInt A (fun i => (th i + Θ) + LocPot.ofFun (u i)) (fun _ => 1) := by
    refine mInt_congr_φ A _ _ (fun i => ?_) _
    funext x y
    show (th i).φ x y + u i y + Θ.φ x y = (th i).φ x y + Θ.φ x y + u i y
    ring
  rw [massIndep A (fun i => th i + Θ) u (fun i => isPotentialAdd A _ _ (hth i) hΘ) hu] at h3
  rw [← h3, h2, integral_const, smul_eq_mul, mul_one, ofReal_measureReal (measure_ne_top _ _)]

end GlobalTheory.CompanionTheory.Ar.Giv.Rate

namespace GlobalTheory.CompanionTheory.Ar.Giv


open GlobalTheory.CompanionTheory.Ar.Giv.Rate in
theorem convergenceRate_holds : ConvergenceRateStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT th₀ ph₀ phT₀ C₅ C t₀
    hW hR hW₀ hR₀
  obtain ⟨K, t₂, ht₂, -, hT⟩ := tail_uniform tailBound_holds A Θ L s m W hΘ hpos hL hS hSNC hnorm
    th ph phT C₅ C t₀ hW hR
  have ht₀ : 0 < t₀ := hR₀.1
  refine ⟨(3 + |C|) * |mInt A (fun i => th i + Θ) (fun _ => 1)| + (|C| + |C₅|) * |K|,
    min t₂ (min t₀ (Real.exp (-Real.exp 1))), lt_min ht₂ (lt_min ht₀ (Real.exp_pos _)), ?_⟩
  intro t t' ht' htt' ht1 c
  have htpos : 0 < t := ht'.trans_le htt'
  have ht_t₂ : t ≤ t₂ := ht1.trans (min_le_left _ _)
  have ht_t₀ : t ≤ t₀ := ht1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht_e : t ≤ Real.exp (-Real.exp 1) := ht1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlogt : Real.log (1 / t) = -Real.log t := by rw [one_div, Real.log_inv]
  have hℓe : Real.exp 1 ≤ Real.log (1 / t) := by
    have := Real.log_le_log htpos ht_e
    rw [Real.log_exp] at this
    linarith
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Real.log (1 / t) = ℓ := ⟨_, rfl⟩
  rw [hℓ] at hℓe hlogt
  rw [hℓ]
  have hℓpos : 0 < ℓ := by linarith
  have hlogℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hℓe
  have hℓu : ∀ u, 0 < u → u ≤ t → ℓ ≤ Real.log (1 / u) := fun u hu hut =>
    hℓ ▸ Real.log_le_log (by positivity) (one_div_le_one_div_of_le hu hut)

  have heps : ∀ u, 0 < u → u ≤ t → epsT C u ≤ |C| * (Real.log ℓ / ℓ) := by
    intro u hu hut
    have hlu := hℓu u hu hut
    have hmono := Real.log_div_self_antitoneOn (Set.mem_Ici.2 hℓe) (Set.mem_Ici.2 (hℓe.trans hlu)) hlu
    have hnn : 0 ≤ Real.log (Real.log (1 / u)) / Real.log (1 / u) :=
      div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
    unfold epsT
    rw [mul_div_assoc]
    calc C * (Real.log (Real.log (1 / u)) / Real.log (1 / u))
        ≤ |C| * (Real.log (Real.log (1 / u)) / Real.log (1 / u)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hnn
      _ ≤ |C| * (Real.log ℓ / ℓ) := mul_le_mul_of_nonneg_left hmono (abs_nonneg C)
  have hrpow : ∀ u, 0 < u → u ≤ t → u ^ ((1 : ℝ) / 3) ≤ 3 / ℓ := by
    intro u hu hut
    refine (Real.rpow_le_rpow hu.le hut (by norm_num)).trans ?_
    rw [Real.rpow_def_of_pos htpos]
    have h3 : Real.log t * (1 / 3) = -(ℓ / 3) := by rw [hlogt]; ring
    rw [h3, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    linarith [Real.add_one_le_exp (ℓ / 3)]
  obtain ⟨q, hq⟩ : ∃ q, q = Real.log ℓ ^ 2 / ℓ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : 1 / ℓ ≤ q := hq ▸ div_le_div_of_nonneg_right (by nlinarith) hℓpos.le
  have hq2 : Real.log ℓ / ℓ ≤ q := hq ▸ div_le_div_of_nonneg_right (by nlinarith) hℓpos.le
  have hsmall : ∀ u, 0 < u → u ≤ t → u ^ ((1 : ℝ) / 3) + epsT C u ≤ (3 + |C|) * q := by
    intro u hu hut
    have h1 := hrpow u hu hut
    have h2 := heps u hu hut
    have h3 : |C| * (Real.log ℓ / ℓ) ≤ |C| * q := mul_le_mul_of_nonneg_left hq2 (abs_nonneg C)
    have h4 : 3 / ℓ = 3 * (1 / ℓ) := by ring
    nlinarith

  obtain ⟨-, hCt, hat, -, -, hdt, -, -⟩ := hR₀.2.2 t htpos ht_t₀
  obtain ⟨-, hCt', hat', -, -, hdt', -, -⟩ := hR₀.2.2 t' ht' (htt'.trans ht_t₀)
  have hsw := hW₀.2.2.2
  have hin : ∀ y ∉ bdry s, rW L s y < ℓ → |phT₀ t y - phT₀ t' y| ≤ (3 + |C|) * q := by
    intro y hy hry
    have h1 := hdt y hy (by rw [hℓ]; exact hry.le)
    have h2 := hdt' y hy (hry.le.trans (hℓu t' ht' htt'))
    have h3 := hsmall t htpos le_rfl
    have h4 := hsmall t' ht' htt'
    have h5 := hat y hy
    have h6 := hat' y hy
    rw [abs_le]
    constructor <;> linarith
  have hout : ∀ y ∉ bdry s, ℓ ≤ rW L s y →
      |phT₀ t y - phT₀ t' y| ≤ (|C| + |C₅|) * Real.log (rW L s y) := by
    intro y hy hry
    have hr1 : 1 ≤ Real.log (rW L s y) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (hℓe.trans hry)
    have h1 := hCt y
    have h2 := hCt' y
    have h5 := hat y hy
    have h6 := hat' y hy
    have h7 := (hsw y hy).1
    have h8 : C ≤ |C| * Real.log (rW L s y) := (le_abs_self C).trans (by nlinarith [abs_nonneg C])
    have h9 : C₅ * Real.log (rW L s y) ≤ |C₅| * Real.log (rW L s y) :=
      mul_le_mul_of_nonneg_right (le_abs_self C₅) (by linarith)
    rw [abs_le]
    constructor <;> nlinarith

  have hτ : ∀ i, 0 < (fun i => if c i then t else t') i ∧ (fun i => if c i then t else t') i ≤ t₂ := by
    intro i
    by_cases h : c i
    · simp only [h, if_true]; exact ⟨htpos, ht_t₂⟩
    · simp only [h]; exact ⟨ht', htt'.trans ht_t₂⟩
  obtain ⟨hPP, hTR⟩ := hT _ hτ
  obtain ⟨-, hlogR⟩ := hTR ℓ hℓe
  beta_reduce at hPP hlogR
  have hsm : ∀ i, A.Smooth (phT i (if c i then t else t')) := by
    intro i
    by_cases h : c i
    · simp only [h, if_true]; exact ((hR i).2.2 t htpos ht_t₀).1
    · simp only [h]; exact ((hR i).2.2 t' ht' (htt'.trans ht_t₀)).1
  have hmass := maMeasure_univ_eq A Θ th (fun i => phT i (if c i then t else t')) hΘ
    (fun i => (hW i).1) hsm (fun i => (hPP i).1) (fun i => (hPP i).2)
  have hnull : maMeasure A (fun i => th i + LocPot.ofFun (phT i (if c i then t else t')) + Θ)
      (bdry s) = 0 := bdry_null A L s m W hL hS hSNC _ (fun i => (hPP i).1)
  have hae := measure_eq_zero_iff_ae_notMem.1 hnull
  set μ := maMeasure A (fun i => th i + LocPot.ofFun (phT i (if c i then t else t')) + Θ) with hμ
  set M := mInt A (fun i => th i + Θ) (fun _ => (1 : ℝ)) with hM
  set k := |C| + |C₅| with hkdef
  have hk : 0 ≤ k := by positivity
  have ha : 0 ≤ (3 + |C|) * q := mul_nonneg (by positivity) hq0
  have hpt : ∀ᵐ y ∂μ, ENNReal.ofReal |phT₀ t y - phT₀ t' y| ≤
      ENNReal.ofReal ((3 + |C|) * q) + ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
        (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y := by
    filter_upwards [hae] with y hy
    by_cases hry : ℓ ≤ rW L s y
    · rw [Set.indicator_of_mem (show y ∈ (bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y} from ⟨hy, hry⟩),
        ← ENNReal.ofReal_mul hk]
      exact (ENNReal.ofReal_le_ofReal (hout y hy hry)).trans le_add_self
    · rw [Set.indicator_of_notMem (by exact fun h => hry h.2), add_zero]
      exact ENNReal.ofReal_le_ofReal (hin y hy (not_le.1 hry))
  have hsec : ∫⁻ y, ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
        (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y ∂μ ≤
      ENNReal.ofReal k * ENNReal.ofReal (|K| * q) := by
    refine (lintegral_indicator_le _ _).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hKq : K * Real.log ℓ ^ 2 / ℓ ≤ |K| * q := by
      rw [hq, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    gcongr
    exact hlogR.trans (ENNReal.ofReal_le_ofReal hKq)
  calc ∫⁻ y, ENNReal.ofReal |phT₀ t y - phT₀ t' y| ∂μ
      ≤ ∫⁻ y, (ENNReal.ofReal ((3 + |C|) * q) + ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
          (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y) ∂μ :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal ((3 + |C|) * q) * μ Set.univ + ∫⁻ y, ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
          (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ ENNReal.ofReal ((3 + |C|) * q) * ENNReal.ofReal |M| +
          ENNReal.ofReal k * ENNReal.ofReal (|K| * q) := by
        rw [hmass]
        gcongr
        exact le_abs_self _
    _ = ENNReal.ofReal ((3 + |C|) * q * |M| + k * (|K| * q)) := by
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hk,
          ← ENNReal.ofReal_add (mul_nonneg ha (abs_nonneg _)) (mul_nonneg hk (mul_nonneg (abs_nonneg _) hq0))]
    _ ≤ ENNReal.ofReal (((3 + |C|) * |M| + k * |K|) * Real.log ℓ ^ 2 / ℓ) :=
        ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hq]; ring))

end GlobalTheory.CompanionTheory.Ar.Giv
end

