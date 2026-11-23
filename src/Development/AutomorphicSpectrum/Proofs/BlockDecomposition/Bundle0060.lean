module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtExpMulExpOfFiniteDimensional
section
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace GlobalTheory.CompanionTheory.MatrixLie

theorem hasDerivAt_exp_mul_exp_of_finiteDimensional {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] (X Y : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y)) (X + Y) 0 := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  have hX := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have hY := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  have hXY := hX.mul hY
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at hXY
  exact hXY

private theorem hasDerivAt_zero_linear_exp_smul_mul_exp_smul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] (X Y : A) (ℓ : A →ₗ[ℝ] ℂ) :
    HasDerivAt (fun t : ℝ => ℓ (NormedSpace.exp (t • X) * NormedSpace.exp (t • Y))) (ℓ (X + Y)) 0 :=
  (LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_mul_exp_of_finiteDimensional X Y)

theorem entry_hasDerivAt_exp_mul_exp {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ =>
      (NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • Y)) i j) ((X + Y) i j) 0 := by
  have hs : ∀ (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ), ((t : ℂ) • Z) = t • Z := by
    intro t Z
    ext a b
    simp [Complex.real_smul]
  simp only [hs]
  exact @hasDerivAt_zero_linear_exp_smul_mul_exp_smul (Matrix (Fin n) (Fin n) ℂ) Matrix.linftyOpNormedRing
    Matrix.linftyOpNormedAlgebra inferInstance X Y
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem hasDerivAt_exp_mul_exp {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • Y))
      (X + Y) 0 :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => entry_hasDerivAt_exp_mul_exp X Y i j

theorem exists_submodule_eq_lieAlg :
    ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G →
      ∃ S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
        (S : Set (Matrix (Fin n) (Fin n) ℂ)) = lieAlg G := by
  intro n G hG
  refine ⟨{ carrier := lieAlg G, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, rfl⟩
  · intro a b ha hb
    have ha' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • a) ∈ G := ha
    have hb' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • b) ∈ G := hb
    refine _root_.GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg n G hG
      (fun t : ℝ => NormedSpace.exp ((t : ℂ) • a) * NormedSpace.exp ((t : ℂ) • b)) (a + b) ?_ ?_
      (hasDerivAt_exp_mul_exp a b)
    · simp
    · exact Filter.Eventually.of_forall (fun t => hG.2.2.1 _ (ha' t) _ (hb' t))
  · show ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (0 : Matrix (Fin n) (Fin n) ℂ)) ∈ G
    intro t
    simpa using hG.2.1
  · intro c X hX
    have hX' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ G := hX
    show ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (c • X)) ∈ G
    intro t
    have he : ((t : ℂ) • (c • X)) = ((t * c : ℝ) : ℂ) • X := by
      ext a b
      simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
      ring
    rw [he]
    exact hX' (t * c)

end GlobalTheory.CompanionTheory.MatrixLie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSumInvariant
section
namespace GlobalTheory.CompanionTheory.Hecke

theorem heckeSum_fixed :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (K : Subgroup G) (f : G → ℂ), (Function.support fun q : G ⧸ K => f q.out).Finite →
      (∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → ∀ v : V, (∀ k ∈ K, ρ k v = v) →
      ∀ k ∈ K, ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := by
  intro G V _ _ _ ρ K f hfin hbi v hv k hk
  have hsupp : (Function.support fun q : G ⧸ K => f q.out • ρ q.out v).Finite := by
    refine hfin.subset ?_
    intro q hq h0
    apply hq
    have h0' : f q.out = 0 := h0
    simp [h0']
  have hstep : ∀ q : G ⧸ K, ρ k (f q.out • ρ q.out v)
      = f (MulAction.toPerm k q).out • ρ (MulAction.toPerm k q).out v := by
    intro q
    have hmk : ((MulAction.toPerm k q : G ⧸ K).out : G ⧸ K) = ((k * q.out : G) : G ⧸ K) := by
      rw [QuotientGroup.out_eq', MulAction.toPerm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hκ : (k * q.out)⁻¹ * (MulAction.toPerm k q : G ⧸ K).out ∈ K :=
      QuotientGroup.eq.mp hmk.symm
    obtain ⟨κ, hκK, hκ⟩ : ∃ κ ∈ K, (MulAction.toPerm k q : G ⧸ K).out = k * q.out * κ :=
      ⟨_, hκ, by group⟩
    rw [hκ, (hbi κ hκK _).2, (hbi k hk _).1, map_mul, map_mul, map_smul]
    simp [hv κ hκK]
  have h1 := (ρ k).toAddMonoidHom.map_finsum hsupp
  have h2 : ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v)
      = ∑ᶠ q : G ⧸ K, ρ k (f q.out • ρ q.out v) := h1
  rw [h2, finsum_congr hstep]
  exact finsum_comp_equiv (MulAction.toPerm k) (f := fun q : G ⧸ K => f q.out • ρ q.out v)

end GlobalTheory.CompanionTheory.Hecke
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdProperty
section
namespace GlobalTheory.CompanionTheory.TwistedCent

open PositivityTheory.Rg.Tf.Loc

theorem mem_twCent_twConj_iff {G : Type} [Group G] (θ : Monoid.End G) (g δ x : G) :
    x ∈ twCent θ (twConj θ g δ) ↔ g * x * g⁻¹ ∈ twCent θ δ := by
  rw [mem_twCent, mem_twCent]
  simp only [twConj, map_mul, map_inv]
  constructor
  · intro h
    calc (g * x * g⁻¹)⁻¹ * δ * (θ g * θ x * (θ g)⁻¹)
        = g * (x⁻¹ * (g⁻¹ * δ * θ g) * θ x) * (θ g)⁻¹ := by group
      _ = g * (g⁻¹ * δ * θ g) * (θ g)⁻¹ := by rw [h]
      _ = δ := by group
  · intro h
    calc x⁻¹ * (g⁻¹ * δ * θ g) * θ x
        = g⁻¹ * ((g * x * g⁻¹)⁻¹ * δ * (θ g * θ x * (θ g)⁻¹)) * θ g := by group
      _ = g⁻¹ * δ * θ g := by rw [h]

theorem h3 : PositivityTheory.Rg.Tf.Loc.H3 := fun _ _ θ g δ x => mem_twCent_twConj_iff θ g δ x

end GlobalTheory.CompanionTheory.TwistedCent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HenselPolynomialRefinement
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.AicStep


open Polynomial in
theorem aic_step : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → ∀ P : Polynomial T, P.Monic → 0 < P.natDegree → ∀ (M : ℕ) (a : B), P.eval (g a) ∈ Ideal.span {g π ^ (P.natDegree * M)} → ∃ a₁ : B, a₁ - a ∈ Ideal.span {π ^ M} ∧ P.eval (g a₁) ∈ Ideal.span {g π ^ (P.natDegree * (M + 1))} := by
  open Polynomial in
  intro B _ T _ π g hC hπ hA hV P hP hd M a ha
  obtain ⟨_, hsurj, hinj⟩ := hC
  haveI : Nontrivial T := by
    by_contra hT
    rw [not_nontrivial_iff_subsingleton] at hT
    have hP0 : P = 0 := Polynomial.ext fun n => Subsingleton.elim _ _
    simp [hP0] at hd
  haveI : Nontrivial B := g.domain_nontrivial
  choose c hc using fun i : ℕ => hsurj (P.natDegree * (M + 1)) (P.coeff i)
  have hsum : (∑ i ∈ Finset.range P.natDegree, C (c i) * X ^ i : Polynomial B) =
      ∑ i : Fin P.natDegree, C (c i) * X ^ (i : ℕ) :=
    (Fin.sum_univ_eq_sum_range (fun i => (C (c i) * X ^ i : Polynomial B)) _).symm
  let Q : Polynomial B := X ^ P.natDegree + ∑ i ∈ Finset.range P.natDegree, C (c i) * X ^ i
  have hQm : Q.Monic := by
    show (X ^ P.natDegree + ∑ i ∈ Finset.range P.natDegree, C (c i) * X ^ i : Polynomial B).Monic
    rw [hsum]
    exact monic_X_pow_add (degree_sum_fin_lt _)
  have hQd : Q.natDegree = P.natDegree := by
    show (X ^ P.natDegree + ∑ i ∈ Finset.range P.natDegree, C (c i) * X ^ i : Polynomial B).natDegree = _
    rw [hsum, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]
    exact degree_sum_fin_lt _
  have key : ∀ x : B, P.eval (g x) - g (Q.eval x) ∈ Ideal.span {g π ^ (P.natDegree * (M + 1))} := by
    intro x
    have e : P.eval (g x) - g (Q.eval x) =
        ∑ i ∈ Finset.range P.natDegree, (P.coeff i - g (c i)) * g x ^ i := by
      conv_lhs => rw [hP.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Q, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, map_add (f := _), map_pow,
        map_sum, map_mul, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [e]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hc i)
  obtain ⟨b, hb⟩ := GlobalTheory.CompanionTheory.AicSplit.exists_eval_eq_prod_of_natDegree_eq
    (fun p hp hpd => hA p hp hpd) P.natDegree Q hQm hQd
  have hle : Ideal.span {g π ^ (P.natDegree * (M + 1))} ≤ Ideal.span {g π ^ (P.natDegree * M)} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (by gcongr; omega))
  have h1 : g (Q.eval a) ∈ Ideal.span {g π ^ (P.natDegree * M)} := by
    have h := Ideal.sub_mem _ ha (hle (key a))
    rwa [sub_sub_cancel] at h
  have h2 := hinj _ _ h1
  rw [hb a] at h2
  obtain ⟨a₁, ha₁, h0⟩ := GlobalTheory.CompanionTheory.RootNear.root_near B π hπ hV P.natDegree M b a hd h2
  refine ⟨a₁, ha₁, ?_⟩
  have h3 := key a₁
  rwa [hb a₁, h0, map_zero, sub_zero] at h3

end GlobalTheory.CompanionTheory.AicStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCountFromHyperplanes
section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpLower

open Finset

theorem re_sesq_sum {V ι : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (s t : Finset ι) (f : ι → V) :
    (B (∑ a ∈ s, f a) (∑ b ∈ t, f b)).re = ∑ a ∈ s, ∑ b ∈ t, (B (f a) (f b)).re := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, Complex.re_sum]
  rw [Finset.sum_comm]

theorem card_filter_ne_zero {α : Type} [Fintype α] [Zero α] :
    (((univ : Finset α).filter (fun a => a ≠ 0)).card : ℝ) = (Fintype.card α : ℝ) - 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset α)) (fun a => a ≠ 0)
  have h0 : ((univ : Finset α).filter (fun a => ¬ a ≠ 0)).card = 1 := by
    have : (univ : Finset α).filter (fun a => ¬ a ≠ 0) = {0} := by
      ext a; simp
    rw [this, card_singleton]
  rw [h0, card_univ] at h
  rw [← h]; push_cast; ring

theorem sum_line {k : Type} [Field k] [Fintype k] {n : ℕ} (a : Fin (n + 1) → k) (ha : a ≠ 0)
    (D : (Fin (n + 1) → k) → ℝ) (hD : ∀ b, (∀ s : k, b ≠ s • a) → D b = 0) :
    ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), D b
      = ∑ s ∈ (univ : Finset k).filter (fun s => s ≠ 0), D (s • a) := by
  have hinj : Function.Injective (fun s : k => s • a) := smul_left_injective k ha
  rw [← Finset.sum_image (f := D) (g := fun s : k => s • a) hinj.injOn]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro b hb
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hb
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    exact smul_ne_zero hs ha
  · intro b hb hb'
    refine hD b ?_
    intro s hs
    apply hb'
    refine Finset.mem_image.mpr ⟨s, ?_, hs.symm⟩
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    rintro rfl
    exact hb (by simpa using hs)

theorem row_identity {k : Type} [Field k] [Fintype k] {n : ℕ} (a : Fin (n + 1) → k) (ha : a ≠ 0)
    (N R : (Fin (n + 1) → k) → ℝ) (c : ℝ)
    (hN0 : N 0 = 0)
    (hNa : (Fintype.card k : ℝ) * N a = (Fintype.card k : ℝ) ^ (n + 1))
    (hNs : ∀ s : k, s ≠ 1 → N (s • a) = 0)
    (hNo : ∀ b, (∀ s : k, b ≠ s • a) → (Fintype.card k : ℝ) * N b = (Fintype.card k : ℝ) ^ n)
    (hR : ∀ s : k, s ≠ 0 → R (s • a) = c) :
    (Fintype.card k : ℝ) * ∑ b, N b * R b
      = (Fintype.card k : ℝ) ^ n *
          ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), R b
        + (Fintype.card k : ℝ) ^ n * c := by
  set q : ℝ := (Fintype.card k : ℝ) with hq
  have hZ : ∑ b, N b * R b
      = ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), N b * R b := by
    symm
    refine Finset.sum_subset (filter_subset _ _) ?_
    intro b _ hb
    have : b = 0 := by simpa using hb
    simp [this, hN0]
  have hD := sum_line a ha (fun b => (q * N b - q ^ n) * R b)
    (fun b hb => by show (q * N b - q ^ n) * R b = 0; rw [hNo b hb]; ring)
  have hterm : ∀ s ∈ (univ : Finset k).filter (fun s => s ≠ 0),
      (q * N (s • a) - q ^ n) * R (s • a) = (if s = 1 then q ^ (n + 1) * c else 0) - q ^ n * c := by
    intro s hs
    have s0 : s ≠ 0 := by simpa using hs
    rw [hR s s0]
    by_cases h : s = 1
    · subst h
      rw [one_smul, hNa]; simp; ring
    · rw [hNs s h]; simp [h]
  have h1mem : (1 : k) ∈ (univ : Finset k).filter (fun s => s ≠ 0) := by simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos h1mem,
    Finset.sum_const, nsmul_eq_mul, card_filter_ne_zero] at hD
  have hsplit : q * ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), N b * R b
      = q ^ n * ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0), R b
        + ∑ b ∈ (univ : Finset (Fin (n + 1) → k)).filter (fun b => b ≠ 0),
            (q * N b - q ^ n) * R b := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hZ, hsplit, hD]
  ring

theorem sum_expand {k : Type} [Field k] [Fintype k] {n : ℕ}
    (R : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ) :
    ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = ∑ a, ∑ b, ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card : ℝ)
          * R a b := by
  calc ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = ∑ x : Fin (n + 1) → k, ∑ a, ∑ b, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : a ⬝ᵥ x = 1
        · simp [ha, Finset.sum_filter]
        · simp [ha]
    _ = ∑ a, ∑ x : Fin (n + 1) → k, ∑ b, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 :=
        Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ x : Fin (n + 1) → k, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem lower_from_counts : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  (w : (Fin (n + 1) → k) → V) (c A : ℝ),
  (∀ x, 0 ≤ (B x x).re) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 →
    Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a b : Fin (n + 1) → k, a ≠ 0 → (∀ s : k, b ≠ s • a) →
    Fintype.card k ^ 2 * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → ∀ s : k, s ≠ 0 → w (s • a) = w a) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → (B (w a) (w a)).re = c) →
  (∀ x : Fin (n + 1) → k, x ≠ 0 →
    (B (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)
       (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)).re = A) →
  (Fintype.card k : ℝ) ^ n * c ≤ (Fintype.card k : ℝ) * A := by
  intro k _ _ n V _ _ B w c A hpos h1 h2 hw hc hA
  have hq1 : (1 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.one_lt_card
  set q : ℝ := (Fintype.card k : ℝ) with hq
  have hq0 : q ≠ 0 := by linarith
  let N : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ := fun a b =>
    ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card : ℝ)
  let R : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ := fun a b => (B (w a) (w b)).re
  let Z : Finset (Fin (n + 1) → k) := univ.filter (fun b => b ≠ 0)
  have hZc : (Z.card : ℝ) = q ^ (n + 1) - 1 := by
    have h := card_filter_ne_zero (α := Fin (n + 1) → k)
    have hc' : (Fintype.card (Fin (n + 1) → k) : ℝ) = q ^ (n + 1) := by simp [hq]
    rw [hc'] at h
    rw [← h]
    simp only [Z]
    congr!
  have hrow : ∀ a, a ≠ 0 → q * ∑ b, N a b * R a b
      = q ^ n * ∑ b ∈ Z, R a b + q ^ n * c := by
    intro a ha
    refine row_identity a ha (N a) (R a) c ?_ ?_ ?_ ?_ ?_
    · simp [N]
    · have h := h1 a ha
      have : N a a = ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card : ℝ) := by
        simp only [N, and_self]
      rw [this]
      exact_mod_cast h
    · intro s hs
      have : univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ (s • a) ⬝ᵥ x = 1) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr ?_
        rintro x - ⟨hx, hx'⟩
        rw [smul_dotProduct, hx] at hx'
        exact hs (by simpa using hx')
      simp only [N, this, card_empty, Nat.cast_zero]
    · intro b hb
      have h := h2 a b ha hb
      have h' : q ^ 2 * N a b = q ^ (n + 1) := by
        simp only [N]; rw [hq]; exact_mod_cast h
      apply mul_left_cancel₀ hq0
      rw [← mul_assoc, ← pow_two, h', pow_succ]; ring
    · intro s hs
      simp only [R, hw a ha s hs, hc a ha]

  have hleft : ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = (q ^ (n + 1) - 1) * A := by
    have hZ : ∑ x ∈ Z, ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
        = ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b := by
      refine Finset.sum_subset (filter_subset _ _) ?_
      intro x _ hx
      have hx0 : x = 0 := by simpa [Z] using hx
      subst hx0
      simp
    rw [← hZ]
    have hconst : ∀ x ∈ Z, ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b = A := by
      intro x hx
      have hx0 : x ≠ 0 := by simpa [Z] using hx
      rw [← hA x hx0, re_sesq_sum]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hZc]

  have hright : q * ∑ a, ∑ b, N a b * R a b
      = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b + (q ^ (n + 1) - 1) * (q ^ n * c) := by
    have hZ : ∑ a ∈ Z, ∑ b, N a b * R a b = ∑ a, ∑ b, N a b * R a b := by
      refine Finset.sum_subset (filter_subset _ _) ?_
      intro a _ ha
      have ha0 : a = 0 := by simpa [Z] using ha
      subst ha0
      simp [N]
    rw [← hZ, Finset.mul_sum, Finset.sum_congr rfl (fun a ha => hrow a (by simpa [Z] using ha)),
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hZc]
  have hP : 0 ≤ ∑ a ∈ Z, ∑ b ∈ Z, R a b := by
    have := hpos (∑ a ∈ Z, w a)
    rwa [re_sesq_sum] at this
  have hmain : q * ((q ^ (n + 1) - 1) * A)
      = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b + (q ^ (n + 1) - 1) * (q ^ n * c) := by
    rw [← hleft, sum_expand R]
    exact hright
  have hQ : 0 < q ^ (n + 1) - 1 := by
    have : 1 < q ^ (n + 1) := one_lt_pow₀ hq1 (Nat.succ_ne_zero n)
    linarith
  have hqn : 0 ≤ q ^ n := by positivity
  have hfin : 0 ≤ (q ^ (n + 1) - 1) * (q * A - q ^ n * c) := by
    have : (q ^ (n + 1) - 1) * (q * A - q ^ n * c) = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b := by
      linear_combination hmain
    rw [this]
    exact mul_nonneg hqn hP
  have := nonneg_of_mul_nonneg_right hfin hQ
  linarith

end GlobalTheory.CompanionTheory.GapOpLower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatricesCard
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem card_hermitian_resAlg (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ)
    (hE : ResAlg E τ q ε) (n : ℕ) :
    Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H} = q ^ (n ^ 2) := by
  have hq : q ≠ 0 := by have := hE.one_lt; omega
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE.card]; exact pow_ne_zero 2 hq)
  obtain ⟨u, hu, -⟩ := hE.basis
  have key := GlobalTheory.GramCount.card_hermitian_dvd_sq τ hE.inv u hu 1 (map_one τ) n
  have hiff : ∀ H : Matrix (Fin n) (Fin n) E,
      cT τ H = H ↔ ((∀ a b, τ (H b a) = H a b) ∧ ∀ a b, (1 : E) ∣ H a b) := by
    intro H
    constructor
    · intro h
      refine ⟨fun a b => ?_, fun a b => one_dvd _⟩
      have := congrFun (congrFun h a) b
      simpa [cT] using this
    · rintro ⟨h, -⟩
      ext a b
      simpa [cT] using h a b
  have e1 : Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H}
      = Nat.card {H : Matrix (Fin n) (Fin n) E //
          (∀ a b, τ (H b a) = H a b) ∧ ∀ a b, (1 : E) ∣ H a b} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  have e2 : Nat.card {x : E // (1 : E) ∣ x} = q ^ 2 := by
    rw [← hE.card]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => one_dvd x)
  rw [e2] at key
  have hsq : (q ^ (n ^ 2)) ^ 2 = (q ^ 2) ^ (n * n) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [e1]
  exact Nat.pow_left_injective (by norm_num) (key.trans hsq.symm)

end GlobalTheory.CompanionTheory.UnrDens
end

