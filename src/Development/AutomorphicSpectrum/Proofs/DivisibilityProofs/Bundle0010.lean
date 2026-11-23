module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.WeilBound.CoreStatements.IdealCycleValues.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0004
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FrobeniusShapeOfSidePreserving
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem isLeft_pow_congr {Ψ : Type} (f : Equiv.Perm (Ψ ⊕ Ψ))
    (hf : (∀ σ, (f σ).isLeft = σ.isLeft) ∨ ∀ σ, (f σ).isLeft = σ.isRight) (k : ℕ) :
    ∀ σ σ' : Ψ ⊕ Ψ, σ.isLeft = σ'.isLeft → ((f ^ k) σ).isLeft = ((f ^ k) σ').isLeft := by
  induction k with
  | zero =>
    intro σ σ' h
    simpa using h
  | succ k ih =>
    intro σ σ' h
    have h' := ih σ σ' h
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rcases hf with hf | hf
    · rw [hf, hf]
      exact h'
    · rw [hf, hf]
      cases h1 : (f ^ k) σ <;> cases h2 : (f ^ k) σ' <;> simp_all

theorem frobShape_of_side : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)), (∀ p, (∀ σ, (φ p σ).isLeft = σ.isLeft) ∨ ∀ σ, (φ p σ).isLeft = σ.isRight) → FrobShape fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ : Ψ ⊕ Ψ) := by
  intro Ψ _ _ φ h
  unfold FrobShape
  intro p n τ τ'
  exact isLeft_pow_congr (φ p) (h p) (n + 1) _ _ rfl

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FunctionalProductLinearForms
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem linearFunctional_prod_linearForms : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (c : Fin d → J → ℝ), Φ (∏ k, ∑ j, C (c k j) * X j) = ∑ w : Fin d → J, (∏ k, c k (w k)) * Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  exact @RootFieldNumerics.linear_functional_product_expansion

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenNumProductExpansion
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem genNum_mul_expand : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * genNum F V cls H (classList cls μ ++ Q) :=
  @BaseChangeColon.genNum_mul_expansion

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HsymmDualRootsTrivNumZero
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem hsymm_dualRoots_triv_numZero : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ a : ℕ, 1 ≤ a → ∀ Y : List (K → ℤ), a + Y.length = e → ∑ α ∈ Finset.Nat.antidiagonalTuple N a, intNumL F (pointIdeal F y) (rootList (fun i => -b i) α ++ Y) = 0 :=
  BaseChangeColon.flag_frame_of_point_ideal

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LimitHeightConstantShift
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

open Filter Topology

theorem arFun_tendsto_PP {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem)
    (h : M.Converges II) (F : RPA Ψ N) :
    Tendsto (fun t => M.arFun II t F) (𝓝[>] 0) (𝓝 (M.PP II F)) := by
  classical
  simp only [GlobalTheory.CompanionTheory.Ar.Top.RootModel.arFun, GlobalTheory.CompanionTheory.Ar.Top.RootModel.PP, Module.Basis.constr_apply, Finsupp.sum]
  refine tendsto_finsetSum _ (fun m _ => ?_)
  obtain ⟨L, hL⟩ := h m
  exact (tendsto_nhds_limUnder ⟨L, hL⟩).const_smul _

theorem PP_eq_add_of_arFun_eq_add :
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M M' : RootModel Ψ N) (II : IntersectionSystem), M.Converges II →
      M'.Converges II → ∀ (F : RPA Ψ N) (c : ℝ), (∀ t : ℝ, 0 < t → M.arFun II t F = M'.arFun II t F + c) →
      M.PP II F = M'.PP II F + c := by
  intro Ψ _ N M M' II hM hM' F c hF
  have h1 := arFun_tendsto_PP M II hM F
  have h2 := (arFun_tendsto_PP M' II hM' F).add_const c
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hF t ht).symm

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalNumberPermutationInvariant
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num.RootPerm

theorem classList_mapDomain {K σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (μ : σ →₀ ℕ) :
    classList cls (Finsupp.mapDomain e μ) = classList (cls ∘ e) μ := by
  unfold classList
  rw [← Finsupp.toMultiset_map, Multiset.map_map]

theorem classNum_rename {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (he : Function.Injective e)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_rename_mapDomain e he, classList_mapDomain]

theorem rename_psumExpansion {r : ℕ} (e : Equiv.Perm (Fin r)) (k : ℕ) (i : Fin r) :
    rename (Sum.map e e) (psumExpansion r k i) = psumExpansion r k (e i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [psumExpansion, map_sum, rename_X]

theorem root_perm : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (r : ℕ) (e : Equiv.Perm (Fin r)) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)), (∀ (a : O) (x : Fin r → K → ℤ), laNum P a (x ∘ e) k Q = laNum P a x k Q) ∧ ∀ T : LocPair ι O (Fin r), (T.comp e).ck P k Q = T.ck P k Q := by
  intro O _ _ _ K _ _ ι _ r e P k Q
  refine ⟨fun a x => ?_, fun T => ?_⟩
  · have h : ∀ W : Ideal (MRing ι O), classNum (x ∘ e) (psum (Fin r) ℤ (k - 1)) Q W =
        classNum x (psum (Fin r) ℤ (k - 1)) Q W := fun W => by
      rw [← classNum_rename x e e.injective, rename_psum]
    simp only [laNum, h]
  · have h : ∀ (i : Fin r) (W : Ideal (MRing ι O)),
        classNum (Sum.elim (T.x ∘ e) (T.x' ∘ e)) (psumExpansion r k i) Q W =
          classNum (Sum.elim T.x T.x') (psumExpansion r k (e i)) Q W := fun i W => by
      have hc : Sum.elim T.x T.x' ∘ Sum.map e e = Sum.elim (T.x ∘ e) (T.x' ∘ e) := by
        funext s
        rcases s with s | s <;> rfl
      rw [← rename_psumExpansion, classNum_rename _ _ (Sum.map_injective.mpr ⟨e.injective, e.injective⟩), hc]
    simp only [LocPair.ck, pairNum, LocPair.comp, Function.comp_apply, h]
    exact Equiv.sum_comp e fun j => cycEval (fun W => classNum (Sum.elim T.x T.x') (psumExpansion r k j) Q W)
      (ratDiv P (T.f j) (T.g j))

end GlobalTheory.CompanionTheory.Ar.Num.RootPerm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralCongrSmul
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem ptsIntegral_congr_and_homog :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (e : ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ), (∀ g g' : ((Σ k, ι k) → ℂ) → ℝ, (∀ z ∈ mcPts P, g z = g' z) → ptsIntegral P φ g = ptsIntegral P φ g') ∧ ∀ (c : ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ), ptsIntegral P φ (fun z => c * g z) = c * ptsIntegral P φ g := by
  classical
  intro K _ _ ι _ P e φ
  refine ⟨fun g g' hg => ?_, fun c g => ?_⟩
  · exact (ReciprocityTheory.ChartRestriction.G.Geo.ptsLocal K ι P e 0 φ φ g g' (fun _ _ _ => rfl) hg).2
  · unfold ptsIntegral
    split_ifs with h
    · unfold ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegralAt
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      funext y
      have : ∀ w, ReciprocityTheory.ChartRestriction.G.Geo.sheetDensity P h.choose φ (fun z => c * g z) y w =
          c * ReciprocityTheory.ChartRestriction.G.Geo.sheetDensity P h.choose φ g y w := by
        intro w
        unfold ReciprocityTheory.ChartRestriction.G.Geo.sheetDensity
        split_ifs <;> ring
      simp only [this]
      rw [← mul_finsum_mem]
    · simp

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MassFormulaConjugationAction
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

section Lin

variable {K : Type} [Fintype K] {ι : K → Type} {σ : Type}
  (I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
  (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (A : σ → HermLine ι)

theorem arNum_eq_sum_of_subset (H : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ)) (hs : H.support ⊆ s) :
    arNum I P A H = ∑ μ ∈ s, H.coeff μ * arList I P (μ.toMultiset.map A).toList := by
  unfold arNum
  refine Finset.sum_subset hs fun μ _ hμ => ?_
  rw [MvPolynomial.notMem_support_iff.1 hμ, zero_mul]

theorem arNum_add' (H H' : MvPolynomial σ ℝ) :
    arNum I P A (H + H') = arNum I P A H + arNum I P A H' := by
  classical
  rw [arNum_eq_sum_of_subset I P A (H + H') (H.support ∪ H'.support) MvPolynomial.support_add,
    arNum_eq_sum_of_subset I P A H (H.support ∪ H'.support) Finset.subset_union_left,
    arNum_eq_sum_of_subset I P A H' (H.support ∪ H'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem arNum_C_mul' (c : ℝ) (H : MvPolynomial σ ℝ) :
    arNum I P A (C c * H) = c * arNum I P A H := by
  have hs : (C c * H).support ⊆ H.support := by
    intro μ hμ
    rw [MvPolynomial.mem_support_iff] at hμ ⊢
    intro h0
    exact hμ (by rw [MvPolynomial.coeff_C_mul, h0, mul_zero])
  rw [arNum_eq_sum_of_subset I P A (C c * H) H.support hs, arNum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_C_mul, mul_assoc]

theorem arNum_zero' : arNum I P A (0 : MvPolynomial σ ℝ) = 0 := by
  simp [arNum]

theorem arNum_sum' {α : Type} (s : Finset α) (H : α → MvPolynomial σ ℝ) :
    arNum I P A (∑ a ∈ s, H a) = ∑ a ∈ s, arNum I P A (H a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using arNum_zero' I P A
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, arNum_add', ih]

theorem arNum_monomial' (μ : σ →₀ ℕ) (c : ℝ) :
    arNum I P A (monomial μ c) = c * arList I P (μ.toMultiset.map A).toList := by
  classical
  rw [arNum_eq_sum_of_subset I P A (monomial μ c) {μ} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

theorem arNum_rename' {σ' : Type} (e : σ' → σ) (H : MvPolynomial σ' ℝ) :
    arNum I P A (rename e H) = arNum I P (A ∘ e) H := by
  classical
  induction H using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [MvPolynomial.rename_monomial, arNum_monomial', arNum_monomial',
      show Finsupp.toMultiset (Finsupp.mapDomain e μ) = (Finsupp.toMultiset μ).map e from
        (Finsupp.toMultiset_map _ _).symm, Multiset.map_map]
  | add p q hp hq => rw [map_add (f := _), arNum_add', arNum_add', hp, hq]

end Lin

theorem exists_perm_of_ofFn_perm' {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : (List.ofFn v).Perm (List.ofFn w)) : ∃ s : Equiv.Perm (Fin n), v = w ∘ s :=
  _root_.UpperTheory.Reformulated.B.Yde7.main v w h

theorem arList_eq_of_perm {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1))
    {I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    (l : List (HermLine ι)) (L : Fin (D + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j))
    (hp : l.Perm (List.ofFn L)) : arList I P l = I P (D + 1) L := by
  have key : ∀ (m : ℕ) (v : Fin m → HermLine ι), (List.ofFn v).Perm (List.ofFn L) →
      I P m v = I P (D + 1) L := by
    intro m v h
    have hm : m = D + 1 := by simpa using h.length_eq
    subst hm
    obtain ⟨s, rfl⟩ := exists_perm_of_ofFn_perm' v L h
    exact hI.1 P _ L s hP hL
  refine key l.length l.get ?_
  rwa [List.ofFn_get]

theorem arNum_linear_arList_symm : (∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι ℤ)) (σ : Type) (A : σ → HermLine ι), (∀ H H' : MvPolynomial σ ℝ, arNum I P A (H + H') = arNum I P A H + arNum I P A H') ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), arNum I P A (C c * H) = c * arNum I P A H) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), arNum I P A (∑ a ∈ s, H a) = ∑ a ∈ s, arNum I P A (H a)) ∧ (∀ (μ : σ →₀ ℕ) (c : ℝ), arNum I P A (monomial μ c) = c * arList I P (μ.toMultiset.map A).toList) ∧ ∀ (σ' : Type) (e : σ' → σ) (H : MvPolynomial σ' ℝ), arNum I P A (rename e H) = arNum I P (A ∘ e) H) ∧ (∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (l : List (HermLine ι)) (L : Fin (D + 1) → HermLine ι), (∀ j, IsSmoothHerm (L j)) → l.Perm (List.ofFn L) → arList I P l = I P (D + 1) L) := by
  refine ⟨?_, ?_⟩
  · intro K _ _ ι _ I P σ A
    exact ⟨arNum_add' I P A, arNum_C_mul' I P A, fun α s H => arNum_sum' I P A s H,
      arNum_monomial' I P A, fun σ' e H => arNum_rename' I P A e H⟩
  · intro K _ _ ι _ P D hP I hI l L hL hp
    exact arList_eq_of_perm hP hI l L hL hp

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MeanSlopeProportionalVolume
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem mean_slope_of_volume_eq : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (C rd Lval : ℝ), T.Proportional → T.VolEq → T.T2 II C rd Lval → T.MeanSlope II C rd Lval :=
  @RootFieldNumerics.mean_slope_of_proportional_volume

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MonomialLinesPermutation
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem monoLines_monomial_word : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) (ℓ : J → HermLine ι) (w : Fin d → J), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ).degree = d ∧ ∃ σ : Equiv.Perm (Fin d), monoLines ℓ (∑ k, Finsupp.single (w k) 1) d = (fun k => ℓ (w k)) ∘ σ ∧ II K ι P d (monoLines ℓ (∑ k, Finsupp.single (w k) 1) d) = II K ι P d (fun k => ℓ (w k)) :=
  RootFieldNumerics.intersection_monomial_lines

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PerturbedWeightGapBounds
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem hypotheses_hold_for_large_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (c₀ θ₀ : ℝ), 0 < c₀ → 0 < θ₀ → ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∀ (τ₀ : Ψ) (lam₀ : Wt Ψ N), InWall T.j τ₀ c₀ lam₀ → let θ : ℝ := 5 * Fintype.card Ψ / B; let lam : Wt Ψ N := fun τ i => lam₀ τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0); 3 ≤ B ∧ 0 < θ ∧ θ ≤ θ₀ ∧ θ ≤ 1 ∧ ‖lam‖ ≤ 1 ∧ ‖T.lamS lam (θ ^ 2)‖ ≤ 1 ∧ (∀ τ, θ ≤ gap T.j lam τ) ∧ gap T.j lam τ₀ = 2 * θ ∧ CompactGapsGE T.j c₀ lam ∧ Dominant lam ∧ Dominant (T.lamS lam (θ ^ 2)) ∧ NefThreshold T.j B (T.lamS lam (θ ^ 2)) ∧ ‖T.lamS lam (θ ^ 2) - lam₀‖ ≤ 2 * θ + ‖T.nu‖ * θ ^ 2 :=
  @RootFieldNumerics.perturbed_weight_wall_bounds

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RationalWeightIntegralCoeffs
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem clear_rat_weight_coef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → ∃ (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), 0 < q ∧ ∀ j, (n j : ℝ) = q * M.coef lam s j :=
  @RootFieldNumerics.exists_integer_coefficients_rational

end GlobalTheory.CompanionTheory.Ar.Top
end

