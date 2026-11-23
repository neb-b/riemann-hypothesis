module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0009
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0010

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.MonomialsAreWeightVectors
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem v2con_X_pderiv {R : Type*} [CommRing R] {σ : Type*} (v w : σ) (m : σ →₀ ℕ) (c : R) :
    (X v : MvPolynomial σ R) * pderiv w (monomial m c) =
      monomial (m - Finsupp.single w 1 + Finsupp.single v 1) (c * (m w : R)) := by
  rw [pderiv_monomial, show (X v : MvPolynomial σ R) = monomial (Finsupp.single v 1) 1 from rfl,
    monomial_mul, one_mul, add_comm (Finsupp.single v 1)]

theorem v2con_X_pderiv_self {R : Type*} [CommRing R] {σ : Type*} (v : σ) (m : σ →₀ ℕ) (c : R) :
    (X v : MvPolynomial σ R) * pderiv v (monomial m c) = monomial m (c * (m v : R)) := by
  rw [v2con_X_pderiv]
  by_cases h : m v = 0
  · simp [h]
  · have hle : Finsupp.single v 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [tsub_add_cancel_of_le hle]

theorem v2con_diag {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : R) :
    glAct R LL S a a (monomial m c) = monomial m (((wtS LL S m a : ℤ) : R) * c) := by
  classical
  unfold glAct wtS
  rw [LinearMap.sum_apply]
  simp only [Int.cast_sum, Finset.sum_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  by_cases h1 : l ∈ S <;> by_cases h2 : LL.vec l = true <;>
    simp [h1, h2, -pderiv_monomial, v2con_X_pderiv_self, mul_comm]

theorem v2con_coeff_diag {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (glAct R LL S a a x) m = ((wtS LL S m a : ℤ) : R) * AddMonoidAlgebra.coeff x m := by
  classical
  induction x using MvPolynomial.induction_on' with
  | monomial m' c =>
    rw [v2con_diag, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem monomials_are_weight_vectors : MonomialsAreWeightVectors := by
  intro R _ _ ι _ LL n S
  constructor
  · intro m c
    rw [weightSp, Submodule.mem_iInf]
    intro a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    change glAct R LL S a a (monomial m c) - _ = 0
    rw [v2con_diag, smul_monomial, smul_eq_mul, sub_self]
  · intro ν x hx m hm
    rw [weightSp, Submodule.mem_iInf] at hx
    funext a
    have h := hx a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h
    have h2 := congrArg (AddMonoidAlgebra.coeff · m) h
    change AddMonoidAlgebra.coeff (glAct R LL S a a x) m = _ at h2
    rw [v2con_coeff_diag, coeff_smul, smul_eq_mul] at h2
    have hc : AddMonoidAlgebra.coeff x m ≠ 0 := mem_support_iff.mp hm
    have h3 := mul_right_cancel₀ hc h2
    exact_mod_cast h3

theorem v2con_stable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (N : ℕ) (a b : Fin n) (x : MvPolynomial (ι × Fin n) R)
    (hx : x ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N}) :
    glAct R LL S a b x ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
  classical
  rw [mem_restrictSupport_iff] at hx
  have hmono : ∀ (m' : ι × Fin n →₀ ℕ) (c' : R), m'.degree ≤ N →
      monomial m' c' ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
    intro m' c' hm'
    rw [mem_restrictSupport_iff]
    intro y hy
    have := Finset.mem_singleton.mp (support_monomial_subset hy)
    subst this
    exact hm'
  have hterm : ∀ (m : ι × Fin n →₀ ℕ) (c : R) (u w : ι × Fin n), m.degree ≤ N →
      (X u : MvPolynomial (ι × Fin n) R) * pderiv w (monomial m c) ∈
        restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
    intro m c u w hm
    rw [v2con_X_pderiv]
    by_cases h0 : m w = 0
    · simp [h0]
    · apply hmono
      have hle : Finsupp.single w 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      have e1 : (m - Finsupp.single w 1).degree + 1 = m.degree := by
        have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        rw [map_add (f := _), Finsupp.degree_single] at this
        exact this
      rw [map_add (f := _), Finsupp.degree_single]
      omega
  set_option synthInstance.maxHeartbeats 100000 in
    rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  have hdeg : m.degree ≤ N := hx hm
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ (fun l _ => ?_)
  split_ifs
  · exact hterm m _ _ _ hdeg
  · rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hterm m _ _ _ hdeg)
  · exact Submodule.zero_mem _

theorem polynomial_locally_finite : PolynomialLocallyFinite := by
  intro R _ ι _ LL n S x
  classical
  refine ⟨restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ x.totalDegree}, ?_, ?_, ?_⟩
  · haveI : Finite {m : ι × Fin n →₀ ℕ | m.degree ≤ x.totalDegree} :=
      (Finsupp.finite_of_degree_le x.totalDegree).to_subtype
    exact Module.Finite.of_basis (basisRestrictSupport R _)
  · rw [mem_restrictSupport_iff]
    intro m hm
    show m.degree ≤ x.totalDegree
    rw [Finsupp.degree_apply]
    exact le_totalDegree hm
  · intro a b y hy
    exact v2con_stable LL S _ a b y hy

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialIsotypicLatticeOfParts
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem operator_list_lattice_scaling {O : Type} [CommRing O] [IsDomain O] {σ : Type} (p : ℕ)
    (L : Submodule O (MvPolynomial σ (KK O))) (W : Submodule (KK O) (MvPolynomial σ (KK O)))
    (l : List (Module.End (KK O) (MvPolynomial σ (KK O)) × ℕ))
    (hW : ∀ eD ∈ l, ∀ F ∈ W, eD.1 F ∈ W)
    (hL : ∀ eD ∈ l, ∀ F ∈ W, F ∈ L → ((p : KK O) ^ eD.2) • eD.1 F ∈ L) :
    ∀ F ∈ W, F ∈ L → (l.map Prod.fst).prod F ∈ W ∧
      ((p : KK O) ^ (l.map Prod.snd).sum) • (l.map Prod.fst).prod F ∈ L := by
  induction l with
  | nil =>
    intro F hF hFL
    simp [hF, hFL]
  | cons eD l ih =>
    intro F hF hFL
    have hW' : ∀ e ∈ l, ∀ F ∈ W, e.1 F ∈ W := fun e he => hW e (List.mem_cons_of_mem _ he)
    have hL' : ∀ e ∈ l, ∀ F ∈ W, F ∈ L → ((p : KK O) ^ e.2) • e.1 F ∈ L :=
      fun e he => hL e (List.mem_cons_of_mem _ he)
    obtain ⟨h1, h2⟩ := ih hW' hL' F hF hFL
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨hW eD (by simp) _ h1, ?_⟩
    have h3 := hL eD (by simp) _ (W.smul_mem ((p : KK O) ^ (l.map Prod.snd).sum) h1) h2
    rw [map_smul, smul_smul, ← pow_add] at h3
    exact h3

theorem polynomial_isotypic_lattice_of_parts (D : Formalism.BasicNotions.D7) (hCR : CompleteReducibilityIsotypic) (hOrth : ContravariantIsotypicOrthogonal) (hDom : HighestWeightDominant)
    (hRes : SubrepRestrictionRep) (hPol : PolynomialGLRepresentation) (hLat : AdmissibleDVRIntegralFormLatticesStable) (h13 : IsotypicProjectorTheoremField D) : FilteredProjectorCorollaryField D := by
  intro p n' O _ _ _ S0 hG n ι _ LL N Ss hmono
  obtain ⟨hchar, hLat'⟩ := hLat p n' O S0 hG
  obtain ⟨hL1, hL2, BBs, hBB, hL3⟩ := hLat' n ι LL
  refine ⟨fun i => hL1 (Ss i), ?_⟩
  intro ee hee
  obtain ⟨hP1, hP2, hP3, -, -, -, B, hB1, hB2⟩ := hPol (KK O) ι n LL
  have hT : ∀ S : Set ι, (⨆ mu : Fin n → ℤ, isoSub (glOps (KK O) n LL S) mu) = ⊤ :=
    fun S => hCR (KK O) _ n _ (hP1 S)

  have hdis : ∀ i lam (S' : Set ι), Disjoint (Ss i) S' → ∀ a b,
      ee i lam * glOps (KK O) n LL S' a b = glOps (KK O) n LL S' a b * ee i lam := by
    intro i lam S' hS' a b
    refine isotypic_projector_commutes _ (hT (Ss i)) lam _ (hee i lam) _ fun mu x hx => ?_
    exact isotypic_stable_commuting _ _ (fun c d => (hP2 (Ss i) S' hS' c d a b).symm) mu x hx
  have hle : ∀ i j, i ≤ j → ∀ lam a b,
      ee i lam * glOps (KK O) n LL (Ss j) a b = glOps (KK O) n LL (Ss j) a b * ee i lam := by
    intro i j hij lam a b
    rw [hP3 (Ss i) (Ss j) (hmono hij) a b, mul_add, add_mul, hdis i lam _ Set.disjoint_sdiff_right a b]
    congr 1
    exact isotypic_projector_commutes _ (hT (Ss i)) lam _ (hee i lam) _ fun mu x hx => isotypic_stable_gl_operator _ mu a b x hx
  have hcomm' : ∀ i j, i ≤ j → ∀ lam mu, ee i lam * ee j mu = ee j mu * ee i lam := by
    intro i j hij lam mu
    refine (isotypic_projector_commutes _ (hT (Ss j)) mu _ (hee j mu) _ fun nu x hx => ?_).symm
    exact isotypic_stable_commuting _ _ (fun c d => hle i j hij lam c d) nu x hx
  refine ⟨hle, hdis, ?_, ?_, ?_⟩
  · intro i j lam mu
    rcases le_total i j with h | h
    · exact hcomm' i j h lam mu
    · exact (hcomm' j i h mu lam).symm
  · intro i lam F G
    rw [← hB1, ← hB1]
    exact isotypic_projector_selfAdjoint _ (hT (Ss i)) lam _ (hee i lam) B
      (hOrth (KK O) _ n _ (hP1 (Ss i)) B (fun a b x y => hB2 (Ss i) a b x y)) F G
  · intro T d F hF
    have hstep := fun (i : Fin N) (lam : Fin n → ℤ) =>
      isotypic_projector_lattice_scaling D hDom hRes hPol h13 p n' O S0 hG n ι LL (Ss i) d lam (ee i lam) (hee i lam)
    have main : ∀ L : Submodule O (MvPolynomial (ι × Fin n) (KK O)),
        (∀ S : Set ι, ∀ u ∈ UZgens (glOps (KK O) n LL S), ∀ F ∈ L, u F ∈ L) → (latticeMultidegreePart L d).FG →
        MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ → F ∈ L →
        ((p : KK O) ^ (∑ i, N0 n * Nat.log p (2 * degIn d (Ss i) + n - 1))) •
          (∑ t ∈ T, (List.ofFn fun i => ee i (t i)).prod) F ∈ L := by
      intro L hst hFG hMQ hFL
      rw [LinearMap.sum_apply, Finset.smul_sum]
      refine Submodule.sum_mem _ fun t _ => ?_
      have h := operator_list_lattice_scaling p L (Pol (KK O) n d)
        (List.ofFn fun i => (ee i (t i), N0 n * Nat.log p (2 * degIn d (Ss i) + n - 1)))
        (by
          intro eD heD
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 heD
          exact (hstep i (t i)).1)
        (by
          intro eD heD
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 heD
          exact (hstep i (t i)).2 L (hst (Ss i)) hFG hMQ) F hF hFL
      rw [List.map_ofFn, List.map_ofFn, List.sum_ofFn] at h
      exact h.2
    obtain ⟨h1, h2, h3, h4⟩ := hL3 d
    refine ⟨fun hFL => main _ (fun S u hu => (hL2 S u hu).1) h1 h2 hFL, fun hFB => ?_⟩
    rw [← hBB] at hFB ⊢
    exact main BBs (fun S u hu F hF => (hBB _).2 ((hL2 S u hu).2 F ((hBB _).1 hF))) h3 h4 hFB

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialMemWeightSpaceIff
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem monomial_shift_cancel {σ : Type} (m : σ →₀ ℕ) (v : σ) (c : K) :
    (monomial (m - Finsupp.single v 1 + Finsupp.single v 1) (c * (m v : K)) : MvPolynomial σ K) =
      monomial m (c * (m v : K)) := by
  by_cases h : m v = 0
  · simp [h]
  · rw [tsub_add_cancel_of_le]
    rw [Finsupp.single_le_iff]
    omega

theorem diagonal_derivation_monomial (LL : Letters ι) (S : Set ι) (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : K) :
    glDerivation K LL S a a (monomial m c) = monomial m (((wtS LL S m a : ℤ) : K) * c) := by
  rw [gl_derivation_monomial]
  simp only [monomial_shift_cancel]
  unfold wtS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Int.cast_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp [mul_comm]

theorem diagonal_derivation_coeff (LL : Letters ι) (S : Set ι) (a : Fin n) (F : MvPolynomial (ι × Fin n) K)
    (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (glDerivation K LL S a a F) m = ((wtS LL S m a : ℤ) : K) * AddMonoidAlgebra.coeff F m := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [diagonal_derivation_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add, mul_add]

theorem polynomial_mem_weightSpace_iff (LL : Letters ι) (S : Set ι) (mu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) K) :
    F ∈ weightSp (glOps K n LL S) mu ↔ ∀ a, glDerivation K LL S a a F = ((mu a : ℤ) : K) • F := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, sub_eq_zero, gl_operator_apply_derivation]
  rfl

theorem weight_vector_monomial_weight [CharZero K] (LL : Letters ι) (S : Set ι) (mu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) K)
    (hF : F ∈ weightSp (glOps K n LL S) mu) (m : ι × Fin n →₀ ℕ) (hm : m ∈ F.support) : wtS LL S m = mu := by
  funext a
  have h := congrArg (AddMonoidAlgebra.coeff · m) ((polynomial_mem_weightSpace_iff LL S mu F).1 hF a)
  rw [diagonal_derivation_coeff, coeff_smul, smul_eq_mul] at h
  have hc : AddMonoidAlgebra.coeff F m ≠ 0 := mem_support_iff.1 hm
  have h2 := mul_right_cancel₀ hc h
  exact_mod_cast h2

theorem monomial_mem_weightSpace (LL : Letters ι) (S : Set ι) (m : ι × Fin n →₀ ℕ) (c : K) :
    monomial m c ∈ weightSp (glOps K n LL S) (wtS LL S m) := by
  rw [polynomial_mem_weightSpace_iff]
  intro a
  rw [diagonal_derivation_monomial, smul_monomial, smul_eq_mul]

theorem polynomial_isGLRep (LL : Letters ι) (S : Set ι) : IsGLRep (glOps K n LL S) := by
  classical
  refine ⟨polynomial_gl_commutation LL S, ?_, ?_⟩
  · intro x
    haveI : ∀ m : x.support, FiniteDimensional K (Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i)) :=
      fun m => homogeneous_multidegree_findim _
    refine ⟨⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i), inferInstance, ?_, ?_⟩
    · have key : ∑ m ∈ x.support, monomial m (AddMonoidAlgebra.coeff x m) ∈
          ⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i) := by
        apply Submodule.sum_mem
        intro m hm
        apply Submodule.mem_iSup_of_mem (⟨m, hm⟩ : x.support)
        rw [Pol, mem_restrictSupport_iff]
        intro m' hm'
        have h1 := support_monomial_subset (Finset.mem_coe.1 hm')
        rw [Finset.mem_singleton] at h1
        subst h1
        intro i
        rfl
      convert key using 1
      exact x.as_sum
    · intro a b y hy
      refine Submodule.iSup_induction _ (motive := fun y => glOps K n LL S a b y ∈
        ⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i)) hy ?_ ?_ ?_
      · intro m z hz
        exact Submodule.mem_iSup_of_mem m (gl_operator_preserves_multidegree LL S _ a b z hz)
      · simp
      · intro z w hz hw
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hz hw
  · rw [eq_top_iff]
    intro F _
    have key : ∑ m ∈ F.support, monomial m (AddMonoidAlgebra.coeff F m) ∈ ⨆ mu : Fin n → ℤ, weightSp (glOps K n LL S) mu := by
      apply Submodule.sum_mem
      intro m _
      exact Submodule.mem_iSup_of_mem (wtS LL S m) (monomial_mem_weightSpace LL S m _)
    convert key using 1
    exact F.as_sum

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.V2repResIsGLRep
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_Umon_stable (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (u : Module.End K V)
    (hu : u ∈ Umon E) : ∀ x ∈ W, u x ∈ W := by
  induction hu using Submonoid.closure_induction with
  | mem u hu => obtain ⟨⟨a, b⟩, rfl⟩ := hu; exact hW a b
  | one => intro x hx; exact hx
  | mul u v _ _ hu hv => intro x hx; exact hu _ (hv x hx)

theorem v2rep_isoIn_stable (E : GLOps n K V) (W : Submodule K V) (mu : Fin n → ℤ) :
    IsStableUnderOperators E (isotypicPartIn E W mu) := by
  intro a b x hx
  unfold isotypicPartIn at hx ⊢
  have h : Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, hhw, rfl⟩
    exact Submodule.subset_span
      ⟨E a b * u, (Umon E).mul_mem (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, v, hv, hhw, rfl⟩
  exact h hx

theorem v2rep_iSup_stable (E : GLOps n K V) {ι : Sort*} (p : ι → Submodule K V) (hp : ∀ i, IsStableUnderOperators E (p i)) :
    IsStableUnderOperators E (⨆ i, p i) := by
  intro a b x hx
  exact Submodule.iSup_induction (motive := fun y => E a b y ∈ ⨆ i, p i) p hx
    (fun i y hy => Submodule.mem_iSup_of_mem i (hp i a b y hy))
    (by rw [map_zero]; exact zero_mem _)
    (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)

def restrictToStableSubmodule (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) : GLOps n K W :=
  fun a b => (E a b).restrict (hW a b)

theorem v2rep_res_apply (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (a b : Fin n) (x : W) :
    ((restrictToStableSubmodule E W hW a b x : W) : V) = E a b x := rfl

theorem v2rep_res_weightSp (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (mu : Fin n → ℤ) :
    weightSp (restrictToStableSubmodule E W hW) mu = (weightSp E mu).comap W.subtype := by
  ext x
  simp only [weightSp, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Submodule.subtype_apply]
  refine forall_congr' fun a => ?_
  rw [← Submodule.coe_eq_zero, Submodule.coe_sub, Submodule.coe_smul, v2rep_res_apply]
  simp

theorem v2rep_res_isGLRep [CharZero K] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (W : Submodule K V)
    [FiniteDimensional K W] (hW : IsStableUnderOperators E W) (hw : W ≤ ⨆ ν, weightSp E ν) : IsGLRep (restrictToStableSubmodule E W hW) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := v2rep_comm E hR a b c d (x : V)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, v2rep_res_apply]
    rw [h, add_sub_cancel_left]
    congr 1
    · split_ifs <;> simp [v2rep_res_apply]
    · split_ifs <;> simp [v2rep_res_apply]
  · intro x
    exact ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  · rw [eq_top_iff]
    intro y _
    have h1 := v2rep_graded E W (fun a => hW a a) y y.2 (hw y.2)
    have h2 : (⨆ ν, weightSp E ν ⊓ W) = (⨆ ν, weightSp (restrictToStableSubmodule E W hW) ν).map W.subtype := by
      rw [Submodule.map_iSup]
      refine iSup_congr fun ν => ?_
      rw [v2rep_res_weightSp, Submodule.map_comap_subtype, inf_comm]
    rw [h2] at h1
    obtain ⟨y', hy', hyy⟩ := Submodule.mem_map.1 h1
    have : y' = y := Subtype.ext hyy
    rwa [this] at hy'

theorem stable_subspace_complete_reducibility (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : StableSubspaceCompleteReducibility := by
  intro K V _ _ _ _ n E hR W hfd hW hw
  have := hfd
  set W' : Submodule K V := ⨆ mu, isotypicPartIn E W mu with hW'
  have hW'st : IsStableUnderOperators E W' := v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E W mu
  obtain ⟨P2, hcompl, hP2⟩ := h2 K W n (restrictToStableSubmodule E W hW) (v2rep_res_isGLRep E hR W hW hw)
    (W'.comap W.subtype) (fun a b x hx => hW'st a b x hx)
  have hbot : P2 = ⊥ := by
    by_contra hne
    let Z : Submodule K V := P2.map W.subtype
    have hZW : Z ≤ W := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have : FiniteDimensional K Z := Submodule.finiteDimensional_of_le hZW
    have hZst : IsStableUnderOperators E Z := by
      rintro a b _ ⟨y, hy, rfl⟩
      exact ⟨restrictToStableSubmodule E W hW a b y, hP2 a b y hy, rfl⟩
    have hZne : Z ≠ ⊥ := by
      intro h
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have h5 : (y : V) ∈ Z := ⟨y, hy, rfl⟩
      rw [h] at h5
      exact hy0 (Subtype.ext h5)
    obtain ⟨mu, v, hvZ, hhw⟩ := v2rep_exists_hwv E hR Z hZst (hZW.trans hw) hZne
    obtain ⟨y, hy, rfl⟩ := hvZ
    have h1 : (y : V) ∈ W' :=
      Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨1, Submonoid.one_mem _, y, y.2, hhw, rfl⟩)
    have h3 : y ∈ (W'.comap W.subtype) ⊓ P2 := ⟨h1, hy⟩
    rw [hcompl.inf_eq_bot] at h3
    have h4 : y = 0 := h3
    exact hhw.1 (by rw [h4]; rfl)
  have htop : W'.comap W.subtype = ⊤ := by
    have := hcompl.sup_eq_top
    rwa [hbot, sup_bot_eq] at this
  intro x hx
  have : (⟨x, hx⟩ : W) ∈ W'.comap W.subtype := by rw [htop]; exact Submodule.mem_top
  exact this

end Formalism.MainNotions.G.GLWeightTheory
end
end

