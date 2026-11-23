module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import Lemmata.GeneralBFactBis.Imports
public import Lemmata.FirstBlockLemmaB.Imports

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section CycBlocks

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

def cycBlockWt [DecidableEq K] (k : K) : (Σ k, ι k) → ℕ := fun p => if p.1 = k then 1 else 0

theorem weight_cycBlockWt [DecidableEq K] (k : K) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (cycBlockWt (ι := ι) k) m = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [cycBlockWt]
  · intro b _ hb
    simp [cycBlockWt, hb]
  · simp

theorem isWeightedHomogeneous_cycBlockWt [DecidableEq K] {s : MRingOver R ι} {a : K → ℕ}
    (h : IsMultiHomog s a) (k : K) : IsWeightedHomogeneous (cycBlockWt (ι := ι) k) s (a k) := by
  intro d hd
  rw [weight_cycBlockWt]
  exact h d (mem_support_iff.mpr hd) k

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem cyc_isHomogeneous_of_isMultiHomogIdeal [DecidableEq K] {P : Ideal (MRingOver R ι)}
    (h : IsMultiHomogIdeal P) (k : K) :
    P.IsHomogeneous (weightedHomogeneousSubmodule R (cycBlockWt (ι := ι) k)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx => ?_
  obtain ⟨a, ha⟩ := hS x hx
  exact ⟨a k, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_cycBlockWt ha k)⟩

theorem cyc_isHomogeneous_of_mem_minimalPrimes {A : Type*} [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] {I W : Ideal A} (hI : I.IsHomogeneous 𝒜)
    (hW : W ∈ I.minimalPrimes) : W.IsHomogeneous 𝒜 := by
  have hWp : W.IsPrime := hW.1.1
  have h1 : (W.homogeneousCore 𝒜).toIdeal.IsPrime := hWp.homogeneousCore
  have h2 : I ≤ (W.homogeneousCore 𝒜).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  have h3 := hW.2 ⟨h1, h2⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
  have e : (W.homogeneousCore 𝒜).toIdeal = W :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _) h3
  exact e ▸ (W.homogeneousCore 𝒜).isHomogeneous

theorem cyc_exists_blockComponent [DecidableEq K] {W : Ideal (MRingOver R ι)}
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule R (cycBlockWt (ι := ι) k)))
    (a : K → ℕ) (T : Finset K) {f : MRingOver R ι} (hf : f ∈ W) :
    ∃ g ∈ W, ∀ m, AddMonoidAlgebra.coeff g m = if (∀ k ∈ T, ∑ i, m ⟨k, i⟩ = a k) then AddMonoidAlgebra.coeff f m else 0 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨f, hf, fun m => by simp⟩
  | @insert k T hk ih =>
    obtain ⟨g, hgW, hg⟩ := ih
    refine ⟨weightedHomogeneousComponent (cycBlockWt k) (a k) g,
      weightedHomogeneousComponent_mem_of_mem R (cycBlockWt k) (hW k) hgW (a k), fun m => ?_⟩
    rw [coeff_weightedHomogeneousComponent, weight_cycBlockWt, hg]
    by_cases h1 : ∑ i, m ⟨k, i⟩ = a k <;> by_cases h2 : ∀ k' ∈ T, ∑ i, m ⟨k', i⟩ = a k' <;>
      simp [h1, h2]

theorem cyc_isMultiHomogIdeal_of_isHomogeneous [DecidableEq K] {W : Ideal (MRingOver R ι)}
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule R (cycBlockWt (ι := ι) k))) :
    IsMultiHomogIdeal W := by
  refine ⟨{f | f ∈ W ∧ ∃ a, IsMultiHomog f a}, fun f hf => hf.2, le_antisymm (fun f hf => ?_)
    (Ideal.span_le.mpr fun f hf => hf.1)⟩
  choose g hgW hg using fun a : K → ℕ => cyc_exists_blockComponent hW a Finset.univ hf
  have hsum : f = ∑ a ∈ f.support.image (fun m k => ∑ i, m ⟨k, i⟩), g a := by
    ext m
    rw [coeff_sum]
    have e : ∀ a : K → ℕ,
        AddMonoidAlgebra.coeff (g a) m = if (fun k => ∑ i, m ⟨k, i⟩) = a then AddMonoidAlgebra.coeff f m else 0 := by
      intro a
      rw [hg a]
      by_cases h : (fun k => ∑ i, m ⟨k, i⟩) = a
      · subst h
        simp
      · rw [if_neg h, if_neg]
        intro h'
        exact h (funext fun k => h' k (Finset.mem_univ k))
    simp_rw [e]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · by_contra hne
      exact hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))
  rw [hsum]
  refine Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨hgW a, a, fun m hm k => ?_⟩
  rw [mem_support_iff, hg a] at hm
  by_contra hk
  exact hm (if_neg fun h => hk (h k (Finset.mem_univ k)))

theorem cyc_isMultiHomogIdeal_of_mem_minimalPrimes {P W : Ideal (MRingOver R ι)} {s : MRingOver R ι}
    {a : K → ℕ} (hP : IsMultiHomogIdeal P) (hs : IsMultiHomog s a)
    (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) : IsMultiHomogIdeal W := by
  classical
  refine cyc_isMultiHomogIdeal_of_isHomogeneous fun k => cyc_isHomogeneous_of_mem_minimalPrimes _
    ((cyc_isHomogeneous_of_isMultiHomogIdeal hP k).sup (Ideal.homogeneous_span _ _ ?_)) hW
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨a k, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_cycBlockWt hs k)⟩

end CycBlocks

section CycDim

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

theorem cyc_withBot_eq_of_add_one {x : WithBot ℕ∞} {m : ℕ} (h : x + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    x = (m : WithBot ℕ∞) := by
  first | exact Bl.general_b_fact_bis.goal1 .. | (apply Bl.general_b_fact_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis.goal1 <;> assumption)

theorem cyc_dim_quot_minimal_add_one {V W : Ideal (MRingOver F ι)} [hVp : V.IsPrime]
    {f : MRingOver F ι} (hf : f ∉ V) (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes)
    (hfin : ringKrullDim (MRingOver F ι ⧸ V) ≠ ⊤) :
    ringKrullDim (MRingOver F ι ⧸ W) + 1 = ringKrullDim (MRingOver F ι ⧸ V) := by
  have hPW : V ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hq : W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk V f} = (Ideal.span {f}).map (Ideal.Quotient.mk V) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]
    exact ⟨W, hW, rfl⟩
  have : (W.map (Ideal.Quotient.mk V)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk V f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hh : (W.map (Ideal.Quotient.mk V)).height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h0
    have : Ideal.Quotient.mk V f ∈ W.map (Ideal.Quotient.mk V) := Ideal.mem_map_of_mem _ hfW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hf this
  have : IsDomain (MRingOver F ι ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType F (MRingOver F ι ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F V)
      (Ideal.Quotient.mkₐ_surjective F V)
  have : IsNoetherianRing (MRingOver F ι ⧸ V) := Algebra.FiniteType.isNoetherianRing F _
  have : FiniteRingKrullDim (MRingOver F ι ⧸ V) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h => by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MRingOver F ι ⧸ V)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := DimF.exists_height_of_isMaximal_of_field F (MRingOver F ι ⧸ V)
  have key := DimF.dim_quot_add_height (A := MRingOver F ι ⧸ V)
    (fun M N hM hN => (hs M hM).trans (hs N hN).symm) (W.map (Ideal.Quotient.mk V))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)] at key
  exact_mod_cast key

end CycDim

section CycChart

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

theorem aeval_blockScale {A : Type*} [CommRing A] [Algebra F A] {g : MRingOver F ι} {a : K → ℕ}
    (hg : IsMultiHomog g a) (c : K → A) (z : (Σ k, ι k) → A) :
    aeval (fun p => c p.1 * z p) g = (∏ k, c k ^ a k) * aeval z g := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h1 : ∏ p, (c p.1 * z p) ^ d p = (∏ p, c p.1 ^ d p) * ∏ p, z p ^ d p := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [mul_pow]
  have h2 : ∏ p : (Σ k, ι k), c p.1 ^ d p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg d hd k]
  rw [h1, h2]
  ring

theorem aeval_blockScale_eq_zero {A : Type*} [CommRing A] [Algebra F A] {V : Ideal (MRingOver F ι)}
    (hV : IsMultiHomogIdeal V) (c : K → A) (θ : MRingOver F ι →ₐ[F] A) (hθ : ∀ g ∈ V, θ g = 0)
    {g : MRingOver F ι} (hg : g ∈ V) : aeval (fun p => c p.1 * θ (X p)) g = 0 := by
  have e : (aeval fun p => θ (X p) : MRingOver F ι →ₐ[F] A) = θ :=
    MvPolynomial.algHom_ext fun p => aeval_X _ _
  obtain ⟨S, hS, rfl⟩ := hV
  have h : Ideal.span S ≤ RingHom.ker (aeval (fun p => c p.1 * θ (X p)) : MRingOver F ι →ₐ[F] A) := by
    refine Ideal.span_le.mpr fun f hfS => ?_
    obtain ⟨a, ha⟩ := hS f hfS
    rw [SetLike.mem_coe, RingHom.mem_ker, aeval_blockScale ha, DFunLike.congr_fun e f,
      hθ f (Ideal.subset_span hfS), mul_zero]
  exact RingHom.mem_ker.mp (h hg)

theorem cyc_dim_add_one_le {R : Type*} [CommRing R] {P Q : Ideal R} [P.IsPrime] (hPQ : P ≤ Q)
    {x : R} (hxQ : x ∈ Q) (hxP : x ∉ P) : ringKrullDim (R ⧸ Q) + 1 ≤ ringKrullDim (R ⧸ P) := by
  first | exact Bl.FirstBlockLemmaB.goal1 .. | (apply Bl.FirstBlockLemmaB.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaB.goal1 <;> assumption)

theorem mk_chartIdeal_X_self (V : Ideal (MRingOver F ι)) (j : ∀ k, ι k) (k : K) :
    Ideal.Quotient.mk (chartIdeal V j) (X ⟨k, j k⟩) = 1 := by
  rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)

end CycChart

end ReciprocityTheory.ChartRestriction.G.AI.I1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

theorem isMultiHomog_mul {f g : MRingOver F ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem isMultiHomog_one : IsMultiHomog (1 : MRingOver F ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

open Classical in
theorem isMultiHomog_X (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver F ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

theorem isMultiHomog_pow {f : MRingOver F ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (isMultiHomog_one (F := F) (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul ih hf

open Classical in
theorem isMultiHomog_coordProd (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver F ι) ^ d k) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRingOver F ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (isMultiHomog_one (F := F) (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X k (c k)) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

theorem coordProd_not_mem {V : Ideal (MRingOver F ι)} (hV : V.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRingOver F ι) ∉ V) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRingOver F ι) ^ d k) ∉ V := by
  intro h
  obtain ⟨k, -, hk⟩ := (hV.prod_mem_iff).mp h
  exact hc k (hV.mem_of_pow_mem _ hk)

theorem isMultiHomog_zero (a : K → ℕ) : IsMultiHomog (0 : MRingOver F ι) a := by
  intro m hm
  simp at hm

theorem isMultiHomog_add {f g : MRingOver F ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_sum {β : Type*} (s : Finset β) (f : β → MRingOver F ι) {a : K → ℕ}
    (h : ∀ b ∈ s, IsMultiHomog (f b) a) : IsMultiHomog (∑ b ∈ s, f b) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_zero (F := F) (ι := ι) a
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    exact isMultiHomog_add (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

theorem isMultiHomog_prod {β : Type*} (s : Finset β) (f : β → MRingOver F ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_one (F := F) (ι := ι)
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact isMultiHomog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

theorem exists_form_avoid (S : Set (Ideal (MRingOver F ι))) (hS : S.Finite)
    (hS' : ∀ W ∈ S, IsMultiProjPrime W) :
    ∃ d₀ : K → ℕ, ∀ d : K → ℕ, d₀ ≤ d →
      ∃ f : MRingOver F ι, IsMultiHomog f d ∧ ∀ W ∈ S, f ∉ W := by
  classical
  set T : Finset (Ideal (MRingOver F ι)) :=
    hS.toFinset.filter (fun W => ∀ W' ∈ S, W ≤ W' → W' = W) with hT
  have hTS : ∀ W ∈ T, W ∈ S := fun W hW => hS.mem_toFinset.mp (Finset.mem_filter.mp hW).1
  have hTmax : ∀ W ∈ T, ∀ W' ∈ S, W ≤ W' → W' = W := fun W hW => (Finset.mem_filter.mp hW).2
  have hle : ∀ W ∈ S, ∃ W' ∈ T, W ≤ W' := by
    intro W hW
    obtain ⟨W', hWW', hW'⟩ := hS.exists_le_maximal hW
    exact ⟨W', Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hW'.prop,
      fun W'' hW'' h => le_antisymm (hW'.2 hW'' h) h⟩, hWW'⟩
  have hgen : ∀ W ∈ T, ∀ W' ∈ T, W' ≠ W →
      ∃ g : MRingOver F ι, ∃ a : K → ℕ, IsMultiHomog g a ∧ g ∈ W' ∧ g ∉ W := by
    intro W hW W' hW' hne
    obtain ⟨S', hS'h, hS'eq⟩ := (hS' W' (hTS W' hW')).2.1
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    apply hne
    refine (hTmax W' hW' W (hTS W hW) ?_).symm
    rw [hS'eq, Ideal.span_le]
    intro g hg
    obtain ⟨a, ha⟩ := hS'h g hg
    exact hc g a ha (hS'eq ▸ Ideal.subset_span hg)
  choose! gen degG hgenH hgenMem hgenNot using hgen
  set a : Ideal (MRingOver F ι) → MRingOver F ι := fun W => ∏ W' ∈ T.erase W, gen W W' with ha
  set δ : Ideal (MRingOver F ι) → K → ℕ := fun W => ∑ W' ∈ T.erase W, degG W W' with hδ
  have haH : ∀ W ∈ T, IsMultiHomog (a W) (δ W) := fun W hW =>
    isMultiHomog_prod _ _ _ fun W' hW' =>
      hgenH W hW W' (Finset.mem_of_mem_erase hW') (Finset.ne_of_mem_erase hW')
  have haNot : ∀ W ∈ T, a W ∉ W := by
    intro W hW h
    obtain ⟨W', hW', hg⟩ := ((hS' W (hTS W hW)).1.prod_mem_iff).mp h
    exact hgenNot W hW W' (Finset.mem_of_mem_erase hW') (Finset.ne_of_mem_erase hW') hg
  have haMem : ∀ W ∈ T, ∀ W'' ∈ T, W'' ≠ W → a W ∈ W'' := by
    intro W hW W'' hW'' hne
    have hmem : W'' ∈ T.erase W := Finset.mem_erase.mpr ⟨hne, hW''⟩
    show (∏ W' ∈ T.erase W, gen W W') ∈ W''
    rw [← Finset.mul_prod_erase _ _ hmem]
    exact Ideal.mul_mem_right _ _ (hgenMem W hW W'' hW'' hne)
  refine ⟨∑ W ∈ T, δ W, fun d hd => ?_⟩
  have hδd : ∀ W ∈ T, δ W ≤ d := fun W hW =>
    le_trans (Finset.single_le_sum (f := δ) (fun _ _ _ => Nat.zero_le _) hW) hd
  have hrel : ∀ W ∈ T, IsRelevant W := fun W hW => (hS' W (hTS W hW)).2.2
  set m : Ideal (MRingOver F ι) → MRingOver F ι := fun W =>
    if h : IsRelevant W then ∏ k, (X ⟨k, (h k).choose⟩ : MRingOver F ι) ^ (d k - δ W k) else 0
    with hm
  have hmH : ∀ W ∈ T, IsMultiHomog (m W) (d - δ W) := by
    intro W hW
    simp only [hm, dif_pos (hrel W hW)]
    exact isMultiHomog_coordProd _ _
  have hmNot : ∀ W ∈ T, m W ∉ W := by
    intro W hW
    simp only [hm, dif_pos (hrel W hW)]
    exact coordProd_not_mem (hS' W (hTS W hW)).1 _ (fun k => ((hrel W hW) k).choose_spec) _
  refine ⟨∑ W ∈ T, a W * m W, ?_, ?_⟩
  · apply isMultiHomog_sum
    intro W hW
    have := isMultiHomog_mul (haH W hW) (hmH W hW)
    rwa [add_tsub_cancel_of_le (hδd W hW)] at this
  · have key : ∀ W₀ ∈ T, (∑ W ∈ T, a W * m W) ∉ W₀ := by
      intro W₀ hW₀ h
      rw [← Finset.add_sum_erase _ _ hW₀] at h
      have hrest : (∑ W ∈ T.erase W₀, a W * m W) ∈ W₀ :=
        Ideal.sum_mem _ fun W hW => Ideal.mul_mem_right _ _
          (haMem W (Finset.mem_of_mem_erase hW) W₀ hW₀ (Finset.ne_of_mem_erase hW).symm)
      have h1 := (Ideal.add_mem_iff_left _ hrest).mp h
      rcases (hS' W₀ (hTS W₀ hW₀)).1.mem_or_mem h1 with h2 | h2
      · exact haNot W₀ hW₀ h2
      · exact hmNot W₀ hW₀ h2
    intro W hW h
    obtain ⟨W', hW', hle'⟩ := hle W hW
    exact key W' hW' (hle' h)

end ReciprocityTheory.ChartRestriction.G.AI.I1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Family

variable {K : Type*} [Fintype K] (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)]

def ExistsUniqueStatement : Prop :=
  ∃ I : IFamily F ι, IsFieldIntersection I ∧
    ∀ J : IFamily F ι, IsFieldIntersection J →
      ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ), IsProjVarF V n → J V n L = I V n L

def SymmStatement : Prop :=
  ∀ I : IFamily F ι, IsFieldIntersection I →
    ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)),
      IsProjVarF V n → I V n (L ∘ σ) = I V n L

def MultilinStatement : Prop :=
  ∀ I : IFamily F ι, IsFieldIntersection I →
    ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ) (j : Fin n) (a b : K → ℤ),
      IsProjVarF V n →
      I V n (Function.update L j (a + b)) = I V n (Function.update L j a) + I V n (Function.update L j b)

end Family

section Projection

variable {K : Type*} [Fintype K] {K' : Type*} [Fintype K'] (F : Type*) [Field F]
  (ι : K → Type*) [∀ k, Fintype (ι k)] (ι' : K' → Type*) [∀ k, Fintype (ι' k)]

def ProjContractStatement : Prop :=
  ∀ I' : IFamily F ι', IsFieldIntersection I' →
    ∀ (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (V' : Ideal (MRingOver F ι')) (e d : ℕ)
      (L : Fin e → K → ℤ), IsBlockMap κ v → IsProjVarF V' e → IsProjVarF (imageVar F v V') d →
      d < e → I' V' e (fun j => pullDeg κ (L j)) = 0

def ProjDegStatement : Prop :=
  ∀ (I : IFamily F ι) (I' : IFamily F ι'), IsFieldIntersection I → IsFieldIntersection I' →
    ∀ (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (V' : Ideal (MRingOver F ι')) (e : ℕ)
      (L : Fin e → K → ℤ) (i' : ∀ k', ι' k'), IsBlockMap κ v → IsProjVarF V' e →
      IsProjVarF (imageVar F v V') e → IsChart V' i' →
      I' V' e (fun j => pullDeg κ (L j)) = (fnDeg v V' i' : ℤ) * I (imageVar F v V') e L

end Projection

section Fibre

variable {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)]

def GeoNumStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (I : IFamily (ZMod p) ι), IsFieldIntersection I →
    ∀ (V : Ideal (MRing ι)) (n : ℕ) (a : Fin n → K → ℤ), IsMultiProjPrime V → (p : MRing ι) ∈ V →
      IsProjVarF (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
      geoNum n V a = I (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n a

end Fibre

section BaseField

variable {K : Type*} [Fintype K] (F F' : Type*) [Field F] [Field F'] [Algebra F F'] (ι : K → Type*)
  [∀ k, Fintype (ι k)]

end BaseField

section Positivity

variable {K : Type*} [Fintype K] (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)]

def PositivityStatement : Prop :=
  ∀ I : IFamily F ι, IsFieldIntersection I →
    ∀ (V : Ideal (MRingOver F ι)) (n : ℕ), IsProjVarF V n →
      (∀ L : Fin n → K → ℤ, (∀ j k, 0 ≤ L j k) → 0 ≤ I V n L) ∧ 0 < I V n (fun _ _ => 1)

end Positivity

section Inhabit

variable (F : Type*) [Field F]

end Inhabit

end ReciprocityTheory.ChartRestriction.G.AI.I1
end
end

