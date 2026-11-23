module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFibA
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

theorem fibSys_finite {W : Type*} [Fintype W] (r : W → ℕ) (H : W → MvPolynomial W ℂ)
    (hH : ∀ i, (H i).totalDegree < r i) :
    {w : W → ℂ | ∀ i, w i ^ r i = eval w (H i)}.Finite := by
  classical
  rcases isEmpty_or_nonempty W with hW | hW
  · exact Set.Subsingleton.finite fun x _ y _ => funext fun i => (IsEmpty.false i).elim
  obtain ⟨B, hB⟩ : ∃ B : Finset (W →₀ ℕ), ∀ u, u ∈ B ↔ ∀ i, u i < r i := by
    refine ⟨(Fintype.piFinset fun i => Finset.range (r i)).map
      Finsupp.equivFunOnFinite.symm.toEmbedding, fun u => ?_⟩
    rw [Finset.mem_map_equiv, Equiv.symm_symm, Fintype.mem_piFinset]
    simp [Finset.mem_range]
  obtain ⟨M, hMdef⟩ : ∃ M : Submodule ℂ (MvPolynomial W ℂ),
      M = Submodule.span ℂ ((fun b => monomial b (1 : ℂ)) '' (B : Set (W →₀ ℕ))) := ⟨_, rfl⟩
  have hmon : ∀ (n : ℕ) (u : W →₀ ℕ), u.degree ≤ n → ∀ a : ℂ, ∃ q ∈ M,
      ∀ w : W → ℂ, (∀ i, w i ^ r i = eval w (H i)) → eval w (monomial u a) = eval w q := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro u hu a
    by_cases hall : ∀ i, u i < r i
    · refine ⟨monomial u a, ?_, fun _ _ => rfl⟩
      have e : monomial u a = a • monomial u (1 : ℂ) := by rw [smul_monomial, smul_eq_mul, mul_one]
      rw [e, hMdef]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨u, (hB u).mpr hall, rfl⟩)
    · push_neg at hall
      obtain ⟨i, hi⟩ := hall
      have hle : Finsupp.single i (r i) ≤ u := Finsupp.single_le_iff.mpr hi
      obtain ⟨u', hu'⟩ : ∃ u', u = u' + Finsupp.single i (r i) :=
        ⟨u - Finsupp.single i (r i), (tsub_add_cancel_of_le hle).symm⟩
      have hdeg : u'.degree + r i = u.degree := by
        rw [hu', map_add (f := _), Finsupp.degree_single]
      have hsplit : ∀ w : W → ℂ, (∀ i, w i ^ r i = eval w (H i)) →
          eval w (monomial u a) = eval w (monomial u' a * H i) := by
        intro w hw
        rw [hu', show monomial (u' + Finsupp.single i (r i)) a =
          monomial u' a * monomial (Finsupp.single i (r i)) 1 by rw [monomial_mul, mul_one],
          map_mul, map_mul, ← X_pow_eq_monomial, map_pow, eval_X, hw i]
      have hsum : monomial u' a * H i =
          ∑ v ∈ (H i).support, monomial (u' + v) (a * AddMonoidAlgebra.coeff (H i) v) := by
        conv_lhs => rw [(H i).as_sum]
        rw [Finset.mul_sum]
        simp only [monomial_mul]
      have hterm : ∀ v ∈ (H i).support, ∃ q ∈ M, ∀ w : W → ℂ, (∀ i, w i ^ r i = eval w (H i)) →
          eval w (monomial (u' + v) (a * AddMonoidAlgebra.coeff (H i) v)) = eval w q := by
        intro v hv
        have hv' : v.degree ≤ (H i).totalDegree := le_totalDegree hv
        have hlt : (u' + v).degree < n := by
          rw [map_add (f := _)]
          have := hH i
          omega
        exact ih _ hlt _ le_rfl _
      choose q hqM hq using hterm
      refine ⟨∑ v ∈ (H i).support.attach, q v.1 v.2, Submodule.sum_mem _ fun v _ => hqM v.1 v.2, ?_⟩
      intro w hw
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsplit w hw, hsum, map_sum, map_sum]
      exact (Finset.sum_attach _ _).symm.trans (Finset.sum_congr rfl fun v _ => hq v.1 v.2 w hw)
  have hA : ∀ p : MvPolynomial W ℂ, ∃ q ∈ M, ∀ w : W → ℂ, (∀ i, w i ^ r i = eval w (H i)) →
      eval w p = eval w q := by
    intro p
    refine MvPolynomial.induction_on' p (fun u a => hmon _ u le_rfl a) (fun p q hp hq => ?_)
    obtain ⟨p', hp'M, hp'⟩ := hp
    obtain ⟨q', hq'M, hq'⟩ := hq
    exact ⟨p' + q', M.add_mem hp'M hq'M, fun w hw => by rw [map_add (f := _), map_add (f := _), hp' w hw, hq' w hw]⟩
  have hex : ∀ x y : W → ℂ, ∃ i, x ≠ y → x i ≠ y i := fun x y => by
    by_cases h : x = y
    · exact ⟨Classical.arbitrary W, fun h' => (h' h).elim⟩
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact ⟨i, fun _ => hi⟩
  choose idx hidx using hex
  by_contra hinf
  have hinf' : Set.Infinite {w : W → ℂ | ∀ i, w i ^ r i = eval w (H i)} := hinf
  obtain ⟨T, hTS, hTcard⟩ := hinf'.exists_subset_card_eq (B.card + 1)
  let Φ : (B → ℂ) →ₗ[ℂ] (T → ℂ) :=
    { toFun := fun c t => ∑ b : B, c b * eval (t : W → ℂ) (monomial (b : W →₀ ℕ) 1)
      map_add' := fun c c' => by
        funext t
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        funext t
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hΦ : ∀ c t, Φ c t = ∑ b : B, c b * eval (t : W → ℂ) (monomial (b : W →₀ ℕ) 1) :=
    fun _ _ => rfl
  have key : ∀ q ∈ M, ∃ c : B → ℂ, ∀ t : T, eval (t : W → ℂ) q = Φ c t := by
    intro q hq
    rw [hMdef] at hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      refine ⟨Pi.single ⟨b, hb⟩ 1, fun t => ?_⟩
      rw [hΦ, Finset.sum_eq_single ⟨b, hb⟩]
      · simp
      · intro b' _ hb'
        simp [Pi.single_apply, hb']
      · simp
    | zero => exact ⟨0, fun t => by simp [hΦ]⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', hc'⟩ := hy
      exact ⟨c + c', fun t => by rw [map_add (f := _), hc, hc', map_add (f := _)]; rfl⟩
    | smul a x _ hx =>
      obtain ⟨c, hc⟩ := hx
      exact ⟨a • c, fun t => by rw [MvPolynomial.smul_eval, hc, map_smul]; rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : (W → ℂ) → MvPolynomial W ℂ, ∀ x, L x = ∏ y ∈ T.erase x,
      (C ((x (idx x y) - y (idx x y))⁻¹) * (X (idx x y) - C (y (idx x y)))) := ⟨_, fun _ => rfl⟩
  have hLself : ∀ x, eval x (L x) = 1 := by
    intro x
    rw [hL, map_prod]
    refine Finset.prod_eq_one fun y hy => ?_
    have hne : x ≠ y := (Finset.ne_of_mem_erase hy).symm
    rw [map_mul, eval_C, map_sub, eval_X, eval_C, inv_mul_cancel₀ (sub_ne_zero.mpr (hidx x y hne))]
  have hLother : ∀ x, ∀ z ∈ T, z ≠ x → eval z (L x) = 0 := by
    intro x z hz hzx
    rw [hL, map_prod]
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hzx, hz⟩) ?_
    rw [map_mul, map_sub, eval_X, eval_C, eval_C, sub_self, mul_zero]
  have hsurj : Function.Surjective Φ := by
    intro f
    obtain ⟨f', hf'⟩ : ∃ f' : (W → ℂ) → ℂ, ∀ t : T, f' t = f t :=
      ⟨fun x => if h : x ∈ T then f ⟨x, h⟩ else 0, fun t => by simp [t.2]⟩
    obtain ⟨q, hqM, hq⟩ := hA (∑ x ∈ T, C (f' x) * L x)
    obtain ⟨c, hc⟩ := key q hqM
    refine ⟨c, funext fun t => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc t, ← hq t (hTS t.2), map_sum, Finset.sum_eq_single (t : W → ℂ)]
    · rw [map_mul, eval_C, hLself, mul_one, hf']
    · intro x _ hxt
      rw [map_mul, hLother x t t.2 (Ne.symm hxt), mul_zero]
    · intro h
      exact absurd t.2 h
  have h1 := LinearMap.finrank_range_le Φ
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe] at h1
  omega

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFibB
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]


variable (ι) in
def blkW : (Σ k, ι k) → (K → ℕ) := fun p => Pi.single p.1 1

theorem weight_blkW (β : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blkW ι) β k = ∑ i, β ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [blkW, Pi.single_apply]

theorem isWeightedHomogeneous_map_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) :
    IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) s) a := by
  intro d hd
  rw [coeff_map] at hd
  have hs' : d ∈ s.support := by
    rw [mem_support_iff]
    intro h0
    apply hd
    simp [h0]
  funext k
  rw [weight_blkW]
  exact hs d hs' k

theorem diag_prod (d : ℕ) : ∀ e : (Σ k, ι k) → ℕ, (∀ k, ∑ i, e ⟨k, i⟩ = d) →
    ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ d ∧
      ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ e p = eval (segre z) G := by
  induction d with
  | zero =>
    intro e he
    refine ⟨1, by simp, fun z => ?_⟩
    have h0 : ∀ p, e p = 0 := by
      intro p
      have := he p.1
      rw [Finset.sum_eq_zero_iff] at this
      exact this p.2 (Finset.mem_univ _)
    simp [h0]
  | succ d ih =>
    intro e he
    have hex : ∀ k, ∃ i, 0 < e ⟨k, i⟩ := by
      intro k
      by_contra hne
      push_neg at hne
      have h1 := he k
      rw [Finset.sum_eq_zero (fun i _ => Nat.le_zero.1 (hne i))] at h1
      omega
    choose i0 hi0 using hex
    classical
    let e' : (Σ k, ι k) → ℕ := fun p => if p.2 = i0 p.1 then e p - 1 else e p
    have hblk : ∀ k, ∑ i, e' ⟨k, i⟩ = d := by
      intro k
      have h1 := he k
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (i0 k))] at h1 ⊢
      have h2 : ∑ i ∈ Finset.univ.erase (i0 k), e' ⟨k, i⟩ = ∑ i ∈ Finset.univ.erase (i0 k), e ⟨k, i⟩ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ i0 k := Finset.ne_of_mem_erase hi
        simp [e', hne]
      rw [h2]
      have h3 : e' ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 := by simp [e']
      rw [h3]
      have := hi0 k
      omega
    obtain ⟨G', hG'deg, hG'⟩ := ih e' hblk
    refine ⟨X i0 * G', ?_, fun z => ?_⟩
    · calc (X i0 * G').totalDegree ≤ (X i0 : MvPolynomial ((k : K) → ι k) ℂ).totalDegree + G'.totalDegree :=
            totalDegree_mul _ _
        _ ≤ 1 + d := by rw [totalDegree_X]; omega
        _ = d + 1 := by ring
    · rw [eval_mul, eval_X, ← hG', segre, Fintype.prod_sigma, Fintype.prod_sigma, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (i0 k)),
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ (i0 k))]
      have h2 : ∏ i ∈ Finset.univ.erase (i0 k), z ⟨k, i⟩ ^ e' ⟨k, i⟩ =
          ∏ i ∈ Finset.univ.erase (i0 k), z ⟨k, i⟩ ^ e ⟨k, i⟩ := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hne : i ≠ i0 k := Finset.ne_of_mem_erase hi
        simp [e', hne]
      rw [h2]
      have h3 : e' ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 := by simp [e']
      rw [h3]
      have h4 : e ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 + 1 := by have := hi0 k; omega
      conv_lhs => rw [h4, pow_succ]
      ring

theorem diag_of_homog (d : ℕ) {f : MvPolynomial (Σ k, ι k) ℂ}
    (hf : IsWeightedHomogeneous (blkW ι) f (fun _ => d)) :
    ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ d ∧
      ∀ z : (Σ k, ι k) → ℂ, eval z f = eval (segre z) G := by
  classical
  have hG : ∀ m : (Σ k, ι k) →₀ ℕ, ∃ G : MvPolynomial ((k : K) → ι k) ℂ,
      m ∈ f.support → G.totalDegree ≤ d ∧ ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ m p = eval (segre z) G := by
    intro m
    by_cases hm : m ∈ f.support
    · have hw := hf (mem_support_iff.1 hm)
      obtain ⟨G, h1, h2⟩ := diag_prod d (fun p => m p) (fun k => by
        have := congrFun hw k
        rwa [weight_blkW] at this)
      exact ⟨G, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose Gf hGf using hG
  refine ⟨∑ m ∈ f.support, C (AddMonoidAlgebra.coeff f m) * Gf m, ?_, fun z => ?_⟩
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (hGf m hm).1
  · rw [eval_eq', map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval_mul, eval_C, (hGf m hm).2 z]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem comp_mul_homog {σ : Type*} {M : Type*} [AddCancelCommMonoid M] [DecidableEq M] {w : σ → M}
    {ψ : MvPolynomial σ ℂ} {δ : M} (hψ : IsWeightedHomogeneous w ψ δ) (g : MvPolynomial σ ℂ) (n : M) :
    weightedHomogeneousComponent w (n + δ) (g * ψ) = weightedHomogeneousComponent w n g * ψ := by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hx
  · refine Finset.sum_congr rfl fun ab hab => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hb : AddMonoidAlgebra.coeff ψ ab.2 = 0
    · simp [hb]
    · have hwb := hψ hb
      have hsum : Finsupp.weight w ab.1 + Finsupp.weight w ab.2 = Finsupp.weight w x := by
        have hab' : ab.1 + ab.2 = x := by simpa using hab
        rw [← map_add (f := _), hab']
      have ha : Finsupp.weight w ab.1 = n := by
        rw [hwb, hx] at hsum
        exact add_right_cancel hsum
      rw [if_pos ha]
  · symm
    refine Finset.sum_eq_zero fun ab hab => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with ha
    · by_cases hb : AddMonoidAlgebra.coeff ψ ab.2 = 0
      · simp [hb]
      · exfalso
        apply hx
        have hwb := hψ hb
        have hab' : ab.1 + ab.2 = x := by simpa using hab
        rw [← hab', map_add (f := _), ha, hwb]
    · simp

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodG
section
namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def segQ (P : Ideal (MRing ι)) (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P :=
  Ideal.Quotient.mk _ (segMon i)

private lemma rename_inl_aeval_mul_prod_X_inr_pow_eq_of_support {r : ℕ} {S : Type} [Fintype S] (c : S → ℕ)
    (H : MvPolynomial (Fin r ⊕ S) ℚ) (hc : ∀ m ∈ H.support, ∀ s, m (Sum.inr s) = c s) :
    rename Sum.inl (aeval (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1) H) *
      ∏ s, (X (Sum.inr s) : MvPolynomial (Fin r ⊕ S) ℚ) ^ c s = H := by
  classical
  conv_rhs => rw [H.as_sum]
  conv_lhs => rw [H.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, aeval_C, aeval_X, Sum.elim_inl, Sum.elim_inr,
    Pi.one_apply, one_pow, Finset.prod_const_one, mul_one, rename_C, rename_X, algebraMap_eq,
    hc m hm, mul_assoc]

private lemma aeval_sumElim_one_eq_aeval_aeval_sumElim_X_one {r : ℕ} {S : Type} {B : Type*} [CommRing B] [Algebra ℚ B]
    (a : Fin r → B) (H : MvPolynomial (Fin r ⊕ S) ℚ) :
    aeval (Sum.elim a 1) H = aeval a (aeval (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1) H) := by
  have hf : (fun i : Fin r ⊕ S => aeval a (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1 i)) =
      Sum.elim a (1 : S → B) := by
    funext i
    cases i <;> simp
  rw [← AlgHom.comp_apply, comp_aeval, hf]

theorem algebraicIndependent_sumElim (P : Ideal (MRing ι)) (hP : P.IsPrime) (hH : IsHorizontal P)
    (hhom : IsMultiHomogIdeal P) (k0 : K) (i0 : (k : K) → ι k)
    (hi0 : ∀ k, (X ⟨k, i0 k⟩ : MRing ι) ∉ P) {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℚ)
    (hind : AlgebraicIndependent ℚ (forms (segQ P) L)) :
    AlgebraicIndependent ℚ (Sum.elim (forms (segQ P) L)
      (fun k' : {k // k ≠ k0} => Ideal.Quotient.mk (qIdeal P) (X ⟨k'.1, i0 k'.1⟩))) := by
  classical
  have : IsDomain (MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P) := isDomain_qQuot P hP hH
  set b : {k // k ≠ k0} → MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P :=
    fun k' => Ideal.Quotient.mk (qIdeal P) (X ⟨k'.1, i0 k'.1⟩) with hbdef
  let yt : Fin r ⊕ {k // k ≠ k0} → MvPolynomial (Σ k, ι k) ℚ :=
    Sum.elim (fun j => ∑ t, L j t • segMon t) (fun k' => X ⟨k'.1, i0 k'.1⟩)
  have hyt : (fun e => Ideal.Quotient.mkₐ ℚ (qIdeal P) (yt e)) = Sum.elim (forms (segQ P) L) b := by
    funext e
    cases e with
    | inl j => simp [yt, forms, segQ, map_sum, Ideal.Quotient.mkₐ_eq_mk]
    | inr k' => simp [yt, b, Ideal.Quotient.mkₐ_eq_mk]
  have hhomY : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (sWt k0 r e) := by
    rintro (j | k')
    · have hmem : (∑ t, L j t • segMon t) ∈
          weightedHomogeneousSubmodule ℚ (blkWt (ι := ι)) oneK :=
        Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (segMon_isWeightedHomogeneous t)
      exact hmem
    · exact isWeightedHomogeneous_X ℚ (blkWt (ι := ι)) ⟨k'.1, i0 k'.1⟩
  have hb : ∀ k', b k' ≠ 0 := by
    intro k' h
    rw [hbdef, Ideal.Quotient.eq_zero_iff_mem] at h
    exact hi0 k'.1 (mem_of_qmap_mem_qIdeal P hP hH (by simpa using h))
  have hev : ∀ G, aeval (Sum.elim (forms (segQ P) L) b) G =
      Ideal.Quotient.mk (qIdeal P) (aeval (R := ℚ) yt G) := by
    intro G
    rw [← hyt, ← comp_aeval, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [algebraicIndependent_iff]
  intro H hH0
  have hmem : aeval (R := ℚ) yt H ∈ qIdeal P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hev]
    exact hH0
  have key : ∀ δ, weightedHomogeneousComponent (sWt k0 r) δ H = 0 := by
    intro δ
    have hHd : IsWeightedHomogeneous (sWt k0 r) (weightedHomogeneousComponent (sWt k0 r) δ H) δ :=
      weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hcomp := weightedHomogeneousComponent_mem_of_mem ℚ (blkWt (ι := ι))
      (qIdeal_isHomogeneous P hhom) hmem δ
    rw [component_aeval (sWt k0 r) yt hhomY H δ] at hcomp
    have h0 : aeval (Sum.elim (forms (segQ P) L) b) (weightedHomogeneousComponent (sWt k0 r) δ H) = 0 := by
      rw [hev, Ideal.Quotient.eq_zero_iff_mem]
      exact hcomp
    by_contra hne
    obtain ⟨n0, hn0⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hne)
    rw [aeval_sumElim_factor k0 hHd hn0] at h0
    have hprod : (∏ k', b k' ^ n0 (Sum.inr k')) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k' _ => pow_ne_zero _ (hb k')
    have h1 := (mul_eq_zero.mp h0).resolve_left hprod
    rw [aeval_sumElim_one_eq_aeval_aeval_sumElim_X_one] at h1
    have h2 := algebraicIndependent_iff.mp hind _ h1
    apply hne
    rw [← rename_inl_aeval_mul_prod_X_inr_pow_eq_of_support (fun s => n0 (Sum.inr s))
      (weightedHomogeneousComponent (sWt k0 r) δ H) ?_, h2, map_zero, zero_mul]
    intro m hm s
    exact inr_eq_of_weight_eq k0 ((hHd (mem_support_iff.mp hm)).trans
      (hHd (mem_support_iff.mp hn0)).symm) s
  ext n
  have := congrArg (AddMonoidAlgebra.coeff · n) (key (Finsupp.weight (sWt k0 r) n))
  rw [coeff_weightedHomogeneousComponent, if_pos rfl] at this
  simpa using this

theorem forms_not_algebraicIndependent (P : Ideal (MRing ι)) (e : ℕ) (hP : IsArithVar P (e + 1))
    {r : ℕ} (hr : e + 1 < r) (L : Fin r → ((k : K) → ι k) → ℚ) :
    ¬ AlgebraicIndependent ℚ (forms (segQ P) L) := by
  classical
  intro hind
  obtain ⟨hne, ⟨hprime, hhom, hrel⟩, hH, hdim⟩ := hP
  obtain ⟨k0⟩ := hne
  choose i0 hi0 using hrel
  have hall := algebraicIndependent_sumElim P hprime hH hhom k0 i0 hi0 L hind
  set n := Fintype.card (Fin r ⊕ {k // k ≠ k0})
  have hall' := hall.comp _ (Fintype.equivFin (Fin r ⊕ {k // k ≠ k0})).symm.injective
  have hle := succ_le_ringKrullDim_of_algebraicIndependent P hprime hH _ hall'
  rw [hdim] at hle
  have hle' : n + 1 ≤ e + 1 + Fintype.card K := by exact_mod_cast hle
  have hcard : n + 1 = r + Fintype.card K := by
    have h1 : Fintype.card {k // k ≠ k0} = Fintype.card K - 1 := by
      simp [Fintype.card_subtype_compl]
    have h2 : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨k0⟩
    simp only [n, Fintype.card_sum, Fintype.card_fin, h1]
    omega
  omega

end

end ReciprocityTheory.ChartRestriction.G.Geo
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHost
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter NumberField

section Host

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def LiesOver {F : Type*} [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (sg : F →+* ℂ)
    (z : (Σ k, ι k) → ℂ) : Prop :=
  ∀ (d : K → ℕ) (g h : MRing ι) (θ : F), IsMultiHomog g d → IsMultiHomog h d →
    aeval y g = algebraMap F Ω θ * aeval y h →
    eval z (map (Int.castRingHom ℂ) g) = sg θ * eval z (map (Int.castRingHom ℂ) h)

end Host

def ArithmeticHilbertSamuelUpperBoundNumberField : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (Λ : (F →+* ℂ) → ℝ) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (A.a = fun k => (a k : ℤ)) → P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A →
    IsConjInvariantH A → (∀ sg, 0 < Λ sg) → (∀ sg, Λ (ComplexEmbedding.conjugate sg) = Λ sg) →
    ∑ sg, Real.log (Λ sg) ≤ 0 →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      ∀ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) → ‖∏ p, z p ^ μ p‖ ≤ Λ sg * A.h z) →
    limsup (fun τ : ℕ =>
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ /
          ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A)

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

