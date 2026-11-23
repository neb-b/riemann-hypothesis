module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0008

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreSt
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

def prFib (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (w : Fin (D + 1) → ℂ) : Set (Ix κ → ℂ) :=
  {z | z ∈ pts (coordIdeal ℤ x) ∧ ∀ k, z (e k) = w k}

theorem exists_proj_ne_zero {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e)
    {z : Ix κ → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) : ∃ k, z (e k) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h; push Not at h; exact hz.1 (funext h)
  obtain ⟨q, hqm, hq⟩ := hfr.integral i
  have hg : ∀ j, ∃ g, coneMap ℤ (x ∘ e) g = ((q.coeff j : coneRing ℤ (x ∘ e)) : Polynomial Ω) :=
    fun j => (q.coeff j).2
  choose g hg using hg
  set n := q.natDegree
  let Q : MvPolynomial (Ix κ) ℤ := ∑ j ∈ Finset.range (n + 1), rename e (g j) * X i ^ j
  have hQ : Q ∈ coordIdeal ℤ x := by
    rw [coordIdeal, RingHom.mem_ker]
    rw [Polynomial.eval₂_eq_sum_range] at hq
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Q, map_sum, map_mul, map_pow, Fib.coneMap_rename, hg]
    convert hq using 2
    simp [coneMap]
  have hz0 := Fib.coneMap_eq_zero_of_mem_pts (coordIdeal_isHomogIdeal ℤ x) hz hQ
  have hze : z ∘ e = 0 := funext hcon
  have hcn : constantCoeff (g n) = 1 := by
    have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) (hg n)
    simp only [coeff_coneMap, homogeneousComponent_zero, aeval_C] at h1
    rw [hqm.coeff_natDegree] at h1
    simp at h1
    exact_mod_cast h1
  have h2 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) hz0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Q, map_sum, map_mul, map_pow, Fib.coneMap_rename, hze] at h2
  have h3 : ∀ j, coneMap ℤ (0 : Fin (D + 1) → ℂ) (g j) =
      Polynomial.C ((constantCoeff (g j) : ℤ) : ℂ) := by
    intro j
    simp [coneMap]
  have hX : coneMap ℤ z (X i) = Polynomial.C (z i) * Polynomial.X := by simp [coneMap]
  simp only [h3, hX, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at h2
  rw [Finset.sum_eq_single n] at h2
  · rw [mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
      if_pos rfl, hcn] at h2
    simp at h2
    exact hi h2.1
  · intro j _ hj
    rw [mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
      if_neg (Ne.symm hj)]
  · intro h; simp at h

def IsDiscr (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (Δ : MvPolynomial (Fin (D + 1)) ℂ) : Prop :=
  Δ ≠ 0 ∧ ∀ w, eval w Δ ≠ 0 →
    (prFib x e w).Finite ∧ (prFib x e w).ncard = projDeg x e ∧
    (∀ z ∈ prFib x e w, ∃ (U : Set (Fin (D + 1) → ℂ)) (γ : (Fin (D + 1) → ℂ) → Ix κ → ℂ),
      IsOpen U ∧ w ∈ U ∧ DifferentiableOn ℂ γ U ∧ γ w = z ∧ ∀ w' ∈ U, γ w' ∈ prFib x e w') ∧
    ∀ (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) (g : MvPolynomial (Fin (D + 1)) ℤ),
      f.IsHomogeneous n → g.IsHomogeneous n → aeval (x ∘ e) g = secTrace x e n (aeval x f) →
      eval w (map (Int.castRingHom ℂ) g) = ∑ᶠ z ∈ prFib x e w, eval z (map (Int.castRingHom ℂ) f)

theorem exists_isDiscr {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) :
    ∃ Δ, IsDiscr x e Δ := by
  classical
  obtain ⟨G, hdeg, hTr, hsc⟩ := Fib.exists_gen x e hfr
  have hy0 : (x ∘ e) 0 ≠ 0 := Fib.coord_ne_zero _ hfr.free 0
  have hx0 : x (e 0) ≠ 0 := hy0
  let Δ0 : MvPolynomial (Fin (D + 1)) ℤ :=
    X 0 * Fib.homog 0 G.dd.totalDegree G.dd * Fib.homog 0 G.cc.totalDegree G.cc
  have hevΔ : ∀ w : Fin (D + 1) → ℂ, w 0 ≠ 0 →
      eval w (map (Int.castRingHom ℂ) Δ0) = w 0 * (w 0 ^ G.dd.totalDegree * Fib.deh w 0 G.dd) *
        (w 0 ^ G.cc.totalDegree * Fib.deh w 0 G.cc) := by
    intro w hw0
    rw [eval_map]
    simp only [Δ0, eval₂_mul, eval₂_X, Fib.eval₂_homog w 0 hw0 _ le_rfl]
  have hgood : ∀ w : Fin (D + 1) → ℂ, eval w (map (Int.castRingHom ℂ) Δ0) ≠ 0 → G.Good w := by
    intro w hw
    have hw0 : w 0 ≠ 0 := by
      intro h0
      apply hw
      rw [eval_map]
      simp [Δ0, h0]
    rw [hevΔ w hw0] at hw
    refine ⟨hw0, fun m hm => ?_, fun h0 => hw (by rw [h0]; ring), fun h0 => hw (by rw [h0]; ring)⟩
    exact Fib.deh_eq_zero_of_deh_eq_zero (x ∘ e) w 0 hy0 hw0
      (fun f hf => by rw [hfr.free, Ideal.mem_bot] at hf; simp [hf]) hm
  refine ⟨map (Int.castRingHom ℂ) Δ0, ?_, fun w hw => ?_⟩
  · intro h0
    have h1 : Δ0 = 0 :=
      map_injective _ (RingHom.injective_int (Int.castRingHom ℂ)) (by rw [h0, map_zero])
    have h2 : aeval (x ∘ e) Δ0 = (x ∘ e) 0 * ((x ∘ e) 0 ^ G.dd.totalDegree *
        Fib.deh (x ∘ e) 0 G.dd) * ((x ∘ e) 0 ^ G.cc.totalDegree * Fib.deh (x ∘ e) 0 G.cc) := by
      simp only [Δ0, aeval_def, algebraMap_int_eq, eval₂_mul, eval₂_X,
        Fib.eval₂_homog _ 0 hy0 _ le_rfl]
    rw [h1, map_zero] at h2
    exact (mul_ne_zero (mul_ne_zero hy0 (mul_ne_zero (pow_ne_zero _ hy0) G.dd_ne))
      (mul_ne_zero (pow_ne_zero _ hy0) G.cc_ne)) h2.symm
  have hgw := hgood w hw
  have hfib : prFib x e w = Fib.fib x e w := rfl
  refine ⟨hfib ▸ G.fib_finite hx0 hgw, by rw [hfib, G.fib_ncard hx0 hgw, hdeg], ?_, ?_⟩
  · intro z hz
    have hWo : IsOpen {w : Fin (D + 1) → ℂ | eval w (map (Int.castRingHom ℂ) Δ0) ≠ 0} :=
      isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const
    obtain ⟨U, γ, hU, hwU, hγ, hγw, hγf⟩ :=
      G.exists_section hx0 hWo (fun w' hw' => hgood w' hw') (w := w) hw (z := z) hz
    exact ⟨U, γ, hU, hwU, hγ, hγw, hγf⟩
  · intro n f g hf hg hfg
    have hdf : aeval x f = x (e 0) ^ n * Fib.deh x (e 0) f :=
      Fib.aeval_eq_pow_mul_deh x (e 0) hx0 hf
    have hdg : aeval (x ∘ e) g = (x ∘ e) 0 ^ n * Fib.deh (x ∘ e) 0 g :=
      Fib.aeval_eq_pow_mul_deh (x ∘ e) 0 hy0 hg
    have hT : Fib.deh (x ∘ e) 0 g = fnTrace x e (Fib.deh x (e 0) f) := by
      rw [hdg, secTrace, hdf, mul_div_cancel_left₀ _ (pow_ne_zero _ hx0)] at hfg
      exact mul_left_cancel₀ (pow_ne_zero _ hy0) hfg
    have htw := G.trace_w hgw (fnTrace x e) hTr hsc hT
    have hw0 := hgw.w0
    rw [hfib, G.finsum_fib hx0 hgw, eval_map, ← algebraMap_int_eq, ← aeval_def,
      Fib.aeval_eq_pow_mul_deh w 0 hw0 hg, htw, ← Multiset.sum_map_mul_left]
    congr 1
    refine Multiset.map_congr rfl fun ρ hρ => ?_
    have hρ' := (G.mem_roots).1 hρ
    rw [eval_map, ← aeval_def,
      Fib.aeval_eq_pow_mul_deh _ (e 0) (by rw [G.zOf_e hgw hρ' 0]; exact hw0) hf, G.zOf_e hgw hρ' 0]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SupportSubsetMonoBox
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem le_of_mem_support_mHom {a : K → ℕ} {f : MRing ι} (hf : f ∈ mHom ι a) {m : (Σ k, ι k) →₀ ℕ}
    (hm : m ∈ f.support) (p : Σ k, ι k) : m p ≤ a p.1 := by
  classical
  revert m
  induction hf using Submodule.span_induction with
  | mem s hs =>
    intro m hm
    rw [← hs m hm p.1]
    exact Finset.single_le_sum (f := fun i => m ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
    · exact hx h
    · exact hy h
  | smul c x _ hx =>
    intro m hm
    exact hx (MvPolynomial.support_smul hm)

theorem finite_monoBox (a : K → ℕ) :
    {m : (Σ k, ι k) →₀ ℕ | ∀ p, m p ≤ a p.1}.Finite := by
  have hfin : (Set.pi Set.univ fun p : (Σ k, ι k) => Set.Iic (a p.1)).Finite :=
    Set.Finite.pi fun p => Set.finite_Iic _
  refine (hfin.preimage (Finsupp.equivFunOnFinite.injective.injOn)).subset ?_
  intro m hm p _
  exact hm p

def monoBox (a : K → ℕ) : Finset ((Σ k, ι k) →₀ ℕ) := (finite_monoBox (ι := ι) a).toFinset

theorem support_subset_monoBox {a : K → ℕ} {f : MRing ι} (hf : f ∈ mHom ι a) :
    f.support ⊆ monoBox a := by
  intro m hm
  simp only [monoBox, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact fun p => le_of_mem_support_mHom hf hm p

theorem finite_mPiece (J : Ideal (MRing ι)) (a : K → ℕ) {p : ℕ} (hp : 0 < p)
    (hpJ : (p : MRing ι) ∈ J) : Finite (mPiece J a) := by
  classical
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  let g : (monoBox (ι := ι) a → Fin (q + 1)) → MRing ι ⧸ J := fun c =>
    Ideal.Quotient.mk J (∑ m : monoBox (ι := ι) a,
      MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (((c m : ℕ) : ℤ)))
  have hsub : (mPiece J a : Set (MRing ι ⧸ J)) ⊆ Set.range g := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
    have hq : (0 : ℤ) < ((q + 1 : ℕ) : ℤ) := by omega
    refine ⟨fun m => ⟨((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩
    · have h0 := Int.emod_nonneg (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) hq.ne'
      have h1 := Int.emod_lt_of_pos (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) hq
      omega
    · show Ideal.Quotient.mk J (∑ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ)) =
        Ideal.Quotient.mk J f
      rw [Ideal.Quotient.eq]
      have hf' : f = ∑ m : monoBox (ι := ι) a,
          MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) := by
        rw [Finset.sum_coe_sort (monoBox a) (fun m => MvPolynomial.monomial m (AddMonoidAlgebra.coeff f m))]
        conv_lhs => rw [MvPolynomial.as_sum f]
        refine Finset.sum_subset (support_subset_monoBox hf) (fun m _ hm => ?_)
        simp only [MvPolynomial.mem_support_iff, ne_eq, not_not] at hm
        simp [hm]
      have hP : ((q + 1 : ℕ) : MRing ι) ∈ J := hpJ
      have hdiff : ∀ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) -
          MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) ∈ J := by
        intro m
        have h0 := Int.emod_nonneg (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) hq.ne'
        rw [Int.toNat_of_nonneg h0, ← map_sub, Int.emod_def]
        have e : AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ) - ((q + 1 : ℕ) : ℤ) *
            (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ) / ((q + 1 : ℕ) : ℤ)) -
            AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ) =
            ((q + 1 : ℕ) : ℤ) * (-(AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ) / ((q + 1 : ℕ) : ℤ))) := by
          ring
        rw [e, ← MvPolynomial.C_mul_monomial, map_natCast]
        exact J.mul_mem_right _ hP
      have e2 : (∑ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ)) - f =
          ∑ m : monoBox (ι := ι) a, (MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ)) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) -
          MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (AddMonoidAlgebra.coeff f (m : (Σ k, ι k) →₀ ℕ))) := by
        rw [Finset.sum_sub_distrib, ← hf']
      rw [e2]
      exact Ideal.sum_mem _ fun m _ => hdiff m
  exact ((Set.finite_range g).subset hsub).to_subtype

theorem card_mPiece_pos (J : Ideal (MRing ι)) (a : K → ℕ) {p : ℕ} (hp : 0 < p)
    (hpJ : (p : MRing ι) ∈ J) : 0 < Nat.card (mPiece J a) := by
  haveI := finite_mPiece J a hp hpJ
  exact Nat.card_pos

theorem card_mPiece_irrel {q : Ideal (MRing ι)} {k : K} (hk : ∀ i, (X ⟨k, i⟩ : MRing ι) ∈ q)
    {a : K → ℕ} (ha : 0 < a k) : Nat.card (mPiece q a) = 1 := by
  classical
  have hmem : ∀ f ∈ mHom ι a, f ∈ q := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem s hs =>
      rw [MvPolynomial.as_sum s]
      refine Ideal.sum_mem _ fun m hm => ?_
      have hsum := hs m hm k
      obtain ⟨i, hi⟩ : ∃ i, 0 < m ⟨k, i⟩ := by
        by_contra hc
        push_neg at hc
        have h0 : ∑ i, m ⟨k, i⟩ = 0 := Finset.sum_eq_zero fun i _ => by have := hc i; omega
        omega
      have e : MvPolynomial.monomial m (AddMonoidAlgebra.coeff s m) =
          MvPolynomial.X ⟨k, i⟩ * MvPolynomial.monomial (m - Finsupp.single ⟨k, i⟩ 1) (AddMonoidAlgebra.coeff s m) := by
        rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
          add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hi)]
      rw [e]
      exact q.mul_mem_right _ (hk i)
    | zero => exact q.zero_mem
    | add x y _ _ hx hy => exact q.add_mem hx hy
    | smul c x _ hx => exact Submodule.smul_of_tower_mem q c hx
  have hzero : ∀ x : mPiece q a, x = 0 := by
    rintro ⟨x, hx⟩
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
    apply Subtype.ext
    show Ideal.Quotient.mk q f = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem f hf)
  haveI : Unique (mPiece q a) := ⟨⟨0⟩, hzero⟩
  exact Nat.card_unique

theorem card_mPiece_mono {J J' : Ideal (MRing ι)} (h : J ≤ J') (a : K → ℕ) [Finite (mPiece J a)] :
    Nat.card (mPiece J' a) ≤ Nat.card (mPiece J a) := by
  have hmap : ∀ x ∈ mPiece J a, Ideal.Quotient.factor h x ∈ mPiece J' a := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨g, hg, ?_⟩
    show Ideal.Quotient.mk J' g = Ideal.Quotient.factor h (Ideal.Quotient.mk J g)
    rw [Ideal.Quotient.factor_mk]
  refine Nat.card_le_card_of_surjective (fun x => ⟨Ideal.Quotient.factor h x, hmap x x.2⟩) ?_
  rintro ⟨y, hy⟩
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hy
  refine ⟨⟨Ideal.Quotient.mk J g, Submodule.mem_map.mpr ⟨g, hg, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  show Ideal.Quotient.factor h (Ideal.Quotient.mk J g) = Ideal.Quotient.mk J' g
  rw [Ideal.Quotient.factor_mk]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

