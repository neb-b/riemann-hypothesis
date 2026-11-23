module

public import ReciprocityTheory.DualLattices.Bundle0003
public import ReciprocityTheory.DualLattices.Bundle0001
public import Mathlib
public import Lemmata.MiscLemmasL.Imports

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.CharTableIsUnit
section
noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

def HopfOrder.ofSpan (S : Set (N → C)) (hlat : IsLat R (Submodule.span R S))
    (hint : S ⊆ (intFun (C := C) R N : Set (N → C))) (h1 : (1 : N → C) ∈ Submodule.span R S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ Submodule.span R S)
    (hcomul : ∀ a ∈ S, addPull R N a ∈ tensorSpan R (Submodule.span R S))
    (hanti : ∀ a ∈ S, (fun x => a (-x)) ∈ Submodule.span R S) : HopfOrder (C := C) R N where
  carrier := Submodule.span R S
  lat := hlat
  le_int := Submodule.span_le.mpr hint
  one_mem := h1
  mul_mem f g hf hg := by
    have h := Submodule.mul_mem_mul hf hg
    rw [Submodule.span_mul_span] at h
    refine (Submodule.span_le.mpr ?_) h
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact hmul a ha b hb
  comul f hf := by
    have : Submodule.span R S ≤
        (tensorSpan R (Submodule.span R S)).comap (addPull R N) :=
      Submodule.span_le.mpr hcomul
    exact this hf
  antipode f hf := by
    have : Submodule.span R S ≤
        (Submodule.span R S).comap (LinearMap.funLeft R C (fun x : N => -x)) :=
      Submodule.span_le.mpr hanti
    exact this hf

def constOrder : HopfOrder (C := C) R N :=
  HopfOrder.ofSpan (Set.range fun a : N => (Pi.single a (1 : C) : N → C))
    ⟨1, by simp, by
      congr 1
      ext f
      simp only [Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨a, by ext x; simp [Matrix.one_apply, Pi.single_apply]⟩
      · rintro ⟨a, rfl⟩; exact ⟨a, by ext x; simp [Matrix.one_apply, Pi.single_apply]⟩⟩
    (by
      rintro f ⟨a, rfl⟩ x
      by_cases h : x = a
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [h]⟩)
    (by
      have : (1 : N → C) = ∑ a, (Pi.single a (1 : C) : N → C) := by
        ext x; simp [Pi.single_apply]
      rw [this]
      exact Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨a, rfl⟩)
    (by
      rintro f ⟨a, rfl⟩ g ⟨b, rfl⟩
      have : (Pi.single a (1 : C) : N → C) * Pi.single b 1 =
          (if a = b then (1 : R) else 0) • (Pi.single a (1 : C) : N → C) := by
        ext x; by_cases h : a = b <;> by_cases hx : x = a <;> simp_all [Pi.single_apply]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    (by
      rintro f ⟨c, rfl⟩
      have : addPull R N (Pi.single c (1 : C) : N → C) =
          ∑ a, fun p : N × N => (Pi.single a (1 : C) : N → C) p.1 *
            (Pi.single (c - a) (1 : C) : N → C) p.2 := by
        ext ⟨x, y⟩
        simp only [addPull, LinearMap.funLeft_apply, Finset.sum_apply, Pi.single_apply,
          ite_mul, one_mul, zero_mul]
        by_cases h : x + y = c
        · have : y = c - x := by rw [← h]; abel
          simp [this]
        · have : ¬ y = c - x := by intro hy; apply h; rw [hy]; abel
          simp [h, this]
      rw [this]
      refine Submodule.sum_mem _ fun a _ => Submodule.subset_span ?_
      exact ⟨_, Submodule.subset_span ⟨a, rfl⟩, _, Submodule.subset_span ⟨c - a, rfl⟩, rfl⟩)
    (by
      rintro f ⟨a, rfl⟩
      refine Submodule.subset_span ⟨-a, ?_⟩
      ext x; simp [Pi.single_apply, neg_eq_iff_eq_neg])

def negChar (ψ : AddChar N C) : AddChar N C where
  toFun x := ψ (-x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by rw [neg_add, AddChar.map_add_eq_mul]

def multOrder (v : Valuation C NNReal) (hv : v.Integers R) (e : N ≃ AddChar N C)
    (hB : IsUnit (Matrix.of fun x j : N => e j x).det) : HopfOrder (C := C) R N :=
  HopfOrder.ofSpan (Set.range fun j : N => ((e j : AddChar N C) : N → C))
    ⟨_, hB, by simp [Matrix.of_apply]⟩
    (by
      rintro f ⟨j, rfl⟩ x
      refine hv.exists_of_le_one ?_
      have hn : (e j x) ^ Fintype.card N = 1 := by
        rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
      have : v (e j x) ^ Fintype.card N ≤ 1 := by rw [← map_pow, hn, map_one]
      exact (pow_le_one_iff_of_nonneg (by positivity) Fintype.card_ne_zero).mp this)
    (Submodule.subset_span ⟨e.symm 1, by simp⟩)
    (by
      rintro f ⟨a, rfl⟩ g ⟨b, rfl⟩
      exact Submodule.subset_span ⟨e.symm (e a * e b), by simp⟩)
    (by
      rintro f ⟨j, rfl⟩
      refine Submodule.subset_span ⟨_, Submodule.subset_span ⟨j, rfl⟩, _,
        Submodule.subset_span ⟨j, rfl⟩, ?_⟩
      ext p; simp [addPull, AddChar.map_add_eq_mul])
    (by
      rintro f ⟨j, rfl⟩
      exact Submodule.subset_span ⟨e.symm (negChar (e j)), by ext x; simp [negChar]⟩)

theorem charTable_isUnit (e : N ≃ AddChar N C) : IsUnit (Matrix.of fun x j : N => e j x).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
  have hinj : Function.Injective fun j : N => (e j).toMonoidHom := fun a b hab =>
    e.injective (DFunLike.ext _ _ fun x => DFunLike.congr_fun hab (Multiplicative.ofAdd x))
  exact (linearIndependent_monoidHom (Multiplicative N) C).comp _ hinj

def multOrder' (v : Valuation C NNReal) (hv : v.Integers R) (e : N ≃ AddChar N C) :
    HopfOrder (C := C) R N :=
  multOrder v hv e (charTable_isUnit e)

end ReciprocityTheory.PGsh.L2
end
end

-- bundled from ReciprocityTheory.DualLattices.CotangentSurjective
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable (p : ℕ) [Fact p.Prime] (g : ℕ)

abbrev Ix (g : ℕ) := Fin g ⊕ Fin g

abbrev TT := Ix g → ℤ_[p]

abbrev Nb := Ix g → ZMod p

def red (t : TT p g) : Nb p g := fun i => PadicInt.toZMod (t i)

def pair (E : Matrix (Ix g) (Ix g) ℤ_[p]) (s t : TT p g) : ℤ_[p] := s ⬝ᵥ (E *ᵥ t)

def sqIdeal {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {X : Type}
    (I : Submodule R (X → C)) : Submodule R (X → C) :=
  Submodule.span R {h | ∃ f ∈ I, ∃ f' ∈ I, h = f * f'}

abbrev LieDualModP (q : ℕ) (R : Type) [CommRing R] (n : ℕ) :=
  (Fin n → R) ⧸ (Ideal.span {(q : R)} • (⊤ : Submodule R (Fin n → R)))

def HasLen {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (M : Type) [AddCommGroup M] [Module R M] (x : NNReal) : Prop :=
  ∃ (m : ℕ) (c : Fin m → R), Nonempty (M ≃ₗ[R] ((i : Fin m) → R ⧸ Ideal.span {c i})) ∧
    ∏ i, v (algebraMap R C (c i)) = x

abbrev OmAA {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {X : Type}
    [AddCommGroup X] (M : Submodule R (X → C)) :=
  augIdeal M ⧸ (sqIdeal (augIdeal M)).comap (augIdeal M).subtype

structure HodgeTateDatum {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O]
    (σ : O ≃ₐ[ℤ_[p]] O) (cp : R) where

  ρ : O →ₐ[ℤ_[p]] Matrix (Ix g) (Ix g) ℤ_[p]

  ρL : O →+* Matrix (Fin g) (Fin g) R

  P : Matrix (Ix g) (Ix g) ℤ_[p]
  PL : Matrix (Fin g) (Fin g) R

  E : Matrix (Ix g) (Ix g) ℤ_[p]
  E_alternating : Eᵀ = -E ∧ ∀ i, E i i = 0
  isUnit_det_E : IsUnit E.det
  E_equivariant : ∀ a, (ρ a)ᵀ * E = E * ρ (σ a)
  projectors : P * P = P ∧ PL * PL = PL ∧ Pᵀ * E = E * P ∧
    (∀ a, P * ρ a = ρ a * P) ∧ ∀ a, PL * ρL a = ρL a * PL

  Ht : Matrix (Fin g) (Ix g) R

  Bt : Matrix (Fin g) (Ix g) R
  Ht_equivariant : (∀ a, Ht * (ρ a).map (algebraMap ℤ_[p] R) = (ρL (σ a))ᵀ * Ht) ∧
    Ht * P.map (algebraMap ℤ_[p] R) = PLᵀ * Ht
  form_eq_alt : Btᵀ * Ht - Htᵀ * Bt = cp • E.map (algebraMap ℤ_[p] R)

  AA : HopfOrder (C := C) R (Nb p g)
  h3 : ∀ a, ∀ f ∈ AA.carrier, ∃ f' ∈ AA.carrier, ∀ t, f' (red p g t) = f (red p g (ρ a *ᵥ t))

  h4 : ∀ k : Fin g,
    (∃ f ∈ AA.carrier, ∀ t : TT p g, ∃ r : R, algebraMap R C
      ((Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) - f (red p g t) = algebraMap R C (p * r)) ∧
    (∃ f ∈ AA.carrier, ∀ t : TT p g, ∃ r : R, algebraMap R C
      ((Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) - f (red p g t) = algebraMap R C (p * r))

  h5 : p = 2 → ∀ s : TT p g, ∃ f ∈ AA.carrier, ∀ t : TT p g,
    f (red p g t) = (-1 : C) ^ (PadicInt.toZMod (pair p g E s t)).val

  φ : augIdeal AA.carrier →ₗ[R] LieDualModP p R g
  cotangent_surjective : Function.Surjective φ
  cotangent_ker_eq : LinearMap.ker φ = (sqIdeal (augIdeal AA.carrier)).comap (augIdeal AA.carrier).subtype
  cotangent_linear : ∀ (a : O) (f f' : augIdeal AA.carrier) (l : Fin g → R),
    (∀ t, (f' : Nb p g → C) (red p g t) = (f : Nb p g → C) (red p g (ρ a *ᵥ t))) →
    φ f = Submodule.Quotient.mk l → φ f' = Submodule.Quotient.mk ((ρL a)ᵀ *ᵥ l)

structure HodgeTateSetting {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O]
    (σ : O ≃ₐ[ℤ_[p]] O) (cp : R) : Prop where
  integers : v.Integers R
  p_lt : v (algebraMap R C (p : R)) < 1
  p_ne : v (algebraMap R C (p : R)) ≠ 0
  cp_val : v (algebraMap R C cp) ^ (p - 1) = v (algebraMap R C (p : R))
  invol : ∀ a, σ (σ a) = a

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.CyclicRecursion
section
noncomputable section

open WittVector MvPolynomial

namespace ReciprocityTheory.PGsh

section TeichSum

variable {p : ℕ} [hp : Fact p.Prime]

private lemma ghost_one {R : Type*} [CommRing R] (x : WittVector p R) :
    ghostComponent 1 x = x.coeff 0 ^ p + (p : R) * x.coeff 1 := by
  rw [WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow]
  simp [Finset.sum_range_succ] <;> ring

private lemma coeff_zero_sum {R ι : Type*} [CommRing R] (s : Finset ι) (f : ι → WittVector p R) :
    (∑ i ∈ s, f i).coeff 0 = ∑ i ∈ s, (f i).coeff 0 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, WittVector.add_coeff_zero, ih]

private lemma ringHom_aeval {K ι : Type*} [CommRing K] (σ : K →+* K) (g : ι → K)
    (S : MvPolynomial ι ℤ) : σ (aeval g S) = aeval (σ ∘ g) S := by
  induction S using MvPolynomial.induction_on <;> simp_all

private lemma univ_coeff {ι : Type} (s : Finset ι) :
    (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 0 = ∑ i ∈ s, X i ∧
    (p : MvPolynomial ι ℤ) * (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 1 =
      ∑ i ∈ s, X i ^ p - (∑ i ∈ s, X i) ^ p := by
  have h0 : (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 0 = ∑ i ∈ s, X i := by
    rw [coeff_zero_sum]
    simp
  refine ⟨h0, ?_⟩
  have hg : ghostComponent 1 (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)) =
      ∑ i ∈ s, (X i : MvPolynomial ι ℤ) ^ p := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ghost_one]
    simp [WittVector.teichmuller_coeff_pos]
  rw [ghost_one, h0] at hg
  linear_combination hg

private lemma verschiebung_eq_map_frobenius_symm_mul_p {K : Type} [CommRing K] [CharP K p] [PerfectRing K p]
    (y : WittVector p K) :
    WittVector.verschiebung y = WittVector.map ((frobeniusEquiv K p).symm : K →+* K) y * p := by
  have hF : WittVector.frobenius (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) y) = y := by
    ext n
    rw [WittVector.coeff_frobenius_charP, WittVector.map_coeff]
    simp [frobeniusEquiv_symm_pow_p]
  calc WittVector.verschiebung y = WittVector.verschiebung
        (WittVector.frobenius (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) y)) := by
        rw [hF]
    _ = _ := WittVector.verschiebung_frobenius _

private lemma exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul {K : Type} [CommRing K] [CharP K p] [PerfectRing K p]
    (x : WittVector p K) :
    ∃ w : WittVector p K, x = teichmuller p (x.coeff 0) +
      (p : WittVector p K) * teichmuller p ((frobeniusEquiv K p).symm (x.coeff 1)) +
      (p : WittVector p K) ^ 2 * w := by
  have h1 : ∀ z : WittVector p K, ∃ u : WittVector p K,
      z = teichmuller p (z.coeff 0) + WittVector.verschiebung u ∧ u.coeff 0 = z.coeff 1 := by
    intro z
    refine ⟨WittVector.mk p (fun n => z.coeff (n + 1)), ?_, rfl⟩
    ext n
    rw [WittVector.coeff_add_of_disjoint]
    · rcases n with _ | n
      · simp [WittVector.teichmuller_coeff_zero, WittVector.verschiebung_coeff_zero]
      · simp [WittVector.teichmuller_coeff_pos, WittVector.verschiebung_coeff_succ]
    · intro m
      rcases m with _ | m
      · right
        simp [WittVector.verschiebung_coeff_zero]
      · left
        simp [WittVector.teichmuller_coeff_pos]
  obtain ⟨u, hu, hu0⟩ := h1 x
  rw [verschiebung_eq_map_frobenius_symm_mul_p] at hu
  obtain ⟨v, hv, -⟩ := h1 (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u)
  rw [verschiebung_eq_map_frobenius_symm_mul_p] at hv
  have hc : (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u).coeff 0 =
      (frobeniusEquiv K p).symm (x.coeff 1) := by
    rw [WittVector.map_coeff, hu0]
    try rfl
  rw [hc] at hv
  refine ⟨WittVector.map ((frobeniusEquiv K p).symm : K →+* K) v, ?_⟩
  calc x = teichmuller p (x.coeff 0) +
        WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u * p := hu
    _ = teichmuller p (x.coeff 0) + (teichmuller p ((frobeniusEquiv K p).symm (x.coeff 1)) +
          WittVector.map ((frobeniusEquiv K p).symm : K →+* K) v * p) * p := by rw [hv]
    _ = _ := by ring

theorem teichSum (p : ℕ) [Fact p.Prime] : TeichSumStatement p := by
  intro ι s
  refine ⟨⟨_, (univ_coeff (p := p) s).2⟩, ?_⟩
  intro K _ _ _ X S hS
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul (∑ i ∈ s, teichmuller p (X i))
    have h0 : (∑ i ∈ s, teichmuller p (X i)).coeff 0 = ∑ i ∈ s, X i := by
      rw [coeff_zero_sum]
      simp
    have hmap : WittVector.map (MvPolynomial.aeval X).toRingHom
        (∑ i ∈ s, teichmuller p (MvPolynomial.X i : MvPolynomial ι ℤ)) =
          ∑ i ∈ s, teichmuller p (X i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [WittVector.map_teichmuller]
      simp
    have hSeq : (∑ i ∈ s, teichmuller p (MvPolynomial.X i : MvPolynomial ι ℤ)).coeff 1 = S := by
      have hp0 : (p : MvPolynomial ι ℤ) ≠ 0 := by
        exact_mod_cast (Fact.out : p.Prime).ne_zero
      exact mul_left_cancel₀ hp0 ((univ_coeff (p := p) s).2.trans hS.symm)
    have h1 : (∑ i ∈ s, teichmuller p (X i)).coeff 1 = MvPolynomial.aeval X S := by
      rw [← hmap, WittVector.map_coeff, hSeq]
      try rfl
    have hfr : (frobeniusEquiv K p).symm (MvPolynomial.aeval X S) =
        MvPolynomial.aeval (fun i => (frobeniusEquiv K p).symm (X i)) S :=
      ringHom_aeval ((frobeniusEquiv K p).symm : K →+* K) X S
    refine ⟨w, ?_⟩
    rw [h0, h1, hfr] at hw
    exact hw
  · intro y t
    have hd : ((p : ℕ) : WittVector p K) ∣ (teichmuller p y + (p : WittVector p K) * t) -
        teichmuller p y := ⟨t, by ring⟩
    obtain ⟨w, hw⟩ := dvd_sub_pow_of_dvd_sub hd 1
    refine ⟨w, ?_⟩
    simp only [pow_one] at hw
    rw [show teichmuller p (y ^ p) = teichmuller p y ^ p from map_pow _ _ _]
    linear_combination hw

end TeichSum

section Cyclic

end Cyclic

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.DualHopfOrderStatement
section
noncomputable section

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def DualHopfOrderStatement : Prop :=
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N H : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] [AddCommGroup H] [Fintype H]
    [DecidableEq H] (e : H ≃ AddChar N C), (∀ h h', e (h + h') = e h * e h') →
    Fintype.card H = Fintype.card N →
    ∀ AA : HopfOrder (C := C) R N,
      ∃ AD : HopfOrder (C := C) R H,
        AD.carrier = (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a) ∧
        (dualLat AD.carrier).map (fourier (R := R) fun a h => e h a) = AA.carrier ∧
        ∀ c c', HasColen R v AA.carrier c → HasColen R v AD.carrier c' →
          (c * c') ^ 2 = v (Fintype.card N : C) ^ Fintype.card N

end ReciprocityTheory.PGsh.L2
end
end

-- bundled from ReciprocityTheory.DualLattices.ExistsSmulMemOfMemSpan
section
noncomputable section

namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

open Module

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem exists_smul_mem_of_mem_span [IsDomain R] [IsFractionRing R C]
    {V : Type} [AddCommGroup V] [Module C V] [Module R V] [IsScalarTower R C V]
    (S : Submodule R V) {x : V} (hx : x ∈ Submodule.span C (S : Set V)) :
    ∃ r : R, r ≠ 0 ∧ r • x ∈ S := by
  exact Bl.SecondBlockLemmaM.goal1 (C := C) S hx

theorem free_of_finite_torsionFree [IsDomain R] [ValuationRing R] (P : Type) [AddCommGroup P]
    [Module R P] [Module.Finite R P] (h : ∀ (r : R) (x : P), r ≠ 0 → r • x = 0 → x = 0) :
    Module.Free R P := by
  have : Module.Flat R P := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
    exact h a x (nonZeroDivisors.ne_zero a.2) ha
  exact Module.free_of_flat_of_isLocalRing

theorem algebraMap_ne_zero [IsFractionRing R C] {r : R} (hr : r ≠ 0) : algebraMap R C r ≠ 0 := by
  intro h0
  exact hr ((IsFractionRing.injective R C) (by simpa using h0))

theorem isLat_of_fg [IsDomain R] [ValuationRing R] [IsFractionRing R C]
    {X : Type} [Fintype X] [DecidableEq X] (M : Submodule R (X → C)) (hfg : M.FG)
    (hsp : Submodule.span C (M : Set (X → C)) = ⊤) : IsLat R M := by
  have : Module.Finite R M := Module.Finite.iff_fg.2 hfg
  have : Module.Free R M := free_of_finite_torsionFree M (by
    rintro r ⟨x, hx⟩ hr h
    have h' : (r • x : X → C) = 0 := by simpa using congrArg Subtype.val h
    rw [← algebraMap_smul C r x] at h'
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left (algebraMap_ne_zero hr)))
  let b := Module.Free.chooseBasis R M
  let v : Module.Free.ChooseBasisIndex R M → X → C := fun i => (b i : X → C)
  have hR : LinearIndependent R v := b.linearIndependent.map' M.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent C v := (LinearIndependent.iff_fractionRing R C).1 hR
  have hspR : Submodule.span R (Set.range v) = M := by
    have : Set.range v = M.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspC : Submodule.span C (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower R, hspR, hsp]
  let bC := Basis.mk hC (by rw [hspC])
  have hcard : Fintype.card X = Fintype.card (Module.Free.ChooseBasisIndex R M) := by
    rw [← Module.finrank_fintype_fun_eq_card (R := C), Module.finrank_eq_card_basis bC]
  let e : X ≃ Module.Free.ChooseBasisIndex R M := Fintype.equivOfCardEq hcard
  refine ⟨fun x j => v (e j) x, ?_, ?_⟩
  · have hli : LinearIndependent C (fun j x => v (e j) x) := hC.comp e e.injective
    have hu := (Matrix.linearIndependent_cols_iff_isUnit (A := (fun x j => v (e j) x : Matrix X X C))).1
      (by convert hli using 1; rfl)
    exact (Matrix.isUnit_iff_isUnit_det _).1 hu
  · have : Set.range (fun j x => v (e j) x) = Set.range v := by
      ext f; constructor
      · rintro ⟨j, rfl⟩; exact ⟨e j, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨e.symm i, by simp⟩
    rw [this, hspR]

theorem fg_of_isLat {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)}
    (h : IsLat R M) : M.FG := by
  obtain ⟨B, -, rfl⟩ := h
  exact Submodule.fg_span (Set.finite_range _)

theorem span_top_of_isLat {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)}
    (h : IsLat R M) : Submodule.span C (M : Set (X → C)) = ⊤ := by
  obtain ⟨B, hB, rfl⟩ := h
  rw [Submodule.span_span_of_tower]
  have hli : LinearIndependent C (fun j x => B x j) := by
    have := (Matrix.linearIndependent_cols_iff_isUnit (A := B)).2 ((Matrix.isUnit_iff_isUnit_det B).2 hB)
    convert this using 1; rfl
  exact hli.span_eq_top_of_card_eq_finrank' (by simp)

end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
end
end

