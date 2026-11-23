module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsUnitIffCharpolyCoeffZeroNe
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL


open Polynomial in
theorem _root_.GlobalTheory.CuspGL.ipGL_charpoly_eq_finsum_mass (F : Type) [Field F] [Finite F]
    (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (φ : Module.End F V → ℂ) (s : F[X] → ℂ) :
    _root_.GlobalTheory.CuspGL.ipGL φ (fun g => s (LinearMap.charpoly g)) =
      ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0},
        _root_.GlobalTheory.CuspGL.mass φ P * star (s P) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective
  set S := {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0} with hS
  set I := S ∩ Set.range (fun g : Module.End F V => LinearMap.charpoly g) with hI
  have hunit : ∀ g : Module.End F V, IsUnit g ↔ LinearMap.charpoly g ∈ S := by
    intro g
    simp only [hS, Set.mem_setOf_eq, LinearMap.charpoly_monic, LinearMap.charpoly_natDegree,
      true_and]
    rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_eq_sign_charpoly_coeff, isUnit_iff_ne_zero]
    simp
  have hset : {g : Module.End F V | IsUnit g} =
      ⋃ P ∈ I, {g : Module.End F V | LinearMap.charpoly g = P} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, hI, Set.mem_inter_iff, Set.mem_range,
      exists_prop]
    rw [hunit]
    constructor
    · intro h
      exact ⟨_, ⟨h, g, rfl⟩, rfl⟩
    · rintro ⟨P, ⟨hP, _⟩, rfl⟩
      exact hP
  have hsupp : S ∩ Function.support (fun P => _root_.GlobalTheory.CuspGL.mass φ P * star (s P)) =
      I ∩ Function.support (fun P => _root_.GlobalTheory.CuspGL.mass φ P * star (s P)) := by
    ext P
    simp only [hI, Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hPS, hne⟩
      refine ⟨⟨hPS, ?_⟩, hne⟩
      by_contra hr
      apply hne
      have hempty : {g : Module.End F V | LinearMap.charpoly g = P} = ∅ := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hr ⟨g, h⟩
      unfold _root_.GlobalTheory.CuspGL.mass
      simp [hempty]
    · rintro ⟨⟨hPS, _⟩, hne⟩
      exact ⟨hPS, hne⟩
  rw [finsum_mem_inter_support_eq _ S I hsupp]
  unfold _root_.GlobalTheory.CuspGL.ipGL _root_.GlobalTheory.CuspGL.mass
  rw [hset, finsum_mem_biUnion ?_ ((Set.finite_range _).subset Set.inter_subset_right)
    (fun _ _ => Set.toFinite _)]
  · refine finsum_mem_congr rfl fun P _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Set.Finite.mem_toFinset] at hg
    show φ g * star (s (LinearMap.charpoly g)) = _
    rw [show LinearMap.charpoly g = P from hg]
  · intro P _ Q _ hPQ
    exact Set.disjoint_left.2 fun g hP hQ => hPQ (hP.symm.trans hQ)

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.KerAevalAddStabilizerNilradicalSocle
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem pow_add_nilRad {A : Submodule F V} {g h : Module.End F V} (hg : ∀ x ∈ A, g x ∈ A)
    (hh : h ∈ nilRad A) (n : ℕ) :
    (∀ x ∈ A, ((g + h) ^ n) x = (g ^ n) x ∧ (g ^ n) x ∈ A) ∧ ∀ x, ((g + h) ^ n) x - (g ^ n) x ∈ A := by
  induction n with
  | zero => exact ⟨fun x hx => ⟨by simp, by simpa using hx⟩, fun x => by simp⟩
  | succ n ih =>
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · obtain ⟨h1, h2⟩ := ih.1 x hx
      simp only [pow_succ', Module.End.mul_apply, LinearMap.add_apply, h1, hh.2 _ h2, add_zero, true_and]
      exact hg _ h2
    · have h1 := hg _ (ih.2 x)
      have h2 := hh.1 (((g + h) ^ n) x)
      have := A.add_mem h1 h2
      simp only [pow_succ', Module.End.mul_apply, LinearMap.add_apply]
      rw [map_sub] at this
      convert this using 1
      abel

theorem aeval_add_nilRad {A : Submodule F V} {g h : Module.End F V} (hg : ∀ x ∈ A, g x ∈ A)
    (hh : h ∈ nilRad A) (p : F[X]) :
    (∀ x ∈ A, aeval (g + h) p x = aeval g p x) ∧ ∀ x, aeval (g + h) p x - aeval g p x ∈ A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · simp only [map_add (f := _), LinearMap.add_apply, hp.1 x hx, hq.1 x hx]
    · have := A.add_mem (hp.2 x) (hq.2 x)
      simp only [map_add (f := _), LinearMap.add_apply]
      convert this using 1
      abel
  | monomial n a =>
    have H := pow_add_nilRad hg hh n
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · simp only [aeval_monomial, Module.End.mul_apply, (H.1 x hx).1]
    · simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, ← smul_sub]
      exact A.smul_mem _ (H.2 x)

theorem ker_aeval_add_nilRad :
    ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g h : Module.End F V) (f : F[X]), h ∈ nilRad (LinearMap.ker (aeval g f)) → LinearMap.ker (aeval g f) ≤ LinearMap.ker (aeval (g + h) f) ∧ (LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) → ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval (g + h) (f ^ j)))) := by
  intro F _ V _ _ _ g h f hh
  have hg : ∀ x ∈ LinearMap.ker (aeval g f), g x ∈ LinearMap.ker (aeval g f) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have : aeval g f * g = g * aeval g f := by
      have h1 : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
      simpa using h1
    rw [← Module.End.mul_apply, this, Module.End.mul_apply, hx, map_zero]
  refine ⟨fun x hx => ?_, fun he j => ?_⟩
  · rw [LinearMap.mem_ker, (aeval_add_nilRad hg hh f).1 x hx]
    exact hx
  · have : LinearMap.ker (aeval g (f ^ j)) = LinearMap.ker (aeval (g + h) (f ^ j)) := by
      cases j with
      | zero =>
        ext x
        simp
      | succ j =>
        ext x
        have H := (aeval_add_nilRad hg hh (f ^ j)).2 x
        have e1 : x ∈ LinearMap.ker (aeval g (f ^ (j + 1))) ↔
            aeval g (f ^ j) x ∈ LinearMap.ker (aeval g f) := by
          rw [pow_succ', map_mul, LinearMap.mem_ker, LinearMap.mem_ker, Module.End.mul_apply]
        have e2 : x ∈ LinearMap.ker (aeval (g + h) (f ^ (j + 1))) ↔
            aeval (g + h) (f ^ j) x ∈ LinearMap.ker (aeval (g + h) f) := by
          rw [pow_succ', map_mul, LinearMap.mem_ker, LinearMap.mem_ker, Module.End.mul_apply]
        rw [e1, e2, he]
        constructor
        · intro a
          have := Submodule.add_mem _ H a
          rwa [sub_add_cancel] at this
        · intro a
          have := Submodule.sub_mem _ a H
          rwa [sub_sub_cancel] at this
    rw [this]

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MatrixTraceIffIsCharacterOverSubfieldComplex
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem matrixChar_iff_isChar : ∀ (G : Type) [Group G] (χ : G → ℂ),
    (∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)) ↔
      IsChar ℂ ℂ χ := by
  intro G _ χ
  constructor
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨n, (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom _).comp ρ), fun g => ?_⟩
    rw [hρ g]
    show _ = Representation.character _ g
    rw [Representation.character,
      LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    change _ = (LinearMap.toMatrix' (Matrix.toLin' _)).trace
    rw [LinearMap.toMatrix'_toLin']
    rfl
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨n, Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp ρ.asGroupHom, fun g => ?_⟩
    rw [hρ g]
    show Representation.character _ g = _
    rw [Representation.character,
      LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    rfl

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MonicFactorizationConvolutionCancelOfOne
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL.ConvCancel

theorem finite_pairs {F : Type} [Field F] (P : F[X]) (hP : P ≠ 0) :
    {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite := by
  classical
  have hfin : {g : F[X] | g.Monic ∧ g ∣ P}.Finite := by
    have h := Polynomial.fintypeSubtypeMonicDvd P hP
    exact @Finite.of_fintype _ h
  refine (hfin.prod hfin).subset ?_
  rintro ⟨D, E⟩ ⟨hD, hE, h⟩
  exact ⟨⟨hD, Dvd.intro _ h⟩, ⟨hE, Dvd.intro_left _ h⟩⟩

theorem conv_cancel : ∀ (F : Type) [Field F] (a b m : F[X] → ℂ), m 1 = 1 →
    (∀ P : F[X], P.Monic → conv a m P = conv b m P) → ∀ P : F[X], P.Monic → a P = b P := by
  intro F _ a b m hm h P
  classical
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    intro hP
    have hfin := finite_pairs P hP.ne_zero
    have h1 := h P hP
    unfold conv at h1
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin] at h1
    have hmem : ((P, 1) : F[X] × F[X]) ∈ hfin.toFinset := by
      simp [hP]
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at h1
    have h2 : ∑ x ∈ hfin.toFinset.erase (P, 1), a x.1 * m x.2
        = ∑ x ∈ hfin.toFinset.erase (P, 1), b x.1 * m x.2 := by
      refine Finset.sum_congr rfl ?_
      rintro ⟨D, E⟩ hx
      rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hx
      obtain ⟨hne, hD, hE, hDE⟩ := hx
      simp only at hD hE hDE ⊢
      have hE1 : E ≠ 1 := by
        rintro rfl
        apply hne
        rw [← hDE, mul_one]
      have hdeg : D.natDegree < n := by
        rw [← hn, ← hDE, hD.natDegree_mul hE]
        have : E.natDegree ≠ 0 := fun h0 => hE1 (hE.natDegree_eq_zero.mp h0)
        omega
      rw [ih _ hdeg D rfl hD]
    rw [h2] at h1
    simpa [hm] using h1

end GlobalTheory.CuspGL.ConvCancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MonicFactorizationConvolutionFiniteCommAssocAdd
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F]

theorem finite_monic_factorisations (P : F[X]) :
    {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite := by
  by_cases hP : P = 0
  · refine Set.finite_empty.subset ?_
    rintro x ⟨h1, h2, h3⟩
    exact False.elim ((h1.mul h2).ne_zero (h3.trans hP))
  · have hfin : {D : F[X] | D.Monic ∧ D ∣ P}.Finite := by
      letI : Fintype {D : F[X] | D.Monic ∧ D ∣ P} := Polynomial.fintypeSubtypeMonicDvd P hP
      exact Set.toFinite _
    refine (hfin.prod hfin).subset ?_
    rintro x ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3 ▸ dvd_mul_right _ _⟩, ⟨h2, h3 ▸ dvd_mul_left _ _⟩⟩

theorem conv_eq_sum (a b : F[X] → ℂ) (P : F[X]) :
    conv a b P = ∑ x ∈ (finite_monic_factorisations P).toFinset, a x.1 * b x.2 :=
  finsum_mem_eq_finite_toFinset_sum _ (finite_monic_factorisations P)

theorem conv_comm (a b : F[X] → ℂ) (P : F[X]) : conv a b P = conv b a P := by
  rw [conv_eq_sum, conv_eq_sum]
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    exact ⟨hx.2.1, hx.1, by rw [← hx.2.2]; exact mul_comm _ _⟩
  · intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    exact ⟨hx.2.1, hx.1, by rw [← hx.2.2]; exact mul_comm _ _⟩
  · intro x _; rfl
  · intro x _; rfl
  · intro x _; exact mul_comm _ _

theorem conv_assoc (a b c : F[X] → ℂ) (P : F[X]) :
    conv (conv a b) c P = conv a (conv b c) P := by
  rw [conv_eq_sum, conv_eq_sum]
  simp only [conv_eq_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun z => ⟨(z.2.1, z.2.2 * z.1.2), (z.2.2, z.1.2)⟩)
    (fun z => ⟨(z.1.1 * z.2.1, z.2.2), (z.1.1, z.2.1)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    exact ⟨⟨h4, h5.mul h2, by rw [← mul_assoc, h6, h3]⟩, h5, h2, trivial⟩
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    exact ⟨⟨h1.mul h4, h5, by rw [mul_assoc, h6, h3]⟩, h1, h4, trivial⟩
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    subst h6
    rfl
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    subst h6
    rfl
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ _
    exact mul_assoc _ _ _

theorem conv_add_left (a b c : F[X] → ℂ) (P : F[X]) :
    conv (a + b) c P = conv a c P + conv b c P := by
  simp only [conv_eq_sum, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem conv_sub_left (a b c : F[X] → ℂ) (P : F[X]) :
    conv (a - b) c P = conv a c P - conv b c P := by
  simp only [conv_eq_sum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem conv_basic : ∀ (F : Type) [Field F] (P : F[X]), P.Monic → {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite ∧ ∀ a b c : F[X] → ℂ, conv a b P = conv b a P ∧ conv (conv a b) c P = conv a (conv b c) P ∧ conv (a + b) c P = conv a c P + conv b c P ∧ conv (a - b) c P = conv a c P - conv b c P :=
  fun _ _ P _ => ⟨finite_monic_factorisations P, fun a b c =>
    ⟨conv_comm a b P, conv_assoc a b c P, conv_add_left a b c P, conv_sub_left a b c P⟩⟩

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MultisetPowerSumNewtonIdentity
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

private theorem sum_antidiagonal_filter_ioo_eq_sum_ioo (k : ℕ) (g : ℕ → ℕ → ℂ) :
    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k, g a.1 a.2
      = ∑ i ∈ Finset.Ioo 0 k, g i (k - i) := by
  rw [Finset.sum_filter,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if i ∈ Set.Ioo 0 k then g i j else 0),
    ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioo, Finset.mem_Ioo]
  omega

private theorem aeval_psum_eq_sum_map_pow (s : Multiset ℂ) (n : ℕ) :
    MvPolynomial.aeval (fun x : s => (x : ℂ)) (MvPolynomial.psum s ℂ n) = (s.map (· ^ n)).sum := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.psum, map_sum]
  simp only [map_pow, MvPolynomial.aeval_X]
  conv_rhs => rw [← Multiset.map_univ_coe s]
  rw [Multiset.map_map]
  rfl

theorem multiset_newton_psum (s : Multiset ℂ) (r : ℕ) (hr : 0 < r) :
    (s.map (· ^ r)).sum = (-1) ^ (r + 1) * (r : ℂ) * s.esymm r
      - ∑ i ∈ Finset.Ioo 0 r, (-1) ^ i * s.esymm i * (s.map (· ^ (r - i))).sum := by
  classical
  have key := congrArg (MvPolynomial.aeval (fun x : s => (x : ℂ)))
    (MvPolynomial.psum_eq_mul_esymm_sub_sum s ℂ r hr)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe,
    aeval_psum_eq_sum_map_pow] at key
  rw [key, sum_antidiagonal_filter_ioo_eq_sum_ioo r (fun i j => (-1) ^ i * s.esymm i * (s.map (· ^ j)).sum)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormEightOfFourierVanishingOrderFifteen
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

theorem no_norm_eight_of_fourier_vanishing_order_fifteen :
    ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 15 → ∑ k ∈ Finset.range 15, c k ^ 2 = 8 →
      (∀ j : ℕ, j < 15 → ¬ 5 ∣ j → ∑ k ∈ Finset.range 15, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  intro ω c hω hs hF
  have hinj : Function.Injective (fun j : Fin 15 => ω ^ (j : ℕ)) := by
    intro a b hab
    exact Fin.ext (hω.pow_inj a.2 b.2 hab)
  have hv : (fun i : Fin 15 => ((c ((i + 12) % 15) - c i : ℤ) : ℂ)) = 0 := by
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hinj
    intro j
    have h15 : (ω ^ (j : ℕ)) ^ 15 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have hprod : ((ω ^ (j : ℕ)) ^ 3 - 1) *
        ∑ k ∈ Finset.range 15, (c k : ℂ) * (ω ^ (j : ℕ)) ^ k = 0 := by
      by_cases h5 : 5 ∣ (j : ℕ)
      · obtain ⟨m, hm⟩ := h5
        have : (ω ^ (j : ℕ)) ^ 3 = 1 := by
          rw [hm, ← pow_mul, show 5 * m * 3 = 15 * m by ring, pow_mul, hω.pow_eq_one, one_pow]
        rw [this, sub_self, zero_mul]
      · have := hF j j.2 h5
        simp only [pow_mul] at this
        rw [this, mul_zero]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (ω ^ (j : ℕ)) ^ i * ((c ((i + 12) % 15) - c i : ℤ) : ℂ)) 15]
    generalize ω ^ (j : ℕ) = x at h15 hprod
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hprod ⊢
    push_cast
    linear_combination hprod - ((c 12 : ℂ) + c 13 * x + c 14 * x ^ 2) * h15
  have hp : ∀ i : ℕ, i < 15 → c i = c ((i + 12) % 15) := by
    intro i hi
    have := congrFun hv ⟨i, hi⟩
    simp only [Pi.zero_apply, Int.cast_eq_zero] at this
    linarith
  have h3 : c 3 = c 0 := hp 3 (by norm_num)
  have h4 : c 4 = c 1 := hp 4 (by norm_num)
  have h5 : c 5 = c 2 := hp 5 (by norm_num)
  have h6 : c 6 = c 3 := hp 6 (by norm_num)
  have h7 : c 7 = c 4 := hp 7 (by norm_num)
  have h8 : c 8 = c 5 := hp 8 (by norm_num)
  have h9 : c 9 = c 6 := hp 9 (by norm_num)
  have h10 : c 10 = c 7 := hp 10 (by norm_num)
  have h11 : c 11 = c 8 := hp 11 (by norm_num)
  have h12 : c 12 = c 9 := hp 12 (by norm_num)
  have h13 : c 13 = c 10 := hp 13 (by norm_num)
  have h14 : c 14 = c 11 := hp 14 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  rw [h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3] at hs
  generalize c 0 ^ 2 = a at hs
  generalize c 1 ^ 2 = b at hs
  generalize c 2 ^ 2 = d at hs
  omega

end GlobalTheory
end

