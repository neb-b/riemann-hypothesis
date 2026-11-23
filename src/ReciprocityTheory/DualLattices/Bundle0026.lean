module

public import ReciprocityTheory.DualLattices.Bundle0023
public import ReciprocityTheory.DualLattices.Bundle0024
public import ReciprocityTheory.DualLattices.Bundle0010
public import ReciprocityTheory.DualLattices.Bundle0019
public import ReciprocityTheory.DualLattices.PowMemCarrier
public import ReciprocityTheory.DualLattices.Bundle0016
public import ReciprocityTheory.DualLattices.Bundle0011

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.AinfTower
section
noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

namespace Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

abbrev R0 (ε : PreTilt O p) := A p O ⧸ span {xi p O ε ^ 2}

abbrev Rn (n : ℕ) := O ⧸ span {(p : O) ^ (n + 1)}

abbrev R'n (ε : PreTilt O p) (n : ℕ) := R0 p O ε ⧸ span {(p : R0 p O ε) ^ (n + 1)}

lemma hpRn (n : ℕ) : (p : Rn p O n) ^ (n + 1) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})) p, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

lemma hpR' (ε : PreTilt O p) (n : ℕ) : (p : R'n p O ε n) ^ (n + 1) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (span {(p : R0 p O ε) ^ (n + 1)})) p, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

lemma Rn_local (hv : v.Integers O) (n : ℕ) : IsLocalRing (Rn p O n) := by
  haveI := O_local O hv
  haveI : Nontrivial (Rn p O n) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 : (1 : O) ∈ span {(p : O) ^ (n + 1)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]; exact h.symm
    rw [Ideal.mem_span_singleton'] at h1
    obtain ⟨a, ha⟩ := h1
    exact (Fact.out : ¬IsUnit (p : O))
      ((isUnit_pow_iff (Nat.succ_ne_zero n)).1 (IsUnit.of_mul_eq_one_right a ha))
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

lemma one_add_unit {S : Type} [CommRing S] (a b : S) (hb : b * b = 0) : IsUnit (1 + a * b) := by
  exact IsUnit.of_mul_eq_one (1 - a * b) (by linear_combination (-a ^ 2) * hb)

variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

def thetaBar : R0 p O ε →+* O :=
  Ideal.Quotient.lift _ (fontaineTheta O p) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, theta_xi p O hv ε hε, zero_pow two_ne_zero, mul_zero])

def algO : Algebra (R0 p O ε) O := (thetaBar p O hv ε hε).toAlgebra

def algRn (n : ℕ) : Algebra (R0 p O ε) (Rn p O n) :=
  ((Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})).comp (thetaBar p O hv ε hε)).toAlgebra

def piRing (n : ℕ) : R'n p O ε n →+* Rn p O n :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})).comp
    (thetaBar p O hv ε hε)) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast, hpRn, mul_zero])

lemma piRing_mk (n : ℕ) (a : A p O) :
    piRing p O hv ε hε n (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a)) =
      Ideal.Quotient.mk _ (fontaineTheta O p a) := rfl

lemma piRing_surj (n : ℕ) : Function.Surjective (piRing p O hv ε hε n) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, rfl⟩ := theta_surj p O hv x
  exact ⟨_, piRing_mk p O hv ε hε n a⟩

def xiR (n : ℕ) : R'n p O ε n :=
  Ideal.Quotient.mk (span {(p : R0 p O ε) ^ (n + 1)}) (Ideal.Quotient.mk (span {xi p O ε ^ 2}) (xi p O ε))

lemma ker_pi (n : ℕ) : RingHom.ker (piRing p O hv ε hε n) = span {xiR p O ε n} := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [piRing_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
    obtain ⟨o, ho⟩ := hx
    obtain ⟨b, rfl⟩ := theta_surj p O hv o
    have hk : a - b * (p : A p O) ^ (n + 1) ∈ RingHom.ker (fontaineTheta O p) := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_pow, map_natCast, ho, sub_self]
    rw [ker_theta p O hv ε hε, Ideal.mem_span_singleton'] at hk
    obtain ⟨c, hc⟩ := hk
    have ha : a = c * xi p O ε + b * (p : A p O) ^ (n + 1) := by rw [hc]; ring
    rw [Ideal.mem_span_singleton']
    refine ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk _ c), ?_⟩
    rw [ha]
    simp only [xiR, map_add (f := _), map_mul, map_pow, map_natCast, hpR', mul_zero, add_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, xiR, piRing_mk,
      theta_xi p O hv ε hε, map_zero]

lemma xi_sq' (n : ℕ) : xiR p O ε n * xiR p O ε n = 0 := by
  unfold xiR
  rw [← map_mul, ← map_mul]
  have h : (Ideal.Quotient.mk (span {xi p O ε ^ 2})) (xi p O ε * xi p O ε) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨1, by ring⟩)
  rw [h, map_zero]

lemma R'n_local (n : ℕ) : IsLocalRing (R'n p O ε n) := by
  haveI := Rn_local p O hv n
  haveI : Nontrivial (R'n p O ε n) := (piRing p O hv ε hε n).domain_nontrivial
  have key : ∀ a : R'n p O ε n, IsUnit (piRing p O hv ε hε n a) → IsUnit a := by
    intro a ha
    obtain ⟨u, hu⟩ := ha.exists_right_inv
    obtain ⟨u', rfl⟩ := piRing_surj p O hv ε hε n u
    have hk : a * u' - 1 ∈ RingHom.ker (piRing p O hv ε hε n) := by
      rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hu, map_one, sub_self]
    rw [ker_pi, Ideal.mem_span_singleton'] at hk
    obtain ⟨k, hk⟩ := hk
    have h1 : a * u' = 1 + k * xiR p O ε n := by rw [hk]; ring
    have h2 := one_add_unit k (xiR p O ε n) (xi_sq' p O hv ε hε n)
    rw [← h1] at h2
    exact isUnit_of_mul_isUnit_left h2
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self (fun a => ?_)
  have h : piRing p O hv ε hε n a + piRing p O hv ε hε n (1 - a) = 1 := by
    change (piRing p O hv ε hε n) a + (piRing p O hv ε hε n) (1 - a) = 1
    rw [← (piRing p O hv ε hε n).map_add, add_sub_cancel, (piRing p O hv ε hε n).map_one]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h with h | h
  · exact Or.inl (key a h)
  · exact Or.inr (key _ h)

lemma ann' (n : ℕ) (a : R'n p O ε n) (ha : a * xiR p O ε n = 0) :
    a ∈ span {xiR p O ε n} := by
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  have hp0 : (p : O) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h'
    exact hp.out.ne_zero (by exact_mod_cast h')
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  unfold xiR at ha
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at ha
  obtain ⟨d0, hd0⟩ := ha
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d0
  rw [← map_natCast (Ideal.Quotient.mk (span {xi p O ε ^ 2})) p, ← map_pow, ← map_mul,
    Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hd0
  obtain ⟨c, hc⟩ := hd0
  have h1 : fontaineTheta O p d * (p : O) ^ (n + 1) = 0 := by
    have h' := congrArg (fontaineTheta O p) hc
    simp only [map_mul, map_sub, map_pow, map_natCast, theta_xi p O hv ε hε] at h'
    linear_combination -h'
  have h2 : fontaineTheta O p d = 0 := (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ hp0)
  have h3 : d ∈ RingHom.ker (fontaineTheta O p) := h2
  rw [ker_theta p O hv ε hε, Ideal.mem_span_singleton'] at h3
  obtain ⟨e0, rfl⟩ := h3
  have h4 : (y - (e0 * (p : A p O) ^ (n + 1) - c * xi p O ε)) * xi p O ε = 0 := by
    linear_combination hc
  have h5 := xi_nzd p O hv ε hε _ h4
  rw [sub_eq_zero] at h5
  rw [h5, Ideal.mem_span_singleton']
  refine ⟨-(Ideal.Quotient.mk _ (Ideal.Quotient.mk _ c)), ?_⟩
  simp only [xiR, RingHom.map_sub, map_mul, map_pow, map_natCast, hpR', mul_zero, zero_sub, neg_mul]

def zv (n : ℕ) : R'n p O ε n :=
  Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (teichmuller p (root p O ε (n + 1))))

def nuR (n : ℕ) : R'n p O ε n := Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (nu p O ε))

lemma zv_pow (n : ℕ) :
    zv p O ε n ^ p ^ (n + 1) = 1 + nuR p O ε n * xiR p O ε n := by
  unfold zv nuR xiR
  rw [← map_pow, ← map_pow, ← map_pow, root_pow, teich_eps p O hv ε hε, map_add (f := _), map_add (f := _), map_one,
    map_one, map_mul, map_mul]

lemma zv_unit (n : ℕ) : IsUnit (zv p O ε n) := by
  have hne : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  refine (isUnit_pow_iff hne).1 ?_
  rw [zv_pow p O hv ε hε n]
  exact one_add_unit _ _ (xi_sq' p O hv ε hε n)

def zetaV (n : ℕ) : O := fontaineTheta O p (teichmuller p (root p O ε (n + 1)))

lemma zeta_unit (n : ℕ) : IsUnit (zetaV p O ε n) := by
  have hne : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have h : zetaV p O ε n ^ p ^ (n + 1) = 1 := by
    unfold zetaV
    rw [← map_pow, ← map_pow, root_pow, teich_eps p O hv ε hε, map_add (f := _), map_one, map_mul,
      theta_xi p O hv ε hε, mul_zero, add_zero]
  refine IsUnit.of_mul_eq_one (zetaV p O ε n ^ (p ^ (n + 1) - 1)) ?_
  rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hne), h]

def LO : LAlg (R0 p O ε) := { carrier := O, alg := algO p O hv ε hε, loc := O_local O hv }

def LR (n : ℕ) : LAlg (R0 p O ε) :=
  { carrier := Rn p O n, alg := algRn p O hv ε hε n, loc := Rn_local p O hv n }

def LR' (n : ℕ) : LAlg (R0 p O ε) := { carrier := R'n p O ε n, loc := R'n_local p O hv ε hε n }

lemma q_surj (n : ℕ) : Function.Surjective (Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})) := by
  exact Ideal.Quotient.mk_surjective

def ainfTower : ATower (R0 p O ε) p where
  O := LO p O hv ε hε
  R' n := LR' p O hv ε hε n
  R n := LR p O hv ε hε n
  π n := ⟨{ toRingHom := piRing p O hv ε hε n, commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (piRing_surj p O hv ε hε n)⟩
  q n := ⟨{ toRingHom := Ideal.Quotient.mk (span {(p : O) ^ (n + 1)}), commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (q_surj p O hv ε hε n)⟩
  ξ n := xiR p O ε n
  surj n := piRing_surj p O hv ε hε n
  ker_eq n := ker_pi p O hv ε hε n
  ξ_sq n := xi_sq' p O hv ε hε n
  ann n a ha := ann' p O hv ε hε n a ha
  char n := by rw [Nat.cast_pow]; exact hpR' p O ε n
  sep a ha := sepO p O a fun n =>
    (Ideal.Quotient.eq_zero_iff_mem (I := span {(p : O) ^ (n + 1)})).1 (ha n)
  c := fontaineTheta O p (nu p O ε)
  cp n := nuR p O ε n
  cp_spec n := rfl
  zh n := (zv_unit p O hv ε hε n).unit
  zh_pow n := by rw [IsUnit.unit_spec]; exact zv_pow p O hv ε hε n
  ζ n := (zeta_unit p O hv ε hε n).unit
  ζ_spec n := by rw [IsUnit.unit_spec, IsUnit.unit_spec]; rfl

theorem ainfTower_isDomain : IsDomain ((ainfTower p O hv ε hε).O : Type) := by
  show IsDomain O
  exact Function.Injective.isDomain (algebraMap O C) hv.hom_inj

end Ainf

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.DualPairInh
section
noncomputable section

open Polynomial

namespace ReciprocityTheory.PGsh

namespace DualNum

variable {R₀ : Type} [CommRing R₀] (R : LAlg R₀)

abbrev DN := (R : Type)[X] ⧸ Ideal.span {(X : (R : Type)[X]) ^ 2}

def ev : DN R →+* (R : Type) :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom 0) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp)

lemma ev_mk (f : (R : Type)[X]) : ev R (Ideal.Quotient.mk _ f) = f.eval 0 := rfl

lemma ev_surj : Function.Surjective (ev R) := fun r => ⟨Ideal.Quotient.mk _ (C r), by rw [ev_mk, eval_C]⟩

def eta : DN R := Ideal.Quotient.mk _ X

lemma eta_sq : eta R * eta R = 0 := by
  unfold eta
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_two]
  exact Ideal.mem_span_singleton_self _

lemma ker_ev : RingHom.ker (ev R) = Ideal.span {eta R} := by
  apply le_antisymm
  · intro y hy
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker, ev_mk] at hy
    have hX : (X : (R : Type)[X]) ∣ f := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
      exact hy
    obtain ⟨g, rfl⟩ := hX
    rw [map_mul]
    exact Ideal.mem_span_singleton.2 (dvd_mul_right (eta R) _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show ev R (eta R) = 0
    rw [eta, ev_mk, eval_X]

lemma isLocal : IsLocalRing (DN R) := by
  have hnt : Nontrivial (DN R) := (ev R).domain_nontrivial
  have hunit : ∀ y : DN R, IsUnit (ev R y) → IsUnit y := by
    intro y hy
    obtain ⟨u, hu⟩ : ∃ u : DN R, u = Ideal.Quotient.mk _ (C (ev R y)) := ⟨_, rfl⟩
    have hev : ev R u = ev R y := by rw [hu, ev_mk, eval_C]
    have hk : y - u ∈ RingHom.ker (ev R) := by rw [RingHom.mem_ker, map_sub, hev, sub_self]
    rw [ker_ev, Ideal.mem_span_singleton] at hk
    obtain ⟨c, hc⟩ := hk
    have hn : IsNilpotent (y - u) := ⟨2, by rw [hc, mul_pow, pow_two (eta R), eta_sq, zero_mul]⟩
    have hu' : IsUnit u := by
      have e : u = ((Ideal.Quotient.mk _).comp Polynomial.C) (ev R y) := hu
      rw [e]
      exact hy.map _
    have h := hn.isUnit_add_left_of_commute hu' (Commute.all _ _)
    rwa [add_sub_cancel] at h
  exact IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    (IsLocalRing.isUnit_or_isUnit_one_sub_self (ev R a)).imp (hunit a)
      fun h => hunit (1 - a) (by rwa [map_sub, map_one])

lemma ev_algebraMap (r : (R : Type)) : ev R (algebraMap (R : Type) (DN R) r) = r := by
  rw [← Ideal.Quotient.mk_algebraMap, ev_mk]
  simp

def evAlg : DN R →ₐ[R₀] (R : Type) :=
  { ev R with
    commutes' := fun r => by
      show ev R (algebraMap R₀ (DN R) r) = _
      rw [← Ideal.Quotient.mk_algebraMap, ev_mk, Polynomial.algebraMap_apply, eval_C] }

def D : LAlg R₀ := { carrier := DN R, loc := isLocal R }

def dualPair : DualPair R where
  D := D R
  π := ⟨evAlg R, TowerExample.isLocalHom_of_surj _ (ev_surj R)⟩
  σ := ⟨IsScalarTower.toAlgHom R₀ (R : Type) (DN R),
    ⟨fun r hr => by
      have h := hr.map (ev R)
      have e : ev R ((IsScalarTower.toAlgHom R₀ (R : Type) (DN R) : (R : Type) →+* DN R) r) = r :=
        ev_algebraMap R r
      convert h using 1
      exact e.symm⟩⟩
  η := eta R
  sect r := ev_algebraMap R r
  η_sq := eta_sq R
  ker_eq := ker_ev R
  free r h := by
    change algebraMap (R : Type) (DN R) r * eta R = 0 at h
    rw [← Ideal.Quotient.mk_algebraMap, eta, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, X_pow_dvd_iff] at h
    have h1 := h 1 (by norm_num)
    simpa [Polynomial.algebraMap_apply] using h1

end DualNum

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.MonomialsSpanOfProdEq
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Basis

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

private lemma col_mem_span {X : Type} [Fintype X] (B' : Matrix X X C) (V : Matrix X X R) (j : X) :
    (fun x => (B' * V.map (algebraMap R C)) x j) ∈
      Submodule.span R (Set.range fun α x => B' x α) := by
  have e : (fun x => (B' * V.map (algebraMap R C)) x j) = ∑ α, V α j • (fun x => B' x α) := by
    ext x
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  rw [e]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

private lemma exists_factor {X : Type} [Fintype X] (B B' : Matrix X X C)
    (h : ∀ α, (fun x => B' x α) ∈ Submodule.span R (Set.range fun j x => B x j)) :
    ∃ W : Matrix X X R, B' = B * W.map (algebraMap R C) := by
  choose c hc using fun α => (Submodule.mem_span_range_iff_exists_fun R).1 (h α)
  refine ⟨Matrix.of fun j α => c α j, ?_⟩
  ext x α
  have h1 := congrFun (hc α) x
  simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at h1
  rw [Matrix.mul_apply, ← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

private lemma prod_pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {ι : Type} [Fintype ι] (f : ι → N → C)
    (hf : ∀ j, f j ∈ A.carrier) (n : ι → ℕ) : (fun y => ∏ j, f j y ^ n j) ∈ A.carrier := by
  have hpow : ∀ j k, f j ^ k ∈ A.carrier := by
    intro j k
    induction k with
    | zero => simpa using A.one_mem
    | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih (hf j)
  have : (fun y => ∏ j, f j y ^ n j) = ∏ j, f j ^ n j := by
    ext y; simp [Finset.prod_apply]
  rw [this]
  exact Finset.prod_induction _ (· ∈ A.carrier) (fun a b ha hb => A.mul_mem a b ha hb)
    A.one_mem (fun j _ => hpow j (n j))

private lemma hasLen_om {p : ℕ} [Fact p.Prime] {g : ℕ} {v : Valuation C NNReal} [Algebra ℤ_[p] R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
    (H : HodgeTateDatum p g v R O σ cp) :
    HasLen v R (OmAA H.AA.carrier) (v (algebraMap R C (p : R)) ^ g) := by
  refine ⟨g, fun _ => (p : R), ⟨?_⟩, by simp⟩
  exact (Submodule.quotEquivOfEq _ _ H.cotangent_ker_eq.symm).trans
    ((LinearMap.quotKerEquivOfSurjective H.φ H.cotangent_surjective).trans (PullbackHopfOrder.qPi p g))

private lemma exp_eq (p g : ℕ) :
    g * (p ^ (g + g - 1) * (p * (p - 1) / 2)) * 2 = (p - 1) * g * p ^ (g + g) := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  have h2 : p * (p - 1) / 2 * 2 = p * (p - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd
  have h3 : p ^ (g + g - 1) * p = p ^ (g + g) := by
    rw [← pow_succ]
    congr 1
    omega
  calc g * (p ^ (g + g - 1) * (p * (p - 1) / 2)) * 2 = g * p ^ (g + g - 1) * (p * (p - 1) / 2 * 2) := by ring
    _ = g * p ^ (g + g - 1) * (p * (p - 1)) := by rw [h2]
    _ = (p - 1) * g * (p ^ (g + g - 1) * p) := by ring
    _ = (p - 1) * g * p ^ (g + g) := by rw [h3]

end Basis

theorem monomials_span_of_prod_eq : EigenLiftsBasisStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H U X hprod D
  classical
  have hv := hS.integers
  have hp1 : v (p : C) < 1 := by simpa [map_natCast] using hS.p_lt

  let B' : Matrix (Nb p g) (Nb p g) C := Matrix.of fun (x α : Nb p g) =>
    ∏ j, (algebraMap R C (D.ε j) * D.u j x) ^ (α j).val
  have hB'v : v B'.det = ∏ j, v (algebraMap R C (D.ε j)) ^
      (p ^ (Fintype.card (Ix g) - 1) * (p * (p - 1) / 2)) :=
    (u5 p C v R hv hp1 (Ix g) D.Λ D.u D.Λ_det D.u_int D.u_cong).2 fun j => algebraMap R C (D.ε j)
  have hε : ∏ j, v (algebraMap R C (D.ε j)) = v (algebraMap R C cp) ^ g := by
    rw [← Finset.prod_fiberwise Finset.univ D.κ, ← hprod]
    exact Finset.prod_congr rfl fun i _ => D.ε_prod i
  have hcard : Fintype.card (Nb p g) = p ^ (g + g) := by
    simp [ZMod.card, Fintype.card_sum, Fintype.card_fin]
  have hsq : v B'.det ^ 2 = (v (algebraMap R C (p : R)) ^ g) ^ Fintype.card (Nb p g) := by
    rw [hB'v, Finset.prod_pow, hε, ← hS.cp_val, hcard]
    simp only [Fintype.card_sum, Fintype.card_fin, ← pow_mul]
    congr 1
    exact exp_eq p g

  obtain ⟨B, hBu, hAA⟩ := H.AA.lat
  have hcol : HasColen R v H.AA.carrier (v B.det) := ⟨B, hAA, rfl⟩
  have hN : ∀ x : Nb p g, p • x = 0 := by
    intro x; ext i; simp
  have hdeg := u4 p C v R hv hp1 (Nb p g) hN H.AA (v B.det) _ hcol (hasLen_om H)

  have hmem : ∀ α : Nb p g, (fun x => B' x α) ∈ H.AA.carrier := by
    intro α
    exact prod_pow_mem H.AA (fun j y => algebraMap R C (D.ε j) * D.u j y)
      (fun j => (Submodule.mem_inf.1 (D.x_mem j)).1) (fun j => (α j).val)
  obtain ⟨W, hW⟩ := exists_factor B B' (fun α => hAA ▸ hmem α)
  have hdet : v B'.det = v B.det * v (algebraMap R C W.det) := by
    rw [hW, Matrix.det_mul, map_mul, RingHom.map_det]; rfl
  have ha : v B.det ≠ 0 := (Valuation.ne_zero_iff v).2 hBu.ne_zero
  have hw1 : v (algebraMap R C W.det) ≤ 1 := hv.map_le_one W.det
  have hw : v (algebraMap R C W.det) = 1 := by
    by_contra hne
    have hlt : v (algebraMap R C W.det) < 1 := lt_of_le_of_ne hw1 hne
    have hpos : 0 < v B.det ^ 2 := pow_pos (pos_iff_ne_zero.2 ha) 2
    have : v B'.det ^ 2 < v B.det ^ 2 := by
      rw [hdet, mul_pow]
      exact mul_lt_of_lt_one_right hpos (pow_lt_one₀ zero_le hlt two_ne_zero)
    rw [hsq] at this
    exact absurd hdeg (not_le.2 this)
  have hWu : IsUnit W.det :=
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hw) hw
  have hBeq : B' * (W⁻¹).map (algebraMap R C) = B := by
    rw [hW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hWu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have hspan : Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val) =
      Submodule.span R (Set.range fun α x => B' x α) := rfl
  rw [hspan]
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [hAA]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have := col_mem_span B' (W⁻¹) j
    rwa [hBeq] at this
  · rintro _ ⟨α, rfl⟩
    exact hmem α

end ReciprocityTheory.PGsh.Up
end
end

