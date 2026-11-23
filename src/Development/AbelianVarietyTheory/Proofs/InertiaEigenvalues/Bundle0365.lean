module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerDistinguishedSpanIsPrimeAndNotMem
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProductOrientedBoundedPrisms
section
noncomputable section

namespace GlobalTheory.Prism

theorem pi_mem_iff_forall_mem_map_eval {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type}
    [∀ i, CommRing (A i)] (K : Ideal (∀ i, A i)) (y : ∀ i, A i) :
    y ∈ K ↔ ∀ i, y i ∈ K.map (Pi.evalRingHom A i) := by
  refine ⟨fun h i => Ideal.mem_map_of_mem _ h, fun h => ?_⟩
  rw [← Finset.univ_sum_single y]
  refine Ideal.sum_mem _ fun i _ => ?_
  obtain ⟨x, hx, hxi⟩ := (Ideal.mem_map_iff_of_surjective _
    (fun b => ⟨Pi.single i b, by simp⟩ : Function.Surjective (Pi.evalRingHom A i))).1 (h i)
  have e : Pi.single i (y i) = Pi.single i 1 * x := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [← hxi]
    · simp [hj]
  rw [e]; exact K.mul_mem_left _ hx

theorem smodEq_smul_top_iff {B : Type} [CommRing B] (K : Ideal B) (x y : B) :
    x ≡ y [SMOD (K • ⊤ : Submodule B B)] ↔ x - y ∈ K := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem mem_nonZeroDivisors_of_invertible_span {A : Type} [CommRing A] {q : A}
    (h : Module.Invertible A ↥(Ideal.span {q})) : q ∈ nonZeroDivisors A := by
  have key : ∀ x : A, x * q = 0 → x = 0 := by
    intro x hx
    apply (Module.Invertible.toModuleEnd_bijective A ↥(Ideal.span {q})).1
    ext ⟨m, hm⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hm
    simp
    linear_combination c * hx
  exact mem_nonZeroDivisors_iff.2 ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

def Delta.pi {l : ℕ} {ι : Type} {A : ι → Type} [∀ i, CommRing (A i)] (D : ∀ i, Delta l (A i)) :
    Delta l (∀ i, A i) where
  δ a i := (D i).δ (a i)
  δ_one := funext fun i => by simpa using (D i).δ_one
  δ_mul a b := funext fun i => by simpa using (D i).δ_mul (a i) (b i)
  δ_add a b := funext fun i => by simpa [Finset.sum_apply] using (D i).δ_add (a i) (b i)
  φ := RingHom.pi fun i => (D i).φ.comp (Pi.evalRingHom A i)
  φ_eq a := funext fun i => (D i).φ_eq (a i)

variable {l : ℕ} {R : Type} [CommRing R] {ι : Type} [Fintype ι]

theorem pi_mem_span_iff (C : ι → Obj l R) (t : ∀ i, (C i).A)
    (ht : ∀ i, (C i).I = Ideal.span {t i}) (x : ∀ i, (C i).A) :
    x ∈ Ideal.span {t} ↔ ∀ i, x i ∈ (C i).I := by
  classical
  rw [pi_mem_iff_forall_mem_map_eval]
  simp [Ideal.map_span, ht]

theorem pi_mem_nonZeroDivisors (C : ι → Obj l R) (t : ∀ i, (C i).A)
    (ht : ∀ i, (C i).I = Ideal.span {t i}) : t ∈ nonZeroDivisors (∀ i, (C i).A) := by
  have hz : ∀ i, t i ∈ nonZeroDivisors (C i).A := fun i =>
    mem_nonZeroDivisors_of_invertible_span (ht i ▸ (C i).inv)
  refine mem_nonZeroDivisors_iff.2 ⟨fun x hx => funext fun i => ?_, fun x hx => funext fun i => ?_⟩
  · exact (mem_nonZeroDivisors_iff.1 (hz i)).1 (x i) (congrFun hx i)
  · exact (mem_nonZeroDivisors_iff.1 (hz i)).2 (x i) (congrFun hx i)

theorem pi_isAdicComplete (C : ι → Obj l R) (t : ∀ i, (C i).A)
    (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    IsAdicComplete (Ideal.span {((l : ℕ) : ∀ i, (C i).A)} ⊔ Ideal.span {t}) (∀ i, (C i).A) := by
  classical
  have hJ : ∀ (m : ℕ) (y : ∀ i, (C i).A),
      y ∈ (Ideal.span {((l : ℕ) : ∀ i, (C i).A)} ⊔ Ideal.span {t}) ^ m ↔
        ∀ i, y i ∈ (Ideal.span {((l : ℕ) : (C i).A)} ⊔ (C i).I) ^ m := by
    intro m y
    rw [pi_mem_iff_forall_mem_map_eval]
    simp [Ideal.map_pow, Ideal.map_sup, Ideal.map_span, ht]
  refine { haus' := fun x hx => funext fun i => ?_, prec' := fun f hf => ?_ }
  · refine (C i).complete.toIsHausdorff.haus' (x i) fun n => ?_
    rw [smodEq_smul_top_iff]
    have := (hJ n _).1 ((smodEq_smul_top_iff _ _ _).1 (hx n)) i
    simpa using this
  · choose L hL using fun i => (C i).complete.toIsPrecomplete.prec' (fun n => f n i)
      (fun {m n} hmn => (smodEq_smul_top_iff _ _ _).2 (by
        have := (hJ m _).1 ((smodEq_smul_top_iff _ _ _).1 (hf hmn)) i
        simpa using this))
    exact ⟨fun i => L i, fun n => (smodEq_smul_top_iff _ _ _).2 ((hJ n _).2 fun i => by
      simpa using (smodEq_smul_top_iff _ _ _).1 (hL i n))⟩

theorem pi_l_mem (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    ((l : ℕ) : ∀ i, (C i).A) ∈ Ideal.span {t} ⊔ (Ideal.span {t}).map (Delta.pi fun i => (C i).D).φ := by
  have h : ∀ i, ∃ a b : (C i).A, a * t i + b * (C i).D.φ (t i) = (l : (C i).A) := by
    intro i
    have := (C i).l_mem
    rw [ht i, Ideal.map_span, Set.image_singleton, Submodule.mem_sup] at this
    obtain ⟨y, hy, z, hz, e⟩ := this
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨a, b, e⟩
  choose a b hab using h
  rw [Submodule.mem_sup]
  refine ⟨a * t, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _),
    b * (Delta.pi fun i => (C i).D).φ t,
    Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)),
    funext fun i => ?_⟩
  exact hab i

theorem quot_natCast_pow_mul_eq_zero_iff {B : Type} [CommRing B] (K : Ideal B) (l m : ℕ) (a : B) :
    ((l : B ⧸ K)) ^ m * Ideal.Quotient.mk K a = 0 ↔ (l : B) ^ m * a ∈ K := by
  rw [← map_natCast (Ideal.Quotient.mk K), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

theorem pi_bdd (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    ∃ N : ℕ, ∀ x : (∀ i, (C i).A) ⧸ Ideal.span {t},
      (∃ m : ℕ, ((l : ℕ) : (∀ i, (C i).A) ⧸ Ideal.span {t}) ^ m * x = 0) →
        ((l : ℕ) : (∀ i, (C i).A) ⧸ Ideal.span {t}) ^ N * x = 0 := by
  choose n hn using fun i => (C i).bdd
  refine ⟨Finset.univ.sup n, fun x ⟨m, hm⟩ => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quot_natCast_pow_mul_eq_zero_iff, pi_mem_span_iff C t ht] at hm ⊢
  intro i
  have h1 := hn i (Ideal.Quotient.mk _ (a i)) ⟨m, (quot_natCast_pow_mul_eq_zero_iff _ _ _ _).2
    (by simpa using hm i)⟩
  rw [quot_natCast_pow_mul_eq_zero_iff] at h1
  have hle : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  have e : ((l : ℕ) : ∀ i, (C i).A) ^ Finset.univ.sup n * a =
      ((l : ℕ) : ∀ i, (C i).A) ^ (Finset.univ.sup n - n i) * (((l : ℕ) : ∀ i, (C i).A) ^ n i * a) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  rw [e]
  simpa using Ideal.mul_mem_left _ ((l : (C i).A) ^ (Finset.univ.sup n - n i)) h1

end GlobalTheory.Prism

namespace GlobalTheory.Prism

variable {l : ℕ} {R : Type} [CommRing R] {ι : Type} [Fintype ι]

def piQuotMap (C : ι → Obj l R) : (∀ i, (C i).A) →+* ∀ i, (C i).A ⧸ (C i).I :=
  RingHom.pi fun i => (Ideal.Quotient.mk (C i).I).comp (Pi.evalRingHom _ i)

theorem piQuotMap_surjective (C : ι → Obj l R) : Function.Surjective (piQuotMap C) := fun y =>
  ⟨fun i => (Ideal.Quotient.mk_surjective (y i)).choose,
    funext fun i => (Ideal.Quotient.mk_surjective (y i)).choose_spec⟩

theorem piQuotMap_ker (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    RingHom.ker (piQuotMap C) = Ideal.span {t} := by
  ext x
  rw [RingHom.mem_ker, pi_mem_span_iff C t ht, funext_iff]
  exact forall_congr' fun i => Ideal.Quotient.eq_zero_iff_mem

def piQuotEquiv (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    (∀ i, (C i).A) ⧸ Ideal.span {t} ≃+* ∀ i, (C i).A ⧸ (C i).I :=
  (Ideal.quotEquivOfEq (piQuotMap_ker C t ht).symm).trans
    (RingHom.quotientKerEquivOfSurjective (piQuotMap_surjective C))

theorem piQuotEquiv_mk (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i})
    (a : ∀ i, (C i).A) :
    piQuotEquiv C t ht (Ideal.Quotient.mk _ a) = fun i => Ideal.Quotient.mk (C i).I (a i) := rfl

def Obj.pi (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    Obj l R where
  A := ∀ i, (C i).A
  D := Delta.pi fun i => (C i).D
  I := Ideal.span {t}
  inv := invertible_span_singleton (pi_mem_nonZeroDivisors C t ht)
  complete := pi_isAdicComplete C t ht
  l_mem := pi_l_mem C t ht
  bdd := pi_bdd C t ht
  str := (piQuotEquiv C t ht).symm.toRingHom.comp (RingHom.pi fun i => (C i).str)

theorem piQuotEquiv_str (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i})
    (r : R) : piQuotEquiv C t ht ((Obj.pi C t ht).str r) = fun i => (C i).str r :=
  (piQuotEquiv C t ht).apply_symm_apply (fun i => (C i).str r)

def Hom.piEval (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i})
    (i : ι) : Hom (Obj.pi C t ht) (C i) where
  f := Pi.evalRingHom (fun i => (C i).A) i
  f_δ _ := rfl
  f_I a h := (pi_mem_span_iff C t ht a).1 h i
  f_str r a h := by
    have := congrArg (piQuotEquiv C t ht) h
    exact congrFun ((piQuotEquiv_mk C t ht a).symm.trans (this.trans (piQuotEquiv_str C t ht r))) i

def Hom.piLift (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i})
    (Z : Obj l R) (a : ∀ i, Hom Z (C i)) : Hom Z (Obj.pi C t ht) where
  f := RingHom.pi fun i => (a i).f
  f_δ z := funext fun i => (a i).f_δ z
  f_I z hz := (pi_mem_span_iff C t ht _).2 fun i => (a i).f_I z hz
  f_str r z h := (piQuotEquiv C t ht).injective ((piQuotEquiv_mk C t ht _).trans
    ((funext fun i => (a i).f_str r z h).trans (piQuotEquiv_str C t ht r).symm))

end GlobalTheory.Prism

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.Prism.finite_product_oriented : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (n : ℕ) (C : Fin n → Obj l R), (∀ i, ∃ t, (C i).I = Ideal.span {t}) → ∃ (Q : Obj l R) (π : ∀ i, Hom Q (C i)), Function.Bijective (fun (x : Q.A) (i : Fin n) => (π i).f x) ∧ (∀ x, x ∈ Q.I ↔ ∀ i, (π i).f x ∈ (C i).I) ∧ ∀ (Z : Obj l R) (a : ∀ i, Hom Z (C i)), ∃ c : Hom Z Q, ∀ i, (π i).comp c = a i := by
  intro l _ R _ n C hC
  choose t ht using hC
  exact ⟨Obj.pi C t ht, fun i => Hom.piEval C t ht i,
    ⟨fun x y h => funext fun i => congrFun h i, fun y => ⟨y, rfl⟩⟩,
    fun x => pi_mem_span_iff C t ht x,
    fun Z a => ⟨Hom.piLift C t ht Z a, fun i => Hom.ext' (RingHom.ext fun _ => rfl)⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProjectiveLiftOfIsAdicComplete
section
open GlobalTheory.Prism

namespace GlobalTheory.BSP.LiftProj

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_mem {I J : Ideal A} {x y : Matrix n n A} (hx : ∀ i j, x i j ∈ I) (hy : ∀ i j, y i j ∈ J)
    (i j : n) : (x * y) i j ∈ I * J := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hx i k) (hy k j)

theorem mul_mem_right {I : Ideal A} {x : Matrix n n A} (y : Matrix n n A) (hx : ∀ i j, x i j ∈ I)
    (i j : n) : (x * y) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hx i k)

theorem mul_mem_left {I : Ideal A} {y : Matrix n n A} (x : Matrix n n A) (hy : ∀ i j, y i j ∈ I)
    (i j : n) : (x * y) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy k j)

theorem exists_idem (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (x : Matrix n n A)
    (hx : ∀ i j, (x * x - x) i j ∈ 𝔞) :
    ∃ e : Matrix n n A, e * e = e ∧ ∀ i j, (e - x) i j ∈ 𝔞 := by
  let f : ℕ → Matrix n n A := fun k => Nat.rec x (fun _ y => 3 * (y * y) - 2 * (y * y * y)) k
  have f0 : f 0 = x := rfl
  have fs : ∀ k, f (k + 1) = 3 * (f k * f k) - 2 * (f k * f k * f k) := fun k => rfl
  have h1 : ∀ k i j, (f k * f k - f k) i j ∈ 𝔞 ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa [f0] using hx
    | succ k ih =>
      have e : f (k + 1) * f (k + 1) - f (k + 1) =
          ((f k * f k - f k) * (f k * f k - f k)) * (4 * (f k * f k) - 4 * f k - 3) := by
        rw [fs]; noncomm_ring
      intro i j
      rw [e]
      refine mul_mem_right _ (fun i j => ?_) i j
      have := mul_mem ih ih i j
      rw [← pow_add] at this
      exact Ideal.pow_le_pow_right (by omega) this
  have h2 : ∀ k i j, (f (k + 1) - f k) i j ∈ 𝔞 ^ (k + 1) := by
    intro k i j
    have e : f (k + 1) - f k = (f k * f k - f k) * (1 - 2 * f k) := by
      rw [fs]; noncomm_ring
    rw [e]
    exact mul_mem_right _ (h1 k) i j
  have h3 : ∀ k m, k ≤ m → ∀ i j, (f m - f k) i j ∈ 𝔞 ^ (k + 1) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => intro i j; simp
    | succ m hkm ih =>
      intro i j
      have e : f (m + 1) - f k = (f (m + 1) - f m) + (f m - f k) := by abel
      rw [e, Matrix.add_apply]
      exact add_mem (Ideal.pow_le_pow_right (by omega) (h2 m i j)) (ih i j)
  have h4 : ∀ i j, ∃ L : A, ∀ k, f k i j - L ∈ 𝔞 ^ k := by
    intro i j
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := 𝔞) (fun k => f k i j) (fun {k m} hkm => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
      exact Ideal.pow_le_pow_right (Nat.le_succ k) (h3 k m hkm i j))
    refine ⟨L, fun k => ?_⟩
    have := hL k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using h4
  let e : Matrix n n A := Matrix.of L
  have hL' : ∀ k i j, (f k - e) i j ∈ 𝔞 ^ k := fun k i j => hL i j k
  refine ⟨e, ?_, fun i j => ?_⟩
  · rw [← sub_eq_zero]
    ext i j
    refine IsHausdorff.haus' (I := 𝔞) _ fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have e1 : e * e - e = (f k * f k - f k) - ((f k - e) * (f k - 1) + e * (f k - e)) := by
      noncomm_ring
    rw [e1, Matrix.sub_apply, Matrix.add_apply]
    exact sub_mem (Ideal.pow_le_pow_right (Nat.le_succ k) (h1 k i j))
      (add_mem (mul_mem_right _ (hL' k) i j) (mul_mem_left _ (hL' k) i j))
  · have e1 : e - x = (f 1 - f 0) - (f 1 - e) := by rw [f0]; abel
    rw [e1, Matrix.sub_apply]
    have a := h2 0 i j
    have b := hL' 1 i j
    rw [zero_add, pow_one] at a
    rw [pow_one] at b
    exact sub_mem a b

theorem exists_idem_lift (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (y : Matrix n n (A ⧸ 𝔞))
    (hy : y * y = y) :
    ∃ e : Matrix n n A, e * e = e ∧ e.map (Ideal.Quotient.mk 𝔞) = y := by
  choose g hg using Ideal.Quotient.mk_surjective (I := 𝔞)
  have hxy : (y.map g).map (Ideal.Quotient.mk 𝔞) = y := by
    ext i j; simp [hg]
  obtain ⟨e, he, hex⟩ := exists_idem 𝔞 (y.map g) fun i j => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : (Ideal.Quotient.mk 𝔞).mapMatrix (y.map g * y.map g - y.map g) = 0 := by
      rw [map_sub, map_mul, RingHom.mapMatrix_apply, hxy, hy, sub_self]
    exact congrFun (congrFun this i) j
  refine ⟨e, he, ?_⟩
  ext i j
  have := (Ideal.Quotient.eq).2 (hex i j)
  simpa [hg] using this

theorem exists_lift : ∀ (A : Type) [CommRing A] (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (N : Type)
    [AddCommGroup N] [Module (A ⧸ 𝔞) N] [Module.Finite (A ⧸ 𝔞) N] [Module.Projective (A ⧸ 𝔞) N],
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module A P) (_ : Module.Finite A P)
      (_ : Module.Projective A P) (u : P →ₛₗ[Ideal.Quotient.mk 𝔞] N), SemiBC u := by
  intro A _ 𝔞 _ N _ _ _ _
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' (A ⧸ 𝔞) N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  have hs' : ∀ z, p (s z) = z := fun z => LinearMap.congr_fun hs z
  obtain ⟨e, he, hey⟩ := exists_idem_lift 𝔞 (LinearMap.toMatrix' (s ∘ₗ p)) (by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    ext1 z
    ext1
    simp [hs'])
  let red : (Fin n → A) →ₛₗ[Ideal.Quotient.mk 𝔞] (Fin n → A ⧸ 𝔞) :=
    { toFun := fun z i => Ideal.Quotient.mk 𝔞 (z i)
      map_add' := fun a b => by ext i; simp
      map_smul' := fun a b => by ext i; simp }
  have red_surj : Function.Surjective red := fun z => by
    choose g hg using Ideal.Quotient.mk_surjective (I := 𝔞)
    exact ⟨fun i => g (z i), funext fun i => hg (z i)⟩
  let E : (Fin n → A) →ₗ[A] (Fin n → A) := Matrix.toLin' e
  have hEE : ∀ z, E (E z) = E z := fun z => by
    simp only [E, Matrix.toLin'_apply, Matrix.mulVec_mulVec, he]
  have hred : ∀ z, red (E z) = s (p (red z)) := fun z => by
    have h1 : s (p (red z)) = Matrix.toLin' (LinearMap.toMatrix' (s ∘ₗ p)) (red z) := by
      rw [Matrix.toLin'_toMatrix']; rfl
    rw [h1, ← hey]
    ext i
    simp [red, E, Matrix.mulVec, dotProduct]
  let P := LinearMap.range E
  let q : (Fin n → A) →ₗ[A] P := E.rangeRestrict
  have hq : ∀ y : P, q y = y := by
    rintro ⟨_, z, rfl⟩
    exact Subtype.ext (hEE z)
  have hproj : Module.Projective A P := Module.Projective.of_split P.subtype q (LinearMap.ext hq)
  let u : P →ₛₗ[Ideal.Quotient.mk 𝔞] N := p.comp (red.comp P.subtype)
  have hu : ∀ y : P, u y = p (red y) := fun y => rfl
  have u_surj : Function.Surjective u := fun z => by
    obtain ⟨t, ht⟩ := red_surj (s z)
    refine ⟨q t, ?_⟩
    rw [hu]
    change p (red (E t)) = z
    rw [hred, ht, hs', hs']
  refine ⟨P, inferInstance, inferInstance, inferInstance, hproj, u, ?_⟩
  intro Q _ _ v
  let w0 : (Fin n → A ⧸ 𝔞) →ₗ[A ⧸ 𝔞] Q :=
    (Pi.basisFun (A ⧸ 𝔞) (Fin n)).constr ℕ fun i => v (q (Pi.single i 1))
  have hw0 : w0.comp red = v.comp q := by
    refine (Pi.basisFun A (Fin n)).ext fun i => ?_
    have : red (Pi.basisFun A (Fin n) i) = Pi.basisFun (A ⧸ 𝔞) (Fin n) i := by
      ext j
      by_cases h : j = i
      · subst h; simp [red]
      · simp [red, h]
    rw [LinearMap.comp_apply, this, LinearMap.comp_apply, Pi.basisFun_apply A]
    exact Module.Basis.constr_basis _ _ _ _
  have key : ∀ y : P, (w0 ∘ₗ s) (u y) = v y := fun y => by
    have h1 : E y = y := congrArg Subtype.val (hq y)
    rw [hu, LinearMap.comp_apply, ← hred, h1]
    have := LinearMap.congr_fun hw0 (y : Fin n → A)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hq] at this
    exact this
  refine ⟨w0 ∘ₗ s, key, fun w hw => ?_⟩
  ext z
  obtain ⟨y, rfl⟩ := u_surj z
  rw [hw, key]

end GlobalTheory.BSP.LiftProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveMapIntegersClToWittQuotient
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem dvd_pow_of_ne_zero_untilt (l : ℕ) [Fact l.Prime] (y : Formalism.Per.OC l) (hy : y ≠ 0) :
    ∃ n : ℕ, y ∣ (l : Formalism.Per.OC l) ^ n := by
  have hy' : (y : ℂ_[l]) ≠ 0 := fun h => hy (Subtype.ext h)
  have hpos : 0 < ‖(y : ℂ_[l])‖ := norm_pos_iff.2 hy'
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (GlobalTheory.RingBasics.norm_p_lt (p := l))
  refine ⟨n, ⟨(l : ℂ_[l]) ^ n / y, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div, norm_pow, div_le_one hpos]
    exact hn.le
  · push_cast
    exact (mul_div_cancel₀ _ hy').symm

theorem constantCoeff_natCast_untilt (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [CharP O l] :
    WittVector.constantCoeff ((l : ℕ) : WittVector l O) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

theorem exists_untilt_map : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∃ θ' : OC l →+* (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}), (∀ a : Ainf l, θ' (Per.θ l a) = Ideal.Quotient.mk _ (WittVector.map ψ a)) ∧ Function.Injective θ' ∧ IsDomain (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) ∧ ∀ a : WittVector l O, ((l : ℕ) : WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) ∣ Ideal.Quotient.mk _ a → ψ bk.flat ^ bk.Ep.natDegree ∣ a.coeff 0 := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc
  obtain ⟨w, hw, hE⟩ := _root_.GlobalTheory.BSP.EisImage.map_E_eq l K bk O ψ hu
  obtain ⟨hp, hl⟩ := _root_.GlobalTheory.teichmuller_distinguished_span_isPrime l O _ h0 hu hc _ w _ bk.deg_pos hw hE
  have hdom : IsDomain (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) :=
    Ideal.Quotient.isDomain _
  have hker : RingHom.ker (Per.θ l) ≤ RingHom.ker ((Ideal.Quotient.mk
      (Ideal.span {WittVector.map ψ (bk.ev bk.E)})).comp (WittVector.map ψ)) := by
    rw [← bk.span_ev, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  refine ⟨(Per.θ l).liftOfSurjective (theta_onto (l := l)) ⟨_, hker⟩, fun a => ?_, ?_, hdom, ?_⟩
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ a
  · rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hne
    obtain ⟨n, z, hz⟩ := dvd_pow_of_ne_zero_untilt l y hne
    have h := congrArg ((Per.θ l).liftOfSurjective (theta_onto (l := l)) ⟨_, hker⟩) hz
    rw [map_mul, hy, zero_mul, map_pow, map_natCast] at h
    have h2 := eq_zero_of_pow_eq_zero h
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem] at h2
    exact hl h2
  · rintro a ⟨b, hb⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hb
    obtain ⟨c, hc⟩ := hb
    have h := congrArg WittVector.constantCoeff hc
    rw [hE, map_mul, map_add (f := _), map_mul, map_sub, map_mul, constantCoeff_natCast_untilt, zero_mul, zero_mul,
      add_zero, sub_zero, map_pow, WittVector.constantCoeff_apply (WittVector.teichmuller _ _),
      WittVector.teichmuller_coeff_zero] at h
    exact ⟨_, h.symm.trans (mul_comm _ _)⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsAdicCompletionMapOfFg
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.AdicComplExists

variable {L : Type} [CommRing L] {J : Ideal L}

theorem evalₐ_algebraMap' (n : ℕ) (r : L) :
    AdicCompletion.evalₐ J n (algebraMap L (AdicCompletion J L) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

theorem mem_map_pow_iff (hfg : J.FG) (n : ℕ) (y : AdicCompletion J L) :
    y ∈ (J ^ n).map (algebraMap L (AdicCompletion J L)) ↔ AdicCompletion.evalₐ J n y = 0 := by
  rw [← Submodule.restrictScalars_mem L, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (J ^ n • ⊤ : Ideal L) = J ^ n := by ext x; simp
  exact (map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq L h').injective).symm

end GlobalTheory.BSP.AdicComplExists


open GlobalTheory.BSP.AdicComplExists in
theorem GlobalTheory.BSP.isCompl_exists : ∀ (L : Type) [CommRing L] (J : Ideal L), J.FG →
    ∃ (Q : Type) (_ : CommRing Q) (i : L →+* Q), IsCompl i J := by
  intro L _ J hfg
  refine ⟨AdicCompletion J L, inferInstance, algebraMap L (AdicCompletion J L), ⟨?_, ?_, ?_⟩⟩
  · rw [IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete hfg
  · intro x n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
    exact ⟨r, by rw [mem_map_pow_iff hfg, map_sub, evalₐ_algebraMap', hr, sub_self]⟩
  · intro a n ha
    rw [mem_map_pow_iff hfg, evalₐ_algebraMap'] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha
end

