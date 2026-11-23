module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0078

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetConjugationMatrixIntegralBasis
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

namespace GlobalTheory.UnitLemma.Unr

theorem conj_matrix_det_isUnit :
    ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), (∀ x, φ (K.c x) = K'.c (φ x)) →
      (letI : Algebra K.E K'.E := φ.toAlgebra
       ∀ w : Module.Basis (Fin d) K.E K'.E,
         (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔
           ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) →
         ∃ u : K.O, IsUnit u ∧
           algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det) := by
  intro K K' d φ hφ
  letI : Algebra K.E K'.E := φ.toAlgebra
  intro w hw
  set C : Matrix (Fin d) (Fin d) K.E := Matrix.of fun m l => w.repr (K'.c (w l)) m with hC
  have hsm : ∀ (e : K.E) (x : K'.E), e • x = φ e * x := fun e x => rfl
  have hint : ∀ m l, ∃ a : K.O, algebraMap K.O K.E a = C m l := by
    intro m l
    have h1 : ∃ y : K'.O, algebraMap K'.O K'.E y = w l := by
      rw [hw]
      intro k
      rw [w.repr_self]
      by_cases h : l = k
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Finsupp.single_apply, h]⟩
    obtain ⟨y, hy⟩ := h1
    obtain ⟨y', hy'⟩ := K'.c_int y
    have h2 : ∃ y : K'.O, algebraMap K'.O K'.E y = K'.c (w l) := ⟨y', by rw [← hy', hy]⟩
    exact (hw _).1 h2 m
  choose A hA using hint
  have hrep : ∀ (x : K'.E) (n : Fin d), w.repr (K'.c x) n = ∑ m, K.c (w.repr x m) * C n m := by
    intro x n
    have hx : K'.c x = ∑ m, K.c (w.repr x m) • K'.c (w m) := by
      conv_lhs => rw [← w.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hsm, hsm, map_mul, ← hφ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rfl
  have hCC : C * (K.c : K.E →+* K.E).mapMatrix C = 1 := by
    ext n l
    have h := hrep (K'.c (w l)) n
    rw [K'.c_c, w.repr_self, Finsupp.single_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_coe]
    rw [eq_comm]
    convert h using 1
    · exact if_congr eq_comm rfl rfl
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm]
    rfl
  have hdet : C.det * K.c C.det = 1 := by
    have h := congrArg Matrix.det hCC
    rw [Matrix.det_mul, Matrix.det_one, ← RingHom.map_det] at h
    exact h
  have hdetA : algebraMap K.O K.E (Matrix.of A).det = C.det := by
    rw [RingHom.map_det]
    congr 1
    ext m l
    simp [hA]
  refine ⟨(Matrix.of A).det, ?_, hdetA⟩
  obtain ⟨β, hβ⟩ := K.c_int (Matrix.of A).det
  apply IsUnit.of_mul_eq_one β
  apply IsFractionRing.injective K.O K.E
  rw [map_mul, ← hβ, hdetA, hdet, map_one]

end GlobalTheory.UnitLemma.Unr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitTraceFormDiscrUnramifiedExt
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.ResDisc

open IsLocalRing

theorem isUnit_discr_of_isMaximal_map {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Finite (ResidueField R)] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S)
    (hmax : (Ideal.map (algebraMap R S) (maximalIdeal R)).IsMaximal) :
    IsUnit (Algebra.discr R b) := by
  haveI : Module.Free R S := Module.Free.of_basis b
  haveI : Module.Finite R S := Module.Finite.of_basis b
  letI := Ideal.Quotient.field (maximalIdeal R)
  letI := Ideal.Quotient.field (Ideal.map (algebraMap R S) (maximalIdeal R))
  haveI : Finite (R ⧸ maximalIdeal R) := ‹Finite (ResidueField R)›
  haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    Module.Finite.of_basis (basisQuotient b)
  haveI : Algebra.IsSeparable (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    inferInstance
  have h1 : Ideal.Quotient.mk (maximalIdeal R) (Algebra.discr R b) =
      Algebra.discr (R ⧸ maximalIdeal R) (basisQuotient b) := by
    rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
    congr 1
    ext k m
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, basisQuotient_apply, ← map_mul, Algebra.trace_quotient_mk]
  have h2 := Algebra.discr_not_zero_of_basis (R ⧸ maximalIdeal R) (basisQuotient b)
  rw [← h1] at h2
  by_contra h
  exact h2 (Ideal.Quotient.eq_zero_iff_mem.2 ((mem_maximalIdeal _).2 h))

theorem discr_trace_isUnit :
    ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∀ (π : K.O) (π' : K'.O),
      algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) →
      IsLocalRing.maximalIdeal K.O = Ideal.span {π} →
      IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} →
      (letI : Algebra K.E K'.E := φ.toAlgebra
       ∀ w : Module.Basis (Fin d) K.E K'.E,
         (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔
           ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) →
         ∃ u : K.O, IsUnit u ∧
           algebraMap K.O K.E u = (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)).det) := by
  intro K K' d φ _ π π' hππ' hm hm'
  letI : Algebra K.E K'.E := φ.toAlgebra
  intro w hw
  have hj : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective K'.O K'.E
  have hi : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
  have hφ : ∀ e : K.E, φ e = algebraMap K.E K'.E e := fun _ => rfl

  have hlift : ∀ a : K.O, φ (algebraMap K.O K.E a) ∈ (algebraMap K'.O K'.E).range := by
    intro a
    apply (hw _).2
    intro k
    obtain ⟨c, hc⟩ := (hw 1).1 ⟨1, map_one _⟩ k
    refine ⟨a * c, ?_⟩
    have h1 : φ (algebraMap K.O K.E a) = (algebraMap K.O K.E a) • (1 : K'.E) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hc]
  let e : K'.O ≃+* (algebraMap K'.O K'.E).range :=
    RingEquiv.ofBijective (algebraMap K'.O K'.E).rangeRestrict
      ⟨fun x y h => hj (congrArg Subtype.val h), (algebraMap K'.O K'.E).rangeRestrict_surjective⟩
  let ι : K.O →+* K'.O :=
    e.symm.toRingHom.comp ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift)
  have hι : ∀ a, algebraMap K'.O K'.E (ι a) = φ (algebraMap K.O K.E a) := by
    intro a
    exact congrArg Subtype.val (e.apply_symm_apply ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift a))
  letI : Algebra K.O K'.O := ι.toAlgebra
  have hsm : ∀ (a : K.O) (y : K'.O),
      algebraMap K'.O K'.E (a • y) = algebraMap K.O K.E a • algebraMap K'.O K'.E y := by
    intro a y
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    exact congrArg (· * _) (hι a)
  have hsum : ∀ (g : Fin d → K.O) (v : Fin d → K'.O),
      algebraMap K'.O K'.E (∑ k, g k • v k) = ∑ k, algebraMap K.O K.E (g k) • algebraMap K'.O K'.E (v k) := by
    intro g v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hsm _ _

  have hw1 : ∀ k, ∃ y : K'.O, algebraMap K'.O K'.E y = w k := by
    intro k
    apply (hw _).2
    intro m
    refine ⟨if m = k then 1 else 0, ?_⟩
    rw [w.repr_self, Finsupp.single_apply]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  choose bv hbv using hw1
  have hcoord : ∀ (y : K'.O) (k : Fin d), ∃ a : K.O, algebraMap K.O K.E a = w.repr (algebraMap K'.O K'.E y) k :=
    fun y => (hw _).1 ⟨y, rfl⟩
  choose c hc using hcoord
  have hli : LinearIndependent K.O bv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h1 := congrArg (algebraMap K'.O K'.E) hg
    rw [hsum, map_zero] at h1
    simp only [hbv] at h1
    have h2 := (Fintype.linearIndependent_iff.1 w.linearIndependent) _ h1 k
    exact hi (by rw [h2, map_zero])
  have hsp : ⊤ ≤ Submodule.span K.O (Set.range bv) := by
    intro y _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c y, hj ?_⟩
    rw [hsum]
    simp only [hbv, hc]
    exact w.sum_repr _
  let b : Module.Basis (Fin d) K.O K'.O := Module.Basis.mk hli hsp
  have hb : ∀ k, algebraMap K'.O K'.E (b k) = w k := fun k => by
    rw [Module.Basis.mk_apply]; exact hbv k
  have hrep : ∀ y k, algebraMap K.O K.E (b.repr y k) = w.repr (algebraMap K'.O K'.E y) k := by
    intro y k
    conv_rhs => rw [← b.sum_repr y, hsum]
    simp only [hb]
    rw [w.repr_sum_self]

  have hTr : ∀ y, algebraMap K.O K.E (Algebra.trace K.O K'.O y) =
      Algebra.trace K.E K'.E (algebraMap K'.O K'.E y) := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace w, Matrix.trace, Matrix.trace,
      map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.diag_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', hrep, map_mul, hb]

  have hιπ : ι π = π' := hj (by rw [hι, hππ'])
  have hmax : (Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)).IsMaximal := by
    rw [hm, Ideal.map_span, Set.image_singleton]
    have h1 : algebraMap K.O K'.O π = π' := hιπ
    rw [h1, ← hm']
    exact IsLocalRing.maximalIdeal.isMaximal _
  refine ⟨Algebra.discr K.O b, isUnit_discr_of_isMaximal_map b hmax, ?_⟩
  rw [Algebra.discr_def, RingHom.map_det]
  congr 1
  ext k m
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, Matrix.of_apply, hTr, map_mul, hb]

end GlobalTheory.UnitLemma.Unr.ResDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnit
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.EtInv

section Gen
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] [Module.Finite F K]

theorem eq_zero_of_trace_mul [CharZero F] [IsReduced K] (a : K)
    (h : ∀ x : K, Algebra.trace F K (x * a) = 0) : a = 0 := by
  classical
  let b := Module.finBasis F K
  have hn : IsNilpotent (Algebra.leftMulMatrix b a) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]
    exact h _
  obtain ⟨m, hm⟩ := hn
  rw [← map_pow, ← map_zero (Algebra.leftMulMatrix b)] at hm
  exact (IsNilpotent.eq_zero ⟨m, Algebra.leftMulMatrix_injective b hm⟩)

variable {r : ℕ} {τ : K}

theorem trace_mul_eq_sum (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ)) (x a : K) :
    Algebra.trace F K (x * a) = ∑ j, bb.repr x j * Algebra.trace F K (τ ^ (j : ℕ) * a) := by
  conv_lhs => rw [← bb.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Finset.sum_mul, smul_mul_assoc, map_sum, hb]

end Gen

section Comp
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] {r : ℕ} {τ : K} {p : Fin r → F}

theorem leftMulMatrix_eq_companion (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ))
    (hr : τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0) : Algebra.leftMulMatrix bb τ = companion p := by
  classical
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, hb, ← pow_succ']
  simp only [companion, Matrix.of_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · rw [if_pos hj, hj, eq_neg_of_add_eq_zero_left hr]
    have : ∑ k, p k • τ ^ (k : ℕ) = ∑ k, p k • bb k := by simp [hb]
    rw [this, map_neg, Finsupp.neg_apply, bb.repr_sum_self]
  · rw [if_neg hj]
    have hlt : (j : ℕ) + 1 < r := by omega
    have : τ ^ ((j : ℕ) + 1) = bb ⟨(j : ℕ) + 1, hlt⟩ := by rw [hb]
    rw [this, bb.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = (j : ℕ) + 1
    · rw [if_pos (Fin.ext hi.symm), if_pos hi]
    · rw [if_neg (fun h => hi (by rw [← h])), if_neg hi]

theorem companion_pow_mulVec (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ))
    (hr : τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0) (n : ℕ) :
    (companion p ^ n) *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : F) else 0) = ⇑(bb.repr (τ ^ n)) := by
  classical
  induction n with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec, pow_zero]
    funext i
    have hr0 : 0 < r := lt_of_le_of_lt (Nat.zero_le _) i.2
    have h1 : (1 : K) = bb ⟨0, hr0⟩ := by rw [hb]; simp
    rw [h1, bb.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
    · rw [if_neg hi, if_neg (fun h => hi (by rw [← h]))]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, ← leftMulMatrix_eq_companion bb hb hr,
      Algebra.leftMulMatrix_apply, LinearMap.toMatrix_mulVec_repr, pow_succ']
    rfl

end Comp

theorem invK_regular_iff_isUnit :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p →
      Function.Bijective (fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a)) ∧
      ∀ a : A.K, (∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a)) ∧
        (Delta (A.invK τ p lam a) ≠ 0 ↔ IsUnit a) := by
  intro F E _ _ _ _ hU A r τ p lam hg
  classical
  haveI : CharZero F := hU.charZero
  obtain ⟨hli, hfr, hr⟩ := hg
  let bb : Module.Basis (Fin r) F A.K :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [hfr, Fintype.card_fin])
  have hb : ∀ i, bb i = τ ^ (i : ℕ) := fun i => by
    simp [bb]
  let Ψ : A.K →ₗ[F] (Fin r → F) :=
    { toFun := fun a i => Algebra.trace F A.K (τ ^ (i : ℕ) * a)
      map_add' := fun a a' => by funext i; simp [mul_add]
      map_smul' := fun c a => by funext i; simp [mul_smul_comm] }
  have hΨ : ∀ a, Ψ a = fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * a) := fun _ => rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    apply eq_zero_of_trace_mul (F := F) a
    intro x
    rw [trace_mul_eq_sum bb hb x a]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun ha j
    simp only [hΨ, Pi.zero_apply] at this
    rw [this, mul_zero]
  have hbij : Function.Bijective Ψ := by
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hfr])).1 hinj
  have hmom : ∀ a : A.K, ∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a) := by
    intro a i
    simp only [mom, sec, Et.invK]
    rw [companion_pow_mulVec bb hb hr i, trace_mul_eq_sum bb hb (τ ^ i) a, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨hbij, fun a => ⟨hmom a, ?_⟩⟩

  have hH : ∀ v : Fin r → F, hankel (A.invK τ p lam a) *ᵥ v = Ψ (a * bb.equivFun.symm v) := by
    intro v
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hankel, Matrix.mulVec, dotProduct, Matrix.of_apply, hmom, hΨ,
      Module.Basis.equivFun_symm_apply, hb, Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]; ring_nf
  have hcomp : Function.Injective (hankel (A.invK τ p lam a)).mulVec ↔ Function.Injective (fun y : A.K => a * y) := by
    constructor
    · intro h y y' hyy
      have := h (a₁ := bb.equivFun y) (a₂ := bb.equivFun y') (by rw [hH, hH]; simp [hyy])
      exact bb.equivFun.injective this
    · intro h v v' hvv
      rw [hH, hH] at hvv
      exact bb.equivFun.symm.injective (h (hinj hvv))
  rw [Delta, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit, hcomp]
  constructor
  · intro h
    have hs : Function.Surjective (Algebra.lmul F A.K a) :=
      LinearMap.injective_iff_surjective.1 h
    obtain ⟨y, hy⟩ := hs 1
    exact ⟨⟨a, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  · intro h
    exact h.mul_right_injective

end GlobalTheory.JR.EtInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Per

theorem linearIndependent_of_invariant (G E M ι : Type) [Field E] [AddCommGroup M] [Module E M]
    [Fintype ι] (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : ι → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : ι → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0) :
    LinearIndependent E v := by
  classical
  rw [Fintype.linearIndependent_iff]

  suffices H : ∀ n : ℕ, ∀ c : ι → E,
      (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ n → ∑ i, c i • v i = 0 → ∀ i, c i = 0 by
    exact fun c hc => H _ c le_rfl hc
  intro n
  induction n with
  | zero =>
    intro c hcard _ i
    by_contra h
    have hpos : 0 < (Finset.univ.filter (fun i => c i ≠ 0)).card :=
      Finset.card_pos.mpr ⟨i, by simp [h]⟩
    omega
  | succ n ih =>
    intro c hcard hsum
    by_contra hne
    obtain ⟨i0, hi0⟩ := not_forall.mp hne

    obtain ⟨c', hc'⟩ : ∃ c' : ι → E, c' = fun i => (c i0)⁻¹ * c i := ⟨_, rfl⟩
    have hc'sum : ∑ i, c' i • v i = 0 := by
      simp only [hc', mul_smul, ← Finset.smul_sum, hsum, smul_zero]
    have hc'i0 : c' i0 = 1 := by
      rw [hc']
      exact inv_mul_cancel₀ hi0
    have hsupp : Finset.univ.filter (fun i => c' i ≠ 0) = Finset.univ.filter (fun i => c i ≠ 0) := by
      ext i
      simp [hc', hi0]

    have hfix : ∀ g i, σ g (c' i) = c' i := by
      intro g
      obtain ⟨d, hd⟩ : ∃ d : ι → E, d = fun i => σ g (c' i) - c' i := ⟨_, rfl⟩
      have h1 : ∑ i, σ g (c' i) • v i = 0 := by
        have h2 := congrArg (ρ g) hc'sum
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_zero] at h2
        simpa [hρ, hv] using h2
      have hdsum : ∑ i, d i • v i = 0 := by
        simp only [hd, sub_smul, Finset.sum_sub_distrib, h1, hc'sum, sub_zero]
      have hsub : Finset.univ.filter (fun i => d i ≠ 0) ⊆
          (Finset.univ.filter (fun i => c' i ≠ 0)).erase i0 := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hi ⊢
        refine ⟨?_, ?_⟩
        · rintro rfl
          apply hi
          simp [hd, hc'i0]
        · intro h0
          apply hi
          simp [hd, h0]
      have hmem : i0 ∈ Finset.univ.filter (fun i => c' i ≠ 0) := by simp [hc'i0]
      have hdcard : (Finset.univ.filter (fun i => d i ≠ 0)).card ≤ n := by
        have h3 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hmem, hsupp] at h3
        omega
      intro i
      have h5 := ih d hdcard hdsum i
      rw [hd] at h5
      exact sub_eq_zero.mp h5
    have h4 := hind c' hfix hc'sum i0
    rw [hc'i0] at h4
    exact one_ne_zero h4

end GlobalTheory.Per
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPreservesTestFixesUnit
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem fourier_test_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ f', IsTest f' → IsTest (fourG M ψ f')) ∧ (∀ f, IsTest f → IsTest (fourU M ψ f)) ∧ IsTest (unitG r F) ∧ IsTest (unitU r F E) ∧ fourG M ψ (unitG r F) = unitG r F ∧ fourU M ψ (unitU r F E) = unitU r F E := by
  intro F E _ _ _ _ hU r M ψ hψ
  haveI := hU.ultraF; haveI := hU.ultraE; haveI := hU.lcF; haveI := hU.lcE
  have htr := _root_.GlobalTheory.trace_eq_add_star F E
  refine ⟨fun f' hf => ⟨_root_.GlobalTheory.JR.fourG_isLocallyConstant_of_invariant F E r M ψ hψ f' hf (_root_.GlobalTheory.isTest_nhds_inv _ f' hf), _root_.GlobalTheory.JR.fourG_hasCompactSupport F E r M ψ hψ f' hf (_root_.GlobalTheory.isTest_nhds_inv _ f' hf)⟩,
    fun f hf => ⟨_root_.GlobalTheory.fourU_isLocallyConstant F E r M ψ hψ htr f hf (_root_.GlobalTheory.isTest_nhds_inv _ f hf), _root_.GlobalTheory.fourU_hasCompactSupport F E r M ψ hψ htr f hf (_root_.GlobalTheory.isTest_nhds_inv _ f hf)⟩,
    _root_.GlobalTheory.JR.UnitTest.unitG_isTest F r, GlobalTheory.T.isTest_unitIndicatorHermitianBlock F E r hU.norm_star, _root_.GlobalTheory.JR.fourG_unitG F E r M ψ hψ, _root_.GlobalTheory.JR.FourUnit.fourU_unitU F E r M ψ hψ htr (_root_.GlobalTheory.TraceUnit.exists_trace_unit F E htr)⟩

end GlobalTheory
end

