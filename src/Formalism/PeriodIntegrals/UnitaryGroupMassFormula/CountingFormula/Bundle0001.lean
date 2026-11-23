module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGSDvr
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Classical ValuativeRel

section Dvr

variable (F : Type) [Field F] [ValuativeRel F]

def resF (x : F) : 𝓀[F] := if h : x ∈ 𝒪[F] then IsLocalRing.residue 𝒪[F] ⟨x, h⟩ else 0

def liftF (c : 𝓀[F]) : F := ((IsLocalRing.residue_surjective c).choose : 𝒪[F])

theorem resF_coe (o : 𝒪[F]) : resF F (o : F) = IsLocalRing.residue 𝒪[F] o := by
  rw [resF, dite_eq_left o.2]

theorem liftF_mem (c : 𝓀[F]) : liftF F c ∈ 𝒪[F] :=
  (IsLocalRing.residue_surjective c).choose.2

theorem resF_liftF (c : 𝓀[F]) : resF F (liftF F c) = c := by
  rw [liftF, resF_coe]
  exact (IsLocalRing.residue_surjective c).choose_spec

theorem resF_one : resF F 1 = 1 := by
  simpa using resF_coe F 1

theorem resF_mul {x y : F} (hx : x ∈ 𝒪[F]) (hy : y ∈ 𝒪[F]) : resF F (x * y) = resF F x * resF F y := by
  have h := resF_coe F (⟨x, hx⟩ * ⟨y, hy⟩)
  rw [map_mul, ← resF_coe F ⟨x, hx⟩, ← resF_coe F ⟨y, hy⟩] at h
  exact h

theorem resF_sum_mul {ι : Type} [Fintype ι] (c x : ι → F) (hc : ∀ i, c i ∈ 𝒪[F]) (hx : ∀ i, x i ∈ 𝒪[F]) :
    resF F (∑ i, c i * x i) = ∑ i, resF F (c i) * resF F (x i) := by
  have hs : ((∑ i, (⟨c i, hc i⟩ : 𝒪[F]) * ⟨x i, hx i⟩ : 𝒪[F]) : F) = ∑ i, c i * x i := by
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hs, resF_coe, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← resF_coe F ⟨c i, hc i⟩, ← resF_coe F ⟨x i, hx i⟩]

theorem resF_eq_zero_of_lt {x : F} (hx : valuation F x < 1) : resF F x = 0 := by
  have hx1 : x ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 hx.le
  rw [show x = ((⟨x, hx1⟩ : 𝒪[F]) : F) from rfl, resF_coe, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one]
  exact hx.ne

theorem dvd_of_resF_eq_zero [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {x : F}
    (hx : x ∈ 𝒪[F]) (h0 : resF F x = 0) : ∃ o : 𝒪[F], x = (ϖ : F) * o := by
  rw [show x = ((⟨x, hx⟩ : 𝒪[F]) : F) from rfl, resF_coe, IsLocalRing.residue_eq_zero_iff,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at h0
  obtain ⟨a, ha⟩ := h0
  refine ⟨a, ?_⟩
  rw [show x = ((⟨x, hx⟩ : 𝒪[F]) : F) from rfl, ← ha]
  push_cast
  ring

theorem resF_irr {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) : resF F (ϖ : F) = 0 := by
  rw [resF_coe, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hϖ.not_isUnit

def SatF {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) : Prop :=
  ∀ u : Fin n → F, (∀ k, u k ∈ 𝒪[F]) → (∃ c : ι → F, ∑ i, c i • X i = u) →
    ∃ c : ι → F, (∀ i, c i ∈ 𝒪[F]) ∧ ∑ i, c i • X i = u

def redM {ι : Type} {n : ℕ} (X : ι → Fin n → F) : ι → Fin n → 𝓀[F] := fun i k => resF F (X i k)

variable {F}

theorem key_norm {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) (c : ι → F) (u : Fin n → F) (hu : ∑ i, c i • X i = u)
    (j : ι) (hj : ∀ i, valuation F (c i) ≤ valuation F (c j)) (hcj : c j ≠ 0)
    (hlt : ∀ k, valuation F (u k) < valuation F (c j)) : False := by
  have hvj : 0 < valuation F (c j) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcj)
  have hd : ∀ i, c i / c j ∈ 𝒪[F] := fun i =>
    (Valuation.mem_integer_iff _ _).2 (by rw [map_div₀]; exact (div_le_one₀ hvj).2 (hj i))
  have hz : ∑ i, resF F (c i / c j) • redM F X i = 0 := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, redM, Pi.zero_apply]
    have h := resF_sum_mul F (fun i => c i / c j) (fun i => X i k) hd (fun i => hX i k)
    rw [← h]
    apply resF_eq_zero_of_lt F
    have hs : ∑ i, c i / c j * X i k = u k / c j := by
      rw [← hu, Finset.sum_apply, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hs, map_div₀]
    exact (div_lt_one₀ hvj).2 (hlt k)
  have h1 := (Fintype.linearIndependent_iff.1 hred) _ hz j
  rw [div_self hcj, resF_one] at h1
  exact one_ne_zero h1

theorem indep_of_red {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) : LinearIndependent F X := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨i0, hi0⟩ := hne
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => valuation F (g i))
    ⟨i0, Finset.mem_univ _⟩
  have hcj : g j ≠ 0 := by
    intro h
    have h2 := hj i0 (Finset.mem_univ _)
    rw [h, map_zero] at h2
    exact hi0 ((Valuation.zero_iff _).1 (le_antisymm h2 zero_le'))
  refine key_norm X hX hred g 0 hg j (fun i => hj i (Finset.mem_univ _)) hcj (fun k => ?_)
  rw [Pi.zero_apply, map_zero]
  exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcj)

theorem sat_of_red {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) : SatF F X := by
  intro u hu hex
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, fun i => ?_, hc⟩
  by_contra hci
  rw [Valuation.mem_integer_iff, not_le] at hci
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => valuation F (c i))
    ⟨i, Finset.mem_univ _⟩
  have hj1 : 1 < valuation F (c j) := lt_of_lt_of_le hci (hj i (Finset.mem_univ _))
  have hcj : c j ≠ 0 := by
    intro h
    rw [h, map_zero] at hj1
    exact not_lt.2 zero_le' hj1
  exact key_norm X hX hred c u hc j (fun i => hj i (Finset.mem_univ _)) hcj
    (fun k => lt_of_le_of_lt ((Valuation.mem_integer_iff _ _).1 (hu k)) hj1)

theorem red_of_indep_sat [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hind : LinearIndependent F X) (hsat : SatF F X) : LinearIndependent 𝓀[F] (redM F X) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  obtain ⟨d, hdm, hres⟩ : ∃ d : ι → F, (∀ i, d i ∈ 𝒪[F]) ∧ ∀ i, resF F (d i) = a i :=
    ⟨fun i => liftF F (a i), fun i => liftF_mem F _, fun i => resF_liftF F _⟩
  have hcomp : ∀ k, (∑ i, d i • X i) k = ∑ i, d i * X i k := fun k => by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hmem : ∀ k, (∑ i, d i • X i) k ∈ 𝒪[F] := fun k => by
    rw [hcomp]
    exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hdm i) (hX i k)
  have hr0 : ∀ k, resF F ((∑ i, d i • X i) k) = 0 := fun k => by
    have h := resF_sum_mul F d (fun i => X i k) hdm (fun i => hX i k)
    rw [hcomp, h]
    simp only [hres]
    have h2 := congrFun ha k
    simpa [Finset.sum_apply, redM] using h2
  choose w hw using fun k => dvd_of_resF_eq_zero F hϖ (hmem k) (hr0 k)
  have hϖ0 : (ϖ : F) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  obtain ⟨c', hc'm, hc'⟩ := hsat (fun k => (w k : F)) (fun k => (w k).2)
    ⟨fun i => d i / ϖ, by
      funext k
      have e := hw k
      rw [hcomp] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div, e]
      field_simp⟩
  have hzero : ∑ i, (d i - ϖ * c' i) • X i = 0 := by
    funext k
    have e1 := congrFun hc' k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e1
    have e2 := hw k
    rw [hcomp] at e2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      Pi.zero_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, e1, e2, sub_self]
  have hdi := (Fintype.linearIndependent_iff.1 hind) _ hzero i
  rw [← hres i, sub_eq_zero.1 hdi, resF_mul F ϖ.2 (hc'm i), resF_irr F hϖ, zero_mul]

theorem dvr_prim_iff [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F]) :
    (LinearIndependent F X ∧ SatF F X) ↔ LinearIndependent 𝓀[F] (redM F X) :=
  ⟨fun h => red_of_indep_sat hϖ X hX h.1 h.2, fun h => ⟨indep_of_red X hX h, sat_of_red X hX h⟩⟩

end Dvr

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FiniteLeOfPosDef
section
namespace PI.UnitaryGroupMassFormula.CntFormula

theorem finite_le_of_posDef {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (B : LinearMap.BilinForm ℚ V) (hS : ∀ x y, B x y = B y x) (hpos : ∀ v, v ≠ 0 → 0 < B v v)
    (A : Submodule ℤ V) (hA : A.FG) (c : ℚ) : {v | v ∈ A ∧ B v v ≤ c}.Finite := by
  classical
  obtain ⟨S, hS'⟩ := hA
  have hnn : ∀ v, 0 ≤ B v v := fun v => by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpos v hv).le

  have cs : ∀ v w, B v w ^ 2 ≤ B v v * B w w := by
    intro v w
    by_cases hw : w = 0
    · simp [hw]
    · have hww := hpos w hw
      have key := hnn (B w w • v - B v w • w)
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hS w v] at key
      have h2 : B w w * B v w ^ 2 ≤ B w w * (B v v * B w w) := by nlinarith [key]
      exact le_of_mul_le_mul_left h2 hww
  let b := Module.finBasis ℚ V
  have hinj : ∀ v w, (∀ i, B v (b i) = B w (b i)) → v = w := by
    intro v w h
    have h0 : B (v - w) = 0 := b.ext fun i => by simp [map_sub, h i]
    by_contra hne
    have h1 := hpos (v - w) (sub_ne_zero.2 hne)
    rw [h0] at h1
    simp at h1
  let N : ℕ := ∏ s ∈ S, ∏ i, (B s (b i)).den
  have hNpos : 0 < N :=
    Finset.prod_pos fun s _ => Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (Rat.den_nz _)

  have hint : ∀ v ∈ A, ∀ i, ∃ z : ℤ, (z : ℚ) = N * B v (b i) := by
    intro v hv
    rw [← hS'] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      intro i
      have hd : (B x (b i)).den ∣ N :=
        (Finset.dvd_prod_of_mem (fun i => (B x (b i)).den) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun s => ∏ i, (B s (b i)).den) hx)
      obtain ⟨k, hk⟩ := hd
      refine ⟨k * (B x (b i)).num, ?_⟩
      have e := Rat.mul_den_eq_num (B x (b i))
      rw [hk]
      push_cast
      linear_combination (-(k : ℚ)) * e
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨z1, h1⟩ := hx i
      obtain ⟨z2, h2⟩ := hy i
      refine ⟨z1 + z2, ?_⟩
      rw [map_add (f := _), LinearMap.add_apply]
      push_cast
      rw [h1, h2]
      ring
    | smul a x _ hx =>
      intro i
      obtain ⟨z, hz⟩ := hx i
      refine ⟨a * z, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℚ a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
      push_cast
      rw [hz]
      ring
  have hbd : ∀ v, B v v ≤ c → ∀ i, |B v (b i)| ≤ 1 + |c| * B (b i) (b i) := by
    intro v hv i
    have h1 := cs v (b i)
    have h2 : B v v * B (b i) (b i) ≤ |c| * B (b i) (b i) :=
      mul_le_mul_of_nonneg_right (hv.trans (le_abs_self c)) (hnn _)
    have h3 : |B v (b i)| ≤ 1 + B v (b i) ^ 2 := by
      nlinarith [sq_nonneg (|B v (b i)| - 1), sq_abs (B v (b i))]
    linarith
  let g : V → Fin (Module.finrank ℚ V) → ℤ := fun v i => round ((N : ℚ) * B v (b i))
  have hg : ∀ v ∈ A, ∀ i, ((g v i : ℤ) : ℚ) = N * B v (b i) := by
    intro v hv i
    obtain ⟨z, hz⟩ := hint v hv i
    simp only [g]
    rw [← hz, round_intCast]
  apply Set.Finite.of_finite_image (f := g)
  · refine Set.Finite.subset (Set.Finite.pi (t := fun i =>
      Set.Icc (-⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉) ⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉)
      fun i => Set.finite_Icc _ _) ?_
    rintro _ ⟨v, ⟨hvA, hvc⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i
    have e := hg v hvA i
    have hb : |((g v i : ℤ) : ℚ)| ≤ N * (1 + |c| * B (b i) (b i)) := by
      rw [e, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hbd v hvc i) (Nat.cast_nonneg _)
    have hK := Int.le_ceil ((N : ℚ) * (1 + |c| * B (b i) (b i)))
    have l1 := neg_abs_le ((g v i : ℤ) : ℚ)
    have l2 := le_abs_self ((g v i : ℤ) : ℚ)
    constructor
    · have : ((-⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉ : ℤ) : ℚ) ≤ ((g v i : ℤ) : ℚ) := by
        push_cast
        linarith
      exact_mod_cast this
    · have : ((g v i : ℤ) : ℚ) ≤ ((⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉ : ℤ) : ℚ) := by
        linarith
      exact_mod_cast this
  · rintro v ⟨hvA, -⟩ w ⟨hwA, -⟩ hvw
    apply hinj
    intro i
    have e : (N : ℚ) * B v (b i) = N * B w (b i) := by
      rw [← hg v hvA i, ← hg w hwA i, congrFun hvw i]
    exact mul_left_cancel₀ (by exact_mod_cast hNpos.ne') e

end PI.UnitaryGroupMassFormula.CntFormula
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDeltaB
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.DeltaB

open Polynomial

variable {R K A : Type} [CommRing R] [Field K] [CommRing A] [Algebra R K] [Algebra K A] [Algebra R A]
  [IsScalarTower R K A]

theorem trace_isIntegral_rank2 (b : Module.Basis (Fin 2) K A) {y : A} (hy : IsIntegral R y) :
    IsIntegral R (Algebra.trace K A y) := by
  classical
  obtain ⟨p, hpm, hp⟩ := hy
  let L := AlgebraicClosure K
  let M : Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix b y
  let M' : Matrix (Fin 2) (Fin 2) L := M.map (algebraMap K L)
  have hpy : Polynomial.aeval y p = 0 := hp
  have hpM : Polynomial.aeval M p = 0 := by
    have h1 := Polynomial.aeval_algHom_apply ((Algebra.leftMulMatrix b).restrictScalars R) y p
    rw [hpy, map_zero] at h1
    exact h1
  have hpM' : Polynomial.aeval M' p = 0 := by
    have h1 := Polynomial.aeval_algHom_apply
      (((Algebra.ofId K L).mapMatrix : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) L).restrictScalars R) M p
    rw [hpM, map_zero] at h1
    exact h1
  have hroot : ∀ μ ∈ M'.charpoly.roots, IsIntegral R μ := by
    intro μ hμ
    have h1 : μ ∈ spectrum L M' := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots'.mp hμ).2
    have h2 := spectrum.subset_polynomial_aeval M' (p.map (algebraMap R L)) ⟨μ, h1, rfl⟩
    rw [Polynomial.aeval_map_algebraMap, hpM', spectrum.zero_eq] at h2
    refine ⟨p, hpm, ?_⟩
    have h3 : Polynomial.eval μ (p.map (algebraMap R L)) = 0 := h2
    rwa [Polynomial.eval_map] at h3
  have htr : algebraMap K L (Algebra.trace K A y) = M'.charpoly.roots.sum := by
    rw [Algebra.trace_eq_matrix_trace b y, ← Matrix.trace_eq_sum_roots_charpoly]
    simp [M', M, Matrix.trace, Matrix.map_apply]
  have hint : IsIntegral R (algebraMap K L (Algebra.trace K A y)) := by
    rw [htr]
    exact IsIntegral.multiset_sum hroot
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).mp hint

end PI.UnitaryGroupMassFormula.CntFormula.DeltaB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.IsIntIntCast
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem isInt_O (o : 𝓞 K) : IsIntegral ℤ (algebraMap (𝓞 K) K o) := o.2

theorem O_of_isInt {x : K} (h : IsIntegral ℤ x) : ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = x := ⟨⟨x, h⟩, rfl⟩

theorem isInt_intCast (n : ℤ) : IsIntegral ℤ (n : K) := by
  simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K n))

theorem isInt_star [StarRing K] {x : K} (h : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  h.map (starRingEnd K).toIntAlgHom

theorem commonDen (s : Finset K) : ∃ d : ℕ, 0 < d ∧ ∀ x ∈ s, IsIntegral ℤ ((d : K) * x) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y.natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hy) 2, fun x hx => ?_⟩
  have e0 : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by rw [Nat.cast_pow, Int.natAbs_sq]
  have e1 : ((y.natAbs ^ 2 : ℕ) : K) = (y : K) ^ 2 := by rw [← Int.cast_natCast, e0, Int.cast_pow]
  rw [e1, pow_two, mul_assoc, ← zsmul_eq_mul x y]
  exact (isInt_intCast y).mul (h x hx)

theorem reduceRep (N : ℕ) (hN : 0 < N) : ∃ Rep : Set K, Rep.Finite ∧ (∀ ρ ∈ Rep, IsIntegral ℤ ρ) ∧
    ∀ o : K, IsIntegral ℤ o → ∃ t ρ : K, IsIntegral ℤ t ∧ ρ ∈ Rep ∧ o = (N : K) * t + ρ := by
  set I : Ideal (𝓞 K) := Ideal.span {(N : 𝓞 K)} with hI
  have hIne : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have := I.finiteQuotientOfFreeOfNeBot hIne
  set σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := I)) with hσ
  refine ⟨Set.range (fun q : 𝓞 K ⧸ I => algebraMap (𝓞 K) K (σ q)), Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩; exact isInt_O _
  · intro o ho
    obtain ⟨oo, rfl⟩ := O_of_isInt ho
    set q := Ideal.Quotient.mk I oo
    have hq : Ideal.Quotient.mk I (σ q) = q := Function.surjInv_eq _ q
    have hmem : oo - σ q ∈ I := Ideal.Quotient.eq.1 hq.symm
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨algebraMap (𝓞 K) K t, algebraMap (𝓞 K) K (σ q), isInt_O _, ⟨q, rfl⟩, ?_⟩
    have e : oo = t * N + σ q := by rw [ht]; ring
    rw [e, map_add (f := _), map_mul, map_natCast]
    ring

end PI.UnitaryGroupMassFormula.CntFormula
end
end

