module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
public import GroundTheory.GlobalFields.Adele.Topology
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.IntegralTransvectionMemSlIntegersConjugateZero
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.CompactSubgroupMembership

variable {F : Type} [Field F] [NumberField F]

def mP (w : Pl F) (c : ℕ) : AddSubgroup (w.adicCompletion F) :=
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c).toAddSubgroup.map
    (w.adicCompletionIntegers F).subtype.toAddMonoidHom

theorem mem_parahoricTimesPrincipalCongruence_iff {w : Pl F} {c : ℕ} {g : GL (Fin 2) (w.adicCompletion F)} :
    g ∈ K1 w c ↔ (∀ a b, g a b ∈ w.adicCompletionIntegers F) ∧
      (∀ a b, (g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b ∈ w.adicCompletionIntegers F) ∧
      g 1 0 ∈ mP w c ∧ g 1 1 - 1 ∈ mP w c := by
  have key : ∀ k : GL (Fin 2) (w.adicCompletionIntegers F),
      k ∈ ((mirab _).comap (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)))) ↔
      k 1 0 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ∧
        k 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c := fun k => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq, map_one]
    change ![0, 1] ᵥ* _ = ![0, 1] ↔ _
    rw [funext_iff, Fin.forall_fin_two]
    simp [Matrix.vecMul, dotProduct]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h1, h2⟩ := (key k).1 hk
    refine ⟨fun a b => (k a b).2, fun a b => ?_, ⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
    rw [← map_inv]; exact ((k⁻¹ : GL (Fin 2) (w.adicCompletionIntegers F)) a b).2
  · rintro ⟨ha, hb, ⟨y, hy, e⟩, ⟨y', hy', e'⟩⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin 2) (w.adicCompletionIntegers F).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin 2) (w.adicCompletionIntegers F) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    refine ⟨k, (key k).2 ⟨?_, ?_⟩, Units.ext rfl⟩
    · rw [show k 1 0 = y from Subtype.ext e.symm]; exact hy
    · rw [show k 1 1 - 1 = y' from Subtype.ext e'.symm]; exact hy'

theorem mem_mP_zero {w : Pl F} {x : w.adicCompletion F} (hx : x ∈ w.adicCompletionIntegers F) : x ∈ mP w 0 :=
  ⟨⟨x, hx⟩, by simp, rfl⟩

theorem mem_O {x : Af F} : x ∈ Ohat F ↔ ∀ w : Pl F, pLoc F w x ∈ w.adicCompletionIntegers F := by
  simp [Ohat, Subring.mem_iInf]

theorem mem_Ov {x : Af F} : x ∈ Ohat F ↔ ∀ w : Pl F, Valued.v (pLoc F w x) ≤ 1 := by
  rw [mem_O]; simp only [HeightOneSpectrum.mem_adicCompletionIntegers]

theorem v_le {x : Af F} (hx : x ∈ Ohat F) (w : Pl F) : Valued.v (pLoc F w x) ≤ 1 := mem_Ov.1 hx w

theorem integral_transvection_mem_slIntegers_conjugate_zero {g : GF F} :
    g ∈ K0 F ↔ (∀ i j, g.val i j ∈ Ohat F) ∧ ∀ i j, (g⁻¹ : GF F).val i j ∈ Ohat F := by
  simp only [K0, Kc, Subgroup.mem_iInf, Subgroup.mem_comap, mem_parahoricTimesPrincipalCongruence_iff, ← map_inv, mem_O]
  constructor
  · intro h
    exact ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2.1 i j⟩
  · rintro ⟨h1, h2⟩ w
    exact ⟨fun i j => h1 i j w, fun i j => h2 i j w, mem_mP_zero (h1 1 0 w),
      mem_mP_zero (sub_mem (h1 1 1 w) (one_mem _))⟩

theorem Kc_le (c : Pl F → ℕ) : Kc c ≤ K0 F := fun g hg => by
  rw [integral_transvection_mem_slIntegers_conjugate_zero]
  simp only [Kc, Subgroup.mem_iInf, Subgroup.mem_comap, mem_parahoricTimesPrincipalCongruence_iff, ← map_inv] at hg
  exact ⟨fun i j => mem_O.2 fun w => (hg w).1 i j, fun i j => mem_O.2 fun w => (hg w).2.1 i j⟩

theorem zc_normal : ((zc F).range).Normal :=
  ⟨fun n hn g => by
    obtain ⟨z, rfl⟩ := hn
    have := Subgroup.mem_center_iff.1 (zc_center z) g
    exact ⟨z, by rw [this, mul_inv_cancel_right]⟩⟩

theorem mem_Hc (c : Pl F → ℕ) (h : GF F) : h ∈ Hc c ↔ ∃ k ∈ Kc c, ∃ z, h = k * zc F z := by
  have := zc_normal (F := F)
  change h ∈ Kc c ⊔ (zc F).range ↔ _
  rw [Subgroup.mem_sup_of_normal_right]
  constructor
  · rintro ⟨k, hk, _, ⟨z, rfl⟩, rfl⟩
    exact ⟨k, hk, z, rfl⟩
  · rintro ⟨k, hk, z, rfl⟩
    exact ⟨k, hk, _, ⟨z, rfl⟩, rfl⟩

theorem det_mem {g : GF F} (h : ∀ i j, g.val i j ∈ Ohat F) : g.val.det ∈ Ohat F := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (h 0 0) (h 1 1)) (mul_mem (h 0 1) (h 1 0))

theorem k_prop {k : GF F} (hk : k ∈ K0 F) (w : Pl F) :
    Valued.v (pLoc F w ((Matrix.GeneralLinearGroup.det k : (Af F)ˣ) : Af F)) = 1 ∧
      max (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) = 1 := by
  obtain ⟨h1, h2⟩ := integral_transvection_mem_slIntegers_conjugate_zero.1 hk
  refine ⟨?_, ?_⟩
  · have hd2 := v_le (det_mem h2) w
    have hdd : k.val.det * (k⁻¹ : GF F).val.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have e1 : Valued.v (pLoc F w k.val.det) * Valued.v (pLoc F w (k⁻¹ : GF F).val.det) = 1 := by
      rw [← map_mul, ← map_mul, hdd, map_one, map_one]
    change Valued.v (pLoc F w k.val.det) = 1
    exact le_antisymm (v_le (det_mem h1) w) (e1 ▸ mul_le_of_le_one_right' hd2)
  · have e : k.val 1 0 * (k⁻¹ : GF F).val 0 1 + k.val 1 1 * (k⁻¹ : GF F).val 1 1 = 1 := by
      have := congrFun (congrFun (Units.mul_inv k) 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at this
      exact this
    have hv : Valued.v (pLoc F w (k.val 1 0) * pLoc F w ((k⁻¹ : GF F).val 0 1) +
        pLoc F w (k.val 1 1) * pLoc F w ((k⁻¹ : GF F).val 1 1)) = 1 := by
      rw [← map_mul, ← map_mul, ← map_add (f := _), e, map_one, map_one]
    refine le_antisymm (max_le (v_le (h1 1 0) w) (v_le (h1 1 1) w)) ?_
    refine hv.ge.trans ((Valuation.map_add _ _ _).trans (max_le_max ?_ ?_))
    · rw [map_mul]; exact mul_le_of_le_one_right' (v_le (h2 0 1) w)
    · rw [map_mul]; exact mul_le_of_le_one_right' (v_le (h2 1 1) w)

theorem val_pLoc (w : Pl F) (x : F) :
    Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem int_iff (t : F) : IsIntegral ℤ t ↔ algebraMap F (Af F) t ∈ Ohat F := by
  rw [mem_Ov]
  simp only [val_pLoc]
  constructor
  · intro h w
    exact HeightOneSpectrum.valuation_le_one w (⟨t, h⟩ : 𝓞 F)
  · intro h
    obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F t h
    exact RingOfIntegers.isIntegral_coe r

theorem af_den (a : Af F) : ∃ n : ℕ, n ≠ 0 ∧ (n : Af F) * a ∈ Ohat F := by
  have hU : IsOpen {z : Af F | a - z ∈ Ohat F} :=
    isOpen_Ohat.preimage (f := fun z : Af F => a - z) (by fun_prop)
  obtain ⟨x, hx⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).exists_mem_open hU
    ⟨a, by simp⟩
  obtain ⟨m, hm0, hm⟩ :=
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, ?_⟩
  have h1 : algebraMap F (Af F) (m • x) ∈ Ohat F :=
    mem_Ohat.2 (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F ⟨_, hm⟩)
  have h2 := add_mem h1 (mul_mem (intCast_mem (Ohat F) m) hx)
  have h3 : (m : Af F) * a ∈ Ohat F := by
    convert h2 using 1
    rw [zsmul_eq_mul, map_mul, map_intCast]; ring
  rcases Int.natAbs_eq m with h | h
  · rw [h] at h3; simpa using h3
  · rw [h] at h3; simpa using neg_mem h3

theorem den_ex (g : GF F) : ∃ N : ℕ, N ≠ 0 ∧ ∀ i j, (N : Af F) * g.val i j ∈ Ohat F := by
  choose n hn0 hn using fun p : Fin 2 × Fin 2 => af_den (g.val p.1 p.2)
  refine ⟨∏ p, n p, Finset.prod_ne_zero_iff.2 fun p _ => hn0 p, fun i j => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (i, j))
  rw [hk, Nat.cast_mul, mul_comm ((n (i, j) : ℕ) : Af F), mul_assoc]
  exact mul_mem (natCast_mem _ k) (hn (i, j))

theorem unit_scalar_mem_maximal_compact {u : (Af F)ˣ} (hu : ∀ w : Pl F, Valued.v (pLoc F w (u : Af F)) = 1) :
    zc F u ∈ K0 F ∧ ∀ t ∈ Ohat F, aff u t ∈ K0 F := by
  have hu1 : (u : Af F) ∈ Ohat F := mem_Ov.2 fun w => (hu w).le
  have hu2 : ((u⁻¹ : (Af F)ˣ) : Af F) ∈ Ohat F := by
    refine mem_Ov.2 fun w => ?_
    have : Valued.v (pLoc F w (u : Af F)) * Valued.v (pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    rw [hu w, one_mul] at this
    exact this.le
  refine ⟨integral_transvection_mem_slIntegers_conjugate_zero.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun t ht => integral_transvection_mem_slIntegers_conjugate_zero.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · fin_cases i <;> fin_cases j <;> simp [zc, hu1]
  · rw [show (zc F u)⁻¹ = zc F u⁻¹ from (map_inv (zc F) u).symm]
    fin_cases i <;> fin_cases j <;> simp [-map_inv, zc, hu2]
  · change (!![(u : Af F), t; 0, 1] : Matrix (Fin 2) (Fin 2) (Af F)) i j ∈ Ohat F
    fin_cases i <;> fin_cases j <;> simp [hu1, ht]
  · change (!![((u⁻¹ : (Af F)ˣ) : Af F), -(((u⁻¹ : (Af F)ˣ) : Af F) * t); 0, 1] : Matrix (Fin 2) (Fin 2) (Af F)) i j ∈
      Ohat F
    fin_cases i <;> fin_cases j <;> simp [hu2, mul_mem hu2 ht]

end UpperTheory.Esk.CompactSubgroupMembership

open UpperTheory.Esk.CompactSubgroupMembership in
theorem UpperTheory.Esk.aMem : UpperTheory.Esk.AMem := by
  intro F _ _
  exact ⟨fun g => integral_transvection_mem_slIntegers_conjugate_zero, fun x => mem_Ov, Kc_le, mem_Hc, fun k hk w => k_prop hk w, int_iff, den_ex,
    fun u hu => unit_scalar_mem_maximal_compact hu⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.IwasawaDecompositionFiniteAdeles
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.IwasawaDecompositionLemmas

theorem ut_mul {R : Type} [CommRing R] {X Y : GL (Fin 2) R} (hX : (X : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    (hY : (Y : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) : ((X * Y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hX, hY]

theorem ut_eq {R : Type} [CommRing R] (p : GL (Fin 2) R) (h : (p : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    ∃ (z t : Rˣ) (x : R), p = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff t x := by
  have hd : IsUnit ((p : Matrix (Fin 2) (Fin 2) R) 0 0 * (p : Matrix (Fin 2) (Fin 2) R) 1 1) := by
    have := (Matrix.GeneralLinearGroup.det p).isUnit
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h, mul_zero, sub_zero] at this
  obtain ⟨a, ha⟩ := isUnit_of_mul_isUnit_left hd
  obtain ⟨d, hdd⟩ := isUnit_of_mul_isUnit_right hd
  refine ⟨d, a * d⁻¹, (p : Matrix (Fin 2) (Fin 2) R) 0 1 * ((d⁻¹ : Rˣ) : R), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_two, ha, hdd, h] <;>
    rw [← hdd, mul_left_comm, Units.mul_inv, mul_one]

def LK {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (m : GL (Fin 2) K) : Prop :=
  (∀ i j, v ((m : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1) ∧ ∀ i j, v (((m⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1

theorem LK_one {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) : LK v 1 :=
  ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp, fun i j => by fin_cases i <;> fin_cases j <;> simp⟩

theorem LK_mul {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {m n : GL (Fin 2) K}
    (hm : LK v m) (hn : LK v n) : LK v (m * n) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (v.map_add _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hm.1 _ _) (hn.1 _ _)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (v.map_add _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hn.2 _ _) (hm.2 _ _)

theorem loc_iw {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (b : GL (Fin 2) K) :
    ∃ p k : GL (Fin 2) K, (p : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ LK v k ∧ b = p * k := by
  have hdet : (b : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  rw [Matrix.det_fin_two] at hdet
  set γ := (b : Matrix (Fin 2) (Fin 2) K) 1 0 with hγ
  set δ := (b : Matrix (Fin 2) (Fin 2) K) 1 1 with hδ
  by_cases h : v γ ≤ v δ
  · have hδ0 : δ ≠ 0 := by
      intro h0
      have h1 : γ = 0 := by
        rw [h0, map_zero] at h
        exact (Valuation.zero_iff v).1 (le_antisymm h zero_le)
      apply hdet; rw [h0, h1]; ring
    let k : GL (Fin 2) K := ⟨!![1, 0; γ / δ, 1], !![1, 0; -(γ / δ), 1],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    refine ⟨b * k⁻¹, k, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, (inv_mul_cancel_right b k).symm⟩
    · change ((b : Matrix (Fin 2) (Fin 2) K) * !![1, 0; -(γ / δ), 1]) 1 0 = 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp [← hγ, ← hδ]
      field_simp
      ring
    · fin_cases i <;> fin_cases j <;> simp [k]
      exact div_le_one_of_le₀ h zero_le
    · change v ((!![1, 0; -(γ / δ), 1] : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1
      fin_cases i <;> fin_cases j <;> simp
      exact div_le_one_of_le₀ h zero_le
  · have hlt : v δ < v γ := lt_of_not_ge h
    have hγ0 : γ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hlt
      exact not_lt_zero hlt
    let k : GL (Fin 2) K := ⟨!![0, 1; 1, δ / γ], !![-(δ / γ), 1; 1, 0],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    refine ⟨b * k⁻¹, k, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, (inv_mul_cancel_right b k).symm⟩
    · change ((b : Matrix (Fin 2) (Fin 2) K) * !![-(δ / γ), 1; 1, 0]) 1 0 = 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp [← hγ, ← hδ]
      field_simp
      ring
    · fin_cases i <;> fin_cases j <;> simp [k]
      exact div_le_one_of_le₀ hlt.le zero_le
    · change v ((!![-(δ / γ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1
      fin_cases i <;> fin_cases j <;> simp
      exact div_le_one_of_le₀ hlt.le zero_le

section Fin

variable {F : Type} [Field F] [NumberField F]

theorem ev_int (x : Af F) : ∀ᶠ w in Filter.cofinite, Valued.v (pLoc F w x) ≤ 1 := by
  filter_upwards [x.2] with w hw
  exact hw

theorem ev_good (b : GL (Fin 2) (Af F)) :
    ∀ᶠ w in Filter.cofinite, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) b) := by
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i j : Fin 2,
      Valued.v (pLoc F w ((b : Matrix (Fin 2) (Fin 2) (Af F)) i j)) ≤ 1 := by
    simp only [Filter.eventually_all]
    exact fun i j => ev_int _
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i j : Fin 2,
      Valued.v (pLoc F w (((b⁻¹ : GL (Fin 2) (Af F)) : Matrix (Fin 2) (Fin 2) (Af F)) i j)) ≤ 1 := by
    simp only [Filter.eventually_all]
    exact fun i j => ev_int _
  filter_upwards [h1, h2] with w hw hw'
  refine ⟨fun i j => hw i j, fun i j => ?_⟩
  rw [← map_inv]
  exact hw' i j

theorem locGL_10 (w : HeightOneSpectrum (𝓞 F)) (p : GL (Fin 2) (w.adicCompletion F))
    (hp : (p : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0 = 0) :
    (locGL F 2 w p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0 = 0 := by
  have key : ∀ v, pLoc F v ((locGL F 2 w p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0) = 0 := fun v => by
    change ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w p) : GL (Fin 2) (v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0
    by_cases hvw : v = w
    · subst hvw; rw [pLoc_locGL]; exact hp
    · rw [pLoc_locGL_of_ne hvw]; simp
  exact FiniteAdeleRing.ext _ fun v => (key v).trans (map_zero (pLoc F v)).symm

theorem iwasawa_decomposition_finite_adeles (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ b : GL (Fin 2) (Af F),
    (∀ w ∉ S, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) b)) →
    ∃ p k : GL (Fin 2) (Af F), (p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0 = 0 ∧
      (∀ w, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) k)) ∧ b = p * k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro b hb
    exact ⟨1, b, by simp, fun w => hb w (Finset.notMem_empty w), (one_mul b).symm⟩
  | insert w S hw ih =>
    intro b hb
    obtain ⟨pw, kw, hpw, hkw, e⟩ := loc_iw Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) b)
    obtain ⟨p, k, hp, hk, e'⟩ := ih ((locGL F 2 w pw)⁻¹ * b * (locGL F 2 w kw)⁻¹) fun v hv => by
      by_cases hvw : v = w
      · subst hvw
        rw [map_mul, map_mul, map_inv, map_inv, pLoc_locGL, pLoc_locGL, e, inv_mul_cancel_left, mul_inv_cancel]
        exact LK_one _
      · rw [map_mul, map_mul, map_inv, map_inv, pLoc_locGL_of_ne hvw, pLoc_locGL_of_ne hvw, inv_one, one_mul,
          mul_one]
        exact hb v (by simp [hvw, hv])
    refine ⟨locGL F 2 w pw * p, k * locGL F 2 w kw, ut_mul (locGL_10 w pw hpw) hp, fun v => ?_, ?_⟩
    · rw [map_mul]
      refine LK_mul _ (hk v) ?_
      by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL]; exact hkw
      · rw [pLoc_locGL_of_ne hvw]; exact LK_one _
    · rw [show locGL F 2 w pw * p * (k * locGL F 2 w kw) = locGL F 2 w pw * (p * k) * locGL F 2 w kw by
        simp only [mul_assoc], ← e']
      group

theorem fin_iw (b : GL (Fin 2) (Af F)) :
    ∃ p k : GL (Fin 2) (Af F), (p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0 = 0 ∧
      (∀ w, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) k)) ∧ b = p * k := by
  have hf := Filter.eventually_cofinite.1 (ev_good b)
  refine iwasawa_decomposition_finite_adeles hf.toFinset b fun w hw => ?_
  by_contra h
  exact hw (hf.mem_toFinset.2 h)

theorem mem_maximal_compact_of_local (h1 : ∀ g : GF F, g ∈ K0 F ↔ (∀ i j, g.val i j ∈ Ohat F) ∧ ∀ i j, (g⁻¹ : GF F).val i j ∈ Ohat F)
    (h2 : ∀ x : Af F, x ∈ Ohat F ↔ ∀ w : Pl F, Valued.v (pLoc F w x) ≤ 1) {k : GF F}
    (hk : ∀ w, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) k)) : k ∈ K0 F := by
  refine (h1 k).2 ⟨fun i j => (h2 _).2 fun w => (hk w).1 i j, fun i j => (h2 _).2 fun w => ?_⟩
  have := (hk w).2 i j
  rw [← map_inv] at this
  exact this

end Fin

end UpperTheory.Esk.IwasawaDecompositionLemmas

open UpperTheory.Esk.IwasawaDecompositionLemmas in
theorem UpperTheory.Esk.aIw : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw := by
  intro hM F _ _ x
  obtain ⟨h1, h2, -⟩ := hM F
  obtain ⟨p, k, hp, hk, e⟩ := fin_iw x
  obtain ⟨z, t, u, hz⟩ := ut_eq p hp
  refine ⟨z, t, u, k, mem_maximal_compact_of_local h1 h2 hk, ?_⟩
  rw [e, hz]
  rfl
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.JFSa
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.AdelicNormalFormLemmas

theorem key {R : Type} [CommRing R] (c α r e r' e' : Rˣ) (u y0 : R) (k : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ * aff α⁻¹ (-y0) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c * r * e) * aff (α * r' * e') u * k) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) r * aff r' 0 *
      (aff 1 (((r'⁻¹ : Rˣ) : R) * (((α⁻¹ : Rˣ) : R) * u - y0)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) e * aff e' 0 * k)) := by
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ * aff α⁻¹ (-y0) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c * r * e) * aff (α * r' * e') u) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) r * aff r' 0 *
      (aff 1 (((r'⁻¹ : Rˣ) : R) * (((α⁻¹ : Rˣ) : R) * u - y0)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) e * aff e' 0)) := by
    have hc := Units.inv_mul c
    have ha := Units.inv_mul α
    have hr := Units.mul_inv r'
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [aff, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, Matrix.vecMul, dotProduct,
        Matrix.diagonal_apply] <;>
      first
      | linear_combination (((α⁻¹ : Rˣ) : R) * α * r * e * r' * e') * hc + ((r : R) * e * r' * e') * ha
      | linear_combination ((r : R) * e * (((α⁻¹ : Rˣ) : R) * u - y0)) * hc - ((r : R) * e * (((α⁻¹ : Rˣ) : R) * u - y0)) * hr
      | linear_combination ((r : R) * e) * hc
  calc _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ * aff α⁻¹ (-y0) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c * r * e) * aff (α * r' * e') u)) * k := by group
    _ = _ := by rw [h1]; group

theorem jF_sa {F : Type} [Field F] [NumberField F] (c α : Fˣ) (β : F) :
    UpperTheory.Esk.jF F (Matrix.GeneralLinearGroup.scalar (Fin 2) c * aff α β) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ratU F c) * aff (ratU F α) (algebraMap F (Af F) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperTheory.Esk.jF, ratU, aff, Matrix.mul_apply, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]

end UpperTheory.Esk.AdelicNormalFormLemmas

open UpperTheory.Esk.AdelicNormalFormLemmas in
theorem UpperTheory.Esk.aBnf : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw → UpperTheory.Esk.ACls → UpperTheory.Esk.AAdd → UpperTheory.Esk.ABnf := by
  intro hM hI hC hA F _ _
  classical
  obtain ⟨T, hT⟩ := hC F
  refine ⟨(T ×ˢ T).image (fun p => zc F p.1 * aff p.2 0), fun x => ?_⟩
  obtain ⟨d, a, u, k, hk, rfl⟩ := hI F x
  obtain ⟨y, e, r, hr, he, hd⟩ := hT d
  obtain ⟨y', e', r', hr', he', ha⟩ := hT a
  obtain ⟨y0, hy0⟩ := hA F r' ((((ratU F y')⁻¹ : (Af F)ˣ) : Af F) * u)
  have hK := (hM F).2.2.2.2.2.2.2
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) y⁻¹ * aff y'⁻¹ (-y0), ?_, zc F r * aff r' 0,
    Finset.mem_image.2 ⟨(r, r'), Finset.mem_product.2 ⟨hr, hr'⟩, rfl⟩,
    aff 1 (((r'⁻¹ : (Af F)ˣ) : Af F) * ((((ratU F y')⁻¹ : (Af F)ˣ) : Af F) * u - algebraMap F (Af F) y0)) *
      (zc F e * aff e' 0 * k), ?_, ?_⟩
  · simp [aff, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  · exact Subgroup.mul_mem _ ((hK 1 (by simp)).2 _ hy0)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hK e he).1 ((hK e' he').2 0 (zero_mem _))) hk)
  · rw [jF_sa, map_inv, map_inv, map_neg, hd, ha]
    exact key (ratU F y) (ratU F y') r e r' e' u (algebraMap F (Af F) y0) k
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.VOne
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.ClassNumberLemmas

theorem v_one {F : Type} [Field F] [NumberField F] (e : (Af F)ˣ) (h1 : (e : Af F) ∈ PIW.ClassFinD.Ohat F)
    (h2 : ((e⁻¹ : (Af F)ˣ) : Af F) ∈ PIW.ClassFinD.Ohat F) (w : Pl F) : Valued.v (pLoc F w (e : Af F)) = 1 := by
  have a1 : Valued.v (pLoc F w (e : Af F)) ≤ 1 := by
    have h := h1 w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have a2 : Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := by
    have h := h2 w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have hm : Valued.v (pLoc F w (e : Af F)) * Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc (1 : _) = Valued.v (pLoc F w (e : Af F)) * Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) := hm.symm
    _ ≤ Valued.v (pLoc F w (e : Af F)) * 1 := by gcongr
    _ = Valued.v (pLoc F w (e : Af F)) := mul_one _

end UpperTheory.Esk.ClassNumberLemmas

namespace UpperTheory.Esk

theorem aCls : ACls := by
  intro F _ _
  obtain ⟨C, hC⟩ := PIW.ClassFinD.idele_class_finite F
  refine ⟨C, fun z => ?_⟩
  obtain ⟨f, c, hc, e, he1, he2, hz⟩ := hC z
  exact ⟨f, e, c, hc, ClassNumberLemmas.v_one e he1 he2, hz⟩

end UpperTheory.Esk
end
end

