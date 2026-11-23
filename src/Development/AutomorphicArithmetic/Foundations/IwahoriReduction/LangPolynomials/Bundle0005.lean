module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PLangR

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormSubLeOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

noncomputable section
namespace UpperTheory.Kd.C7.C2

private theorem map_sb {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (b : ℕ) (h : PowerSeries R) :
    PowerSeries.map f (sb b h) = sb b (PowerSeries.map f h) := by
  have key := PowerSeries.map_subst (hasSubst_pow (R := R) b) (h := f) h
  unfold sb
  rw [PowerSeries.coe_substAlgHom, PowerSeries.coe_substAlgHom]
  have e : MvPowerSeries.map f (((1 + PowerSeries.X : PowerSeries R) ^ b) - 1) = (((1 + PowerSeries.X : PowerSeries S) ^ b) - 1) := by
    change PowerSeries.map f _ = _
    simp
  rw [e] at key
  exact key

private theorem sb_C {R : Type} [CommRing R] (b : ℕ) (x : R) (h : PowerSeries R) :
    sb b (PowerSeries.C x * h) = PowerSeries.C x * sb b h := by
  rw [map_mul]
  congr 1
  exact (sb (R := R) b).commutes x

variable {l : ℕ} [Fact l.Prime]

private theorem norm_sum_le_one {K ι : Type} [NormedField K] [IsUltrametricDist K] (s : Finset ι) (f : ι → K)
    (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h

private theorem norm_sub_le_one {K : Type} [NormedField K] [IsUltrametricDist K] {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))

private theorem nmul {K : Type} [NormedField K] {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

private theorem npow {K : Type} [NormedField K] {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha

private theorem norm_root {K : Type} [NormedField K] {a : K} {n : ℕ} (hn : n ≠ 0) (h : a ^ n = 1) : ‖a‖ ≤ 1 := by
  have : ‖a‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this).le

private theorem norm_chi (φ : DirichletCharacter (Qbar l) l) (x : ZMod l) : ‖φ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    refine norm_root (n := Fintype.card (ZMod l)ˣ) Fintype.card_ne_zero ?_
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  · rw [φ.map_nonunit hx, norm_zero]; exact zero_le_one

private theorem intg_lin (φ : DirichletCharacter (Qbar l) l) (k r : ℕ) (ξ : Qbar l) (hξ : IsPrimitiveRoot ξ (l ^ r)) :
    ∃ a : ℕ → Qbar l, (∀ n, ‖a n‖ ≤ 1) ∧ ∀ L, intg φ k L r ξ = ∑ n ∈ Finset.range (l ^ (3 * r)), a n * L.coeff n := by
  have h1 : ‖ξ‖ ≤ 1 := norm_root (pow_ne_zero r (Fact.out : l.Prime).ne_zero) hξ.pow_eq_one
  refine ⟨fun n => ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), ∑ i ∈ Finset.range (l ^ r),
    φ (x : ZMod l) * ((x : Qbar l) ^ k) * (ξ ^ (l ^ r - (i * x) % l ^ r) * (ξ ^ i - 1) ^ n), fun n => ?_, fun L => ?_⟩
  · refine norm_sum_le_one _ _ fun x _ => norm_sum_le_one _ _ fun i _ => ?_
    exact nmul (nmul (norm_chi φ _) (npow (IsUltrametricDist.norm_natCast_le_one _ _) _))
      (nmul (npow h1 _) (npow (norm_sub_le_one (npow h1 _) norm_one.le) _))
  · simp only [intg, mass, tval, Finset.mul_sum, Finset.sum_mul]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun n _ => ?_
    ring

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (Φ : Fr l A j) {c : Coef l} (β : Bas c)

private def abelian₂ (D : Fin β.d → PowerSeries Φ.R) : PowerSeries ℂ_[l] :=
  ∑ i, PowerSeries.C (algebraMap (PadicAlgCl l) ℂ_[l] (β.val i)) * PowerSeries.map Φ.jh (D i)

private theorem Lam_coeff (D : Fin β.d → PowerSeries Φ.R) (n : ℕ) :
    (abelian₂ Φ β D).coeff n = Φ.lam β (fun i => (D i).coeff n) := by
  simp [abelian₂, Fr.lam, PowerSeries.coeff_C_mul]

private theorem Lam_sub (D E : Fin β.d → PowerSeries Φ.R) :
    abelian₂ Φ β (fun i => D i - E i) = abelian₂ Φ β D - abelian₂ Φ β E := by
  simp [abelian₂, mul_sub, Finset.sum_sub_distrib]

private theorem Lam_sb (g : ℕ) (D : Fin β.d → PowerSeries Φ.R) :
    abelian₂ Φ β (fun i => sb g (D i)) = sb g (abelian₂ Φ β D) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [abelian₂, map_sum, sb_C, map_sb]

private theorem val_mul (b : c.O) (k : Fin β.d) :
    ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.mat b i k) = (b : PadicAlgCl l) * β.val k := by
  have h := β.e.sum_repr (b * β.e k)
  have h2 := congrArg (fun x : c.O => (x : PadicAlgCl l)) h
  simp only [Bas.val, Bas.mat, Algebra.leftMulMatrix_eq_repr_mul]
  simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, ← Algebra.smul_def]
  rfl

private theorem Lam_act (b : c.O) (D : Fin β.d → PowerSeries Φ.R) :
    abelian₂ Φ β (Φ.act (β.mat b) D) = PowerSeries.C (algebraMap (PadicAlgCl l) ℂ_[l] (b : PadicAlgCl l)) * abelian₂ Φ β D := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [abelian₂, Fr.act, map_sum, map_mul, PowerSeries.map_C, Φ.jh_alg, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← mul_assoc, ← map_mul, ← map_mul, ← val_mul β b k, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, mul_assoc]

private theorem nf (x : PadicAlgCl l) : ‖algebraMap (PadicAlgCl l) ℂ_[l] x‖ = ‖x‖ := PadicComplex.norm_extends l x

private theorem Lam_le (hβ : ∀ i, ‖β.val i‖ ≤ 1) (D : Fin β.d → PowerSeries Φ.R) (n : ℕ) : ‖(abelian₂ Φ β D).coeff n‖ ≤ 1 := by
  rw [Lam_coeff, Fr.lam]
  exact norm_sum_le_one _ _ fun i _ => nmul (by rw [nf]; exact hβ i) (Φ.jh_le _)

private theorem approx (hj : ∀ x ∈ A, ‖j x‖ ≤ 1) (hβ : ∀ i, ‖β.val i‖ ≤ 1) (D : Fin β.d → PowerSeries Φ.R) (N : ℕ) :
    ∃ (H : PowerSeries (Qbar l)) (E : Fin β.d → PowerSeries Φ.R), (∀ n, ‖H.coeff n‖ ≤ 1) ∧
      abelian₂ Φ β D = PowerSeries.map (algebraMap (PadicAlgCl l) ℂ_[l]) H + PowerSeries.C ((l : ℂ_[l]) ^ N) * abelian₂ Φ β E := by
  have h : ∀ (i : Fin β.d) (n : ℕ), ∃ (y : R0 A) (e : Φ.R), (D i).coeff n = Φ.i0 y + (l : Φ.R) ^ N * e := by
    intro i n
    obtain ⟨y, hy⟩ := Φ.dense ((D i).coeff n) N
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hy
    exact ⟨y, e, by linear_combination -he⟩
  choose y e hye using h
  refine ⟨PowerSeries.mk fun n => ∑ i, β.val i * j (y i n), fun i => PowerSeries.mk (e i), fun n => ?_, ?_⟩
  · rw [PowerSeries.coeff_mk]
    exact norm_sum_le_one _ _ fun i _ => nmul (hβ i) (hj _ (y i n).2.1)
  · ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), PowerSeries.coeff_C_mul, Lam_coeff, Lam_coeff, PowerSeries.coeff_map, PowerSeries.coeff_mk, Fr.lam, Fr.lam,
      map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hye, PowerSeries.coeff_mk, map_add (f := _), map_mul, map_mul, map_pow, map_natCast, Φ.jh_comp_incl]
    ring

end UpperTheory.Kd.C7.C2

open UpperTheory.Kd.C7.C2 in
theorem UpperTheory.Kd.C7.pClause2 :
    UpperTheory.Kd.C7.SClause2 := by
  intro l _ _ Ω _ _ _ A _ j Φ hj c β D D' Gs v g c₂ k φ θ hg hθ hv _ hD hrel n
  have hβ := ((pBasEx l c).2 β).1
  refine ⟨n + c₂ + 1, fun r hr ξ hξ => ?_⟩
  obtain ⟨a, ha, hint⟩ := intg_lin φ k r ξ hξ
  obtain ⟨H, E, hH, hHE⟩ := approx Φ β hj hβ D' (2 * r)
  have hS := pIntShift l H hH g hg φ k r ξ (by omega) hξ
  set f := algebraMap (PadicAlgCl l) ℂ_[l] with hf
  have h1 : abelian₂ Φ β D = PowerSeries.C v * PowerSeries.map f Gs := by
    ext m
    rw [Lam_coeff, hD, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  have h2 : abelian₂ Φ β (Φ.act (β.mat ((l : c.O) ^ c₂)) D) = abelian₂ Φ β (fun i => sb g (D' i) - Φ.act (β.mat θ) D' i) :=
    congrArg _ (funext hrel)
  rw [Lam_sub, Lam_sb, Lam_act, Lam_act, h1, hHE, map_add (f := _), sb_C, ← map_sb, ← Lam_sb] at h2
  set W := abelian₂ Φ β (fun i => sb g (E i) - Φ.act (β.mat θ) E i) with hW
  have hWle : ∀ m, ‖W.coeff m‖ ≤ 1 := Lam_le Φ β hβ _
  rw [Lam_sub, Lam_act] at hW
  have hl : algebraMap (PadicAlgCl l) ℂ_[l] (((l : c.O) ^ c₂ : c.O) : PadicAlgCl l) = (l : ℂ_[l]) ^ c₂ := by
    simp
  have h3 : ∀ m, (l : ℂ_[l]) ^ c₂ * v * f (Gs.coeff m) =
      f ((sb g H).coeff m - (θ : PadicAlgCl l) * H.coeff m) + (l : ℂ_[l]) ^ (2 * r) * W.coeff m := by
    intro m
    have h4 := congrArg (PowerSeries.coeff m) h2
    rw [hW]
    simp only [map_sub, map_add (f := _), mul_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, map_mul f] at h4 ⊢
    linear_combination h4 - v * f (Gs.coeff m) * hl
  have h5 : (l : ℂ_[l]) ^ c₂ * v * f (intg φ k Gs r ξ) =
      f (intg φ k (sb g H) r ξ - φ (g : ZMod l) * (g : Qbar l) ^ k * intg φ k H r ξ) +
        (l : ℂ_[l]) ^ (2 * r) * ∑ m ∈ Finset.range (l ^ (3 * r)), f (a m) * W.coeff m := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hθ, hint, hint, hint, Finset.mul_sum, ← Finset.sum_sub_distrib, map_sum, map_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h6 := h3 m
    simp only [map_sub, map_mul] at h6 ⊢
    linear_combination f (a m) * h6
  have hfl : ‖(l : ℂ_[l])‖ = ‖(l : Qbar l)‖ := by rw [← nf, map_natCast]
  have h7 : ‖(l : ℂ_[l]) ^ c₂ * v * f (intg φ k Gs r ξ)‖ ≤ ‖(l : Qbar l)‖ ^ (2 * r) := by
    rw [h5]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [hf, nf, ← norm_pow]; exact hS
    · rw [norm_mul, norm_pow, hfl]
      refine mul_le_of_le_one_right (by positivity) (norm_sum_le_one _ _ fun m _ => nmul ?_ (hWle m))
      rw [hf, nf]; exact ha m
  rw [norm_mul, norm_mul, norm_pow, hv, hfl, mul_one, hf, nf] at h7
  have hpos : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hle : ‖(l : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  rw [Cg, sub_zero, norm_pow]
  refine le_of_mul_le_mul_left (h7.trans ?_) (pow_pos hpos c₂)
  rw [← pow_add]
  exact pow_le_pow_of_le_one hpos.le hle (by omega)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Period
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7
open scoped Matrix

namespace UpperTheory.Kd.C7

section
variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l}
  (Φ : Fr l A j) {c : Coef l} (β : Bas c)

end

section
variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l}
  (Φ : Fr l A j) {c : Coef l} (β : Bas c)

end

end UpperTheory.Kd.C7

private theorem ringHom_algebraMap_padicInt_eq {l : ℕ} [Fact (Nat.Prime l)] {R : Type} [CommRing R] [Algebra ℤ_[l] R]
    (hH : IsHausdorff (Ideal.span {(l : R)}) R) (f : R →+* R) (z : ℤ_[l]) :
    f (algebraMap ℤ_[l] R z) = algebraMap ℤ_[l] R z := by
  apply sub_eq_zero.mp
  apply hH.haus
  intro n
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n z)
  have hz : z = ((z.appr n : ℕ) : ℤ_[l]) + w * (l : ℤ_[l]) ^ n := by
    rw [hw]
    ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hz]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  exact ⟨f (algebraMap ℤ_[l] R w) - algebraMap ℤ_[l] R w, by ring⟩

private theorem transpose_leftMulMatrix_mul_structure_mul_eq {l : ℕ} [Fact (Nat.Prime l)] {S : Type} [CommRing S] [Algebra ℤ_[l] S] {d : ℕ}
    (e : Module.Basis (Fin d) ℤ_[l] S) (a b : S) (hab : a * b = 1) (i : Fin d) :
    (Algebra.leftMulMatrix e a)ᵀ * Matrix.of (fun k m => e.repr (e k * e m) i) * Algebra.leftMulMatrix e b =
      Matrix.of (fun k m => e.repr (e k * e m) i) := by
  have hsum : ∀ (y : S) (k' : Fin d), ∑ k, Algebra.leftMulMatrix e y k k' • e k = y * e k' := by
    intro y k'
    simp only [Algebra.leftMulMatrix_eq_repr_mul]
    exact e.sum_repr _
  ext k' m'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have h1 : ∀ m, ∑ k, Algebra.leftMulMatrix e a k k' * e.repr (e k * e m) i = e.repr (a * e k' * e m) i := by
    intro m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum a k', Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  simp only [h1]
  have h2 : ∑ m, e.repr (a * e k' * e m) i * Algebra.leftMulMatrix e b m m' = e.repr (a * e k' * (b * e m')) i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum b m', Finset.mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]
    ring
  rw [h2, show a * e k' * (b * e m') = (a * b) * (e k' * e m') by ring, hab, one_mul]

private theorem sum_algebraMap_basis_mul_eq_algebraMap_sum_smul {l : ℕ} [Fact (Nat.Prime l)] {c : Coef l} (β : Bas c) (z : Fin β.d → ℤ_[l]) :
    ∑ i, algebraMap (PadicAlgCl l) ℂ_[l] (β.val i) *
        algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℤ_[l] (PadicAlgCl l) (z i)) =
      algebraMap (PadicAlgCl l) ℂ_[l] ((∑ i, z i • β.e i : c.O) : PadicAlgCl l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_mul, ← map_sum]
  congr 1
  simp [Bas.val, Algebra.smul_def, mul_comm]

theorem UpperTheory.Kd.C7.pPeriod :
    UpperTheory.Kd.C7.SPeriod := by
  intro l _ _ Ω _ _ _ A _ j Φ c β a ha
  obtain ⟨hval, -, -, -⟩ := (pBasEx l c).2 β
  have hH : IsHausdorff (Ideal.span {(l : Φ.R)}) Φ.R := by
    haveI := Φ.fl.complete
    exact IsAdicComplete.toIsHausdorff
  have hσs : ∀ z : ℤ_[l], Φ.σ.symm (algebraMap ℤ_[l] Φ.R z) = algebraMap ℤ_[l] Φ.R z :=
    fun z => ringHom_algebraMap_padicInt_eq hH Φ.σ.symm.toRingHom z
  set b : c.O := ↑(ha.unit⁻¹) with hb
  have hab : a * b = 1 := ha.mul_val_inv
  have hba : b * a = 1 := ha.val_inv_mul
  set f := algebraMap ℤ_[l] Φ.R with hf
  set Na := (β.mat a).map f with hNa
  set Nb := (β.mat b).map f with hNb
  have hmat : ∀ x y : c.O, β.mat (x * y) = β.mat x * β.mat y := fun x y => map_mul _ x y
  have hmat1 : β.mat 1 = 1 := map_one (Algebra.leftMulMatrix β.e)
  have hNab : Na * Nb = 1 := by
    rw [hNa, hNb, ← Matrix.map_mul, ← hmat, hab, hmat1, Matrix.map_one f (map_zero f) (map_one f)]
  have hNba : Nb * Na = 1 := by
    rw [hNa, hNb, ← Matrix.map_mul, ← hmat, hba, hmat1, Matrix.map_one f (map_zero f) (map_one f)]
  obtain ⟨V, hV, hVσ⟩ := pLangR Φ.R l Φ.σ Φ.fl Φ.unit Φ.closed β.d Na
    (Matrix.isUnit_det_of_right_inverse hNab)
  have hle : ∀ y, ‖Φ.lam β y‖ ≤ 1 := by
    intro y
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro i _
    rw [norm_mul, norm_algebraMap']
    exact mul_le_one₀ (hval i) (norm_nonneg _) (Φ.jh_le _)
  set e1 : Fin β.d → Φ.R := fun i => f (β.e.repr 1 i) with he1
  set s := V⁻¹ *ᵥ e1 with hs
  have hVs : V *ᵥ s = e1 := by
    rw [hs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V hV, Matrix.one_mulVec]
  have h1 : Φ.lam β e1 = 1 := by
    simp only [Fr.lam, he1, hf, Fr.jh_alg]
    rw [sum_algebraMap_basis_mul_eq_algebraMap_sum_smul, β.e.sum_repr]
    simp
  have hsum : (1 : ℂ_[l]) = ∑ m, Φ.jh (s m) * Φ.lam β (fun i => V i m) := by
    rw [← h1, ← hVs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Fr.lam, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
  have hne : (Finset.univ : Finset (Fin β.d)).Nonempty := by
    by_contra hE
    rw [Finset.not_nonempty_iff_eq_empty] at hE
    rw [hE, Finset.sum_empty] at hsum
    exact one_ne_zero hsum
  obtain ⟨m0, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun m => ‖Φ.jh (s m) * Φ.lam β (fun i => V i m)‖) hne
  have hm0 : ‖∑ m, Φ.jh (s m) * Φ.lam β (fun i => V i m)‖ ≤
      ‖Φ.jh (s m0) * Φ.lam β (fun i => V i m0)‖ := by
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) hmax
  rw [← hsum, norm_one, norm_mul] at hm0
  set η : Fin β.d → Φ.R := fun i => V i m0 with hηdef
  set μ := Φ.lam β η with hμdef
  have hμ : ‖μ‖ = 1 :=
    le_antisymm (hle _) (hm0.trans (mul_le_of_le_one_left (norm_nonneg _) (Φ.jh_le _)))
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hμ
    exact zero_ne_one hμ
  refine ⟨μ⁻¹, by rw [norm_inv, hμ, inv_one], ?_⟩
  intro x hx
  have hη : (fun i => Φ.σ (η i)) = Na *ᵥ η := by
    funext i
    have := congrFun (congrFun hVσ i) m0
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hmapv : ∀ (M : Matrix (Fin β.d) (Fin β.d) ℤ_[l]) (w : Fin β.d → Φ.R) (i : Fin β.d),
      Φ.σ.symm ((M.map f *ᵥ w) i) = (M.map f *ᵥ fun k => Φ.σ.symm (w k)) i := by
    intro M w i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hσs]
  have hηs' : η = Na *ᵥ fun k => Φ.σ.symm (η k) := by
    funext i
    have h := congrArg Φ.σ.symm (congrFun hη i)
    simp only [RingEquiv.symm_apply_apply] at h
    rw [h, hNa]
    exact hmapv _ _ i
  have hηs : (fun k => Φ.σ.symm (η k)) = Nb *ᵥ η := by
    conv_rhs => rw [hηs']
    rw [Matrix.mulVec_mulVec, hNba, Matrix.one_mulVec]
  have hxs : (fun k => Φ.σ.symm (x k)) = Na *ᵥ x := by
    funext k
    rw [hx k]
    simp [Matrix.mulVec, dotProduct, hNa]
  set Ci : Fin β.d → Matrix (Fin β.d) (Fin β.d) Φ.R :=
    fun i => (Matrix.of fun k m => β.e.repr (β.e k * β.e m) i).map f with hCi
  have hCfix : ∀ i, Na.transpose * Ci i * Nb = Ci i := by
    intro i
    rw [hNa, hNb, hCi]
    simp only
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun M => M.map f) (transpose_leftMulMatrix_mul_structure_mul_eq β.e a b hab i)
  set P : Fin β.d → Φ.R := fun i => x ⬝ᵥ (Ci i *ᵥ η) with hP
  have hPs : ∀ i, Φ.σ.symm (P i) = P i := by
    intro i
    have h2 : Φ.σ.symm (P i) =
        (fun k => Φ.σ.symm (x k)) ⬝ᵥ (Ci i *ᵥ fun m => Φ.σ.symm (η m)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hP, hCi, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, hσs]
    rw [h2, hxs, hηs]
    calc (Na *ᵥ x) ⬝ᵥ (Ci i *ᵥ (Nb *ᵥ η)) = (x ᵥ* Na.transpose) ⬝ᵥ ((Ci i * Nb) *ᵥ η) := by
          rw [Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ ((Na.transpose * Ci i * Nb) *ᵥ η) := by
          rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
      _ = P i := by rw [hCfix]
  have hPf : ∀ i, Φ.σ (P i) = P i := by
    intro i
    conv_lhs => rw [← hPs i]
    exact Φ.σ.apply_symm_apply _
  choose z hz using fun i => Φ.fixed (P i) (hPf i)
  have key : ∀ k m, ∑ i, algebraMap (PadicAlgCl l) ℂ_[l] (β.val i) *
      algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr (β.e k * β.e m) i)) =
      algebraMap (PadicAlgCl l) ℂ_[l] (β.val k) * algebraMap (PadicAlgCl l) ℂ_[l] (β.val m) := by
    intro k m
    rw [sum_algebraMap_basis_mul_eq_algebraMap_sum_smul, β.e.sum_repr]
    simp [Bas.val]
  have hmul : Φ.lam β P = Φ.lam β x * μ := by
    calc Φ.lam β P = ∑ k, ∑ m, Φ.jh (x k) * Φ.jh (η m) * ∑ i, algebraMap (PadicAlgCl l) ℂ_[l] (β.val i) *
          algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr (β.e k * β.e m) i)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [Fr.lam, hP, hCi, dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.of_apply, map_sum,
            map_mul, hf, Fr.jh_alg, Finset.mul_sum]
          conv_lhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ k, ∑ m, Φ.jh (x k) * Φ.jh (η m) * (algebraMap (PadicAlgCl l) ℂ_[l] (β.val k) *
          algebraMap (PadicAlgCl l) ℂ_[l] (β.val m)) := by
          simp only [key]
      _ = Φ.lam β x * μ := by
          rw [hμdef]
          simp only [Fr.lam]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          clear_value P Ci μ η s e1 Nb Na b f
          ring_nf
          done
  refine ⟨∑ i, z i • β.e i, ?_⟩
  have hPz : P = fun i => f (z i) := funext fun i => (hz i).symm
  have hfin : Φ.lam β x * μ =
      algebraMap (PadicAlgCl l) ℂ_[l] ((∑ i, z i • β.e i : c.O) : PadicAlgCl l) := by
    rw [← hmul, hPz, ← sum_algebraMap_basis_mul_eq_algebraMap_sum_smul]
    simp only [Fr.lam, hf, Fr.jh_alg]
  rw [eq_inv_mul_iff_mul_eq₀ hμ0, mul_comm, hfin]
end

