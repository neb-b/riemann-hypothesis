module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0352
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0345

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroOrdinaryClassOfCompatibleCocyclesModPow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem limit_nonzero_ordinary_class : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (N : ℕ), (∀ n s i, a n s i ∈ c.O) → (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (a (n + 1) s) (a n s)) → (∀ n, ∀ b ∈ (toGS Ω (S : Set Pl)).ker, Cv n (a n b) 0) → (∀ n, ∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, Cv n (a n s) (mat W s *ᵥ y - y)) → (∀ n, ∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, Cg n (a n s 1) (mat W s 1 1 * y - y)) → (¬ ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s, Cv N (a N s) (mat W s *ᵥ y - y)) → ¬ GrZero W A := by
  intro l _ Ω _ _ _ S A W c hWc hWint hg a N ha hcoc hloc hstep hker hine hdec hN hGZ
  obtain ⟨z0, hz0O, hz0⟩ := _root_.GlobalTheory.Ord2.exists_limit_coef l c (G ℚ Ω × Fin 2) (fun n p => a n p.1 p.2) (fun n p => ha n p.1 p.2)
    (fun n p => hstep n p.1 p.2)
  let z : G ℚ Ω → Fin 2 → Qbar l := fun s i => z0 (s, i)
  have hzO : ∀ s i, z s i ∈ c.O := fun s i => hz0O (s, i)
  have hza : ∀ n s, Cv n (z s) (a n s) := fun n s i => hz0 n (s, i)
  have hZ : z ∈ Z1 (Loc.colRep W) := _root_.GlobalTheory.Ord2.limit_cocycle_mem_cocycles l Ω W c hWint a z hcoc hloc hza
  have hcol : ∀ s (v : Fin 2 → Qbar l), Loc.colRep W s v = mat W s *ᵥ v := fun s v => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  have hrow : ∀ s (y : Fin 2 → Qbar l) i, (fun j => (mat W s - 1) i j) ⬝ᵥ y = (mat W s *ᵥ y - y) i := by
    intro s y i
    show ((mat W s - 1) *ᵥ y) i = _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hzker : ∀ b ∈ (toGS Ω (S : Set Pl)).ker, z b = 0 := by
    intro b hb
    funext i
    refine eq_zero_of_forall_norm_le _ fun n => ?_
    have h := cg_trans (hza n b i) (hker n b hb i)
    simp only [Cg, Pi.zero_apply, sub_zero] at h
    exact h
  have hexact : ∀ H : Subgroup (G ℚ Ω), (∀ n, ∃ y : Fin 2 → Qbar l, ∀ s ∈ H, Cv n (a n s) (mat W s *ᵥ y - y)) →
      ∃ x : Fin 2 → Qbar l, ∀ s ∈ H, z s = mat W s *ᵥ x - x := by
    intro H hH
    obtain ⟨x, hx⟩ := _root_.GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow l (↥H × Fin 2) 2 (fun p j => (mat W p.1 - 1) p.2 j) (fun p => z p.1 p.2) (fun n => by
      obtain ⟨y, hy⟩ := hH n
      refine ⟨y, fun p => ?_⟩
      have h := cg_trans (hza n p.1 p.2) (hy p.1 p.1.2 p.2)
      rw [← hrow] at h
      exact h)
    exact ⟨x, fun s hs => funext fun i => by rw [← hrow]; exact hx (⟨s, hs⟩, i)⟩
  have hUnr : Unr W z := by
    intro w hw
    refine ⟨placeOf Ω w, isPlaceOver_placeOf Ω w, ?_⟩
    by_cases hwS : w ∈ S
    · exact hexact (Ine (F := ℚ) (placeOf Ω w)) fun n => by
        obtain ⟨y, -, hy⟩ := hine n w hwS hw _ (isPlaceOver_placeOf Ω w)
        exact ⟨y, hy⟩
    · refine ⟨0, fun s hs => ?_⟩
      have hsN : s ∈ (toGS Ω (S : Set Pl)).ker := by
        show s ∈ (QuotientGroup.mk' (NS Ω (S : Set Pl))).ker
        rw [QuotientGroup.ker_mk']
        apply Subgroup.le_topologicalClosure
        apply Subgroup.subset_normalClosure
        simp only [Set.mem_iUnion]
        exact ⟨w, by simpa using hwS, placeOf Ω w, isPlaceOver_placeOf Ω w, hs⟩
      rw [hzker s hsN]
      simp
  have hGr : Gr W A z := by
    obtain ⟨y, hy⟩ := _root_.GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow l (↥(Dec (F := ℚ) A)) 1 (fun s _ => mat W s 1 1 - 1) (fun s => z s 1) (fun n => by
      obtain ⟨y, -, hy⟩ := hdec n
      refine ⟨fun _ => y, fun s => ?_⟩
      have h := cg_trans (hza n s 1) (hy s s.2)
      have e : (fun _ : Fin 1 => mat W s 1 1 - 1) ⬝ᵥ (fun _ => y) = mat W s 1 1 * y - y := by
        simp [dotProduct]; ring
      rw [e]; exact h)
    refine ⟨y 0, fun s hs => ?_⟩
    have h := hy ⟨s, hs⟩
    rw [h]
    simp [dotProduct]
    ring
  obtain ⟨x, hx⟩ := (mem_coboundaries1 _ _).1 (hGZ z hZ hUnr hGr)
  obtain ⟨g, hdg⟩ := hg
  have hMO : ∀ i j, (mat W g - 1) i j ∈ c.O := by
    intro i j
    rw [Matrix.sub_apply, Matrix.one_apply]
    split_ifs
    · exact c.O.sub_mem (hWint g i j) c.O.one_mem
    · exact c.O.sub_mem (hWint g i j) c.O.zero_mem
  have hdO : (mat W g - 1).det ∈ c.O := by
    rw [Matrix.det_fin_two]
    exact c.O.sub_mem (c.O.mul_mem (hMO 0 0) (hMO 1 1)) (c.O.mul_mem (hMO 0 1) (hMO 1 0))
  have hadjO : ∀ i j, (mat W g - 1).adjugate i j ∈ c.O := by
    intro i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · exact hMO 1 1
    · exact c.O.neg_mem (hMO 0 1)
    · exact c.O.neg_mem (hMO 1 0)
    · exact hMO 0 0
  have hMx : (mat W g - 1) *ᵥ x = z g := by rw [hx g, hcol, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hdx : (mat W g - 1).det • x = (mat W g - 1).adjugate *ᵥ z g := by
    rw [← hMx, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.Ord2.memE_inv_of_mem l c _ hdO hdg
  have hxE : VecE c x := ⟨k, fun i => by
    have e : x i = ((mat W g - 1).det)⁻¹ * ((mat W g - 1).adjugate *ᵥ z g) i := by
      rw [← hdx, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdg, one_mul]
    rw [e, ← mul_assoc]
    refine c.O.mul_mem hk ?_
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.add_mem (c.O.mul_mem (hadjO i 0) (hzO g 0)) (c.O.mul_mem (hadjO i 1) (hzO g 1))⟩
  refine hN ⟨x, hxE, fun s => ?_⟩
  have h := hza N s
  rw [hx s, hcol] at h
  exact cv_symm h

end GlobalTheory.Ord2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.CoefCoord

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral (x : PadicAlgCl l) (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  change spectralValue (minpoly ℚ_[l] x) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hi)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

theorem norm_le_one (c : Coef l) (x : c.O) : ‖(x : PadicAlgCl l)‖ ≤ 1 :=
  norm_le_one_of_isIntegral _
    ((isIntegral_algHom_iff c.O.val Subtype.val_injective).2 (Algebra.IsIntegral.isIntegral x))

theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 := norm_le_one c u
  have h2 := norm_le_one c (↑u⁻¹ : c.O)
  have h3 : ((u : c.O) : PadicAlgCl l) * ((↑u⁻¹ : c.O) : PadicAlgCl l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  have h5 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((↑u⁻¹ : c.O) : PadicAlgCl l)‖ ≤ ‖((u : c.O) : PadicAlgCl l)‖ :=
    mul_le_of_le_one_right (norm_nonneg _) h2
  linarith

theorem norm_natCast_lt_one : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem norm_algebraMap_padicInt (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ = ‖a‖ := by
  show ‖algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l])‖ = ‖a‖
  rw [PadicAlgCl.norm_extends]; rfl

theorem exists_eq_pow_mul (c : Coef l) (m : ℕ) (x : c.O)
    (hx : ‖(x : PadicAlgCl l)‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ m‖) : ∃ z : c.O, x = (l : c.O) ^ m * z := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' := congrArg (fun y : c.O => (y : PadicAlgCl l)) h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero] at h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h'
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hπ
  set q := ‖(π : PadicAlgCl l)‖ with hqdef
  have hlq : ‖((l : ℕ) : PadicAlgCl l)‖ = q ^ e := by
    have h' := congrArg (fun y : c.O => ‖(y : PadicAlgCl l)‖) hw
    simp only [SubringClass.coe_natCast, Subalgebra.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow,
      norm_unit, one_mul] at h'
    exact h'
  have hq0 : 0 < q := by
    rw [hqdef, norm_pos_iff]
    intro h
    exact hπ.ne_zero (Subtype.ext h)
  have hq1 : q < 1 := by
    rcases (norm_le_one c π).lt_or_eq with h | h
    · exact h
    · exfalso
      have := (norm_natCast_lt_one (l := l))
      rw [hlq, hqdef, h, one_pow] at this
      exact lt_irrefl _ this
  have hxq : ‖(((u : c.O) * π ^ k : c.O) : PadicAlgCl l)‖ = q ^ k := by
    simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
    rfl
  rw [hxq, norm_pow, hlq, ← pow_mul] at hx
  have hk : e * m ≤ k := (pow_le_pow_iff_right_of_lt_one₀ hq0 hq1).1 hx
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨(u : c.O) * (↑w⁻¹ : c.O) ^ m * π ^ r, ?_⟩
  rw [hw]
  have h2 : ((w : c.O) * (↑w⁻¹ : c.O)) ^ m = 1 := by rw [Units.mul_inv, one_pow]
  linear_combination (-((u : c.O) * π ^ (e * m + r))) * h2

theorem norm_sub_val_le (m : ℕ) (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a - (((PadicInt.toZModPow m a).val : ℕ) : PadicAlgCl l)‖
      ≤ ‖((l : ℕ) : PadicAlgCl l) ^ m‖ := by
  have hk : a - (((PadicInt.toZModPow m a).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p := l) m) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨t, ht⟩ := hk
  have e : algebraMap ℤ_[l] (PadicAlgCl l) a - (((PadicInt.toZModPow m a).val : ℕ) : PadicAlgCl l)
      = algebraMap ℤ_[l] (PadicAlgCl l) t * ((l : ℕ) : PadicAlgCl l) ^ m := by
    have := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) ht
    simp only [map_mul, map_pow, map_natCast, map_sub] at this
    rw [this]
  rw [e, norm_mul, norm_algebraMap_padicInt]
  exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one t)

theorem coe_eq_sum {ι : Type} [Fintype ι] (c : Coef l) (b : Module.Basis ι ℤ_[l] c.O) (y : c.O) :
    (y : PadicAlgCl l) = ∑ i, ((b i : c.O) : PadicAlgCl l) * algebraMap ℤ_[l] (PadicAlgCl l) (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr y]
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subalgebra.coe_smul, Algebra.smul_def, mul_comm]

theorem coord_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (m : ℕ), ∃ (ι : Type) (_ : Fintype ι) (o : ι → Qbar l)
    (crd : Qbar l → ι → ZMod (l ^ m)), (∀ i, o i ∈ c.O ∧ ‖o i‖ ≤ 1) ∧
    (∀ x ∈ c.O, ∀ y ∈ c.O, crd (x + y) = crd x + crd y) ∧ (∀ x ∈ c.O, Cg m x 0 → crd x = 0) ∧
    (∀ x ∈ c.O, Cg m x (∑ i, o i * ((crd x i).val : Qbar l))) ∧
    (∀ n : ι → ZMod (l ^ m), Cg m (∑ i, o i * ((n i).val : Qbar l)) 0 → n = 0) := by
  intro l _ c m
  classical
  let b := Module.Free.chooseBasis ℤ_[l] c.O
  let crd : Qbar l → Module.Free.ChooseBasisIndex ℤ_[l] c.O → ZMod (l ^ m) := fun x i =>
    if hx : x ∈ c.O then PadicInt.toZModPow m (b.repr ⟨x, hx⟩ i) else 0
  have hcrd : ∀ (x : Qbar l) (hx : x ∈ c.O) i, crd x i = PadicInt.toZModPow m (b.repr ⟨x, hx⟩ i) :=
    fun x hx i => dif_pos hx
  have hkill : ∀ x ∈ c.O, Cg m x 0 → crd x = 0 := by
    intro x hx h
    unfold Cg at h
    rw [sub_zero] at h
    obtain ⟨z, hz⟩ := exists_eq_pow_mul c m ⟨x, hx⟩ h
    funext i
    rw [hcrd x hx i, hz]
    have e : ((l : c.O) ^ m * z) = ((l : ℤ_[l]) ^ m) • z := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, ← Nat.cast_pow,
      ZMod.natCast_self, zero_mul]
    rfl
  refine ⟨Module.Free.ChooseBasisIndex ℤ_[l] c.O, inferInstance, fun i => ((b i : c.O) : PadicAlgCl l), crd,
    fun i => ⟨(b i).2, norm_le_one c (b i)⟩, ?_, hkill, ?_, ?_⟩
  · intro x hx y hy
    funext i
    rw [hcrd _ (add_mem hx hy), Pi.add_apply, hcrd x hx, hcrd y hy,
      show (⟨x + y, add_mem hx hy⟩ : c.O) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add, Finsupp.add_apply, map_add]
  · intro x hx
    unfold Cg
    have hx' := coe_eq_sum c b ⟨x, hx⟩
    change x = _ at hx'
    simp only [hcrd x hx]
    rw [congrArg (fun t => t - _) hx', ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [← mul_sub, norm_mul]
    exact (mul_le_mul (norm_le_one c (b i)) (norm_sub_val_le m _) (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
  · intro n hn
    set y : Qbar l := ∑ i, ((b i : c.O) : PadicAlgCl l) * (((n i).val : ℕ) : Qbar l) with hydef
    have hy : y ∈ c.O := Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (b i).2 (Subalgebra.natCast_mem _ _)
    have hyb : (⟨y, hy⟩ : c.O) = ∑ i, (((n i).val : ℕ) : ℤ_[l]) • b i := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Subalgebra.coe_smul, Algebra.smul_def, map_natCast, mul_comm]
    have h0 := hkill y hy hn
    funext i
    have := congrFun h0 i
    rw [hcrd y hy i, hyb, b.repr_sum_self, map_natCast, ZMod.natCast_zmod_val] at this
    exact this

end GlobalTheory.CoefCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory.AmiceDist

variable {l : ℕ} [Fact l.Prime]

theorem sum_level (μ : ∀ r : ℕ, ZMod (l ^ r) → Qbar l)
    (hμ : ∀ r (x : ZMod (l ^ r)), μ r x = ∑ x' ∈ Finset.univ.filter
      (fun x' : ZMod (l ^ (r + 1)) => ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) x' = x), μ (r + 1) x')
    {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) (R : ℕ) (hR : r ≤ R) :
    ∑ x : ZMod (l ^ R), μ R x * z ^ x.val = ∑ x : ZMod (l ^ r), μ r x * z ^ x.val := by
  induction R, hR using Nat.le_induction with
  | base => rfl
  | succ R hR ih =>
    rw [← ih]
    have hzR : z ^ (l ^ R) = 1 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hR
      rw [pow_add, pow_mul, hz, one_pow]
    rw [← Finset.sum_fiberwise Finset.univ
      (fun x' : ZMod (l ^ (R + 1)) => ZMod.castHom (pow_dvd_pow l (Nat.le_succ R)) (ZMod (l ^ R)) x')]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hμ R x, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    rw [← (Finset.mem_filter.1 hx').2, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
      ← pow_eq_pow_mod _ hzR]

theorem norm_trunc_binomial {w : Qbar l} (hw : ‖w‖ ≤ 1) (N k : ℕ) :
    ‖∑ n ∈ Finset.range N, (k.choose n : Qbar l) * w ^ n - (w + 1) ^ k‖ ≤ ‖w‖ ^ N := by
  have h1 : (w + 1) ^ k = ∑ n ∈ Finset.range (N + (k + 1)), (k.choose n : Qbar l) * w ^ n := by
    rw [add_pow]
    simp only [one_pow, mul_one]
    simp_rw [mul_comm (w ^ _)]
    refine Finset.sum_subset (Finset.range_mono (Nat.le_add_left _ _)) fun n _ hn => ?_
    rw [Nat.choose_eq_zero_of_lt (by simpa using hn)]
    simp
  rw [h1, Finset.sum_range_add, sub_add_cancel_left, norm_neg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i _ => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (IsUltrametricDist.norm_natCast_le_one _ _)).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hw (Nat.le_add_right _ _))

theorem norm_sub_one_le {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) : ‖z - 1‖ ≤ 1 := by
  have h : ‖z‖ = 1 := by
    have h1 := congrArg norm hz
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 h1
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  simp [h]

theorem norm_sub_one_pow_le {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) : ‖z - 1‖ ^ (l ^ r) ≤ ‖((l : ℕ) : Qbar l)‖ := by
  have hw := norm_sub_one_le hz
  have h := (Commute.all (z - 1) 1).add_pow_prime_pow_eq (Fact.out : l.Prime) r
  rw [sub_add_cancel, hz] at h
  simp only [one_pow, mul_one] at h
  have h2 : (z - 1) ^ (l ^ r) = -((l : Qbar l) * (z - 1) *
      ∑ k ∈ Finset.Ioo 0 (l ^ r), (z - 1) ^ (k - 1) * (((l ^ r).choose k / l : ℕ) : Qbar l)) := by
    linear_combination -h
  rw [← norm_pow, h2, norm_neg, norm_mul, norm_mul]
  have h3 : ‖∑ k ∈ Finset.Ioo 0 (l ^ r), (z - 1) ^ (k - 1) * (((l ^ r).choose k / l : ℕ) : Qbar l)‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hw) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  calc _ ≤ ‖((l : ℕ) : Qbar l)‖ * 1 * 1 := by gcongr
    _ = _ := by ring

theorem norm_sub_one_pow_three_le {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) :
    ‖z - 1‖ ^ (l ^ (3 * r)) ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
  rw [show 3 * r = r + 2 * r by ring, pow_add, pow_mul, norm_pow]
  refine (pow_le_pow_left₀ (by positivity) (norm_sub_one_pow_le hz) _).trans ?_
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
    (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le

theorem amice : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (μ : ∀ r : ℕ, ZMod (l ^ r) → Qbar l), (∀ r x, μ r x ∈ c.O) →
    (∀ r (x : ZMod (l ^ r)), μ r x = ∑ x' ∈ Finset.univ.filter
      (fun x' : ZMod (l ^ (r + 1)) => ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) x' = x), μ (r + 1) x') →
    ∃ L : PowerSeries (Qbar l), (∀ n, L.coeff n ∈ c.O) ∧ ∀ r, 1 ≤ r → ∀ z : Qbar l, z ^ (l ^ r) = 1 →
      Cg (2 * r) (tval L (l ^ (3 * r)) z) (∑ x : ZMod (l ^ r), μ r x * z ^ x.val) := by
  intro l _ c μ hO hμ
  let a : ℕ → ℕ → Qbar l := fun n R => ∑ x : ZMod (l ^ R), μ R x * (x.val.choose n : Qbar l)
  have ha : ∀ n R, a n R ∈ c.O := fun n R => sum_mem fun x _ => mul_mem (hO R x) (natCast_mem _ _)
  have hlim : ∀ n, ∃ b ∈ c.O, Filter.Tendsto (a n) (Filter.hyperfilter ℕ) (nhds b) := by
    intro n
    obtain ⟨b, hb, h⟩ := (GlobalTheory.Coef.isCompact_O l c).ultrafilter_le_nhds ((Filter.hyperfilter ℕ).map (a n))
      (by
        rw [Filter.le_principal_iff]
        exact Filter.mem_map.2 (Filter.univ_mem' fun R => ha n R))
    exact ⟨b, hb, h⟩
  choose b hb hab using hlim
  refine ⟨PowerSeries.mk b, fun n => by simpa using hb n, fun r _ z hz => ?_⟩
  unfold Cg tval
  simp only [PowerSeries.coeff_mk]
  have ht : Filter.Tendsto (fun R => ‖∑ n ∈ Finset.range (l ^ (3 * r)), a n R * (z - 1) ^ n -
      ∑ x : ZMod (l ^ r), μ r x * z ^ x.val‖) (Filter.hyperfilter ℕ)
      (nhds ‖∑ n ∈ Finset.range (l ^ (3 * r)), b n * (z - 1) ^ n - ∑ x : ZMod (l ^ r), μ r x * z ^ x.val‖) :=
    ((tendsto_finsetSum _ fun n _ => (hab n).mul_const _).sub_const _).norm
  refine le_of_tendsto ht ?_
  have hev : ∀ᶠ R in (Filter.hyperfilter ℕ : Filter ℕ), r ≤ R :=
    Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop r)
  filter_upwards [hev] with R hR
  rw [← sum_level μ hμ hz R hR]
  simp only [a, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x _ => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← mul_sub, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (FirstDer.norm_le_one_of_mem c (hO R x))).trans ?_
  have h := norm_trunc_binomial (norm_sub_one_le hz) (l ^ (3 * r)) x.val
  rw [sub_add_cancel] at h
  exact h.trans (norm_sub_one_pow_three_le hz)

end GlobalTheory.AmiceDist
end

