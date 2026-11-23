module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0069
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CuspMean
section
open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf Filter Topology
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Br

private theorem cm_aff_add {R : Type} [CommRing R] (x y : R) : aff 1 (x + y) = aff 1 x * aff 1 y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem cm_map_aff {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map p (aff 1 x) = aff 1 (p x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.GeneralLinearGroup.map]

private theorem cm_aff_zero {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem cm_continuous_aff {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun x : R => aff (1 : Rˣ) x := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · change Continuous fun x : R => (!![(((1 : Rˣ)⁻¹ : Rˣ) : R), -((((1 : Rˣ)⁻¹ : Rˣ) : R) * x); 0, 1] : Matrix (Fin 2) (Fin 2) R)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private noncomputable def eR (t : ℝ) : Ad ℚ := TR.sInf ℚ (algebraMap ℝ (TR.Rinf ℚ) t)

private theorem pInf_eR (t : ℝ) : TR.pInf ℚ (eR t) = algebraMap ℝ (TR.Rinf ℚ) t := (TR.infEq ℚ).symm_apply_apply _

private theorem pFin_eR (t : ℝ) : pFin ℚ (eR t) = 0 := rfl

private theorem pInf_sFin (a : Af ℚ) : TR.pInf ℚ (sFin ℚ a) = 0 := map_zero (TR.infEq ℚ).symm

private theorem pFin_sFin (a : Af ℚ) : pFin ℚ (sFin ℚ a) = a := rfl

private theorem pInf_rat (q : ℚ) : TR.pInf ℚ (algebraMap ℚ (Ad ℚ) q) = algebraMap ℝ (TR.Rinf ℚ) (q : ℝ) :=
  DFunLike.congr_fun (Subsingleton.elim ((TR.pInf ℚ).comp (algebraMap ℚ (Ad ℚ)))
    ((algebraMap ℝ (TR.Rinf ℚ)).comp (Rat.castHom ℝ))) q

private theorem pFin_rat (q : ℚ) : pFin ℚ (algebraMap ℚ (Ad ℚ) q) = algebraMap ℚ (Af ℚ) q := rfl

private theorem eR_add (s t : ℝ) : eR (s + t) = eR s + eR t := by simp only [eR, map_add (f := _)]

private theorem cm_upR_aff (t : ℝ) : upR (aff 1 t) = aff 1 (eR t) :=
  TR.ga_ext (by simp [upR, cm_map_aff, pInf_eR]) (by simp [upR, cm_map_aff, pFin_eR, cm_aff_zero])

private theorem cm_finGL_aff (a : Af ℚ) : finGL ℚ 2 (aff 1 a) = aff 1 (sFin ℚ a) :=
  TR.ga_ext (by simp [cm_map_aff, pInf_sFin, cm_aff_zero]) (by simp [cm_map_aff, pFin_sFin])

private theorem cm_decomp (x : Ad ℚ) (q : ℚ) :
    ∃ s : ℝ, x = algebraMap ℚ (Ad ℚ) q + eR s + sFin ℚ (pFin ℚ x - algebraMap ℚ (Af ℚ) q) := by
  refine ⟨ev (TR.pInf ℚ x) - q, TR.ad_ext ?_ ?_⟩
  · rw [map_add (f := _), map_add (f := _), pInf_rat, pInf_eR, pInf_sFin, add_zero, ← map_add (f := _), add_sub_cancel]
    funext v
    rw [Subsingleton.elim v Rat.infinitePlace]
    rfl
  · rw [map_add (f := _), map_add (f := _), pFin_rat, pFin_eR, pFin_sFin, add_zero, add_sub_cancel]

private theorem cm_mean {ψ : Ad ℚ → ℂ} {U : Set (Af ℚ)} (hU : IsOpen U) (h0 : 0 ∈ U) {N : ℕ} (hN : (N : Af ℚ) ∈ U)
    (hq : ∀ (q : ℚ) x, ψ (algebraMap ℚ (Ad ℚ) q + x) = ψ x) (hu : ∀ a ∈ U, ∀ x, ψ (x + sFin ℚ a) = ψ x) :
    Function.Periodic (fun t : ℝ => ψ (eR t)) N ∧ ∀ x, ∫ t in (0 : ℝ)..N, ψ (eR t + x) = ∫ t in (0 : ℝ)..N, ψ (eR t) := by
  have hp : Function.Periodic (fun t : ℝ => ψ (eR t)) N := fun t => by
    have e : eR (t + N) + sFin ℚ (N : Af ℚ) = algebraMap ℚ (Ad ℚ) (N : ℚ) + eR t := by
      refine TR.ad_ext ?_ ?_
      · rw [map_add (f := _), map_add (f := _), pInf_rat, pInf_eR, pInf_eR, pInf_sFin, add_zero, Rat.cast_natCast, map_add (f := _), add_comm]
      · rw [map_add (f := _), map_add (f := _), pFin_rat, pFin_eR, pFin_eR, pFin_sFin, zero_add, add_zero, map_natCast]
    beta_reduce
    rw [← hu _ hN, e, hq]
  refine ⟨hp, fun x => ?_⟩
  obtain ⟨q, hq'⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing ℚ).exists_mem_open
    (hU.preimage (continuous_const.sub continuous_id : Continuous fun z : Af ℚ => pFin ℚ x - z)) ⟨pFin ℚ x, by simpa using h0⟩
  obtain ⟨s, hs⟩ := cm_decomp x q
  have e : ∀ t, ψ (eR t + x) = ψ (eR (t + s)) := fun t => by
    rw [hs, ← add_assoc, hu (pFin ℚ x - algebraMap ℚ (Af ℚ) q) hq', add_left_comm, hq, eR_add]
  simp only [e]
  rw [intervalIntegral.integral_comp_add_right (fun t => ψ (eR t)) s, zero_add, add_comm,
    hp.intervalIntegral_add_eq s 0, zero_add]

open GroundTheory.Automorphic.AutomorphicForm in
private theorem cm_fund : ∃ (_ : MeasurableSpace (BlockIx 2 1 → Ad ℚ)) (_ : BorelSpace (BlockIx 2 1 → Ad ℚ))
    (μ : Measure (BlockIx 2 1 → Ad ℚ)) (D : Set (BlockIx 2 1 → Ad ℚ)), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratN ℚ 2 1) D μ := by
  have hμ : (unipMeasure ℚ 2 1).IsAddHaarMeasure := inferInstance
  have hB : BorelSpace (UPos 2 1 → AdeleRing (𝓞 ℚ) ℚ) := inferInstance
  have hL : ratN ℚ 2 1 = unipLattice ℚ 2 1 := AddSubgroup.ext fun x =>
    ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  exact ⟨_, hB, unipMeasure ℚ 2 1, unipFundamentalDomain ℚ 2 1, hμ, by
    rw [hL]; exact isAddFundamentalDomain_unipFundamentalDomain⟩

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.cuspMean :
    UpperTheory.V.Br.CuspMean := by
  intro φ hφ g
  have hl := hφ.1.left
  have ho := hφ.1.level
  set u : GL (Fin 2) (Af ℚ) := Matrix.GeneralLinearGroup.map (pFin ℚ) g with hu
  have hc : Continuous fun x : Af ℚ => u⁻¹ * aff 1 x * u := (continuous_const.mul cm_continuous_aff).mul continuous_const
  have hU := ho.preimage hc
  have h0 : (0 : Af ℚ) ∈ (fun x : Af ℚ => u⁻¹ * aff 1 x * u) ⁻¹' {k | TR.finRep ℚ 2 k φ = φ} := by
    simp [cm_aff_zero]
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ).eventually (hU.mem_nhds h0)).exists
  refine ⟨n.factorial, n.factorial_pos, fun y => ?_⟩
  set N : ℕ := n.factorial
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 n.factorial_pos
  have hq : ∀ (q : ℚ) x, φ.1 (aff 1 (algebraMap ℚ (Ad ℚ) q + x) * (g * upR y)) = φ.1 (aff 1 x * (g * upR y)) := fun q x => by
    rw [cm_aff_add, ← cm_map_aff, mul_assoc]
    exact hl _ _
  obtain ⟨hp, hm⟩ := cm_mean (ψ := fun x => φ.1 (aff 1 x * (g * upR y))) hU h0 hn hq fun a ha x => by
    have h1 : ∀ g, φ.1 (g * finGL ℚ 2 (u⁻¹ * aff 1 a * u)) = φ.1 g := fun g => congrFun (congrArg Subtype.val ha) g
    have e1 : g * upR y * finGL ℚ 2 (u⁻¹ * aff 1 a * u) = finGL ℚ 2 (aff 1 a) * (g * upR y) :=
      TR.ga_ext (by simp) (by simp [upR, ← hu, mul_assoc])
    rw [cm_aff_add, ← cm_finGL_aff, mul_assoc, ← e1, ← mul_assoc, h1]
  simp only [cm_upR_aff]
  refine ⟨hp, ?_⟩
  set c := ∫ t in (0 : ℝ)..N, φ.1 (aff 1 (eR t) * (g * upR y))
  obtain ⟨_, _, μ, D, hμ, hD⟩ := cm_fund
  obtain ⟨i1, i2, i3, i4, hco, hcu, hx⟩ := UpperTheory.eisenstein_constantTerm_upperBlock ℚ
  have hψ : Continuous fun x : BlockIx 2 1 → Ad ℚ => φ.1 (unip x * (g * upR y)) :=
    (smCont ℚ 2 φ ho).comp (hcu.mul continuous_const)
  have hinv : ∀ γ ∈ ratN ℚ 2 1, ∀ x, φ.1 (unip (γ + x) * (g * upR y)) = φ.1 (unip x * (g * upR y)) := by
    rintro _ ⟨q, rfl⟩ x
    rw [hx, hx]
    exact hq _ _
  obtain ⟨hfin, hP⟩ := UpperTheory.periodic_integral_fundamentalDomain_invariant _ (ratN ℚ 2 1) hco μ D hD
  have hint := (hP _ hinv).1 hψ
  have he : Continuous fun (t : ℝ) (_ : BlockIx 2 1) => eR t := continuous_pi fun _ =>
    (((TR.continuous_infEq ℚ).comp (continuous_algebraMap ℝ (TR.Rinf ℚ))).prodMk continuous_const :
      Continuous fun t : ℝ => ((TR.infEq ℚ (algebraMap ℝ (TR.Rinf ℚ) t), 0) :
        InfiniteAdeleRing ℚ × Af ℚ))
  have key := avgZero _ (ratN ℚ 2 1) μ D hμ hD (fun x => φ.1 (unip x * (g * upR y)) - c / N) (hψ.sub continuous_const)
    (fun γ hγ x => by rw [hinv γ hγ]) _ he N hN fun x => by
      have h2 : Continuous fun t : ℝ => φ.1 (unip ((fun _ => eR t) + x) * (g * upR y)) := hψ.comp (he.add continuous_const)
      rw [intervalIntegral.integral_sub (h2.intervalIntegrable _ _) (by simp)]
      simp only [hx]
      rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul, Complex.ofReal_natCast,
        mul_div_cancel₀ _ (Nat.cast_ne_zero.2 n.factorial_pos.ne'), sub_eq_zero]
      exact hm _
  rw [integral_sub hint (integrableOn_const hfin), hφ.2 1 one_pos one_lt_two μ D hμ hD, setIntegral_const, zero_sub, neg_eq_zero,
    smul_eq_zero, div_eq_zero_iff] at key
  rcases key with key | key | key
  · exact absurd key (ENNReal.toReal_ne_zero.2 ⟨hD.measure_ne_zero (NeZero.ne μ), hfin⟩)
  · exact key
  · exact absurd key (Nat.cast_ne_zero.2 n.factorial_pos.ne')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CuspSet
section
open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Eis
open scoped Matrix

namespace UpperTheory.V.Br.CuspStabilizer

section Aff
variable {R S : Type} [CommRing R] [CommRing S]

private theorem aff_mul (y y' : Rˣ) (x x' : R) : aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem aff_one : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem corner_aff (s : R →ₙ+* S) (y : Rˣ) (x : R) : cornerGL 2 s (aff y x) = aff (Units.map (corner s) y) (s x) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (aff y x i j) = _
  fin_cases i <;> fin_cases j <;> simp [aff, corner]

private theorem continuous_aff [TopologicalSpace R] [IsTopologicalRing R] : Continuous fun y : Rˣ => aff y (0 : R) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop

end Aff

variable {F : Type} [Field F] [NumberField F]

private noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

private noncomputable def eps (s : InfinitePlace F → ℤˣ) : TR.Kinf F 2 :=
  ⟨!![1, 0; 0, fun v => ((s v : ℤ) : ℝ)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    rcases Int.units_eq_one_or (s v) with h | h <;> simp [h]⟩

private theorem real_dec {a b c d : ℝ} (h1 : a * a + b * b = 1) (h2 : a * c + b * d = 0) (h3 : c * c + d * d = 1) :
    ∃ (s : ℤˣ) (t : ℝ), a = Real.cos t ∧ b = Real.sin t ∧ c = -((s : ℤ) * Real.sin t) ∧ d = (s : ℤ) * Real.cos t := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, h1, Real.sqrt_one]
  have h0 : (⟨a, b⟩ : ℂ) ≠ 0 := fun h => by simp [h] at hn
  have ha : a = Real.cos (Complex.arg ⟨a, b⟩) := by rw [Complex.cos_arg h0, hn, div_one]
  have hb : b = Real.sin (Complex.arg ⟨a, b⟩) := by rw [Complex.sin_arg, hn, div_one]
  have hc : c = -((a * d - b * c) * b) := by linear_combination (-c) * h1 + a * h2
  have hd : d = (a * d - b * c) * a := by linear_combination (-d) * h1 + b * h2
  have hs : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h1 + h3 - (a * c + b * d) * h2
  rcases mul_self_eq_one_iff.1 hs with h | h
  · exact ⟨1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩
  · exact ⟨-1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩

omit [NumberField F] in
private theorem dec (x : TR.Kinf F 2) : ∃ s θ, x = eps s * rot θ := by
  have h := Matrix.mem_unitaryGroup_iff.1 x.2
  have e : ∀ i j v, x.1 i 0 v * x.1 j 0 v + x.1 i 1 v * x.1 j 1 v = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v := fun i j v => by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  choose s θ h1 h2 h3 h4 using fun v => real_dec (a := x.1 0 0 v) (b := x.1 0 1 v) (c := x.1 1 0 v) (d := x.1 1 1 v)
    (by simpa using e 0 0 v) (by simpa using e 0 1 v) (by simpa using e 1 1 v)
  refine ⟨s, θ, ?_⟩
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, eps, Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, h3, h4]

variable [IsTotallyReal F]

private def stab (M : ℕ) (g : GA F 2) : Subgroup (Ideles F) where
  carrier := {u | ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff (t * u) 0 * g ∈ Z ↔ aff t 0 * g ∈ Z}
  one_mem' := fun Z _ t => by rw [mul_one]
  mul_mem' := fun {a b} ha hb Z hZ t => by rw [← mul_assoc, hb Z hZ, ha Z hZ]
  inv_mem' := fun {a} ha Z hZ t => by rw [← ha Z hZ, inv_mul_cancel_right]

private theorem mem_stab {M : ℕ} {g : GA F 2} {u : Ideles F}
    (h1 : ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z → aff (t * u) 0 * g ∈ Z)
    (h2 : ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z → aff (t * u⁻¹) 0 * g ∈ Z) : u ∈ stab M g :=
  fun Z hZ t => ⟨fun h => by simpa only [mul_inv_cancel_right] using h2 Z hZ _ h, h1 Z hZ t⟩

private theorem stab_fin {M : ℕ} (hM : 1 ≤ M) (g : GA F 2) : (stab M g).FiniteIndex := by
  have am : ∀ t u : Ideles F, aff (t * u) (0 : Ad F) = aff u 0 * aff t 0 := fun t u => by rw [aff_mul, mul_comm]; simp
  have h1 : ∀ a : Fˣ, ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z → aff (t * diagUnits F a) 0 * g ∈ Z :=
    fun a Z hZ t h => by rw [am, mul_assoc]; exact hZ.rat a _ h
  have h2 : ∀ y : (TR.Rinf F)ˣ, (∀ v, 0 < y.val v) → ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z →
      aff (t * TR.infId F y) 0 * g ∈ Z := fun y hy Z hZ t h => by
    have := hZ.pos y hy _ h
    rw [TR.infGL, corner_aff, map_zero] at this
    rw [am, mul_assoc]; exact this
  set k := Matrix.GeneralLinearGroup.map (pFin F) g with hk
  have h3 : ∀ u : (Af F)ˣ, k⁻¹ * aff u 0 * k ∈ KLev F 2 M → ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z →
      aff (t * finId F u) 0 * g ∈ Z := fun u hu Z hZ t h => by
    have e : aff (finId F u) 0 * g = g * finGL F 2 (k⁻¹ * aff u 0 * k) := by
      have : aff (finId F u) 0 = finGL F 2 (aff u 0) := by rw [finGL, corner_aff, map_zero]; rfl
      rw [this]
      exact TR.ga_ext (by simp) (by simp [k, mul_assoc])
    rw [mul_comm t, am, mul_assoc, e, ← mul_assoc]
    exact hZ.lev _ hu _ h
  refine (UpperTheory.ray_class_group_finite F (stab M g) (fun a => mem_stab (h1 a) ?_) (fun y hy => mem_stab (h2 y hy) ?_) ?_).2
  · rw [← map_inv]; exact h1 _
  · rw [← map_inv]
    refine h2 _ fun v => ?_
    have h : y.val v * (y⁻¹).val v = 1 := congrFun y.mul_inv v
    exact (mul_pos_iff_of_pos_left (hy v)).1 (h ▸ one_pos)
  · have h4 := ((isOpen_KLev (F := F) (n := 2) hM).preimage (f := fun u : (Af F)ˣ => k⁻¹ * aff u 0 * k)
      ((continuous_const.mul continuous_aff).mul continuous_const)).mem_nhds (x := 1) (by simp [aff_one])
    filter_upwards [h4] with u hu
    refine mem_stab (h3 u hu) ?_
    rw [← map_inv]
    refine h3 _ ?_
    have e : aff u⁻¹ (0 : Af F) = (aff u 0)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [aff_mul]; simp [aff_one])
    have := (KLev F 2 M).inv_mem hu
    rw [e]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using this

end UpperTheory.V.Br.CuspStabilizer

open UpperTheory.V.Br.CuspStabilizer in
theorem UpperTheory.V.Br.cuspSet :
    UpperTheory.V.Br.CuspSet := by
  intro F _ _ _ M hM
  haveI : CompactSpace (KLev F 2 1) := isCompact_iff_compactSpace.1 (isCompact_KLev le_rfl)
  haveI : Finite (KLev F 2 1 ⧸ (KLev F 2 M).subgroupOf (KLev F 2 1)) :=
    Subgroup.quotient_finite_of_isOpen _ ((isOpen_KLev hM).preimage continuous_subtype_val)
  let b : (InfinitePlace F → ℤˣ) × (KLev F 2 1 ⧸ (KLev F 2 M).subgroupOf (KLev F 2 1)) → GA F 2 := fun p =>
    TR.infGL F 2 (Unitary.toUnits (eps p.1)) * finGL F 2 p.2.out.1
  haveI : ∀ g : GA F 2, (stab M g).FiniteIndex := stab_fin hM
  refine ⟨⋃ p, Set.range fun q : Ideles F ⧸ stab M (b p) => aff q.out 0 * b p,
    Set.finite_iUnion fun p => Set.finite_range _, fun Z hS hZ => Set.eq_univ_of_forall fun g => ?_⟩
  have h1 : ∀ p t, aff t 0 * b p ∈ Z := fun p t => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (stab M (b p)) t
    refine (h.2 Z hZ t).1 ?_
    rw [← hh]
    exact hS (Set.mem_iUnion.2 ⟨p, _, rfl⟩)
  obtain ⟨z, y, x, r, u, hu, rfl⟩ := UpperTheory.V.Br.iwasawaA F g
  obtain ⟨s, θ, rfl⟩ := dec r
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((KLev F 2 M).subgroupOf (KLev F 2 1)) ⟨u, hu⟩
  have h2 := hZ.lev _ ((KLev F 2 M).inv_mem h.2) _ (h1 (s, QuotientGroup.mk ⟨u, hu⟩) y)
  have h3 := hZ.cent z _ (hZ.unip x _ (hZ.rot θ (Unitary.toUnits (rot θ)) rfl _ h2))
  have e1 : aff y x = aff 1 x * aff y 0 := by rw [aff_mul]; simp
  convert h3 using 1
  simp only [b, hh, e1, mul_assoc, map_mul, Subgroup.coe_mul, map_inv]
  rw [TR.infGL_comm]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.DownChar
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd Matrix CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

private theorem loc_unit {R : Type} [CommRing R] [IsLocalRing R] {d N : R} (h : IsCoprime d N) : ∃ y, IsUnit (d + N * y) := by
  by_cases hd : IsUnit d
  · exact ⟨0, by simpa using hd⟩
  · obtain ⟨a, b, e⟩ := h
    have hN : IsUnit N := by
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one e with h | h
      · exact absurd (isUnit_of_mul_isUnit_right h) hd
      · exact isUnit_of_mul_isUnit_right h
    refine ⟨1, ?_⟩
    have : IsUnit ((d + N * 1) + -d) := by simpa using hN
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add this with h | h
    · exact h
    · exact absurd h.neg (by simpa using hd)

private noncomputable def jj : (∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) →+* Af ℚ where
  toFun x := ⟨fun v => (x v : v.adicCompletion ℚ), Filter.Eventually.of_forall fun v => (x v).2⟩
  map_one' := FiniteAdeleRing.ext _ fun _ => rfl
  map_mul' _ _ := FiniteAdeleRing.ext _ fun _ => rfl
  map_zero' := FiniteAdeleRing.ext _ fun _ => rfl
  map_add' _ _ := FiniteAdeleRing.ext _ fun _ => rfl

private theorem jj_mem (x) : jj x ∈ Ohat ℚ := by
  rw [Ohat, Subring.mem_iInf]
  exact fun v => (x v).2

private theorem ex_unit {d : ℤ} {N : ℕ} (h : IsCoprime d (N : ℤ)) :
    ∃ u, IsZU u ∧ ∃ y ∈ Ohat ℚ, (u : Af ℚ) - d = N * y := by
  choose y hy using fun v : HeightOneSpectrum (𝓞 ℚ) =>
    loc_unit (h.map (Int.castRingHom (v.adicCompletionIntegers ℚ)))
  have hu : IsUnit ((d : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) + N * y) :=
    Pi.isUnit_iff.2 fun v => by simpa using hy v
  obtain ⟨w, hw⟩ := hu
  refine ⟨Units.map jj.toMonoidHom w, ⟨jj_mem _, jj_mem _⟩, jj y, jj_mem _, ?_⟩
  change jj w - d = _
  rw [hw]
  simp

private theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (u : Rˣ) :
    cornerGL 2 s (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (Units.map (corner s) u) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (Matrix.scalar (Fin 2) u.val i j) =
    Matrix.scalar (Fin 2) (1 - s 1 + s u.val) i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem ex_K {N : ℕ} (δ : SL(2, ℤ)) (hδ0 : δ ∈ Gamma0 N) : ∃ u, IsZU u ∧
    (toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ K1G N ∧
    ∃ y ∈ Ohat ℚ, (u : Af ℚ) - (δ 1 1 : ℤ) = N * y := by
  obtain ⟨c, hc⟩ : (N : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 hδ0)
  have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have := δ.det_coe
    rwa [Matrix.det_fin_two] at this
  obtain ⟨u, hu, y, hy, hd⟩ := ex_unit (d := δ 1 1) (N := N) ⟨δ 0 0, -(δ 0 1 * c), by rw [hc] at hdet; linear_combination hdet⟩
  have hI : ∀ n : ℤ, (n : Af ℚ) ∈ Ohat ℚ := fun n => intCast_mem _ n
  have hδ : ∀ (δ : SL(2, ℤ)) a b, (toF (Matrix.SpecialLinearGroup.mapGL ℚ δ)).val a b = ((δ a b : ℤ) : Af ℚ) := by
    intro δ a b
    show algebraMap ℚ (Af ℚ) (algebraMap ℤ ℚ (δ a b)) = _
    simp
  have e1 : ∀ a b, ((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u).val a b
      = (((δ⁻¹ : SL(2, ℤ)) a b : ℤ) : Af ℚ) * u := by
    intro a b
    rw [← map_inv, ← map_inv, Units.val_mul, ← hδ]
    simp
  have e2 : ∀ a b, (((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹).val a b
      = (u⁻¹ : (Af ℚ)ˣ) * ((δ a b : ℤ) : Af ℚ) := by
    intro a b
    rw [_root_.mul_inv_rev, inv_inv, ← map_inv, Units.val_mul, ← hδ]
    generalize u⁻¹ = v
    simp
  have i10 : (δ⁻¹ : SL(2, ℤ)) 1 0 = -δ 1 0 := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
  have i11 : (δ⁻¹ : SL(2, ℤ)) 1 1 = δ 0 0 := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
  have hdet' : ((δ 0 0 : ℤ) : Af ℚ) * (δ 1 1 : ℤ) - (δ 0 1 : ℤ) * (N * c) = 1 := by
    rw [hc] at hdet
    exact_mod_cast congrArg (Int.cast : ℤ → Af ℚ) hdet
  refine ⟨u, hu, (memK N _).2 ⟨fun a b => ?_, fun a b => ?_, ⟨-(c * u), neg_mem (mul_mem (hI _) hu.1), ?_⟩,
    (δ 0 0 : ℤ) * y + (δ 0 1 : ℤ) * c, add_mem (mul_mem (hI _) hy) (mul_mem (hI _) (hI _)), ?_⟩, y, hy, hd⟩
  · rw [e1]; exact mul_mem (hI _) hu.1
  · rw [e2]; exact mul_mem hu.2 (hI _)
  · rw [e1, i10, hc]; push_cast; ring
  · rw [e1, i11]; linear_combination ((δ 0 0 : ℤ) : Af ℚ) * hd + hdet'

private theorem nsl_aff (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    nsl k f (aff (Units.mk0 z.im z.im_pos.ne') z.re).val UpperHalfPlane.I = ((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) * f z := by
  have e : (aff (Units.mk0 z.im z.im_pos.ne') z.re).val = !![z.im, z.re; 0, 1] := rfl
  have hd : (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = z.im := by simp
  have hz : (z.im : ℂ) * Complex.I + z.re = z := by
    rw [add_comm]; exact Complex.re_add_im z
  rw [e, nsl, hd, abs_of_pos z.im_pos, sign_pos z.im_pos]
  simp [hz]

theorem UpperTheory.V.Br.downChar :
    UpperTheory.V.Br.DownChar := by
  intro k N hN χ ω hω f φ hφ hc δ hδ
  obtain ⟨u, hu, hK, hd⟩ := ex_K δ hδ
  set β := Matrix.SpecialLinearGroup.mapGL ℚ δ with hβ
  have h2 := hω.unit u hu _ hd
  have s3 : GeneralLinearGroup.scalar (Fin 2) (finId ℚ u) = finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) u) :=
    (corner_sc _ u).symm
  have hβ' : (toR β).val = δ.1.map (Int.cast : ℤ → ℝ) := by
    ext i j
    change (Rat.castHom ℝ) (algebraMap ℤ ℚ (δ i j)) = _
    simp
  have key : ∀ x : GL (Fin 2) ℝ, nsl k f x.val UpperHalfPlane.I =
      ((ω.1 (finId ℚ u) : ℂˣ) : ℂ) * nsl k f (toR β * x).val UpperHalfPlane.I := by
    intro x
    have e : GeneralLinearGroup.scalar (Fin 2) (finId ℚ u) * (ratGL ℚ 2 1 * (upR (toR β * x) * finGL ℚ 2 1)) =
        ratGL ℚ 2 β * (upR x * finGL ℚ 2 ((toF β)⁻¹ * GeneralLinearGroup.scalar (Fin 2) u)) := by
      have c : ∀ (x : GL (Fin 2) ℝ) (y : GL (Fin 2) (Af ℚ)) (w : GA ℚ 2), finGL ℚ 2 y * (upR x * w) = upR x * (finGL ℚ 2 y * w) :=
        fun x y w => by rw [← mul_assoc, ← upR_comm, mul_assoc]
      rw [s3, ratGL_eq β, map_one, one_mul]
      simp only [mul_assoc, c]
      simp only [mul_assoc, map_mul, map_inv, mul_inv_cancel_left, map_one, mul_one]
    rw [← hφ β x _ hK, ← e, hc, hφ 1 _ 1 (one_mem _)]
  funext z
  have h := key (aff (Units.mk0 z.im z.im_pos.ne') z.re)
  have hdet : 0 < (aff (Units.mk0 z.im z.im_pos.ne') z.re).val.det := by
    have e : (aff (Units.mk0 z.im z.im_pos.ne') z.re).val = !![z.im, z.re; 0, 1] := rfl
    rw [e]
    simpa using z.im_pos
  rw [Units.val_mul, ← (nslMul k f).1 _ _ (toR β).det_ne_zero hdet, hβ', (nslSl k f).1, nsl_aff, nsl_aff] at h
  have hne : ((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos z.im_pos _).ne'
  refine mul_left_cancel₀ hne ?_
  rw [Pi.smul_apply, smul_eq_mul]
  linear_combination (-χ ((δ 1 1 : ℤ) : ZMod N)) * h - (((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (f ∣[(k : ℤ)] δ) z) * h2
end

