module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.RankinSelbergLocalGeneratingSeriesIdentity
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private def UpperTheory.powerSeriesFirstDifferenceSeq (a : ℂ) (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => f 0
  | k + 1 => f (k + 1) - a * f k

private theorem UpperTheory.power_series_mul_linear (a : ℂ) (f : ℕ → ℂ) :
    PowerSeries.mk f * (1 - PowerSeries.C a * PowerSeries.X) =
      PowerSeries.mk (UpperTheory.powerSeriesFirstDifferenceSeq a f) := by
  have h : PowerSeries.mk f * (1 - PowerSeries.C a * PowerSeries.X) =
      PowerSeries.mk f - PowerSeries.C a * (PowerSeries.mk f * PowerSeries.X) := by ring
  rw [h]
  ext k
  cases k with
  | zero => simp [UpperTheory.powerSeriesFirstDifferenceSeq]
  | succ k =>
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X]
    simp [UpperTheory.powerSeriesFirstDifferenceSeq]

private theorem UpperTheory.geometric_sum_recurrence (x y : ℂ) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1 + 1), x ^ i * y ^ (k + 1 - i)) =
      x ^ (k + 1) + y * ∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.succ_sub hi', pow_succ]
  ring

private theorem UpperTheory.product_four_geometric_series (x y x' y' c : ℂ) (S T : ℕ → ℂ)
    (hS0 : S 0 = 1) (hT0 : T 0 = 1)
    (hS : ∀ k, S (k + 1) = x ^ (k + 1) + y * S k)
    (hT : ∀ k, T (k + 1) = x' ^ (k + 1) + y' * T k) :
    (PowerSeries.mk fun k : ℕ => c ^ k * S k * T k) *
          ((1 - PowerSeries.C (x * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (x * y' * c) * PowerSeries.X) *
            (1 - PowerSeries.C (y * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (y * y' * c) * PowerSeries.X)) =
          1 - PowerSeries.C (x * y * x' * y' * c ^ 2) * PowerSeries.X ^ 2 := by
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear,
    UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear]
  have hS2 : ∀ k, S (k + 1 + 1) = (x + y) * S (k + 1) - x * y * S k := fun k => by
    rw [hS (k + 1), hS k]; ring
  have hT2 : ∀ k, T (k + 1 + 1) = (x' + y') * T (k + 1) - x' * y' * T k := fun k => by
    rw [hT (k + 1), hT k]; ring
  ext k
  rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_one,
    PowerSeries.coeff_mk]
  rcases k with _ | _ | _ | _ | k
  · simp [UpperTheory.powerSeriesFirstDifferenceSeq, hS0, hT0]
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · rw [if_neg (by omega), if_neg (by omega)]
    simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS2, hT2]
    ring

theorem UpperTheory.rankinSelberg_local_generating_series_identity :
    ∀ x y x' y' c : ℂ, (PowerSeries.mk fun k : ℕ => c ^ k * (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i)) * (∑ i ∈ Finset.range (k + 1), (x') ^ i * (y') ^ (k - i))) *
          ((1 - PowerSeries.C (x * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (x * y' * c) * PowerSeries.X) *
            (1 - PowerSeries.C (y * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (y * y' * c) * PowerSeries.X)) =
          1 - PowerSeries.C (x * y * x' * y' * c ^ 2) * PowerSeries.X ^ 2 := by
  intro x y x' y' c
  exact UpperTheory.product_four_geometric_series x y x' y' c
    (fun k => ∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i))
    (fun k => ∑ i ∈ Finset.range (k + 1), x' ^ i * y' ^ (k - i))
    (by simp) (by simp) (UpperTheory.geometric_sum_recurrence x y) (UpperTheory.geometric_sum_recurrence x' y')
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.RealIdeleMulAbsContinuousAndUnitAbsEqOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private noncomputable def cu (y : ℝ) (h : y ≠ 0) : (TR.Rinf ℚ)ˣ :=
  ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ h, funext fun _ => inv_mul_cancel₀ h⟩

private theorem iy_eq {y : ℝ} (h : y ≠ 0) : iy y = TR.infId ℚ (cu y h) := dif_neg h

private theorem nrm_unit {v : H.P ℚ} {x : H.Kv v} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

theorem UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one :
    (∀ y y' : ℝ, y ≠ 0 → y' ≠ 0 → iy (y * y') = iy y * iy y') ∧ (∀ y : ℝ, y ≠ 0 → ab (iy y) = |y|) ∧ Continuous (fun t : ℝ => iy (Real.exp t)) ∧ ∀ u ∈ UU, ab u = 1 := by
  refine ⟨fun y y' hy hy' => ?_, fun y hy => ?_, ?_, fun u hu => ?_⟩
  · rw [iy_eq (mul_ne_zero hy hy'), iy_eq hy, iy_eq hy', ← map_mul]
    congr 1
    exact Units.ext rfl
  · rw [iy_eq hy]
    show (IdeleGroup.ideleModule ℚ (TR.infId ℚ (cu y hy)) : ℝ) = |y|
    rw [GlobalTheory.HenQ.DetSplit.ideleModule_infId]
    simp [cu]
  · have hu : Continuous fun t : ℝ => cu (Real.exp t) (Real.exp_ne_zero t) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact continuous_pi fun _ => Real.continuous_exp
      · exact continuous_pi fun _ => Real.continuous_exp.inv₀ Real.exp_ne_zero
    have he : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (cu (Real.exp t) (Real.exp_ne_zero t)) :=
      funext fun t => iy_eq (Real.exp_ne_zero t)
    rw [he]
    exact (TR.continuous_infId ℚ).comp hu
  · show (IdeleGroup.ideleModule ℚ u : ℝ) = 1
    rw [IdeleGroup.ideleModule_eq]
    have h1 : ((u : A ℚ)).1 = 1 := hu.1
    have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖((u : A ℚ)).2 v‖ = 1 :=
      finprod_eq_one_of_forall_eq_one fun v => nrm_unit (hu.2 v)
    rw [h1, h2, mul_one]
    exact Finset.prod_eq_one fun w _ => by
      rw [show (1 : InfiniteAdeleRing ℚ) w = 1 from rfl, norm_one, one_pow]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.RightInvariantBaseChangeUnipotentOfPlacesAboveFi
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma nL_memK {K : Type} [Field K] [NumberField K] {v : H.P K} {c : H.Kv v} (hc : Valued.v c ≤ 1) :
    H.nL c ∈ GlobalTheory.LFun.KGL v (n := 2) := by
  have hc' : c ∈ v.adicCompletionIntegers K := hc
  have hn : -c ∈ v.adicCompletionIntegers K := neg_mem hc'
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  have h1 : (1 : H.Kv v) ∈ v.adicCompletionIntegers K := one_mem _
  have h0 : (0 : H.Kv v) ∈ v.adicCompletionIntegers K := zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hc'
    · exact h0
    · exact h1
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hn
    · exact h0
    · exact h1

private lemma fix_sum {K : Type} [Field K] [NumberField K] (φ : GL (Fin 2) (A K) → ℂ) (S : Finset (H.P K)) :
    (∀ w ∈ S, H.Fix w φ) → ∀ z : A K, z.1 = 0 → (∀ w, w ∉ S → H.cp w z = 0) → (∀ w, Valued.v (H.cp w z) ≤ 1) →
      ∀ g, φ (g * gl (nU z)) = φ g := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ z h1 h2 _ g
    have hz : z = 0 := Prod.ext h1 (FiniteAdeleRing.ext K fun w => h2 w (Finset.notMem_empty w))
    have h : nU (0 : A K) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [nU]
    rw [hz, h, gl, map_one, mul_one]
  | insert w S hw ih =>
    intro hF z h1 h2 h3 g
    obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := H.sgLaws K w
    have hne : ∀ u, u ≠ w → H.cp u (H.sg w (H.cp w z)) = 0 := fun u hu => (hs _).2 u hu
    have e : z = (z - H.sg w (H.cp w z)) + H.sg w (H.cp w z) := (sub_add_cancel _ _).symm
    rw [e, nU_add, gl, map_mul, ← mul_assoc]
    have e2 : Matrix.SpecialLinearGroup.toGL (nU (H.sg w (H.cp w z))) = H.lc w (H.nL (H.cp w z)) :=
      ((H.lcLaws K w).1 _).symm
    rw [e2, hF w (Finset.mem_insert_self _ _) _ _ (nL_memK (h3 w))]
    refine ih (fun u hu => hF u (Finset.mem_insert_of_mem hu)) _ ?_ (fun u hu => ?_) (fun u => ?_) g
    · show z.1 - (H.sg w (H.cp w z)).1 = 0
      rw [h1, (hs _).1, sub_zero]
    · rw [map_sub]
      by_cases h : u = w
      · subst h
        rw [hc, sub_self]
      · rw [hne u h, sub_zero]
        exact h2 u (by simp [h, hu])
    · rw [map_sub]
      by_cases h : u = w
      · subst h
        rw [hc, sub_self, map_zero]
        exact zero_le'
      · rw [hne u h, sub_zero]
        exact h3 u

private lemma fin_over {E : Type} [Field E] [NumberField E] (v : H.P ℚ) :
    {w : H.P E | AdeleBaseChange.below ℚ w = v}.Finite := by
  have := v.isMaximal
  refine Set.Finite.of_finite_image (f := fun w : H.P E => w.asIdeal) ?_ fun a _ b _ h => HeightOneSpectrum.ext h
  refine (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, (AdeleBaseChange.below_eq_iff _ _).1 hw⟩

theorem UpperTheory.right_invariant_baseChangeUnipotent_of_places_above_fixed :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (v : H.P ℚ), H.Gd D.δ v → (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.Fix w φ) → ∀ c : H.Kv v, H.IsInt c → ∀ g, φ (g * Xg.nu D (H.sg v c)) = φ g := by
  intro E _ _ D φ v hG hF c hc g
  obtain ⟨-, -, hcp, -, -, -, -, hs, -, -⟩ := H.sgLaws ℚ v
  have hz : D.mkE 0 (H.sg v c) = AdeleBaseChange.adeleMap ℚ E (H.sg v c) * rt D.θ := by
    rw [Dat.mkE, map_zero, zero_add]
  have hoff : ∀ w : H.P E, AdeleBaseChange.below ℚ w ≠ v → H.cp w (D.mkE 0 (H.sg v c)) = 0 := fun w hw => by
    have h : H.cp w (AdeleBaseChange.adeleMap ℚ E (H.sg v c)) = 0 := by
      change SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w ((H.sg v c).2 (AdeleBaseChange.below ℚ w)) = 0
      rw [(hs c).2 _ hw, map_zero]
    rw [hz, map_mul, h, zero_mul]
  change φ (g * gl (nU (D.mkE 0 (H.sg v c)))) = φ g
  refine fix_sum φ (fin_over (E := E) v).toFinset (fun w hw => hF w ((fin_over v).mem_toFinset.1 hw)) _ ?_
    (fun w hw => hoff w fun h => hw ((fin_over v).mem_toFinset.2 h)) (fun w => ?_) g
  · rw [hz]
    change InfinitePlace.infiniteAdeleRingMap (H.sg v c).1 * _ = 0
    rw [(hs c).1, map_zero, zero_mul]
  · by_cases hw : AdeleBaseChange.below ℚ w = v
    · subst hw
      have hk : ∀ x : H.Kv (AdeleBaseChange.below ℚ w), Valued.v x ≤ 1 →
          Valued.v (SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w x) ≤ 1 := fun x hx => by
        rw [SemiLocal.valued_completionMap]
        exact pow_le_one' hx _
      have h1 : H.cp w (AdeleBaseChange.adeleMap ℚ E (H.sg _ c)) = SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w c :=
        congrArg (SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w) (hcp c)
      have h2 : H.cp w (rt D.θ) ^ 2 =
          SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w (D.δ : H.Kv (AdeleBaseChange.below ℚ w)) := by
        rw [← map_pow, ← map_pow, D.sq]
        have a := eq_ratCast (((H.cp w).comp (algebraMap E (A E))).comp (algebraMap ℚ E)) D.δ
        rw [map_ratCast]
        exact a
      have h3 : Valued.v (H.cp w (rt D.θ)) ≤ 1 := by
        have hd := hG.del
        rw [eq_ratCast] at hd
        have h := hk _ hd.le
        rw [← h2, map_pow] at h
        exact (pow_le_one_iff two_ne_zero).1 h
      rw [hz, map_mul, h1, map_mul]
      exact mul_le_one' (hk c hc) h3
    · rw [hoff w hw, map_zero]
      exact zero_le'
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.SumRangeRatAdeleCharIotaMulOneSubEqIte
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem psi_add (x y : A ℚ) : ψ (x + y) = ψ x * ψ y := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem psi_eq_one_iff (x : A ℚ) : ψ x = 1 ↔ adelicChar ℚ x = 1 := Circle.coe_eq_one

private theorem psi_neg_of_one {x : A ℚ} (h : ψ x = 1) : ψ (-x) = 1 := by
  rw [psi_eq_one_iff] at *
  rw [AddChar.map_neg_eq_inv, h, inv_one]

private theorem psi_zsmul (m : ℤ) {x : A ℚ} (h : ψ x = 1) : ψ (m • x) = 1 := by
  rw [psi_eq_one_iff] at *
  rw [AddChar.map_zsmul_eq_zpow, h, _root_.one_zpow]

private theorem psi_nsmul (a : ℕ) (x : A ℚ) : ψ (a • x) = ψ x ^ a := by
  simp only [ψ, AddChar.map_nsmul_eq_pow, Circle.coe_pow]

private theorem psi_Oh {c : A ℚ} (hc : c ∈ Oh ℚ) : ψ c = 1 := by
  have h : c ∈ invDifferentAdeles ℚ :=
    mem_invDifferentAdeles.2 (mem_finiteInvDifferent.2 fun v =>
      mem_localInvDifferent_of_mem (hc.2 v))
  rw [psi_eq_one_iff, adelicChar_of_mem_invDifferentAdeles h, hc.1]
  simp

private theorem different_rat : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal (K := ℚ), NumberField.discr_rat]
  rfl

private theorem mem_inv_iff (v : H.P ℚ) (x : H.Kv v) : x ∈ localInvDifferent v ↔ Valued.v x ≤ 1 := by
  rw [mem_localInvDifferent_iff_valued, different_rat]
  simp [FractionalIdeal.count_one]

private theorem psi_sg_eq (v : H.P ℚ) (x : H.Kv v) : ψ (H.sg v x) = (localAdelicChar ℚ v x : ℂ) := rfl

private noncomputable def eA : A ℚ := (0, 1)

private theorem fin_alg_val {K : Type} [Field K] [NumberField K] (v : H.P K) (a : K) :
    Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) a) v) = v.valuation K a :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a

private theorem nat_val (v : H.P ℚ) (n : ℕ) : Valued.v ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 := by
  have e : (n : FiniteAdeleRing (𝓞 ℚ) ℚ) v = (n : H.Kv v) := map_natCast (pLoc ℚ v) n
  rw [e]
  exact natCast_mem (v.adicCompletionIntegers ℚ) n

private theorem decomp (n : ℕ) (hn : 0 < n) {c : A ℚ} (hc : c ∈ Oh ℚ) :
    ∃ (m : ℤ) (c' : A ℚ), c' ∈ Oh ℚ ∧ c = m • eA + (n : A ℚ) * c' := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨k, hk⟩ := exists_sub_mem_finiteInvDifferent (K := ℚ)
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ * c.2)
  obtain ⟨f, hf⟩ : ∃ f, f = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ * c.2 -
      algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k := ⟨_, rfl⟩
  rw [← hf] at hk
  have hfv : ∀ v : H.P ℚ, Valued.v (f v) ≤ 1 := fun v =>
    (mem_inv_iff v _).1 (mem_finiteInvDifferent.1 hk v)
  have hnn : (n : FiniteAdeleRing (𝓞 ℚ) ℚ) * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) n, ← map_mul, mul_inv_cancel₀ hn0, map_one]
  have key : c.2 = (n : FiniteAdeleRing (𝓞 ℚ) ℚ) * f + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℚ) * k) := by
    rw [hf, map_mul, map_natCast, mul_sub, ← mul_assoc, hnn, one_mul, sub_add_cancel]
  have hint : ∀ v : H.P ℚ, v.valuation ℚ ((n : ℚ) * k) ≤ 1 := by
    intro v
    have e : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℚ) * k)) v = c.2 v - (n : FiniteAdeleRing (𝓞 ℚ) ℚ) v * f v := by
      have h2 : c.2 v = (n : FiniteAdeleRing (𝓞 ℚ) ℚ) v * f v + (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℚ) * k)) v :=
        congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) key
      rw [h2]
      ring
    rw [← fin_alg_val, e]
    refine (Valuation.map_sub _ _ _).trans (max_le (hc.2 v) ?_)
    rw [map_mul]
    exact mul_le_one' (nat_val v n) (hfv v)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ _ hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 (r.2 : IsIntegral ℤ (r : ℚ))
  have hmk : (n : ℚ) * k = (m : ℚ) := by
    exact hr.symm.trans (hm.symm.trans (eq_intCast (algebraMap ℤ ℚ) m))
  refine ⟨m, ((0, f) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ), ⟨rfl, hfv⟩, ?_⟩
  refine Prod.ext ?_ ?_
  · change c.1 = m • (0 : InfiniteAdeleRing ℚ) + (n : A ℚ).1 * 0
    rw [hc.1]
    simp
  · change c.2 = m • (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) + (n : FiniteAdeleRing (𝓞 ℚ) ℚ) * f
    rw [key, hmk, map_intCast, zsmul_one, add_comm]

private theorem local_good (v : H.P ℚ) (x : H.Kv v)
    (h : ∀ c : H.Kv v, Valued.v c ≤ 1 → ψ (H.sg v (c * x)) = 1) : Valued.v x ≤ 1 := by
  refine (mem_inv_iff v x).1 ((forall_localAdelicChar_mul_eq_one_iff v x).1 fun a ha => ?_)
  have := h a ha
  rw [psi_sg_eq] at this
  exact Circle.coe_eq_one.1 this

private theorem sg_oh (v : H.P ℚ) (c : H.Kv v) (hc : Valued.v c ≤ 1) : H.sg v c ∈ Oh ℚ := by
  obtain ⟨-, -, hcp, -, -, -, -, hs, -, -⟩ := H.sgLaws ℚ v
  refine ⟨(hs c).1, fun w => ?_⟩
  by_cases h : w = v
  · subst h
    have : (H.sg w c).2 w = c := hcp c
    rw [this]
    exact hc
  · rw [(hs c).2 w h, map_zero]
    exact zero_le'

private theorem oh_nat_mul (n : ℕ) {c : A ℚ} (hc : c ∈ Oh ℚ) : (n : A ℚ) * c ∈ Oh ℚ := by
  refine ⟨?_, fun v => ?_⟩
  · change (n : A ℚ).1 * c.1 = 0
    rw [hc.1, mul_zero]
  · change Valued.v ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) v * c.2 v) ≤ 1
    rw [map_mul]
    exact mul_le_one' (nat_val v n) (hc.2 v)

private theorem eA_mem : eA ∈ Oh ℚ := by
  refine ⟨rfl, fun v => ?_⟩
  change Valued.v (1 : H.Kv v) ≤ 1
  rw [map_one]

private theorem eA_mul {c : A ℚ} (hc : c.1 = 0) : eA * c = c := by
  refine Prod.ext ?_ ?_
  · change 0 * c.1 = c.1
    rw [hc, mul_zero]
  · change 1 * c.2 = c.2
    rw [one_mul]

private theorem L_iota (L : ℕ) (hL : 0 < L) : (L : A ℚ) * iota L = eA := by
  have hL0 : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  refine Prod.ext ?_ ?_
  · change (L : A ℚ).1 * 0 = 0
    rw [mul_zero]
  · change (L : FiniteAdeleRing (𝓞 ℚ) ℚ) * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ)⁻¹ = 1
    rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) L, ← map_mul, mul_inv_cancel₀ hL0, map_one]

private theorem psi_mul_of_one (L M : ℕ) (hL : 0 < L) (hM : 0 < M) (y : A ℚ)
    (hy : ∀ c ∈ Oh ℚ, ψ (y * ((M : A ℚ) * c)) = 1) (hz : ψ (iota L * (1 - y)) = 1)
    {c : A ℚ} (hc : c ∈ Oh ℚ) : ψ (c * (iota L * (1 - y))) = 1 := by
  obtain ⟨m, c', hc', e⟩ := decomp (L * M) (Nat.mul_pos hL hM) hc
  have hw : (iota L * (1 - y)).1 = 0 := by
    change (0 : InfiniteAdeleRing ℚ) * (1 - y).1 = 0
    rw [zero_mul]
  have e2 : c * (iota L * (1 - y)) =
      m • (iota L * (1 - y)) + ((M : A ℚ) * c' + -(y * ((M : A ℚ) * c'))) := by
    have h1 : ((L * M : ℕ) : A ℚ) * c' * (iota L * (1 - y)) = (M : A ℚ) * c' - y * ((M : A ℚ) * c') := by
      have h2 : ((L * M : ℕ) : A ℚ) * c' * (iota L * (1 - y)) = (M : A ℚ) * (eA * c') * (1 - y) := by
        rw [← L_iota L hL]
        push_cast
        ring
      rw [h2, eA_mul hc'.1]
      ring
    rw [e, add_mul, h1, zsmul_eq_mul, mul_assoc, ← zsmul_eq_mul, eA_mul hw, sub_eq_add_neg ((M : A ℚ) * c')]
  rw [e2, psi_add, psi_add, psi_zsmul m hz, psi_Oh (oh_nat_mul M hc'), psi_neg_of_one (hy c' hc')]
  simp

private theorem val_iff (L : ℕ) (hL : 0 < L) (y : A ℚ) (v : H.P ℚ) :
    Dv L v (y - 1) ↔ Valued.v (H.cp v (iota L * (1 - y))) ≤ 1 := by
  have hab : Valued.v (L : H.Kv v) * Valued.v (H.cp v (iota L)) = 1 := by
    have e : (L : H.Kv v) * H.cp v (iota L) = 1 := by
      have h1 : H.cp v ((L : A ℚ) * iota L) = 1 := by
        rw [L_iota L hL]
        rfl
      rwa [map_mul, map_natCast] at h1
    rw [← map_mul, e, map_one]
  have hx : Valued.v (H.cp v (iota L * (1 - y))) =
      Valued.v (H.cp v (iota L)) * Valued.v (H.cp v (y - 1)) := by
    rw [map_mul, map_mul, ← neg_sub y 1, map_neg, Valuation.map_neg]
  rw [hx]
  unfold Dv
  constructor
  · intro h
    calc _ ≤ Valued.v (H.cp v (iota L)) * Valued.v (L : H.Kv v) := mul_le_mul' le_rfl h
      _ = 1 := by rw [mul_comm, hab]
  · intro h
    calc Valued.v (H.cp v (y - 1)) =
        Valued.v (L : H.Kv v) * (Valued.v (H.cp v (iota L)) * Valued.v (H.cp v (y - 1))) := by
          rw [← mul_assoc, hab, one_mul]
      _ ≤ Valued.v (L : H.Kv v) * 1 := mul_le_mul' le_rfl h
      _ = _ := mul_one _

theorem UpperTheory.sum_range_ratAdeleChar_iota_mul_one_sub_eq_ite :
    ∀ (L M : ℕ), 0 < L → 0 < M → ∀ y : A ℚ, (∀ c ∈ Oh ℚ, ψ (y * ((M : A ℚ) * c)) = 1) → ∑ a ∈ Finset.range (L * M), ψ ((a : A ℚ) * iota L * (1 - y)) = if ∀ v : H.P ℚ, Dv L v (y - 1) then ((L * M : ℕ) : ℂ) else 0 := by
  intro L M hL hM y hy
  have hsum : ∀ a : ℕ, ψ ((a : A ℚ) * iota L * (1 - y)) = ψ (iota L * (1 - y)) ^ a := by
    intro a
    rw [mul_assoc, ← nsmul_eq_mul, psi_nsmul]
  simp only [hsum]
  have hzn : ψ (iota L * (1 - y)) ^ (L * M) = 1 := by
    rw [← psi_nsmul, nsmul_eq_mul]
    have e : ((L * M : ℕ) : A ℚ) * (iota L * (1 - y)) =
        (M : A ℚ) * eA + -(y * ((M : A ℚ) * eA)) := by
      have h1 : ((L * M : ℕ) : A ℚ) * (iota L * (1 - y)) =
          (M : A ℚ) * ((L : A ℚ) * iota L) * (1 - y) := by
        push_cast
        ring
      rw [h1, L_iota L hL]
      ring
    rw [e, psi_add, psi_Oh (oh_nat_mul M eA_mem), psi_neg_of_one (hy eA eA_mem), one_mul]
  have hw1 : (iota L * (1 - y)).1 = 0 := by
    change (0 : InfiniteAdeleRing ℚ) * (1 - y).1 = 0
    rw [zero_mul]
  split_ifs with h
  · have hz : ψ (iota L * (1 - y)) = 1 :=
      psi_Oh ⟨hw1, fun v => (val_iff L hL y v).1 (h v)⟩
    simp [hz]
  · have hz : ψ (iota L * (1 - y)) ≠ 1 := by
      intro hz
      refine h fun v => (val_iff L hL y v).2 (local_good v _ fun c hc => ?_)
      obtain ⟨-, hm, -⟩ := H.sgLaws ℚ v
      rw [mul_comm c, ← hm, mul_comm]
      exact psi_mul_of_one L M hL hM y hy hz (sg_oh v c hc)
    rw [geom_sum_eq hz, hzn]
    simp
end

