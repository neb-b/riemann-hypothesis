module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Formalism.LatticeTheta.Statement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevIteratedOneParameterSubgroupsWords
section
open MeasureTheory

namespace GlobalTheory

theorem sobolev_iterated_one_parameter_subgroups_words : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : ℕ) (c : Fin N → ℝ → G) (s : ℝ), 0 < s → (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : List (Fin N) → G → ℂ), (∀ l, Continuous (F l)) → (∀ l i x, HasDerivAt (fun t => F l (x * c i t)) (F (i :: l) x) 0) → ∀ (y : G) (M : ℝ), (∀ l : List (Fin N), l.length ≤ N → ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖F l (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ M) → ‖F [] y‖ ^ 2 ≤ C * M := by
  intro G _ _ _ N c s hs hc
  obtain ⟨enc, hinj, h1, h2⟩ : ∃ enc : List (Fin N) → ℝ, Function.Injective enc ∧
      (∀ l, 1 ≤ ‖enc l‖) ∧ ∀ l, ‖enc l‖ ≤ 2 := by
    have hpos : ∀ l : List (Fin N), (0 : ℝ) < 1 / ((Encodable.encode l : ℝ) + 1) := fun l => by
      positivity
    have hle : ∀ l : List (Fin N), 1 / ((Encodable.encode l : ℝ) + 1) ≤ 1 := fun l => by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (Encodable.encode l : ℝ) := Nat.cast_nonneg _
      linarith
    refine ⟨fun l => 1 + 1 / ((Encodable.encode l : ℝ) + 1), ?_, fun l => ?_, fun l => ?_⟩
    · intro a b hab
      have h : (1 : ℝ) / ((Encodable.encode a : ℝ) + 1) = 1 / ((Encodable.encode b : ℝ) + 1) :=
        add_left_cancel hab
      rw [one_div, one_div, inv_inj, add_left_inj, Nat.cast_inj] at h
      exact Encodable.encode_injective h
    · have := hpos l
      rw [Real.norm_of_nonneg (by linarith)]
      linarith
    · have := hpos l
      have := hle l
      rw [Real.norm_of_nonneg (by linarith)]
      linarith
  have hdec : ∀ l, Function.invFun enc (enc l) = l := Function.leftInverse_invFun hinj
  have hK : 0 ≤ (2 / s + 2 * s * 2 ^ 2) ^ N := by positivity
  refine ⟨(2 / s + 2 * s * 2 ^ 2) ^ N * 4, by positivity, ?_⟩
  intro F hF hD y M hM
  have hM0 : 0 ≤ M :=
    le_trans (integral_nonneg fun t => by positivity) (hM [] (Nat.zero_le _))
  have main := sobolev_iterated_one_parameter_subgroups G ℝ ℂ N 0 c
    (fun p => enc '' {l | l.length ≤ p}) (fun i u => enc (i :: Function.invFun enc u))
    (fun u => F (Function.invFun enc u)) s 2 M y hs (by norm_num) hM0 hc
    (fun p q hpq => Set.image_mono fun l hl => le_trans hl hpq) ?_ ?_ ?_ (enc [])
    ⟨[], Nat.le_refl 0, rfl⟩
  · rw [hdec] at main
    have h4 : ‖enc []‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h2 _) 2
    calc _ ≤ _ := main
      _ ≤ (2 / s + 2 * s * 2 ^ 2) ^ N * M * 2 ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg hK hM0)
      _ = _ := by ring
  · rintro p _ ⟨l, hl, rfl⟩
    simp only [hdec]
    exact ⟨hF l, fun i => ⟨⟨i :: l, Nat.succ_le_succ hl, rfl⟩, hD l i⟩⟩
  · rintro p _ _ ⟨l, hl, rfl⟩ i
    have := h1 l
    have := h2 (i :: Function.invFun enc (enc l))
    linarith
  · rintro _ ⟨l, hl, rfl⟩
    simp only [hdec]
    have hl' : l.length ≤ N := by simpa using hl
    exact (hM l hl').trans (le_mul_of_one_le_right hM0 (one_le_pow₀ (h1 l)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitInjectiveOfForallPrimeBaseChangeFieldInject
section
open TensorProduct

namespace GlobalTheory

theorem split_injective_of_forall_prime_baseChange_field_injective :
    ∀ (R : Type) [CommRing R] (M : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Projective R M] (N : Type 1) [AddCommGroup N] [Module R N] [Module.Finite R N]
      [Module.Projective R N] (f : M →ₗ[R] N),
      (∀ P : PrimeSpectrum R, ∃ (k : Type) (_ : Field k) (_ : Algebra R k),
        RingHom.ker (algebraMap R k) = P.asIdeal ∧ Function.Injective (f.baseChange k)) →
      ∃ g : N →ₗ[R] M, g ∘ₗ f = LinearMap.id := by
  intro R _ M _ _ _ _ N _ _ _ _ f h
  refine split_injective_of_forall_lTensor_residueField_injective f fun m hm => ?_
  obtain ⟨k, _, _, hk, hinj⟩ := h ⟨m, hm.isPrime⟩
  simp only at hk
  let φ : m.ResidueField →ₐ[R] k := Ideal.ResidueField.liftₐ m (Algebra.ofId R k) hk.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hk ▸ h0))
  letI : Algebra m.ResidueField k := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R m.ResidueField k :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have e : (AlgebraTensorModule.cancelBaseChange R m.ResidueField m.ResidueField k N) ∘
        ((f.baseChange m.ResidueField).lTensor k) =
      (f.lTensor k) ∘ (AlgebraTensorModule.cancelBaseChange R
        m.ResidueField m.ResidueField k M) := by
    funext x
    exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
      m.ResidueField m.ResidueField (M := k) f) x).symm
  have h1 : Function.Injective ((f.baseChange m.ResidueField).lTensor k) :=
    Function.Injective.of_comp (e ▸ (hinj.comp (LinearEquiv.injective _)))
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective m.ResidueField k _).1 h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableLipschitzLatticeNormPowSummand
section
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR.LhsSum

variable {F : Type} [Field F] [NumberField F]

theorem prod_realEmb_eq_norm [IsTotallyReal F] (x : F) :
    (∏ τ : F →+* ℝ, τ x) = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [show ((Algebra.norm ℚ x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ x) from rfl, h]
  have hb : Function.Bijective (fun τ : F →+* ℝ => Complex.ofRealHom.comp τ) := by
    refine ⟨fun τ τ' h => ?_, fun φ => ?_⟩
    · ext x
      exact Complex.ofReal_injective (RingHom.congr_fun h x)
    · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x =>
        (IsTotallyReal.complexEmbedding_isReal φ).coe_embedding_apply x⟩
  refine Fintype.prod_bijective (fun τ : F →+* ℝ => RingHom.equivRatAlgHom F ℂ (Complex.ofRealHom.comp τ))
    ((RingHom.equivRatAlgHom F ℂ).bijective.comp hb) _ _ (fun τ => ?_)
  rfl

theorem one_le_abs_prod_int [IsTotallyReal F] (y : 𝓞 F) (hy : y ≠ 0) :
    1 ≤ |∏ τ : F →+* ℝ, τ (y : F)| := by
  rw [prod_realEmb_eq_norm, ← Algebra.coe_norm_int]
  have h : Algebra.norm ℤ y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ y| := Int.one_le_abs h
  have h2 : (((Algebra.norm ℤ y : ℤ) : ℚ) : ℝ) = ((Algebra.norm ℤ y : ℤ) : ℝ) := by push_cast; rfl
  rw [h2]
  exact_mod_cast h1

theorem exists_lower_norm [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ a ∈ M, a ≠ 0 → ν ≤ |∏ τ : F →+* ℝ, τ a| := by
  obtain ⟨d, hd, hint⟩ := M.isFractional
  have hd0 : (d : F) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hd
    exact_mod_cast this
  have hP : 0 < |∏ τ : F →+* ℝ, τ (d : F)| :=
    abs_pos.2 (Finset.prod_ne_zero_iff.2 fun τ _ => (map_ne_zero τ).2 hd0)
  refine ⟨1 / |∏ τ : F →+* ℝ, τ (d : F)|, by positivity, fun a ha ha0 => ?_⟩
  obtain ⟨y, hy⟩ := hint a ha
  have hy' : (y : F) = (d : F) * a := by
    rw [← Algebra.smul_def]; exact hy
  have hy0 : y ≠ 0 := by
    intro h; apply mul_ne_zero hd0 ha0; rw [← hy', h]; simp
  have h1 := one_le_abs_prod_int y hy0
  rw [hy'] at h1
  simp only [map_mul, Finset.prod_mul_distrib, abs_mul] at h1
  rw [div_le_iff₀ hP]
  linarith [mul_comm (|∏ τ : F →+* ℝ, τ (d : F)|) (|∏ τ : F →+* ℝ, τ a|)]

theorem exists_lower_one_add (w : ℂ) (hw : w.im ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * (1 + |t|) ≤ ‖w + (t : ℂ)‖ := by
  have him : 0 < |w.im| := abs_pos.2 hw
  refine ⟨|w.im| / (|w.im| + 1 + ‖w‖), by positivity, fun t => ?_⟩
  have h1 : |w.im| ≤ ‖w + (t : ℂ)‖ := by
    have := Complex.abs_im_le_norm (w + (t : ℂ))
    simpa using this
  have h2 : |t| ≤ ‖w + (t : ℂ)‖ + ‖w‖ := by
    have := norm_sub_le (w + (t : ℂ)) w
    simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hn : 0 ≤ ‖w‖ := norm_nonneg _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem floor_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (x : ℝ) :
    s / 2 * (1 + |((⌊x / s⌋ : ℤ) : ℝ)|) ≤ 1 + |x| := by
  set n : ℤ := ⌊x / s⌋ with hn
  have h1 : (n : ℝ) ≤ x / s := Int.floor_le _
  have h2 : x / s < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have h1' : (n : ℝ) * s ≤ x := by rwa [le_div_iff₀ hs0] at h1
  have h2' : x < ((n : ℝ) + 1) * s := by rwa [div_lt_iff₀ hs0] at h2
  rcases le_or_gt 0 (n : ℝ) with hn0 | hn0
  · rw [abs_of_nonneg hn0, abs_of_nonneg (by nlinarith)]
    nlinarith
  · have hn1 : (n : ℝ) ≤ -1 := by
      have : n ≤ -1 := by
        have : n < 0 := by exact_mod_cast hn0
        omega
      exact_mod_cast this
    rw [abs_of_neg hn0]
    have : |x| ≥ -x := neg_le_abs x
    nlinarith

def wt (m : ℤ) : ℝ := ((1 + |(m : ℝ)|) ^ 2)⁻¹

theorem wt_nonneg (m : ℤ) : 0 ≤ wt m := by unfold wt; positivity

theorem summable_wt : Summable wt := by
  have hA : Summable (fun m : ℤ => |(m : ℝ)| ^ (-(2 : ℝ))) := Real.summable_abs_int_rpow (by norm_num)
  have hB : Summable (fun m : ℤ => if m = 0 then (1 : ℝ) else 0) := (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le wt_nonneg (fun m => ?_) (hA.add hB)
  by_cases hm : m = 0
  · subst hm
    simp [wt, Real.zero_rpow]
  · simp only [hm, if_false, add_zero]
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    rw [Real.rpow_neg (abs_nonneg _), wt]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    apply inv_anti₀ (by positivity)
    nlinarith [abs_nonneg (m : ℝ)]

theorem summable_prod_wt (ι : Type) [Fintype ι] [DecidableEq ι] :
    Summable (fun n : ι → ℤ => ∏ i, wt (n i)) := by
  refine summable_of_sum_le (c := ∏ _i : ι, ∑' m, wt m)
    (fun n => Finset.prod_nonneg fun i _ => wt_nonneg _) (fun u => ?_)
  calc ∑ n ∈ u, ∏ i, wt (n i)
      ≤ ∑ n ∈ Fintype.piFinset (fun i => u.image (fun n : ι → ℤ => n i)), ∏ i, wt (n i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Fintype.mem_piFinset]
          intro i
          exact Finset.mem_image_of_mem _ hn
        · intro n _ _
          exact Finset.prod_nonneg fun i _ => wt_nonneg _
    _ = ∏ i, ∑ m ∈ u.image (fun n : ι → ℤ => n i), wt m := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : ι, ∑' m, wt m := by
        apply Finset.prod_le_prod₀
        · intro i _; exact Finset.sum_nonneg fun m _ => wt_nonneg m
        · intro i _; exact summable_wt.sum_le_tsum _ (fun m _ => wt_nonneg m)

end GlobalTheory.LipschitzTR.LhsSum


open GlobalTheory.LipschitzTR.LhsSum in
theorem GlobalTheory.LipschitzTR.summable_lhsTerm_ideal :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 →
      ∀ (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) →
        Summable (fun a : (M : Set F) => lhsTerm k z a) := by
  intro F _ _ _ M _ k hk z hz
  classical
  obtain ⟨ν, hν0, hν⟩ := exists_lower_norm M
  have hcard : 0 < Fintype.card (F →+* ℝ) := by
    rw [card_realEmb]; exact Module.finrank_pos
  set s : ℝ := min 1 (ν / 2) with hs
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsν : s ^ Fintype.card (F →+* ℝ) < ν :=
    lt_of_le_of_lt (pow_le_of_le_one hs0.le hs1 hcard.ne') (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  let N : ↥(M : Set F) → ((F →+* ℝ) → ℤ) := fun a τ => ⌊τ (a : F) / s⌋
  have hN : Function.Injective N := by
    intro a b hab
    by_contra hne
    have hne' : (a : F) - b ≠ 0 := sub_ne_zero.2 (fun h => hne (Subtype.ext h))
    have hmem : (a : F) - b ∈ M := (M : Submodule (𝓞 F) F).sub_mem a.2 b.2
    have h1 := hν _ hmem hne'
    have h2 : |∏ τ : F →+* ℝ, τ ((a : F) - b)| ≤ s ^ Fintype.card (F →+* ℝ) := by
      rw [Finset.abs_prod, ← Finset.card_univ, ← Finset.prod_const]
      refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun τ _ => ?_)
      have hf := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun hab τ)
      rw [← sub_div, abs_div, abs_of_pos hs0, div_lt_one hs0] at hf
      rw [map_sub]; exact hf.le
    linarith
  have hc : ∀ τ : F →+* ℝ, ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * (1 + |t|) ≤ ‖z τ + (t : ℂ)‖ :=
    fun τ => exists_lower_one_add (z τ) (hz τ)
  choose c hc0 hc using hc
  set C : ℝ := ∏ τ : F →+* ℝ, ((c τ * (s / 2)) ^ k)⁻¹ with hC
  refine Summable.of_norm_bounded (g := fun a => C * ∏ τ, wt (N a τ))
    (((summable_prod_wt (F →+* ℝ)).comp_injective hN).mul_left C) (fun a => ?_)
  simp only [lhsTerm, zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib, norm_prod, norm_inv, norm_pow]
  rw [hC, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun τ _ => ?_)
  have hD : 0 < c τ * (s / 2) := by have := hc0 τ; positivity
  have hfl := floor_bound hs0 hs1 (τ (a : F))
  have he : c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|) ≤ ‖z τ + ((τ (a : F) : ℝ) : ℂ)‖ := by
    calc c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|) = c τ * (s / 2 * (1 + |((N a τ : ℤ) : ℝ)|)) := by ring
      _ ≤ c τ * (1 + |τ (a : F)|) := mul_le_mul_of_nonneg_left hfl (hc0 τ).le
      _ ≤ _ := hc τ _
  have hone : (1 : ℝ) ≤ 1 + |((N a τ : ℤ) : ℝ)| := by linarith [abs_nonneg ((N a τ : ℤ) : ℝ)]
  rw [wt, ← mul_inv]
  apply inv_anti₀ (by positivity)
  calc (c τ * (s / 2)) ^ k * (1 + |((N a τ : ℤ) : ℝ)|) ^ 2
      ≤ (c τ * (s / 2)) ^ k * (1 + |((N a τ : ℤ) : ℝ)|) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hone hk) (by positivity)
    _ = (c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|)) ^ k := by rw [mul_pow (c τ * (s / 2))]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) he k
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
section
noncomputable section

namespace GlobalTheory.SwapSlice

open GlobalTheory.WeilM

variable {k κ Y : Type}

def barL (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun Φ := fun y => starRingEnd ℂ (ι (fun x => starRingEnd ℂ (Φ x)) y)
  map_add' Φ Ψ := by
    funext y
    have e : (fun x => starRingEnd ℂ ((Φ + Ψ) x)) = (fun x => starRingEnd ℂ (Φ x)) + fun x => starRingEnd ℂ (Ψ x) := by
      funext x; simp
    show starRingEnd ℂ (ι (fun x => starRingEnd ℂ ((Φ + Ψ) x)) y) = _
    rw [e, map_add (f := _), Pi.add_apply, map_add (f := _)]
    rfl
  map_smul' c Φ := by
    funext y
    have e : (fun x => starRingEnd ℂ ((c • Φ) x)) = starRingEnd ℂ c • fun x => starRingEnd ℂ (Φ x) := by
      funext x; simp
    show starRingEnd ℂ (ι (fun x => starRingEnd ℂ ((c • Φ) x)) y) = _
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]
    rfl

theorem barL_apply (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (Φ : (κ → k) → ℂ) (y : Y) :
    barL ι Φ y = starRingEnd ℂ (ι (fun x => starRingEnd ℂ (Φ x)) y) := rfl

def sliceT (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] (Y × Y → ℂ) where
  toFun Φ := fun Z => barL ι (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) Z.2
  map_add' Φ Ψ := by
    funext Z
    have e : (fun x₂ => ι (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) Z.1) =
        (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) + fun x₂ => ι (fun x₁ => Ψ (Sum.elim x₁ x₂)) Z.1 := by
      funext x₂
      have e' : (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) = (fun x₁ => Φ (Sum.elim x₁ x₂)) + fun x₁ => Ψ (Sum.elim x₁ x₂) := rfl
      rw [e', map_add (f := _)]
      rfl
    show barL ι (fun x₂ => ι (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) Z.1) Z.2 = _
    rw [e, map_add (f := _)]
    rfl
  map_smul' c Φ := by
    funext Z
    have e : (fun x₂ => ι (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) Z.1) =
        c • fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1 := by
      funext x₂
      have e' : (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) = c • fun x₁ => Φ (Sum.elim x₁ x₂) := rfl
      rw [e', map_smul]
      rfl
    show barL ι (fun x₂ => ι (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) Z.1) Z.2 = _
    rw [e, map_smul]
    rfl

theorem sliceT_apply (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (Φ : (κ ⊕ κ → k) → ℂ) (Z : Y × Y) :
    sliceT ι Φ Z = barL ι (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) Z.2 := rfl

def swapNeg [Neg Y] (Z : Y × Y) : Y × Y := (-Z.2, -Z.1)

theorem swapNeg_apply [Neg Y] (Z : Y × Y) : swapNeg Z = (-Z.2, -Z.1) := rfl

theorem sliceT_boxFun [CommRing k] (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ₁ φ₂ : (κ → k) → ℂ) (Z : Y × Y) :
    sliceT ι (boxFun φ₁ φ₂) Z = ι φ₁ Z.1 * barL ι φ₂ Z.2 := by
  have e : (fun x₂ => ι (fun x₁ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) Z.1) = ι φ₁ Z.1 • φ₂ := by
    funext x₂
    have e' : (fun x₁ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₂ x₂ • φ₁ := by
      funext x₁; simp [boxFun, Function.comp_def, mul_comm]
    rw [e', map_smul]
    simp [mul_comm]
  rw [sliceT_apply, e, map_smul]
  simp

end GlobalTheory.SwapSlice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticZmodLift
section
namespace GlobalTheory

theorem symplectic_zmod_lift : ∀ (h k : ℕ) (M : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) (ZMod k)),
    M ∈ Matrix.symplecticGroup (Fin h) (ZMod k) → ∃ N : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) ℤ,
      N ∈ Matrix.symplecticGroup (Fin h) ℤ ∧ N.map (Int.cast : ℤ → ZMod k) = M := by
  intro h k M hM
  obtain ⟨N, hN⟩ := symplecticGroupMap_zmod_surjective (Fin h) k ⟨M, hM⟩
  refine ⟨N.1, N.2, ?_⟩
  have := congrArg Subtype.val hN
  rw [coe_symplecticGroupMap] at this
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorComp
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace TensorProduct

namespace GlobalTheory.AnPer

theorem Step.tensor_comp {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {D C : Type} [CommRing D] [Algebra ℂ D]
    [CommRing C] [Algebra ℂ C] {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)} (Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀)
    (hT : ∀ a h, Ta (dw (W := W) a h) = LinearMap.lTensor D (dw (W := W₀) a).toLinearMap (Ta h))
    (J : Ideal C) (J' : Ideal (D ⊗[ℂ] C))
    (hJ : ∀ c ∈ J, (1 : D) ⊗ₜ[ℂ] c ∈ J') (ρ₁ ρ₂ : Hol W₀ →ₐ[ℂ] C)
    (s : Step J (ρ₁ : Hol W₀ →+* C) (ρ₂ : Hol W₀ →+* C)) :
    Step J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
      ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂).comp Ta).toRingHom := by
  obtain ⟨n, h1, h2, h3⟩ := s
  refine ⟨fun a ↦ (1 : D) ⊗ₜ[ℂ] n a, fun a ↦ hJ _ (h1 a), fun a b ↦ by simp [h2], fun f ↦ ?_⟩
  have key : ∀ x : D ⊗[ℂ] Hol W₀, Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂ x =
      Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁ x +
        ∑ a, Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁ (LinearMap.lTensor D (dw (W := W₀) a).toLinearMap x) *
          (1 : D) ⊗ₜ[ℂ] n a := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul d h =>
      have := h3 h
      simp only [RingHom.coe_coe] at this
      simp [this, tmul_add, tmul_sum]
    | add x y hx hy =>
      simp only [map_add (f := _), hx, hy, add_mul, Finset.sum_add_distrib]
      abel
  simpa [hT] using key (Ta f)

theorem Close.tensor_comp {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {D C : Type} [CommRing D] [Algebra ℂ D]
    [CommRing C] [Algebra ℂ C] {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)} (Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀)
    (hT : ∀ a h, Ta (dw (W := W) a h) = LinearMap.lTensor D (dw (W := W₀) a).toLinearMap (Ta h))
    (J : Ideal C) (J' : Ideal (D ⊗[ℂ] C))
    (hJ : ∀ c ∈ J, (1 : D) ⊗ₜ[ℂ] c ∈ J') (ρ₁ ρ₂ : Hol W₀ →ₐ[ℂ] C)
    (h : Close J (ρ₁ : Hol W₀ →+* C) (ρ₂ : Hol W₀ →+* C)) :
    Close J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
      ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂).comp Ta).toRingHom := by
  have key : ∀ ρ : Hol W₀ →+* C, Close J (ρ₁ : Hol W₀ →+* C) ρ → ∃ σ : Hol W₀ →ₐ[ℂ] C, (σ : Hol W₀ →+* C) = ρ ∧
      Close J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
        ((Algebra.TensorProduct.map (AlgHom.id ℂ D) σ).comp Ta).toRingHom := by
    intro ρ hρ
    induction hρ with
    | refl => exact ⟨ρ₁, rfl, Relation.ReflTransGen.refl⟩
    | @tail b c _ s ih =>
      obtain ⟨σ, rfl, ih⟩ := ih
      have hc : ∀ z : ℂ, c (algebraMap ℂ (Hol W₀) z) = algebraMap ℂ C z := by
        intro z
        obtain ⟨n, -, -, h3⟩ := s
        rw [h3]
        simp [Derivation.map_algebraMap]
      exact ⟨{ c with commutes' := hc }, rfl,
        Relation.ReflTransGen.tail ih (Step.tensor_comp Ta hT J J' hJ σ { c with commutes' := hc } s)⟩
  obtain ⟨σ, hσ, h'⟩ := key _ h
  obtain rfl : σ = ρ₂ := AlgHom.toRingHom_injective hσ
  exact h'

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetFgOverFirstStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_fg_over_first : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A), ∃ F' : Finset (firstAndFinite R A k F), Algebra.adjoin R (Set.range (firstIncl R A k F) ∪ (F' : Set (firstAndFinite R A k F))) = ⊤ := by
  first | (exact @GlobalTheory.EtC.firstAndFinite_fg_over_first) | (exact GlobalTheory.EtC.firstAndFinite_fg_over_first) | (intros; apply GlobalTheory.EtC.firstAndFinite_fg_over_first  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetIsIntegralStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_isIntegral : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A), Algebra.IsIntegral R (firstAndFinite R A k F) := by
  first | (exact @GlobalTheory.EtC.firstAndFinite_isIntegral) | (exact GlobalTheory.EtC.firstAndFinite_isIntegral) | (intros; apply GlobalTheory.EtC.firstAndFinite_isIntegral  <;> assumption)
end

