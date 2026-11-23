module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntegralTestFunctionMulTraceCharacterQuadFormOfD
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem et_pow_den_eq_one {F : Type} [Field F] [NumberField F] (y : F) :
    et y ^ (Algebra.trace ℚ F y).den = 1 := by
  unfold et
  set q : ℚ := Algebra.trace ℚ F y
  rw [← Complex.exp_nat_mul]
  have h : ((q.den : ℕ) : ℂ) * (q : ℂ) = (q.num : ℂ) := by
    have := Rat.den_mul_eq_num q
    exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) this
  have : ((q.den : ℕ) : ℂ) * (2 * Real.pi * Complex.I * (q : ℂ)) = (q.num : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [← h]; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem padic_norm_et_eq_one {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (y : F) :
    ‖ι.symm (et y)‖ = 1 := by
  have h := congrArg (fun z => ‖ι.symm z‖) (et_pow_den_eq_one y)
  simp only [map_pow, norm_pow, map_one, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Rat.den_nz _)).1 h

theorem QF_mulVec_of_iso {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {G S : Matrix κ κ ℤ} (h : Sᵀ * G * S = G) (x : κ → F) :
    QF G (S.map (Int.cast : ℤ → F) *ᵥ x) = QF G x := by
  have h' : (S.map (Int.cast : ℤ → F))ᵀ * G.map (Int.cast : ℤ → F) * S.map (Int.cast : ℤ → F)
      = G.map (Int.cast : ℤ → F) := by
    have := congrArg (fun A : Matrix κ κ ℤ => A.map (Int.castRingHom F)) h
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  unfold QF BF
  congr 1
  conv_rhs => rw [← h']
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x,
    Matrix.vecMul_transpose]

theorem good_mul_et_QF : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (δ : F), IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → ∀ b : F, PInt p (δ * b) → Good ι S fun x => Φ x * et (b * QF G x) := by
  intro F _ _ p hp ι δ hδ κ _ _ G S t hL Φ hΦ b hb
  obtain ⟨⟨N, hN, hNp, hsupp, hper⟩, hS, hint, h0⟩ := hΦ
  obtain ⟨M, hM, hMp, htr⟩ := (GlobalTheory.HilbertThetaSeries.denominators_prime_to F p hp.out δ hδ).2.2.1 b hb
  obtain ⟨hadd, hsmul, -, hI, hLL, haL, het, -⟩ := GlobalTheory.HilbertThetaSeries.formLatticeProps F κ G hL.pos
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  have hnat : ∀ (n : ℕ) (l : κ → F), l ∈ LL F κ → (n : F) • l ∈ LL F κ := by
    intro n l hl
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ hl n
  refine ⟨⟨N * N * M, by positivity, Nat.Coprime.mul_left (Nat.Coprime.mul_left hNp hNp) hMp, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨l, hl, rfl⟩ := (haL _ _).1 (hsupp x (left_ne_zero_of_mul hx))
    refine (haL _ _).2 ⟨_, hnat (N * M) l hl, ?_⟩
    rw [smul_smul]
    congr 1
    push_cast
    field_simp
  · intro x l' hl'
    obtain ⟨l, hl, rfl⟩ := (haL _ _).1 hl'
    have h1 : Φ (x + ((N * N * M : ℕ) : F) • l) = Φ x := by
      refine hper x _ ((haL _ _).2 ⟨_, hnat (N * M) l hl, ?_⟩)
      rw [smul_smul]
      congr 1
      push_cast
      ring
    show Φ _ * _ = Φ x * _
    rw [h1]
    by_cases hx : Φ x = 0
    · simp [hx]
    obtain ⟨y, hy, rfl⟩ := (haL _ _).1 (hsupp x hx)
    congr 1
    have hz : IsIntegral ℤ ((N : F) * BF G y l + ((N * N * N * N * M : ℕ) : F) * QF G l) :=
      ((isIntegral_natCast N).mul ((hI y hy).2 l hl)).add ((isIntegral_natCast _).mul (hI l hl).1)
    have h2 : b * QF G ((N : F)⁻¹ • y + ((N * N * M : ℕ) : F) • l) = b * QF G ((N : F)⁻¹ • y) +
        (M : F) * b * ((N : F) * BF G y l + ((N * N * N * N * M : ℕ) : F) * QF G l) := by
      rw [(hadd _ _).2, (hsmul _ y _).1, (hadd y _).1, (hsmul _ l y).1, (hsmul _ l y).2.1, (hadd l y).1]
      push_cast
      field_simp
      ring
    rw [h2, (het _ _).1, (het _ 0).2.2.1.2 (htr _ hz), mul_one]
  · intro x
    show Φ _ * _ = Φ x * _
    rw [hS, QF_mulVec_of_iso hL.iso]
  · intro x
    show ‖ι.symm (Φ x * _)‖ ≤ 1
    rw [map_mul, norm_mul, padic_norm_et_eq_one, mul_one]
    exact hint x
  · show ‖ι.symm (Φ 0 * _) - 1‖ ≤ _
    have : et (b * QF G (0 : κ → F)) = 1 := by simp [et, QF, BF]
    rw [this, mul_one]
    exact h0

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_test_function_mul_trace_character_quad_form_of_delta_integral : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (δ : F), IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → ∀ b : F, PInt p (δ * b) → Good ι S fun x => Φ x * et (b * QF G x) := by
  first | exact @GlobalTheory.HilbertThetaSeries.good_mul_et_QF | exact GlobalTheory.HilbertThetaSeries.good_mul_et_QF | (intros; apply GlobalTheory.HilbertThetaSeries.good_mul_et_QF <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.QExpansionMulFiniteConvolution
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem reAt_add_qm {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) (x y : F) :
    reAt v (x + y) = reAt v x + reAt v y := by
  simp [reAt, map_add (f := _)]

theorem ez_add_qm {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (x y : F) (z : Hn F) :
    ez (x + y) z = ez x z * ez y z := by
  simp only [ez, ← Complex.exp_add, reAt_add_qm, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add]

theorem TP_add {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {x y : F} (hx : TP x) (hy : TP y) :
    TP (x + y) := fun v => by rw [reAt_add_qm]; exact add_pos (hx v) (hy v)

theorem hasQ_mul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ),
    HasQ f a → HasQ g b → ∃ c, HasQ (f * g) c ∧ ∀ ξ, ∃ s : Finset F, c ξ = ∑ η ∈ s, a η * b (ξ - η) := by
  intro F _ _ _ f g a b ⟨⟨D, hD, ha⟩, hf⟩ ⟨⟨E, hE, hb⟩, hg⟩
  have hfin : ∀ ξ, (Function.support fun η => a η * b (ξ - η)).Finite := by
    intro ξ
    refine (GlobalTheory.T.totallyPositive_summands_with_denominator_finite F D hD ξ).subset ?_
    intro η hη
    have h1 : a η ≠ 0 := left_ne_zero_of_mul hη
    have h2 : b (ξ - η) ≠ 0 := right_ne_zero_of_mul hη
    exact ⟨(ha η h1).1, (hb _ h2).1, (ha η h1).2⟩
  refine ⟨fun ξ => ∑ η ∈ (hfin ξ).toFinset, a η * b (ξ - η), ⟨⟨D * E, Nat.mul_pos hD hE, ?_⟩, ?_⟩,
    fun ξ => ⟨_, rfl⟩⟩
  · intro ξ hξ
    obtain ⟨η, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hξ
    have h1 : a η ≠ 0 := left_ne_zero_of_mul hne
    have h2 : b (ξ - η) ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨p1, i1⟩ := ha η h1
    obtain ⟨p2, i2⟩ := hb _ h2
    have hsum : ξ = η + (ξ - η) := by ring
    refine ⟨?_, ?_⟩
    · rcases p1 with e1 | t1 <;> rcases p2 with e2 | t2
      · left; rw [e1, sub_zero] at e2; exact e2
      · right; rw [e1, sub_zero] at t2; exact t2
      · right; rw [sub_eq_zero] at e2; rw [e2]; exact t1
      · right; rw [hsum]; exact TP_add t1 t2
    · have hE' : IsIntegral ℤ (E : F) := by
        have := isIntegral_algebraMap (R := ℤ) (A := F) (x := (E : ℤ))
        simpa using this
      have hD' : IsIntegral ℤ (D : F) := by
        have := isIntegral_algebraMap (R := ℤ) (A := F) (x := (D : ℤ))
        simpa using this
      have : ((D * E : ℕ) : F) * ξ = (E : F) * ((D : F) * η) + (D : F) * ((E : F) * (ξ - η)) := by
        push_cast; ring
      rw [this]
      exact (hE'.mul i1).add (hD'.mul i2)
  · intro z
    have hu := summable_norm_iff.mpr (hf z).summable
    have hw := summable_norm_iff.mpr (hg z).summable
    have H : HasSum (fun p : F × F => (a p.1 * ez p.1 z) * (b p.2 * ez p.2 z)) (f z * g z) := by
      have hs := summable_mul_of_summable_norm hu hw
      have ht := tsum_mul_tsum_of_summable_norm hu hw
      rw [(hf z).tsum_eq, (hg z).tsum_eq] at ht
      rw [ht]; exact hs.hasSum
    let e : F × F ≃ F × F :=
      { toFun := fun p => (p.2, p.1 - p.2), invFun := fun q => (q.1 + q.2, q.1),
        left_inv := fun p => by simp, right_inv := fun q => by simp }
    have H2 := (e.hasSum_iff).mpr H
    refine H2.prod_fiberwise fun ξ => ?_
    have hx : (fun η => ((fun p : F × F => (a p.1 * ez p.1 z) * (b p.2 * ez p.2 z)) ∘ e) (ξ, η)) =
        fun η => a η * b (ξ - η) * ez ξ z := by
      funext η
      simp only [Function.comp, e, Equiv.coe_fn_mk]
      have : ez ξ z = ez η z * ez (ξ - η) z := by rw [← ez_add_qm, add_sub_cancel]
      rw [this]; ring
    rw [hx, Finset.sum_mul]
    apply hasSum_sum_of_ne_finset_zero
    intro η hη
    have : a η * b (ξ - η) = 0 := by
      by_contra h
      exact hη ((hfin ξ).mem_toFinset.mpr h)
    rw [this, zero_mul]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_mul_finite_convolution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ), HasQ f a → HasQ g b → ∃ c, HasQ (f * g) c ∧ ∀ ξ, ∃ s : Finset F, c ξ = ∑ η ∈ s, a η * b (ξ - η) := by
  first | exact @GlobalTheory.HilbertThetaSeries.hasQ_mul | exact GlobalTheory.HilbertThetaSeries.hasQ_mul | (intros; apply GlobalTheory.HilbertThetaSeries.hasQ_mul <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.StabilizerEqScalarMulCongruenceMulFinset
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.StabFin

variable {F : Type} [Field F] [NumberField F]

theorem cover_gen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K U : Subgroup G)
    (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G)) (g : G) :
    ∃ C : Finset G, ∀ k ∈ K, ∃ c ∈ C, g * k * g⁻¹ * c⁻¹ ∈ U := by
  have hc : IsCompact ((fun k : G => g * k * g⁻¹) '' (K : Set G)) := hK.image (by fun_prop)
  obtain ⟨C, hC⟩ := hc.elim_finite_subcover (fun c : G => (fun x => x * c⁻¹) ⁻¹' (U : Set G))
    (fun c => hU.preimage (by fun_prop)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ⟨C, fun k hk => ?_⟩
  obtain ⟨c, hc, h⟩ := Set.mem_iUnion₂.1 (hC ⟨k, hk, rfl⟩)
  exact ⟨c, hc, h⟩

theorem cover (g : GL (Fin 2) (Af F)) {N : ℕ} (hN : 0 < N) :
    ∃ C : Finset (GL (Fin 2) (Af F)), ∀ k ∈ KLev F 2 1, ∃ c ∈ C, g * k * g⁻¹ * c⁻¹ ∈ KLev F 2 N :=
  cover_gen _ _ (isCompact_KLev le_rfl) (isOpen_KLev hN) g

theorem toFin_scalar (η : Fˣ) : toFin (Matrix.GeneralLinearGroup.scalar (Fin 2) η) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap F (Af F)).toMonoidHom η) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toFin, Matrix.GeneralLinearGroup.scalar]

theorem det_toFin (δ : GL (Fin 2) F) : (toFin δ).val.det = algebraMap F (Af F) δ.val.det := by
  rw [RingHom.map_det]; rfl

theorem exists_unit {x : F} (h : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x = 1) (hx : x ≠ 0) :
    ∃ ε : (𝓞 F)ˣ, ((ε : 𝓞 F) : F) = x := by
  have H := (GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.2.2.2
  have h1 : IsIntegral ℤ x := (H x).1 fun w => (h w).le
  have h2 : IsIntegral ℤ x⁻¹ := (H _).1 fun w => by rw [map_inv₀, h w, inv_one]
  refine ⟨⟨⟨x, h1⟩, ⟨x⁻¹, h2⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx)
  · exact Subtype.ext (inv_mul_cancel₀ hx)

theorem det_unit {g k : GL (Fin 2) (Af F)} (hk : k ∈ KLev F 2 1) {δ : GL (Fin 2) F} (h : toFin δ = g * k * g⁻¹) :
    ∃ ε : (𝓞 F)ˣ, ((ε : 𝓞 F) : F) = δ.val.det := by
  obtain ⟨H1, -, -, H4, -⟩ := GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F
  refine exists_unit (fun w => ?_) δ.det_ne_zero
  have e : (toFin δ).val.det = k.val.det := by
    rw [h, Units.val_mul, Units.val_mul, Matrix.det_units_conj]
  rw [← H4, ← det_toFin, e]
  exact ((H1 k).1 hk).2 w

theorem integral_of_mem {x : F} (h : algebraMap F (Af F) x ∈ Ohat F) : IsIntegral ℤ x := by
  obtain ⟨-, -, -, H4, H5⟩ := GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F
  refine (H5 x).1 fun w => ?_
  rw [← H4]
  exact (Subring.mem_iInf.1 h w : pLoc F w (algebraMap F (Af F) x) ∈ w.adicCompletionIntegers F)

theorem inGam_of_mem {N : ℕ} (hN : 0 < N) {γ : GL (Fin 2) F} (hd : γ.val.det = 1) (h : toFin γ ∈ KLev F 2 N) :
    InGam N γ := by
  obtain ⟨h1, -, h3⟩ := mem_KLev.1 h
  refine ⟨hd, integral_of_mem (h1 0 0), integral_of_mem (h1 0 1), integral_of_mem ?_, integral_of_mem (h1 1 1)⟩
  obtain ⟨y, hy, e⟩ := h3 1 0
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e' : algebraMap F (Af F) (γ.val 1 0) = (N : Af F) * y := by
    rw [← e]; simp [toFin]
  have : algebraMap F (Af F) (γ.val 1 0 / N) = y := by
    rw [div_eq_inv_mul, map_mul, e', ← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul,
      inv_mul_cancel₀ hN', map_one, one_mul]
  rwa [this]

theorem unit_scalar_mem (ε : (𝓞 F)ˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2)
    (Units.map (algebraMap F (Af F)).toMonoidHom (Units.map (algebraMap (𝓞 F) F).toMonoidHom ε)) ∈ KLev F 2 1 := by
  obtain ⟨-, H2, -, H4, -⟩ := GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F
  refine (H2 _ 0 (fun w => ?_) (fun w => by simp)).2
  refine (H4 (algebraMap (𝓞 F) F ε) w).trans ?_
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 fun h => w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ε.isUnit)

theorem invariants [IsTotallyReal F] (g : GL (Fin 2) (Af F)) {N : ℕ} (hN : 0 < N) :
    ∃ I : Finset (F × GL (Fin 2) (Af F)), ∀ γ, Stab g γ → ∃ i ∈ I, ∃ η : Fˣ,
      (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det = i.1 ∧
        toFin (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) * i.2⁻¹ ∈ KLev F 2 N := by
  classical
  obtain ⟨⟨Y, hY⟩, E, hE⟩ := GlobalTheory.T.finite_narrowIdeleClasses_and_units_mod_squares F
  obtain ⟨C, hC⟩ := cover g hN
  have hb : ∀ y : (Af F)ˣ, ∃ b : GL (Fin 2) F, ∀ δ : GL (Fin 2) F, ∀ k ∈ KLev F 2 1,
      toFin δ = Matrix.GeneralLinearGroup.scalar (Fin 2) y * (g * k * g⁻¹) →
        ∃ k' ∈ KLev F 2 1, toFin (δ * b⁻¹) = g * k' * g⁻¹ := fun y => by
    by_cases h : ∃ b : GL (Fin 2) F, ∃ k ∈ KLev F 2 1,
      toFin b = Matrix.GeneralLinearGroup.scalar (Fin 2) y * (g * k * g⁻¹)
    · obtain ⟨b, k₀, hk₀, e⟩ := h
      refine ⟨b, fun δ k hk e' => ⟨k * k₀⁻¹, mul_mem hk (inv_mem hk₀), ?_⟩⟩
      rw [map_mul, map_inv, e, e', Matrix.GeneralLinearGroup.scalar_commute y,
        Matrix.GeneralLinearGroup.scalar_commute y]
      group
    · exact ⟨1, fun δ k hk e => absurd ⟨δ, k, hk, e⟩ h⟩
  choose b hb using hb
  refine ⟨(Y ×ˢ E ×ˢ C).image fun t => (((t.2.1 : 𝓞 F) : F) * (b t.1).val.det, t.2.2 * toFin (b t.1)), ?_⟩
  rintro γ ⟨-, z, u, hu, e⟩
  obtain ⟨y, hy, ξ, v, -, hv, rfl⟩ := hY z
  have hvK := ((GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.1 v 0 hv (fun w => by simp)).2
  obtain ⟨k, hk, ek⟩ := hb y (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ⁻¹ * γ) _ (mul_mem hvK hu) (by
    rw [map_mul, eq_mul_inv_of_mul_eq e, map_inv, map_inv, toFin_scalar, map_mul, map_mul, ← mul_assoc g,
      ← Matrix.GeneralLinearGroup.scalar_commute v g]
    group)
  obtain ⟨ε, hε⟩ := det_unit hk ek
  obtain ⟨e₀, he₀, η, rfl⟩ := hE ε
  obtain ⟨c, hc, hcK⟩ := hC _ (mul_mem (unit_scalar_mem η⁻¹) hk)
  refine ⟨_, Finset.mem_image.2 ⟨(y, e₀, c), by simp [hy, he₀, hc], rfl⟩,
    Units.map (algebraMap (𝓞 F) F).toMonoidHom η⁻¹ * ξ⁻¹, ?_, ?_⟩
  · have h1 : (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ⁻¹ * γ).val.det =
        ((e₀ * η ^ 2 : (𝓞 F)ˣ) : 𝓞 F) * (b y).val.det := by
      rw [hε, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel_right]
    rw [map_mul, mul_assoc, Units.val_mul, Matrix.det_mul, h1, ← Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.det_scalar]
    have hη : ((η : 𝓞 F) : F) ≠ 0 := by simp
    simp
    field_simp
  · convert hcK using 1
    rw [map_mul (Matrix.GeneralLinearGroup.scalar (Fin 2)), mul_assoc _ _ γ, map_mul toFin, toFin_scalar, ← mul_assoc g, ← Matrix.GeneralLinearGroup.scalar_commute _ g,
      mul_assoc _ g k, mul_assoc _ (g * k), ← ek, map_mul toFin _ (b y)⁻¹, map_inv toFin]
    group

theorem finite_index : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : GL (Fin 2) (Af F)) (N : ℕ), 0 < N → ∃ T : Finset (GL (Fin 2) F), (∀ τ ∈ T, Stab g τ) ∧ ∀ γ, Stab g γ → ∃ (η : Fˣ) (γ₀ : GL (Fin 2) F), ∃ τ ∈ T, InGam N γ₀ ∧ γ = Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ₀ * τ := by
  classical
  intro F _ _ _ g N hN
  obtain ⟨I, hI⟩ := invariants g hN
  let P : GL (Fin 2) F → F × GL (Fin 2) (Af F) → Prop := fun γ i => Stab g γ ∧ ∃ η : Fˣ,
      (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det = i.1 ∧
        toFin (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) * i.2⁻¹ ∈ KLev F 2 N
  have hr : ∀ i, ∃ τ, (∃ γ, P γ i) → P τ i := fun i => by
    by_cases h : ∃ γ, P γ i
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose r hr using hr
  refine ⟨(I.filter fun i => ∃ γ, P γ i).image r, fun τ hτ => ?_, fun γ hγ => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hτ
    exact (hr i (Finset.mem_filter.1 hi).2).1
  · obtain ⟨i, hi, η, h1, h2⟩ := hI γ hγ
    have hP : ∃ γ, P γ i := ⟨γ, hγ, η, h1, h2⟩
    obtain ⟨-, η', h1', h2'⟩ := hr i hP
    refine ⟨η⁻¹ * η', Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) η' * r i)⁻¹, r i,
      Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hi, hP⟩), inGam_of_mem hN ?_ ?_, ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, h1, ← h1', ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.det_one]
    · convert mul_mem h2 (inv_mem h2') using 1
      rw [map_mul toFin (_ * γ), map_inv]
      group
    · rw [mul_comm η⁻¹, map_mul, map_inv, Matrix.GeneralLinearGroup.scalar_commute η' (r i), mul_assoc, mul_assoc,
        Matrix.GeneralLinearGroup.scalar_commute η']
      rw [← Matrix.GeneralLinearGroup.scalar_commute η' (r i), mul_assoc, mul_assoc, mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute η' (r i)]
      group

end GlobalTheory.HilbertThetaSeries.StabFin

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_eq_scalar_mul_congruence_mul_finset : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : GL (Fin 2) (Af F)) (N : ℕ), 0 < N → ∃ T : Finset (GL (Fin 2) F), (∀ τ ∈ T, Stab g τ) ∧ ∀ γ, Stab g γ → ∃ (η : Fˣ) (γ₀ : GL (Fin 2) F), ∃ τ ∈ T, InGam N γ₀ ∧ γ = Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ₀ * τ := by
  first | exact @GlobalTheory.HilbertThetaSeries.StabFin.finite_index | exact GlobalTheory.HilbertThetaSeries.StabFin.finite_index | (intros; apply GlobalTheory.HilbertThetaSeries.StabFin.finite_index <;> assumption)
end

