module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
public import ReciprocityTheory.GaloisValuations.GlobalB
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0336
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0341

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapPadicIntQbarContinuous
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory

theorem algebraMap_padicInt_qbar_continuous (l : ℕ) [Fact l.Prime] :
    Continuous (algebraMap ℤ_[l] (Qbar l)) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l)]
  exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (by exact continuous_subtype_val)

theorem Coef.isCompact_O (l : ℕ) [Fact l.Prime] (c : Coef l) :
    IsCompact ((c.O : Set (Qbar l))) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ_[l] c.O
  have hg : Continuous (fun v : Fin n → ℤ_[l] => ((f v : c.O) : Qbar l)) := by
    have h : (fun v : Fin n → ℤ_[l] => ((f v : c.O) : Qbar l)) =
        fun v => ∑ i, algebraMap ℤ_[l] (Qbar l) (v i) *
          ((f (fun j => if i = j then 1 else 0) : c.O) : Qbar l) := by
      funext v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      simp [Algebra.smul_def]
    rw [h]
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact ((algebraMap_padicInt_qbar_continuous l).comp (continuous_apply i)).mul continuous_const
  have hrange : Set.range (fun v : Fin n → ℤ_[l] => ((f v : c.O) : Qbar l)) = (c.O : Set (Qbar l)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (f v).2
    · intro hx
      obtain ⟨v, hv⟩ := hf ⟨x, hx⟩
      exact ⟨v, by simp [hv]⟩
  rw [← hrange]
  exact isCompact_range hg

theorem norm_natCast_prime_qbar (l : ℕ) [Fact l.Prime] :
    ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem coef_limit (l : ℕ) [Fact l.Prime] (c : Coef l) (a : ℕ → Qbar l)
    (ha : ∀ r, a r ∈ c.O) (hstep : ∀ r, ‖a (r + 1) - a r‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) :
    ∃ b ∈ c.O, ∀ r, ‖b - a r‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  set q : ℝ := ‖((l : ℕ) : Qbar l)‖ with hq
  have hq1 : q < 1 := norm_natCast_prime_qbar l
  have hq0 : 0 ≤ q := norm_nonneg _
  have hstep' : ∀ r, ‖a (r + 1) - a r‖ ≤ q ^ r := fun r => by simpa [norm_pow] using hstep r

  have htail : ∀ N k, ‖a (N + k) - a N‖ ≤ q ^ N := by
    intro N k
    induction k with
    | zero => simpa using pow_nonneg hq0 N
    | succ k ih =>
      have e : a (N + (k + 1)) - a N = (a (N + k + 1) - a (N + k)) + (a (N + k) - a N) := by
        rw [← add_assoc]; abel
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (hstep' (N + k)).trans (pow_le_pow_of_le_one hq0 hq1.le (Nat.le_add_right N k))
  have htail' : ∀ N n, N ≤ n → ‖a n - a N‖ ≤ q ^ N := by
    intro N n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact htail N k
  have hcau : CauchySeq a := by
    refine cauchySeq_of_le_tendsto_0 (fun N => q ^ N) (fun n m N hn hm => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    rw [dist_eq_norm]
    have e : a n - a m = (a n - a N) + -(a m - a N) := by abel
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (htail' N n hn) ?_)
    rw [norm_neg]; exact htail' N m hm
  obtain ⟨b, hb, hlim⟩ := cauchySeq_tendsto_of_isComplete (GlobalTheory.Coef.isCompact_O l c).isComplete ha hcau
  refine ⟨b, hb, fun r => ?_⟩
  have hmem : b ∈ Metric.closedBall (a r) (q ^ r) := by
    refine Metric.isClosed_closedBall.mem_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop r] with n hn
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact htail' r n hn
  rw [Metric.mem_closedBall, dist_eq_norm] at hmem
  simpa [norm_pow] using hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryInertiaIndependent
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.CobConj

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_memO (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : c.O) := Algebra.IsIntegral.isIntegral _
  exact norm_le_one_of_isIntegral x (hi.map c.O.val)

def Sm (n : ℕ) (v : Fin 2 → Qbar l) : Prop := ∀ i, ‖v i‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖

theorem sm_add {n : ℕ} {a b : Fin 2 → Qbar l} (ha : Sm n a) (hb : Sm n b) : Sm n (a + b) := fun i =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))

theorem sm_neg {n : ℕ} {a : Fin 2 → Qbar l} (ha : Sm n a) : Sm n (-a) := fun i => by
  simpa using ha i

theorem sm_sub {n : ℕ} {a b : Fin 2 → Qbar l} (ha : Sm n a) (hb : Sm n b) : Sm n (a - b) := by
  rw [sub_eq_add_neg]; exact sm_add ha (sm_neg hb)

theorem sm_mulVec (c : Coef l) {n : ℕ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O)
    {a : Fin 2 → Qbar l} (ha : Sm n a) : Sm n (M *ᵥ a) := fun i => by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (norm_le_one_of_memO c (hM _ _)) (ha _) (norm_nonneg _) zero_le_one).trans (by rw [one_mul])

theorem cv_iff {n : ℕ} {a b : Fin 2 → Qbar l} : Cv n a b ↔ Sm n (a - b) := Iff.rfl

theorem key_identity (Mσ Ms Mτ : Matrix (Fin 2) (Fin 2) (Qbar l)) (hτσ : Mτ * Mσ = 1)
    (zs' zσ zsτ zs zτ z1 x : Fin 2 → Qbar l) :
    zs' - ((Mσ * Ms * Mτ) *ᵥ (Mσ *ᵥ x - zσ) - (Mσ *ᵥ x - zσ)) =
      (zs' - (zσ + Mσ *ᵥ zsτ)) + Mσ *ᵥ (zsτ - (zs + Ms *ᵥ zτ)) + Mσ *ᵥ (zs - (Ms *ᵥ x - x))
        - Mσ *ᵥ (Ms *ᵥ (z1 - (z1 + (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z1)))
        - Mσ *ᵥ (Ms *ᵥ (z1 - (zτ + Mτ *ᵥ zσ))) := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.one_mulVec, Matrix.mul_assoc, hτσ,
    Matrix.mul_one]
  abel

theorem cob_conj : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (q : Pl) (B B' : ValuationSubring Ω), (∀ s i j, mat W s i j ∈ c.O) → Coc1 c n W ⊤ z → IsPlaceOver B q → IsPlaceOver B' q → Cob1 c n W (Ine (F := ℚ) B) z → Cob1 c n W (Ine (F := ℚ) B') z := by
  intro l _ Ω _ _ _ W c n z q B B' hW hC hB hB' hcob
  obtain ⟨x, hxO, hx⟩ := hcob
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hB hB'
  have hcoc : ∀ a b : G ℚ Ω, Sm n (z (a * b) - (z a + mat W a *ᵥ z b)) := fun a b =>
    hC.2.2 a (Subgroup.mem_top a) b (Subgroup.mem_top b)
  have hτσ : mat W σ⁻¹ * mat W σ = 1 := by
    simp only [mat, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h1 : mat W 1 = 1 := by simp [mat]
  refine ⟨mat W σ *ᵥ x - z σ, fun i => ?_, fun s' hs' => ?_⟩
  · simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.sub_mem (c.O.add_mem (c.O.mul_mem (hW _ _ _) (hxO _)) (c.O.mul_mem (hW _ _ _) (hxO _))) (hC.2.1 σ i)
  set s := σ⁻¹ * s' * σ with hsdef
  have hs : s ∈ Ine (F := ℚ) B := GlobalTheory.ParamRepCompare.conj_mem_Ine_of_smul_eq hσ hs'
  have e : s' = σ * (s * σ⁻¹) := by rw [hsdef]; group
  have hM : mat W s' = mat W σ * mat W s * mat W σ⁻¹ := by
    rw [e]; simp only [mat, map_mul, Units.val_mul, Matrix.mul_assoc]
  rw [cv_iff, hM, key_identity _ _ _ hτσ (z s') (z σ) (z (s * σ⁻¹)) (z s) (z σ⁻¹) (z 1) x]
  have hA : Sm n (z s' - (z σ + mat W σ *ᵥ z (s * σ⁻¹))) := by
    have := hcoc σ (s * σ⁻¹); rwa [← e] at this
  have hD : Sm n (z 1 - (z 1 + (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z 1)) := by
    have := hcoc 1 1; rwa [mul_one, h1] at this
  have hE : Sm n (z 1 - (z σ⁻¹ + mat W σ⁻¹ *ᵥ z σ)) := by
    have := hcoc σ⁻¹ σ; rwa [inv_mul_cancel] at this
  exact sm_sub (sm_sub (sm_add (sm_add hA (sm_mulVec c (hW σ) (hcoc s σ⁻¹))) (sm_mulVec c (hW σ) (hx s hs)))
    (sm_mulVec c (hW σ) (sm_mulVec c (hW s) hD))) (sm_mulVec c (hW σ) (sm_mulVec c (hW s) hE))

end GlobalTheory.Ord2.CobConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfOrthogonalDualCharacterModPrimePowStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_of_orthogonal_dualCharacter_modPrimePow : LocalFiniteness → LocalTateDuality → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ θ' : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → Continuous (fun g => ((θ' g : c.Oˣ) : c.O)) → θ * θ' = (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype → ∀ n : ℕ, 1 ≤ n → ∀ b : ↥(Dec (F := ℚ) A) → c.O, Continuous b → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ b (s * t) - (b s + ((θ s : c.Oˣ) : c.O) * b t)) → (∀ a : ↥(Dec (F := ℚ) A) → c.O, Continuous a → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a (s * t) - (a s + ((θ' s : c.Oˣ) : c.O) * a t)) → ∃ u : ↥(Dec (F := ℚ) A) → c.O, Continuous u ∧ ∀ s t, ((l : ℕ) : c.O) ^ n ∣ b s * (((θ' s : c.Oˣ) : c.O) * a t) - ((((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) * u t - u (s * t) + u s)) → ∃ x : c.O, ∀ s, ((l : ℕ) : c.O) ^ n ∣ b s - (((θ s : c.Oˣ) : c.O) * x - x) := by
  first | exact @GlobalTheory.Ord2.LocCharPerfect.perfect | exact GlobalTheory.Ord2.LocCharPerfect.perfect | (intros; apply GlobalTheory.Ord2.LocCharPerfect.perfect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfUniformLimitCoboundariesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_of_uniform_limit_coboundaries : ∀ {𝕜 : Type} [NormedField 𝕜] {Γ : Type} (H : Set Γ) (k f : Γ → 𝕜), (∃ s ∈ H, k s ≠ 1) → (∀ ε : ℝ, 0 < ε → ∃ X : 𝕜, ∀ s ∈ H, ‖f s - (k s * X - X)‖ ≤ ε) → ∃ X : 𝕜, ∀ s ∈ H, f s = k s * X - X := by
  first | exact @GlobalTheory.coboundary_closed_of_uniform_approx | exact GlobalTheory.coboundary_closed_of_uniform_approx | (intros; apply GlobalTheory.coboundary_closed_of_uniform_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocyclePairingLocallyConstant
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.XiCoc

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_int (x : Qbar l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt
  | exact _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt
  | (apply _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> assumption)
  | (intros; apply _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt ..)

theorem norm_le_one (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  haveI := c.fin
  have : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  exact norm_le_one_of_int x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem eps_mem (c : Coef l) (s : G ℚ Ω) : eps l s ∈ c.O := by
  have h : eps l s = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]; rfl
  rw [h]; exact c.O.algebraMap_mem _

theorem eps_cont : Continuous fun s : G ℚ Ω => eps l s :=
  (continuous_algebraMap ℚ_[l] (Qbar l)).comp
    (continuous_subtype_val.comp ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)))

theorem eps_mul (r s : G ℚ Ω) : eps l (r * s) = eps l r * eps l s := by
  simp [eps, map_mul]

theorem mat_mul (W : R2 Ω l) (r s : G ℚ Ω) : mat W (r * s) = mat W r * mat W s := by
  simp [mat, map_mul]

theorem dt_val (W : R2 Ω l) (s : G ℚ Ω) : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
  simp [dt, mat]

theorem dt_inv (W : R2 Ω l) (h2 : dt W ^ 2 = 1) (s : G ℚ Ω) : (dt W s)⁻¹ = dt W s := by
  have h := congrArg (fun f => f s) h2
  simp only [MonoidHom.pow_apply, MonoidHom.one_apply] at h
  exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h)

theorem det_sq (W : R2 Ω l) (h2 : dt W ^ 2 = 1) (s : G ℚ Ω) : (mat W s).det * (mat W s).det = 1 := by
  have h := congrArg (fun f => f s) h2
  simp only [MonoidHom.pow_apply, MonoidHom.one_apply] at h
  rw [← dt_val, ← Units.val_mul, ← sq, h, Units.val_one]

theorem matD (W : R2 Ω l) (h2 : dt W ^ 2 = 1) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (mat W s).det) • mat W s := by
  have := dt_inv W h2 s
  simp [dual1, tw, mat, eps, Matrix.GeneralLinearGroup.scalar, this, ← dt_val]
  exact (Matrix.smul_eq_diagonal_mul _ _).symm

theorem sm_add {x y : Qbar l} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x + y‖ ≤ B :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

theorem sm_sub {x y : Qbar l} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x - y‖ ≤ B := by
  rw [sub_eq_add_neg]; exact sm_add hx (by rwa [norm_neg])

theorem sm_mul {a x : Qbar l} {B : ℝ} (ha : ‖a‖ ≤ 1) (hx : ‖x‖ ≤ B) : ‖a * x‖ ≤ B := by
  rw [norm_mul]
  calc ‖a‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ = ‖x‖ := one_mul _
    _ ≤ B := hx

theorem om_sm {e v : Fin 2 → Qbar l} {B : ℝ} (he : ∀ i, ‖e i‖ ≤ B) (hv : ∀ i, ‖v i‖ ≤ 1) : ‖om e v‖ ≤ B := by
  unfold om
  exact sm_sub (by rw [mul_comm]; exact sm_mul (hv 1) (he 0)) (by rw [mul_comm]; exact sm_mul (hv 0) (he 1))

theorem mulVec_sm {M : Matrix (Fin 2) (Fin 2) (Qbar l)} {v : Fin 2 → Qbar l} {B : ℝ} (hM : ∀ i j, ‖M i j‖ ≤ 1)
    (hv : ∀ i, ‖v i‖ ≤ B) (i : Fin 2) : ‖(M *ᵥ v) i‖ ≤ B := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact sm_add (sm_mul (hM i 0) (hv 0)) (sm_mul (hM i 1) (hv 1))

theorem mulVec_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} {v : Fin 2 → Qbar l} (hM : ∀ i j, M i j ∈ c.O)
    (hv : ∀ i, v i ∈ c.O) (i : Fin 2) : (M *ᵥ v) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact add_mem (mul_mem (hM i 0) (hv 0)) (mul_mem (hM i 1) (hv 1))

theorem psi_sm (n : ℕ) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (r s : G ℚ Ω) :
    ‖(((ψ (r * s)).toAdd.val : ℕ) : Qbar l) - ((ψ r).toAdd.val : ℕ) - ((ψ s).toAdd.val : ℕ)‖ ≤
      ‖((l : ℕ) : Qbar l) ^ n‖ := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have e1 : (ψ (r * s)).toAdd = (ψ r).toAdd + (ψ s).toAdd := by rw [map_mul, toAdd_mul]
  rw [e1, ZMod.val_add]
  set m := (ψ r).toAdd.val + (ψ s).toAdd.val
  have e2 : ((m % l ^ n : ℕ) : Qbar l) = (m : Qbar l) - ((l : ℕ) : Qbar l) ^ n * ((m / l ^ n : ℕ) : Qbar l) := by
    have := Nat.mod_add_div m (l ^ n)
    rw [eq_sub_iff_add_eq, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, this]
  have e3 : ((m % l ^ n : ℕ) : Qbar l) - ((ψ r).toAdd.val : ℕ) - ((ψ s).toAdd.val : ℕ) =
      -(((l : ℕ) : Qbar l) ^ n * ((m / l ^ n : ℕ) : Qbar l)) := by
    rw [e2]; simp only [m, Nat.cast_add]; ring
  rw [e3, norm_neg, norm_mul]
  calc _ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ * 1 :=
        mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_natCast_le_one _ _) (norm_nonneg _)
    _ = _ := mul_one _

theorem ident (Ar As : Matrix (Fin 2) (Fin 2) (Qbar l)) (er es Pp pr ps prs ut us ust cyz : Qbar l)
    (dr ds drs ys zs zt : Fin 2 → Qbar l) (hdet : Ar.det * Ar.det = 1)
    (hcyz : cyz = om ys (((es * As.det) • As) *ᵥ zt)) :
    er * (om ds (((es * As.det) • As) *ᵥ zt) - ps * Pp * es * ut) +
        (om dr (((er * Ar.det) • Ar) *ᵥ (zs + ((es * As.det) • As) *ᵥ zt)) - pr * Pp * er * ust) -
      ((om drs (((er * es * (Ar.det * As.det)) • (Ar * As)) *ᵥ zt) - prs * Pp * (er * es) * ut) +
        (om dr (((er * Ar.det) • Ar) *ᵥ zs) - pr * Pp * er * us)) =
    -om (drs - (dr + Ar *ᵥ ds + (pr * Pp) • (Ar *ᵥ ys))) (((er * es * (Ar.det * As.det)) • (Ar * As)) *ᵥ zt) +
      Pp * (er * es) * ut * (prs - pr - ps) - Pp * pr * er * (cyz - (es * ut - ust + us)) := by
  have key : er * (om ds (((es * As.det) • As) *ᵥ zt) - ps * Pp * es * ut) +
        (om dr (((er * Ar.det) • Ar) *ᵥ (zs + ((es * As.det) • As) *ᵥ zt)) - pr * Pp * er * ust) -
      ((om drs (((er * es * (Ar.det * As.det)) • (Ar * As)) *ᵥ zt) - prs * Pp * (er * es) * ut) +
        (om dr (((er * Ar.det) • Ar) *ᵥ zs) - pr * Pp * er * us)) -
    (-om (drs - (dr + Ar *ᵥ ds + (pr * Pp) • (Ar *ᵥ ys))) (((er * es * (Ar.det * As.det)) • (Ar * As)) *ᵥ zt) +
      Pp * (er * es) * ut * (prs - pr - ps) - Pp * pr * er * (cyz - (es * ut - ust + us))) =
    -(er * om ds (((es * As.det) • As) *ᵥ zt) + pr * Pp * er * cyz) * (Ar.det * Ar.det - 1) := by
    subst hcyz
    simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, Matrix.mul_apply, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.det_fin_two]
    ring
  linear_combination key + (-(er * om ds (((es * As.det) • As) *ᵥ zt) + pr * Pp * er * cyz)) * hdet

end GlobalTheory.Ord2.XiCoc


open GlobalTheory.Ord2.XiCoc in
theorem GlobalTheory.Ord2.cup_product_two_cocycle : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (W : R2 Ω l) (y z d : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (P : Qbar l) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → (toGS Ω (S : Set Pl)).ker ≤ N0g W ⊓ ψ.ker → IsLocallyConstant ψ → P ∈ c.O → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, y a = 0 ∧ z a = 0 ∧ Cv n (d a) 0) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → Continuous d → (∀ s i, d s i ∈ c.O) → (∀ s t, Cv n (d (s * t)) (d s + mat W s *ᵥ d t + ((((ψ s).toAdd.val : ℕ) : Qbar l) * P) • (mat W s *ᵥ y t))) → Coc2 c n S (fun s t => cup W d z s t - (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u t) := by
  intro l _ Ω _ _ _ c n S W y z d u P ψ hW hWO hdt hker hψ hP hy hz hyO hzO hyz0 hu huO huS hcup hd hdO hdrec
  set B : ℝ := ‖((l : ℕ) : Qbar l) ^ n‖
  have nO : ∀ x ∈ c.O, ‖x‖ ≤ 1 := fun x hx => norm_le_one c hx
  have detO : ∀ s, (mat W s).det ∈ c.O := fun s => by
    rw [Matrix.det_fin_two]; exact sub_mem (mul_mem (hWO _ _ _) (hWO _ _ _)) (mul_mem (hWO _ _ _) (hWO _ _ _))
  have DO : ∀ s i j, mat (dual1 W) s i j ∈ c.O := fun s i j => by
    rw [matD W hdt, Matrix.smul_apply, smul_eq_mul]; exact mul_mem (mul_mem (eps_mem c s) (detO s)) (hWO _ _ _)
  have psiO : ∀ s, ((((ψ s).toAdd.val : ℕ) : Qbar l)) ∈ c.O := fun s => natCast_mem c.O _
  have zrec : ∀ s t, z (s * t) = z s + mat (dual1 W) s *ᵥ z t := fun s t => by
    have := hz.2 s t
    rw [this]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hA : Continuous fun s => mat W s := Units.continuous_val.comp hW
    have hAij : ∀ i j, Continuous fun s => mat W s i j := fun i j =>
      (continuous_apply j).comp ((continuous_apply i).comp hA)
    have hdet : Continuous fun s => (mat W s).det := by
      simp_rw [Matrix.det_fin_two]
      exact ((hAij 0 0).mul (hAij 1 1)).sub ((hAij 0 1).mul (hAij 1 0))
    have hψc : Continuous fun s => (((ψ s).toAdd.val : ℕ) : Qbar l) :=
      (hψ.comp (fun x => ((x.toAdd.val : ℕ) : Qbar l))).continuous
    have hdi : ∀ i, Continuous fun s => d s i := fun i => (continuous_apply i).comp hd
    have hzi : ∀ i, Continuous fun s => z s i := fun i => (continuous_apply i).comp hz.1
    have he : Continuous fun s : G ℚ Ω => eps l s := eps_cont
    have hf : ∀ {f : G ℚ Ω → Qbar l}, Continuous f → Continuous fun p : G ℚ Ω × G ℚ Ω => f p.1 :=
      fun h => h.comp continuous_fst
    have hg : ∀ {f : G ℚ Ω → Qbar l}, Continuous f → Continuous fun p : G ℚ Ω × G ℚ Ω => f p.2 :=
      fun h => h.comp continuous_snd
    simp only [cup, om, matD W hdt, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
    have hD : ∀ i j, Continuous fun p : G ℚ Ω × G ℚ Ω => eps l p.1 * (mat W p.1).det * mat W p.1 i j :=
      fun i j => ((hf he).mul (hf hdet)).mul (hf (hAij i j))
    exact (((hf (hdi 0)).mul (((hD 1 0).mul (hg (hzi 0))).add ((hD 1 1).mul (hg (hzi 1))))).sub
      ((hf (hdi 1)).mul (((hD 0 0).mul (hg (hzi 0))).add ((hD 0 1).mul (hg (hzi 1)))))).sub
      ((((hf hψc).mul continuous_const).mul (hf he)).mul (hg hu))
  ·
    intro s t
    refine sub_mem ?_ (mul_mem (mul_mem (mul_mem (psiO s) hP) (eps_mem c s)) (huO t))
    unfold cup om
    exact sub_mem (mul_mem (hdO s 0) (mulVec_mem c (DO s) (hzO t) 1)) (mul_mem (hdO s 1) (mulVec_mem c (DO s) (hzO t) 0))
  ·
    intro r s t
    show ‖_ - _‖ ≤ B
    have key := ident (mat W r) (mat W s) (eps l r) (eps l s) P (((ψ r).toAdd.val : ℕ) : Qbar l)
      (((ψ s).toAdd.val : ℕ) : Qbar l) (((ψ (r * s)).toAdd.val : ℕ) : Qbar l) (u t) (u s) (u (s * t)) (cup W y z s t)
      (d r) (d s) (d (r * s)) (y s) (z s) (z t) (det_sq W hdt r) (by rw [cup, matD W hdt])
    simp only [cup, zrec, matD W hdt, mat_mul, eps_mul, Matrix.det_mul] at key ⊢
    rw [key]
    have hV : ∀ s' i j, ((eps l s' * (mat W s').det) • mat W s') i j ∈ c.O := fun s' i j => by
      rw [← matD W hdt]; exact DO s' i j
    have hVrs : ∀ i, ‖(((eps l r * eps l s * ((mat W r).det * (mat W s).det)) • (mat W r * mat W s)) *ᵥ z t) i‖ ≤ 1 := by
      intro i
      refine nO _ (mulVec_mem c (fun i j => ?_) (hzO t) i)
      have := hV (r * s) i j
      rwa [mat_mul, eps_mul, Matrix.det_mul] at this
    have hEu := hcup s t
    simp only [Cg, cup, matD W hdt] at hEu
    refine sm_sub (sm_add (by rw [norm_neg]; exact om_sm (fun i => hdrec r s i) hVrs)
      (sm_mul (nO _ (mul_mem (mul_mem hP (mul_mem (eps_mem c r) (eps_mem c s))) (huO t))) (psi_sm n ψ r s)))
      (sm_mul (nO _ (mul_mem (mul_mem hP (psiO r)) (eps_mem c r))) hEu)
  ·
    intro s t a ha b hb
    have ha' := hker ha
    simp only [N0g, Subgroup.mem_inf, MonoidHom.mem_ker] at ha'
    obtain ⟨⟨hca, hWa⟩, hψa⟩ := ha'
    have hAa : mat W a = 1 := by simp [mat, hWa]
    have hea : eps l a = 1 := by simp [eps, hca]
    have hAsa : mat W (s * a) = mat W s := by rw [mat_mul, hAa, mul_one]
    have hesa : eps l (s * a) = eps l s := by rw [eps_mul, hea, mul_one]
    have hψsa : ψ (s * a) = ψ s := by rw [map_mul, hψa, mul_one]
    have hztb : z (t * b) = z t := by rw [zrec, (hyz0 b hb).2.1]; simp
    show ‖_ - _‖ ≤ B
    simp only [cup, matD W hdt, hAsa, hesa, hψsa, hztb]
    have hE : ∀ i, ‖(d (s * a) - d s) i‖ ≤ B := by
      intro i
      have h1 := hdrec s a i
      simp only [Cg, (hyz0 a ha).1, Matrix.mulVec_zero, smul_zero, add_zero, Pi.add_apply, Pi.zero_apply] at h1
      have h2 : ‖(mat W s *ᵥ d a) i‖ ≤ B :=
        mulVec_sm (fun i j => nO _ (hWO s i j)) (fun j => by have h0 := (hyz0 a ha).2.2 j; simp only [Cg, Pi.zero_apply, sub_zero] at h0; exact h0) i
      have h3 : (d (s * a) - d s) i = (d (s * a) i - (d s i + (mat W s *ᵥ d a) i)) + (mat W s *ᵥ d a) i := by
        simp only [Pi.sub_apply]; ring
      rw [h3]; exact sm_add h1 h2
    have hVs : ∀ i, ‖(((eps l s * (mat W s).det) • mat W s) *ᵥ z t) i‖ ≤ 1 := by
      intro i
      refine nO _ (mulVec_mem c (fun i j => ?_) (hzO t) i)
      rw [← matD W hdt]; exact DO s i j
    have e : om (d (s * a)) (((eps l s * (mat W s).det) • mat W s) *ᵥ z t) -
          (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u (t * b) -
        (om (d s) (((eps l s * (mat W s).det) • mat W s) *ᵥ z t) -
          (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u t) =
        om (d (s * a) - d s) (((eps l s * (mat W s).det) • mat W s) *ᵥ z t) -
          ((((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s) * (u (t * b) - u t) := by
      simp only [om, Pi.sub_apply]; ring
    rw [e]
    exact sm_sub (om_sm hE hVs) (sm_mul (nO _ (mul_mem (mul_mem (psiO s) hP) (eps_mem c s))) (huS t b hb))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocycleVanishesOnKerToGSOfInertiaCoboundary
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

theorem cocycle_zero_on_ker_toGS : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (Y : G ℚ Ω → Fin 2 → Qbar l), Nf e S A W → Y ∈ Z1 (Loc.colRep W) → (∀ q : Pl, q ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, Y s = mat W s *ᵥ x - x) → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Y a = 0 := by
  intro l _ Ω _ _ _ e S A W Y hN hY hc a ha
  have hcoc : ∀ g h, Y (g * h) = Y g + mat W g *ᵥ Y h := fun g h => ((mem_Z1_iff_cocycle _ _).1 hY).2 g h
  have hcont : Continuous Y := ((mem_Z1_iff_cocycle _ _).1 hY).1
  have h1 : Y 1 = 0 := by
    have := hcoc 1 1
    simpa [mat] using this
  let H : Subgroup (G ℚ Ω) :=
    { carrier := {g | Y g = 0 ∧ W g = 1}
      one_mem' := ⟨h1, map_one W⟩
      mul_mem' := fun {g h} hg hh => ⟨by rw [hcoc, hg.1, hh.1]; simp, by rw [map_mul, hg.2, hh.2, one_mul]⟩
      inv_mem' := fun {g} hg => by
        refine ⟨?_, by rw [map_inv, hg.2, inv_one]⟩
        have := hcoc g g⁻¹
        rw [mul_inv_cancel, h1, hg.1] at this
        simpa [mat, hg.2] using this.symm }
  have hH : ∀ g, g ∈ H ↔ Y g = 0 ∧ W g = 1 := fun g => Iff.rfl
  haveI : H.Normal := ⟨fun g hg h => by
    rw [hH] at hg ⊢
    refine ⟨?_, by rw [map_mul, map_mul, hg.2, mul_one, ← map_mul, mul_inv_cancel, map_one]⟩
    have e1 : Y (g * h⁻¹) = Y h⁻¹ := by
      rw [hcoc, hg.1]; simp [mat, hg.2]
    rw [mul_assoc, hcoc, e1, ← hcoc, mul_inv_cancel, h1]⟩
  have hcl : IsClosed (H : Set (G ℚ Ω)) :=
    (isClosed_singleton.preimage hcont).inter (isClosed_singleton.preimage hN.cont)
  have hle : Subgroup.normalClosure
      (⋃ v ∈ (S : Set Pl)ᶜ, ⋃ B ∈ {B : ValuationSubring Ω | IsPlaceOver B v}, Inertia (F := ℚ) B) ≤ H := by
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    have hv' : v ∉ S := by simpa using hv
    have hτ' : τ ∈ Ine (F := ℚ) B := hτ
    have hW : W τ = 1 := hN.unr v hv' B hB hτ'
    obtain ⟨x, hx⟩ := hc v hv' B hB
    refine (hH τ).2 ⟨?_, hW⟩
    rw [hx τ hτ']
    simp [mat, hW]
  have ha' : a ∈ NS Ω (S : Set Pl) := by
    rwa [toGS, QuotientGroup.ker_mk'] at ha
  exact ((hH a).1 (Subgroup.topologicalClosure_minimal _ hle hcl ha')).1

end GlobalTheory.Ord2.GwCount
end

