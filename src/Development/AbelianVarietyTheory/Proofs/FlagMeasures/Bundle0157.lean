module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem countHyp_one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  have hd : (1 : ℝ) ≤ |(discr I.E : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs (NumberField.discr_ne_zero I.E)
    exact_mod_cast h1
  show 1 ≤ |(discr I.E : ℝ)| ^ ((1 : ℝ) / (2 * (I.f : ℝ)))
  exact Real.one_le_rpow hd (by positivity)

theorem countHyp_card_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  have : IsTotallyReal I.F := I.cm.totReal
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
    add_zero]
  exact (IsTotallyReal.finrank I.F).symm

theorem countHyp_pAt_add_qAt (I : AutInst) (v : InfinitePlace I.F) : I.pAt v + I.qAt v = I.n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin I.n)))
    (fun a => I.ε v a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem countHyp_numerics : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → 0 ≤ Cg ∧ 1 ≤ B.I.rd ∧ 1 ≤ B.I.f ∧ Fintype.card (InfinitePlace B.I.F) = B.I.f ∧ p + q = B.I.n ∧ 2 * q + 2 ≤ B.I.n ∧ (∀ v, rkR (B.I.ε v) = q) ∧ min p q = q ∧ 0 < (∏ v, d v) ∧ 16 ≤ bigX B b ∧ 0 < tauStar B q b ∧ (1 ≤ q → tauStar B q b < 1 / 2 ∧ (B.I.n : ℝ) ^ 19 ≤ b ^ 2) ∧ ∃ h : ℝ, h = 8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) ∧ GapGe B h ∧ HBig B 40 h ∧ HBig B 32 h ∧ 8 * (B.I.n : ℝ) * q < h ∧ 120 * (B.I.n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h ∧ 40 * (B.I.n : ℝ) ^ 2 * Real.sqrt q ≤ h := by
  intro B Cg n₀ d p q b hn₀ hC
  unfold CountHyp at hC
  obtain ⟨hDS, hSig, hn, hq2, -, -, hb, -, hlam, hg1, hgC, -, -, -, hgap⟩ := hC
  have hrd : 1 ≤ B.I.rd := countHyp_one_le_rd B.I
  have hcard : Fintype.card (InfinitePlace B.I.F) = B.I.f := countHyp_card_places B.I
  have hf : 1 ≤ B.I.f := Module.finrank_pos
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace B.I.F) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨hp₀, hq₀⟩ := hSig v₀
  have hpq : p + q = B.I.n := by rw [← hp₀, ← hq₀]; exact countHyp_pAt_add_qAt B.I v₀
  have h2q : 2 * q + 2 ≤ B.I.n := by
    rcases Nat.lt_or_ge q 3 with h | h
    · omega
    · nlinarith
  have hqp : q ≤ p := by omega
  have hmin : min p q = q := min_eq_right hqp
  have hrk : ∀ v, rkR (B.I.ε v) = q := by
    intro v
    obtain ⟨hp, hq⟩ := hSig v
    show min (B.I.pAt v) (B.I.qAt v) = q
    rw [hp, hq, hmin]
  have hd : 0 < ∏ v, d v := by
    refine Finset.prod_pos fun v _ => ?_
    obtain ⟨-, -, -, ⟨hdv, -⟩⟩ := hDS v
    exact hdv
  have hCg : 0 ≤ Cg := by
    by_contra hneg
    have h1 : b ^ Cg < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (lt_of_not_ge hneg)
    have h2 : (1 : ℝ) ≤ B.g := by exact_mod_cast hg1
    linarith
  have hnr : (8 : ℝ) ≤ B.I.n := by exact_mod_cast le_trans hn₀ hn
  have hfr : (1 : ℝ) ≤ B.I.f := by exact_mod_cast hf
  have hgr : (1 : ℝ) ≤ B.g := by exact_mod_cast hg1
  have hX : 16 ≤ bigX B b := by
    show 16 ≤ (B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b
    have a1 : 8 ≤ (B.I.n : ℝ) * B.I.f := by nlinarith
    have a2 : 8 ≤ (B.I.n : ℝ) * B.I.f * B.I.rd := by nlinarith
    have a3 : 8 ≤ (B.I.n : ℝ) * B.I.f * B.I.rd * B.g := by nlinarith
    nlinarith
  have htpos : 0 < tauStar B q b := by
    show 0 < (bigX B b)⁻¹ ^ (11 * q)
    have : 0 < bigX B b := by linarith
    positivity

  have hL : Real.log 2 ≤ Real.log (b * B.I.rd) := Real.log_le_log (by norm_num) (by nlinarith)
  have hlog2 := Real.log_two_gt_d9
  have hF5 : (1 : ℝ) ≤ (B.I.f : ℝ) ^ 5 := one_le_pow₀ hfr
  have hP1 : 2 ≤ (Cg + 4) * Real.log (b * B.I.rd) := by nlinarith
  have hP : 2 ≤ (Cg + 4) * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) := by
    have : (Cg + 4) * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd)
        = ((Cg + 4) * Real.log (b * B.I.rd)) * (B.I.f : ℝ) ^ 5 := by ring
    rw [this]
    nlinarith
  have hN : 0 ≤ (B.I.n : ℝ) ^ 19 := by positivity
  have hbig : 10 ^ 15 * (B.I.n : ℝ) ^ 19 ≤
      8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) := by
    have : 8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd)
        = 8 * 10 ^ 14 * (B.I.n : ℝ) ^ 19 * ((Cg + 4) * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd)) := by
      ring
    rw [this]
    nlinarith
  have hn1 : (1 : ℝ) ≤ B.I.n := by linarith
  have hn2 : (B.I.n : ℝ) ^ 2 ≤ (B.I.n : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have hn3 : (B.I.n : ℝ) ^ 3 ≤ (B.I.n : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have hqn : (q : ℝ) ≤ B.I.n := by exact_mod_cast (show q ≤ B.I.n by omega)
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsq : Real.sqrt q ≤ B.I.n := by
    calc Real.sqrt q ≤ Real.sqrt ((B.I.n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = B.I.n := Real.sqrt_sq (by positivity)
  have hs40 : 40 * (B.I.n : ℝ) ^ 2 * Real.sqrt q ≤
      8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) := by
    have e1 : 40 * (B.I.n : ℝ) ^ 2 * Real.sqrt q ≤ 40 * (B.I.n : ℝ) ^ 2 * B.I.n :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e2 : 40 * (B.I.n : ℝ) ^ 2 * B.I.n = 40 * (B.I.n : ℝ) ^ 3 := by ring
    linarith
  refine ⟨hCg, hrd, hf, hcard, hpq, h2q, hrk, hmin, hd, hX, htpos, ?_, _, rfl, hgap, ?_, ?_, ?_, ?_, hs40⟩
  · intro hq1
    constructor
    · show (bigX B b)⁻¹ ^ (11 * q) < 1 / 2
      have hXp : 0 < bigX B b := by linarith
      have hi : (bigX B b)⁻¹ ≤ 16⁻¹ := inv_anti₀ (by norm_num) hX
      have hi0 : 0 ≤ (bigX B b)⁻¹ := inv_nonneg.mpr hXp.le
      have hpow : (bigX B b)⁻¹ ^ (11 * q) ≤ (bigX B b)⁻¹ :=
        pow_le_of_le_one hi0 (by linarith [show (16 : ℝ)⁻¹ ≤ 1 by norm_num]) (by omega)
      have : (16 : ℝ)⁻¹ < 1 / 2 := by norm_num
      linarith
    · have hpc : 0 < (Finset.univ.filter fun a => B.I.ε v₀ a = true).card := by
        show 0 < B.I.pAt v₀
        omega
      have hqc : 0 < (Finset.univ.filter fun a => B.I.ε v₀ a = false).card := by
        show 0 < B.I.qAt v₀
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpc
      obtain ⟨a', ha'⟩ := Finset.card_pos.mp hqc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
      have hne : B.I.ε v₀ a ≠ B.I.ε v₀ a' := by rw [ha, ha']; decide
      have hg := hgap v₀ a a' hne
      obtain ⟨l1, l2⟩ := abs_le.mp (hlam v₀ a)
      obtain ⟨l3, l4⟩ := abs_le.mp (hlam v₀ a')
      have hdiff : |B.lam v₀ a - B.lam v₀ a'| ≤ 2 * b ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hb0 : 0 ≤ b ^ 2 := by positivity
      linarith
  · intro v
    rw [hrk v]
    linarith
  · intro v
    rw [hrk v]
    have : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
    nlinarith
  · have hpos : 0 < (B.I.n : ℝ) ^ 19 := by positivity
    have e1 : 8 * (B.I.n : ℝ) * q ≤ 8 * (B.I.n : ℝ) ^ 2 := by nlinarith
    linarith
  · have r1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (B.I.n : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow hq0 hqn (by norm_num)
    have r2 : (B.I.n : ℝ) ^ ((3 : ℝ) / 2) ≤ (B.I.n : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    rw [Real.rpow_two] at r2
    have e1 : 120 * (B.I.n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (B.I.n : ℝ) * (B.I.n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (r1.trans r2) (by positivity)
    have e2 : 120 * (B.I.n : ℝ) * (B.I.n : ℝ) ^ 2 = 120 * (B.I.n : ℝ) ^ 3 := by ring
    linarith

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetConjOnMatricesKillingIntoSubspace
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.HomConjDet

section General

variable {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

theorem det_eq_of_equiv (e : U ≃ₗ[ℂ] V) (φ : U →ₗ[ℂ] U) (ψ : V →ₗ[ℂ] V)
    (h : ∀ x, e (φ x) = ψ (e x)) : LinearMap.det φ = LinearMap.det ψ := by
  rw [← LinearMap.det_conj φ e]
  congr 1
  ext y
  simp [h]

variable [Module.Finite ℂ U] [Module.Finite ℂ V]

theorem det_comp_left (α : V →ₗ[ℂ] V) :
    LinearMap.det (LinearMap.llcomp ℂ U V V α : (U →ₗ[ℂ] V) →ₗ[ℂ] (U →ₗ[ℂ] V)) = LinearMap.det α ^ Module.finrank ℂ U := by
  let b := Module.finBasis ℂ U
  have h := LinearMap.det_pi (fun _ : Fin (Module.finrank ℂ U) => α)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  symm
  refine det_eq_of_equiv (b.constr ℂ) _ _ fun x => ?_
  refine b.ext fun i => ?_
  simp

theorem det_comp_right (β : U →ₗ[ℂ] U) :
    LinearMap.det (LinearMap.lcomp ℂ V β) = LinearMap.det β ^ Module.finrank ℂ V := by
  let b := Module.finBasis ℂ V
  have h := LinearMap.det_pi (fun _ : Fin (Module.finrank ℂ V) => β.dualMap)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, LinearMap.det_dualMap] at h
  rw [← h]
  symm
  refine det_eq_of_equiv ((LinearEquiv.linearMapPi ℂ).trans (LinearEquiv.congrRight b.equivFun.symm))
    _ _ fun x => ?_
  ext y
  simp [LinearEquiv.congrRight]

end General

variable {n : ℕ}

def homMat (P Q : Submodule ℂ (Fin n → ℂ)) :
    (((Fin n → ℂ) ⧸ P) →ₗ[ℂ] Q) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.toMatrix' : ((Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ
    LinearMap.llcomp ℂ _ _ _ Q.subtype ∘ₗ LinearMap.lcomp ℂ Q P.mkQ

theorem homMat_mulVec (P Q : Submodule ℂ (Fin n → ℂ)) (T : ((Fin n → ℂ) ⧸ P) →ₗ[ℂ] Q) (y : Fin n → ℂ) :
    homMat P Q T *ᵥ y = (T (P.mkQ y) : Fin n → ℂ) := by
  simp [homMat, LinearMap.toMatrix'_mulVec]

theorem homMat_injective (P Q : Submodule ℂ (Fin n → ℂ)) : Function.Injective (homMat P Q) := by
  intro S T h
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := P.mkQ_surjective x
  apply Subtype.ext
  rw [← homMat_mulVec, ← homMat_mulVec, h]

theorem range_homMat (P Q : Submodule ℂ (Fin n → ℂ)) (H : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hH : ∀ X, X ∈ H ↔ (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q) : LinearMap.range (homMat P Q) = H := by
  ext X
  rw [hH]
  constructor
  · rintro ⟨T, rfl⟩
    refine ⟨fun y hy => ?_, fun y => ?_⟩
    · rw [homMat_mulVec, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hy]
      simp
    · rw [homMat_mulVec]
      exact Subtype.property _
  · rintro ⟨h1, h2⟩
    refine ⟨P.liftQ ((Matrix.toLin' X).codRestrict Q fun y => by simpa using h2 y) ?_, ?_⟩
    · intro y hy
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      simpa using h1 y hy
    · apply Matrix.toLin'.injective
      refine LinearMap.ext fun y => ?_
      rw [Matrix.toLin'_apply, homMat_mulVec]
      simp

theorem det_conj_hom : ∀ (n : ℕ) (f g : Matrix (Fin n) (Fin n) ℂ) (P Q : Submodule ℂ (Fin n → ℂ)) (H : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)), f * g = 1 → ‖f.det‖ = 1 → (∀ y ∈ P, f *ᵥ y ∈ P) → (∀ y ∈ Q, f *ᵥ y ∈ Q) → (∀ X, X ∈ H ↔ (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q) → Module.finrank ℂ H = (n - Module.finrank ℂ P) * Module.finrank ℂ Q ∧ ∀ φ : H →ₗ[ℂ] H, (∀ X : H, ((φ X : H) : Matrix (Fin n) (Fin n) ℂ) = f * (X : Matrix (Fin n) (Fin n) ℂ) * g) → ‖LinearMap.det φ‖ = detOn f Q ^ (n - Module.finrank ℂ P) * detOn f P ^ Module.finrank ℂ Q := by
  intro n f g P Q H hfg hdet hP hQ hH
  obtain rfl := range_homMat P Q H hH
  let e := LinearEquiv.ofInjective _ (homMat_injective P Q)
  have hq : Module.finrank ℂ ((Fin n → ℂ) ⧸ P) = n - Module.finrank ℂ P := by
    have := P.finrank_quotient_add_finrank
    rw [Module.finrank_fin_fun] at this
    omega
  refine ⟨?_, fun φ hφ => ?_⟩
  · rw [← e.finrank_eq, Module.finrank_linearMap, hq]
  have hgf : g * f = 1 := mul_eq_one_comm.1 hfg
  have hgP := GlobalTheory.FlagLeviGroup.inv_keeps hgf P hP
  have hP' : ∀ y ∈ P, Matrix.toLin' f y ∈ P := fun y hy => by simpa using hP y hy
  have hQ' : ∀ y ∈ Q, Matrix.toLin' f y ∈ Q := fun y hy => by simpa using hQ y hy
  have hgP' : P ≤ P.comap (Matrix.toLin' g) := fun y hy => by simpa using hgP y hy
  set α := (Matrix.toLin' f).restrict hQ' with hα
  set β := P.mapQ P (Matrix.toLin' g) hgP' with hβ
  have h1 : LinearMap.det (LinearMap.llcomp ℂ _ _ _ α ∘ₗ LinearMap.lcomp ℂ Q β) = LinearMap.det φ := by
    refine det_eq_of_equiv e _ _ fun T => ?_
    apply Subtype.ext
    rw [hφ]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun y => ?_
    simp only [Matrix.toLin'_apply, e, LinearEquiv.ofInjective_apply, ← Matrix.mulVec_mulVec,
      homMat_mulVec]
    simp [hα, hβ, LinearMap.restrict_apply]
  have h2 := LinearMap.det_eq_det_mul_det P (Matrix.toLin' g) hgP'
  have h3 : LinearMap.det ((Matrix.toLin' f).restrict hP') *
      LinearMap.det ((Matrix.toLin' g).restrict hgP') = 1 := by
    rw [← map_mul, ← LinearMap.det_id (A := ℂ) (M := P)]
    congr 1
    refine LinearMap.ext fun y => Subtype.ext ?_
    simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec, hfg]
  have h4 : ‖g.det‖ = 1 := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => ‖M.det‖) hfg
    simpa [hdet] using this
  have h5 : LinearMap.det β = LinearMap.det ((Matrix.toLin' f).restrict hP') * g.det := by
    rw [← LinearMap.det_toLin' g, h2, ← mul_assoc, h3, one_mul]
  rw [← h1, LinearMap.det_comp, det_comp_left, det_comp_right, hq, h5, detOn, detOn, dite_eq_left hP',
    dite_eq_left hQ']
  simp [h4, hα]

end GlobalTheory.HomConjDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsDer
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.DerOf

variable {n : ℕ} {ε : Fin n → Bool}

theorem rd_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) : Rd X f g = Rd X f' g := by
  unfold Rd
  congr 1
  funext t
  exact h _ (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))

theorem eab_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, inUJ ε g → f g = f' g)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : Eab ε a b f g = Eab ε a b f' g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold Eab Ec
  rw [rd_congr h h1 hg, rd_congr h h2 hg]

theorem J_single_J (a b : Fin n) :
    Jm ε * Matrix.single a b (1 : ℂ) * Jm ε = (sgn ε a b : ℂ) • Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [Jm, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ε a <;> cases ε b <;> simp
  · simp [h]

theorem sgn_comm (a b : Fin n) : sgn ε a b = sgn ε b a := by
  simp only [sgn, eq_comm]

theorem sgn_sq (a b : Fin n) : (sgn ε a b : ℂ) * sgn ε a b = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem cpart1_swap (a b : Fin n) : cpart1 ε (Matrix.single a b (1 : ℂ)) =
    ((-sgn ε a b : ℝ) : ℂ) • cpart1 ε (Matrix.single b a (1 : ℂ)) := by
  simp only [cpart1, conjTranspose_single, star_one, J_single_J, sgn_comm (ε := ε) b a]
  have := sgn_sq (ε := ε) a b
  push_cast
  match_scalars
  · linear_combination (-1 / 2 : ℂ) * this
  · ring

theorem cpart2_swap (a b : Fin n) : cpart2 ε (Matrix.single a b (1 : ℂ)) =
    ((sgn ε a b : ℝ) : ℂ) • cpart2 ε (Matrix.single b a (1 : ℂ)) := by
  simp only [cpart2, conjTranspose_single, star_one, J_single_J, sgn_comm (ε := ε) b a]
  have := sgn_sq (ε := ε) a b
  match_scalars
  · linear_combination (-1 / (2 * Complex.I) : ℂ) * this
  · ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H}

theorem exists_D (hV : ∀ v ∈ V, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ v' ∈ V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ D : Module.End ℂ V, inG ε X → ∀ v : V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) (D v : H) 0 := by
  by_cases hX : inG ε X
  · choose d hd hd' using fun v : V => hV v v.2 X hX
    refine ⟨⟨⟨fun v => ⟨d v, hd v⟩, fun v w => Subtype.ext ?_⟩, fun c v => Subtype.ext ?_⟩, fun _ v => hd' v⟩
    · refine (hd' (v + w)).unique ?_
      simpa using (hd' v).fun_add (hd' w)
    · refine (hd' (c • v)).unique ?_
      simpa using (hd' v).fun_const_smul c
  · exact ⟨0, fun h => absurd h hX⟩

theorem rd_coef (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v v' : H}
    (h : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) (y : H)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Rd X (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g v'⟫_ℂ := by
  have h1 := (((innerSL ℂ y).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  refine Eq.trans ?_ h1.deriv
  unfold Rd
  congr 1
  funext t
  have := hσ.1.2 g hg _ (exp_indefinite_unitary_holds n ε X hX t)
  simp only [this]
  rfl

theorem skew (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {x x' y y' : H}
    (hx : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) x) x' 0)
    (hy : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) y) y' 0) :
    ⟪x', y⟫_ℂ = -⟪x, y'⟫_ℂ := by
  have h := hx.inner ℂ hy
  have hc : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) x, σ (NormedSpace.exp ((t : ℂ) • X)) y⟫_ℂ)
      = fun _ => ⟪x, y⟫_ℂ := by
    funext t
    exact LinearIsometry.inner_map_map
      ⟨(σ (NormedSpace.exp ((t : ℂ) • X))).toLinearMap, hσ.2.1 _ (exp_indefinite_unitary_holds n ε X hX t)⟩ x y
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply] at h0
  linear_combination h0

theorem exists_isDer : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H),
    IsURepOn (UJset ε) σ →
    (∀ v ∈ V, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ v' ∈ V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) →
    (∀ v ∈ V, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ)) →
    ∃ E : Fin n → Fin n → Module.End ℂ V, IsDer ε σ V E := by
  intro n ε H _ _ _ σ V hσ hV hs
  choose D hD using exists_D hV
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have h1 : ∀ v : H, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have hc := fun a b : Fin n => complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have hR : ∀ X, inG ε X → ∀ (v : V) (y : H) g, inUJ ε g →
      Rd X (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g (D X v)⟫_ℂ :=
    fun X hX v y g hg => rd_coef hσ hX (hD X hX v) y hg
  set E : Fin n → Fin n → Module.End ℂ V := fun a b =>
    D (cpart1 ε (Matrix.single a b 1)) + Complex.I • D (cpart2 ε (Matrix.single a b 1)) with hE
  have hEab : ∀ a b (v : V) (y : H) g, inUJ ε g →
      Eab ε a b (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g (E a b v)⟫_ℂ := by
    intro a b v y g hg
    unfold Eab Ec
    rw [hR _ (hc a b).1 v y g hg, hR _ (hc a b).2.1 v y g hg]
    simp [hE, inner_add_right, inner_smul_right]
  have hsm : ∀ X (r : ℝ), inG ε X → inG ε ((r : ℂ) • X) → ∀ v : V,
      (D ((r : ℂ) • X) v : H) = (r : ℂ) • (D X v : H) := by
    intro X r hX hrX v
    refine ext_inner_left ℂ fun y => ?_
    have := (rdLin n ε _ _ X X r 0 1 (hs v v.2 y) (hs v v.2 y) hX hX hone).2.1
    rwa [hR _ hX v y 1 hone, hR _ hrX v y 1 hone, h1, h1, ← inner_smul_right] at this
  refine ⟨E, ?_, ?_, ?_, fun v y => hs v v.2 y⟩
  · intro a b c d
    refine LinearMap.ext fun v => Subtype.ext (ext_inner_left ℂ fun y => ?_)
    have := eabGl n ε _ a b c d 1 (hs v v.2 y) hone
    rw [eab_congr (hEab c d v y) a b hone, eab_congr (hEab a b v y) c d hone] at this
    simp only [hEab _ _ _ y 1 hone, h1] at this
    split_ifs at this ⊢ <;> simpa [inner_sub_right] using this
  · intro a b x y
    have e1 := hsm _ (-sgn ε a b) (hc b a).1 (cpart1_swap a b ▸ (hc a b).1) y
    have e2 := hsm _ (sgn ε a b) (hc b a).2.1 (cpart2_swap a b ▸ (hc a b).2.1) y
    rw [← cpart1_swap] at e1
    rw [← cpart2_swap] at e2
    have s1 := skew hσ (hc a b).1 (hD _ (hc a b).1 x) (hD _ (hc a b).1 y)
    have s2 := skew hσ (hc a b).2.1 (hD _ (hc a b).2.1 x) (hD _ (hc a b).2.1 y)
    rw [e1, inner_smul_right] at s1
    rw [e2, inner_smul_right] at s2
    simp only [hE, Submodule.coe_inner, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
      Submodule.coe_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, s1, s2,
      Complex.conj_I]
    push_cast
    ring
  · intro X hX v
    convert hD X hX v using 1
    refine ext_inner_left ℂ fun y => ?_
    have := ecSumV n ε ℂ _ X 1 (hs v v.2 y) hone
    obtain ⟨e1, e2⟩ := (complex_parts_mem_lie_algebra_holds n ε X).2.2.2 hX
    simp only [eabV_eq, hEab _ _ _ y 1 hone, h1] at this
    rw [EcV, e1, e2, rdV_eq, rdV_eq, hR _ hX v y 1 hone, h1] at this
    simpa [Rd, inner_sum, inner_smul_right] using this.symm

end GlobalTheory.DerOf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankAndDetOfRealBasisSkewPartStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_and_det_of_real_basis_skew_part : ∀ (n : ℕ) (ε : Fin n → Bool) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ N, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N) → LinearIndependent ℝ E → (∀ X, (X ∈ N ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → Module.finrank ℂ N = d ∧ ∀ (φ : N →ₗ[ℂ] N) (L : Matrix (Fin d) (Fin d) ℝ), (∀ (k : Fin d) (h : E k ∈ N), ((φ ⟨E k, h⟩ : N) : Matrix (Fin n) (Fin n) ℂ) = ∑ i, L i k • E i) → LinearMap.det φ = ((L.det : ℝ) : ℂ) := by
  first | exact @GlobalTheory.RealFormBasis.finrank_and_det | exact GlobalTheory.RealFormBasis.finrank_and_det | (intros; apply GlobalTheory.RealFormBasis.finrank_and_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableAndNormAmplitudeLeOfPairingsStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_and_norm_amplitude_le_of_pairings : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ν : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c K : ℝ), γ ∈ GG k r → ν {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → 0 < c → 0 ≤ K → (∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (‖⟪v, Φ (γ * Matrix.of x)⟫_ℂ‖ * ‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖) ∂ν ≤ ENNReal.ofReal K) → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) ν ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ ν c Φ Φ' γ)‖ ≤ K / c := by
  first | exact @GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le | exact GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le | (intros; apply GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le <;> assumption)
end

