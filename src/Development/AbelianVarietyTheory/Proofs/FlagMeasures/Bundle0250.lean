module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Formalism.PeriodIntegrals.Bundle0016
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CmStarOfIsCMUnram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapPairingBound
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DatumOfPeriods

section

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma dsigW_eq (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v = PI.UpqRep.dsigW (k := k) (r := r) σ w v := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show Formalism.MainNotions.S.dsig σ X (Formalism.MainNotions.S.dsigW σ w v) = PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ w v)
    rw [ih]; rfl

lemma isBesselMapSm_smul {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {l : H → Wp}
    (h : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π l) (a : ℂ) :
    Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun v => a • l v) := by
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun g hg m hm v hv => ?_, ‖a‖ * C, Ws, h4, fun v hv => ?_⟩
  · simp only [h1 v hv w hw, smul_add]
  · simp only [h2 c v hv]; rw [smul_comm]
  · simp only [h3 g hg m hm v hv, map_smul]; rw [smul_comm]
  · simp only [dsigW_eq, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h5 v hv) (norm_nonneg _)

lemma l2SG_sqrt_smul_eq_ofReal_mul {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (n : ℕ) (c : ℝ)
    (h : l2SG ν F = ENNReal.ofReal c) :
    l2SG ν (fun g => ((Real.sqrt n : ℝ) : ℂ) • F g) = ENNReal.ofReal (c * n) := by
  have e : ∀ y : Wp, ((‖((Real.sqrt n : ℝ) : ℂ) • y‖₊ : ℝ≥0∞)) ^ 2 = (n : ℝ≥0∞) * (‖y‖₊ : ℝ≥0∞) ^ 2 := by
    intro y
    have : ‖((Real.sqrt n : ℝ) : ℂ)‖₊ ^ 2 = (n : NNReal) := by
      apply NNReal.eq
      simp [Real.sq_sqrt, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [nnnorm_smul, ENNReal.coe_mul, mul_pow, ← ENNReal.coe_pow, this, ENNReal.coe_natCast]
  unfold l2SG at h ⊢
  simp only [e]
  rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n), h, mul_comm c, ENNReal.ofReal_mul (Nat.cast_nonneg n),
    ENNReal.ofReal_natCast]

end

theorem exists_goodS : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDS (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  intro hH D τ w w' θ W lam R _ l l' dd _ _ hR hl hl' hdd hn hn'
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨P, hP, hD⟩ := hR.2
  have hD' : Formalism.MainNotions.S.IsDS (epsSH D.R) lam (fun g => R.σ (P⁻¹ * g * P)) := hD
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ _ _ _ _ hD' _ (D.s.cdScale_pos _ (epsSH D.R))
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hD'
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hvs : v ∈ R.sm :=
    ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK _ _ _ lam R hR P hP S hS.1 hS.2.1).1 v hvS).2
  refine ⟨{ H := R.H, σ := R.σ, B := fun x => ((Real.sqrt (Module.finrank ℂ W.Wp : ℕ) : ℝ) : ℂ) • l x,
            B' := fun x => ((Real.sqrt (Module.finrank ℂ W.Wq : ℕ) : ℝ) : ℂ) • l' x,
            v0 := v, cN := ‖v‖ ^ 2 / dd, deg := d },
    hR.1, hR.2, isBesselMapSm_smul hl _, isBesselMapSm_smul hl' _, hvs, hv0, ⟨P, hP, ?_⟩,
    div_pos (pow_pos (norm_pos_iff.2 hv0) 2) hdd, l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn v hvs),
    l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn' v hvs), P, hP.1, hd⟩
  exact (le_sSup (s := {S | IsKTypeOf (epsSH D.R) (fun g => R.σ (P⁻¹ * g * P)) (Formalism.QuantumDeterminants.lowK (epsSH D.R) lam) S}) hS) hvS

end GlobalTheory.DatumOfPeriods
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliDiscreteSeriesInfChar
section
namespace GlobalTheory

theorem capelliDiscreteSeriesInfChar : PI.DSInfCharCap.DSInfCharCap :=
  CompanionTheory.D.DSIC.discrete_series_infinitesimal_character

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliTransportUnitaryConj
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

private theorem list_prod_ofFn_sum_eq_sum_prod {A : Type*} [Semiring A] {ι : Type*} [Fintype ι] :
    ∀ {t : ℕ} (f : Fin t → ι → A),
      (List.ofFn fun k => ∑ i, f k i).prod = ∑ c : Fin t → ι, (List.ofFn fun k => f k (c k)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, list_prod_ofFn_sum_eq_sum_prod (fun k => f k.succ), Finset.sum_mul_sum,
      ← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
    simp [Fin.consEquiv, List.ofFn_succ]

private theorem list_prod_ofFn_smul_eq_prod_smul {A : Type*} [Semiring A] [Algebra ℂ A] :
    ∀ {t : ℕ} (r : Fin t → ℂ) (x : Fin t → A),
      (List.ofFn fun k => r k • x k).prod = (∏ k, r k) • (List.ofFn x).prod
  | 0, r, x => by simp
  | t + 1, r, x => by
    rw [List.ofFn_succ, List.prod_cons, list_prod_ofFn_smul_eq_prod_smul (fun k => r k.succ) (fun k => x k.succ),
      smul_mul_smul_comm, Fin.prod_univ_succ, List.ofFn_succ (f := x), List.prod_cons]

private theorem Tm_conj_eq_sum_conj_Tm {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (v : ℂ) (a b : Fin n) :
    Formalism.REAL.Tm (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) v a b =
      ∑ c, ∑ d, (P c a * Q b d) • Formalism.REAL.Tm E v c d := by
  have h1 : ∑ c, P c a * Q b c = if a = b then 1 else 0 := by
    have := congrFun (congrFun hQP b) a
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [show (∑ c, P c a * Q b c) = ∑ c, Q b c * P c a from
      Finset.sum_congr rfl fun c _ => mul_comm _ _, this]
    by_cases h : a = b <;> simp [h, eq_comm]
  simp only [Formalism.REAL.Tm, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  congr 1
  rw [← Finset.sum_smul, h1]
  by_cases h : a = b <;> simp [h]

private theorem sum_sign_mul_prod_eq_zero_of_not_bijective {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (r : Fin n → Fin n)
    (hr : ¬ Function.Bijective r) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (r k) (σ k) = 0 := by
  have := Matrix.det_mul_aux (M := Pᵀ) (N := Matrix.of fun _ _ => (1 : ℂ)) hr
  simpa [Matrix.transpose_apply] using this

private theorem sum_sign_mul_prod_perm_eq_sign_mul_det {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (τ : Equiv.Perm (Fin n)) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (τ k) (σ k) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) * Matrix.det P := by
  rw [← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
  conv_lhs => rw [← Equiv.sum_comp (Equiv.mulRight τ)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, Equiv.Perm.coe_mul,
    Function.comp_apply, Matrix.transpose_apply]
  rw [show (∏ k, P (τ k) (ρ (τ k))) = ∏ j, P j (ρ j) from Equiv.prod_comp τ (fun j => P j (ρ j))]
  ring

private theorem sum_fun_eq_sum_perm_of_eq_zero_of_not_bijective {M : Type*} [AddCommMonoid M] {n : ℕ} (g : (Fin n → Fin n) → M)
    (h : ∀ r, ¬ Function.Bijective r → g r = 0) :
    ∑ r, g r = ∑ τ : Equiv.Perm (Fin n), g τ := by
  let e : Equiv.Perm (Fin n) ↪ (Fin n → Fin n) := ⟨fun τ => τ, DFunLike.coe_injective⟩
  rw [show (∑ τ : Equiv.Perm (Fin n), g τ) = ∑ r ∈ Finset.univ.map e, g r from
    (Finset.sum_map Finset.univ e g).symm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro r _ hr
  apply h r
  intro hb
  exact hr (Finset.mem_map.2 ⟨Equiv.ofBijective r hb, Finset.mem_univ _, rfl⟩)

private theorem qminor_eq_zero_of_not_bijective {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (u : ℂ) (s : Fin n → Fin n) (hs : ¬ Function.Bijective s) :
    Formalism.REAL.qminor E id s u = 0 := by
  have hni : ¬ Function.Injective s := fun hi => hs (Finite.injective_iff_bijective.mp hi)
  obtain ⟨p, q, hsq, hpq⟩ : ∃ p q, s p = s q ∧ p ≠ q := by
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨p, q, h1, h2⟩ := hni
    exact ⟨p, q, h1, h2⟩
  have hsw : s ∘ Equiv.swap p q = s := by
    funext i
    simp only [Function.comp_apply]
    rcases eq_or_ne i p with rfl | hip
    · simp [hsq]
    rcases eq_or_ne i q with rfl | hiq
    · simp [hsq]
    · rw [Equiv.swap_apply_of_ne_of_ne hip hiq]
  have h := Formalism.REAL.qSkewCol A n n E hE id s (Equiv.swap p q) u
  rw [hsw, Equiv.Perm.sign_swap hpq] at h
  set x := Formalism.REAL.qminor E id s u
  have h2 : x + x = 0 := by
    nth_rewrite 2 [h]
    simp
  calc x = (1 / 2 : ℂ) • (x + x) := by rw [← two_smul ℂ x, smul_smul]; norm_num
    _ = 0 := by rw [h2, smul_zero]

private theorem qdet_conj_eq_qdet_of_mul_eq_one {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (u : ℂ) :
    Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u = Formalism.REAL.qdet E u := by
  classical
  have hsg : ∀ (z : ℤ) (x : A), (z : A) * x = (z : ℂ) • x := fun z x => by
    rw [Algebra.smul_def, map_intCast]
  have ha : ∀ σ : Equiv.Perm (Fin n),
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d)
        (u - (k : ℂ)) (id (σ k)) (id k)).prod =
        ∑ r : Fin n → Fin n, ∑ s : Fin n → Fin n, (∏ k, (P (r k) (σ k) * Q k (s k))) •
          (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k)).prod := by
    intro σ
    simp only [id, Tm_conj_eq_sum_conj_Tm E P Q hQP]
    rw [list_prod_ofFn_sum_eq_sum_prod (fun k c => ∑ d, (P c (σ k) * Q k d) • Formalism.REAL.Tm E (u - (k : ℂ)) c d)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [list_prod_ofFn_sum_eq_sum_prod (fun k d => (P (r k) (σ k) * Q k d) • Formalism.REAL.Tm E (u - (k : ℂ)) (r k) d)]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact list_prod_ofFn_smul_eq_prod_smul (fun k => P (r k) (σ k) * Q k (s k))
      (fun k => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k))
  have hq : ∀ s : Fin n → Fin n, Formalism.REAL.qminor E id s u =
      ∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : ℂ) •
        (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (τ k) (s k)).prod := by
    intro s
    unfold Formalism.REAL.qminor
    exact Finset.sum_congr rfl fun τ _ => hsg _ _
  have hs : ∀ s : Fin n → Fin n,
      ∑ r : Fin n → Fin n, (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, (P (r k) (σ k) * Q k (s k))) •
          (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k)).prod =
        (∏ k, Q k (s k)) • (Matrix.det P • Formalism.REAL.qminor E id s u) := by
    intro s
    have hD : ∀ r : Fin n → Fin n, (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, (P (r k) (σ k) * Q k (s k))) =
          (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (r k) (σ k)) *
            ∏ k, Q k (s k) := by
      intro r
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun σ _ => by rw [Finset.prod_mul_distrib, mul_assoc]
    simp_rw [hD]
    rw [sum_fun_eq_sum_perm_of_eq_zero_of_not_bijective _ (fun r hr => by rw [sum_sign_mul_prod_eq_zero_of_not_bijective P r hr, zero_mul, zero_smul])]
    simp_rw [sum_sign_mul_prod_perm_eq_sign_mul_det P]
    rw [hq s, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hL : Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u =
      ∑ s : Fin n → Fin n, (∏ k, Q k (s k)) • (Matrix.det P • Formalism.REAL.qminor E id s u) := by
    have step : Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u =
        ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) *
          ∑ r : Fin n → Fin n, ∑ s : Fin n → Fin n, (∏ k, (P (r k) (σ k) * Q k (s k))) •
            (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k)).prod := by
      unfold Formalism.REAL.qdet Formalism.REAL.qminor
      exact Finset.sum_congr rfl fun σ _ => by rw [ha σ]
    rw [step]
    simp_rw [← hs]
    simp only [Finset.sum_smul, Finset.mul_sum, Finset.smul_sum, hsg, smul_smul]
    first
      | exact Finset.sum_comm
      | exact Eq.trans Finset.sum_comm (Finset.sum_congr rfl fun r _ => Finset.sum_comm)
      | exact Eq.trans Finset.sum_comm (Eq.trans (Finset.sum_congr rfl fun r _ => Finset.sum_comm) Finset.sum_comm)
  have hperm : ∀ τ : Equiv.Perm (Fin n),
      Formalism.REAL.qminor E id τ u = ((Equiv.Perm.sign τ : ℤ) : ℂ) • Formalism.REAL.qdet E u := by
    intro τ
    have h := Formalism.REAL.qSkewCol A n n E hE id id τ u
    rw [hsg] at h
    exact h
  have hdetQ : ∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, Q k (τ k) =
      Matrix.det Q := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  have hscal : ∑ τ : Equiv.Perm (Fin n), (∏ k, Q k (τ k)) *
      (Matrix.det P * ((Equiv.Perm.sign τ : ℤ) : ℂ)) = 1 := by
    rw [show (1 : ℂ) = Matrix.det P * Matrix.det Q by rw [← Matrix.det_mul, hPQ, Matrix.det_one],
      ← hdetQ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [hL, sum_fun_eq_sum_perm_of_eq_zero_of_not_bijective _ (fun s hs => by rw [qminor_eq_zero_of_not_bijective E hE u s hs, smul_zero, smul_zero])]
  simp_rw [hperm, smul_smul]
  rw [← Finset.sum_smul, hscal, one_smul]

theorem capelli_transport_conj : PI.UnitaryGroupMassFormula.CapelliEig.CapTransport := by
  intro n ε E _ _ H P Q F u g hQP hPQ hH hF hg
  have hx : Formalism.REAL.inUJ ε (P * g * Q) := Formalism.QuantumDeterminants.ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x₀, hx₀⟩ := Formalism.QuantumDeterminants.io_rep_mk (ε := ε) (E := E) hF
  have hA := Formalism.QuantumDeterminants.ioh_qminor_rep (Formalism.QuantumDeterminants.ioh_repr (ε := ε) (E := E) P Q) id id u hx₀
  have hB := Formalism.QuantumDeterminants.io_qminor_rep (ε := ε) id id u hx₀
  have hkey : Formalism.REAL.qminor (Formalism.QuantumDeterminants.iohE ε E P Q) id id u =
      Formalism.REAL.qminor (Formalism.QuantumDeterminants.ioE ε E) id id u :=
    qdet_conj_eq_qdet_of_mul_eq_one (Formalism.QuantumDeterminants.ioE ε E) (Formalism.QuantumDeterminants.io_gl ε E) P Q hQP hPQ u
  have h1 := Formalism.QuantumDeterminants.ioh_qminor ε H P Q hQP hPQ hH (id : Fin n → Fin n) id u F g
  show Formalism.QuantumDeterminants.qminorOp (Formalism.QuantumDeterminants.EabH H) id id u F g =
    Formalism.QuantumDeterminants.qminorOp (Formalism.REAL.EabV ε) id id u (fun x => F (Q * x * P)) (P * g * Q)
  rw [h1, hA _ hx, hB _ hx, hkey]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLeOfDiag
section
open NumberField Formalism.BasicNotions

namespace GlobalTheory.SA.AmbSig

open Matrix Module

theorem card_le_of_diag {p q d : ℕ} (N : Matrix (Fin p ⊕ Fin q) (Fin d) ℂ) (δ : Fin d → ℂ)
    (hδ : ∀ j, (δ j).re ≤ 0) (hN : Nᴴ * Formalism.UG.Jpq p q * N = diagonal δ)
    (hinj : ∀ c, N *ᵥ c = 0 → c = 0) : d ≤ q := by
  classical

  let f : (Fin d → ℂ) →ₗ[ℂ] (Fin q → ℂ) :=
    LinearMap.funLeft ℂ ℂ (Sum.inr : Fin q → Fin p ⊕ Fin q) ∘ₗ Matrix.mulVecLin N
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun c hc => ?_
    set w := N *ᵥ c with hw
    have hr : ∀ i, w (Sum.inr i) = 0 := fun i => congrFun hc i

    have hform : star w ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ w) = star c ⬝ᵥ (diagonal δ *ᵥ c) := by
      rw [← hN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      conv_rhs => rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    have hleft : (star w ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ w)).re = ∑ i, Complex.normSq (w (Sum.inl i)) := by
      unfold Formalism.UG.Jpq
      rw [Matrix.fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type, hr, Complex.mul_re, Complex.normSq_apply]
    have hright : (star c ⬝ᵥ (diagonal δ *ᵥ c)).re = ∑ j, (δ j).re * Complex.normSq (c j) := by
      simp only [dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.normSq_apply]
      ring
    have hnn : ∀ i, 0 ≤ Complex.normSq (w (Sum.inl i)) := fun i => Complex.normSq_nonneg _
    have hsum : ∑ i, Complex.normSq (w (Sum.inl i)) ≤ 0 := by
      rw [← hleft, hform, hright]
      exact Finset.sum_nonpos fun j _ =>
        mul_nonpos_of_nonpos_of_nonneg (hδ j) (Complex.normSq_nonneg _)
    have hl : ∀ i, w (Sum.inl i) = 0 := fun i =>
      Complex.normSq_eq_zero.1 (le_antisymm
        ((Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)).trans hsum) (hnn i))
    apply hinj
    funext x
    cases x with
    | inl i => exact hl i
    | inr i => exact hr i
  simpa using LinearMap.finrank_le_finrank_of_injective hf

theorem hT_eq_sum {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ b, (∑ a, star (S.frame.repr x a) * S.gram a b) * S.frame.repr y b := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  simp only [HSpace.gram]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem amb_of_sig : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (k r : ℕ),
    GlobalTheory.SA.CMStar E → S.SigOK → (∀ τ : E →+* ℂ, S.sig τ = (k + r, r + 1)) → GlobalTheory.SA.Amb S k r := by
  intro E _ _ _ S k r hcm hok hsig

  have hfac : ∀ τ : E →+* ℂ, S.rank = k + r + (r + 1) ∧
      ∃ A : Matrix (Fin (k + r) ⊕ Fin (r + 1)) (Fin S.rank) ℂ,
        Aᴴ * Formalism.UG.Jpq (k + r) (r + 1) * A = S.gram.map τ ∧
        ∃ B : Matrix (Fin S.rank) (Fin (k + r) ⊕ Fin (r + 1)) ℂ, B * A = 1 := by
    intro τ
    have h := hok τ
    rw [hsig τ] at h
    obtain ⟨h1, ⟨A, hA⟩, h3⟩ :=
      GlobalTheory.Mem.SignatureFactor.exists_factor S.rank (k + r) (r + 1) _ h
    obtain ⟨B, -, hBA⟩ := h3 A hA
    exact ⟨h1.symm, A, hA, B, hBA⟩
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine ⟨hcm, ?_, ?_⟩
  · rw [S.rank_eq, (hfac τ₀).1]
    ring
  · intro τ U hU
    classical
    obtain ⟨-, A, hA, B, hBA⟩ := hfac τ

    let F : U →ₗ[E] U →ₛₗ[starRingEnd E] E := S.hT.flip.domRestrict₁₂ U U
    have hF : ∀ x y, starRingEnd E (F x y) = F y x := fun x y => S.herm.eq (y : S.V) (x : S.V)
    obtain ⟨u, hu⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin (E := E) (c := starRingEnd E)
      two_ne_zero (Module.finrank E U) F hF rfl

    let v : Fin (Module.finrank E U) → Fin S.rank → E := fun j => S.frame.repr (u j : S.V)
    have hv : LinearIndependent E v := by
      have hker : LinearMap.ker (S.frame.equivFun.toLinearMap ∘ₗ U.subtype) = ⊥ :=
        LinearMap.ker_eq_bot.2 (S.frame.equivFun.injective.comp Subtype.val_injective)
      exact u.linearIndependent.map' _ hker
    letI : Algebra E ℂ := τ.toAlgebra
    haveI : FaithfulSMul E ℂ := (faithfulSMul_iff_algebraMap_injective E ℂ).2 τ.injective
    have hvC : LinearIndependent ℂ (fun j => algebraMap E ℂ ∘ v j) :=
      linearIndependent_algebraMap_comp_iff.2 hv
    let C : Matrix (Fin S.rank) (Fin (Module.finrank E U)) ℂ := Matrix.of fun a j => τ (v j a)
    refine card_le_of_diag (A * C) (fun j => τ (S.hT (u j : S.V) (u j : S.V)))
      (fun j => hU _ (u j).2) ?_ ?_
    · have hsplit : (A * C)ᴴ * Formalism.UG.Jpq (k + r) (r + 1) * (A * C) =
          Cᴴ * (Aᴴ * Formalism.UG.Jpq (k + r) (r + 1) * A) * C := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [hsplit, hA]
      ext i j
      have hij : τ (S.hT (u i : S.V) (u j : S.V)) = (Cᴴ * S.gram.map τ * C) i j := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hT_eq_sum, map_sum, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_mul, map_sum, Matrix.mul_apply]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        simp [C, v, hcm τ]
      rw [← hij, Matrix.diagonal_apply]
      split_ifs with h
      · rw [h]
      · have h0 : F (u j) (u i) = 0 := hu j i (Ne.symm h)
        simp only [F, LinearMap.domRestrict₁₂_apply, LinearMap.flip_apply] at h0
        rw [h0, map_zero]
    · intro c hc
      have hCc : C *ᵥ c = 0 := by
        rw [← Matrix.mulVec_mulVec] at hc
        rw [← Matrix.one_mulVec (C *ᵥ c), ← hBA, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
      have hlin := Fintype.linearIndependent_iff.1 hvC c (by
        rw [← hCc]
        funext a
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, C, mul_comm, RingHom.algebraMap_toAlgebra])
      funext j
      exact hlin j

end GlobalTheory.SA.AmbSig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FourMulAddFiveLeRank
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.CmHermitianRankFrames

theorem four_mul_add_five_le_rank (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    4 * D.R.rS + 5 ≤ X.B.I.n := by

  rw [X.n_eq]
  have hk := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

theorem cm_herm_rank_frames : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig ∧ IsHermND X.B.I.cm.sig X.B.I.J ∧ 4 * D.R.rS + 5 ≤ X.B.I.n ∧ ∀ u, ∃ T : X.B.I.F, (Formalism.L2.SG.TypedSets.frameOf X u).IsStd X.B.I.cm.sig X.B.I.J T :=
  fun D X => ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, four_mul_add_five_le_rank D X,
    fun u => MassDataLevelSSteps.frameStd_holds X u⟩

end GlobalTheory.CmHermitianRankFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FractionalIdealBasisTransportMeasurePreservingStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving : ∀ (K : Type) [Field K] [NumberField K] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure W) (e : mixedEmbedding.mixedSpace K ≃L[ℝ] W), MeasurePreserving e volume μ → ∀ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ W), (Submodule.span ℤ (Set.range b) : Set W) = (fun x : K => e (mixedEmbedding K x)) '' {x : K | x ∈ (J : FractionalIdeal (𝓞 K)⁰ K)} ∧ μ (ZSpan.fundamentalDomain b) = ENNReal.ofReal (FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) * (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) := by
  first | exact @GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport | exact GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport | (intros; apply GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory

theorem haarLie_isHaarOn_Nset : ∀ (k r : ℕ) (κ : ENNReal), 0 < κ → κ < ⊤ →
    IsHaarOn (Nset k r) (haarLie (Nset k r) κ) :=
  fun k r κ h0 h1 => Formalism.MainNotions.BridgeCSB.haarLieN k r κ h0.ne' h1.ne

end GlobalTheory
end

