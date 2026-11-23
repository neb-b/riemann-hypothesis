module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Formalism.PieriBlockIdeals.LemmaWFromLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvSectionMulEntriesNearOne
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.SUVol

theorem conj_inv_section_mul_entries_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm), IsOrth X x → σ 0 = 1 → ContinuousAt σ 0 → ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ z : V (nd X), ‖z‖ < κ → ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∀ τ a b, ‖((mat x τ)⁻¹ * (((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ) a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < η := by
  intro E _ _ _ r X x σ hx hσ0 hσc η hη
  classical
  let One : X.Ψ → Fin r → Fin r → ℂ := fun _ a b => (1 : Matrix (Fin r) (Fin r) ℂ) a b
  let F : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) → (X.Ψ → Fin r → Fin r → ℂ) :=
    fun PQ τ => (mat x τ)⁻¹ * (Matrix.of (PQ.1 τ) * Matrix.of (PQ.2 τ)) * mat x τ
  have hFc : Continuous F := by
    refine continuous_pi fun τ => ?_
    have h1 : Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) =>
        Matrix.of (PQ.1 τ) :=
      (continuous_apply τ).comp continuous_fst
    have h2 : Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) =>
        Matrix.of (PQ.2 τ) :=
      (continuous_apply τ).comp continuous_snd
    show Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) =>
      (mat x τ)⁻¹ * (Matrix.of (PQ.1 τ) * Matrix.of (PQ.2 τ)) * mat x τ
    exact (continuous_const.matrix_mul (h1.matrix_mul h2)).matrix_mul continuous_const
  have hF1 : F (One, One) = One := by
    funext τ
    have hu : IsUnit (mat x τ).det :=
      isUnit_iff_ne_zero.mpr (ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.orthogonalFrame_det_ne_zero X x hx τ)
    have h1 : Matrix.of (One τ) = 1 := rfl
    show (mat x τ)⁻¹ * (Matrix.of (One τ) * Matrix.of (One τ)) * mat x τ = Matrix.of (One τ)
    rw [h1, Matrix.mul_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.1 hFc.continuousAt (ε := η) hη
  rw [hF1] at hδF
  let A : V (nd X) → (X.Ψ → Fin r → Fin r → ℂ) := fun z τ =>
    ((((σ z)⁻¹ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)
  have hAc : ContinuousAt A 0 := by
    refine continuousAt_pi.2 fun τ => ?_
    have : ContinuousAt (fun z => (σ z)⁻¹) 0 := ContinuousAt.comp (f := σ) continuous_inv.continuousAt hσc
    exact (Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).continuousAt.comp this
  have hA0 : A 0 = One := by
    funext τ
    simp only [A, One, hσ0, inv_one]
    rfl
  obtain ⟨κ, hκ, hκA⟩ := Metric.continuousAt_iff.1 hAc (ε := δ) hδ
  rw [hA0] at hκA
  refine ⟨δ, hδ, κ, hκ, fun z hz g hg τ a b => ?_⟩
  let B : X.Ψ → Fin r → Fin r → ℂ := fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)
  have hzA : dist (A z) One < δ := hκA (by simpa [dist_zero_right] using hz)
  have hgB : dist B One < δ := by
    refine (dist_pi_lt_iff hδ).2 fun τ => (dist_pi_lt_iff hδ).2 fun a => (dist_pi_lt_iff hδ).2 fun b => ?_
    rw [dist_eq_norm]
    exact hg τ a b
  have hPQ : dist (A z, B) (One, One) < δ := by
    rw [Prod.dist_eq]; exact max_lt hzA hgB
  have hout := hδF hPQ
  have hent : dist (F (A z, B) τ a b) (One τ a b) < η :=
    lt_of_le_of_lt ((dist_le_pi_dist _ _ b).trans ((dist_le_pi_dist _ _ a).trans (dist_le_pi_dist _ _ τ))) hout
  rw [dist_eq_norm] at hent
  convert hent using 3
  all_goals rfl

end GlobalTheory.SUVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffExpSub
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

namespace GlobalTheory.WachExp

open PowerSeries

theorem ringHom_gam_X {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L]
    [Algebra ℤ_[l] O] [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] (φ : O⟦X⟧ →+* L⟦X⟧)
    (hφ : ∀ a : O, φ (C a) = C (algebraMap O L a)) (z : L) (hX : φ X = C z * exp L - 1) (hz : z ^ l = 1)
    (c : ℤ_[l]) (hc : (l : ℤ_[l]) ∣ c - 1) :
    φ (GlobalTheory.Fon.gam O c X) = C z * rescale (algebraMap ℤ_[l] L c) (exp L) - 1 := by
  let f : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
    { toRingHom := φ
      commutes' := fun a => (congrArg φ (PowerSeries.algebraMap_apply (R := O) (A := O))).trans
        ((hφ a).trans (PowerSeries.algebraMap_apply (R := O) (A := L)).symm) }
  have h := GlobalTheory.HWL.Ser.map_gam_X f z hX 1 1 (by rw [pow_one]; exact hz) c (by simpa using hc)
  rw [pow_one] at h
  exact h

end GlobalTheory.WachExp

namespace GlobalTheory.WachExp

open PowerSeries

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

theorem norm_root_sub_one_lt {z : ↥LL.1} (hz : z ^ l = 1) : ‖(((z - 1 : ↥LL.1)) : Om l)‖ < 1 := by
  have h : ((z : Om l)) ^ l ^ 1 = 1 := by
    rw [pow_one]; exact_mod_cast congrArg (fun y : ↥LL.1 => (y : Om l)) hz
  have := GlobalTheory.HWL.Ser.norm_sub_one_lt h
  push_cast
  exact this

theorem constantCoeff_exp_sub (z a : ↥LL.1) :
    constantCoeff (C z * rescale a (exp ↥LL.1) - 1) = z - 1 := by
  rw [map_sub, map_mul, GlobalTheory.HWL.Ser.constantCoeff_rescale_exp, constantCoeff_C, mul_one, map_one]

theorem ev_unique (x : PowerSeries ↥LL.1) (hx : ‖((constantCoeff x : ↥LL.1) : Om l)‖ < 1)
    (φ ψ : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1)
    (hφ : ∀ a : ↥(OL LL), φ (C a) = C (a : ↥LL.1)) (hψ : ∀ a : ↥(OL LL), ψ (C a) = C (a : ↥LL.1))
    (hφX : φ X = x) (hψX : ψ X = x) : φ = ψ := by
  let φ' : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1 :=
    { toRingHom := φ, commutes' := fun a => by change φ (C a) = C (a : ↥LL.1); exact hφ a }
  let ψ' : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1 :=
    { toRingHom := ψ, commutes' := fun a => by change ψ (C a) = C (a : ↥LL.1); exact hψ a }
  have h := (GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL x hx).1.unique (y₁ := φ') (y₂ := ψ') hφX hψX
  exact RingHom.ext fun f => AlgHom.congr_fun h f

theorem exists_ev (z : ↥LL.1) (hz : z ^ l = 1) :
    ∃ φ : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1,
      (∀ a : ↥(OL LL), φ (C a) = C (a : ↥LL.1)) ∧ φ X = C z * exp ↥LL.1 - 1 := by
  have h := GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL (C z * rescale 1 (exp ↥LL.1) - 1)
    (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL hz)
  obtain ⟨ev, hev, -⟩ := h.1
  refine ⟨ev.toRingHom, fun a => ?_, by
    change ev X = _
    rw [hev, rescale_one, RingHom.id_apply]⟩
  have := ev.commutes a
  exact this

theorem rescale_C' (r z : ↥LL.1) : rescale r (C z) = C z := by
  ext n
  by_cases h : n = 0 <;> simp [coeff_rescale, coeff_C, h]

end GlobalTheory.WachExp

namespace GlobalTheory.WachExp

open PowerSeries

end GlobalTheory.WachExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfZero
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace Katz
namespace WittHaus

theorem constantCoeff_subst_of_zero' {σ τ R : Type} [CommRing R] {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (ha' : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have h1 := constantCoeff_subst_eq_zero ha ha' (f := f - C (constantCoeff f)) (by simp)
  have h2 : subst a (C (constantCoeff f) : MvPowerSeries σ R) = C (constantCoeff f) := by
    rw [← coe_substAlgHom ha]
    exact (substAlgHom ha).commutes (constantCoeff f)
  rw [← coe_substAlgHom ha, map_sub, coe_substAlgHom ha, h2, map_sub, constantCoeff_C] at h1
  exact sub_eq_zero.mp h1

theorem isUnit_natCast_of_not_dvd (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (u : ℕ)
    (hu : ¬ p ∣ u) : IsUnit (u : WittVector p k) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  intro h0
  have : (WittVector.constantCoeff (u : WittVector p k)) = 0 := h0
  rw [map_natCast, CharP.cast_eq_zero_iff k p] at this
  exact hu this

theorem constantCoeff_int (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) {f : MvPowerSeries (Fin d) (Fr p k)}
    (hf : f ∈ quasiLog p h) :
    ∃ w : WittVector p k, coeff 0 f = algebraMap _ (Fr p k) w := by
  obtain ⟨w, hw⟩ := hf.2 0
  have hμ : HasSubst (fun i => lift p (μ i)) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_lift p (h.const i)
  have hX : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hc : coeff 0 (cob1 (fun i => lift p (μ i)) f) = - coeff 0 f := by
    simp only [coeff_zero_eq_constantCoeff_apply]
    unfold cob1 inL inR
    rw [map_sub, map_sub, constantCoeff_subst_of_zero' hμ (fun i => constantCoeff_lift p (h.const i)),
      constantCoeff_subst_of_zero' hX (fun _ => constantCoeff_X _),
      constantCoeff_subst_of_zero' hY (fun _ => constantCoeff_X _)]
    ring
  refine ⟨-(1 * w), ?_⟩
  rw [map_neg, ← hw, hc, neg_neg]

theorem haus : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ),
    IsHausdorff (Ideal.span {(p : WittVector p k)}) (Mod p h) := by
  intro p _ k _ _ _ d μ h
  refine ⟨fun x hx => ?_⟩
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  have key : ∀ n : ℕ, ∃ g : quasiLog p h,
      (f : MvPowerSeries (Fin d) (Fr p k)) - ((p : WittVector p k) ^ n) • (g : MvPowerSeries (Fin d) (Fr p k))
        ∈ intBy p k (Fin d) 1 := by
    intro n
    have h1 := (SModEq.sub_mem.mp (hx n))
    rw [sub_zero, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨b, -, hb⟩ := h1
    induction b using Submodule.Quotient.induction_on with | _ g => ?_
    refine ⟨g, ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_eq_zero] at hb
    rw [Submodule.submoduleOf, Submodule.mem_comap] at hb
    have := neg_mem hb
    simpa [neg_sub] using this
  rw [Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
  intro α
  by_cases hα : α = 0
  · subst hα
    obtain ⟨w, hw⟩ := constantCoeff_int p h f.2
    exact ⟨w, by rw [one_mul]; exact hw⟩
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra! hc
    exact hα (Finsupp.ext hc)
  obtain ⟨v, u, hu, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi p (Nat.Prime.ne_one Fact.out)
  obtain ⟨g, hg⟩ := key v
  obtain ⟨w₁, hw₁⟩ := hg α
  obtain ⟨w₂, hw₂⟩ := g.2.1 α i
  obtain ⟨U, hU⟩ := isUnit_natCast_of_not_dvd p k u hu
  refine ⟨w₁ + ↑U⁻¹ * w₂, ?_⟩
  have hsm : coeff α (((p : WittVector p k) ^ v) • (g : MvPowerSeries (Fin d) (Fr p k))) =
      algebraMap _ (Fr p k) ((p : WittVector p k) ^ v) * coeff α (g : MvPowerSeries (Fin d) (Fr p k)) := by
    rw [← algebraMap_smul (Fr p k), LinearMap.map_smul, smul_eq_mul]
  have hα' : ((α i : ℕ) : Fr p k) = algebraMap _ (Fr p k) ((p : WittVector p k) ^ v) * algebraMap _ (Fr p k) (U : WittVector p k) := by
    rw [hU, ← map_mul, hm]; push_cast; rfl
  rw [map_sub, hsm] at hw₁
  have e2 : algebraMap _ (Fr p k) ((p : WittVector p k) ^ v) * coeff α (g : MvPowerSeries (Fin d) (Fr p k)) =
      algebraMap _ (Fr p k) (↑U⁻¹ * w₂) := by
    rw [map_mul, ← hw₂, hα']
    have : algebraMap _ (Fr p k) (↑U⁻¹ : WittVector p k) * algebraMap _ (Fr p k) (U : WittVector p k) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-(algebraMap _ (Fr p k) ((p : WittVector p k) ^ v) * coeff α (g : MvPowerSeries (Fin d) (Fr p k)))) * this
  rw [one_mul, map_add (f := _), ← e2]
  rw [one_mul] at hw₁
  linear_combination hw₁

end WittHaus
end Katz
end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
section
noncomputable section

open Filter Topology Matrix

namespace GlobalTheory.ClosedMatGroup

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasStrictFDerivAt_ofFn_prod {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ (d : ℕ) (f : Fin d → E → 𝔸) (f' : Fin d → E →L[ℝ] 𝔸) (x : E), (∀ i, f i x = 1) →
    (∀ i, HasStrictFDerivAt (f i) (f' i) x) →
    HasStrictFDerivAt (fun y => (List.ofFn fun i => f i y).prod) (∑ i, f' i) x := by
  intro d
  induction d with
  | zero =>
    intro f f' x _ _
    simpa using (hasStrictFDerivAt_const (1 : 𝔸) x)
  | succ d ih =>
    intro f f' x h1 hd
    have hr := ih (fun i => f i.succ) (fun i => f' i.succ) x (fun i => h1 _) (fun i => hd _)
    have hm := (hd 0).mul' hr
    simp only [List.ofFn_succ, List.prod_cons]
    refine hm.congr_fderiv ?_
    ext1 v
    simp [Fin.sum_univ_succ, h1, add_comm]

theorem exists_left_inv_ofFn_prod {S : Set 𝔸} (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) :
    ∀ (d : ℕ) (Y : Fin d → 𝔸), (∀ i, NormedSpace.exp (-Y i) ∈ S) →
      ∃ Q ∈ S, Q * (List.ofFn fun i => NormedSpace.exp (Y i)).prod = 1 := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  intro d
  induction d with
  | zero => intro Y _; exact ⟨1, h1, by simp⟩
  | succ d ih =>
    intro Y hY
    obtain ⟨Q, hQ, hQe⟩ := ih (fun i => Y i.succ) (fun i => hY _)
    refine ⟨Q * NormedSpace.exp (-Y 0), hm _ hQ _ (hY 0), ?_⟩
    rw [List.ofFn_succ, List.prod_cons]
    have e : NormedSpace.exp (-Y 0) * NormedSpace.exp (Y 0) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl (Y 0)).neg_left, neg_add_cancel,
        NormedSpace.exp_zero]
    calc Q * NormedSpace.exp (-Y 0) * (NormedSpace.exp (Y 0) * (List.ofFn fun i => NormedSpace.exp (Y i.succ)).prod)
        = Q * (NormedSpace.exp (-Y 0) * NormedSpace.exp (Y 0)) * (List.ofFn fun i => NormedSpace.exp (Y i.succ)).prod := by
          simp only [mul_assoc]
      _ = 1 := by rw [e, mul_one, hQe]

end Banach

section Banach2

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem exists_coords_second_kind [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S)
    (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S) :
    ∃ (d : ℕ) (Z : Fin d → 𝔸) (s : 𝔸 → Fin d → ℝ), (∀ i, Z i ∈ lieSub S hc h1 hm) ∧
      Tendsto s (𝓝 1) (𝓝 0) ∧
      ∀ᶠ X in 𝓝 (1 : 𝔸), X ∈ S → X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨W, hW⟩ := (lieSub S hc h1 hm).exists_isCompl
  let L := lieSub S hc h1 hm
  let d := Module.finrank ℝ L
  let bL := Module.finBasis ℝ L
  let Z : Fin d → 𝔸 := fun i => (bL i : 𝔸)
  have hZ : ∀ i, ∀ t : ℝ, NormedSpace.exp (t • Z i) ∈ S := fun i t => (bL i).2 t
  let c : 𝔸 →L[ℝ] (Fin d → ℝ) :=
    LinearMap.toContinuousLinearMap (bL.equivFun.toLinearMap ∘ₗ L.projectionOnto W hW)
  let p : 𝔸 →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap (L.projection W hW)
  have hpc : ∀ z, ∑ i, c z i • Z i = p z := by
    intro z
    show ∑ i, (bL.equivFun (L.projectionOnto W hW z)) i • (bL i : 𝔸) = ((L.projectionOnto W hW z : L) : 𝔸)
    conv_rhs => rw [← bL.sum_equivFun (L.projectionOnto W hW z)]
    rw [Submodule.coe_sum]
    rfl
  have hqW : ∀ z, z - p z ∈ W := fun z => by
    have h := Submodule.projection_add_projection_eq_self hW z
    have e : z - p z = W.projection _ hW.symm z := by
      rw [sub_eq_iff_eq_add']; exact h.symm
    rw [e]; exact Submodule.projection_apply_mem hW.symm z
  let P : 𝔸 → 𝔸 := fun z => (List.ofFn fun i => NormedSpace.exp (c z i • Z i)).prod
  let Φ : 𝔸 → 𝔸 := fun z => P z * NormedSpace.exp (z - p z)
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : 𝔸 →L[ℝ] 𝔸) (0 : 𝔸) := hasStrictFDerivAt_exp_zero
  have hf : ∀ i, HasStrictFDerivAt (fun z => NormedSpace.exp (c z i • Z i))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (((ContinuousLinearMap.proj i).comp c).smulRight (Z i))) 0 := fun i =>
    HasStrictFDerivAt.comp (0 : 𝔸) (g := NormedSpace.exp) (by rw [map_zero, Pi.zero_apply, zero_smul]; exact hexp)
      (((ContinuousLinearMap.proj i).comp c).smulRight (Z i)).hasStrictFDerivAt
  have hP := hasStrictFDerivAt_ofFn_prod d (fun i z => NormedSpace.exp (c z i • Z i)) _ 0
    (fun i => by simp) hf
  have h2 : HasStrictFDerivAt (fun z => NormedSpace.exp (z - p z))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (ContinuousLinearMap.id ℝ 𝔸 - p)) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (f := fun z => z - p z) (by rw [map_zero, sub_zero]; exact hexp)
      (ContinuousLinearMap.id ℝ 𝔸 - p).hasStrictFDerivAt
  have hP0 : P 0 = 1 := by simp [P]
  have h4 : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
    refine (hP.mul' h2).congr_fderiv ?_
    ext1 z
    have e1 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • Z i)).prod = 1 := by simp
    simp [e1, hpc]
  have hΦ0 : Φ 0 = 1 := by
    show P 0 * NormedSpace.exp (0 - p 0) = 1
    rw [hP0, map_zero, sub_zero, NormedSpace.exp_zero, one_mul]
  let Ψ := h4.localInverse Φ _ 0
  have hΨ : Tendsto Ψ (𝓝 1) (𝓝 0) := by
    have h := h4.localInverse_tendsto
    rw [hΦ0] at h
    exact h
  have hR : ∀ᶠ X in 𝓝 (1 : 𝔸), Φ (Ψ X) = X := by
    have h := h4.eventually_right_inverse
    rw [hΦ0] at h
    exact h
  have hp0 : Tendsto p (𝓝 0) (𝓝 0) := by simpa using p.continuous.tendsto 0
  have hq0 : Tendsto (fun z => z - p z) (𝓝 0) (𝓝 (0 : 𝔸)) := by
    simpa using (tendsto_id (x := 𝓝 (0 : 𝔸))).sub hp0
  refine ⟨d, Z, fun X => c (Ψ X), fun i => (bL i).2, ?_, ?_⟩
  · have hc0 : Tendsto c (𝓝 0) (𝓝 0) := by simpa using c.continuous.tendsto 0
    exact hc0.comp hΨ
  · filter_upwards [hR, hΨ.eventually (hq0.eventually (eventually_eq_zero hc h1 hm hi hW.disjoint))]
      with X hX1 hX2 hXS
    obtain ⟨Q, hQ, hQe⟩ := exists_left_inv_ofFn_prod h1 hm d (fun i => c (Ψ X) i • Z i)
      (fun i => by rw [← neg_smul]; exact hZ i _)
    have hE : NormedSpace.exp (Ψ X - p (Ψ X)) = Q * X := by
      conv_rhs => rw [← hX1]
      show _ = Q * ((List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)))
      rw [← mul_assoc, hQe, one_mul]
    have hw := hX2 (hqW _) (by rw [hE]; exact hm _ hQ _ hXS)
    calc X = Φ (Ψ X) := hX1.symm
      _ = _ := by
        show (List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)) = _
        rw [hw, NormedSpace.exp_zero, mul_one]

end Banach2

theorem skew_of_exp_smul_mem {m : ℕ} (A Z : Matrix (Fin m) (Fin m) ℂ)
    (hZ : ∀ t : ℝ, NormedSpace.exp (t • Z) ∈ {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}) :
    Zᴴ * A + A * Z = 0 := by
  let _ := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin m) (α := ℂ)
  have _ : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  have e : ∀ t : ℝ, NormedSpace.exp (t • Zᴴ) * A * NormedSpace.exp (t • Z) = A := fun t => by
    have h := hZ t
    simp only [Set.mem_setOf_eq] at h
    rwa [← Matrix.exp_conjTranspose, conjTranspose_smul, star_trivial] at h
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A * NormedSpace.exp (t • Z))
      (Zᴴ * A + A * Z) 0 := by
    have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) Zᴴ (0 : ℝ)).mul_const A
    have h2 := h1.mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ))
    simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h2
    exact h2
  have hc : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A * NormedSpace.exp (t • Z)) 0 0 := by
    have h : (fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A * NormedSpace.exp (t • Z)) = fun _ => A :=
      funext e
    rw [h]; exact hasDerivAt_const 0 A
  exact hd.unique hc

theorem coords_second_kind_unitary : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), ∃ (d : ℕ)
    (Z : Fin d → Matrix (Fin m) (Fin m) ℂ) (s : Matrix (Fin m) (Fin m) ℂ → Fin d → ℝ),
    (∀ i, (Z i)ᴴ * A + A * Z i = 0) ∧
    Tendsto s (𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1) (𝓝 0) ∧
    ∀ᶠ X in 𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1,
      X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  intro m A
  let S := {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}
  have hc : IsClosed S :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ S := by simp [S]
  have hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    intro a ha b hb
    simp only [S, Set.mem_setOf_eq] at ha hb ⊢
    rw [conjTranspose_mul]
    calc bᴴ * aᴴ * A * (a * b) = bᴴ * (aᴴ * A * a) * b := by simp only [Matrix.mul_assoc]
      _ = A := by rw [ha, hb]
  have hi : ∀ Z : Matrix (Fin m) (Fin m) ℂ, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S := by
    intro Z hZ
    simp only [S, Set.mem_setOf_eq] at hZ ⊢
    have hXY : NormedSpace.exp Z * NormedSpace.exp (-Z) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_right, add_neg_cancel,
        NormedSpace.exp_zero]
    calc (NormedSpace.exp (-Z))ᴴ * A * NormedSpace.exp (-Z)
        = (NormedSpace.exp (-Z))ᴴ * ((NormedSpace.exp Z)ᴴ * A * NormedSpace.exp Z) * NormedSpace.exp (-Z) := by
          rw [hZ]
      _ = (NormedSpace.exp Z * NormedSpace.exp (-Z))ᴴ * A * (NormedSpace.exp Z * NormedSpace.exp (-Z)) := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = A := by rw [hXY]; simp
  let _ := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin m) (α := ℂ)
  have _ : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  obtain ⟨d, Z, s, hZ, hs, hev⟩ := exists_coords_second_kind hc h1 hm hi
  exact ⟨d, Z, s, fun i => skew_of_exp_smul_mem A (Z i) (hZ i), hs.mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_iff.2 hev⟩

end GlobalTheory.ClosedMatGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueToLocallyDirectedColimitOfBasisStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_to_locallyDirected_colimit_of_basis : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens) (F : 𝒰 ⥤ Scheme.{0}) [∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected] (X : Scheme.{0}) (G : B₀.Opens → X.Opens) (hG : Monotone G), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ G U → x ∈ G V → ∃ W ∈ 𝒰, x ∈ G W ∧ W ≤ U ∧ W ≤ V) → (∀ x : X, ∃ U ∈ 𝒰, x ∈ G U) → ∀ (e : ∀ U : 𝒰, (G U.1).toScheme ⟶ F.obj U), (∀ {U V : 𝒰} (h : U.1 ≤ V.1), X.homOfLE (hG h) ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → ∃ j : X ⟶ colimit F, ∀ U : 𝒰, (G U.1).ι ≫ j = e U ≫ colimit.ι F U := by
  first | exact @GlobalTheory.ColimitGlue.exists_glue | exact GlobalTheory.ColimitGlue.exists_glue | (intros; apply GlobalTheory.ColimitGlue.exists_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandPushoutGoodBasicOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ferrand_pushout_good_basic_open : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂], ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U), Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a) ∈ GlobalTheory.FerrandPush.good i₁ i₂ := by
  first | exact @GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good | exact GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good | (intros; apply GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good; all_goals assumption)
end

