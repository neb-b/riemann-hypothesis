module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionClosedDiscBreuilKisin
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionBreuilKisinHom
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem breuilKisinDatum_radius_pow_degree_eq_inv {K : FinExt l} (bk : BK K) : bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have he : (bk.Ep.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2 bk.deg_pos.ne'
  unfold BK.ρ₀
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he, NNReal.rpow_neg_one]

theorem breuilKisinDatum_radius_le_one {K : FinExt l} (bk : BK K) : bk.ρ₀ ≤ 1 := by
  unfold BK.ρ₀
  exact NNReal.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hl.out.one_lt.le)
    (neg_nonpos.2 (by positivity))

theorem breuilKisinDatum_radius_pos {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ := by
  unfold BK.ρ₀
  exact NNReal.rpow_pos (by exact_mod_cast hl.out.pos)

theorem inv_le_rho {K : FinExt l} (bk : BK K) {ρ : ℝ≥0} (h : bk.ρ₀ ≤ ρ) : (l : ℝ≥0)⁻¹ ≤ ρ := by
  rw [← breuilKisinDatum_radius_pow_degree_eq_inv]
  exact (pow_le_of_le_one (by positivity) (breuilKisinDatum_radius_le_one bk) bk.deg_pos.ne').trans h

theorem E_eq {K : FinExt l} (bk : BK K) : ∃ q : bk.S, bk.E = X ^ bk.Ep.natDegree + (l : bk.S) * q := by
  have hm : bk.Ep - Polynomial.X ^ bk.Ep.natDegree ∈ (Ideal.span {(l : Wq l bk.a)}).map Polynomial.C := by
    rw [Ideal.mem_map_C_iff]
    intro n
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy n bk.Ep.natDegree with hn | hn | hn
    · rw [if_neg hn.ne, sub_zero]
      exact Ideal.mem_span_singleton.2 (bk.dvd_coeff n hn)
    · subst hn
      rw [if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact zero_mem _
    · rw [if_neg hn.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hn, sub_zero]; exact zero_mem _
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hm
  obtain ⟨q, hq⟩ := hm
  refine ⟨(q : bk.S), ?_⟩
  have h1 : bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
    rw [← hq]; ring
  have h2 : (bk.Ep : bk.S) =
      ((Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q : Polynomial (Wq l bk.a)) : bk.S) :=
    congrArg _ h1
  show (bk.Ep : bk.S) = _
  rw [h2, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C, map_natCast]

theorem gauge_mono_le {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (a b : ℕ) {r : ℝ} (hr : 0 < r)
    (h : (ρ : ℝ) ^ b ≤ r * (l : ℝ) ^ a) :
    ‖algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b)‖ ≤ r :=
  gauge_le l u ρ hr (Submodule.subset_span ⟨a, b, 0, by simpa using h, by simp⟩)

end GlobalTheory.BSP.DiscPrism

namespace GlobalTheory.BSP.DiscPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_toDisc_hf_le {K : FinExt l} (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ρ : ℝ≥0)
    (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ ≤ 1) : ‖toDisc l (BK.hf f X) ρ (BK.hf g X)‖ ≤ ρ := by
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.2 ((breuilKisinDatum_radius_pos bk).trans_le h0)
  have hρ1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast h1
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hlρ : (1 : ℝ) ≤ ρ * l := by
    have h := inv_le_rho bk h0
    have h' : ((l : ℝ))⁻¹ ≤ ρ := by exact_mod_cast h
    rw [inv_le_iff_one_le_mul₀ hl0] at h'
    linarith [mul_comm (l : ℝ) ρ]
  set u := BK.hf f X with hu
  let am := algebraMap B.A (PreDisc l u ρ)
  have um : ∀ x y : PreDisc l u ρ, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := gauge_add_le_max l u ρ
  have hX : ‖am u‖ ≤ ρ := by
    simpa using gauge_mono_le (l := l) u ρ 0 1 hρ (by simp)
  have hE : ‖am (BK.hf f bk.E)‖ ≤ ρ := by
    obtain ⟨q, hq⟩ := E_eq bk
    have e1 : BK.hf f bk.E = u ^ bk.Ep.natDegree + (l : B.A) ^ 1 * u ^ 0 * BK.hf f q := by
      rw [hq, map_add (f := _), map_pow, map_mul, map_natCast, hu]; ring
    rw [e1, map_add (f := _), map_mul]
    refine (um _ _).trans (max_le ?_ ?_)
    · have := gauge_mono_le (l := l) u ρ 0 bk.Ep.natDegree hρ
        (by simpa using pow_le_of_le_one hρ.le hρ1 bk.deg_pos.ne')
      simpa using this
    · refine (norm_mul_le _ _).trans ?_
      have h2 := gauge_mono_le (l := l) u ρ 1 0 hρ (by simpa using hlρ)
      have h3 := norm_algebraMap_le (l := l) (u := u) (ρ := ρ) (BK.hf f q)
      calc _ ≤ (ρ : ℝ) * 1 := mul_le_mul h2 h3 (norm_nonneg _) hρ.le
        _ = ρ := mul_one _
  have hmem : BK.hf g X - BK.hf f X ∈ B.I := by
    have hs : Ideal.Quotient.mk bk.prism.I (X : bk.S) = bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ X)) :=
      (bk.str.apply_symm_apply _).symm
    exact Ideal.Quotient.eq.1 ((g.f_str _ _ hs).trans (f.f_str _ _ hs).symm)
  have hI : B.I = Ideal.span {BK.hf f bk.E} := by
    rw [← GlobalTheory.T.prism_hom_map_ideal_eq l ↥(OL K) bk.prism B f]
    show (Ideal.span {bk.E}).map (BK.hf f) = _
    rw [Ideal.map_span, Set.image_singleton]
  rw [hI, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have e2 : BK.hf g X = u + BK.hf f bk.E * c := by rw [← hc, hu]; ring
  show ‖ofPre l u ρ (am (BK.hf g X))‖ ≤ ρ
  rw [norm_ofPre, ← norm_preDisc, e2, map_add (f := _), map_mul]
  refine (um _ _).trans (max_le hX ?_)
  refine (norm_mul_le _ _).trans ?_
  calc _ ≤ (ρ : ℝ) * 1 := mul_le_mul hE (norm_algebraMap_le _) (norm_nonneg _) hρ.le
    _ = ρ := mul_one _

theorem disc_map_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ (B : Obj l ↥(OL K))
    (f g : Hom bk.prism B) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ ≤ 1 →
    ∃ F : bk.DS ρ →+* Disc l (BK.hf f X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) F := by
  intro l _ K bk B f g ρ h0 h1
  exact ⟨Disc.map (BK.hf g) (norm_toDisc_hf_le bk B f g ρ h0 h1), isDiscMap_map _ _⟩

end GlobalTheory.BSP.DiscPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCongrPowE
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.WApprox

theorem ρ₀_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by simp only [neg_neg_iff_pos]; positivity)

theorem exists_congr_pow_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ) (x : bk.DS bk.ρ₀),
    ∃ (k : ℕ) (s : bk.S), toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣
      (l : bk.DS bk.ρ₀) ^ k * x - toDisc l (X : bk.S) bk.ρ₀ s := by
  intro l _ K bk m
  induction m with
  | zero => intro x; exact ⟨0, 0, by simp⟩
  | succ m ih =>
    intro x
    obtain ⟨q, k, r, -, hx⟩ := WDiv.weierstrass_div l K bk bk.ρ₀ le_rfl (ρ₀_lt_one bk) x
    obtain ⟨k', s', w, hw⟩ := ih q
    refine ⟨k + k', bk.E * s' + (l : bk.S) ^ k' * (r : bk.S), w, ?_⟩
    have hq : (l : bk.DS bk.ρ₀) ^ k' * q = toDisc l (X : bk.S) bk.ρ₀ s' +
        toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m * w := by rw [← hw]; ring
    calc (l : bk.DS bk.ρ₀) ^ (k + k') * x - toDisc l (X : bk.S) bk.ρ₀ (bk.E * s' + (l : bk.S) ^ k' * (r : bk.S))
        = (l : bk.DS bk.ρ₀) ^ k' * ((l : bk.DS bk.ρ₀) ^ k * x) - toDisc l (X : bk.S) bk.ρ₀ (bk.E * s' + (l : bk.S) ^ k' * (r : bk.S)) := by ring
      _ = toDisc l (X : bk.S) bk.ρ₀ bk.E * ((l : bk.DS bk.ρ₀) ^ k' * q) - toDisc l (X : bk.S) bk.ρ₀ bk.E * toDisc l (X : bk.S) bk.ρ₀ s' := by
          rw [hx, map_add (f := _), map_mul, map_mul, map_pow, map_natCast]; ring
      _ = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (m + 1) * w := by rw [hq]; ring

end GlobalTheory.BKLim.WApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoordAcrisBcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CoordTW

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K]
  [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G]
  (T : LocLat G ℚ_[l] K O) (φ : ↥T.L.T →+ ℤ_[l])
  (hφ : ∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t)
  (R : Type) [CommRing R] [Algebra ℤ_[l] R]

def inner (t : ↥T.L.T) : O ⊗[ℤ_[l]] R →+ R :=
  TensorProduct.liftAddHom
    { toFun := fun o => AddMonoidHom.mulLeft (algebraMap ℤ_[l] R (φ (o • t)))
      map_zero' := by ext r; simp
      map_add' := by intro a b; ext r; simp [add_smul, add_mul] }
    (fun z o r => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_mulLeft]
      rw [Algebra.smul_def z o, mul_smul, hφ, Algebra.smul_def z r, map_mul]; ring)

theorem inner_tmul (t : ↥T.L.T) (o : O) (r : R) :
    inner T φ hφ R t (o ⊗ₜ[ℤ_[l]] r) = algebraMap ℤ_[l] R (φ (o • t)) * r := by
  simp [inner]

theorem inner_add (t t' : ↥T.L.T) (w : O ⊗[ℤ_[l]] R) :
    inner T φ hφ R (t + t') w = inner T φ hφ R t w + inner T φ hφ R t' w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o r => simp only [inner_tmul, smul_add, map_add (f := _), add_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; ring

theorem inner_zero (w : O ⊗[ℤ_[l]] R) : inner T φ hφ R 0 w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o r => simp [inner_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]

theorem inner_smul (o : O) (t : ↥T.L.T) (w : O ⊗[ℤ_[l]] R) :
    inner T φ hφ R t (o • w) = inner T φ hφ R (o • t) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o' r =>
    rw [TensorProduct.smul_tmul', inner_tmul, inner_tmul, smul_eq_mul, mul_smul, smul_comm o o' t]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

def coord : TW (O ⊗[ℤ_[l]] R) T →+ R :=
  TensorProduct.liftAddHom
    { toFun := fun w =>
        { toFun := fun t => inner T φ hφ R t w
          map_zero' := inner_zero T φ hφ R w
          map_add' := fun t t' => inner_add T φ hφ R t t' w }
      map_zero' := by ext t; simp
      map_add' := by intro a b; ext t; simp }
    (fun o w t => by simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]; exact inner_smul T φ hφ R o t w)

theorem coord_tmul (w : O ⊗[ℤ_[l]] R) (t : ↥T.L.T) :
    coord T φ hφ R (w ⊗ₜ[O] t) = inner T φ hφ R t w := by
  simp [coord]

theorem coord_mul (a : R) (w : TW (O ⊗[ℤ_[l]] R) T) :
    coord T φ hφ R (((1 : O) ⊗ₜ[ℤ_[l]] a : O ⊗[ℤ_[l]] R) • w) = a * coord T φ hφ R w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [TensorProduct.smul_tmul', coord_tmul, coord_tmul, smul_eq_mul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inner_tmul, inner_tmul]; ring
    | add x y hx hy => simp only [mul_add, map_add (f := _), hx, hy]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy, mul_add]

theorem coord_one_tmul (t : ↥T.L.T) :
    coord T φ hφ R ((1 : O ⊗[ℤ_[l]] R) ⊗ₜ[O] t) = algebraMap ℤ_[l] R (φ t) := by
  rw [coord_tmul, Algebra.TensorProduct.one_def, inner_tmul, one_smul, mul_one]

theorem coord_algebraMap_smul (z : ℤ_[l]) (w : TW (O ⊗[ℤ_[l]] R) T) :
    coord T φ hφ R ((algebraMap ℤ_[l] O z) • w) = algebraMap ℤ_[l] R z * coord T φ hφ R w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [TensorProduct.smul_tmul', coord_tmul, coord_tmul, inner_smul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      rw [inner_tmul, inner_tmul, smul_comm o (algebraMap ℤ_[l] O z) t, hφ, map_mul]; ring
    | add x y hx hy => simp only [mul_add, map_add (f := _), hx, hy]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy, mul_add]

theorem coord_toOB (w : TW (OCr l O) T) :
    coord T φ hφ (Per.Bcris l) (TWincl (toOB l O) T w) = acrisToBcris l (coord T φ hφ (Per.Acris l) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    simp only [TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq,
      coord_tmul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      simp only [toOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, inner_tmul, map_mul,
        AlgHom.commutes]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.CoordTW

namespace GlobalTheory


open GlobalTheory.CoordTW in
theorem exists_coord_acris_bcris : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (φ : ↥T.L.T →+ ℤ_[l]), (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → ∃ (ΦA : TW (OCr l O) T →+ Per.Acris l) (ΦB : TW (OB l O) T →+ Per.Bcris l), (∀ (a : Per.Acris l) (w : TW (OCr l O) T), ΦA (((1 : O) ⊗ₜ[ℤ_[l]] a : OCr l O) • w) = a * ΦA w) ∧ (∀ (y : Per.Bcris l) (w : TW (OB l O) T), ΦB (((1 : O) ⊗ₜ[ℤ_[l]] y : OB l O) • w) = y * ΦB w) ∧ (∀ x : ↥T.L.T, ΦB ((1 : OB l O) ⊗ₜ[O] x) = algebraMap ℤ_[l] (Per.Bcris l) (φ x)) ∧ (∀ (N : ℕ) (w : TW (OCr l O) T), ΦA (((l : O) ^ N) • w) = (l : Per.Acris l) ^ N * ΦA w) ∧ (∀ w : TW (OCr l O) T, ΦB (TWincl (toOB l O) T w) = acrisToBcris l (ΦA w)) := by
  intro l _ O K _ _ _ _ _ _ G _ _ T φ hφ
  refine ⟨coord T φ hφ (Per.Acris l), coord T φ hφ (Per.Bcris l), coord_mul T φ hφ _,
    coord_mul T φ hφ _, coord_one_tmul T φ hφ _, fun N w => ?_, coord_toOB T φ hφ⟩
  have h : ((l : O) ^ N) = algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ N) := by simp
  rw [h, coord_algebraMap_smul]
  simp

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCornerSeparableCharpolyOfIsInternal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem isInternal_map_of_corner {K : Type} [Field K] {n t : ℕ} (ι : Type) [Fintype ι]
    [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hV : DirectSum.IsInternal Vs) (hba : b * a = 1)
    (he : ∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) :
    DirectSum.IsInternal (fun j => (Vs j).map b.mulVecLin) := by
  classical
  have hfg : ∀ w : Fin t → K, b.mulVecLin (a.mulVecLin w) = w := fun w => by
    simp [Matrix.mulVec_mulVec, hba]
  have hE : (a * b).mulVecLin = a.mulVecLin ∘ₗ b.mulVecLin := Matrix.mulVecLin_mul a b

  have hback : ∀ S : Submodule K (Fin n → K), S.map (a * b).mulVecLin ≤ S →
      (S.map b.mulVecLin).map a.mulVecLin ≤ S := by
    intro S hS
    rwa [← Submodule.map_comp, ← hE]
  have hVj : ∀ j, (Vs j).map (a * b).mulVecLin ≤ Vs j := by
    rintro j _ ⟨v, hv, rfl⟩
    exact he j v hv
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hV ⊢
  obtain ⟨hind, htop⟩ := hV
  constructor
  · rw [iSupIndep_def] at hind ⊢
    intro j
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have hrest : (⨆ k, ⨆ (_ : k ≠ j), Vs k).map (a * b).mulVecLin ≤ ⨆ k, ⨆ (_ : k ≠ j), Vs k := by
      simp_rw [Submodule.map_iSup]
      exact iSup₂_mono fun k _ => hVj k
    have hx2' : x ∈ (⨆ k, ⨆ (_ : k ≠ j), Vs k).map b.mulVecLin := by
      simp_rw [Submodule.map_iSup]
      exact hx2
    have h1 : a.mulVecLin x ∈ Vs j := hback _ (hVj j) (Submodule.mem_map_of_mem hx1)
    have h2 : a.mulVecLin x ∈ ⨆ k, ⨆ (_ : k ≠ j), Vs k :=
      hback _ hrest (Submodule.mem_map_of_mem hx2')
    rw [← hfg x, Submodule.disjoint_def.1 (hind j) _ h1 h2, map_zero]
  · rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
    exact fun w => ⟨a.mulVecLin w, hfg w⟩

theorem exists_separable_charpoly_of_isInternal {K : Type} [Field K] [Infinite K] {t : ℕ}
    (ι : Type) [Fintype ι] [DecidableEq ι] (W : ι → Submodule K (Fin t → K))
    (hW : DirectSum.IsInternal W) :
    ∃ D : Matrix (Fin t) (Fin t) K, (∀ j, ∀ w ∈ W j, D.mulVec w ∈ W j) ∧
      D.charpoly.Separable := by
  classical

  let v : ∀ j, Module.Basis (Fin (Module.finrank K (W j))) K (W j) := fun j => Module.finBasis K (W j)
  let B := hW.collectedBasis v
  let μ : (Σ j, Fin (Module.finrank K (W j))) → K :=
    fun s => Infinite.natEmbedding K (Fintype.equivFin _ s)
  have hμ : Function.Injective μ :=
    (Infinite.natEmbedding K).injective.comp (Fin.val_injective.comp (Fintype.equivFin _).injective)
  let φ : (Fin t → K) →ₗ[K] (Fin t → K) := B.constr K (fun s => μ s • B s)
  have hφB : ∀ s, φ (B s) = μ s • B s := fun s => B.constr_basis K _ s
  refine ⟨LinearMap.toMatrix' φ, ?_, ?_⟩
  · intro j w hw
    have hD : (LinearMap.toMatrix' φ).mulVec w = φ w := by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    have hw' : w = ((∑ k, (v j).repr ⟨w, hw⟩ k • v j k : W j) : Fin t → K) := by
      rw [(v j).sum_repr]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hD, hw', Submodule.coe_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Submodule.coe_smul, map_smul]
    refine Submodule.smul_mem _ _ ?_
    have hk : ((v j k : W j) : Fin t → K) = B ⟨j, k⟩ := by simp [B]
    rw [hk, hφB]
    exact Submodule.smul_mem _ _ (hW.collectedBasis_mem v ⟨j, k⟩)
  · have h1 : (LinearMap.toMatrix' φ).charpoly = φ.charpoly := by
      rw [← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix]
    have h2 : LinearMap.toMatrix B B φ = Matrix.diagonal μ := by
      ext s s'
      rw [LinearMap.toMatrix_apply, hφB, map_smul, B.repr_self, Matrix.diagonal_apply]
      by_cases h : s = s'
      · subst h; simp
      · simp [h]
    rw [h1, ← LinearMap.charpoly_toMatrix φ B, h2, Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.2 hμ

theorem exists_corner_separable_charpoly :
    ∀ {K : Type} [Field K] [Infinite K] {n t : ℕ} (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), DirectSum.IsInternal Vs → b * a = 1 → (∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) → ∃ m : Matrix (Fin n) (Fin n) K, (∀ j, ∀ v ∈ Vs j, m.mulVec v ∈ Vs j) ∧ (b * m * a).charpoly.Separable := by
  intro K _ _ n t ι _ _ Vs a b hV hba he
  obtain ⟨D, hD, hsep⟩ :=
    exists_separable_charpoly_of_isInternal ι _ (isInternal_map_of_corner ι Vs a b hV hba he)
  refine ⟨a * D * b, ?_, ?_⟩
  · intro j v hv
    obtain ⟨u, hu, hu'⟩ := hD j (b.mulVec v) (Submodule.mem_map_of_mem hv)
    have hm : (a * D * b).mulVec v = (a * b).mulVec u := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      congr 1
      exact hu'.symm
    rw [hm]
    exact he j u hu
  · have hc : b * (a * D * b) * a = D := by
      calc b * (a * D * b) * a = (b * a) * D * (b * a) := by simp only [Matrix.mul_assoc]
        _ = D := by rw [hba, Matrix.one_mul, Matrix.mul_one]
    rw [hc]
    exact hsep

end GlobalTheory.SpanRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystalCoordinatesOverBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysExt

theorem exists_ext {A B M N R T ι : Type} [CommRing A] [CommRing B] [CommRing R] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (J : T → B →+* R)
    (v : M →+ (T → ι → R)) (hv : ∀ (w : A) (x : M) τ i, v (w • x) τ i = J τ (f w) * v x τ i) :
    ∃ lam : N →+ (T → ι → R), (∀ (r : B) (y : N) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧
      ∀ x, lam (u x) = v x := by
  letI : Module B (T → ι → R) := Module.compHom (T → ι → R)
    (RingHom.pi fun τ => RingHom.pi fun _ : ι => J τ : B →+* (T → ι → R))
  let v' : M →ₛₗ[f] (T → ι → R) :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun w x => funext fun τ => funext fun i => hv w x τ i }
  obtain ⟨lam, hlam, -⟩ := h (T → ι → R) v'
  exact ⟨lam.toAddMonoidHom, fun r y τ i => congrFun (congrFun (lam.map_smul r y) τ) i, hlam⟩

theorem frob_toAc {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O)
    (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem exists_coord : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → ∃ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧ ∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ EE c hc PP p J g hJ
  let v : EE.M (ϖ.prism a) →+ (ZMod a → ι → K⟦X⟧⟦X⟧) :=
    { toFun := fun x τ i => g (frob K l (c x (τ - 1) i))
      map_zero' := by ext1 τ; ext1 i; simp
      map_add' := fun x y => by ext1 τ; ext1 i; simp }
  obtain ⟨lam, h1, h2⟩ := exists_ext (EE.tr_bc p) J v (fun w x τ i => by
    change g (frob K l (c (w • x) (τ - 1) i)) = J τ (p.f w) * g (frob K l (c x (τ - 1) i))
    have e1 : c (w • x) (τ - 1) i = (toAc t K w (τ - 1) : K⟦X⟧) * c x (τ - 1) i :=
      congrFun (congrFun (hc w x) (τ - 1)) i
    have e2 := hJ τ w
    have e3 := frob_toAc (K := K) t w τ
    rw [e1, map_mul, map_mul]
    exact congrArg (· * _) ((congrArg g e3).trans e2.symm))
  exact ⟨lam, h1, fun x τ i => congrFun (congrFun (h2 x) τ) i⟩

end GlobalTheory.CrysExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisDeRhamLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodge_basis_deRham_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ N : ℕ, (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∀ i, |(H.p i : ℤ) - H.q| ≤ N := by
  first | (exact @GlobalTheory.HodgeEx.exists_hodge) | (exact GlobalTheory.HodgeEx.exists_hodge) | (intros; apply GlobalTheory.HodgeEx.exists_hodge  <;> assumption)
end

