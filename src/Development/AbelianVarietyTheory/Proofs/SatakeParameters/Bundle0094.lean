module

public import Mathlib
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0004
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetLL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationUnimodularCompanionEq
section
open NumberField Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F

noncomputable section

namespace GlobalTheory.CompanLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem locS_mono {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (S : Submonoid (𝓞 E)) {M M₁ : Submodule (𝓞 E) W}
    (h : M ≤ M₁) : Formalism.HermitianLatticesTheory.locS S M ≤ Formalism.HermitianLatticesTheory.locS S M₁ := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem le_locS {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (S : Submonoid (𝓞 E)) (M : Submodule (𝓞 E) W) :
    M ≤ Formalism.HermitianLatticesTheory.locS S M := fun x hx => ⟨1, S.one_mem, by simpa using hx⟩

theorem locS_le_of_le {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (S : Submonoid (𝓞 E)) {M M₁ : Submodule (𝓞 E) W}
    (h : M ≤ Formalism.HermitianLatticesTheory.locS S M₁) : Formalism.HermitianLatticesTheory.locS S M ≤ Formalism.HermitianLatticesTheory.locS S M₁ := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hx'⟩ := h hx
  refine ⟨t * s, S.mul_mem ht hs, ?_⟩
  rw [mul_smul]
  exact hx'

abbrev conjO : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)

theorem conjO_mem_hcompl (Q : Ideal (𝓞 E)) {s : 𝓞 E} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q) :
    conjO s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q := by
  have hle : Formalism.HermitianLatticesTheory.hcompl (K := E) Q ≤ (Formalism.HermitianLatticesTheory.hcompl (K := E) Q).comap (conjO (E := E)).toMonoidHom := by
    unfold Formalism.HermitianLatticesTheory.hcompl
    rw [Submonoid.closure_le]
    rintro s ⟨hs1, hs2⟩
    apply Submonoid.subset_closure
    refine ⟨?_, ?_⟩
    · exact hs2 _ rfl
    · intro t ht hm
      have : t = s := by
        apply RingOfIntegers.ext
        have h1 : (t : E) = star (star (s : E)) := ht
        simpa using h1
      exact hs1 (this ▸ hm)
  exact hle hs

theorem hform_smul_left {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (c : E) (x y : Fin N → E) :
    Formalism.UG.hform σ J (c • x) y = σ c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem hform_smul_right {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (c : E) (x y : Fin N → E) :
    Formalism.UG.hform σ J x (c • y) = c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem hform_add_left {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (x x' y : Fin N → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  unfold Formalism.UG.hform
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, map_add (f := _)]
  ring

theorem hform_zero_left {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (y : Fin N → E) :
    Formalism.UG.hform σ J 0 y = 0 := by
  unfold Formalism.UG.hform
  simp

theorem smul_coe {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (c : 𝓞 E) (w : W) :
    c • w = (c : E) • w := (algebraMap_smul E c w).symm

theorem span_dual_le {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E))
    (hfg : Λ₁.FG) (h : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ) :
    Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (starRingEnd E) J Λ) ≤
      Formalism.HermitianLatticesTheory.loc (K := E) Q (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (starRingEnd E) J Λ₁)) := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  have hg : ∀ g ∈ s, ∃ t ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q, t • g ∈ Λ := fun g hg => h (Submodule.subset_span hg)
  choose t ht hts using hg
  set u : 𝓞 E := ∏ g ∈ s.attach, conjO (t g.1 g.2) with hu
  have hu_mem : u ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q :=
    Submonoid.prod_mem _ fun g _ => conjO_mem_hcompl Q (ht g.1 g.2)
  rw [Submodule.span_le]
  intro y hy
  refine ⟨u, hu_mem, Submodule.subset_span ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem g hgs =>
    rw [smul_coe, hform_smul_right]
    have e : u = (∏ g' ∈ s.attach.erase ⟨g, hgs⟩, conjO (t g'.1 g'.2)) * conjO (t g hgs) := by
      rw [hu]
      exact (Finset.prod_erase_mul _ _ (Finset.mem_attach _ _)).symm
    have h2 : Formalism.UG.hform (starRingEnd E) J (t g hgs • g) y ∈ (algebraMap (𝓞 E) E).range := hy _ (hts g hgs)
    rw [smul_coe, hform_smul_left] at h2
    rw [e, show ∀ A B : 𝓞 E, ((A * B : 𝓞 E) : E) = (A : E) * (B : E) from fun _ _ => rfl, mul_assoc]
    refine Subring.mul_mem _ ⟨_, rfl⟩ ?_
    exact h2
  | zero => rw [hform_zero_left]; exact Subring.zero_mem _
  | add x x' _ _ hx hx' => rw [hform_add_left]; exact Subring.add_mem _ hx hx'
  | smul c x _ hx =>
    rw [smul_coe, hform_smul_left]
    exact Subring.mul_mem _ ⟨conjO c, rfl⟩ hx

theorem compan_le_loc {R : Ranks} {F : Type} [Field F] [NumberField F] [Algebra F E] (sp : Spaces R F E) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)) (hfg : Λ₁.FG)
    (h : Λ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁) (h₁ : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ) :
    compan (sp := sp) J a Λ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) := by
  have hσ : (sp.cm.sig : E →+* E) = starRingEnd E := RingHom.ext fun _ => rfl
  unfold compan
  rw [hσ]
  apply sup_le
  · exact h.trans (locS_mono _ le_sup_left)
  · rw [Submodule.smul_le]
    intro r hr n hn
    obtain ⟨s, hs, hsn⟩ := span_dual_le J Q Λ Λ₁ hfg h₁ hn
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hsn)

end GlobalTheory.CompanLoc

namespace GlobalTheory

theorem loc_compan_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)),
    Λ.FG → Λ₁.FG → Formalism.HermitianLatticesTheory.loc (K := E) Q Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁ →
    Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) := by
  intro R F E _ _ _ _ _ _ sp N J a Q Λ Λ₁ hfg hfg₁ h
  have h1 : Λ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁ := (CompanLoc.le_locS _ Λ).trans h.le
  have h2 : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ := (CompanLoc.le_locS _ Λ₁).trans h.ge
  exact le_antisymm (CompanLoc.locS_le_of_le _ (CompanLoc.compan_le_loc sp J a Q Λ Λ₁ hfg₁ h1 h2))
    (CompanLoc.locS_le_of_le _ (CompanLoc.compan_le_loc sp J a Q Λ₁ Λ hfg h2 h1))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogPeriodCongruenceBdr
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.StLat

theorem exists_mul_eq_pow_pred {l : ℕ} [Fact l.Prime] {j m : ℕ} (hj : j ≠ 0) (hm : ¬ l ^ m ∣ j) :
    ∃ c : ℤ_[l], ((j : ℕ) : ℤ_[l]) * c = (l : ℤ_[l]) ^ (m - 1) := by
  first
  | exact @_root_.GlobalTheory.PolynomialNormBound.main
  | exact _root_.GlobalTheory.PolynomialNormBound.main
  | (apply _root_.GlobalTheory.PolynomialNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialNormBound.main ..)

theorem not_pow_dvd {l m j : ℕ} (h1 : j ≠ 0) (h2 : j < 2 * l ^ m) (h3 : j ≠ l ^ m) : ¬ l ^ m ∣ j := by
  rintro ⟨t, rfl⟩
  rcases t with _ | _ | t
  · simp at h1
  · simp at h3
  · have : l ^ m * 2 ≤ l ^ m * (t + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem log_trunc_pow : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) → ∀ u : Per.BdRp l, IsLogP (beta ϖ) u →
  ∀ m : ℕ, 1 ≤ m → ∃ s ∈ Sg ϖ, ∃ e : Per.BdRp l, (e = 1 ∨ e = -1) ∧
    betaD ϖ ^ (2 * l ^ m) ∣ ((l : ℕ) : Per.BdRp l) * (((l : ℕ) : Per.BdRp l) ^ (m - 1) * u - s) -
      e * betaD ϖ ^ (l ^ m) := by
  intro l _ ϖ hker hfil u hu m hm
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set M := l ^ (m + 1) with hM
  set n := 2 * M with hn
  have hlpos : 0 < l := (Fact.out : l.Prime).pos
  have hMpos : 0 < M := pow_pos hlpos _
  set β := beta ϖ with hβ

  have hc : ∀ j : ℕ, ∃ c : ℤ_[l], (j ≠ 0 ∧ j < n ∧ j ≠ M) → ((j : ℕ) : ℤ_[l]) * c = (l : ℤ_[l]) ^ m := by
    intro j
    by_cases h : j ≠ 0 ∧ j < n ∧ j ≠ M
    · obtain ⟨c, hc⟩ := exists_mul_eq_pow_pred (l := l) (m := m + 1) h.1 (not_pow_dvd h.1 h.2.1 h.2.2)
      exact ⟨c, fun _ => by simpa using hc⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose c hc using hc
  let d : ℕ → ℤ_[l] := fun j => if j = M ∨ j = n then 0 else c j
  let a : ℕ → Per.AinfP l := fun k => (-1) ^ k * Per.zP l (d (k + 1)) * β ^ (k + 1)
  let S : Per.AinfP l := ∑ k ∈ Finset.range n, a k
  let e0 : Per.AinfP l := (-1) ^ (M - 1)
  let T : Per.AinfP l := (-1) ^ (n - 1) * ((l : ℕ) : Per.AinfP l) ^ (m + 1) *
    ((n.factorial / (n - 1 + 1) : ℕ) : Per.AinfP l) * β ^ (n - 1 + 1)
  have hS : S ∈ Sa ϖ := by
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ?_ _) ?_) (Subalgebra.pow_mem _ ?_ _)
    · exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
    · first
      | exact Subalgebra.algebraMap_mem _ _
      | (rw [GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp]; exact Subalgebra.algebraMap_mem _ _)
    · exact Algebra.subset_adjoin (Set.mem_singleton _)

  have hterm : ∀ k ∈ Finset.range n, ((l : ℕ) : Per.AinfP l) ^ (m + 1) *
      ((-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1)) =
      ((n.factorial : ℕ) : Per.AinfP l) * ((l : ℕ) : Per.AinfP l) * a k +
      (if k = M - 1 then ((n.factorial : ℕ) : Per.AinfP l) * ((-1) ^ k * β ^ (k + 1)) else 0) +
      (if k = n - 1 then (-1) ^ k * ((l : ℕ) : Per.AinfP l) ^ (m + 1) *
        ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1) else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hdvd : (k + 1) ∣ n.factorial := Nat.dvd_factorial (by omega) (by omega)
    have hq : (((n.factorial / (k + 1) : ℕ) : Per.AinfP l)) * ((k + 1 : ℕ) : Per.AinfP l) =
        ((n.factorial : ℕ) : Per.AinfP l) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    by_cases h1 : k = M - 1
    · have h2 : ¬ k = n - 1 := by omega
      have hk1 : k + 1 = M := by omega
      have hda : d (k + 1) = 0 := by simp [d, hk1]
      rw [if_pos h1, if_neg h2]
      simp only [a, hda, map_zero, mul_zero, zero_mul, add_zero, zero_add]
      rw [← hq, hk1, hM, Nat.cast_pow]
      ring
    · by_cases h2 : k = n - 1
      · have hk1 : k + 1 = n := by omega
        have hda : d (k + 1) = 0 := by simp [d, hk1]
        rw [if_neg h1, if_pos h2]
        simp only [a, hda, map_zero, mul_zero, zero_mul, add_zero, zero_add]
        ring
      · have hne : ¬ (k + 1 = M ∨ k + 1 = n) := by omega
        have hda : d (k + 1) = c (k + 1) := by simp only [d, hne, if_false]
        have hck := hc (k + 1) ⟨by omega, by omega, by omega⟩
        have hck' := congrArg (Per.zP l) hck
        rw [map_mul, map_natCast, map_pow, map_natCast] at hck'
        rw [if_neg h1, if_neg h2]
        simp only [a, hda, add_zero]
        rw [← hq]
        linear_combination -(-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1) *
          ((l : ℕ) : Per.AinfP l) * hck'
  have hsum : ((l : ℕ) : Per.AinfP l) ^ (m + 1) * ∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1) =
      ((n.factorial : ℕ) : Per.AinfP l) * (((l : ℕ) : Per.AinfP l) * S + e0 * β ^ M) + T := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.mul_sum]
    have hm1 : M - 1 ∈ Finset.range n := Finset.mem_range.2 (by omega)
    have hn1 : n - 1 ∈ Finset.range n := Finset.mem_range.2 (by omega)
    rw [if_pos hm1, if_pos hn1, Nat.sub_add_cancel (by omega : 1 ≤ M)]
    simp only [S, e0, T]
    ring
  have hβI : β ∈ Per.kerP l := by rw [hker]; exact Ideal.mem_span_singleton_self _
  have hT : T ∈ Per.kerP l ^ n := by
    have : β ^ (n - 1 + 1) ∈ Per.kerP l ^ n := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact Ideal.pow_mem_pow hβI n
    exact Ideal.mul_mem_left _ _ this

  let s : Per.BdRp l := algebraMap (Per.AinfP l) (Per.BdRp l) S
  refine ⟨s, Subring.mem_map.2 ⟨S, hS, rfl⟩, algebraMap (Per.AinfP l) (Per.BdRp l) e0, ?_, ?_⟩
  · rcases neg_one_pow_eq_or (Per.AinfP l) (M - 1) with h | h
    · left; simp [e0, h]
    · right; simp [e0, h]
  · rw [← Ideal.mem_span_singleton, ← hfil]
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    have hev : ∀ x : Per.AinfP l, Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) =
        Ideal.Quotient.mk _ x := fun x => GlobalTheory.RingIface.ev_alg l n x
    let q : Per.AinfP l →+* Per.AinfP l ⧸ Per.kerP l ^ n := Ideal.Quotient.mk _
    have hunit : IsUnit ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) := by
      have := (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero).map q
      rwa [map_natCast] at this
    have hqT : q T = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hT
    have hs2 := congrArg q hsum
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, hqT, add_zero] at hs2
    have hun := hu n
    apply hunit.mul_left_cancel
    rw [mul_zero]
    simp only [betaD, map_sub, map_mul, map_pow, map_natCast, s, hev]
    change ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) * (((l : ℕ) : _) * (((l : ℕ) : _) ^ m * Per.ev l n u - q S) -
      q e0 * q β ^ M) = 0
    change _ = q _ at hun
    linear_combination ((l : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) ^ (m + 1) * hun + hs2

end GlobalTheory.Pst.StLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormNatCastOfCoprime
section
open NumberField

namespace GlobalTheory.CoprimeUnitMultipliers

theorem exists_common_smul {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (U : R → Prop) (h1 : U 1) (hm : ∀ a b, U a → U b → U (a * b))
    (M N : Submodule R V) (hM : M.FG) (h : ∀ x ∈ M, ∃ s, U s ∧ s • x ∈ N) :
    ∃ s, U s ∧ ∀ x ∈ M, s • x ∈ N := by
  classical
  obtain ⟨S, rfl⟩ := hM
  have key : ∀ T : Finset V, (∀ x ∈ T, ∃ s, U s ∧ s • x ∈ N) → ∃ s, U s ∧ ∀ x ∈ T, s • x ∈ N := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨1, h1, by simp⟩
    | insert a T _ ih =>
      intro hT
      obtain ⟨s, hs, hsT⟩ := ih fun x hx => hT x (Finset.mem_insert_of_mem hx)
      obtain ⟨t, ht, hta⟩ := hT a (Finset.mem_insert_self a T)
      refine ⟨s * t, hm _ _ hs ht, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [mul_smul]; exact N.smul_mem _ hta
      · rw [mul_comm, mul_smul]; exact N.smul_mem _ (hsT x hx)
  obtain ⟨s, hs, hS⟩ := key S fun x hx => h x (Submodule.subset_span hx)
  refine ⟨s, hs, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact N.smul_mem _ hx

theorem norm_natCast_of_coprime {p : ℕ} [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) :
    ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 h.symm

theorem general {E : Type*} [Field E] {p : ℕ} [Fact p.Prime] (ρ : E →+* ℂ_[p]) {N N' : ℕ}
    (L L₁ : Submodule (𝓞 E) (Fin N → E)) (L' L₁' : Submodule (𝓞 E) (Fin N' → E))
    (P : Matrix (Fin N) (Fin N) E) (P' : Matrix (Fin N') (Fin N') E) (hfg : L₁.FG)
    (s : ℕ) (hs : Nat.Coprime s p) (hL : ∀ x ∈ L₁, (s : E) • x ∈ L)
    (s' : ℕ) (hs' : Nat.Coprime s' p) (hL' : ∀ x ∈ L', (s' : E) • x ∈ L₁')
    (hdet : P.det ≠ 0)
    (hP : ∀ x ∈ L, ∃ t : 𝓞 E, ‖ρ (t : E)‖ = 1 ∧ ∃ c : Fin N → 𝓞 E, t • x = ∑ a, c a • P.transpose a)
    (hP' : ∀ a, ∃ t : 𝓞 E, ‖ρ (t : E)‖ = 1 ∧ t • P'.transpose a ∈ L') :
    ∃ σ σ' : 𝓞 E, ‖ρ (σ : E)‖ = 1 ∧ ‖ρ (σ' : E)‖ = 1 ∧
      (∀ a : Fin N, ∀ x ∈ L₁, ∃ o : 𝓞 E, (o : E) = (σ : E) * ∑ j : Fin N, P⁻¹ a j * x j) ∧
      ∀ b : Fin N', (fun i : Fin N' => (σ' : E) * P' i b) ∈ L₁' := by
  have h1 : ‖ρ ((1 : 𝓞 E) : E)‖ = 1 := by simp
  have hm : ∀ a b : 𝓞 E, ‖ρ (a : E)‖ = 1 → ‖ρ (b : E)‖ = 1 → ‖ρ ((a * b : 𝓞 E) : E)‖ = 1 := by
    intro a b ha hb
    rw [RingOfIntegers.coe_eq_algebraMap] at ha hb ⊢
    rw [map_mul, map_mul, norm_mul, ha, hb, one_mul]
  have hn : ∀ n : ℕ, Nat.Coprime n p → ‖ρ (((n : 𝓞 E)) : E)‖ = 1 := by
    intro n hn
    rw [RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast]
    exact norm_natCast_of_coprime hn
  have hsm : ∀ {k : ℕ} (n : ℕ) (x : Fin k → E), (n : 𝓞 E) • x = (n : E) • x := by
    intro k n x
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨σ, hσ, hσL⟩ := exists_common_smul (fun t : 𝓞 E => ‖ρ (t : E)‖ = 1) h1 hm L₁
    (Submodule.span (𝓞 E) (Set.range P.transpose)) hfg (by
      intro x hx
      obtain ⟨t, ht, c, hc⟩ := hP _ (hL x hx)
      refine ⟨t * s, hm _ _ ht (hn s hs), ?_⟩
      rw [mul_smul, hsm, hc]
      exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  obtain ⟨σ', hσ', hσL'⟩ := exists_common_smul (fun t : 𝓞 E => ‖ρ (t : E)‖ = 1) h1 hm
    (Submodule.span (𝓞 E) (Set.range P'.transpose)) L₁'
    (Submodule.fg_span (Set.finite_range _)) (by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨t, ht, hta⟩ := hP' a
        refine ⟨s' * t, hm _ _ (hn s' hs') ht, ?_⟩
        rw [mul_smul, hsm]
        exact hL' _ hta
      | zero => exact ⟨1, h1, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨t, ht, htx⟩ := hx
        obtain ⟨u, hu, huy⟩ := hy
        refine ⟨t * u, hm _ _ ht hu, ?_⟩
        rw [smul_add]
        refine L₁'.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L₁'.smul_mem _ htx
        · rw [mul_smul]; exact L₁'.smul_mem _ huy
      | smul a x _ hx =>
        obtain ⟨t, ht, htx⟩ := hx
        exact ⟨t, ht, by rw [smul_comm]; exact L₁'.smul_mem _ htx⟩)
  refine ⟨σ, σ', hσ, hσ', fun a x hx => ?_, fun b => ?_⟩
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hσL x hx)
    refine ⟨c a, ?_⟩
    have e1 : P.mulVec (fun i => (c i : E)) = (σ : E) • x := by
      funext i
      have := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Algebra.smul_def] at this
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [RingOfIntegers.coe_eq_algebraMap σ, ← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e2 : (fun i => (c i : E)) = (σ : E) • P⁻¹.mulVec x := by
      rw [← Matrix.mulVec_smul, ← e1, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
    have := congrFun e2 a
    simpa [Matrix.mulVec, dotProduct] using this
  · have := hσL' _ (Submodule.subset_span ⟨b, rfl⟩)
    convert this using 1
    funext i
    simp [Pi.smul_apply, Algebra.smul_def]

theorem exists_unit_multipliers : ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [inst : Fact (Nat.Prime p)] (ρ : (Formalism.BasicNotions.D7.host D).E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N → (Formalism.BasicNotions.D7.host D).E)) (L' L₁' : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N' → (Formalism.BasicNotions.D7.host D).E)) (P : Matrix (Fin N) (Fin N) ((Formalism.BasicNotions.D7.host D).E)) (P' : Matrix (Fin N') (Fin N') ((Formalism.BasicNotions.D7.host D).E)), Submodule.FG L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D p L L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D p L' L₁' → Formalism.MainNotions.TaylorLogMetric.LocBasisW D (⇑ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) L P → Formalism.MainNotions.TaylorLogMetric.LocBasisW D (⇑ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) L' P' → ∃ (σ : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (σ' : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)), ‖(ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) (↑σ : (Formalism.BasicNotions.D7.host D).E)‖ = (1 : ℝ) ∧ ‖(ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) (↑σ' : (Formalism.BasicNotions.D7.host D).E)‖ = (1 : ℝ) ∧ (∀ (a : Fin N), ∀ x ∈ L₁, ∃ (o : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)), (↑o : (Formalism.BasicNotions.D7.host D).E) = (↑σ : (Formalism.BasicNotions.D7.host D).E) * ∑ j : Fin N, P⁻¹ a j * x j) ∧ ∀ (b : Fin N'), (fun (i : Fin N') ↦ (↑σ' : (Formalism.BasicNotions.D7.host D).E) * P' i b) ∈ L₁' := by
  intro D p inst ρ N N' L L₁ L' L₁' P P' hfg h h' hP hP'
  obtain ⟨s, hs, -, hL⟩ := h
  obtain ⟨s', hs', hL', -⟩ := h'
  exact general ρ L L₁ L' L₁' P P' hfg s hs hL s' hs' hL' hP.1 hP.2.2 hP'.2.1

end GlobalTheory.CoprimeUnitMultipliers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelMapsStepWeightValues
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

theorem evG_id_smul {ι Yv : Type} [Fintype ι] {n : ℕ} (fr : Yv → ι → Matrix (Fin n) (Fin n) ℂ) (sh : ι → ℤ) (a : ℂ) (P : Pol ℂ ι n) :
    evG fr sh (RingHom.id ℂ) (a • P) = a • evG fr sh (RingHom.id ℂ) P := by
  funext y
  simp only [evG, Pi.smul_apply, smul_eq_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, RingHom.id_apply]
  ring

theorem Kmap_isVal : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)) f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → IsVal (O.frm (i + 1)) (lamTG M (i + 1)) (RingHom.id ℂ) (C.Kmap i c c' f) := by
  intro D u C A Pm M O i hi hU c c' f hf
  obtain ⟨P, hP, rfl⟩ := hf
  obtain ⟨n, h1, h2, h3, h4⟩ := _root_.GlobalTheory.KerWtStep.trueWt_step D u C A Pm M i hi
  have hle : D.R.N i ≤ D.R.N (i + 1) := by
    unfold Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  have key := GlobalTheory.KerWt.tied_on_models D u C O i hi (nuT D u i) hU ℂ (RingHom.id ℂ) (lamTG M i) n h1 c c'
    (jetC O.dgen (O.Th i c c')) 1 (fun m => by simp) (fun τ => (lamTG M i τ).detShift) h2 P hP
  rw [one_smul] at key
  have hsh : (fun τ => -C.sDiv i τ) = fun τ => (lamTG M (i + 1) τ).detShift := funext fun τ => (h4 τ).symm
  rw [hsh] at key
  refine ⟨(C.rhoDet i c * C.rhoDet' i c') • jetMap (jetC O.dgen (O.Th i c c')) n P, ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (GlobalTheory.KerWt.jet_in_vv_of_weight ℂ D.what₂.Tau _ _ hle (lamTG M i) (lamTG M (i + 1)) n h3 _ P hP)
  · rw [key, evG_id_smul]

end GlobalTheory.KerJ
end
end

