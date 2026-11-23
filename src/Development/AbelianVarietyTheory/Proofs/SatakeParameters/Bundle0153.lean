module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651
public import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LocLanglands
namespace TemperedRec

theorem tempered_lpSum : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x y : WD h), x.tempered → y.tempered → (x.lpSum y).tempered := _root_.GlobalTheory.WeilDeligne.WD.tempered_lpSum

theorem tempered_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), x.mono0 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ‖α‖ = 1) → ∀ l : ℕ, (x.lpChar (WD.lpSp (h := h) l)).tempered := by
  intro E Ω _ _ _ _ _ A w h x
  induction x using WD.ind with
  | hP n a =>
    intro hx heig l
    have hN : a.N = 0 := (WD.monodromyZero_ofWeilDeligneRepClass_iff a).mp hx
    rw [WD.lpSp, WD.lpChar_mk, WD.tempered_mk]
    intro φ hφ
    have hroots : ∀ α ∈ (a.ρ φ).charpoly.roots, ‖α‖ = 1 := fun α hα =>
      heig φ hφ α (by rwa [WD.eig_mk])
    have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
    have hp := isPurePair_scaledDiag_vecShift hq (a.semisimple φ) hroots
      (fun i => (WDRep.spEig w l i : ℂ)) (fun i => by rw [WDRep.spEig, norm_qPow])
    let e := TensorProduct.piScalarRight ℂ ℂ (Fin n → ℂ) (Fin l)
    have hρ : ∀ t, e ((a.tensor (WDRep.sp (h := h) l)).ρ φ t) =
        scaledDiag (a.ρ φ) (fun i => (WDRep.spEig w l i : ℂ)) (e t) := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        ext1 i
        simp [e, TensorProduct.piScalarRightHom_tmul, scaledDiag_apply, hφ, smul_smul]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    have hshift : ∀ t, e ((a.tensor (WDRep.sp (h := h) l)).N t) = vecShift l (e t) := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        ext1 i
        by_cases hi : 1 ≤ (i : ℕ) <;>
          simp [e, TensorProduct.piScalarRightHom_tmul, vecShift_apply, shiftEnd_apply, hN, hi]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    refine hp.of_equiv e.symm (fun v => ?_) (fun v => ?_)
    · obtain ⟨t, rfl⟩ := e.surjective v
      rw [← hρ, e.symm_apply_apply, e.symm_apply_apply]
    · obtain ⟨t, rfl⟩ := e.surjective v
      rw [← hshift, e.symm_apply_apply, e.symm_apply_apply]

theorem norm_eig_eq_of_isIrrWD : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ = ‖β‖ := _root_.GlobalTheory.IrrWeilAbs.irrWD_eig_norm_eq

theorem prod_eig_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp (h := h) l)).eig σ).prod = ((x.eig σ).prod) ^ l := GlobalTheory.T.lp_character_eigen_product

theorem not_precedes_of_norm_eig : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ Δ Δ' : Segment (w.adicCompletion E), (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → ¬ Δ.Precedes Δ' := GlobalTheory.T.segment_sum_tempered

theorem monodromy_zero_of_irreducible_weilDeligne : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → x.mono0 := by
  intro E Ω _ _ _ _ _ A w h x ⟨n, a, hx, hirr⟩
  subst hx
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff]
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans (one_lt_normV w)).ne'
  let S : Subrepresentation a.ρ := ⟨LinearMap.ker a.N, fun σ v hv => by
    have h1 := a.comm_apply σ v
    rw [LinearMap.mem_ker.1 hv, map_zero] at h1
    exact LinearMap.mem_ker.2 ((smul_eq_zero.1 h1.symm).resolve_left (zpow_ne_zero _ hq))⟩
  rcases hirr.eq_bot_or_eq_top S with hS | hS
  · exfalso
    have hinj : Function.Injective a.N := by
      rw [← LinearMap.ker_eq_bot]
      exact congrArg Subrepresentation.toSubmodule hS
    obtain ⟨m, hm⟩ := a.nilpotent
    have hinj' : Function.Injective (a.N ^ m) := by
      rw [FunLike.coe_pow_eq_iterate]; exact hinj.iterate m
    rw [hm] at hinj'
    have := Model.nontrivial_of_isIrreducible hirr
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → ℂ)
    exact hv (hinj' (a₁ := v) (a₂ := 0) (by simp))
  · refine LinearMap.ext fun v => ?_
    have : v ∈ S.toSubmodule := by rw [hS]; trivial
    exact LinearMap.mem_ker.1 this

theorem tempered_lpZero {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) : (WD.lpZero (h := h)).tempered :=
  (WD.tempered_mk _).mpr ((WD.tempered_diag_iff _).mpr fun i => i.elim0)

theorem tempered_sumList {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} :
    ∀ l : List (WD h), (∀ y ∈ l, y.tempered) → (sumList l).tempered
  | [], _ => tempered_lpZero h
  | y :: l, H => tempered_lpSum E Ω A w h y (sumList l) (H y (by simp))
      (tempered_sumList l fun z hz => H z (by simp [hz]))

theorem norm_centralChar_eq_one {k : Type} [CommRing k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] {π : Representation ℂ (GL (Fin n) k) V} {ω : kˣ →* ℂˣ} (hu : IsUnitarisable π)
    (hω : HasCentralChar π ω) (z : kˣ) : ‖(ω z : ℂ)‖ = 1 := by
  obtain ⟨B, -, hpos, hinv⟩ := hu
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 := hinv (Matrix.GeneralLinearGroup.scalar (Fin n) z) v v
  rw [hω] at h1
  simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at h1
  have hB : B v v ≠ 0 := fun h0 => by have := hpos v hv; rw [h0] at this; simp at this
  have h2 : ((ω z : ℂ) * starRingEnd ℂ (ω z : ℂ)) * B v v = 1 * B v v := by linear_combination h1
  have h3 := mul_right_cancel₀ hB h2
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h3
  have h4 : ‖(ω z : ℂ)‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4

theorem norm_eq_one_of_norm_prod {s : Multiset ℂ} (hp : ‖s.prod‖ = 1) (hs : ∀ α ∈ s, ∀ β ∈ s, ‖α‖ = ‖β‖) {α : ℂ}
    (hα : α ∈ s) : ‖α‖ = 1 := by
  have hmap : s.map (fun β => ‖β‖) = Multiset.replicate (Multiset.card s) ‖α‖ := by
    rw [Multiset.eq_replicate]
    refine ⟨by simp, fun r hr => ?_⟩
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hr
    exact (hs α hα β hβ).symm
  have h1 : ‖s.prod‖ = (s.map (fun β => ‖β‖)).prod := map_multiset_prod (normHom : ℂ →*₀ ℝ) s
  rw [hmap, Multiset.prod_replicate, hp] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Multiset.card_pos_iff_exists_mem.2 ⟨α, hα⟩).ne').1 h1.symm

theorem isCosocle_rep_cl {G : Type} [Group G] [TopologicalSpace G] (σ : IrrRep G) {V : Type} [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ G V} (e : σ.ρ.Equiv π) : IsCosocle σ.cl.rep.ρ π := by
  obtain ⟨f⟩ := σ.nonempty_equiv_rep
  exact (isCosocle_self σ.irr).of_equiv f.symm e

theorem norm_eig_segParam {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : IsRec h rc) (δ : IrrGL (k := w.adicCompletion E))
    (Δ : Segment (w.adicCompletion E)) (hΔ : IsLSeg Δ δ.rep) (hu : IsUnitarisable δ.rep) :
    ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1 := by
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  intro φ hφ
  have hz : (rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2) = rc (Δ.first.nu ((((Δ.len : ℝ) - 1) / 2 : ℝ) : ℂ)) :=
    (H.nu_eq _ _).symm
  have hirr : IsIrrWD ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)) := by
    rw [hz]; exact (H.cusp _).1 (Δ.isCusp_first.nu _)
  have hδ : rc δ = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len) := by
    have hL : IsL ((([Δ] : List (Segment (w.adicCompletion E))) : Multiset (Segment (w.adicCompletion E)))) δ.rep := by
      simpa using hΔ.isL
    rw [H.langlands [Δ] δ hL]
    exact WD.lpSum_zero _
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar δ.2.rep.smooth δ.2.rep.irr
  have : Nontrivial δ.2.rep.V := Model.nontrivial_of_isIrreducible δ.2.rep.irr
  have hc := H.central δ ω hω φ
  rw [hδ, prod_eig_lpChar_lpSp] at hc
  have hn : ‖((((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ).prod)‖ ^ Δ.len = 1 := by
    rw [← norm_pow, hc]; exact norm_centralChar_eq_one hu hω _
  have hp1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) Δ.len_pos.ne').1 hn
  intro α hα
  exact norm_eq_one_of_norm_prod hp1 (norm_eig_eq_of_isIrrWD E Ω A w h _ hirr φ hφ) hα

end TemperedRec


open TemperedRec in
theorem tempered_of_isTemperedGL : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ (n : ℕ) (σ : IrrRep (GL (Fin n) (w.adicCompletion E))), GlobalTheory.LocGL.IsTemperedGL σ.ρ → (rc (cls σ)).tempered := by
  intro E Ω _ _ _ _ _ A w h rc hrc n σ hσ
  have hrc' := hrc
  obtain ⟨a, ha, ε, -, H⟩ := hrc'
  obtain ⟨m, δ, hd, hδ, ⟨e⟩⟩ := hσ
  choose Δ hΔ using fun i => (hδ i).1
  have hunit := fun i => norm_eig_segParam hrc (δ i) (Δ i) (hΔ i) (hδ i).2
  have hL : IsL (((List.ofFn Δ : List (Segment (w.adicCompletion E)))) : Multiset (Segment (w.adicCompletion E)))
      (cls σ).rep := by
    refine ⟨m, δ, hd, ⟨Δ, ⟨?_, fun i j _ hp => not_precedes_of_norm_eig E Ω A w h rc hrc (Δ i) (Δ j) (hunit i) (hunit j) hp⟩, hΔ⟩, ?_⟩
    · exact Fin.univ_val_map Δ
    · exact isCosocle_rep_cl σ e
  rw [H.langlands _ _ hL]
  refine tempered_sumList _ fun y hy => ?_
  obtain ⟨Γ, hΓ, rfl⟩ := List.mem_map.1 hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hΓ
  have hz : (rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2) = rc ((Δ i).first.nu (((((Δ i).len : ℝ) - 1) / 2 : ℝ) : ℂ)) :=
    (H.nu_eq _ _).symm
  have hirr : IsIrrWD ((rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2)) := by
    rw [hz]; exact (H.cusp _).1 ((Δ i).isCusp_first.nu _)
  exact tempered_lpChar_lpSp E Ω A w h _ (monodromy_zero_of_irreducible_weilDeligne E Ω A w h _ hirr) (hunit i) _

end GlobalTheory.LocLanglands
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGroupNewtonLiftStep
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.UnitaryNewton

open Formalism.UG GlobalTheory.Hk3.IntWitt GlobalTheory.Hk3.IntWittBase

variable {L : Type} [Field L]

theorem cT_smul' (σ : L →+* L) {n : ℕ} (s : L) (A : Matrix (Fin n) (Fin n) L) :
    cT σ (s • A) = σ s • cT σ A := by ext i j; simp [cT]

theorem cT_add' (σ : L →+* L) {n : ℕ} (A B : Matrix (Fin n) (Fin n) L) :
    cT σ (A + B) = cT σ A + cT σ B := by ext i j; simp [cT]

theorem cT_cT' {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) :
    cT σ (cT σ A) = A := by ext i j; simp [cT, hσ]

theorem newton_identity {n : ℕ} (s c : L) (hc : c + c = 1) (Gc g J X Xc E : Matrix (Fin n) (Fin n) L)
    (h1 : Gc * J * g = J + s • E) (h2 : J * X = -(c • E)) (h3 : Xc * J = -(c • E)) :
    (Gc + s • (Xc * Gc)) * J * (g + s • (g * X)) - J =
      (s * s) • (E * X + Xc * E + Xc * (Gc * J * g) * X) := by
  have e : (Gc + s • (Xc * Gc)) * J * (g + s • (g * X)) =
      Gc * J * g + s • (Gc * J * g * X) + s • (Xc * (Gc * J * g)) + (s * s) • (Xc * (Gc * J * g) * X) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, smul_add]
    abel
  rw [e]
  nth_rewrite 1 [h1]; nth_rewrite 1 [h1]; nth_rewrite 1 [h1]
  rw [Matrix.add_mul, Matrix.mul_add, h2, h3, Matrix.smul_mul, Matrix.mul_smul]
  have hE : (c + c) • E = (1 : L) • E := by rw [hc]
  linear_combination (norm := module) (-s) • hE

end GlobalTheory.Hk3.UnitaryNewton

end

namespace GlobalTheory.Hk3.UnitaryNewton

open Formalism.UG GlobalTheory.Hk3.IntWitt GlobalTheory.Hk3.IntWittBase

theorem newton_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (J : GL (Fin n) L), J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) →
    ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) L), (∀ i j, g i j ∈ Formalism.UG.intL L) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1)
      ((Formalism.UG.cT σ g * (J : Matrix (Fin n) (Fin n) L) * g - (J : Matrix (Fin n) (Fin n) L)) i j)) →
    ∃ g' : Matrix (Fin n) (Fin n) L, (∀ i j, g' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (g' i j - g i j)) ∧
      ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 2)
        ((Formalism.UG.cT σ g' * (J : Matrix (Fin n) (Fin n) L) * g' - (J : Matrix (Fin n) (Fin n) L)) i j) := by
  intro L _ _ ϖ σ q hU hq n J hJ hJh k g hg hD
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -⟩ := hU
  set Jm : Matrix (Fin n) (Fin n) L := (J : Matrix (Fin n) (Fin n) L) with hJm
  set Ji : Matrix (Fin n) (Fin n) L := ((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hJidef
  have hJi : Ji * Jm = 1 := by rw [hJm, hJidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJi' : Jm * Ji = 1 := by rw [hJm, hJidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨g0, hg0⟩ := hJ
  have hJI : ∀ i j, Jm i j ∈ intL L := by
    intro i j; rw [hJm, ← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have hJiI : ∀ i j, Ji i j ∈ intL L := by
    intro i j; rw [hJidef, ← hg0, ← map_inv]
    exact (((g0⁻¹ : GL (Fin n) (intL L)) : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have hJc : cT σ Jm = Jm := by ext i j; rw [cT_apply]; exact hJh j i
  have hJic : cT σ Ji = Ji := by
    have h : cT σ Ji * Jm = 1 := by rw [← hJc, ← cT_mul, hJi', cT_one]
    calc cT σ Ji = cT σ Ji * Jm * Ji := by rw [Matrix.mul_assoc, hJi', Matrix.mul_one]
      _ = Ji := by rw [h, Matrix.one_mul]
  unfold DvdPow at hD
  choose E hE hEeq using hD
  set s : L := ϖ ^ (k + 1) with hs
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖv; exact WithZero.zero_ne_coe hϖv
  have hϖI : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1 from by decide)
  have hs0 : s ≠ 0 := pow_ne_zero _ hϖ0
  have hσs : σ s = s := by rw [hs, map_pow, hσϖ]
  have hsI : s ∈ intL L := (intL L).pow_mem hϖI _
  set Em : Matrix (Fin n) (Fin n) L := Matrix.of E with hEm
  have hEmI : ∀ i j, Em i j ∈ intL L := hE
  have hDE : cT σ g * Jm * g = Jm + s • Em := by
    ext i j
    have := hEeq i j
    rw [Matrix.sub_apply] at this
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hEm, Matrix.of_apply, ← this]; ring
  have hEh : cT σ Em = Em := by
    have h := congrArg (cT σ) hDE
    rw [cT_mul, cT_mul, cT_cT' hσσ, hJc, cT_add', cT_smul', hσs, hJc, ← Matrix.mul_assoc, hDE] at h
    exact (smul_right_injective _ hs0 (add_left_cancel h)).symm
  have h20 : (2 : L) ≠ 0 := by intro h0; rw [h0, map_zero] at h2; exact zero_ne_one h2
  set c : L := (2 : L)⁻¹ with hcdef
  have hc : c + c = 1 := by rw [← two_mul, hcdef, mul_inv_cancel₀ h20]
  have hσc : σ c = c := by rw [hcdef, map_inv₀, map_ofNat]
  have hcI : c ∈ intL L := by
    show Valued.v c ≤ 1
    rw [hcdef, map_inv₀, h2, inv_one]
  set X : Matrix (Fin n) (Fin n) L := (-c) • (Ji * Em) with hX
  have hXI : ∀ i j, X i j ∈ intL L := by
    intro i j; rw [hX, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (neg_mem hcI) (int_mul hJiI hEmI i j)
  have hXc : cT σ X = (-c) • (Em * Ji) := by
    rw [hX, cT_smul', cT_mul, hEh, hJic, map_neg, hσc]
  have hJX : Jm * X = -(c • Em) := by
    rw [hX, Matrix.mul_smul, ← Matrix.mul_assoc, hJi', Matrix.one_mul, neg_smul]
  have hXJ : cT σ X * Jm = -(c • Em) := by
    rw [hXc, Matrix.smul_mul, Matrix.mul_assoc, hJi, Matrix.mul_one, neg_smul]
  refine ⟨g + s • (g * X), ?_, ?_, ?_⟩
  · intro i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (hg i j) (mul_mem hsI (int_mul hg hXI i j))
  · intro i j
    refine ⟨(g * X) i j, int_mul hg hXI i j, ?_⟩
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · have hg'c : cT σ (g + s • (g * X)) = cT σ g + s • (cT σ X * cT σ g) := by
      rw [cT_add', cT_smul', hσs, cT_mul]
    have key := newton_identity s c hc (cT σ g) g Jm X (cT σ X) Em hDE hJX hXJ
    rw [hg'c, key]
    have hgc : ∀ i j, cT σ g i j ∈ intL L := int_cT hσv hg
    have hXcI : ∀ i j, cT σ X i j ∈ intL L := int_cT hσv hXI
    have hR : ∀ i j, (Em * X + cT σ X * Em + cT σ X * (cT σ g * Jm * g) * X) i j ∈ intL L := by
      intro i j
      rw [Matrix.add_apply, Matrix.add_apply]
      exact add_mem (add_mem (int_mul hEmI hXI i j) (int_mul hXcI hEmI i j))
        (int_mul (int_mul hXcI (int_mul (int_mul hgc hJI) hg)) hXI i j)
    intro i j
    refine ⟨ϖ ^ k * (Em * X + cT σ X * Em + cT σ X * (cT σ g * Jm * g) * X) i j,
      mul_mem ((intL L).pow_mem hϖI _) (hR i j), ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, hs]; ring

end GlobalTheory.Hk3.UnitaryNewton
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem weil_rep_equiv_of_charpoly_eq : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (n m : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h (Fin m → ℂ)), (∀ σ : Weil h, (a.ρ σ).charpoly = (b.ρ σ).charpoly) → ∃ e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), ∀ σ z, e (a.ρ σ z) = b.ρ σ (e z) := by
  intro K Ω _ _ _ _ _ A v h n m a b hc
  have ha := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule a.ρ).1
    (GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho K Ω A v h n a)
  have hb := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule b.ρ).1
    (GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho K Ω A v h m b)
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt ℂ (Weil h) _ _ a.ρ b.ρ ha hb hc
  exact ⟨e, fun σ z => LinearMap.congr_fun (he σ) z⟩

end GlobalTheory.AboveL
end

