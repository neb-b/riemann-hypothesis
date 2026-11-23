module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Foundations.FrobLiftWittClosure
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DecayAtCusp
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Decay

theorem per_exists : ∀ (Γ : Subgroup SL(2, ℤ)), Γ.FiniteIndex → ∀ σ : SL(2, ℤ), ∃ n : ℕ, 0 < n ∧ σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹ ∈ Γ := by
  intro Γ hΓ σ
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hΓ.index_ne_zero (σ * ModularGroup.T * σ⁻¹)
  refine ⟨n, hn, ?_⟩
  have : (σ * ModularGroup.T * σ⁻¹) ^ n = σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹ := by
    rw [zpow_natCast, conj_pow]
  rwa [← this]

theorem eichler_mem (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) : eichler w f τ ∈ degreeLT ℂ (w + 1) := by
  unfold eichler
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [mem_degreeLT]
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  have := Finset.mem_range.1 hj
  exact_mod_cast this

theorem per_cov (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (U : ℍ → ℂ[X]) (hU : ∀ τ, U τ ∈ degreeLT ℂ (w + 1))
    (heq : ∀ (γ : Γ) (τ : ℍ), slP w (mat γ) (U ((γ : SL(2, ℤ)) • τ)) = U τ) (σ : SL(2, ℤ)) (n : ℕ)
    (hγ : σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹ ∈ Γ) (τ : ℍ) :
    slP w (mat (ModularGroup.T ^ (n : ℤ))) (slP w (mat σ) (U (σ • (ModularGroup.T ^ (n : ℤ) • τ)))) =
      slP w (mat σ) (U (σ • τ)) := by
  have h1 := heq ⟨_, hγ⟩ (σ • τ)
  have h2 : ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) • σ • τ = σ • (ModularGroup.T ^ (n : ℤ) • τ) := by
    simp only [← mul_smul]; congr 1; group
  rw [h2] at h1
  rw [← h1]
  have hm' : ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ = σ * ModularGroup.T ^ (n : ℤ) := by
    simp only [Subgroup.coe_mk]; group
  have e1 : slP w (mat (ModularGroup.T ^ (n : ℤ))) (slP w (mat σ) (U (σ • ModularGroup.T ^ (n : ℤ) • τ))) =
      slP w (mat (σ * ModularGroup.T ^ (n : ℤ))) (U (σ • ModularGroup.T ^ (n : ℤ) • τ)) := by
    rw [show mat (σ * ModularGroup.T ^ (n : ℤ)) = mat σ * mat (ModularGroup.T ^ (n : ℤ)) from
      Matrix.SpecialLinearGroup.coe_mul _ _, (_root_.GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act w _ _ _ (hU _)).2.1]
  have e2 : slP w (mat σ) (slP w (mat ((⟨_, hγ⟩ : Γ) : SL(2, ℤ))) (U (σ • ModularGroup.T ^ (n : ℤ) • τ))) =
      slP w (mat (((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ)) (U (σ • ModularGroup.T ^ (n : ℤ) • τ)) := by
    rw [show mat (((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ) = mat ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * mat σ from
      Matrix.SpecialLinearGroup.coe_mul _ _, (_root_.GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act w _ _ _ (hU _)).2.1]
  rw [e1, e2, hm']

theorem decay_at_cusp : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)) (p : ℂ[X]), p ∈ degreeLT ℂ (k - 1) → (∀ (γ : Γ) (τ : ℍ), slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ) - (eichler (k - 2) ⇑h ((γ : SL(2, ℤ)) • τ)).map (starRingEnd ℂ) - p) = eichler (k - 2) ⇑f τ - (eichler (k - 2) ⇑h τ).map (starRingEnd ℂ) - p) → ∀ σ : SL(2, ℤ), Filter.Tendsto (fun τ : ℍ => ‖(eichler (k - 2) ⇑f (σ • τ) - (eichler (k - 2) ⇑h (σ • τ)).map (starRingEnd ℂ) - p).eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) UpperHalfPlane.atImInfty (nhds 0) := by
  intro Γ k hΓ hk f h p hp hequiv σ
  have hk2 : 2 ≤ k := by omega
  set w := k - 2 with hw
  have hw1 : 1 ≤ w := by omega
  set U : ℍ → ℂ[X] := fun τ =>
    eichler w ⇑f τ - (eichler w ⇑h τ).map (starRingEnd ℂ) - p with hU
  have hpw : p ∈ degreeLT ℂ (w + 1) := by
    rwa [show w + 1 = k - 1 by omega]
  have hUdeg : ∀ τ, U τ ∈ degreeLT ℂ (w + 1) := by
    intro τ
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (eichler_mem w _ τ) ?_) hpw
    have h0 := eichler_mem w (⇑h) τ
    rw [mem_degreeLT] at h0 ⊢
    exact (degree_map_le).trans_lt h0
  set V : ℍ → ℂ[X] := fun τ => slP w (mat σ) (U (σ • τ)) with hV
  have hVdeg : ∀ τ, V τ ∈ degreeLT ℂ (w + 1) := fun τ => (_root_.GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act w (mat σ) 1 _ (hUdeg _)).1
  have hexp : (-((k : ℝ) - 2) / 2) = -(w : ℝ) / 2 := by
    rw [hw, Nat.cast_sub hk2]; push_cast; ring
  have hfun : (fun τ : ℍ => ‖(U (σ • τ)).eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) =
      fun τ => ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
    funext τ; rw [hexp]; exact _root_.GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow w σ (U (σ • τ)) τ (hUdeg _)
  change Filter.Tendsto (fun τ : ℍ => ‖(U (σ • τ)).eval ((σ • τ : ℍ) : ℂ)‖ *
    (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) _ _
  rw [hfun]
  obtain ⟨n, hn, hγ⟩ := per_exists Γ hΓ σ
  have hVper : ∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ :=
    fun τ => per_cov Γ w U hUdeg hequiv σ n hγ τ
  obtain ⟨hfd, Cf, cf, hcf, hfb⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.cuspForm_slash_holo_decay Γ k hΓ f σ
  obtain ⟨hhd, Ch, ch, hch, hhb⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.cuspForm_slash_holo_decay Γ k hΓ h σ
  obtain ⟨Q, C', c, hQ, hc, hQb⟩ := _root_.GlobalTheory.EichlerLimit.polySlash_eichler_limit k (⇑f) (⇑h) p σ Cf cf Ch ch hk2 hcf hch
    (CuspFormClass.holo f) (CuspFormClass.holo h) hfd hhd hfb hhb hp
  have hQb' : ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w :=
    hQb
  have hQc := _root_.GlobalTheory.HeckeFamilyMatrices.QConst.qconst w n V Q C' c hn hc hQ hVdeg hVper hQb'
  rw [hQc] at hQb'
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨A, hA⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.strip_eval_decay w n (Q.coeff 0) V C' c hw1 hc hVdeg hQb' ε hε
  refine (atImInfty_mem _).2 ⟨A, fun τ hτ => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set m : ℤ := -⌊τ.re / n⌋ with hm
  set τ' : ℍ := ModularGroup.T ^ ((n : ℤ) * m) • τ with hτ'
  have hτ'v : τ' = ((((n : ℤ) * m : ℤ)) : ℝ) +ᵥ τ := modular_T_zpow_smul τ _
  have hre : τ'.re = τ.re + n * m := by
    rw [hτ'v]; simp [add_comm]
  have him : τ'.im = τ.im := by
    rw [hτ'v]; simp
  have hg := _root_.GlobalTheory.HeckeFamilyMatrices.evalDiag_T_invariant w n V hVdeg hVper m τ
  have hfl1 : (⌊τ.re / n⌋ : ℝ) ≤ τ.re / n := Int.floor_le _
  have hfl2 : τ.re / n < ⌊τ.re / n⌋ + 1 := Int.lt_floor_add_one _
  have hr1 : 0 ≤ τ'.re := by
    rw [hre, hm]; push_cast
    have := (le_div_iff₀ hnR).1 hfl1
    nlinarith
  have hr2 : τ'.re ≤ n := by
    rw [hre, hm]; push_cast
    have := (div_lt_iff₀ hnR).1 hfl2
    nlinarith
  have := hA τ' (him ▸ hτ) hr1 hr2
  rw [hg, him] at this
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero]
  rw [abs_of_nonneg (by positivity)]
  exact this

end GlobalTheory.HeckeFamilyMatrices.Decay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOneAddXPow
section
noncomputable section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

open PowerSeries in
private theorem one_add_X_pow_eq_sum_fin_choose {R : Type} [CommRing R] (p j : ℕ) (hj : j < p) :
    (1 + X : R⟦X⟧) ^ j = ∑ i : Fin p, ((j.choose i : ℕ) : R⟦X⟧) * X ^ (i : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((j.choose i : ℕ) : R⟦X⟧) * X ^ i) p, add_comm, add_pow]
  have hsub : Finset.range (j + 1) ⊆ Finset.range p := Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub (fun i _ hi => by
    rw [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, mul_comm]

open PowerSeries in
private theorem subsingleton_of_isUnit_natCast_of_isAdicComplete {R : Type} [CommRing R] (p : ℕ)
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) (hu : IsUnit (p : R)) : Subsingleton R := by
  have htop : Ideal.span {(p : R)} = ⊤ := Ideal.span_singleton_eq_top.2 hu
  constructor
  intro a b
  have h := hR.toIsHausdorff.haus (a - b) (fun n => by
    rw [htop, Ideal.top_pow, Submodule.top_smul]; exact SModEq.top)
  exact sub_eq_zero.1 h


open PowerSeries in
theorem _root_.GlobalTheory.Col.exists_basis_one_add_X_pow (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) :
    ∃ b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      (@Algebra.toModule _ _ _ _ (_root_.GlobalTheory.Col.phi (R := R) p hp.out.pos).toRingHom.toAlgebra), ∀ i, b i = (1 + X) ^ (i : ℕ) := by
  by_cases hn : (p : R) ∈ nonunits R
  · haveI := hR
    set e := _root_.GlobalTheory.Col.Model.basis (R := R) p hn
    have he : ∀ i, e i = _root_.GlobalTheory.Col.Model.toUp p (X ^ (i : ℕ)) := fun i => by
      show (_root_.GlobalTheory.Col.Model.basis (R := R) p hn) i = _
      unfold _root_.GlobalTheory.Col.Model.basis
      rw [Module.Basis.mk_apply]
      rfl
    let v : Fin p → _root_.GlobalTheory.Col.Model.Up R p :=
      fun j => _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (j : ℕ))
    have hv : ∀ j : Fin p, v j = ∑ i : Fin p, (((j : ℕ).choose i : ℕ) : R⟦X⟧) • e i := by
      intro j
      simp only [he, Algebra.smul_def, map_natCast]
      exact one_add_X_pow_eq_sum_fin_choose p j j.2
    have hrepr : ∀ j i : Fin p, e.repr (v j) i = (((j : ℕ).choose i : ℕ) : R⟦X⟧) := by
      intro j i
      rw [hv, e.repr_sum_self]
    have hdet : e.det v = 1 := by
      rw [Module.Basis.det_apply, Matrix.det_of_upperTriangular]
      · simp [Module.Basis.toMatrix_apply, hrepr]
      · intro i j hij
        simp [Module.Basis.toMatrix_apply, hrepr, Nat.choose_eq_zero_of_lt (show (j : ℕ) < i from hij)]
    obtain ⟨hli, hspan⟩ := (Module.Basis.is_basis_iff_det e).2 (by rw [hdet]; exact isUnit_one)
    let b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p) := Module.Basis.mk hli hspan.ge
    have hb : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hli hspan.ge i
    exact ⟨b, hb⟩
  · have hu : IsUnit (p : R) := by simpa [mem_nonunits_iff] using hn
    haveI := subsingleton_of_isUnit_natCast_of_isAdicComplete p hR hu
    haveI : Subsingleton R⟦X⟧ := ⟨fun a b => PowerSeries.ext fun n => Subsingleton.elim _ _⟩
    haveI : Subsingleton (_root_.GlobalTheory.Col.Model.Up R p) := ‹Subsingleton R⟦X⟧›
    haveI : Subsingleton (Fin p →₀ R⟦X⟧) := ⟨fun a b => Finsupp.ext fun i => Subsingleton.elim _ _⟩
    let b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p) :=
      Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _)
    have hb : ∀ i, b i = _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (i : ℕ)) := fun i => Subsingleton.elim _ _
    exact ⟨b, hb⟩

end GlobalTheory.Col
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoxInvariantSnd
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitDict

section Partial

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}

theorem bijOn_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Set.BijOn (fun f : Y → ℂ => f ∘ e) {f | f ∈ SB Y} {f | f ∈ SB X} := by
  refine ⟨fun f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩,
    fun f _ g _ hfg => ?_, fun g hg => ⟨g ∘ e.symm, ⟨hg.1.comp_continuous e.symm.continuous,
      hg.2.comp_homeomorph e.symm⟩, ?_⟩⟩
  · funext y
    simpa using congrFun hfg (e.symm y)
  · funext x
    simp


omit [DecidableEq n] [T2Space T] in
theorem exists_box_invariant_snd {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) :
    ∃ s : kˣ, ∀ u ∈ box n s, ∀ z : T × (n → k), f (z.1, z.2 + u) = f z := by
  obtain ⟨hlc, hcs⟩ := hf
  have hlc2 : IsLocallyConstant fun p : (T × (n → k)) × (n → k) => f (p.1.1, p.1.2 + p.2) - f p.1 :=
    (hlc.comp_continuous (by fun_prop)).sub (hlc.comp_continuous continuous_fst)
  have hW : IsOpen {p : (T × (n → k)) × (n → k) | f (p.1.1, p.1.2 + p.2) - f p.1 = 0} :=
    hlc2.isOpen_fiber 0
  obtain ⟨U, V, -, hV, hKU, h0V, hUV⟩ := generalized_tube_lemma hcs.isCompact (isCompact_singleton (x := (0 : n → k))) hW (by
    rintro ⟨z, u⟩ ⟨-, hu⟩
    simp only [Set.mem_singleton_iff] at hu
    simp [hu])
  obtain ⟨s, hs⟩ := exists_box_subset (hV.mem_nhds (h0V rfl))
  have key : ∀ z ∈ tsupport f, ∀ u ∈ box n s, f (z.1, z.2 + u) = f z := by
    intro z hz u hu
    have hm : (z, u) ∈ {p : (T × (n → k)) × (n → k) | f (p.1.1, p.1.2 + p.2) - f p.1 = 0} :=
      hUV ⟨hKU hz, hs hu⟩
    exact sub_eq_zero.mp hm
  refine ⟨s, fun u hu z => ?_⟩
  by_cases hz : z ∈ tsupport f
  · exact key z hz u hu
  · by_cases hz' : (z.1, z.2 + u) ∈ tsupport f
    · have hneg : -u ∈ box n s := fun i _ => neg_mem_cball (hu i (Set.mem_univ i))
      have := key _ hz' (-u) hneg
      simp only [add_neg_cancel_right, Prod.mk.eta] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

omit [DecidableEq n] [T2Space T] [Fintype n] in
theorem slice_mem_SB {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (t : T) :
    (fun x => f (t, x)) ∈ SB (n → k) := by
  haveI := t2Space k
  refine ⟨hf.1.comp_continuous (by fun_prop),
    HasCompactSupport.intro (hf.2.isCompact.image continuous_snd) fun x hx => ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩

variable [MeasurableSpace k] [BorelSpace k]

def pf (ψ : AddChar k Circle) (μ : Measure (n → k)) (f : T × (n → k) → ℂ) : T × (n → k) → ℂ :=
  fun z => ∫ x, f (z.1, x) * (ψ (x ⬝ᵥ z.2) : ℂ) ∂μ

private theorem exists_isOpen_nhd_eq_of_mem_SB {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (t₀ : T) :
    ∃ V : Set T, IsOpen V ∧ t₀ ∈ V ∧ ∀ t ∈ V, ∀ x, f (t, x) = f (t₀, x) := by
  obtain ⟨hlc, hcs⟩ := hf
  have hW : IsOpen {p : T × (n → k) | f p - f (t₀, p.2) = 0} :=
    (hlc.sub (hlc.comp_continuous (by fun_prop))).isOpen_fiber 0
  obtain ⟨U, V, hU, -, ht₀U, hLV, hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := t₀))
    (hcs.isCompact.image continuous_snd) hW (by
      rintro ⟨t, x⟩ ⟨ht, -⟩
      simp only [Set.mem_singleton_iff] at ht
      simp [ht])
  refine ⟨U, hU, ht₀U rfl, fun t ht x => ?_⟩
  by_cases hx : x ∈ Prod.snd '' tsupport f
  · have hm : (t, x) ∈ {p : T × (n → k) | f p - f (t₀, p.2) = 0} := hUV ⟨ht, hLV hx⟩
    exact sub_eq_zero.mp hm
  · have h1 : (t, x) ∉ tsupport f := fun h => hx ⟨_, h, rfl⟩
    have h2 : (t₀, x) ∉ tsupport f := fun h => hx ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem pf_mem_SB (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c)
    {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) : pf ψ μ f ∈ SB (T × (n → k)) := by
  obtain ⟨s, hs⟩ := exists_box_invariant_snd hf
  have hslice : ∀ t, (fun y => ∫ x, f (t, x) * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (n → k) :=
    fun t => fourier_mem_SB μ h (slice_mem_SB hf t)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    rintro ⟨t₀, y₀⟩
    obtain ⟨V, hV, ht₀, hVf⟩ := exists_isOpen_nhd_eq_of_mem_SB hf t₀
    obtain ⟨O, hO, hy₀, hOf⟩ := (IsLocallyConstant.iff_exists_open _).mp (hslice t₀).1 y₀
    refine ⟨V ×ˢ O, hV.prod hO, ⟨ht₀, hy₀⟩, ?_⟩
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have e1 : pf ψ μ f (t, y) = pf ψ μ f (t₀, y) := by
      simp only [pf]
      congr 1
      funext x
      rw [hVf t ht x]
    rw [e1]
    exact hOf y hy
  · haveI := t2Space k
    refine HasCompactSupport.intro
      ((hf.2.isCompact.image continuous_fst).prod (isCompact_box (c * s⁻¹))) ?_
    rintro ⟨t, y⟩ hty
    rw [Set.mem_prod, not_and_or] at hty
    rcases hty with ht | hy
    · have h0 : ∀ x, f (t, x) = 0 := fun x =>
        image_eq_zero_of_notMem_tsupport fun hx => ht ⟨_, hx, rfl⟩
      simp [pf, h0]
    · show ∫ x, f (t, x) * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0
      exact fourier_eq_zero_pi μ h (f := fun x => f (t, x)) (fun u hu x => hs u hu (t, x)) hy

theorem inversion_const (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => m)) ∂(Measure.pi fun _ => m) =
      (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) * f 0 := by
  haveI := secondCountable k
  obtain ⟨s, hs⟩ := fourier_inversion_pi (Measure.pi fun _ : n => m) h hf
  have hbox : ∀ r : kˣ, (Measure.pi fun _ : n => m).real (box n r) =
      (nabs k r * m.real (𝒪[k] : Set k)) ^ Fintype.card n := by
    intro r
    have hc := measureReal_cball m r
    simp only [Measure.real] at hc ⊢
    rw [box, Measure.pi_pi, ENNReal.toReal_prod, hc, Finset.prod_const, Finset.card_univ]
  have h1 : nabs k s * nabs k (c * s⁻¹) = nabs k c := by
    rw [nabs_mul k, mul_left_comm, ← nabs_mul k, mul_inv_cancel, nabs_one k, mul_one]
  have h2 : nabs k s * m.real (𝒪[k] : Set k) * (nabs k (c * s⁻¹) * m.real (𝒪[k] : Set k)) =
      m.real (𝒪[k] : Set k) ^ 2 * nabs k c := by
    rw [← h1]; ring
  rw [hs, hbox, hbox, ← mul_pow, h2]

omit [T2Space T] in
theorem pf_pf (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (z : T × (n → k)) :
    pf ψ (Measure.pi fun _ => m) (pf ψ (Measure.pi fun _ => m) f) z =
      (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) * f (z.1, -z.2) := by
  haveI := secondCountable k
  obtain ⟨t, y⟩ := z
  have hsl := slice_mem_SB hf t
  have hg : (fun w => f (t, w - y)) ∈ SB (n → k) :=
    ⟨hsl.1.comp_continuous (continuous_sub_right y), hsl.2.comp_homeomorph (Homeomorph.subRight y)⟩
  have hinv := inversion_const m h hg
  simp only [zero_sub] at hinv
  show ∫ x, (∫ w, f (t, w) * (ψ (w ⬝ᵥ x) : ℂ) ∂(Measure.pi fun _ => m)) * (ψ (x ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => m) = _ * f (t, -y)
  rw [← hinv]
  congr 1
  funext x
  rw [← integral_mul_const]
  have e := integral_sub_right_eq_self (μ := Measure.pi fun _ : n => m)
    (fun u => f (t, u) * (ψ ((u + y) ⬝ᵥ x) : ℂ)) y
  simp only [sub_add_cancel] at e
  rw [e]
  congr 1
  funext u
  rw [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dotProduct_comm y x]
  ring

theorem pf_bijOn (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c) :
    Set.BijOn (pf ψ (Measure.pi fun _ => m)) {f | f ∈ SB (T × (n → k))} {f | f ∈ SB (T × (n → k))} := by
  haveI := secondCountable k
  set C : ℂ := (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) with hC
  have hC0 : C ≠ 0 := by
    have h1 : 0 < m.real (𝒪[k] : Set k) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos ((isOpen_int k).measure_ne_zero m ⟨0, by simp⟩)
        (isCompact_int k).measure_lt_top.ne
    have h2 := nabs_pos k c
    rw [hC]
    exact Complex.ofReal_ne_zero.mpr (pow_pos (mul_pos (pow_pos h1 2) h2) _).ne'
  have hsmul : ∀ (a : ℂ) (g : T × (n → k) → ℂ), pf ψ (Measure.pi fun _ : n => m) (a • g) = a • pf ψ (Measure.pi fun _ : n => m) g := by
    intro a g
    funext z
    simp only [pf, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul a _
  have hpp : ∀ g ∈ SB (T × (n → k)), ∀ z, pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) g) z = C * g (z.1, -z.2) :=
    fun g hg z => pf_pf m h hg z
  refine ⟨fun g hg => pf_mem_SB (Measure.pi fun _ : n => m) h hg, fun g hg g' hg' hgg => ?_, fun g hg => ?_⟩
  · funext z
    have e1 := hpp g hg (z.1, -z.2)
    have e2 := hpp g' hg' (z.1, -z.2)
    rw [hgg] at e1
    simp only [neg_neg, Prod.mk.eta] at e1 e2
    exact mul_left_cancel₀ hC0 (e1.symm.trans e2)
  · have h2 := pf_mem_SB (Measure.pi fun _ : n => m) h (pf_mem_SB (Measure.pi fun _ : n => m) h hg)
    refine ⟨(C ^ 2)⁻¹ • pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) g)), (SB _).smul_mem _ (pf_mem_SB (Measure.pi fun _ : n => m) h h2), ?_⟩
    rw [hsmul]
    funext z
    rw [Pi.smul_apply, hpp _ h2, hpp _ hg]
    simp only [neg_neg, Prod.mk.eta, smul_eq_mul]
    field_simp

end Partial

section Matrices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable [MeasurableSpace k] [BorelSpace k]

end Matrices

section Homeos

variable (k : Type) [TopologicalSpace k] (ρ v τ w W : Type)

end Homeos

section Main

variable {k : Type} [Field k]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

variable (ψ : AddChar k Circle) (m : Measure k) [m.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (s₁ s₂ : ℤˣ)
variable {ρ v τ w W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
  [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w] [Fintype W] [DecidableEq W]



end Main

end GlobalTheory.SplitDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleExtensionOfNegCentralElement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem exists_cocycle_extension_of_neg_action : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ φ : G → V, (∀ δ ∈ Δ, φ δ ∈ S) → (∀ δ ∈ Δ, ∀ δ' ∈ Δ, φ (δ * δ') = φ δ + φ δ') → (∀ g, ∀ δ ∈ Δ, ρ g (φ (g * δ * g⁻¹)) = φ δ) → ∃ z : G → V, (∀ g, z g ∈ S) ∧ (∀ g h, z (g * h) = ρ h (z g) + z h) ∧ ∀ δ ∈ Δ, z δ = φ δ := by
  intro G _ R _ V _ _ ρ hmul hone h2 S hS Δ hΔ hΔtriv c hc hk φ hφS hφadd hφinv
  obtain ⟨u, hu⟩ := h2
  have hinv : ∀ g v, ρ g (ρ g⁻¹ v) = v := by
    intro g v; rw [← hmul, inv_mul_cancel, hone]
  have hconj : ∀ g, ∀ δ ∈ Δ, φ (g * δ * g⁻¹) = ρ g⁻¹ (φ δ) := by
    intro g δ hδ
    rw [← hφinv g δ hδ, ← hmul, mul_inv_cancel, hone]
  have hkmul : ∀ g h : G, c * (g * h) * c⁻¹ * (g * h)⁻¹
      = (c * g * c⁻¹ * g⁻¹) * (g * (c * h * c⁻¹ * h⁻¹) * g⁻¹) := by
    intro g h; group
  have hw : ∀ g h : G, ρ (g * h) (φ (c * (g * h) * c⁻¹ * (g * h)⁻¹))
      = ρ h (ρ g (φ (c * g * c⁻¹ * g⁻¹))) + ρ h (φ (c * h * c⁻¹ * h⁻¹)) := by
    intro g h
    rw [hkmul, hφadd _ (hk g) _ (hΔ.conj_mem _ (hk h) g), hconj g _ (hk h), hmul,
      map_add, map_add, hinv]
  have h1 : φ 1 = 0 := by
    have := hφadd 1 Δ.one_mem 1 Δ.one_mem
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hneg : ∀ δ ∈ Δ, φ δ⁻¹ = -φ δ := by
    intro δ hδ
    have := hφadd δ hδ δ⁻¹ (Δ.inv_mem hδ)
    rw [mul_inv_cancel, h1] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  refine ⟨fun g => -(↑u⁻¹ : R) • ρ g (φ (c * g * c⁻¹ * g⁻¹)), ?_, ?_, ?_⟩
  · intro g
    exact S.smul_mem _ (hS g _ (hφS _ (hk g)))
  · intro g h
    simp only
    rw [hw, smul_add, map_smul]
  · intro δ hδ
    simp only
    have hcδ : c * δ * c⁻¹ ∈ Δ := hΔ.conj_mem _ hδ c
    have hc' : φ (c * δ * c⁻¹) = -φ δ := by
      have e1 := hφinv c δ hδ
      rw [hc _ (hφS _ hcδ)] at e1
      rw [← e1, neg_neg]
    rw [hΔtriv δ hδ, hφadd _ hcδ _ (Δ.inv_mem hδ), hc', hneg δ hδ,
      show -φ δ + -φ δ = -((2 : R) • φ δ) by rw [two_smul, neg_add],
      smul_neg, neg_smul, neg_neg, smul_smul, ← hu, Units.inv_mul, one_smul]

end GlobalTheory.KZ.H3
end

