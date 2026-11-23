module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodOneGenus
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.StdLatEqSpan
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsExactIdeal
section
open NumberField Module IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Dedekind

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem count_span_unit (v : HeightOneSpectrum R) (s : R) (hs : s ∉ v.asIdeal) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K s)) = 0 := by
  have hs0 : s ≠ 0 := fun h => hs (h ▸ v.asIdeal.zero_mem)
  have hsp : Ideal.span {s} ≠ ⊥ := by simpa using hs0
  rw [← FractionalIdeal.coeIdeal_span_singleton, count_coe_eq_multiplicity v hsp]
  have : multiplicity v.asIdeal (Ideal.span {s}) = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  simp [this]

theorem count_le_of_mem (v : HeightOneSpectrum R) {I : FractionalIdeal (nonZeroDivisors R) K} {y : K}
    (hy : y ∈ I) (hy0 : y ≠ 0) :
    FractionalIdeal.count K v I ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ y) :=
  FractionalIdeal.count_mono K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy0)
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr hy)

theorem exists_exact_ideal (v : HeightOneSpectrum R) (T : Finset R) (hT : T.Nonempty) (h0 : ∀ g ∈ T, g ≠ 0) :
    ∃ g ∈ T, multiplicity v.asIdeal (Ideal.span {g}) = multiplicity v.asIdeal (Ideal.span (T : Set R)) := by
  classical
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, Finset.mem_singleton_self a, by simp⟩
  | cons a T ha hT ih =>
    have hT0 : ∀ g ∈ T, g ≠ 0 := fun g hg => h0 g (Finset.mem_cons_of_mem hg)
    obtain ⟨g, hg, hgm⟩ := ih hT0
    have ha0 : Ideal.span {a} ≠ ⊥ := by simpa using h0 a (Finset.mem_cons_self a T)
    have hT' : Ideal.span (T : Set R) ≠ ⊥ := by
      intro hb
      have : g ∈ Ideal.span (T : Set R) := Ideal.subset_span hg
      rw [hb, Ideal.mem_bot] at this
      exact hT0 g hg this
    have hspan : Ideal.span ((Finset.cons a T ha : Finset R) : Set R) = Ideal.span {a} ⊔ Ideal.span (T : Set R) := by
      rw [Finset.coe_cons, Ideal.span_insert]
    rw [hspan, HeightOneSpectrum.multiplicity_sup v ha0 hT']
    rcases le_total (multiplicity v.asIdeal (Ideal.span {a})) (multiplicity v.asIdeal (Ideal.span (T : Set R))) with h | h
    · exact ⟨a, Finset.mem_cons_self a T, (min_eq_left h).symm⟩
    · exact ⟨g, Finset.mem_cons_of_mem hg, by rw [min_eq_right h, hgm]⟩

theorem exists_exact (v : HeightOneSpectrum R) {I : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) :
    ∃ y ∈ I, y ≠ 0 ∧
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors R) y) = FractionalIdeal.count K v I := by
  classical
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    apply hI
    rw [hIJ, FractionalIdeal.coeIdeal_bot, mul_zero]
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian J : J.FG)
  set T' := T.filter (· ≠ 0)
  have hT' : Ideal.span (T' : Set R) = J := by
    rw [← hT]
    apply le_antisymm
    · exact Ideal.span_mono (by intro z hz; exact (Finset.mem_filter.mp hz).1)
    · rw [Ideal.span_le]
      intro z hz
      by_cases hz0 : z = 0
      · rw [hz0]; exact Ideal.zero_mem _
      · exact Ideal.subset_span (Finset.mem_filter.mpr ⟨hz, hz0⟩)
  have hne : T'.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hJ0
    rw [← hT', hemp, Finset.coe_empty, Ideal.span_empty]
  obtain ⟨g, hgT, hgm⟩ := exists_exact_ideal v T' hne (fun g hg => (Finset.mem_filter.mp hg).2)
  have hg0 : g ≠ 0 := (Finset.mem_filter.mp hgT).2
  have hgJ : g ∈ J := hT' ▸ Ideal.subset_span hgT
  have ha' : algebraMap R K a ≠ 0 := (IsFractionRing.injective R K).ne_iff.mpr ha |>.trans_eq (map_zero _) |> fun h => by
    simpa using (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr ha
  have hg' : algebraMap R K g ≠ 0 := (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hg0
  refine ⟨(algebraMap R K a)⁻¹ * algebraMap R K g, ?_, mul_ne_zero (inv_ne_zero ha') hg', ?_⟩
  · rw [hIJ]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hgJ)
  · have hsa : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a)⁻¹ ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero ha')
    have hsg : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K g) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hg'
    have hJc : (J : FractionalIdeal (nonZeroDivisors R) K) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have hsp : Ideal.span {g} ≠ ⊥ := by simpa using hg0
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K v hsa hsg, hIJ,
      FractionalIdeal.count_mul K v hsa hJc, ← FractionalIdeal.coeIdeal_span_singleton,
      count_coe_eq_multiplicity v hsp, count_coe_eq_multiplicity v hJ0, hgm, hT']

theorem prod_mem_prod' {ι : Type*} (s : Finset ι) (𝔞 : ι → FractionalIdeal (nonZeroDivisors R) K)
    (m : ι → K) (hm : ∀ i, m i ∈ 𝔞 i) : ∏ i ∈ s, m i ∈ ∏ i ∈ s, 𝔞 i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact FractionalIdeal.mul_mem_mul (hm j) ih

theorem det_mem_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔞 : ι → FractionalIdeal (nonZeroDivisors R) K)
    (M : Matrix ι ι K) (hM : ∀ i k, M i k ∈ 𝔞 i) : M.det ∈ ∏ i, 𝔞 i := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hp : ∏ i, M (σ i) i ∈ ∏ i, 𝔞 i := by
    have : ∏ i, M (σ i) i = ∏ j, M j (σ.symm j) := by
      rw [← Equiv.prod_comp σ (fun j => M j (σ.symm j))]
      simp
    rw [this]
    exact prod_mem_prod' _ 𝔞 _ fun j => hM j _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul]; exact Submodule.neg_mem _ hp

end Dedekind

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GESymmApply
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Form

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem hWb_swap (x y : WbQ D F0) : hWb D F0 y x = star (hWb D F0 x y) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [hWb_mk, hWb_mk]
  exact PI.ScalarPairDr.W.hT_swap _ _ _

theorem hWb_sepR (y : WbQ D F0) (hy : ∀ x, hWb D F0 x y = 0) : y = 0 := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  show (b : (VS D).V) ∈ F0.X
  have h2 : (b : (VS D).V) ∈ orth (VS D) (orth (VS D) F0.X) := by
    rw [PI.ScalarPairDr.W.mem_orth]
    intro x hx
    rw [← perpS_eq_orth] at hx
    have h3 := hy (Submodule.Quotient.mk ⟨x, hx⟩)
    rwa [hWb_mk] at h3
  rw [PI.ScalarPairDr.W.orth_orth] at h2
  exact h2

theorem hWb_eq_of (x y : WbQ D F0) (h : ∀ a, hWb D F0 a x = hWb D F0 a y) : x = y := by
  refine sub_eq_zero.1 (hWb_sepR D F0 (x - y) (fun a => ?_))
  rw [map_sub, h a, sub_self]

theorem exists_u (sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X) :
    ∃ u : (VS D).V →ₗ[D.host.E] WbQ D F0,
      ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v := by
  classical
  let b := Module.finBasis D.host.E (WbQ D F0)
  let M : WbQ D F0 →ₗ[D.host.E] (Fin (Module.finrank D.host.E (WbQ D F0)) → D.host.E) :=
    LinearMap.pi (fun i => hWb D F0 (b i))
  have hMinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, hWb D F0 (b i) y = 0 := fun i => congrFun hy i
    apply hWb_sepR D F0 y
    intro a
    rw [← b.sum_repr a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy',
      smul_zero, Finset.sum_const_zero]
  have hMsurj : Function.Surjective M :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hMinj
  obtain ⟨Me, hMe⟩ : ∃ Me : WbQ D F0 ≃ₗ[D.host.E] (Fin (Module.finrank D.host.E (WbQ D F0)) → D.host.E),
      ∀ x, Me x = M x := ⟨LinearEquiv.ofBijective M ⟨hMinj, hMsurj⟩, fun x => rfl⟩
  let g : (VS D).V →ₗ[D.host.E] (Fin (Module.finrank D.host.E (WbQ D F0)) → D.host.E) :=
    LinearMap.pi (fun i => (VS D).hT (sE (b i) : (VS D).V))
  refine ⟨Me.symm.toLinearMap ∘ₗ g, fun a v => ?_⟩
  have key : ∀ i, hWb D F0 (b i) (Me.symm (g v)) = (VS D).hT (sE (b i) : (VS D).V) v := by
    intro i
    have h := hMe (Me.symm (g v))
    rw [Me.apply_symm_apply] at h
    exact (congrFun h i).symm
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← b.sum_repr a]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, map_smul, Submodule.coe_smul, key]

end Form

section Gamma

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def gF (sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X) (u : (VS D).V →ₗ[D.host.E] WbQ D F0)
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id + (perpS (VS D) F0.X).subtype ∘ₗ sE ∘ₗ
    ((σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) - LinearMap.id) ∘ₗ u

variable {D F0}
variable {sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X} {u : (VS D).V →ₗ[D.host.E] WbQ D F0}

theorem gF_apply (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) (v : (VS D).V) :
    gF D F0 sE u σ v = v + (sE (σ (u v) - u v) : (VS D).V) := by
  rfl

theorem u_perp (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (y : perpS (VS D) F0.X) :
    u y = Submodule.Quotient.mk y := by
  apply hWb_eq_of D F0
  intro a
  rw [hu]
  conv_rhs => rw [← hsE a]
  rw [hWb_mk]

theorem u_sE (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (b : WbQ D F0) :
    u (sE b : (VS D).V) = b := by
  rw [u_perp hsE hu (sE b), hsE b]

theorem u_X (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) {x : (VS D).V} (hx : x ∈ F0.X) :
    u x = 0 := by
  apply hWb_sepR D F0
  intro a
  rw [hu]
  exact hT_perp_X D F0 (sE a).2 hx

theorem u_gF (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (v : (VS D).V) : u (gF D F0 sE u σ v) = σ (u v) := by
  rw [gF_apply, map_add (f := _), u_sE hsE hu]
  abel

theorem gF_symm (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (v : (VS D).V) : gF D F0 sE u σ.symm (gF D F0 sE u σ v) = v := by
  rw [gF_apply σ.symm (gF D F0 sE u σ v), u_gF hsE hu σ v, LinearEquiv.symm_apply_apply, gF_apply σ v,
    show u v - σ (u v) = -(σ (u v) - u v) by abel, map_neg, Submodule.coe_neg, add_neg_cancel_right]

def gE (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) :
    (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (gF D F0 sE u σ) (gF D F0 sE u σ.symm)
    (by
      ext v
      have := gF_symm hsE hu σ.symm v
      rwa [LinearEquiv.symm_symm] at this)
    (by
      ext v
      exact gF_symm hsE hu σ v)

theorem gE_symm_apply (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (v : (VS D).V) : (gE hsE hu σ).symm v = gF D F0 sE u σ.symm v := rfl

theorem gF_isom (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (hσ : ∀ x y, hWb D F0 (σ x) (σ y) = hWb D F0 x y) (v w : (VS D).V) :
    (VS D).hT (gF D F0 sE u σ v) (gF D F0 sE u σ w) = (VS D).hT v w := by
  rw [gF_apply, gF_apply]
  have h1 : ∀ c x, (VS D).hT x (sE c : (VS D).V) = hWb D F0 (u x) c := by
    intro c x
    rw [PI.ScalarPairDr.W.hT_swap (VS D) (sE c : (VS D).V) x, ← hu, ← hWb_swap D F0 c (u x)]
  have h2 : ∀ c x, (VS D).hT (sE c : (VS D).V) x = hWb D F0 c (u x) := fun c x => (hu c x).symm
  have h3 : ∀ c c', (VS D).hT (sE c : (VS D).V) (sE c' : (VS D).V) = hWb D F0 c c' := by
    intro c c'
    rw [h2, u_sE hsE hu]
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [h3, h1, h2]
  simp only [map_sub, LinearMap.sub_apply, hσ]
  ring

end Gamma

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.PartnerVectorExists
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem hT_sub_sum_left {r : ℕ} (x w : S.V) (c : Fin r → E) (y : Fin r → S.V) :
    S.hT (x - ∑ d, c d • y d) w = S.hT x w - ∑ d, star (c d) * S.hT (y d) w := by
  first
  | simp [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  | simp [map_sub, map_sum, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem hT_sub_sum_right {r : ℕ} (x w : S.V) (c : Fin r → E) (y : Fin r → S.V) :
    S.hT w (x - ∑ d, c d • y d) = S.hT w x - ∑ d, c d * S.hT w (y d) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sub, map_sum, map_smul, smul_eq_mul]

theorem coord_surj {r : ℕ} {T : E} (F0 : FlagG S r T) :
    Function.Surjective (LinearMap.pi (fun a => S.hT (F0.e a)) : S.V →ₗ[E] (Fin r → E)) := by
  classical
  by_contra hns
  have hlt : LinearMap.range (LinearMap.pi (fun a => S.hT (F0.e a)) : S.V →ₗ[E] (Fin r → E)) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hns (LinearMap.range_eq_top.mp h)
  obtain ⟨ψ, hψne, hψ⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  have key : ∀ x : S.V, ∑ a, ψ (Pi.single a 1) * S.hT (F0.e a) x = 0 := by
    intro x
    have hx := hψ (LinearMap.mem_range_self (LinearMap.pi (fun a => S.hT (F0.e a)) : S.V →ₗ[E] (Fin r → E)) x)
    rw [LinearMap.mem_ker] at hx
    have hdec : (LinearMap.pi (fun a => S.hT (F0.e a)) : S.V →ₗ[E] (Fin r → E)) x
        = ∑ a, S.hT (F0.e a) x • (Pi.single a 1 : Fin r → E) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hdec, map_sum] at hx
    simpa [map_smul, smul_eq_mul, mul_comm] using hx
  have hv : (∑ a, star (ψ (Pi.single a 1)) • F0.e a) = 0 := by
    apply S.nondeg.1
    intro x
    first
    | simpa [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply, star_star] using key x
    | simpa [map_sum, LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply, star_star] using key x
  have hc : ∀ a, ψ (Pi.single a 1) = 0 := by
    intro a
    have h0 := (Fintype.linearIndependent_iff.mp F0.e_indep) _ hv a
    simpa using h0
  apply hψne
  apply LinearMap.pi_ext
  intro i x
  have hs : (Pi.single i x : Fin r → E) = x • (Pi.single i 1 : Fin r → E) := by
    ext j
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  rw [hs, map_smul, hc i]
  simp

private theorem star_hT_eq_hT_swap (x y : S.V) : star (S.hT x y) = S.hT y x := by
  have h : starRingEnd E (S.hT x y) = S.hT y x := by
    first
    | exact S.herm.eq x y
    | exact S.herm x y
  simpa [starRingEnd_apply] using h

theorem partner_exists {r : ℕ} {T : E} (F0 : FlagG S r T) (hT0 : T ≠ 0) :
    ∃ f : Fin r → S.V, (∀ a b, S.hT (F0.e a) (f b) = if a = b then 1 else 0) ∧
      (∀ a b, S.hT (f a) (f b) = 0) ∧ ∀ a, S.hT (f a) F0.z = 0 := by
  classical
  have hE : ∀ b, ∃ g0 : S.V, ∀ a, S.hT (F0.e a) g0 = if a = b then 1 else 0 := by
    intro b
    obtain ⟨g0, hg0⟩ := coord_surj S F0 (fun a => if a = b then (1 : E) else 0)
    refine ⟨g0, fun a => ?_⟩
    have h1 := congrFun hg0 a
    simpa using h1
  choose g0 hg0 using hE
  have hZ : S.hT F0.z F0.z ≠ 0 := by
    rw [F0.z_norm]
    exact neg_ne_zero.mpr hT0
  set g : Fin r → S.V := fun b => g0 b - (S.hT F0.z (g0 b) / S.hT F0.z F0.z) • F0.z with hgdef
  have hgE : ∀ a b, S.hT (F0.e a) (g b) = if a = b then 1 else 0 := by
    intro a b
    simp [g, map_sub, map_smul, smul_eq_mul, F0.z_orth, hg0]
  have hgZ : ∀ b, S.hT F0.z (g b) = 0 := by
    intro b
    simp only [g, map_sub, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hZ, sub_self]
  have hZg : ∀ b, S.hT (g b) F0.z = 0 := by
    intro b
    rw [← star_hT_eq_hT_swap, hgZ, star_zero]
  have hgeE : ∀ a d, S.hT (g a) (F0.e d) = if d = a then 1 else 0 := by
    intro a d
    rw [← star_hT_eq_hT_swap, hgE]
    split_ifs <;> simp
  set c : Fin r → Fin r → E := fun b d => S.hT (g d) (g b) / 2 with hcdef
  have hf1 : ∀ a b, S.hT (F0.e a) (g b - ∑ d, c b d • F0.e d) = if a = b then 1 else 0 := by
    intro a b
    rw [hT_sub_sum_right]
    simp [hgE, F0.e_iso]
  refine ⟨fun b => g b - ∑ d, c b d • F0.e d, hf1, ?_, ?_⟩
  · intro a b
    rw [hT_sub_sum_left]
    simp only [hf1]
    rw [hT_sub_sum_right]
    simp only [hgeE, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hs : star (c a b) = S.hT (g a) (g b) / 2 := by
      simp only [c]
      rw [← star_hT_eq_hT_swap (S := S) (g a) (g b)]
      first
      | simp [star_div₀]
      | simp [star_div']
      | simp
    rw [hs]
    simp only [c]
    ring
  · intro a
    rw [hT_sub_sum_left]
    simp [hZg, F0.z_orth]

end Gen

theorem partner_vector_exists : PartnerEx := by
  intro D u F0
  refine partner_exists (VS D) F0 ?_
  unfold Tn
  exact_mod_cast (D.mem u).A.T_prime.ne_zero

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodularOneGenus
section
open NumberField

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

open Formalism.HermitianLattices.Ext.L3.WA

theorem unimodOneGenus_of (hP : PairUnitLoc) : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.UnimodOneGenus := by
  intro K _ _ _ V _ _ _ _ _ h hK hs hnd L M hLl hMl hLu hMu p hp
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    PI.UG.W.star_mem_range K
  have huL := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs hstar L hLl.fg).2.mp hLu p hp
  have huM := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs hstar M hMl.fg).2.mp hMu p hp
  have hS := isHermSemilocal_locRing hK hp
  have hLfull : Submodule.IsFullLattice K L :=
    { toIsLattice := hLl
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs hnd hLl hLu }
  have hMfull : Submodule.IsFullLattice K M :=
    { toIsLattice := hMl
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs hnd hMl hMu }
  have hL' := isSelfDualMod_loc hLfull hp.isPrime huL
  have hM' := isSelfDualMod_loc hMfull hp.isPrime huM
  obtain ⟨g, hg, hiff⟩ := exists_isom_selfDual hS hs hnd
    (fun w y hyw hw hy => hP K hK p hp V h hs w y hyw hw hy) hL' hM'
  refine ⟨g, hg, ?_⟩
  ext w
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (hiff v).1 hv
  · intro hw
    refine ⟨g.symm w, (hiff _).2 ?_, by simp⟩
    simpa using hw

theorem unimodular_one_genus : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.UnimodOneGenus :=
  unimodOneGenus_of pair_unit_local

end PI.UnitaryGroupMassFormula.CntFormula.UG
end
end

