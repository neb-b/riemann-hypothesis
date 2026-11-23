module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfForallApprox
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLocApprox

theorem integral_eq_zero_of_forall_approx {X : Type} [MeasurableSpace X] {μ : Measure X} {v : X → ℂ} {w : X → ℝ}
    (hw : Integrable w μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ u : X → ℂ, Integrable u μ ∧ ∫ x, u x ∂μ = 0 ∧ ∀ x, ‖u x - v x‖ ≤ ε * w x) :
    ∫ x, v x ∂μ = 0 := by
  by_cases hv : Integrable v μ
  swap
  · exact integral_undef hv
  have key : ∀ ε : ℝ, 0 < ε → ‖∫ x, v x ∂μ‖ ≤ ε * ∫ x, w x ∂μ := fun ε hε => by
    obtain ⟨u, hu, h0, hn⟩ := h ε hε
    have e : ∫ x, (u x - v x) ∂μ = -∫ x, v x ∂μ := by rw [integral_sub hu hv, h0, zero_sub]
    rw [← norm_neg, ← e, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul ε) (Filter.Eventually.of_forall hn)
  have t : Filter.Tendsto (fun ε : ℝ => ε * ∫ x, w x ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * ∫ x, w x ∂μ)) :=
    ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul] at t
  exact norm_le_zero_iff.1 (ge_of_tendsto t (eventually_nhdsWithin_of_forall key))

variable {D : D7} {V : HSp D}

def LocApprox (V : HSp D) (f : GA D V → ℂ) : Prop :=
  ∀ C : Set (GA D V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (ψ : Fin n → GA D V → ℂ),
    (∀ l, Continuous (ψ l) ∧ (∀ γ ∈ GQ V, ∀ g, ψ l (γ * g) = ψ l g) ∧ IsCuspFun V (ψ l)) ∧
    ∀ x ∈ C, ‖f x - ∑ l, ψ l x‖ < ε

theorem leftInv_of_locApprox {f : GA D V → ℂ} (h : LocApprox V f) : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g := by
  intro γ hγ g
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨n, ψ, hψ, happ⟩ := h {γ * g, g} (Set.toFinite _).isCompact (ε / 2) (by positivity)
  have e : ∑ l, ψ l (γ * g) = ∑ l, ψ l g := Finset.sum_congr rfl fun l _ => (hψ l).2.1 γ hγ g
  have h1 := happ (γ * g) (by simp)
  have h2 := happ g (by simp)
  rw [dist_eq_norm]
  have e' : f (γ * g) - f g = (f (γ * g) - ∑ l, ψ l (γ * g)) - (f g - ∑ l, ψ l g) := by rw [e]; ring
  rw [e']
  linarith [norm_sub_le (f (γ * g) - ∑ l, ψ l (γ * g)) (f g - ∑ l, ψ l g)]

theorem isCuspFun_of_locApprox {f : GA D V → ℂ} (h : LocApprox V f) : IsCuspFun V f := by
  have hl := leftInv_of_locApprox h
  rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ x, φ (γ * x) = φ x) →
      IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl'
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl'
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl' μ hμ 𝓕 h𝓕 g
  obtain ⟨K, hK, hKs⟩ := GlobalTheory.AutFunCompare.unipRad_cocompact D.sp.cm V W hW
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have hcont : Continuous fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g :=
    continuous_subtype_val.mul continuous_const
  have hw : Integrable (fun _ : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (1 : ℝ)) (μ.restrict 𝓕) := by
    simpa using (hint (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl).norm
  refine integral_eq_zero_of_forall_approx (μ := μ.restrict 𝓕) (v := fun n => f (n.1 * g)) hw fun ε hε => ?_
  obtain ⟨m, ψ, hψ, happ⟩ := h _ (hK.image hcont) ε hε
  refine ⟨fun n => ∑ l, ψ l (n.1 * g), integrable_finsetSum _ fun l _ => hint _ (hψ l).1 (hψ l).2.1, ?_,
    fun n => ?_⟩
  · rw [integral_finsetSum _ fun l _ => hint _ (hψ l).1 (hψ l).2.1]
    exact Finset.sum_eq_zero fun l _ =>
      (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V _).1 (hψ l).2.2 W hW μ hμ 𝓕 h𝓕 g
  · obtain ⟨γ, hγ, hk⟩ := hKs n
    have e1 : f (n.1 * g) = f ((γ * n).1 * g) := by
      rw [Subgroup.coe_mul, mul_assoc]; exact (hl _ hγ _).symm
    have e2 : ∀ l, ψ l (n.1 * g) = ψ l ((γ * n).1 * g) := fun l => by
      have hl' := (hψ l).2.1
      rw [GlobalTheory.AutFunCompare.GQ_eq] at hl'
      rw [Subgroup.coe_mul, mul_assoc]; exact (hl' _ hγ _).symm
    show ‖∑ l, ψ l (n.1 * g) - f (n.1 * g)‖ ≤ ε * 1
    rw [e1, Finset.sum_congr rfl fun l _ => e2 l, mul_one, norm_sub_rev]
    exact (happ _ ⟨_, hk, rfl⟩).le

end GlobalTheory.CuspLocApprox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfApproxAlt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspApproxCompact

theorem isCuspFun_of_approx (D : D7) (V : HSp D) (f : GA D V → ℂ) (hf : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g)
    (ha : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ ψ : GA D V → ℂ, Continuous ψ ∧
      (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) ∧ IsCuspFun V ψ ∧ ∀ h ∈ C, ‖f h - ψ h‖ < δ) :
    IsCuspFun V f := by
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
      ∀ W, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W → ∀ μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarMeasure →
      ∀ 𝓕, IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRat D.sp.cm V W) 𝓕 μ → ∀ g : GA D V,
        IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl W hW μ hμ 𝓕 h𝓕 g
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl μ hμ 𝓕 h𝓕 g
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.AutFunCompare.unipRad_cocompact D.sp.cm V W hW
  have hcont : Continuous fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g := by
    have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    have : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    exact continuous_subtype_val.mul continuous_const
  have hC : IsCompact ((fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g) '' K) :=
    hK.image hcont
  have h1 := hint (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl) W hW μ hμ 𝓕 h𝓕 g
  have hfin : μ 𝓕 < ⊤ := by
    rcases (integrableOn_const_iff (C := (1 : ℂ))).1 h1 with h | h
    · exact absurd h (by simp)
    · exact h
  have hM0 : 0 ≤ μ.real 𝓕 := measureReal_nonneg
  have key : ∀ δ : ℝ, 0 < δ → ‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ ≤ δ * μ.real 𝓕 := by
    intro δ hδ
    obtain ⟨ψ, hψc, hψl, hψcusp, hψ⟩ := ha _ hC δ hδ
    have h0 := (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V ψ).1 hψcusp W hW μ hμ 𝓕 h𝓕 g
    have hfi := hint f hf hl W hW μ hμ 𝓕 h𝓕 g
    have hψi := hint ψ hψc hψl W hW μ hμ 𝓕 h𝓕 g
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm at h0 ⊢
    have e : ∫ n in 𝓕, f ((n : GA D V) * g) ∂μ = ∫ n in 𝓕, (f ((n : GA D V) * g) - ψ ((n : GA D V) * g)) ∂μ := by
      rw [integral_sub hfi hψi, h0, sub_zero]
    rw [e]
    refine norm_setIntegral_le_of_norm_le_const hfin fun n _ => ?_
    obtain ⟨γ, hγ, hk⟩ := hKc n
    have hγ' : ((γ : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) ∈ GQ V := by
      rw [GlobalTheory.AutFunCompare.GQ_eq]
      exact Subgroup.mem_subgroupOf.1 hγ
    have ee : f ((n : GA D V) * g) - ψ ((n : GA D V) * g) =
        f (((γ * n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) * g) -
          ψ (((γ * n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) * g) := by
      rw [Subgroup.coe_mul, mul_assoc, hl _ hγ', hψl _ hγ']
    rw [ee]
    exact (hψ _ ⟨_, hk, rfl⟩).le
  by_contra hne
  have hpos : 0 < ‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ := norm_pos_iff.2 hne
  have := key (‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ / (μ.real 𝓕 + 1)) (div_pos hpos (by linarith))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at this
  nlinarith

end GlobalTheory.CuspApproxCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinTranslate

variable {D : D7} (θ : InfFam D) (V : HSp D)

theorem comm_fin_real {a b : GA D V} (ha : a ∈ GfC V) (hb : b ∈ GinfC V) : a * b = b * a := by
  have h1 : (GfC V).Normal := MonoidHom.normal_ker _
  have h2 : (GinfC V).Normal := MonoidHom.normal_ker _
  exact Subgroup.commute_of_normal_of_disjoint (GfC V) (GinfC V) h1 h2
    (Subgroup.disjoint_def.2 fun {x} hx hy => GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V hx hy) a b ha hb

theorem atTau_mem (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact (GinfC V).one_mem

theorem oneP_mem (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) : oneP θ V τ X t ∈ GinfC V :=
  atTau_mem θ V τ _

def rTrL (κ : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := LinearMap.funLeft ℂ ℂ fun g => g * κ

theorem rTrL_apply (κ : GA D V) (φ : GA D V → ℂ) : rTrL V κ φ = rTr V κ φ := rfl

variable {κ : GA D V}

theorem Rder_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (rTr V κ φ) = rTr V κ (Rder θ V τ X φ) := by
  funext g
  simp only [Rder, rTr]
  congr 1
  funext t
  rw [mul_assoc, mul_assoc, comm_fin_real V hκ (oneP_mem θ V τ X t)]

theorem RderC_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V τ Z (rTr V κ φ) = rTr V κ (RderC θ V τ Z φ) := by
  unfold RderC
  rw [Rder_rTr θ V hκ, Rder_rTr θ V hκ]
  rfl

theorem foldr_comm {α : Type} (T : α → α) (l : List (α → α)) (hl : ∀ f ∈ l, ∀ x, f (T x) = T (f x)) (x : α) :
    l.foldr (fun f acc => f acc) (T x) = T (l.foldr (fun f acc => f acc) x) := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    simp only [List.foldr_cons]
    rw [ih fun g hg => hl g (List.mem_cons_of_mem _ hg), hl f List.mem_cons_self]

theorem gelf_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ) :
    gelf θ V τ k (rTr V κ φ) = rTr V κ (gelf θ V τ k φ) := by
  unfold gelf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← rTrL_apply V κ (∑ _, _), map_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [rTrL_apply]
  refine foldr_comm (rTr V κ) _ ?_ φ
  intro f hf x
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
  exact RderC_rTr θ V hκ τ _ x

theorem foldr_Rder_rTr (hκ : κ ∈ GfC V) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (rTr V κ φ) = rTr V κ (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    rw [ih, Rder_rTr θ V hκ]

theorem isAutFun_rTr (hκ : κ ∈ GfC V) {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V (rTr V κ φ) := by
  have := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  refine ⟨fun γ hγ g => ?_, ?_, h.cont.comp (continuous_id.mul continuous_const)⟩
  · simp only [rTr]
    rw [mul_assoc, h.left γ hγ]
  · obtain ⟨U, hU, hinv⟩ := h.level
    refine ⟨U.comap (MulAut.conj κ⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩
    · have hc : Continuous fun k : GA D V => κ⁻¹ * k * κ⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hU.preimage hc
    · have hk' : κ⁻¹ * k * κ⁻¹⁻¹ ∈ U := hk
      have hf : κ⁻¹ * k * κ⁻¹⁻¹ ∈ GfC V :=
        (GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hκ) hkf) ((GfC V).inv_mem ((GfC V).inv_mem hκ))
      simp only [rTr]
      rw [← hinv _ hk' hf (g * κ)]
      congr 1
      group

theorem isAutFunSm_rTr : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (κ : GA D V), κ ∈ GfC V → ∀ φ : GA D V → ℂ,
    IsAutFunSm θ V φ → IsAutFunSm θ V (rTr V κ φ) := by
  intro D θ V κ hκ φ h
  refine ⟨isAutFun_rTr V hκ h.toIsAutFun, fun k τs Xs hX g => ?_, ?_, ?_⟩
  · have e : (fun t : Fin k → ℝ => rTr V κ φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) =
        fun t : Fin k → ℝ => φ (g * κ * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
      funext t
      have hm : (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod ∈ GinfC V := by
        refine (GinfC V).list_prod_mem fun x hx => ?_
        obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
        exact oneP_mem θ V _ _ _
      simp only [rTr]
      rw [mul_assoc, mul_assoc, comm_fin_real V hκ hm]
    rw [e]
    exact h.smooth k τs Xs hX (g * κ)
  · obtain ⟨W, hW, hφ, hst⟩ := h.zfin
    refine ⟨W.map (rTrL V κ), inferInstance, ⟨φ, hφ, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    exact ⟨gelf θ V τ k f, hst τ k f hf, (gelf_rTr θ V hκ τ k f).symm⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl (x * κ)
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_Rder_rTr θ V hκ]
    simp only [rTr]
    rw [mul_assoc, ← comm_fin_real V hκ hg, ← mul_assoc]
    exact hC g hg

end GlobalTheory.FinTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionIsAction
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem isLift_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    IsLevelLift V β L (g * g') (κ * κ') := by
  refine ⟨(GfC V).mul_mem hκ.1 hκ'.1, ?_, ?_⟩
  · rw [map_mul]; exact Subgroup.mul_mem _ hκ.2.1 hκ'.2.1
  · rw [map_mul, Formalism.L2.DIV.rTup_mul hκ.2.1 hκ'.2.1, hκ.2.2, hκ'.2.2]

theorem levChi_flag_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    levChi V β (flagL L) (κ * κ') = levChi V β (flagL L) κ * levChi V β (flagL L) κ' := by
  unfold levChi
  rw [map_mul, levFn_flag_mul hκ.2.1 hκ'.2.1, Units.val_mul]

theorem levChi_flag1 (κ : GA D V) : levChi V β (flag1L L) κ = levChi V β (flagL L) κ := by
  unfold levChi
  rw [levFn_flag1]

theorem isLift_one_of_mem {κ : GA D V} (hκ : κ ∈ levG V β (flag1L L)) : IsLevelLift V β L 1 κ := by
  refine ⟨hκ.1, hκ.2.1, ?_⟩
  have h : Formalism.L2.DIV.rTup β L (finE V κ) ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 L.Pg L.r)) := hκ.2.2
  exact Subgroup.mem_bot.mp h

theorem act_one {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) : actG0 V β L 1 F = F := by
  have h1 : (1 : GA D V) ∈ levG V β (flag1L L) := Subgroup.one_mem _
  have hl := isLift_one_of_mem h1
  funext h
  rw [level_action_spec hF ⟨1, hl⟩ 1 hl h, hF 1 h1 h, levChi_flag1]
  have := levChi_ne_zero (V := V) (β := β) (flagL L) 1
  field_simp

theorem act_hasType {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {g : G0 L.Pg L.r}
    (hex : ∃ κ, IsLevelLift V β L g κ) : HasType V β (flag1L L) (actG0 V β L g F) := by
  intro k hk h
  obtain ⟨κ, hκ⟩ := hex
  have hl := isLift_one_of_mem hk
  have hkκ : IsLevelLift V β L g (k * κ) := by simpa using isLift_mul hl hκ
  rw [level_action_spec hF ⟨κ, hκ⟩ κ hκ (h * k), level_action_spec hF ⟨κ, hκ⟩ (k * κ) hkκ h, levChi_flag_mul hl hκ,
    levChi_flag1, mul_assoc h k κ]
  have := levChi_ne_zero (V := V) (β := β) (flagL L) k
  have := levChi_ne_zero (V := V) (β := β) (flagL L) κ
  field_simp

theorem act_mul {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {g g' : G0 L.Pg L.r}
    (hex : ∃ κ, IsLevelLift V β L g κ) (hex' : ∃ κ, IsLevelLift V β L g' κ) :
    actG0 V β L (g * g') F = actG0 V β L g (actG0 V β L g' F) := by
  obtain ⟨κ, hκ⟩ := hex
  obtain ⟨κ', hκ'⟩ := hex'
  have hm := isLift_mul hκ hκ'
  funext h
  rw [level_action_spec hF ⟨_, hm⟩ _ hm h, level_action_spec (act_hasType hF ⟨κ', hκ'⟩) ⟨κ, hκ⟩ κ hκ h,
    level_action_spec hF ⟨κ', hκ'⟩ κ' hκ' (h * κ), levChi_flag_mul hκ hκ', mul_assoc h κ κ', mul_inv, mul_assoc]

theorem levelGroupAction_isAction : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), LiftsExist V β L → ∀ F : GA D V → ℂ, HasType V β (flag1L L) F → (actG0 V β L 1 F = F ∧ ∀ g, HasType V β (flag1L L) (actG0 V β L g F)) ∧ ∀ g g', actG0 V β L (g * g') F = actG0 V β L g (actG0 V β L g' F) := by
  intro D V β L hL F hF
  exact ⟨⟨act_one hF, fun g => act_hasType hF (hL g)⟩, fun g g' => act_mul hF (hL g) (hL g')⟩

end GlobalTheory.FlagAction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerZeroUpperBlockIndicatorSqSumEqCard
section
open Classical

namespace GlobalTheory.LevelVecNorm

theorem finsum_indicator_one_eq_ncard' {α : Type} (s : Set α) :
    (∑ᶠ x, s.indicator (fun _ => (1:ℝ)) x) = (s.ncard : ℝ) := by
  by_cases hs : s.Finite
  · rw [← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]
    simp
  · have hsupp : Function.support (s.indicator (fun _ => (1:ℝ))) = s := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [finsum_of_infinite_support (by rw [hsupp]; exact hs), Set.Infinite.ncard hs]
    simp

theorem suppInd_sq_sum_eq_card : ∀ {k : Type} [CommRing k] {b a : ℕ} (r t : ℕ), b = r + t → a = r → ∀ H : Subgroup (GL (Fin r) k),
    ∑ᶠ z : Matrix (Fin b) (Fin a) k, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = (Nat.card H : ℝ) := by
  intro k _ b a r t hb ha H
  subst hb; subst a
  let f : GL (Fin r) k → Matrix (Fin (r + t)) (Fin r) k := fun g i j =>
    if h : i.val < r then (g : Matrix (Fin r) (Fin r) k) ⟨i.val, h⟩ j else 0
  have htop : ∀ g, Formalism.IndefR.Datum.topL r (f g) = (g : Matrix (Fin r) (Fin r) k) := by
    intro g; ext i j
    simp [Formalism.IndefR.Datum.topL, f, i.isLt, j.isLt, show i.val < r + t by omega]
  have hlow : ∀ g, Formalism.IndefR.Datum.LowZero r (f g) := by
    intro g i j hi _
    simp [f, show ¬ i.val < r by omega]
  have hinj : Function.Injective f := by
    intro g g' h
    apply Units.ext
    rw [← htop g, ← htop g', h]
  let S : Set (Matrix (Fin (r + t)) (Fin r) k) :=
    {z | Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z}
  have hS : S = f '' (H : Set (GL (Fin r) k)) := by
    ext z
    constructor
    · rintro ⟨hz, g, hg, hgz⟩
      refine ⟨g, hg, ?_⟩
      ext i j
      by_cases hi : i.val < r
      · have := congrFun (congrFun hgz ⟨i.val, hi⟩) j
        simp only [Formalism.IndefR.Datum.topL, j.isLt, show i.val < r + t by omega] at this
        simpa [f, hi] using this
      · simp [f, hi, hz i j (by omega) j.isLt]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hlow g, g, hg, (htop g).symm⟩
  have hfun : ∀ z, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = S.indicator (fun _ => (1:ℝ)) z := by
    intro z
    unfold GlobalTheory.LevelVecNorm.suppInd
    by_cases hz : z ∈ S
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_pos hz', Set.indicator_of_mem hz]; norm_num
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_neg hz', Set.indicator_of_notMem hz]; norm_num
  simp_rw [hfun]
  rw [finsum_indicator_one_eq_ncard', hS, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
  rfl

end GlobalTheory.LevelVecNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem mult_value_left_cont_level :
    ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ, ∀ T ∈ Mult θ M J χ, ∀ v, (∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) ∧ Continuous (T v) ∧ ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  intro D V S θ M J χ T hT v
  induction hT using Submodule.span_induction with
  | mem x hx =>
    exact ⟨(hx.aut v).left, (hx.aut v).cont, hx.lev v⟩
  | zero =>
    refine ⟨fun γ _ g => ?_, ?_, fun k _ g => ?_⟩
    · simp
    · simp only [MultilinearMap.zero_apply]
      exact continuous_zero
    · simp
  | add x y _ _ hx hy =>
    refine ⟨fun γ hγ g => ?_, ?_, fun k hk g => ?_⟩
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.1 γ hγ g, hy.1 γ hγ g]
    · simpa only [MultilinearMap.add_apply] using hx.2.1.add hy.2.1
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.2.2 k hk g, hy.2.2 k hk g, mul_add]
  | smul c x _ hx =>
    refine ⟨fun γ hγ g => ?_, ?_, fun k hk g => ?_⟩
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.1 γ hγ g]
    · simpa only [MultilinearMap.smul_apply] using hx.2.1.const_smul c
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.2.2 k hk g]
      ring

end GlobalTheory
end

