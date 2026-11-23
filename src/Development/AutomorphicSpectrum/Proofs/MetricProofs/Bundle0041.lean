module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0024
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import Development.WeilBound.CoreStatements.AmpleLineBundles.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicQuotientStructure
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem orth_of_set {m : ℕ} {T : Set (Fin m → ℂ)} {H : Matrix (Fin m) (Fin m) ℂ} {z : Fin m → ℂ}
    (h : ∀ t ∈ T, z ⬝ᵥ H *ᵥ star t = 0) : ∀ s ∈ Submodule.span ℂ T, z ⬝ᵥ H *ᵥ star s = 0 := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simp [star_add, mulVec_add, dotProduct_add, hx, hy]
  | smul a x _ hx => simp [star_smul, mulVec_smul, dotProduct_smul, hx]

theorem span_period (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k : ℕ} {e : Fin k → Λ}
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range e)) :
    Submodule.span ℂ (R.P '' I) = Submodule.span ℂ (Set.range fun i => R.P (e i)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (hI v).1 hv
    show R.P v ∈ Submodule.span ℂ (Set.range fun i => R.P (e i))
    induction hv' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y hx' hy' hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (hx ((hI x).2 hx')) (hy ((hI y).2 hy'))
    | smul a x hx' hx =>
      rw [map_zsmul]
      exact Submodule.smul_of_tower_mem _ a (hx ((hI x).2 hx'))
  · refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨e i, (hI _).2 (Submodule.subset_span ⟨i, rfl⟩), rfl⟩

theorem im_quot (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k : ℕ} {e : Fin k → Λ}
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range e)) (hiso : IsIsoSub R.form I)
    (hLI : LinearIndependent ℂ fun i => R.P (e i)) {g' : ℕ} (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (hk : LinearMap.ker q = Submodule.span ℂ (R.P '' I)) (H' : Matrix (Fin g') (Fin g') ℂ)
    (hm : ∀ a b, (∀ v ∈ I, R.ip (R.P v) a = 0) → q b ⬝ᵥ H' *ᵥ star (q a) = b ⬝ᵥ R.Hm *ᵥ star a)
    {x y : Λ} (hx : ∀ v ∈ I, R.form x v = 0) (hy : ∀ v ∈ I, R.form y v = 0) :
    (q (R.P x) ⬝ᵥ H' *ᵥ star (q (R.P y))).im = R.form x y := by
  have heI : ∀ i, e i ∈ I := fun i => (hI _).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hui : ∀ i j, (R.P (e i) ⬝ᵥ R.Hm *ᵥ star (R.P (e j))).im = 0 := fun i j => by
    rw [R.im, hiso _ (heI i) _ (heI j)]; simp
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ProjReal.orthogonal_projection_real_coefficients g k R.Hm R.pos _ hLI (_root_.GlobalTheory.CompanionTheory.Ar.PosFormProjection.exists_orthogonal_coefficients g k R.Hm R.pos _ hLI) hui (R.P y) (fun j => by
    rw [R.im, hy _ (heI j)]; simp)
  set s : Fin g → ℂ := ∑ i, (c i : ℂ) • R.P (e i) with hs
  have hsk : q s = 0 := by
    have : s ∈ LinearMap.ker q := by
      rw [hk, span_period R hI]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact this
  have hqy : q (R.P y - s) = q (R.P y) := by rw [map_sub, hsk, sub_zero]
  have horth : ∀ v ∈ I, R.ip (R.P v) (R.P y - s) = 0 := by
    intro v hv
    have hv' : R.P v ∈ Submodule.span ℂ (Set.range fun i => R.P (e i)) := by
      rw [← span_period R hI]; exact Submodule.subset_span ⟨v, hv, rfl⟩
    refine orth_of_set (T := Set.range fun i => R.P (e i)) ?_ _ hv'
    rintro _ ⟨j, rfl⟩
    exact hc j
  rw [← hqy, hm _ _ horth]
  have hxs : (R.P x ⬝ᵥ R.Hm *ᵥ star s).im = 0 := by
    simp only [hs, star_sum, star_smul, mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul,
      smul_eq_mul, Complex.im_sum, Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul, R.im,
      hx _ (heI _)]
    simp
  rw [star_sub, mulVec_sub, dotProduct_sub, Complex.sub_im, hxs, sub_zero, R.im]

theorem period_facts (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (f : Fin k → Fin n) (hf : Function.Injective f)
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range fun i => b (f i))) (hiso : IsIsoSub R.form I) :
    LinearIndependent ℂ fun i => R.P (b (f i)) := by
  have heI : ∀ i, b (f i) ∈ I := fun i => (hI _).2 (Submodule.subset_span ⟨i, rfl⟩)
  refine _root_.GlobalTheory.CompanionTheory.Ar.RealFormIndep.linearIndependent_complex_of_real_form g k R.Hm R.pos _ ((_root_.GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_basis_periods_linearIndependent E g Λ R n b).comp f hf) fun i j => ?_
  rw [R.im, hiso _ (heI i) _ (heI j)]; simp

theorem exists_orth (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k : ℕ} {e : Fin k → Λ}
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range e))
    (hLI : LinearIndependent ℂ fun i => R.P (e i)) (z : Fin g → ℂ) :
    ∃ s ∈ Submodule.span ℂ (R.P '' I), ∀ v ∈ Submodule.span ℂ (R.P '' I), (z - s) ⬝ᵥ R.Hm *ᵥ star v = 0 := by
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PosFormProjection.exists_orthogonal_coefficients g k R.Hm R.pos _ hLI z
  rw [span_period R hI]
  refine ⟨∑ i, c i • R.P (e i), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
  refine orth_of_set ?_
  rintro _ ⟨j, rfl⟩
  exact hc j

theorem mem_of_mem_span (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (f : Fin k → Fin n) (hf : Function.Injective f)
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range fun i => b (f i))) (hiso : IsIsoSub R.form I)
    {x : Λ} (hx : ∀ v ∈ I, R.form x v = 0) (hs : R.P x ∈ Submodule.span ℂ (R.P '' I)) : x ∈ I := by
  have heI : ∀ i, b (f i) ∈ I := fun i => (hI _).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hLI := period_facts R b f hf hI hiso
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ProjReal.orthogonal_projection_real_coefficients g k R.Hm R.pos _ hLI (_root_.GlobalTheory.CompanionTheory.Ar.PosFormProjection.exists_orthogonal_coefficients g k R.Hm R.pos _ hLI) (fun i j => by
    rw [R.im, hiso _ (heI i) _ (heI j)]; simp) (R.P x) (fun j => by rw [R.im, hx _ (heI j)]; simp)
  rw [span_period R hI] at hs
  set s : Fin g → ℂ := ∑ i, (c i : ℂ) • R.P (b (f i)) with hsdef
  have hsm : s ∈ Submodule.span ℂ (Set.range fun i => R.P (b (f i))) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hw : R.P x - s = 0 := by
    by_contra hne
    have h0 : (R.P x - s) ⬝ᵥ R.Hm *ᵥ star (R.P x - s) = 0 :=
      orth_of_set (by rintro _ ⟨j, rfl⟩; exact hc j) _ (Submodule.sub_mem _ hs hsm)
    have := R.pos _ hne
    rw [h0] at this
    simp at this
  exact (hI x).2 (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.mem_span_part_of_period_real_comb g k n Λ R.P b f (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_basis_periods_linearIndependent E g Λ R n b) hf x c (sub_eq_zero.1 hw))

end

theorem exists_univ_quot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsSaturated I → IsIsoSub R₀.form I → ∃ (g' k : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ') (e : Fin k → Λ) (form' : Λ' →ₗ[ℤ] Λ' →ₗ[ℤ] ℤ) (π : Λ → Λ'), k + g' = g ∧ (∀ x', ∃ x, (∀ y ∈ I, R₀.form x y = 0) ∧ π x = x') ∧ ∀ R : RiemLat E g Λ, R.form = R₀.form → LinearIndependent ℂ (fun i => R.P (e i)) ∧ Submodule.span ℂ (R.P '' I) = Submodule.span ℂ (Set.range fun i => R.P (e i)) ∧ ∀ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), Function.Surjective q → LinearMap.ker q = Submodule.span ℂ (R.P '' I) → ∃ R' : RiemLat E g' Λ', R'.form = form' ∧ (∀ x, (∀ y ∈ I, R.form x y = 0) → R'.P (π x) = q (R.P x)) ∧ ∀ x y, (∀ v ∈ I, R.ip (R.P v) x = 0) → R'.ip (q x) (q y) = R.ip x y := by
  intro E _ _ _ g Λ _ _ R₀ I hsat hiso
  classical
  haveI := R₀.free
  haveI := R₀.fin
  obtain ⟨g', Λ', i1, i2, R₀', q₀, hq₀s, hq₀k, hq₀B, hq₀r, hq₀m⟩ := _root_.LevelTowerAlt.isotropic_quotient_lattice E g Λ Unit R₀ I hsat hiso
  obtain ⟨k, n, b, f, hf, hN⟩ := GlobalTheory.T.exists_basis_subset_of_saturated_submodule Λ (AddSubgroup.toIntSubmodule I.toAddSubgroup) (fun v m hm h => hsat v m hm h)
  have hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range fun i => b (f i)) := fun v => by
    rw [hN]; rfl
  have hLI₀ := period_facts R₀ b f hf hI hiso

  let D : AddSubgroup Λ :=
    { carrier := {x | ∀ y ∈ I, R₀.form x y = 0}
      add_mem' := fun {a c} ha hc y hy => by simp [ha y hy, hc y hy]
      zero_mem' := fun y _ => by simp
      neg_mem' := fun {a} ha y hy => by simp [ha y hy] }
  have hDmem : ∀ x, x ∈ D ↔ ∀ y ∈ I, R₀.form x y = 0 := fun x => Iff.rfl
  have hDsmul : ∀ (a : 𝓞 E), ∀ x ∈ D, a • x ∈ D := by
    intro a x hx y hy
    rw [R₀.adj a (IsCMField.ringOfIntegersComplexConj E a) (by simp [IsCMField.coe_ringOfIntegersComplexConj])]
    exact hx _ (I.smul_mem _ hy)
  have hex : ∀ x ∈ D, ∃ x', R₀'.P x' = q₀ (R₀.P x) := by
    intro x hx
    have : q₀ (R₀.P x) ∈ Set.range R₀'.P := by
      rw [hq₀r]; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact this
  let π : Λ → Λ' := fun x => if h : x ∈ D then (hex x h).choose else 0
  have hπ : ∀ x ∈ D, R₀'.P (π x) = q₀ (R₀.P x) := by
    intro x h
    simp only [π, dif_pos h]
    exact (hex x h).choose_spec
  have hinj : Function.Injective R₀'.P := (_root_.LevelTowerAlt.riemann_lattice_eigen_projections E g' Λ' Unit R₀').1
  have hπs : ∀ x', ∃ x ∈ D, π x = x' := by
    intro x'
    have : R₀'.P x' ∈ Set.range R₀'.P := ⟨x', rfl⟩
    rw [hq₀r] at this
    obtain ⟨_, ⟨x, hx, rfl⟩, h⟩ := this
    exact ⟨x, hx, hinj ((hπ x hx).trans h)⟩
  have hπadd : ∀ x ∈ D, ∀ y ∈ D, π (x + y) = π x + π y := by
    intro x hx y hy
    apply hinj
    rw [hπ _ (D.add_mem hx hy), map_add (f := _), map_add (f := _), map_add (f := _), hπ x hx, hπ y hy]
  have hπsmul : ∀ (a : 𝓞 E), ∀ x ∈ D, a • x ∈ D ∧ π (a • x) = a • π x := by
    intro a x hx
    refine ⟨hDsmul a x hx, hinj ?_⟩
    rw [hπ _ (hDsmul a x hx), R₀'.act, hπ x hx, R₀.act, hq₀B]
  have hπI : ∀ x ∈ D, π x = 0 → x ∈ I := by
    intro x hx h0
    have h1 : q₀ (R₀.P x) = 0 := by rw [← hπ x hx, h0, map_zero]
    have h2 : R₀.P x ∈ LinearMap.ker q₀ := h1
    rw [hq₀k] at h2
    exact mem_of_mem_span R₀ b f hf hI hiso hx h2
  have hπform : ∀ x ∈ D, ∀ y ∈ D, R₀'.form (π x) (π y) = R₀.form x y := by
    intro x hx y hy
    have h := im_quot R₀ hI hiso hLI₀ q₀ hq₀k R₀'.Hm (fun a c ha => hq₀m a c ha) hx hy
    rw [← hπ x hx, ← hπ y hy, R₀'.im] at h
    exact_mod_cast h
  have hk : k + g' = g := by
    have h1 := LinearMap.finrank_range_add_finrank_ker q₀
    rw [LinearMap.range_eq_top.2 hq₀s, hq₀k, span_period R₀ hI, finrank_span_eq_card hLI₀] at h1
    simp at h1
    omega
  refine ⟨g', k, Λ', i1, i2, fun i => b (f i), R₀'.form, π, hk, hπs, fun R hR => ?_⟩
  have hiso' : IsIsoSub R.form I := hR ▸ hiso
  have hLI := period_facts R b f hf hI hiso'
  refine ⟨hLI, span_period R hI, fun q hqs hqk => ?_⟩
  obtain ⟨Hm', hherm, hpos, hmet⟩ := _root_.GlobalTheory.CompanionTheory.Ar.QuotUniv.hermitian_transport_along_orthogonal_complement g g' R.Hm R.herm R.pos _ q hqs hqk (exists_orth R hI hLI)
  have hD' : ∀ x, (∀ y ∈ I, R.form x y = 0) → x ∈ D := fun x h => by rw [hDmem, ← hR]; exact h
  have hDR : ∀ x ∈ D, ∀ y ∈ I, R.form x y = 0 := fun x h => by rw [hR]; exact h
  have hmet' : ∀ a c, (∀ v ∈ I, R.ip (R.P v) a = 0) → q c ⬝ᵥ Hm' *ᵥ star (q a) = c ⬝ᵥ R.Hm *ᵥ star a := by
    intro a c ha
    refine hmet a c (orth_of_set ?_)
    rintro _ ⟨v, hv, rfl⟩
    exact ha v hv
  have hqB : ∀ (a : 𝓞 E) z, q z = 0 → q (R.B a z) = 0 := by
    intro a z hz
    have hz' : z ∈ Submodule.span ℂ (R.P '' I) := by rw [← hqk]; exact hz
    clear hz
    have : R.B a z ∈ Submodule.span ℂ (R.P '' I) := by
      induction hz' using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨v, hv, rfl⟩ := hw
        rw [← R.act]
        exact Submodule.subset_span ⟨_, I.smul_mem _ hv, rfl⟩
      | zero => simp
      | add w w' _ _ h h' =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ h h'
      | smul c w _ h =>
        rw [map_smul]
        exact Submodule.smul_mem _ c h
    rw [← hqk] at this
    exact this
  have hker : ∀ x ∈ D, π x = 0 → q (R.P x) = 0 := by
    intro x hx h0
    have : R.P x ∈ LinearMap.ker q := by
      rw [hqk]; exact Submodule.subset_span ⟨x, hπI x hx h0, rfl⟩
    exact this
  have him : ∀ x ∈ D, ∀ y ∈ D, (q (R.P x) ⬝ᵥ Hm' *ᵥ star (q (R.P y))).im = R₀'.form (π x) (π y) := by
    intro x hx y hy
    rw [im_quot R hI hiso' hLI q hqk Hm' hmet' (hDR x hx) (hDR y hy), hπform x hx y hy, hR]
  obtain ⟨B', hB'⟩ := GlobalTheory.T.exists_descended_ringHom_on_quotient (𝓞 E) g g' R.B q hqs hqB
  obtain ⟨R', h1, h2, h3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_assemble_of_quot E g g' Λ Λ' R R₀' D π q Hm' B' hπs hπadd hπsmul hker hB' hherm hpos him
  refine ⟨R', h1, fun x hx => h3 x (hD' x hx), fun x y hx => ?_⟩
  show q y ⬝ᵥ R'.Hm *ᵥ star (q x) = y ⬝ᵥ R.Hm *ᵥ star x
  rw [h2]
  exact hmet' x y hx

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviPullEq
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PshPull

open scoped ContDiff

theorem levi_pull_eq {e e' : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' Z) (h : X → Z) (hh : HoloMap A A' h) (th : LocPot X) (th' : LocPot Z) (u : Z → ℝ)
    (hth : IsPotential A th) (hth' : IsPotential A' th') (hu : A'.Smooth u)
    (hs : SamePot A Set.univ th (th'.pullback h hh.1)) (c : ℝ) (x : X) (j : Fin A.n) (y : Fin e → ℂ)
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ th.U x) (w : Fin e → ℂ) :
    ∃ (j' : Fin A'.n) (y' v : Fin e' → ℂ), y' ∈ (A'.chart j').target ∧
      (A'.chart j').symm y' = h ((A.chart j).symm y) ∧
      levi (fun t => c * (th.φ x ((A.chart j).symm t) + u (h ((A.chart j).symm t)))) y w =
        levi (fun s => c * (th'.φ (h ((A.chart j).symm y)) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) y' v := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ :=
    WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  obtain ⟨p, hp⟩ : ∃ p, p = (A.chart j).symm y := ⟨_, rfl⟩
  rw [← hp] at hyU ⊢
  obtain ⟨j', hj'⟩ := A'.cover (h p)
  obtain ⟨W₁, hW₁o, hpW₁, G₁, hG₁, hE₁⟩ := hth.2 x p p ⟨hyU, th.mem_U p⟩
  obtain ⟨W₂, hW₂o, hpW₂, G₂, hG₂, hE₂⟩ := hs p (Set.mem_univ p)
  have hτ : AnalyticAt ℂ (A'.chart j' ∘ h ∘ (A.chart j).symm) y :=
    hh.2 j j' y ⟨hy, by simpa [← hp] using hj'⟩
  have hGa : AnalyticAt ℂ (fun t => G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)) y :=
    AnalyticAt.add (hG₁ j y ⟨hy, by simpa [← hp] using hpW₁⟩) (hG₂ j y ⟨hy, by simpa [← hp] using hpW₂⟩)
  have hτy : (A'.chart j' ∘ h ∘ (A.chart j).symm) y = A'.chart j' (h p) := by simp [← hp]
  have hy' : A'.chart j' (h p) ∈ (A'.chart j').target := (A'.chart j').map_source hj'
  have hsy' : (A'.chart j').symm (A'.chart j' (h p)) = h p := (A'.chart j').left_inv hj'

  have hψ₁ : ContDiffAt ℝ 2 (th'.φ (h p) ∘ (A'.chart j').symm) (A'.chart j' (h p)) := by
    have hO : IsOpen ((A'.chart j').target ∩ (A'.chart j').symm ⁻¹' th'.U (h p)) :=
      (A'.chart j').isOpen_inter_preimage_symm (th'.isOpen_U _)
    have hm : A'.chart j' (h p) ∈ (A'.chart j').target ∩ (A'.chart j').symm ⁻¹' th'.U (h p) :=
      ⟨hy', by simpa [hsy'] using th'.mem_U (h p)⟩
    exact (((hth'.1 (h p) j').contDiffAt (hO.mem_nhds hm))).of_le h2
  have hψ₂ : ContDiffAt ℝ 2 (u ∘ (A'.chart j').symm) (A'.chart j' (h p)) := by
    have hO : IsOpen ((A'.chart j').target ∩ (A'.chart j').symm ⁻¹' Set.univ) := by
      simpa using (A'.chart j').open_target
    have hm : A'.chart j' (h p) ∈ (A'.chart j').target ∩ (A'.chart j').symm ⁻¹' Set.univ :=
      ⟨hy', Set.mem_univ _⟩
    exact ((hu j').contDiffAt (hO.mem_nhds hm)).of_le h2
  have hψ : ContDiffAt ℝ 2 (fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s)))
      (A'.chart j' (h p)) :=
    contDiffAt_const.mul (hψ₁.add hψ₂)
  have hψτ : ContDiffAt ℝ 2 (fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s)))
      ((A'.chart j' ∘ h ∘ (A.chart j).symm) y) := by rwa [hτy]
  have hτ2 : ContDiffAt ℝ 2 (A'.chart j' ∘ h ∘ (A.chart j).symm) y :=
    (hτ.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hf : ContDiffAt ℝ 2 ((fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ∘
      (A'.chart j' ∘ h ∘ (A.chart j).symm)) y := hψτ.comp y hτ2
  have hg : ContDiffAt ℝ 2 (fun t => (G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt

  have hev : (fun t => c * (th.φ x ((A.chart j).symm t) + u (h ((A.chart j).symm t)))) =ᶠ[𝓝 y]
      fun t => ((fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ∘
        (A'.chart j' ∘ h ∘ (A.chart j).symm)) t + c * (G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)).re := by
    have hcs : ContinuousAt (A.chart j).symm y := (A.chart j).continuousAt_symm hy
    have hOx : ∀ᶠ t in 𝓝 y, (A.chart j).symm t ∈ W₁ ∩ W₂ ∩ th.U x ∩ th.U p ∩ h ⁻¹' (A'.chart j').source := by
      apply hcs.eventually_mem
      rw [← hp]
      refine IsOpen.mem_nhds ?_ ⟨⟨⟨⟨hpW₁, hpW₂⟩, hyU⟩, th.mem_U p⟩, hj'⟩
      exact (((hW₁o.inter hW₂o).inter (th.isOpen_U x)).inter (th.isOpen_U p)).inter
        ((A'.chart j').open_source.preimage hh.1)
    filter_upwards [hOx] with t ht
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := ht
    have e1 := hE₁ _ ⟨⟨h1, h3⟩, h4⟩
    have e2 : th.φ p ((A.chart j).symm t) - th'.φ (h p) (h ((A.chart j).symm t)) =
      (G₂ ((A.chart j).symm t)).re := hE₂ _ h2
    have e3 : (A'.chart j').symm (A'.chart j' (h ((A.chart j).symm t))) = h ((A.chart j).symm t) :=
      (A'.chart j').left_inv h5
    simp only [Function.comp_apply, e3, Complex.add_re]
    rw [← e1, ← e2]
    ring
  refine ⟨j', A'.chart j' (h p), fderiv ℂ (A'.chart j' ∘ h ∘ (A.chart j).symm) y w, hy', hsy', ?_⟩
  rw [levi_congr hev w, levi_add_smul c hf hg w, levi_comp w hτ hψτ, levi_re_analytic hGa w, hτy]
  ring

theorem isPsh_pull : ∀ (e e' : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' Z) (h : X → Z) (hh : HoloMap A A' h) (th : LocPot X) (th' : LocPot Z) (u : Z → ℝ),
    IsPotential A th → IsPotential A' th' → A'.Smooth u → SamePot A Set.univ th (th'.pullback h hh.1) →
    (IsPsh A' (th' + LocPot.ofFun u) → IsPsh A (th + LocPot.ofFun (u ∘ h))) ∧
      (IsPsh A' ((th' + LocPot.ofFun u).rsmul (-1)) → IsPsh A ((th + LocPot.ofFun (u ∘ h)).rsmul (-1))) := by
  intro e e' X Z _ _ A A' h hh th th' u hth hth' hu hs
  refine ⟨fun H x j y hy w => ?_, fun H x j y hy w => ?_⟩
  · obtain ⟨j', y', v, hy', hsy, hl⟩ := levi_pull_eq A A' h hh th th' u hth hth' hu hs 1 x j y hy.1 hy.2.1 w
    have hH := H (h ((A.chart j).symm y)) j' y' ⟨hy', by
      rw [Set.mem_preimage, hsy]; exact LocPot.mem_U _ _⟩ v
    simp only [one_mul] at hl
    exact hl ▸ hH
  · obtain ⟨j', y', v, hy', hsy, hl⟩ := levi_pull_eq A A' h hh th th' u hth hth' hu hs (-1) x j y hy.1 hy.2.1 w
    have hH := H (h ((A.chart j).symm y)) j' y' ⟨hy', by
      rw [Set.mem_preimage, hsy]; exact LocPot.mem_U _ _⟩ v
    exact hl ▸ hH

end GlobalTheory.CompanionTheory.Ar.PB.PshPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemComplexConjugation
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

open Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_cross {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (k : K) (a b : ι k) :
    z ⟨k, a⟩ * z' ⟨k, b⟩ = z ⟨k, b⟩ * z' ⟨k, a⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  simp only
  ring

theorem sameOrbit_of_cross {z z' : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0)
    (h : ∀ (k : K) (a b : ι k), z ⟨k, a⟩ * z' ⟨k, b⟩ = z ⟨k, b⟩ * z' ⟨k, a⟩) :
    SameOrbit z z' := by
  choose j hj using hz'
  refine ⟨fun k => z ⟨k, j k⟩ / z' ⟨k, j k⟩, fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz k
    refine div_ne_zero (fun h0 => ?_) (hj k)
    have := h k i (j k)
    rw [h0, zero_mul] at this
    exact (mul_ne_zero hi (hj k)) this
  · funext ⟨k, a⟩
    have := h k a (j k)
    have hjk := hj k
    simp only
    field_simp
    linear_combination this

theorem continuousAt_of_holo {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {y : X} (hy : y ∈ U) : ContinuousAt g y := by
  obtain ⟨j, hj⟩ := A.cover y
  have h1 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) y :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm)
      (hg j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩).continuousAt
      ((A.chart j).continuousAt hj)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [Function.comp, (A.chart j).left_inv hz]

theorem exists_conj_of_isLiftSys {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X}
    {lift : X → X → (Σ k, ι k) → ℂ} (hS : IsLiftSys A P U lift) :
    ∃ c : X → X, (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) ∧ Continuous c ∧
      ∀ x, c (c x) = x := by
  obtain ⟨hU, hmem, hholo, hlift, hcompat, hsurj, hinj, -⟩ := hS
  choose c hc using fun x => hsurj _ (cj_mem_mcPts (hlift x x (hmem x)))
  refine ⟨c, hc, ?_, fun x => ?_⟩
  · refine continuous_iff_ultrafilter.2 fun x F hF => ?_
    obtain ⟨x', -, hx'⟩ := isCompact_univ.ultrafilter_le_nhds (F.map c) (by simp)
    have hcF : Tendsto c F (𝓝 x') := hx'
    have hev : ∀ᶠ y in (F : Filter X), y ∈ U x ∧ c y ∈ U x' :=
      Filter.Eventually.and (hF ((hU x).mem_nhds (hmem x))) (hcF ((hU x').mem_nhds (hmem x')))
    have horb : ∀ᶠ y in (F : Filter X), SameOrbit (lift x' (c y)) (cj (lift x y)) := by
      filter_upwards [hev] with y hy
      exact sameOrbit_trans (hcompat x' (c y) (c y) ⟨hy.2, hmem _⟩)
        (sameOrbit_trans (hc y) (sameOrbit_cj (hcompat y x y ⟨hmem y, hy.1⟩)))
    have hl1 : ∀ p, Tendsto (fun y => lift x' (c y) p) F (𝓝 (lift x' x' p)) := fun p =>
      (continuousAt_of_holo A (hholo x' p) (hmem x')).tendsto.comp hcF
    have hl2 : ∀ p, Tendsto (fun y => cj (lift x y) p) F (𝓝 (cj (lift x x) p)) := fun p =>
      (Complex.continuous_conj.tendsto _).comp
        ((continuousAt_of_holo A (hholo x p) (hmem x)).tendsto.mono_left hF)
    have hcross : ∀ (k : K) (a b : ι k),
        lift x' x' ⟨k, a⟩ * cj (lift x x) ⟨k, b⟩ = lift x' x' ⟨k, b⟩ * cj (lift x x) ⟨k, a⟩ :=
      fun k a b => tendsto_nhds_unique_of_eventuallyEq
        ((hl1 ⟨k, a⟩).mul (hl2 ⟨k, b⟩)) ((hl1 ⟨k, b⟩).mul (hl2 ⟨k, a⟩))
        (horb.mono fun y hy => sameOrbit_cross hy k a b)
    have horb' : SameOrbit (lift x' x') (cj (lift x x)) :=
      sameOrbit_of_cross (hlift x' x' (hmem x')).1 (cj_nonzero (hlift x x (hmem x)).1) hcross
    have hxx : x' = c x := hinj _ _ (sameOrbit_trans horb' (sameOrbit_symm (hc x)))
    exact hxx ▸ hcF
  · refine hinj _ _ (sameOrbit_trans (hc (c x)) ?_)
    have := sameOrbit_cj (hc x)
    rwa [cj_cj] at this

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeFullRankSublattice
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.IndexBound

theorem full_sublattice_normDegree_bounds : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier), E.rank F = Module.finrank (𝓞 K) E.carrier → E.normDegree F ≤ E.normDegree ⊤ ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ F) → E.normDegree ⊤ ≤ E.normDegree F + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  exact @CoverDenseAlt.normDegree_full_rank_submodule_bounds

end GlobalTheory.CompanionTheory.Ar.IndexBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SlopeBoundComparableMetric
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem basis_slope_degree_bound : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ) (b : Module.Basis (Fin r) (𝓞 K) E.carrier) (C : ℝ), 1 ≤ C → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ≤ C * ∑ a, ‖w a‖ ^ 2) → E.slopeMax ≤ ((Real.log C / 2 : ℝ) : EReal) ∧ |E.normDegree ⊤| ≤ r / 2 * Real.log C :=
  @CoverDenseAlt.slopeMax_le_of_comparable_metric

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ValuationRingExtensionSpecializationStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_ring_extension_specialization : ∀ (L : Type) [Field L] (O : Subring L) (v : O →+* ℂ), (∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) → ∃ V : ValuationSubring L, (∀ s ∈ O, s ∈ V) ∧ ∀ T : Finset L, (∀ t ∈ T, t ∈ V) → ∃ (R : Subring L) (hO : O ≤ R) (ψ : R →+* ℂ), (∀ t ∈ T, t ∈ R) ∧ (∀ s : O, ψ (Subring.inclusion hO s) = v s) ∧ ∀ t ∈ T, t ≠ 0 → t⁻¹ ∈ V → t⁻¹ ∈ R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place | exact GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place | (intros; apply GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place <;> assumption)
end

