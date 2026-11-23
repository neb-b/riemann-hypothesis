module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPullPreserve
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_preserve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

theorem below_ne {Ω : Type} [Field Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (h : mseg (joinCoord x z) s ≠ 0) : mseg x (restrictChart s) ≠ 0 := by
  unfold mseg at h ⊢
  rw [Finset.prod_ne_zero_iff] at h ⊢
  intro k _
  exact h (Sum.inl k) (Finset.mem_univ _)

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {V : Type} [AddCommGroup V]
  [Module Ω V]

theorem smul_mem (R : Subalgebra O Ω) (L : AddSubgroup V) (b : Ω) (hb : b ∈ R) (v : V)
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e}) :
    b • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, e, he, rfl⟩ := hv
    exact AddSubgroup.subset_closure ⟨b * a, R.mul_mem hb ha, e, he, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
  | neg v _ hv => rw [smul_neg]; exact neg_mem hv

theorem le_closure (R : Subalgebra O Ω) (L L' : AddSubgroup V) (h : L ≤ L') :
    AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e} ≤
      AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L', v = a • e} := by
  apply AddSubgroup.closure_mono
  rintro v ⟨a, ha, e, he, rfl⟩
  exact ⟨a, ha, e, h he, rfl⟩

theorem gen_closure [IsDomain O] (R : Subalgebra O Ω) (L L' : AddSubgroup V)
    (h : ∀ v ∈ L, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ L') (v : V)
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e}) :
    ∃ c : O, c ≠ 0 ∧
      algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L', v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, e, he, rfl⟩ := hv
    obtain ⟨c, hc, hce⟩ := h e he
    exact ⟨c, hc, AddSubgroup.subset_closure ⟨a, ha, _, hce, smul_comm _ _ _⟩⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add v w _ _ hv hw =>
    obtain ⟨c, hc, hv⟩ := hv
    obtain ⟨d, hd, hw⟩ := hw
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add, map_mul]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact smul_mem R L' _ (R.algebraMap_mem d) _ hv
    · rw [mul_smul]
      exact smul_mem R L' _ (R.algebraMap_mem c) _ hw
  | neg v _ hv =>
    obtain ⟨c, hc, hv⟩ := hv
    exact ⟨c, hc, by rw [smul_neg]; exact neg_mem hv⟩

theorem scaled_closure (R : Subalgebra O Ω) (L L' : AddSubgroup V) (c : Ω)
    (h : ∀ v, v ∈ L' ↔ ∃ e ∈ L, v = c • e) (v : V) :
    v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L', v = a • e} ↔
      ∃ e ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e}, v = c • e := by
  constructor
  · intro hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, e, he, rfl⟩ := hv
      obtain ⟨e', he', rfl⟩ := (h e).1 he
      exact ⟨a • e', AddSubgroup.subset_closure ⟨a, ha, e', he', rfl⟩, smul_comm _ _ _⟩
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add v w _ _ hv hw =>
      obtain ⟨e, he, rfl⟩ := hv
      obtain ⟨f, hf, rfl⟩ := hw
      exact ⟨e + f, add_mem he hf, (smul_add _ _ _).symm⟩
    | neg v _ hv =>
      obtain ⟨e, he, rfl⟩ := hv
      exact ⟨-e, neg_mem he, (smul_neg _ _).symm⟩
  · rintro ⟨e, he, rfl⟩
    induction he using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, e, he, rfl⟩ := hv
      exact AddSubgroup.subset_closure ⟨a, ha, c • e, (h _).2 ⟨e, he, rfl⟩, smul_comm _ _ _⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | neg v _ hv => rw [smul_neg]; exact neg_mem hv

end PositivityTheory.Xgn.A_pull_preserve

theorem PositivityTheory.Xgn.t_pull_preserve : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → (LatLE O x E E' → LatLE O (joinCoord x z) EB E'B) ∧ (SameGeneric O x E E' → SameGeneric O (joinCoord x z) EB E'B) ∧ (∀ c : Ω, IsScaled x c E.lat E'.lat → IsScaled (joinCoord x z) c EB.lat E'B.lat) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E E' K' _ _ ι' _ z EB E'B hP hP'
  refine ⟨fun h s hs => ?_, fun h s hs => ?_, fun c h s hs v => ?_⟩
  · rw [hP s hs, hP' s hs]
    exact PositivityTheory.Xgn.A_pull_preserve.le_closure _ _ _ (h _ (PositivityTheory.Xgn.A_pull_preserve.below_ne x z s hs))
  · rw [hP s hs, hP' s hs]
    have h0 := h _ (PositivityTheory.Xgn.A_pull_preserve.below_ne x z s hs)
    exact ⟨PositivityTheory.Xgn.A_pull_preserve.gen_closure _ _ _ h0.1,
      PositivityTheory.Xgn.A_pull_preserve.gen_closure _ _ _ h0.2⟩
  · rw [hP s hs, hP' s hs]
    exact PositivityTheory.Xgn.A_pull_preserve.scaled_closure _ _ _ c
      (h _ (PositivityTheory.Xgn.A_pull_preserve.below_ne x z s hs)) v
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XRelabelBundle
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_relabel_bundle

variable {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}

theorem exists_snd {K : Type} {ι : K → Type} (p : Σ k, ι k) (k : K) (h : p.1 = k) :
    ∃ i : ι k, p = ⟨k, i⟩ := by
  obtain ⟨a, i⟩ := p
  simp only at h
  subst h
  exact ⟨i, rfl⟩

theorem exists_down (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (s₂ : ∀ k, ι₂ k) : ∃ s₁ : ∀ k, ι₁ k, ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩ := by
  have h : ∀ k, ∃ i : ι₁ k, σ.symm ⟨e k, s₂ (e k)⟩ = ⟨k, i⟩ := fun k => by
    apply exists_snd
    apply e.injective
    rw [← hσ, Equiv.apply_symm_apply]
  choose s₁ hs using h
  exact ⟨s₁, fun k => by rw [← hs k, Equiv.apply_symm_apply]⟩

theorem exists_up (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (s₁ : ∀ k, ι₁ k) : ∃ s₂ : ∀ k, ι₂ k, ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩ := by
  have h : ∀ k, ∃ i : ι₂ k, σ ⟨e.symm k, s₁ (e.symm k)⟩ = ⟨k, i⟩ := fun k => by
    apply exists_snd
    rw [hσ, Equiv.apply_symm_apply]
  choose s₂ hs using h
  refine ⟨s₂, fun k => ?_⟩
  rw [← hs (e k)]
  exact congrArg (fun k => σ ⟨k, s₁ k⟩) (e.symm_apply_apply k).symm

theorem down_unique (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) {s₂ : ∀ k, ι₂ k}
    {s₁ t₁ : ∀ k, ι₁ k} (hs : ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩)
    (ht : ∀ k, σ ⟨k, t₁ k⟩ = ⟨e k, s₂ (e k)⟩) : s₁ = t₁ := by
  funext k
  have h := σ.injective ((hs k).trans (ht k).symm)
  exact eq_of_heq (Sigma.mk.inj_iff.1 h).2

variable {Ω : Type} [Field Ω]

theorem cone_rename (O : Type) [CommRing O] [Algebra O Ω] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω)
    (f : MvPolynomial (Σ k, ι₁ k) O) :
    pointConeMap O y (rename σ f) = rename e (pointConeMap O (y ∘ σ) f) := by
  have key : (pointConeMap O y).comp (rename σ) =
      ((rename e : MvPolynomial K₁ Ω →ₐ[Ω] MvPolynomial K₂ Ω).restrictScalars O).comp
        (pointConeMap O (y ∘ σ)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, hσ]
  exact congrArg (fun φ => φ f) key

theorem pointIdeal_eq (O : Type) [CommRing O] [Algebra O Ω] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω) :
    pointIdeal O y = (pointIdeal O (y ∘ σ)).map (rename σ) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨f, rfl⟩ := rename_surjective (R := O) σ σ.surjective g
    apply Ideal.mem_map_of_mem
    have h0 : pointConeMap O y (rename σ f) = 0 := hg
    rw [cone_rename O e σ hσ] at h0
    show pointConeMap O (y ∘ σ) f = 0
    apply rename_injective e e.injective
    rw [h0, map_zero]
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    have h0 : pointConeMap O (y ∘ σ) f = 0 := hf
    show pointConeMap O y (rename σ f) = 0
    rw [cone_rename O e σ hσ, h0, map_zero]

theorem fnField_eq (O : Type) [CommRing O] [Algebra O Ω] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω) :
    fnField O y = fnField O (y ∘ σ) := by
  unfold fnField
  congr 2
  ext a
  constructor
  · rintro ⟨⟨k, i, j⟩, rfl⟩
    have h : ∀ i : ι₂ k, ∃ i' : ι₁ (e.symm k), σ.symm ⟨k, i⟩ = ⟨e.symm k, i'⟩ := fun i => by
      apply exists_snd
      apply e.injective
      rw [← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    obtain ⟨i', hi⟩ := h i
    obtain ⟨j', hj⟩ := h j
    refine ⟨⟨e.symm k, i', j'⟩, ?_⟩
    simp only [Function.comp]
    rw [← hi, ← hj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · rintro ⟨⟨k, i, j⟩, rfl⟩
    obtain ⟨i', hi⟩ := exists_snd (σ ⟨k, i⟩) (e k) (hσ _)
    obtain ⟨j', hj⟩ := exists_snd (σ ⟨k, j⟩) (e k) (hσ _)
    refine ⟨⟨e k, i', j'⟩, ?_⟩
    simp only [Function.comp]
    rw [hi, hj]

variable [Fintype K₁] [Fintype K₂] [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)]

theorem mseg_eq (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (y : (Σ k, ι₂ k) → Ω)
    {s₁ : ∀ k, ι₁ k} {s₂ : ∀ k, ι₂ k} (hs : ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) :
    mseg y s₂ = mseg (y ∘ σ) s₁ := by
  simp only [mseg, Function.comp, hs]
  exact (Equiv.prod_comp e (fun k => y ⟨k, s₂ k⟩)).symm

theorem mon_eq (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (y : (Σ k, ι₂ k) → Ω)
    {s₁ : ∀ k, ι₁ k} {s₂ : ∀ k, ι₂ k} (hs : ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) (a : K₂ → ℤ) :
    ∏ k, y ⟨k, s₂ k⟩ ^ a k = ∏ k, (y ∘ σ) ⟨k, s₁ k⟩ ^ (a ∘ e) k := by
  simp only [Function.comp, hs]
  exact (Equiv.prod_comp e (fun k => y ⟨k, s₂ k⟩ ^ a k)).symm

theorem chartRing_eq (O : Type) [CommRing O] [Algebra O Ω] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω)
    {s₁ : ∀ k, ι₁ k} {s₂ : ∀ k, ι₂ k} (hs : ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) :
    chartRing O (mseg y) s₂ = chartRing O (mseg (y ∘ σ)) s₁ := by
  unfold chartRing
  congr 1
  ext a
  simp only [Set.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨t₁, ht⟩ := exists_down e σ hσ t
    exact ⟨t₁, by rw [mseg_eq e σ y hs, mseg_eq e σ y ht]⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨t₂, ht⟩ := exists_up e σ hσ t
    exact ⟨t₂, by rw [mseg_eq e σ y hs, mseg_eq e σ y ht]⟩

end PositivityTheory.Xgn.A_relabel_bundle

open PositivityTheory.Xgn.A_relabel_bundle in
theorem PositivityTheory.Xgn.t_relabel_bundle : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K₁ : Type) [Fintype K₁] [DecidableEq K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] [DecidableEq K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) → ∀ y : (Σ k, ι₂ k) → Ω, pointIdeal O y = (pointIdeal O (y ∘ σ)).map (rename σ) ∧ fnField O y = fnField O (y ∘ σ) ∧ ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E₁ : ChartBundle O (mseg (y ∘ σ)) N V), ∃ E₂ : ChartBundle O (mseg y) N V, (∀ (s₁ : ∀ k, ι₁ k) (s₂ : ∀ k, ι₂ k), (∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) → E₂.lat s₂ = E₁.lat s₁) ∧ ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K₂ → ℤ), IsFlagFrame (y ∘ σ) E₁ w (fun i => b i ∘ e) → IsFlagFrame y E₂ w b := by
  intro O _ Ω _ _ K₁ _ _ ι₁ _ K₂ _ _ ι₂ _ e σ hσ y
  refine ⟨pointIdeal_eq O e σ hσ y, fnField_eq O e σ hσ y, fun N V _ _ E₁ => ?_⟩
  choose d hd using exists_down e σ hσ
  have hm : ∀ s, mseg y s = mseg (y ∘ σ) (d s) := fun s => mseg_eq e σ y (hd s)
  have hc : ∀ s, chartRing O (mseg y) s = chartRing O (mseg (y ∘ σ)) (d s) :=
    fun s => chartRing_eq O e σ hσ y (hd s)
  refine ⟨{ lat := fun s => E₁.lat (d s)
            stable := fun s a ha v hv => E₁.stable (d s) a (by rw [← hc]; exact ha) v hv
            frame := fun s hs => by
              simp only [hc]
              exact E₁.frame (d s) (by rw [← hm]; exact hs)
            overlap := fun s t hs ht v hv => by
              simp only [hm]
              exact E₁.overlap (d s) (d t) (by rw [← hm]; exact hs) (by rw [← hm]; exact ht) v hv },
    fun s₁ s₂ h => ?_, fun w b h => ⟨fun s hs i => ?_⟩⟩
  · show E₁.lat (d s₂) = E₁.lat s₁
    rw [down_unique e σ (hd s₂) h]
  · have hs' : segreVec (y ∘ σ) (d s) ≠ 0 := by
      show mseg (y ∘ σ) (d s) ≠ 0
      rw [← hm]
      exact hs
    refine (h.graded (d s) hs' i).trans ?_
    have hc' : chartRing O (segreVec y) s = chartRing O (segreVec (y ∘ σ)) (d s) := hc s
    unfold degLat
    rw [hc', mon_eq e σ y (hd s) (b i)]
end

