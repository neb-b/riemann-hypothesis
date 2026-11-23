module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0009
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0014
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingDimLe

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.NonvanishingPointsDense
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem PositivityTheory.Xgn.nonvanishing_points_dense : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.proof)
      GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.proof)
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFlattenLines
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_flatten_lines

theorem span_line {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R R' : Subalgebra O Ω) (hle : R ≤ R')
    {M : ℕ} (v : Fin M → Ω) (m : Ω) (l₀ : Fin M) (h0 : v l₀ ≠ 0) (hq : ∀ l, v l / v l₀ ∈ R') (w : Ω) :
    w ∈ spanOver R' (spanOver R (Set.range fun l => m • v l) : Set Ω) ↔ ∃ r ∈ R', w = r * (m * v l₀) := by
  let L : AddSubgroup Ω :=
    { carrier := {w | ∃ r ∈ R', w = r * (m * v l₀)}
      add_mem' := by
        rintro _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
        exact ⟨r + s, R'.add_mem hr hs, by ring⟩
      zero_mem' := ⟨0, R'.zero_mem, by simp⟩
      neg_mem' := by
        rintro _ ⟨r, hr, rfl⟩
        exact ⟨-r, R'.neg_mem hr, by ring⟩ }
  have hin : spanOver R (Set.range fun l => m • v l) ≤ L := by
    unfold spanOver
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, ⟨l, rfl⟩, rfl⟩
    refine ⟨a * (v l / v l₀), R'.mul_mem (hle ha) (hq l), ?_⟩
    simp only [smul_eq_mul]
    field_simp
  have hout : spanOver R' (spanOver R (Set.range fun l => m • v l) : Set Ω) ≤ L := by
    unfold spanOver
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, he, rfl⟩
    obtain ⟨r, hr, rfl⟩ := hin he
    exact ⟨a * r, R'.mul_mem ha hr, by simp only [smul_eq_mul]; ring⟩
  constructor
  · intro hw
    exact hout hw
  · rintro ⟨r, hr, rfl⟩
    have hm : m • v l₀ ∈ spanOver R (Set.range fun l => m • v l) :=
      AddSubgroup.subset_closure ⟨1, R.one_mem, m • v l₀, ⟨l₀, rfl⟩, by simp⟩
    exact AddSubgroup.subset_closure ⟨r, hr, m • v l₀, hm, by simp⟩

theorem chartMon_join {Ω : Type} [Field Ω] {K K' : Type} [Fintype K] [Fintype K'] [DecidableEq K']
    {ι : K → Type} {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (c : ∀ k : K ⊕ K', Sum.elim ι ι' k) (a : K → ℤ) (j : K') :
    chartMon (joinCoord x z) c (Sum.elim (-a) (Pi.single j 1)) =
      (chartMon x (restrictChart c) a)⁻¹ * z ⟨j, c (.inr j)⟩ := by
  unfold chartMon restrictChart
  rw [Fintype.prod_sum_type]
  simp only [joinCoord, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

end PositivityTheory.Xgn.A_flatten_lines

theorem PositivityTheory.Xgn.t_flatten_lines : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ (I : Type) [Fintype I] (Γ : I → (∀ k, ι k) → AddSubgroup Ω), (∀ j, IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → Γ j c ≠ ⊥ ∧ ∃ S : Finset Ω, Γ j c = spanOver (chartRing O (mseg x) c) (S : Set Ω)) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ ∀ j, ∃ a : K ⊕ K' → ℤ, IsLine O (joinCoord x z) 1 a fun c => spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set Ω) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hmod hfn I _ Γ hΓ
  classical
  obtain ⟨_, hx0, _, _⟩ := (PositivityTheory.Xgn.A_join_model.isModelOver_iff x d).mp hmod
  choose c0 hc0 using hx0
  have hm0 : mseg x c0 ≠ 0 := by
    unfold mseg
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hc0 k
  have key : ∀ j, ∃ (a : K → ℤ) (M : ℕ) (v : Fin M → Ω), ∀ c, mseg x c ≠ 0 →
      Γ j c = spanOver (chartRing O (mseg x) c) (Set.range fun l => (chartMon x c a)⁻¹ • v l) := by
    intro j
    obtain ⟨a₁, ha₁⟩ := PositivityTheory.Xgn.t_coherent_gens O Ω K ι x Ω (Γ j) (hΓ j).1
      (fun c hc => ((hΓ j).2 c hc).2)
    obtain ⟨M, v, hv⟩ := ha₁ a₁ le_rfl
    exact ⟨a₁, M, v, hv⟩
  choose a M v hv using key
  have hnz : ∀ j, ∃ l, v j l ≠ 0 := by
    intro j
    by_contra hall
    push_neg at hall
    apply ((hΓ j).2 c0 hm0).1
    rw [hv j c0 hm0, eq_bot_iff]
    unfold spanOver
    rw [AddSubgroup.closure_le]
    rintro _ ⟨r, _, e, ⟨l, rfl⟩, rfl⟩
    simp [hall l]
  let z : (Σ j : I, Fin (M j)) → Ω := fun p => v p.1 p.2
  have hJ := (PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x).2.2 I (fun j => Fin (M j)) z
  refine ⟨I, inferInstance, inferInstance, fun j => Fin (M j), fun _ => inferInstance, z, ?_, ?_⟩
  · have hmodJ := PositivityTheory.Xgn.t_join_model O Ω K ι x d 0 hmod I (fun j => Fin (M j)) z hnz
      Fin.elim0 algebraicIndependent_empty_type (fun i => Fin.elim0 i) ?_
    · simpa using hmodJ
    · intro w _
      have hw : w ∈ fnField O x := by
        rw [hfn]
        exact Subfield.mem_top w
      exact isAlgebraic_algebraMap
        (⟨w, IntermediateField.algebraMap_mem _ (⟨w, hw⟩ : fnField O x)⟩ :
          IntermediateField.adjoin (fnField O x) (Set.range (Fin.elim0 : Fin 0 → Ω)))
  · intro j
    refine ⟨Sum.elim (-a j) (Pi.single j 1), ?_⟩
    intro c hc w
    obtain ⟨hrc, hle⟩ := hJ.2 c hc
    have hmz := PositivityTheory.Xgn.A_chart_noeth_frac.mseg_join x z c
    have hz0 : z ⟨j, c (Sum.inr j)⟩ ≠ 0 := by
      rw [hmz] at hc
      have h2 := right_ne_zero_of_mul hc
      unfold mseg at h2
      exact Finset.prod_ne_zero_iff.mp h2 j (Finset.mem_univ _)
    show w ∈ spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set Ω) ↔ _
    rw [hv j _ hrc, one_mul, PositivityTheory.Xgn.A_flatten_lines.chartMon_join]
    refine PositivityTheory.Xgn.A_flatten_lines.span_line _ _ hle _ _ (c (Sum.inr j)) hz0 ?_ w
    intro l
    have h := PositivityTheory.Xgn.A_chart_noeth_frac.ratio_eq (joinCoord x z) c hc (Sum.inr j) l
    have hmem : mseg (joinCoord x z) (Function.update c (Sum.inr j) l) / mseg (joinCoord x z) c ∈
        chartRing O (mseg (joinCoord x z)) c := Algebra.subset_adjoin ⟨_, rfl⟩
    rw [h] at hmem
    exact hmem
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFlattenMany
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_flatten_many

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {V : Type} [AddCommGroup V] [Module Ω V]

theorem mem_span (R : Subalgebra O Ω) {S : Set V} {e : V} (he : e ∈ S) {a : Ω} (ha : a ∈ R) :
    a • e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨a, ha, e, he, rfl⟩

theorem smul_mem_span (R : Subalgebra O Ω) (S : Set V) {a : Ω} (ha : a ∈ R) {e : V}
    (he : e ∈ spanOver R S) : a • e ∈ spanOver R S := by
  induction he using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, w, hw, rfl⟩ := hy
    rw [smul_smul]
    exact mem_span R hw (mul_mem ha hb)
  | zero => rw [smul_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [smul_add]; exact add_mem hy hw
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

def combs (R : Subalgebra O Ω) {N : ℕ} (b : Fin N → V) : AddSubgroup V where
  carrier := {e | ∃ a : Fin N → Ω, (∀ q, a q ∈ R) ∧ e = ∑ q, a q • b q}
  zero_mem' := ⟨0, fun _ => zero_mem _, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
    exact ⟨a + a', fun q => add_mem (ha q) (ha' q), by simp [add_smul, Finset.sum_add_distrib]⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, fun q => neg_mem (ha q), by simp⟩

theorem smul_mem_combs (R : Subalgebra O Ω) {N : ℕ} (b : Fin N → V) {a : Ω} (ha : a ∈ R) {e : V}
    (he : e ∈ combs R b) : a • e ∈ combs R b := by
  obtain ⟨u, hu, rfl⟩ := he
  exact ⟨fun q => a * u q, fun q => mul_mem ha (hu q), by simp [Finset.smul_sum, smul_smul]⟩

theorem spanOver_le_combs (R R₀ : Subalgebra O Ω) (h : R₀ ≤ R) {N : ℕ} (b : Fin N → V) (S : Set V)
    (hS : ∀ e ∈ S, e ∈ combs R b) : spanOver R₀ S ≤ combs R b := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact smul_mem_combs R b (h ha) (hS e he)

theorem locFree_of_minor (R R₀ : Subalgebra O Ω) (h : R₀ ≤ R) {N M : ℕ} (B : Module.Basis (Fin N) Ω V)
    (v : Fin M → V) (p : Ω) (hp : p ≠ 0) (I : Fin N → Fin M) (hI : B.det (v ∘ I) ≠ 0)
    (hJ : ∀ J : Fin N → Fin M, B.det (v ∘ J) / B.det (v ∘ I) ∈ R) :
    LocFree R N (spanOver R (spanOver R₀ (Set.range fun l => p • v l) : Set V)) := by
  classical
  obtain ⟨hli, hsp⟩ := (B.is_basis_iff_det (v := v ∘ I)).2 (Ne.isUnit hI)
  let C := Module.Basis.mk hli hsp.ge
  have hC : ∀ q, C q = v (I q) := fun q => Module.Basis.mk_apply hli hsp.ge q
  have hco : ∀ l q, C.repr (v l) q ∈ R := by
    intro l q
    have h1 := LinearMap.congr_fun (B.det_smul_mk_coord_eq_det_update hli hsp.ge q) (v l)
    have h2 : B.det (v ∘ I) * C.repr (v l) q = B.det (v ∘ Function.update I q l) := by
      rw [Function.comp_update]
      exact h1
    have h3 : C.repr (v l) q = B.det (v ∘ Function.update I q l) / B.det (v ∘ I) := by
      rw [eq_div_iff hI, mul_comm, h2]
    rw [h3]
    exact hJ _
  let b : Fin N → V := fun q => p • v (I q)
  have hb : b = ⇑(C.unitsSMul fun _ => Units.mk0 p hp) := by
    funext q
    rw [Module.Basis.unitsSMul_apply, hC]
    rfl
  have key : spanOver R (spanOver R₀ (Set.range fun l => p • v l) : Set V) = combs R b := by
    apply le_antisymm
    · refine spanOver_le_combs R R le_rfl b _ fun e he => ?_
      refine spanOver_le_combs R R₀ h b _ ?_ he
      rintro _ ⟨l, rfl⟩
      refine ⟨fun q => C.repr (v l) q, hco l, ?_⟩
      have e1 := C.sum_repr (v l)
      simp only [b]
      conv_lhs => rw [← e1]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hC, smul_comm]
    · rintro _ ⟨a, ha, rfl⟩
      refine sum_mem fun q _ => mem_span R ?_ (ha q)
      have := mem_span R₀ (S := Set.range fun l => p • v l) ⟨I q, rfl⟩ (one_mem R₀)
      rwa [one_smul] at this
  refine ⟨fun a ha e he => smul_mem_span R _ ha he, 1, fun _ => 1, fun _ => 1, fun _ => one_mem _,
    fun _ => one_mem _, by simp, fun _ => ⟨b, ?_, ?_, fun e => ?_⟩⟩
  · rw [hb]; exact Module.Basis.linearIndependent _
  · rw [hb]; exact Module.Basis.span_eq _
  · rw [key]
    simp only [one_pow, one_smul, one_mul, exists_const]
    rfl

theorem exists_minor {N M : ℕ} (hN : Module.finrank Ω V = N) (v : Fin M → V)
    (hv : Submodule.span Ω (Set.range v) = ⊤) :
    ∃ (B : Module.Basis (Fin N) Ω V) (I : Fin N → Fin M), B.det (v ∘ I) ≠ 0 := by
  classical
  obtain ⟨κ, e, he, hsp, hli⟩ := exists_linearIndependent' Ω v
  haveI : Finite κ := Finite.of_injective e he
  letI : Fintype κ := Fintype.ofFinite κ
  let B : Module.Basis κ Ω V := Module.Basis.mk hli (by rw [hsp, hv])
  have hc : Fintype.card κ = N := by rw [← hN, Module.finrank_eq_card_basis B]
  let σ : κ ≃ Fin N := Fintype.equivFinOfCardEq hc
  refine ⟨B.reindex σ, fun a => e (σ.symm a), ?_⟩
  have : (v ∘ fun a => e (σ.symm a)) = ⇑(B.reindex σ) := by
    funext a
    rw [Module.Basis.reindex_apply]
    exact (Module.Basis.mk_apply hli _ _).symm
  rw [this, Module.Basis.det_self]
  exact one_ne_zero

theorem span_top (R : Subalgebra O Ω) (S : Set V) (hS : Submodule.span Ω S = ⊤) {M : ℕ} (v : Fin M → V)
    (p : Ω) (h : spanOver R S = spanOver R (Set.range fun l => p • v l)) :
    Submodule.span Ω (Set.range v) = ⊤ := by
  rw [eq_top_iff, ← hS, Submodule.span_le]
  intro e he
  have h1 := mem_span R he (one_mem R)
  rw [one_smul, h] at h1
  have h2 : spanOver R (Set.range fun l => p • v l) ≤ (Submodule.span Ω (Set.range v)).toAddSubgroup := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, -, _, ⟨l, rfl⟩, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  exact h2 h1

end PositivityTheory.Xgn.A_flatten_many

open PositivityTheory.Xgn.A_flatten_many in
theorem PositivityTheory.Xgn.t_flatten_many : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ (I : Type) [Fintype I] (N : I → ℕ) (V : I → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module Ω (V j)] (Γ : ∀ j, (∀ k, ι k) → AddSubgroup (V j)), (∀ j, Module.finrank Ω (V j) = N j ∧ IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → ∃ S : Finset (V j), Γ j c = spanOver (chartRing O (mseg x) c) (S : Set (V j)) ∧ Submodule.span Ω (S : Set (V j)) = ⊤) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ ∀ j c, mseg (joinCoord x z) c ≠ 0 → LocFree (chartRing O (mseg (joinCoord x z)) c) (N j) (spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set (V j))) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hM hF I _ N V _ _ Γ hΓ
  classical
  have hjoin : ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (z : (Σ k, ι' k) → Ω), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d := by
    intro K' _ _ ι' _ z hz
    refine PositivityTheory.Xgn.t_join_model O Ω K ι x d 0 hM K' ι' z hz Fin.elim0
      algebraicIndependent_empty_type (fun i => i.elim0) fun v _ => ?_
    have hv : v ∈ fnField O x := hF ▸ Subfield.mem_top v
    exact isAlgebraic_algebraMap
      (⟨v, IntermediateField.algebraMap_mem _ (⟨v, hv⟩ : fnField O x)⟩ :
        IntermediateField.adjoin (fnField O x) (Set.range (Fin.elim0 : Fin 0 → Ω)))
  have hch := (PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x).2.2
  by_cases h0 : ∃ c₀, mseg x c₀ ≠ 0
  · obtain ⟨c₀, hc₀⟩ := h0
    have hg : ∀ j, ∃ (a : K → ℤ) (M : ℕ) (v : Fin M → V j) (B : Module.Basis (Fin (N j)) Ω (V j)),
        (∃ J : Fin (N j) → Fin M, B.det (v ∘ J) ≠ 0) ∧ ∀ c, mseg x c ≠ 0 →
          Γ j c = spanOver (chartRing O (mseg x) c) (Set.range fun l => (chartMon x c a)⁻¹ • v l) := by
      intro j
      obtain ⟨h1, h2, h3⟩ := hΓ j
      obtain ⟨a, ha⟩ := PositivityTheory.Xgn.t_coherent_gens O Ω K ι x (V j) (Γ j) h2
        fun c hc => (h3 c hc).imp fun _ h => h.1
      obtain ⟨M, v, hv⟩ := ha a le_rfl
      obtain ⟨S, hS, hS'⟩ := h3 c₀ hc₀
      obtain ⟨B, J, hJ⟩ := exists_minor h1 v (span_top _ _ hS' v _ (hS.symm.trans (hv c₀ hc₀)))
      exact ⟨a, M, v, B, ⟨J, hJ⟩, hv⟩
    choose a M v B hJ hv using hg
    let ι' : I → Type := fun j => Fin (N j) → Fin (M j)
    let z : (Σ j, ι' j) → Ω := fun q => (B q.1).det (v q.1 ∘ q.2)
    refine ⟨I, inferInstance, inferInstance, ι', inferInstance, z, hjoin I ι' z hJ, fun j c hc => ?_⟩
    obtain ⟨hc1, hle⟩ := (hch I ι' z).2 c hc
    rw [hv j _ hc1]
    have hk : ∀ k, x ⟨k, restrictChart c k⟩ ≠ 0 :=
      fun k => Finset.prod_ne_zero_iff.1 hc1 k (Finset.mem_univ k)
    refine locFree_of_minor _ _ hle (B j) (v j) _ (inv_ne_zero ?_) (c (.inr j))
      (Finset.prod_ne_zero_iff.1 hc (.inr j) (Finset.mem_univ _)) fun J => ?_
    · exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hk k)
    · have h := PositivityTheory.Xgn.A_chart_noeth_frac.ratio_eq (joinCoord x z) c hc (.inr j) J
      change joinCoord x z ⟨.inr j, J⟩ / joinCoord x z ⟨.inr j, c (.inr j)⟩ ∈ _
      rw [← h]
      exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
  · let ι' : Empty → Type := fun _ => Empty
    let z : (Σ k, ι' k) → Ω := fun _ => 0
    refine ⟨Empty, inferInstance, inferInstance, ι', inferInstance, z, hjoin Empty ι' z (fun k => k.elim),
      fun j c hc => ?_⟩
    exact absurd ⟨_, ((hch Empty ι' z).2 c hc).1⟩ h0
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSDivcyclehomloc
section
namespace PositivityTheory.Xgn.A_s_divcyclehomloc

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem homLocRingLocal : HomLocRingLocal.Statement.{0} :=
  HomLocRingLocal.proof (HomLocRingIsLocal.proof HomLocRingMem.proof)
    (HomLocRingNoetherian.proof HomLocRingMem.proof)
    (HomLocRingDimLe.proof HomLocRingMem.proof (HomLocRingIsLocal.proof HomLocRingMem.proof))

end PositivityTheory.Xgn.A_s_divcyclehomloc

theorem PositivityTheory.Xgn.t_s_divcyclehomloc : GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.Statement.{0} :=
  GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.proof PositivityTheory.Xgn.A_s_divcyclehomloc.homLocRingLocal
end

