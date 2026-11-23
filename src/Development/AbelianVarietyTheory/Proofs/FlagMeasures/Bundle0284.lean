module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0001
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerLatticeIdentificationCompatOfGraphEq
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IotaGraph

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem mem_gmap_iff (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.gmap ψ Λ ↔ ψ.symm x ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨ψ.symm x, h, by simp⟩

theorem mem_map_iff (ψ : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) (x : S.V) :
    x ∈ U.map (ψ : S.V →ₗ[E] S.V) ↔ ψ.symm x ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨ψ.symm x, h, by simp⟩

theorem mem_orth_iff (U : Submodule E S.V) (x : S.V) :
    x ∈ orth S U ↔ ∀ y ∈ U, S.hT y x = 0 := by
  unfold orth
  simp [Submodule.mem_iInf]

theorem mem_orth_map (ψ : S.V ≃ₗ[E] S.V) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (U : Submodule E S.V)
    (x : S.V) : x ∈ orth S (U.map (ψ : S.V →ₗ[E] S.V)) ↔ ψ.symm x ∈ orth S U := by
  have hi : ∀ a b, S.hT (ψ a) (ψ b) = S.hT a b := hψ
  rw [mem_orth_iff, mem_orth_iff]
  constructor
  · intro h y hy
    have := h (ψ y) ⟨y, hy, rfl⟩
    rw [← hi y (ψ.symm x)]
    simpa using this
  · rintro h _ ⟨y, hy, rfl⟩
    have := h y hy
    rw [← hi y (ψ.symm x)] at this
    simpa using this

variable {T T' : E}

theorem mem_Lrep_map (ψ : S.V ≃ₗ[E] S.V) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F G : LFlag S r T) (hF : (Xsp F).map (ψ : S.V →ₗ[E] S.V) = Xsp G) (x : S.V) :
    x ∈ Lrep (Formalism.HermitianLatticesTheory.gmap ψ Λ) G ↔ ψ.symm x ∈ Lrep Λ F := by
  unfold Lrep
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_gmap_iff, toO, toO, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, ← hF, mem_orth_map ψ hψ]

theorem gmap_eq (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap ψ Λ = Λ.map (ψ.restrictScalars (𝓞 E) : S.V →ₗ[𝓞 E] S.V) := by
  ext x
  rw [mem_gmap_iff, Submodule.mem_map_equiv]
  rfl

theorem XLam_map (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V)
    (F G : LFlag S r T) (hF : (Xsp F).map (ψ : S.V →ₗ[E] S.V) = Xsp G) :
    XLam (Formalism.HermitianLatticesTheory.gmap ψ Λ) G = (XLam Λ F).map (ψ.restrictScalars (𝓞 E) : S.V →ₗ[𝓞 E] S.V) := by
  ext x
  rw [Submodule.mem_map_equiv]
  unfold XLam
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_gmap_iff, toO, toO, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, ← hF, mem_map_iff]
  rfl

theorem mem_NgX_map (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) (g : ℕ)
    (F G : LFlag S r T) (F' G' : LFlag S r T') (hF : (Xsp F).map (ψ : S.V →ₗ[E] S.V) = Xsp G)
    (hF' : (Xsp F').map (ψ : S.V →ₗ[E] S.V) = Xsp G') (x : S.V) :
    x ∈ NgX (Formalism.HermitianLatticesTheory.gmap ψ Λ) g G G' ↔ ψ.symm x ∈ NgX Λ g F F' := by
  have h : NgX (Formalism.HermitianLatticesTheory.gmap ψ Λ) g G G' =
      (NgX Λ g F F').map (ψ.restrictScalars (𝓞 E) : S.V →ₗ[𝓞 E] S.V) := by
    unfold NgX
    rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'', XLam_map ψ Λ F G hF,
      XLam_map ψ Λ F' G' hF', gmap_eq]
  rw [h, Submodule.mem_map_equiv]
  rfl

end Gen

end GlobalTheory.IotaGraph

namespace GlobalTheory.IotaGraph

section Dv

variable {D : D7} {T T' : D.host.E}

theorem mem_graph_iff (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D)
    {x' l : (VS D).V} (hx' : x' ∈ Lrep Λ F') (hl : l ∈ Lrep Λ F) :
    (x', l) ∈ (gdat F F' Λ).2.2 ↔ l - x' ∈ NgX Λ (gS D) F F' := by
  simp only [gdat, Set.mem_setOf_eq]
  constructor
  · rintro ⟨l', hl', l₀, hl₀, h1, h2, h3⟩
    have hx'Λ : x' ∈ Λ := (Submodule.mem_inf.1 hx').1
    have hlΛ : l ∈ Λ := (Submodule.mem_inf.1 hl).1
    have hl'Λ : l' ∈ Λ := (Submodule.mem_inf.1 hl').1
    have hl₀Λ : l₀ ∈ Λ := (Submodule.mem_inf.1 hl₀).1
    have a1 : x' - l' ∈ XLam Λ F' := Submodule.mem_inf.2 ⟨Λ.sub_mem hx'Λ hl'Λ, h1⟩
    have a2 : l - l₀ ∈ XLam Λ F := Submodule.mem_inf.2 ⟨Λ.sub_mem hlΛ hl₀Λ, h2⟩
    have b1 : x' - l' ∈ NgX Λ (gS D) F F' := by
      unfold NgX; exact Submodule.mem_sup_right a1
    have b2 : l - l₀ ∈ NgX Λ (gS D) F F' := by
      unfold NgX; exact Submodule.mem_sup_left (Submodule.mem_sup_right a2)
    have e : l - x' = (l - l₀) + (l₀ - l') - (x' - l') := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.add_mem _ b2 h3) b1
  · intro h
    exact ⟨x', hx', l, hl, by simp, by simp, h⟩

theorem mem_graph_of_sub (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D)
    {p q : (VS D).V × (VS D).V} (h1 : q.1 - p.1 ∈ Xsp F') (h2 : q.2 - p.2 ∈ Xsp F)
    (hp : p ∈ (gdat F F' Λ).2.2) : q ∈ (gdat F F' Λ).2.2 := by
  simp only [gdat, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨l', hl', l, hl, k1, k2, k3⟩ := hp
  refine ⟨l', hl', l, hl, ?_, ?_, k3⟩
  · have e : q.1 - l' = (q.1 - p.1) + (p.1 - l') := by abel
    rw [e]; exact Submodule.add_mem _ h1 k1
  · have e : q.2 - l = (q.2 - p.2) + (p.2 - l) := by abel
    rw [e]; exact Submodule.add_mem _ h2 k2

theorem mem_graph_congr (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D)
    {p q : (VS D).V × (VS D).V} (h1 : q.1 - p.1 ∈ Xsp F') (h2 : q.2 - p.2 ∈ Xsp F) :
    p ∈ (gdat F F' Λ).2.2 ↔ q ∈ (gdat F F' Λ).2.2 := by
  refine ⟨mem_graph_of_sub F F' Λ h1 h2, mem_graph_of_sub F F' Λ ?_ ?_⟩
  · rw [← neg_sub]; exact Submodule.neg_mem _ h1
  · rw [← neg_sub]; exact Submodule.neg_mem _ h2

theorem mem_graph_map (ψ : GV D) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (F G : LFlag (D.sp.Y 0) D.R.rS T) (F' G' : LFlag (D.sp.Y 0) D.R.rS T')
    (hF : (Xsp F).map (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G)
    (hF' : (Xsp F').map (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G') (Λ : LV D) (x y : (VS D).V) :
    (x, y) ∈ (gdat F F' Λ).2.2 ↔ (ψ x, ψ y) ∈ (gdat G G' (Formalism.HermitianLatticesTheory.gmap ψ Λ)).2.2 := by
  simp only [gdat, Set.mem_setOf_eq]
  constructor
  · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
    refine ⟨ψ l', ?_, ψ l, ?_, ?_, ?_, ?_⟩
    · rw [mem_Lrep_map ψ hψ Λ F' G' hF']; simpa using hl'
    · rw [mem_Lrep_map ψ hψ Λ F G hF]; simpa using hl
    · rw [← hF', mem_map_iff]; simpa using h1
    · rw [← hF, mem_map_iff]; simpa using h2
    · rw [mem_NgX_map ψ Λ (gS D) F G F' G' hF hF']; simpa using h3
  · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
    refine ⟨ψ.symm l', (mem_Lrep_map ψ hψ Λ F' G' hF' l').1 hl', ψ.symm l,
      (mem_Lrep_map ψ hψ Λ F G hF l).1 hl, ?_, ?_, ?_⟩
    · rw [← hF', mem_map_iff] at h1; simpa using h1
    · rw [← hF, mem_map_iff] at h2; simpa using h2
    · rw [mem_NgX_map ψ Λ (gS D) F G F' G' hF hF'] at h3; simpa using h3

end Dv

end GlobalTheory.IotaGraph

namespace GlobalTheory

open GlobalTheory.IotaGraph

theorem iotaCompat_of_graph_eq : ∀ (D : D7) (T T' : D.host.E) (F₀ B : LFlag (D.sp.Y 0) D.R.rS T) (P₁ P₂ B' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D) (ψ₀ ψ₁ β : GV D), ψ₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ψ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (Xsp F₀).map (ψ₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B → (Xsp F₀).map (ψ₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B → (Xsp P₁).map (ψ₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B' → (Xsp P₂).map (ψ₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B' → (gdat B B' (Formalism.HermitianLatticesTheory.gmap ψ₀ Λ)).2.2 = (gdat B B' (Formalism.HermitianLatticesTheory.gmap ψ₁ Λ)).2.2 → β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (Xsp P₁).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp P₂ → (∀ l ∈ Lrep Λ F₀, (ψ₁⁻¹ * ψ₀) l - l ∈ Xsp F₀) → (∀ x' ∈ Lrep Λ P₁, (ψ₁⁻¹ * ψ₀) x' - β x' ∈ Xsp P₂) → IotaCompat Λ F₀ P₁ P₂ β (gS D) := by
  intro D T T' F₀ B P₁ P₂ B' Λ ψ₀ ψ₁ β h0 h1 hF0 hF1 hP1 hP2 hgr hβ hβΛ hβP hml hmx x' hx' l hl
  have hc : ∀ y, ψ₁ ((ψ₁⁻¹ * ψ₀) y) = ψ₀ y := fun y => ψ₁.apply_symm_apply (ψ₀ y)

  have hβx : β x' ∈ Lrep Λ P₂ := by
    have := (mem_Lrep_map (S := VS D) β hβ Λ P₁ P₂ hβP (β x')).2 (by simpa using hx')
    rwa [hβΛ] at this
  have e1 := mem_graph_iff F₀ P₁ Λ hx' hl
  have e2 := mem_graph_map ψ₀ h0 F₀ B P₁ B' hF0 hP1 Λ x' l
  have e3 := mem_graph_map ψ₁ h1 F₀ B P₂ B' hF1 hP2 Λ ((ψ₁⁻¹ * ψ₀) x') ((ψ₁⁻¹ * ψ₀) l)
  rw [hc, hc] at e3
  have e4 := mem_graph_congr F₀ P₂ Λ (p := ((ψ₁⁻¹ * ψ₀) x', (ψ₁⁻¹ * ψ₀) l)) (q := (β x', l))
    (by rw [← neg_sub]; exact Submodule.neg_mem _ (hmx x' hx'))
    (by rw [← neg_sub]; exact Submodule.neg_mem _ (hml l hl))
  have e5 := mem_graph_iff F₀ P₂ Λ hβx hl
  rw [← e1, ← e5, e2, hgr, ← e3, e4]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantExtensionIntegrableOnCompact
section
open MeasureTheory Filter Set Formalism.MainNotions.S GlobalTheory.RightRegFund
open scoped ENNReal Pointwise

namespace GlobalTheory.LocalL2Isometry

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ]
  {D : Set G} {r : G → G}

private lemma card_le_of_translates_mem_mul_inv_tsum_indicator {C : Set G} (S : Finset Γ)
    (hS : ∀ γ : Γ, (γ : G) ∈ C * C⁻¹ → γ ∈ S) (x : G) :
    ∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) ≤ S.card := by
  classical
  by_cases h : ∃ γ₀ : Γ, (γ₀ : G) * x ∈ C
  · obtain ⟨γ₀, h₀⟩ := h
    have hsupp : ∀ γ ∉ S.image (· * γ₀),
        C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) = 0 := by
      intro γ hγ
      by_contra hne
      have hγC : (γ : G) * x ∈ C := by
        by_contra hn
        exact hne (Set.indicator_of_notMem hn _)
      apply hγ
      refine Finset.mem_image.2 ⟨γ * γ₀⁻¹, hS _ ?_, by simp⟩
      refine Set.mem_mul.2 ⟨(γ : G) * x, hγC, ((γ₀ : G) * x)⁻¹, by simpa using h₀, ?_⟩
      simp [mul_assoc]
    rw [tsum_eq_sum hsupp]
    calc ∑ γ ∈ S.image (· * γ₀), C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)
        ≤ ∑ _γ ∈ S.image (· * γ₀), (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun γ _ => ?_
          by_cases hm : (γ : G) * x ∈ C <;> simp [hm]
      _ = ((S.image (· * γ₀)).card : ℝ≥0∞) := by simp
      _ ≤ S.card := by exact_mod_cast Finset.card_image_le
  · push_neg at h
    simp [h]

theorem lintegral_rep_le (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {C : Set G} (hC : MeasurableSet C)
    (S : Finset Γ) (hS : ∀ γ : Γ, (γ : G) ∈ C * C⁻¹ → γ ∈ S) {φ : G → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ y in C, φ (r y) ∂μ ≤ S.card * ∫⁻ x in D, φ x ∂μ := by
  classical
  have hfix : ∀ᵐ x ∂μ.restrict D, ∀ γ : Γ, r ((γ : G) * x) = x := by
    filter_upwards [ae_restrict_of_ae (ae_good hD), ae_restrict_mem hDm] with x hx hxD γ
    rw [rep_mul hr hx γ]
    simpa using rep_eq hr hx (γ := 1) (by simpa using hxD)
  have hmeas : ∀ γ : Γ, AEMeasurable
      (fun x => C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x) (μ.restrict D) := fun γ =>
    (((measurable_const.indicator hC).comp (measurable_const_mul (γ : G))).mul hφ).aemeasurable
  calc ∫⁻ y in C, φ (r y) ∂μ = ∫⁻ y, C.indicator (fun y => φ (r y)) y ∂μ :=
        (lintegral_indicator hC _).symm
    _ = ∑' γ : Γ, ∫⁻ x in D, C.indicator (fun y => φ (r y)) (γ • x) ∂μ :=
        hD.lintegral_eq_tsum'' _
    _ = ∑' γ : Γ, ∫⁻ x in D, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x ∂μ := by
        refine tsum_congr fun γ => lintegral_congr_ae ?_
        filter_upwards [hfix] with x hx
        change C.indicator (fun y => φ (r y)) ((γ : G) * x) = _
        by_cases hm : (γ : G) * x ∈ C
        · simp [hm, hx γ]
        · simp [hm]
    _ = ∫⁻ x in D, ∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x ∂μ :=
        (lintegral_tsum hmeas).symm
    _ = ∫⁻ x in D, (∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) * φ x ∂μ :=
        lintegral_congr fun x => ENNReal.tsum_mul_right
    _ ≤ ∫⁻ x in D, (S.card : ℝ≥0∞) * φ x ∂μ :=
        lintegral_mono fun x => by gcongr; exact card_le_of_translates_mem_mul_inv_tsum_indicator S hS x
    _ = S.card * ∫⁻ x in D, φ x ∂μ := lintegral_const_mul _ hφ

theorem integrableOn_rep (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {C : Set G} (hC : MeasurableSet C)
    (hCf : μ C ≠ ∞) (S : Finset Γ) (hS : ∀ γ : Γ, (γ : G) ∈ C * C⁻¹ → γ ∈ S) :
    ∃ M : ℝ, ∀ F : Lp ℂ 2 (μ.restrict D), IntegrableOn (fun y => F (r y)) C μ ∧
      ∫ y in C, ‖F (r y)‖ ∂μ ≤ M * ‖F‖ := by
  refine ⟨((S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ)).toReal, fun F => ?_⟩
  haveI : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.2 hCf
  have hFm : Measurable (F : G → ℂ) := (Lp.stronglyMeasurable F).measurable
  have hgm : AEStronglyMeasurable (fun y => F (r y)) (μ.restrict C) :=
    (aestronglyMeasurable_comp_rep hD hDm hr (Lp.stronglyMeasurable F)).restrict
  have hcard : (S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.natCast_ne_top _)
  have hCr : μ C ^ (1 / 2 : ℝ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCf
  have h2 : eLpNorm (fun y => F (r y)) 2 (μ.restrict C) ≤
      (S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm F 2 (μ.restrict D) := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hgm,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
        (Lp.stronglyMeasurable F).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    gcongr
    exact lintegral_rep_le hD hDm hr hC S hS (φ := fun x => ‖F x‖ₑ ^ (2 : ℝ)) (by fun_prop)
  have h1 : eLpNorm (fun y => F (r y)) 1 (μ.restrict C) ≤
      eLpNorm (fun y => F (r y)) 2 (μ.restrict C) * μ C ^ (1 / 2 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hgm
    rw [Measure.restrict_apply_univ] at h
    convert h using 3
    norm_num
  have hL2 : MemLp (fun y => F (r y)) 2 (μ.restrict C) :=
    h2.trans_lt (ENNReal.mul_lt_top hcard.lt_top (Lp.eLpNorm_lt_top F))
  refine ⟨hL2.integrable (by norm_num), ?_⟩
  calc ∫ y in C, ‖F (r y)‖ ∂μ = (eLpNorm (fun y => F (r y)) 1 (μ.restrict C)).toReal := by
        rw [integral_norm_eq_lintegral_enorm hgm, eLpNorm_one_eq_lintegral_enorm hgm]
    _ ≤ ((S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm F 2 (μ.restrict D) * μ C ^ (1 / 2 : ℝ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hcard (Lp.eLpNorm_ne_top F)) hCr)
          (h1.trans (by gcongr))
    _ = ((S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ)).toReal * ‖F‖ := by
        rw [Lp.norm_def, ← ENNReal.toReal_mul, mul_right_comm]

theorem ext_integrableOn : ∀ (B : RowsAut) (C : Set B.I.GA), IsCompact C → ∃ M : ℝ,
    ∀ F : B.I.L2 B.μf B.fund, IntegrableOn (B.I.ext F) C (B.I.muA B.μf) ∧
      ∫ y in C, ‖B.I.ext F y‖ ∂(B.I.muA B.μf) ≤ M * ‖F‖ := by
  intro B C hC
  obtain ⟨Γ, hΓ, hΓc, hfin, hfd⟩ := _root_.GlobalTheory.RatDiscrete.rational_points B.I
  obtain ⟨hT2, -, hsc, -⟩ := _root_.GlobalTheory.CongTop.adelic_topology B.I
  haveI := hΓc
  haveI := hT2
  haveI := hsc
  have hD := hfd B.μf B.fund B.fund_spec
  haveI : (B.I.muA B.μf).IsMulLeftInvariant := ⟨(_root_.GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf).1⟩
  haveI : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA
    infer_instance
  have hDm : MeasurableSet B.fund := B.fund_spec.1
  have hr : ∀ y, ∃ γ : Γ, B.I.rep B.fund y = (γ : B.I.GA) * y ∧ B.I.rep B.fund y ∈ B.fund := by
    intro y
    have h := B.fund_spec.2.1 y
    refine ⟨⟨h.choose, ?_⟩, ?_, ?_⟩
    · rw [← SetLike.mem_coe, hΓ]
      exact h.choose_spec.1
    · rw [AutInst.rep, dite_eq_left h]
    · rw [AutInst.rep, dite_eq_left h]
      exact h.choose_spec.2
  have hK : IsCompact (C * C⁻¹) := hC.mul hC.inv
  have hSfin : {γ : Γ | (γ : B.I.GA) ∈ C * C⁻¹}.Finite :=
    ((hfin _ hK).preimage Subtype.val_injective.injOn).subset fun γ hγ => ⟨hγ, by
      rw [← hΓ]
      exact γ.2⟩
  obtain ⟨M, hM⟩ := integrableOn_rep hD hDm hr hC.measurableSet hC.measure_lt_top.ne
    hSfin.toFinset fun γ hγ => hSfin.mem_toFinset.2 hγ
  exact ⟨M, fun F => hM F⟩

end GlobalTheory.LocalL2Isometry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsComplHermitianOrthogonalOfTotallyPositive
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.isCompl_orth_of_definite {E : Type} [Field E] [NumberField E] [StarRing E]
    (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V)
    (hpos : ∀ x ∈ orth S U, x ≠ 0 → 0 < Algebra.trace ℚ E (S.hT x x)) :
    IsCompl U (orth S U) := by
  have hmem : ∀ v, v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
    intro v
    simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  have hdis : U ⊓ orth S U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases hx with ⟨hxU, hxO⟩
    by_contra hne
    have h0 : S.hT x x = 0 := (hmem x).1 hxO x hxU
    have := hpos x hxO hne
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  let b := Module.finBasis E U
  let φ : S.V →ₗ[E] (Fin (Module.finrank E U) → E) := LinearMap.pi fun i => S.hT (b i : S.V)
  have hker : LinearMap.ker φ ≤ orth S U := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [hmem]
    intro x hx
    have hy' : ∀ i, S.hT (b i : S.V) y = 0 := fun i => congrFun hy i
    have hx' : (⟨x, hx⟩ : U) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
    have hxs : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : S.V) := by
      have := congrArg (Subtype.val) hx'
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxs, map_sum]
    simp [LinearMap.sum_apply, hy']
  have hrk : Module.finrank E S.V ≤ Module.finrank E U + Module.finrank E (orth S U) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank E (LinearMap.range φ) ≤ Module.finrank E U := by
      have := Submodule.finrank_le (LinearMap.range φ)
      simpa using this
    have h3 := Submodule.finrank_mono hker
    omega
  have hcod : U ⊔ orth S U = ⊤ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U (orth S U)
    rw [hdis, finrank_bot] at h
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (U ⊔ orth S U)
    omega
  exact ⟨disjoint_iff.2 hdis, codisjoint_iff.2 hcod⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubspaceRingOfIntegers
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_ne_zero_smul_mem_of_span_eq_top {K V : Type} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.span K (Λ : Set V) = ⊤) (v : V) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.TargetStatementBis.target
  | exact _root_.GlobalTheory.TargetStatementBis.target
  | (apply _root_.GlobalTheory.TargetStatementBis.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementBis.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementBis.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementBis.target ..)

theorem isLattice_comap_subtype_ringOfIntegers {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.IsLattice K Λ) (W : Submodule K V) :
    Submodule.IsLattice K (Λ.comap (W.subtype.restrictScalars (𝓞 K))) := by
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (W.subtype.restrictScalars (𝓞 K)) :=
      W.injective_subtype
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    exact Submodule.FG.of_le hΛ.fg (Submodule.map_comap_le _ _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfSumSqEq
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem measurePreserving_of_sum_sq_eq : ∀ (k a b : ℕ), k = a + b → ∀ Q : (Fin k → ℝ) →ₗ[ℝ] (Fin a → ℝ) × (Fin b → ℝ), (∀ z, ∑ i, (Q z).1 i ^ 2 + ∑ i, (Q z).2 i ^ 2 = ∑ i, z i ^ 2) → MeasurePreserving Q volume volume := by
  intro k a b hk Q hQ
  let L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin a ⊕ Fin b) :=
    (WithLp.linearEquiv 2 ℝ (Fin a ⊕ Fin b → ℝ)).symm.toLinearMap ∘ₗ
      (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℝ ℝ).symm.toLinearMap ∘ₗ Q ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap
  have hL : ∀ z, ‖L z‖ = ‖z‖ := by
    intro z
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [Real.norm_eq_abs, sq_abs, Fintype.sum_sum_type]
    rw [← hQ z.ofLp]
    rfl
  let Li : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a ⊕ Fin b) := ⟨L, hL⟩
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin k))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin a ⊕ Fin b)) := by
    simp [hk]
  have h1 := (Li.toLinearIsometryEquiv hd).measurePreserving
  have h2 := PiLp.volume_preserving_toLp (Fin k)
  have h3 := PiLp.volume_preserving_ofLp (Fin a ⊕ Fin b)
  have h4 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)
  have h := h4.comp (h3.comp (h1.comp h2))
  exact h

end GlobalTheory.IwConst
end

