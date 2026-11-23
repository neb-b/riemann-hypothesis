module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits Topology Filter TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Points

namespace GlobalTheory.ProperPoints

section Ultrapower

variable {I F : Type} [NormedField F] (𝒰 : Ultrafilter I)

def bddRing (F : Type) [NormedField F] : ValuationSubring ((𝒰 : Filter I).Germ F) where
  carrier := {a | ∃ (M : ℝ) (f : I → F), a = (f : (𝒰 : Filter I).Germ F) ∧ ∀ᶠ i in (𝒰 : Filter I), ‖f i‖ ≤ M}
  mul_mem' := by
    rintro _ _ ⟨M, f, rfl, hf⟩ ⟨N, g, rfl, hg⟩
    refine ⟨M * N, f * g, rfl, ?_⟩
    filter_upwards [hf, hg] with i h1 h2
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  one_mem' := ⟨1, 1, rfl, Eventually.of_forall fun i => by simp⟩
  add_mem' := by
    rintro _ _ ⟨M, f, rfl, hf⟩ ⟨N, g, rfl, hg⟩
    refine ⟨M + N, f + g, rfl, ?_⟩
    filter_upwards [hf, hg] with i h1 h2
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  zero_mem' := ⟨0, 0, rfl, Eventually.of_forall fun i => by simp⟩
  neg_mem' := by
    rintro _ ⟨M, f, rfl, hf⟩
    refine ⟨M, -f, rfl, ?_⟩
    filter_upwards [hf] with i h1
    simpa using h1
  mem_or_inv_mem' := by
    intro a
    induction a using Germ.inductionOn with
    | h f =>
      by_cases h : ∀ᶠ i in (𝒰 : Filter I), ‖f i‖ ≤ 1
      · exact Or.inl ⟨1, f, rfl, h⟩
      · refine Or.inr ⟨1, f⁻¹, rfl, ?_⟩
        filter_upwards [Ultrafilter.eventually_not.2 h] with i hi
        rw [Pi.inv_apply, norm_inv]
        exact inv_le_one_of_one_le₀ (not_le.1 hi).le

def constBdd (F : Type) [NormedField F] : F →+* bddRing 𝒰 F where
  toFun a := ⟨((fun _ => a : I → F) : (𝒰 : Filter I).Germ F), ‖a‖, _, rfl, Eventually.of_forall fun _ => le_rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable [ProperSpace F]

theorem exists_tendsto (a : bddRing 𝒰 F) : ∃ c : F, (a : (𝒰 : Filter I).Germ F).Tendsto (𝓝 c) := by
  obtain ⟨_, M, f, rfl, hf⟩ := a
  obtain ⟨c, -, hc⟩ := (isCompact_closedBall (0 : F) M).ultrafilter_le_nhds (𝒰.map f) (by
    rw [le_principal_iff]
    exact hf.mono fun i hi => by simpa using hi)
  exact ⟨c, hc⟩

theorem tendsto_choose (a : bddRing 𝒰 F) (f : I → F) (hf : (a : (𝒰 : Filter I).Germ F) = f) :
    Tendsto f 𝒰 (𝓝 (exists_tendsto 𝒰 a).choose) := by
  have h := (exists_tendsto 𝒰 a).choose_spec
  generalize (exists_tendsto 𝒰 a).choose = c at h ⊢
  rwa [hf] at h

theorem choose_eq (a : bddRing 𝒰 F) (f : I → F) (hf : (a : (𝒰 : Filter I).Germ F) = f) {c : F}
    (hc : Tendsto f 𝒰 (𝓝 c)) : (exists_tendsto 𝒰 a).choose = c :=
  tendsto_nhds_unique (tendsto_choose 𝒰 a f hf) hc

def stdPart (F : Type) [NormedField F] [ProperSpace F] : bddRing 𝒰 F →+* F where
  toFun a := (exists_tendsto 𝒰 a).choose
  map_one' := choose_eq 𝒰 1 (fun _ => 1) rfl tendsto_const_nhds
  map_zero' := choose_eq 𝒰 0 (fun _ => 0) rfl tendsto_const_nhds
  map_mul' := by
    rintro a b
    obtain ⟨_, f, hf, -⟩ := a.2
    obtain ⟨_, g, hg, -⟩ := b.2
    exact choose_eq 𝒰 _ (f * g) (by rw [Germ.coe_mul, ← hf, ← hg]; rfl)
      ((tendsto_choose 𝒰 a f hf).mul (tendsto_choose 𝒰 b g hg))
  map_add' := by
    rintro a b
    obtain ⟨_, f, hf, -⟩ := a.2
    obtain ⟨_, g, hg, -⟩ := b.2
    exact choose_eq 𝒰 _ (f + g) (by rw [Germ.coe_add, ← hf, ← hg]; rfl)
      ((tendsto_choose 𝒰 a f hf).add (tendsto_choose 𝒰 b g hg))

theorem tendsto_stdPart (a : bddRing 𝒰 F) (f : I → F) (hf : (a : (𝒰 : Filter I).Germ F) = f) :
    Tendsto f 𝒰 (𝓝 (stdPart 𝒰 F a)) := tendsto_choose 𝒰 a f hf

theorem stdPart_constBdd (a : F) : stdPart 𝒰 F (constBdd 𝒰 F a) = a :=
  choose_eq 𝒰 _ (fun _ => a) rfl tendsto_const_nhds

end Ultrapower

theorem valR_mul_pow {C : Type} [CommRing C] {X : Scheme.{0}} {U V : X.Opens} (h : Γ(X, U))
    (hV : X.basicOpen h ≤ V) (f : Γ(X, V)) (n : ℕ) (a : Γ(X, U))
    (ha : (X.presheaf.map (homOfLE hV).op).hom f * algebraMap Γ(X, U) Γ(X, X.basicOpen h) h ^ n =
      algebraMap Γ(X, U) Γ(X, X.basicOpen h) a)
    (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ X.basicOpen h) : valR y V f * valR y U h ^ n = valR y U a := by
  have h1 := congrArg (valR y (X.basicOpen h)) ha
  rw [valR_mul y _ hy, valR_pow y _ hy, valR_res y hV hy] at h1
  have h2 : ∀ t : Γ(X, U), valR y (X.basicOpen h) (algebraMap Γ(X, U) Γ(X, X.basicOpen h) t) =
      valR y U t := fun t => valR_res y (X.basicOpen_le h) hy t
  rwa [h2, h2] at h1

section Limit

variable {I F : Type} [Field F] (𝒰 : Ultrafilter I) {X : Scheme.{0}} (e : I → (Sp F ⟶ X)) {U : X.Opens}

def germVal (hl : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ U) : Γ(X, U) →+* (𝒰 : Filter I).Germ F where
  toFun f := ((fun i => valR (e i) U f : I → F) : (𝒰 : Filter I).Germ F)
  map_one' := Germ.coe_eq.2 (hl.mono fun _ hi => valR_one _ U hi)
  map_mul' f g := Germ.coe_eq.2 (hl.mono fun _ hi => valR_mul _ U hi f g)
  map_zero' := Germ.coe_eq.2 (hl.mono fun _ hi => valR_zero _ U hi)
  map_add' f g := Germ.coe_eq.2 (hl.mono fun _ hi => valR_add _ U hi f g)

theorem exists_germPoint [CompactSpace X] : ∃ ξ : Sp ((𝒰 : Filter I).Germ F) ⟶ X, ∀ V : X.Opens, ⊤ ≤ ξ ⁻¹ᵁ V →
    (∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ V) ∧
      ∀ f : Γ(X, V), valR ξ V f = ((fun i => valR (e i) V f : I → F) : (𝒰 : Filter I).Germ F) := by
  obtain ⟨z, hz⟩ : ∃ z : X, Tendsto (fun i => e i (IsLocalRing.closedPoint F)) 𝒰 (𝓝 z) :=
    ⟨_, (𝒰.map fun i => e i (IsLocalRing.closedPoint F)).le_nhds_lim⟩
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := z) trivial
  have hl : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ U :=
    (hz.eventually (U.isOpen.mem_nhds hzU)).mono fun i hi => (le_preimage_iff _ _).2 hi
  let ξ : Sp ((𝒰 : Filter I).Germ F) ⟶ X := Spec.map (CommRingCat.ofHom (germVal 𝒰 e hl)) ≫ hU.fromSpec
  have hξ : ⊤ ≤ ξ ⁻¹ᵁ U := le_preimage_specMap_fromSpec hU _
  have hval : ∀ f, valR ξ U f = germVal 𝒰 e hl f := fun f => by
    rw [valR_eq ξ U hξ, valMap_specMap_fromSpec]
    rfl
  refine ⟨ξ, fun V hV => ?_⟩
  obtain ⟨h, hhV, hh⟩ := hU.exists_basicOpen_le (V := V) ⟨_, (le_preimage_iff ξ V).1 hV⟩
    ((le_preimage_iff ξ U).1 hξ)
  have hξh : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen h := (le_preimage_iff ξ _).2 hh
  have hne : germVal 𝒰 e hl h ≠ 0 := by
    rw [← hval]
    exact ((le_preimage_basicOpen_iff ξ hξ h).1 hξh).ne_zero
  have hl' : ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ e i ⁻¹ᵁ X.basicOpen h := by
    have h0 : ¬ ∀ᶠ i in (𝒰 : Filter I), valR (e i) U h = 0 := fun h0 => hne (Germ.coe_eq.2 h0)
    filter_upwards [hl, Ultrafilter.eventually_not.2 h0] with i h1 h2
      using (le_preimage_basicOpen_iff _ h1 h).2 (Ne.isUnit h2)
  refine ⟨hl'.mono fun i hi => le_preimage_mono _ hhV hi, fun f => ?_⟩
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h ((X.presheaf.map (homOfLE hhV).op).hom f)
  have h1 := valR_mul_pow h hhV f n a ha ξ hξh
  rw [hval, hval] at h1
  apply mul_right_cancel₀ (pow_ne_zero n hne)
  rw [h1, ← map_pow]
  refine Germ.coe_eq.2 ?_
  filter_upwards [hl, hl'] with i h2 h3
  have := valR_mul_pow h hhV f n a ha (e i) h3
  rw [← valR_pow _ _ h2] at this
  exact this.symm

end Limit

theorem compactSpace_pts {F : Type} [NormedField F] [ProperSpace F] {X : Scheme.{0}} (p : X ⟶ Sp F)
    [UniversallyClosed p] : CompactSpace (Pts p) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  refine ⟨isCompact_iff_ultrafilter_le_nhds.2 fun 𝒰 _ => ?_⟩
  obtain ⟨ξ, hξ⟩ := exists_germPoint 𝒰 (fun x : Pts p => x.1)
  have hE : ValuativeCriterion.Existence p :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed p) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) p).1
  have hw : ξ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap (bddRing 𝒰 F) ((𝒰 : Filter (Pts p)).Germ F))) ≫
      spMap (constBdd 𝒰 F) := by
    rw [← Spec.map_comp, ← Spec.map_preimage (ξ ≫ p)]
    congr 1
    ext a
    refine (valR_constFn p ξ ⊤ (le_preimage_top _) a).symm.trans ?_
    rw [(hξ ⊤ (le_preimage_top _)).2]
    exact Germ.coe_eq.2 (Eventually.of_forall fun x => valR_constFn_of_section p x.1 x.2 ⊤ (le_preimage_top _) a)
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Sp (bddRing 𝒰 F) ⟶ X,
      spMap (algebraMap (bddRing 𝒰 F) ((𝒰 : Filter (Pts p)).Germ F)) ≫ l = ξ ∧ l ≫ p = spMap (constBdd 𝒰 F) := by
    obtain ⟨⟨l, hl, hl'⟩⟩ := (hE
      { R := bddRing 𝒰 F, K := (𝒰 : Filter (Pts p)).Germ F, i₁ := ξ, i₂ := spMap (constBdd 𝒰 F),
        commSq := ⟨hw⟩ }).exists_lift
    exact ⟨l, hl, hl'⟩
  have hx : (spMap (stdPart 𝒰 F) ≫ l) ≫ p = 𝟙 _ := by
    rw [Category.assoc, hl₂, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact stdPart_constBdd 𝒰 a
  refine ⟨⟨_, hx⟩, trivial, ?_⟩
  obtain ⟨V, hV, hlV, -⟩ := exists_isAffineOpen_le (C := bddRing 𝒰 F) l (le_preimage_top _)
  have hξV : ⊤ ≤ ξ ⁻¹ᵁ V := hl₁ ▸ le_preimage_comp _ l hlV (le_preimage_top _)
  have H : Tendsto (fun x : Pts p => x.1) 𝒰 (𝓝 (spMap (stdPart 𝒰 F) ≫ l)) := by
    refine tendsto_of_isAffineOpen hV (le_preimage_comp _ l hlV (le_preimage_top _)) (hξ V hξV).1 fun f => ?_
    rw [valR_spMap_comp _ l V hlV]
    refine tendsto_stdPart 𝒰 _ _ ?_
    rw [← (hξ V hξV).2, ← hl₁, valR_spMap_comp _ l V hlV]
    rfl
  exact tendsto_id'.1 (tendsto_subtype_rng.2 H)

end GlobalTheory.ProperPoints
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology

namespace GlobalTheory.GardingVec

theorem contDiff_setIntegral_nat {X P E : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K) {a : X → E} (ha : Continuous a)
    (m : ℕ) : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Ψ : P × E → F),
      ContDiff ℝ ∞ Ψ → ContDiff ℝ m fun p => ∫ x in K, Ψ (p, a x) ∂μ := by
  first
  | exact @_root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral
  | exact _root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral
  | (apply _root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral ..)

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_list_prod {n : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (l : List (P → Matrix (Fin n) (Fin n) ℂ)) (h : ∀ f ∈ l, ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p => (l.map fun f => f p).prod := by
  induction l with
  | nil => simpa using contDiff_const
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h f (by simp)).mul (ih fun g hg => h g (by simp [hg]))

theorem contDiff_expProd {n k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
  have := contDiff_list_prod (List.ofFn fun i => fun t : Fin k → ℝ => NormedSpace.exp (t i • Xs i)) (by
    intro f hf
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    have h1 : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
      contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    exact h1.comp ((contDiff_apply ℝ (fun _ => ℝ) i).smul contDiff_const))
  simpa [List.map_ofFn, Function.comp_def] using this

theorem contDiff_conjTranspose {n : ℕ} : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ => xᴴ := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun x => xᴴ
      map_add' := fun x y => conjTranspose_add x y
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  exact (LinearMap.toContinuousLinearMap L).contDiff


open Formalism.MainNotions.S in
theorem exists_garding {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) :
    ∃ v : H, v ≠ 0 ∧ ∀ (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ), ContDiff ℝ ∞ x →
      (∀ t, x t ∈ UJset ε) → ContDiff ℝ ∞ fun t => σ (x t) v := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  set μ := Formalism.REAL.muG ε
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w := (hcont w).comp_continuous hu hmem
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := hmem 1
  have hnb : {g | ‖σ g w - w‖ < ‖w‖ / 2} ∈ 𝓝[UJset ε] (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := (hcont w 1 hone) (Metric.ball_mem_nhds _ (half_pos hwpos))
    simpa [h1, Set.preimage, dist_eq_norm] using h
  obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnb
  obtain ⟨φ, hφU, hφc, hφ, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hU
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  have hψ : Continuous fun g : Formalism.REAL.UJ ε => φ (umat g) := hφ.continuous.comp hu
  have hψc : HasCompactSupport fun g : Formalism.REAL.UJ ε => φ (umat g) := hφc.comp_isClosedEmbedding hemb
  have hint : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • σ (umat g) w) μ :=
    (hψ.smul hb).integrable_of_hasCompactSupport hψc.smul_right
  have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) μ := hψ.integrable_of_hasCompactSupport hψc
  have hpos : 0 < ∫ g : Formalism.REAL.UJ ε, φ (umat g) ∂μ :=
    hψ.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hψc (fun g => hφ0 _)
      (by show φ 1 ≠ 0; rw [hφ1]; exact one_ne_zero)
  refine ⟨∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂μ, ?_, ?_⟩
  · intro h0
    have e1 : ∫ g : Formalism.REAL.UJ ε, (φ (umat g) • σ (umat g) w - φ (umat g) • w) ∂μ
        = -((∫ g : Formalism.REAL.UJ ε, φ (umat g) ∂μ) • w) := by
      rw [integral_sub hint (hψi.smul_const w), h0, integral_smul_const, zero_sub]
    have e2 : ‖∫ g : Formalism.REAL.UJ ε, (φ (umat g) • σ (umat g) w - φ (umat g) • w) ∂μ‖
        ≤ ∫ g : Formalism.REAL.UJ ε, φ (umat g) * (‖w‖ / 2) ∂μ := by
      refine norm_integral_le_of_norm_le (hψi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ0 _)]
      by_cases hg : φ (umat g) = 0
      · simp [hg]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hUs ⟨hφU (subset_tsupport _ hg), hmem g⟩)) (hφ0 _)
    rw [e1, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le, integral_mul_const] at e2
    nlinarith [mul_pos hpos hwpos]
  · intro k x hx hxG
    let y : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun t => Formalism.REAL.Jm ε * (x t)ᴴ * Formalism.REAL.Jm ε
    have hy : ContDiff ℝ ∞ y := (contDiff_const.mul (contDiff_conjTranspose.comp hx)).mul contDiff_const
    have hyx : ∀ t, y t * x t = 1 := fun t => by
      have h : (x t)ᴴ * Formalism.REAL.Jm ε * x t = Formalism.REAL.Jm ε := hxG t
      calc y t * x t = Formalism.REAL.Jm ε * ((x t)ᴴ * Formalism.REAL.Jm ε * x t) := by simp only [y, Matrix.mul_assoc]
        _ = 1 := by rw [h, Formalism.REAL.Jm_mul_self]
    have hxy : ∀ t, x t * y t = 1 := fun t => mul_eq_one_comm.1 (hyx t)
    have hform : ∀ t, σ (x t) (∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂μ)
        = ∫ g : Formalism.REAL.UJ ε, φ (y t * umat g) • σ (umat g) w ∂μ := by
      intro t
      obtain ⟨z, hz⟩ : x t ∈ Set.range (fun g : Formalism.REAL.UJ ε => umat g) := by
        rw [show Set.range (fun g : Formalism.REAL.UJ ε => umat g) = _ from hrange]; exact hxG t
      have hz' : umat z = x t := hz
      rw [← ContinuousLinearMap.integral_comp_comm _ hint,
        ← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => φ (y t * umat g) • σ (umat g) w) z]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have e : umat (z * g) = x t * umat g := by rw [← hz']; rfl
      simp only [e]
      rw [← Matrix.mul_assoc, hyx, Matrix.one_mul, hmul _ (hxG t) _ (hmem g),
        ContinuousLinearMap.map_smul_of_tower]
      rfl
    simp only [hform]
    refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
    have hC : IsCompact (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1) (tsupport φ)) :=
      ((isCompact_closedBall t₀ 1).image hx.continuous).mul hφc
    have hK := hemb.isCompact_preimage hC
    have hs : ContDiff ℝ ∞ fun t => ∫ g in (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹'
        (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1) (tsupport φ)),
        φ (y t * umat g) • σ (umat g) w ∂μ :=
      contDiff_infty.2 fun m => contDiff_setIntegral_nat μ hK (hu.prodMk hb) m
        (fun z : (Fin k → ℝ) × (Matrix (Fin n) (Fin n) ℂ × H) => φ (y z.1 * z.2.1) • z.2.2)
        ((hφ.comp ((hy.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd))).smul
          (contDiff_snd.comp contDiff_snd))
    refine hs.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Metric.closedBall_mem_nhds t₀ one_pos] with t ht
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    by_contra hne
    refine hg ⟨x t, ⟨t, ht, rfl⟩, y t * umat g, subset_tsupport _ fun h => hne (by rw [h, zero_smul]), ?_⟩
    show x t * (y t * umat g) = umat g
    rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]

theorem conj_mem {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ} (hg' : gᴴ * G * g = G) :
    P * g * P⁻¹ ∈ Formalism.MainNotions.S.UJset ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [h, hg', ← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

theorem exp_mem {n : ℕ} {G X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) (hX : Xᴴ * G + G * X = 0) (t : ℝ) :
    (NormedSpace.exp (t • X))ᴴ * G * NormedSpace.exp (t • X) = G := by
  have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have h1 : (t • X)ᴴ = G * (-(t • X)) * G⁻¹ := by
    have h2 : Xᴴ = G * (-X) * G⁻¹ := by
      rw [Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
        Matrix.mul_one]
    rw [conjTranspose_smul, h2]
    simp
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hG, Matrix.exp_neg]
  have hu : IsUnit (NormedSpace.exp (t • X)).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  rw [Matrix.mul_assoc (G * _), Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem list_prod_mem {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (l : List (Matrix (Fin n) (Fin n) ℂ))
    (h : ∀ g ∈ l, gᴴ * G * g = G) : l.prodᴴ * G * l.prod = G := by
  induction l with
  | nil => simp
  | cons g l ih =>
    have h1 := h g (by simp)
    have h2 := ih fun g hg => h g (by simp [hg])
    rw [List.prod_cons, conjTranspose_mul]
    calc l.prodᴴ * gᴴ * G * (g * l.prod) = l.prodᴴ * (gᴴ * G * g) * l.prod := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, h2]

theorem exists_smoothVec {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) :
    ∃ v : H, v ≠ 0 ∧ Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v := by
  obtain ⟨v, hv, hs⟩ := exists_garding hσ
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  refine ⟨v, hv, fun k Xs hX => hs k _ ((contDiff_const.mul (contDiff_expProd Xs)).mul contDiff_const) fun t => ?_⟩
  refine conj_mem hP h (list_prod_mem _ fun g hg => ?_)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
  exact exp_mem hG (hX i) _

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sm_ne_bot (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) :
    M.sm τ ≠ ⊥ := by
  obtain ⟨h1, h2, h3, -⟩ := M.ds τ
  obtain ⟨v, hv, hs⟩ := exists_smoothVec h3 (M.fr_unit τ) (M.fr_gram τ)
  exact (Submodule.ne_bot_iff _).2 ⟨v, Submodule.subset_span hs, hv⟩

end GlobalTheory.GardingVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarFund
section
noncomputable section

namespace GlobalTheory.Mem.SJ.HaarMove

open MeasureTheory
open scoped Pointwise

theorem exists_haar_fund {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [MeasurableSpace G'] [BorelSpace G']
    (μ' : Measure G') [μ'.IsHaarMeasure] (ι : G ≃ₜ* G') (Γ : Subgroup G) (Γ' : Set G')
    (hΓ : ∀ g, g ∈ Γ ↔ ι g ∈ Γ') (F' : Set G') (hm : MeasurableSet F') (hc : ∀ y, ∃ γ ∈ Γ', γ * y ∈ F')
    (hd : ∀ γ ∈ Γ', γ ≠ 1 → μ' ((fun y => γ * y) '' F' ∩ F') = 0) (t : G) :
    ∃ (μ : Measure G) (F : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ F μ ∧
      ∀ f : G → ℂ, ∫ g in F, f g ∂μ = ∫ x in F', f (ι.symm x * t) ∂μ' := by
  let e : G' ≃ᵐ G := (ι.symm.toHomeomorph.trans (Homeomorph.mulRight t)).toMeasurableEquiv
  have he : ∀ x, e x = ι.symm x * t := fun _ => rfl
  have hes : ∀ g, e.symm g = ι (g * t⁻¹) := fun g => by
    rw [MeasurableEquiv.symm_apply_eq, he]; simp
  have hH : (μ'.map e).IsHaarMeasure := by
    have h1 : (μ'.map ι.symm).IsHaarMeasure := ι.symm.isHaarMeasure_map μ'
    have h2 : μ'.map e = (μ'.map ι.symm).map (· * t) := by
      exact (Measure.map_map (measurable_mul_const t) (map_continuous ι.symm).measurable).symm
    rw [h2]; infer_instance
  refine ⟨μ'.map e, e.symm ⁻¹' F', hH, ?_, fun f => ?_⟩
  · refine IsFundamentalDomain.mk'' (e.symm.measurable hm).nullMeasurableSet (ae_of_all _ fun g => ?_)
      (fun γ hγ => ?_) (fun γ => (measurePreserving_mul_left (μ'.map e) (γ : G)).quasiMeasurePreserving)
    · obtain ⟨γ, hγ, h⟩ := hc (e.symm g)
      refine ⟨⟨ι.symm γ, (hΓ _).2 (by simpa using hγ)⟩, ?_⟩
      show e.symm (ι.symm γ * g) ∈ F'
      rw [hes] at h ⊢
      simpa [mul_assoc] using h
    · have h0 := hd (ι γ) ((hΓ _).1 γ.2) (fun h => hγ (Subtype.ext (ι.injective (by simpa using h))))
      rw [AEDisjoint, MeasurableEquiv.map_apply]
      refine measure_mono_null ?_ h0
      rintro x ⟨⟨g, hg, hx⟩, h2⟩
      refine ⟨⟨e.symm g, hg, ?_⟩, by simpa using h2⟩
      have hx' : (γ : G) * g = ι.symm x * t := hx
      show ι γ * e.symm g = x
      rw [hes, ← map_mul, ← mul_assoc, hx']; simp
  · rw [setIntegral_map_equiv]
    simp only [he]
    congr 2
    ext x; simp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult
open scoped InnerProductSpace TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem schur_of_bridge {D : D7} {V : HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel V S)
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D V))
    (χ : GA D V → ℂ) (hS : ∀ μ 𝓕, SchurMult θ M J χ μ 𝓕) (hθ : IsInfFam θ)
    (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (hf : I.IsFundDom (I.muA μf) fund) (ι : GA D V ≃ₜ* I.GA) (hι : ∀ g, g ∈ GQ V ↔ ι g ∈ I.GFset) (t : GA D V)
    (T : MMap M) (hT : T ∈ Mult θ M J χ) (T' : MMap M) (hT' : T' ∈ Mult θ M J χ) :
    ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v (ι.symm x * t)) * T' v' (ι.symm x * t) ∂((I.muA μf).restrict fund) =
      c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : (I.muA μf).IsHaarMeasure := by
    unfold AutInst.muA Formalism.REAL.muG; infer_instance
  obtain ⟨μ, F, hμ, hF, hint⟩ := exists_haar_fund (I.muA μf) ι (GQ V) I.GFset hι fund hf.1 hf.2.1 hf.2.2 t
  obtain ⟨c, hc⟩ := hS μ F hθ hμ hF T hT T' hT'
  exact ⟨c, fun v v' => (hint fun g => star (T v g) * T' v' g).symm.trans (hc v v').2⟩

end GlobalTheory.Mem.SJ.HaarMove

end
end

