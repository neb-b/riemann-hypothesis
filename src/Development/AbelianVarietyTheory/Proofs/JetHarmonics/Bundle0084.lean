module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LetterLiftOfParts
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersPassDiGIBoundedFactors
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0081
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPointOfIffThick
section
noncomputable section

namespace GlobalTheory.TorusModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {T T' : Over (Spec (CommRingCat.of R))}

variable {U} in
theorem hasCoords_pull {e : ℕ} {k : T' ⟶ T} {g : GtPt D.toPre T} {g' : GtPt D.toPre T'}
    (h : GtPt.IsPull k.left g g') {Z : Scheme.{0}} {r : Z ⟶ T'.left} {y : Z ⟶ (thickObj R I e G).left} :
    HasCoords U e g (r ≫ k.left) y ↔ HasCoords U e g' r y := by
  rw [hasCoords_iff, hasCoords_iff, h.1, Category.assoc]
  refine and_congr Iff.rfl (forall_congr' fun χ => forall_congr' fun z => forall_congr' fun J =>
    forall_congr' fun hJ => ?_)
  rw [(val_corr hJ (h.2 χ) r).trans (val_pull hJ _ _ _)]

variable {U} in
theorem eq_of_hasCoords {e : ℕ} {g g' : GtPt D.toPre T} {y : T.left ⟶ (thickObj R I e G).left}
    (h : HasCoords U e g (𝟙 _) y) (h' : HasCoords U e g' (𝟙 _) y) : g = g' := by
  rw [hasCoords_iff, Category.id_comp] at h h'
  exact pt_ext (Over.OverMorphism.ext (h.1.symm.trans h'.1)) fun χ z J hJ => (h.2 χ z J hJ).symm.trans (h'.2 χ z J hJ)

theorem isPointOf_iff_thick (g : GtPt D.toPre T) (x : T ⟶ G) :
    IsPointOf U g x ↔ ∀ e, HasCoords U e g (thickι I e T) (thickHom I e x) := by
  refine ⟨fun h e => h e _ _ _ (thickHom_ι I e x), fun h e Z r y hy => ?_⟩
  have w : r ≫ T.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ thickι I e T = r := ⟨pullback.lift r _ w, pullback.lift_fst _ _ _⟩
  obtain rfl : y = l ≫ thickHom I e x := by
    rw [← cancel_mono (thickι I e G), Category.assoc, thickHom_ι]
    exact hy.trans (Category.assoc _ _ _)
  exact (h e).comp l

theorem existsUnique_point (hT : IsAdicColimit I T) (g : GtPt D.toPre T) : ∃! x : T ⟶ G, IsPointOf U g x := by
  choose y hy using fun e =>
    exists_hasCoords U e g (thickι I e T) (thickObj R I e T).hom pullback.condition.symm
  refine existsUnique_of_exists_of_unique ?_ fun x x' h h' => Over.OverMorphism.ext (hT.hom_ext fun e =>
    (h.comp_fstG_eq (hy e)).symm.trans (h'.comp_fstG_eq (hy e)))
  obtain ⟨x, hx, -⟩ := hT G.left (fun e => y e ≫ thickι I e G) fun e => by
    have h₁ := (hy (e + 1)).comp (thickMap R I e T)
    rw [thickMap_ι] at h₁
    rw [← Category.assoc, h₁.unique (hy e).succ, Category.assoc, thickMap_ι]
  have hw : x ≫ G.hom = T.hom := hT.hom_ext fun e => by
    have h₁ : thickι I e G ≫ G.hom = (U.gt e).pG.left ≫ D.toPre.P.A.hom :=
      (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
    rw [reassoc_of% hx e, h₁, reassoc_of% (hy e).1, Over.w]
  refine ⟨Over.homMk x hw, (isPointOf_iff_thick U g _).2 fun e => ?_⟩
  have : thickHom I e (Over.homMk x hw : T ⟶ G) = y e := by
    rw [← cancel_mono (thickι I e G), thickHom_ι]
    exact hx e
  rw [this]
  exact hy e

variable {H : Over (Spec (CommRingCat.of R))} [GrpObj H] {Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T}

theorem existsUnique_lift (hΦ : Represents Φ) (hT : IsAdicColimit I T) (x : T ⟶ G) :
    ∃! w : T ⟶ H, IsPointOf U (Φ T w) x := by
  have pl : ∀ (e : ℕ) (w : T ⟶ H), HasCoords U e (Φ T w) (thickι I e T) (thickHom I e x) ↔
      HasCoords U e (Φ _ (fstG I e T ≫ w)) (𝟙 _) (thickHom I e x) := fun e w => by
    rw [← hasCoords_pull (hΦ.1 _ _ (fstG I e T) w), Category.id_comp]; rfl
  refine existsUnique_of_exists_of_unique ?_ fun w w' h h' => Over.OverMorphism.ext (hT.hom_ext fun e =>
    congrArg (·.left) ((Φ _).injective (eq_of_hasCoords ((pl e w).1 ((isPointOf_iff_thick U _ x).1 h e))
      ((pl e w').1 ((isPointOf_iff_thick U _ x).1 h' e)))))
  have ex : ∀ e, ∃ w : (Over.map (thick R I e)).obj (thickObj R I e T) ⟶ H,
      HasCoords U e (Φ _ w) (𝟙 _) (thickHom I e x) := fun e => by
    obtain ⟨ξ, hξ⟩ := TorusCoord.exists_isPointOf (U.gt e) (T := (Over.map (thick R I e)).obj (thickObj R I e T))
      (thickHom I e x) (by rw [← Category.assoc, Over.w]; rfl)
    refine ⟨(Φ _).symm ξ, ?_⟩
    rw [Equiv.apply_symm_apply, hasCoords_iff]
    refine ⟨hξ.1.symm.trans (Category.id_comp _).symm, fun χ z J hJ => ?_⟩
    have := (val_corr hJ (hξ.2 χ) (𝟙 _)).trans (val_pull hJ _ _ _)
    rw [Category.id_comp] at this
    exact this.symm
  choose w hw using ex
  obtain ⟨v, hv, -⟩ := hT H.left (fun e => (w e).left) fun e => by
    let m : (Over.map (thick R I e)).obj (thickObj R I e T) ⟶
        (Over.map (thick R I (e + 1))).obj (thickObj R I (e + 1) T) := Over.homMk (thickMap R I e T)
      (((congrArg (thickMap R I e T ≫ ·) (Over.w (fstG I (e + 1) T)).symm).trans
        (thickMap_ι_assoc I e T T.hom)).trans (Over.w (fstG I e T)))
    have h₁ := (hw (e + 1)).comp (thickMap R I e T)
    rw [thickMap_thickHom, Category.comp_id, ← Category.id_comp (thickMap R I e T)] at h₁
    have h₂ := (hasCoords_pull (hΦ.1 _ _ m (w (e + 1)))).1 h₁
    exact congrArg (·.left) ((Φ _).injective (eq_of_hasCoords h₂ (hw e).succ))
  have hv' : v ≫ H.hom = T.hom := hT.hom_ext fun e => by
    rw [reassoc_of% hv e, Over.w]
    exact (Over.w (fstG I e T)).symm
  refine ⟨Over.homMk v hv', (isPointOf_iff_thick U _ x).2 fun e => (pl e _).2 ?_⟩
  have : fstG I e T ≫ (Over.homMk v hv' : T ⟶ H) = w e := Over.OverMorphism.ext (hv e)
  rw [this]
  exact hw e

theorem exists_mulEquiv (hG : GlobalFnsSt) (hΦ : Represents Φ) :
    ∃ J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G)),
      ∀ T hT w x, J T hT w = x ↔ IsPointOf U (Φ T w) x := by
  choose j hj hu using fun T (hT : IsAdicColimit I T) (w : T ⟶ H) => existsUnique_point U hT (Φ T w)
  have bij : ∀ T hT, Function.Bijective (j T hT) := fun T hT => (Function.bijective_iff_existsUnique _).2 fun x =>
    (existsUnique_congr fun w => ⟨fun h => (hu T hT w x h).symm, fun h => h ▸ hj T hT w⟩).1
      (existsUnique_lift U hΦ hT x)
  exact ⟨fun T hT => MulEquiv.mk' (Equiv.ofBijective _ (bij T hT)) fun w w' =>
      (hu T hT _ _ ((hj T hT w).mul hG (hj T hT w') (hΦ.2 T w w'))).symm,
    fun T hT w x => ⟨fun h => h ▸ hj T hT w, fun h => (hu T hT w x h).symm⟩⟩

end GlobalTheory.TorusModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsometricBesselSideBound
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem eLpNorm_two_of_lintegral_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : α → E) (c : ℝ) (hc : 0 ≤ c) (hf : AEStronglyMeasurable f μ) (h : ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ = ENNReal.ofReal (c ^ 2)) :
    eLpNorm f 2 μ = ENNReal.ofReal c := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hf]
  have h2 : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ = ENNReal.ofReal c ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hc (by norm_num), Real.rpow_two, ← h]
    refine lintegral_congr fun x => ?_
    simp [enorm_eq_nnnorm]
  rw [h2, ← ENNReal.rpow_mul]
  norm_num

theorem integral_inner_of_isometric {α E F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (S : Submodule ℂ E) (Φ : E → α → F)
    (hm : ∀ w ∈ S, MemLp (Φ w) 2 μ) (hn : ∀ w ∈ S, eLpNorm (Φ w) 2 μ = ENNReal.ofReal ‖w‖)
    (hadd : ∀ v ∈ S, ∀ w ∈ S, Φ (v + w) =ᵐ[μ] Φ v + Φ w)
    (hsmul : ∀ (c : ℂ), ∀ v ∈ S, Φ (c • v) =ᵐ[μ] c • Φ v) :
    ∀ w ∈ S, ∀ w' ∈ S, ∫ x, ⟪Φ w' x, Φ w x⟫_ℂ ∂μ = ⟪w', w⟫_ℂ := by
  let L : S →ₗᵢ[ℂ] Lp F 2 μ :=
    { toFun := fun v => (hm v v.2).toLp (Φ v)
      map_add' := fun v w => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (hadd v v.2 w w.2)
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (hsmul c v v.2)
      norm_map' := fun v => by
        change ‖(hm v v.2).toLp (Φ v)‖ = _
        rw [Lp.norm_toLp, hn v v.2, ENNReal.toReal_ofReal (norm_nonneg _)]
        rfl }
  intro w hw w' hw'
  have h := L.inner_map_map ⟨w', hw'⟩ ⟨w, hw⟩
  rw [L2.inner_def] at h
  refine Eq.trans ?_ h
  refine integral_congr_ae ?_
  filter_upwards [(hm w hw).coeFn_toLp, (hm w' hw').coeFn_toLp] with x h1 h2
  change _ = ⟪((hm w' hw').toLp (Φ w')) x, ((hm w hw).toLp (Φ w)) x⟫_ℂ
  rw [h1, h2]

theorem isoBessel_polarised : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → (∀ w ∈ R.sm, MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq) ∧ ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∫ x, ⟪Bm (R.σ (Matrix.of x) w'), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = ⟪w', w⟫_ℂ := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq Bm hDS hS hB
  obtain ⟨hae, -, -, hmeas⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hDS hS
  obtain ⟨-, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hDS
  have hn : ∀ w ∈ R.sm, eLpNorm (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq =
      ENNReal.ofReal ‖w‖ := fun w hw =>
    eLpNorm_two_of_lintegral_sq _ _ (norm_nonneg _) (hmeas Bm hB.1 w hw) (hB.2 w hw)
  have hm : ∀ w ∈ R.sm, MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq := fun w hw =>
    by rw [memLp_iff, hn w hw]; exact ENNReal.ofReal_lt_top
  refine ⟨hm, ?_⟩
  refine integral_inner_of_isometric R.smSub
    (fun w (x : Formalism.QuantumDeterminants.Mt k r) => Bm (R.σ (Matrix.of x) w)) hm hn ?_ ?_
  · intro v hv w hw
    filter_upwards [hae] with x hx
    simp only [Pi.add_apply, map_add (f := _)]
    exact hB.1.1 _ (hsm _ hx v hv) _ (hsm _ hx w hw)
  · intro c v hv
    filter_upwards [hae] with x hx
    simp only [Pi.smul_apply, map_smul]
    exact hB.1.2.1 c _ (hsm _ hx v hv)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LetterColMemNormalFormProductSpan
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.LetterEntries

open Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.TLA

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]


omit [StarModule ℂ A] in
theorem gen_mem (d : Q.NFData P A) {T : Set A} {b X : A} (hb : b ∈ bmon d) (hX : X ∈ T) :
    b * d.L.Di * X ∈ nfSpan d T 1 0 1 :=
  Submodule.subset_span ⟨b, hb, [X], rfl, by simpa using hX, by simp⟩


omit [StarModule ℂ A] in
theorem bounded_induction (d : Q.NFData P A) (N : Submodule ℂ A) (hN : ∀ b ∈ bmon d, b ∈ N) {E : A}
    (hE : E ∈ nfSpan d ∅ 0 0 0) : E ∈ N := by
  refine (Submodule.span_le.mpr ?_ : nfSpan d ∅ 0 0 0 ≤ N) hE
  rintro x ⟨b, hb, H, hH, -, rfl⟩
  rw [List.length_eq_zero_iff] at hH
  subst hH
  simpa using hN b hb

omit [StarModule ℂ A] in
theorem bounded_mul_mem (d : Q.NFData P A) {T : Set A} {E b X : A} (hE : E ∈ nfSpan d ∅ 0 0 0) (hb : b ∈ bmon d)
    (hX : X ∈ T) : E * (b * d.L.Di * X) ∈ nfSpan d T 1 0 1 := by
  refine bounded_induction d ((nfSpan d T 1 0 1).comap (LinearMap.mulRight ℂ (b * d.L.Di * X))) ?_ hE
  intro c hc
  have := gen_mem d (mul_mem hc hb) hX
  simpa [mul_assoc] using this

omit [StarModule ℂ A] in
theorem bounded_comm (d : Q.NFData P A) {E f : A} (hE : E ∈ nfSpan d ∅ 0 0 0) (hf : ∀ b ∈ bmon d, Commute b f) :
    f * E = E * f := by
  have := bounded_induction d (LinearMap.ker (LinearMap.mulLeft ℂ f - LinearMap.mulRight ℂ f))
    (fun b hb => by simp [(hf b hb).eq]) hE
  simpa [sub_eq_zero] using this

variable {S : Type} [Fintype S] [DecidableEq S]

omit [StarModule ℂ A] [StarRing A] in
theorem io_mem {N : Submodule ℂ A} {a : A} (ha : a ∈ N) (e e' : Ix S) : (io a : SlopeTestRemainingChoices S A) e e' ∈ N := by
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact ha
  · exact N.zero_mem

omit [StarModule ℂ A] [StarRing A] in
theorem col_mem {N : Submodule ℂ A} {s X k V W : A} {E : SlopeTestRemainingChoices S A} (h1 : s * (X * V + W) ∈ N)
    (h2 : ∀ e e', s * k * E e e' * V ∈ N) (e e' : Ix S) :
    (io s * ((io X + io k * E) * io V + io W) : SlopeTestRemainingChoices S A) e e' ∈ N := by
  have key : io s * ((io X + io k * E) * io V + io W) =
      (io (s * (X * V + W)) : SlopeTestRemainingChoices S A) + io (s * k) * E * io V := by
    simp only [io, map_mul, map_add (f := _)]; noncomm_ring
  rw [key, Matrix.add_apply]
  refine N.add_mem (io_mem h1 e e') ?_
  have : (io (s * k) * E * io V : SlopeTestRemainingChoices S A) e e' = s * k * E e e' * V := by
    simp [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [this]
  exact h2 e e'

theorem letterCol_mem : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s →
    ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (l : Letter ℂ S) (w : List (Letter ℂ S)), admitted st (l :: w) →
    ∀ i e e', TL.letterCol L st l w i e e' ∈ nfSpan d (hats d.L) 1 0 1 := by
  intro P A _ _ _ _ d hd0 L st s hT S _ _ l w hA i e e'
  obtain ⟨hnd, hre, hpt, hpw⟩ := hA
  have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
    List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
  have hpw' := List.pairwise_cons.mp hpw
  have hAw : admitted st w :=
    ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
  obtain ⟨p0, p1, pm1, -, -⟩ := hpt l (by simp)
  have hd := hpw'.1
  have m0 : l.pt ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p0 (fun l' hl' =>
    ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
  have m1 : l.pt + 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p1 (fun l' hl' =>
    ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
  have mm1 : l.pt - 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ pm1 (fun l' hl' =>
    ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
  have hr : star l.pt = l.pt := hre l (by simp)
  obtain ⟨-, hb, -⟩ := _root_.GlobalTheory.HatNF.Den.hat_den P A d hd0
  obtain ⟨ep, epb, ec, eci, ecb, ecbi, eζ, eζi, eζb, eζbi, eG, eGi, -⟩ := hT.2.1
  have eT : L.Tprod l.pt = d.L.Tprod l.pt := by
    unfold LevelData.Tprod LevelData.Tl; rw [ep, ec, eci]
  have eTv : L.Tvprod l.pt = d.L.Tvprod l.pt := by
    unfold LevelData.Tvprod LevelData.Tvl; rw [epb, ecb, ecbi]
  have eA : L.Ar l.pt = d.L.Ar l.pt := by unfold LevelData.Ar; rw [eT]
  have eB : L.Br l.pt = d.L.Br l.pt := by unfold LevelData.Br; rw [eT]
  have eAv : L.Avr l.pt = d.L.Avr l.pt := by unfold LevelData.Avr; rw [eTv]
  have eBv : L.Bvr l.pt = d.L.Bvr l.pt := by unfold LevelData.Bvr; rw [eTv]
  have hβ : d.L.D * d.L.Dbi ∈ bmon d := Submonoid.subset_closure (by simp [bset])
  have i1 : 1 * d.L.Di * d.L.Dr = d.L.ζi := by
    rw [one_mul, LevelData.Di, mul_assoc, Dri_Dr, mul_one]
  have i2 : d.L.D * d.L.Dbi * d.L.Di * d.L.Drb = d.L.ζbi := by
    have : d.L.Di * d.L.D = 1 := by
      rw [LevelData.D, ← mul_assoc, ← one_mul d.L.Di, i1, d.L.ζi_ζ]
    rw [(hb _ hβ).2.1.eq, ← mul_assoc, this, one_mul, LevelData.Dbi, mul_assoc, Drbi_Drb, mul_one]
  have j1 : d.L.ζi * d.L.Ar l.pt = 1 * d.L.Di * d.L.Ahat l.pt := by
    rw [LevelData.Ahat, ← mul_assoc, i1]
  have j2 : d.L.ζbi * d.L.Avr l.pt = d.L.D * d.L.Dbi * d.L.Di * d.L.Ahatv l.pt := by
    rw [LevelData.Ahatv, ← mul_assoc, i2]
  have hA1 : d.L.Ahat l.pt ∈ hats d.L := by simp [hats]
  have hA2 : d.L.Ahatv l.pt ∈ hats d.L := by simp [hats]
  have hR1 : d.L.R0 l.pt ∈ hats d.L := by simp [hats]
  have hR2 : d.L.R0v l.pt ∈ hats d.L := by simp [hats]
  unfold TL.letterCol
  by_cases hp : l.plus
  · simp only [hp, if_true]
    fin_cases i
    · refine io_mem (a := TL.aP L l.pt) ?_ e e'
      rw [TL.aP, eζi, eA, j1]
      exact gen_mem d (one_mem _) hA1
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      obtain ⟨E, hE, hl⟩ := _root_.GlobalTheory.HatNF.WordL.word_l_shape P A d hd0 L st s hT S w hAw l.pt m0 m1
      rw [hl, eζbi, eG, eA, eB, kapL]
      refine col_mem ?_ (fun f f' => ?_) e e'
      · have := gen_mem d hβ hR1
        rwa [LevelData.R0, ← mul_assoc, ← mul_assoc, i2] at this
      · rw [ColumnLift.s1p, bounded_comm d (hE f f') (fun b h => (hb b h).1 _ (by simp [LevelData.fns])), mul_assoc, j1]
        exact bounded_mul_mem d (hE f f') (one_mem _) hA1
  · simp only [hp, Bool.false_eq_true, if_false]
    fin_cases i
    · refine io_mem (a := TL.aM L l.pt) ?_ e e'
      rw [TL.aM, eζbi, eAv, j2]
      exact gen_mem d hβ hA2
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      obtain ⟨E, hE, hl⟩ := GlobalTheory.T.word_m_decomposition_self_adjoint P A d hd0 L st s hT S w hAw l.pt m0 hr mm1
      rw [hl, eζi, eG, eAv, eBv]
      refine col_mem ?_ (fun f f' => ?_) e e'
      · have := gen_mem d (one_mem _) hR2
        rwa [LevelData.R0v, ← mul_assoc, ← mul_assoc, i1] at this
      · rw [ColumnLift.s1m, bounded_comm d (hE f f') (fun b h => (hb b h).1 _ (by simp [LevelData.fns])), mul_assoc, j2]
        exact bounded_mul_mem d (hE f f') hβ hA2

end GlobalTheory.HatNF.LetterEntries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqContractLe
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.ContractLinear

open Formalism.FourierDecayAlt.P

theorem norm_sq_contract_le {V V₂ : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] {k : ℕ} (a : Fin k → (V₂ →L[ℂ] V))
    (ha : ∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) (l : Fin k → ℂ) :
    ‖∑ c, l c • a c‖ ^ 2 ≤ ∑ c, ‖l c‖ ^ 2 := by
  have h0 : 0 ≤ ∑ c, ‖l c‖ ^ 2 := Finset.sum_nonneg fun c _ => by positivity
  have h1 : ‖∑ c, l c • a c‖ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
    have h2 : ‖(∑ c, l c • a c) y‖ ≤ ∑ c, ‖l c‖ * ‖a c y‖ := by
      rw [ContinuousLinearMap.sum_apply]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [ContinuousLinearMap.smul_apply, norm_smul]
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => ‖l c‖) (fun c => ‖a c y‖)
    rw [ha y] at h3
    refine h2.trans (le_of_sq_le_sq ?_ (by positivity))
    rw [mul_pow, Real.sq_sqrt h0]
    exact h3
  calc ‖∑ c, l c • a c‖ ^ 2 ≤ (Real.sqrt (∑ c, ‖l c‖ ^ 2)) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt h0

theorem wigMap_contract : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (a : Fin k → (V₂ →L[ℂ] V)), inWb k r z → 0 < Tz k r z → IsFrameOf k r [z] B → (∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) → (∀ h ∈ UWset k r z, ∀ y c, a c (π₂ h y) = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (a d y)) → GlobalTheory.WigSh.WigMap k r z π₂ π 1 (fun ω => ∑ c, herm (Hpk k r) ω (B c) • a c) ∧ ∀ c₀, (∑ c, herm (Hpk k r) (B c₀) (B c) • a c) = a c₀ := by
  intro V _ _ _ k r z π B V₂ _ _ _ π₂ a hz hT hB ha heq
  obtain ⟨hexp, hU⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB
  refine ⟨⟨⟨k, fun c => ∑ j, MvPolynomial.C ((star (B c) ᵥ* Hpk k r) j) * MvPolynomial.X (Sum.inl j), a,
    fun c => ?_, fun ω => ?_⟩, fun h hh ω => ?_, fun t ω => ?_, fun ω hω hωz => ?_⟩, fun c₀ => ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inl]
    rw [herm, Matrix.dotProduct_mulVec]
    rfl
  · obtain ⟨hW, hpres, -⟩ := hU h hh
    ext y
    have key : ∀ d, herm (Hpk k r) ω (B d) =
        ∑ c, star (herm (Hpk k r) (h *ᵥ B d) (B c)) * herm (Hpk k r) (h *ᵥ ω) (B c) := by
      intro d
      obtain ⟨h1, h2⟩ := hW (B d) (hB.1 d) (hB.2.2 d z (by simp))
      rw [← HermitianFormSums.herm_rsum, ← hexp _ h1 h2, hpres]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      heq h hh, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [key d, Finset.sum_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
  · simp only [Qx8.herm_smul_left', pow_one, Finset.smul_sum, smul_smul]
  · refine (norm_sq_contract_le a ha _).trans (le_of_eq ?_)
    have h1 := HermitianFormSums.herm_comb hB (fun c => herm (Hpk k r) ω (B c)) (fun c => herm (Hpk k r) ω (B c))
    rw [← hexp ω hω hωz] at h1
    rw [pow_one, h1, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  · simp [hB.2.1]

end GlobalTheory.ContractLinear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumDeterminantEigenvalue
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliSmooth

lemma entry_conj {n : ℕ} (P P' : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (P * Matrix.single a b (1 : ℂ) * P') c d = P c a * P' b d := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hx, mul_zero]
  · simp

theorem qdet_smooth : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → ∀ (Y : ℂ) (w : R.smSub), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w := by
  intro hyp k r ε mu R hR Q E hQ hE Y w
  have hK : PI.KFinSmooth := hyp.1.2.2.1
  have hC := hyp.2.2.1
  obtain ⟨hmu, Q0, hQ0, hDS⟩ := id hR
  have hU0 : IsUnit Q0 := hQ0.1.1
  obtain ⟨E0, hE0, hgl⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε mu R hR Q0 hU0
  obtain ⟨hsm, hd⟩ := _root_.GlobalTheory.CayleyTransport.smooth_and_dsigC_transport k r ε R Q0 hQ0
  obtain ⟨-, hexp, -⟩ := GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q0 E0 hU0 hE0
  have hdQ : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have hdQ0 : IsUnit Q0.det := (Matrix.isUnit_iff_isUnit_det Q0).1 hU0
  have hEE : E = Formalism.FourierDecayAlt.Q.Econj E0 (Q0 * Q⁻¹) (Q * Q0⁻¹) := by
    funext a b
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [hE a b v, hexp]
    have h1 : Q0 * (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * Q0⁻¹ =
        (Q0 * Q⁻¹) * Matrix.single a b (1 : ℂ) * (Q * Q0⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [h1]
    simp only [entry_conj, Formalism.FourierDecayAlt.Q.Econj, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
  have h2 : (Q * Q0⁻¹) * (Q0 * Q⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ0, Matrix.mul_nonsing_inv _ hdQ]
  have h3 : (Q0 * Q⁻¹) * (Q * Q0⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ, Matrix.mul_nonsing_inv _ hdQ0]
  rw [hEE, covariant_det_of_lin covariant_linear _ _ E0 _ _ hgl h2 h3]
  apply Subtype.ext
  have h4 := _root_.GlobalTheory.CapelliFreeAction.actU_qdet _ ε R.H (fun g => R.σ (Q0⁻¹ * g * Q0)) R.smSub E0
    (fun a b v => by rw [hd, hE0 a b v]; rfl) (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w
  rw [← h4, hC _ ε mu R.H _ hmu hDS w (hsm w w.2) Y]
  rfl

end GlobalTheory.CapelliSmooth
end

