module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.HermitianCurvature.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRepStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFRep_exteriorPower_standardRep : ∀ (k r : ℕ) (l : ℕ), IsFRep (k := k) (r := r) (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) l := by
  first | exact @GlobalTheory.WedgeFRep.isFRep_cmp | exact GlobalTheory.WedgeFRep.isFRep_cmp | (intros; apply GlobalTheory.WedgeFRep.isFRep_cmp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFiniteFlatTorsionOfIsGt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace ExtensionTorsion

open KernelNoTorsion

variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]

noncomputable def torsionHom (q : G ⟶ B) [IsMonHom q] (N : ℕ) : torsion G N ⟶ torsion B N :=
  torsionLift (torsion.ι G N ≫ q) (by rw [← MonObj.pow_comp, torsionι_pow, MonObj.one_comp])

theorem torsionHom_ι (q : G ⟶ B) [IsMonHom q] (N : ℕ) :
    torsionHom q N ≫ torsion.ι B N = torsion.ι G N ≫ q :=
  torsionLift_ι _ _

theorem exists_isPullback_mulN [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P Q : Over S} {a : P ⟶ G} {b : P ⟶ torsion B N} (hP : IsPullback a b q (torsion.ι B N))
    {s : Q ⟶ P} {r : Q ⟶ torsion G N} (hQ : IsPullback s r b (torsionHom q N)) :
    ∃ (c : P ⟶ T) (t : Q ⟶ T), IsPullback s t c (mulN T N) := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  have hpow : ∀ {W : Over S} (x : W ⟶ torsion G N), (x ≫ torsion.ι G N) ^ N = 1 := fun x => by
    rw [← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]
  obtain ⟨c, hc⟩ := ex (a ^ N) (by
    rw [MonObj.pow_comp, hP.w, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one])
  have hsr : s ≫ a ≫ q = r ≫ torsion.ι G N ≫ q := by
    rw [hP.w, ← Category.assoc, hQ.w, Category.assoc, torsionHom_ι]
  obtain ⟨t, ht⟩ := ex ((s ≫ a) / (r ≫ torsion.ι G N)) (by
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, hsr, div_self'])
  refine ⟨c, t, ⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · apply inj
    rw [comp_mulN, MonObj.pow_comp, ht, div_pow, hpow, div_one, Category.assoc, hc,
      MonObj.comp_pow]
  · have hW : W.fst ≫ c = W.snd ^ N := by rw [W.condition, comp_mulN]
    have hg : ((W.fst ≫ a) / (W.snd ≫ i)) ^ N = 1 := by
      rw [div_pow, ← MonObj.pow_comp _ _ i, ← hW, Category.assoc, hc, MonObj.comp_pow, div_self']
    have hl : W.fst ≫ b = torsionLift _ hg ≫ torsionHom q N := by
      apply torsion_hom_ext
      rw [Category.assoc, Category.assoc, torsionHom_ι, ← Category.assoc (torsionLift _ hg),
        torsionLift_ι, GrpObj.div_comp, Category.assoc, Category.assoc, hiq, MonObj.comp_one,
        div_one, hP.w]
    refine ⟨hQ.lift W.fst _ hl, hQ.lift_fst _ _ _, ?_, ?_⟩
    · apply inj
      change (_ ≫ t) ≫ i = _
      rw [Category.assoc, ht, GrpObj.comp_div, ← Category.assoc, ← Category.assoc, hQ.lift_fst,
        hQ.lift_snd, torsionLift_ι, div_div_cancel]
    · intro (m : W.pt ⟶ Q) (h1 : m ≫ s = W.fst) (h2 : m ≫ t = W.snd)
      change m = _
      refine hQ.hom_ext (by rw [hQ.lift_fst, h1]) ?_
      apply torsion_hom_ext
      rw [hQ.lift_snd, torsionLift_ι, ← h1, ← h2, Category.assoc, Category.assoc, Category.assoc,
        ht, GrpObj.comp_div, div_div_cancel]

theorem torsionHom_of_mulN (Pr : MorphismProperty Scheme.{0}) [Pr.IsStableUnderBaseChange]
    [Pr.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ) (h : Pr (mulN T N).left) :
    Pr (torsionHom q N).left := by
  have hP := IsPullback.of_hasPullback q (torsion.ι B N)
  have hQ := IsPullback.of_hasPullback (pullback.snd q (torsion.ι B N)) (torsionHom q N)
  obtain ⟨c, t, H⟩ := exists_isPullback_mulN i q hk N hP hQ
  have hP' := hP.map (Over.forget S)
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := Pr)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (hQ.map (Over.forget S)) ⟨⟨?_, ?_⟩, ?_⟩ ?_
  · exact MorphismProperty.of_isPullback (P := @Surjective) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := Pr) (H.map (Over.forget S)).flip h

end ExtensionTorsion


open ExtensionTorsion in
theorem isFinite_flat_torsion_of_isGt :
    ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G], E.IsGt G → ∀ N : ℕ, 1 ≤ N → IsFinite (torsion E.B N).hom → Flat (torsion E.B N).hom → IsFinite (torsion G N).hom ∧ Flat (torsion G N).hom := by
  rintro S E G _ _ ⟨D⟩ N hN h1 h2
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have hN' : N ≠ 0 := by omega
  have hf : IsFinite (mulN (splitTorus S E.X) N).left := Diag.isFinite_mulN S E.X hN'
  have hl : Flat (mulN (splitTorus S E.X) N).left := Diag.flat_mulN S E.X hN'
  have := flat_descendsAlong_fpqc
  have := isAffineHom_descendsAlong_fpqc.{0}
  have a1 : Flat (torsionHom D.q N).left :=
    torsionHom_of_mulN @Flat D.i D.q D.isKernel N hl
  have a2 : IsAffineHom (torsionHom D.q N).left :=
    torsionHom_of_mulN @IsAffineHom D.i D.q D.isKernel N inferInstance
  have a3 : UniversallyClosed (torsionHom D.q N).left :=
    torsionHom_of_mulN @UniversallyClosed D.i D.q D.isKernel N inferInstance
  have a4 : LocallyOfFiniteType (torsionHom D.q N).left :=
    torsionHom_of_mulN @LocallyOfFiniteType D.i D.q D.isKernel N inferInstance
  have a5 : IsFinite (torsionHom D.q N).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  rw [← Over.w (torsionHom D.q N)]
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.QuotRightInv

open PI

theorem measurable_mul_left {m : ℕ} (x : MtM m) :
    Measurable (fun s : MtM m => (fun i j => (Matrix.of s * Matrix.of x) i j : MtM m)) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurable_rmulQ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : Measurable (rmulQ g) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [rmulQ, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurableSet_not_mem {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) :
    MeasurableSet {x : MtM m | Matrix.of x ∉ G} := by
  have hc : IsClosed {x : MtM m | Matrix.of x ∈ G} := by
    have hof : Continuous (fun x : MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
    exact hG.1.preimage hof
  exact hc.measurableSet.compl

private lemma mul_not_mem_of_mem_of_not_mem {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G)
    (hSG : S ⊆ G) {s x : Matrix (Fin m) (Fin m) ℂ} (hs : s ∈ S) (hx : x ∉ G) : s * x ∉ G := by
  intro hsx
  apply hx
  obtain ⟨hinv, hone⟩ := hG.2.2.2 s (hSG hs)
  have hleft : s⁻¹ * s = 1 := mul_eq_one_comm.mp hone
  have h1 := hG.2.2.1 _ hinv _ hsx
  rwa [← Matrix.mul_assoc, hleft, Matrix.one_mul] at h1

private lemma continuous_mul_swap_pair {m : ℕ} :
    Continuous (fun p : MtM m × MtM m => (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : MtM m)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem ae_mem_of_quot {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
    (h : QuotientSetting G S μG μS ν) : ∀ᵐ x ∂ν, Matrix.of x ∈ G := by
  obtain ⟨hG, hS, hSG, hHG, hHS, -, -, hQ⟩ := h
  have : SigmaFinite μS := hHS.1
  have hBm : MeasurableSet {x : MtM m | Matrix.of x ∉ G} := measurableSet_not_mem hG
  have hSm : MeasurableSet {x : MtM m | Matrix.of x ∈ S} := by
    have h1 := (measurableSet_not_mem hS).compl
    simpa only [Set.compl_setOf, not_not] using h1
  have hf : Measurable ({x : MtM m | Matrix.of x ∉ G}.indicator (1 : MtM m → ℝ≥0∞)) :=
    measurable_one.indicator hBm
  have h0 := hQ _ hf
  rw [lintegral_indicator_one hBm, hHG.2.2.1] at h0
  have hinner : Measurable fun x : MtM m =>
      ∫⁻ s, {x : MtM m | Matrix.of x ∉ G}.indicator (1 : MtM m → ℝ≥0∞)
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS :=
    Measurable.lintegral_prod_right (hf.comp continuous_mul_swap_pair.measurable)
  have hae := (lintegral_eq_zero_iff hinner).mp h0.symm
  have hSpos : μS {s : MtM m | Matrix.of s ∈ S} ≠ 0 := by
    intro hz
    apply hHS.2.1
    rw [← Measure.measure_univ_eq_zero]
    have hu := measure_union_le (μ := μS) {s : MtM m | Matrix.of s ∈ S} {s : MtM m | Matrix.of s ∈ S}ᶜ
    rw [Set.union_compl_self] at hu
    have hc : μS {s : MtM m | Matrix.of s ∈ S}ᶜ = 0 := hHS.2.2.1
    rw [hz, hc, add_zero] at hu
    exact le_antisymm hu zero_le
  filter_upwards [hae] with x hx
  by_contra hxG
  apply hSpos
  refine le_antisymm ?_ zero_le
  refine le_trans ?_ (le_of_eq hx)
  rw [← lintegral_indicator_one hSm]
  refine lintegral_mono fun s => ?_
  by_cases hs : Matrix.of s ∈ S
  · have hs' : s ∈ {s : MtM m | Matrix.of s ∈ S} := hs
    have hmem : (fun i j => (Matrix.of s * Matrix.of x) i j : MtM m) ∈ {x : MtM m | Matrix.of x ∉ G} :=
      mul_not_mem_of_mem_of_not_mem hG hSG hs hxG
    have e1 : {s : MtM m | Matrix.of s ∈ S}.indicator (1 : MtM m → ℝ≥0∞) s = 1 :=
      Set.indicator_of_mem hs' _
    have e2 : {x : MtM m | Matrix.of x ∉ G}.indicator (1 : MtM m → ℝ≥0∞)
        (fun i j => (Matrix.of s * Matrix.of x) i j) = 1 := Set.indicator_of_mem hmem _
    exact (e1.trans e2.symm).le
  · have e1 : {s : MtM m | Matrix.of s ∈ S}.indicator (1 : MtM m → ℝ≥0∞) s = 0 :=
      Set.indicator_apply_eq_zero.mpr fun h' => absurd h' hs
    exact e1.trans_le zero_le

theorem lintegral_eq_cutoff {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
    (h : QuotientSetting G S μG μS ν) (φ : MtM m → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∀ x : MtM m, Matrix.of x ∈ G →
      ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1)
    (F : MtM m → ℝ≥0∞) (hF : Measurable F)
    (hFS : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (fun i j => (s * Matrix.of x) i j) = F x) :
    ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  have hνG := ae_mem_of_quot h
  obtain ⟨hG, hS, hSG, hHG, hHS, hRG, hRS, hQ⟩ := h
  rw [hQ (fun x => φ x * F x) (hφ.mul hF)]
  refine lintegral_congr_ae ?_
  filter_upwards [hνG] with x hx
  have hSae : ∀ᵐ s ∂μS, Matrix.of s ∈ S := ae_iff.mpr hHS.2.2.1
  have e : ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) *
        F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS
      = ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) * F x ∂μS := by
    refine lintegral_congr_ae ?_
    filter_upwards [hSae] with s hs
    rw [hFS _ hs x hx]
  rw [e, lintegral_mul_const (f := fun s : MtM m => φ (fun i j => (Matrix.of s * Matrix.of x) i j)) _
    (hφ.comp (measurable_mul_left x)), hφ1 x hx, one_mul]

theorem quotInv : PI.QuotInv := by
  intro m G S μG μS ν h F hF hFS g hg
  obtain ⟨φ, hφ, hφ1⟩ := _root_.GlobalTheory.exists_normalised_cutoff m G S μS h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.1
  have hG : IsMatGroup G := h.1
  have hxg : ∀ x : MtM m, Matrix.of x ∈ G →
      Matrix.of (fun i j => (Matrix.of x * g) i j : MtM m) ∈ G := fun x hx => hG.2.2.1 _ hx _ hg
  have hφ' : Measurable (fun x : MtM m => φ (fun i j => (Matrix.of x * g) i j)) :=
    hφ.comp (measurable_rmulQ g)
  have hφ'1 : ∀ x : MtM m, Matrix.of x ∈ G →
      ∫⁻ s, (fun x : MtM m => φ (fun i j => (Matrix.of x * g) i j))
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1 := by
    intro x hx
    rw [← hφ1 _ (hxg x hx)]
    refine lintegral_congr fun s => ?_
    show φ _ = φ _
    congr 1
    change (Matrix.of s * Matrix.of x) * g = Matrix.of s * (Matrix.of x * g)
    exact Matrix.mul_assoc _ _ _
  have hFg : Measurable (fun x : MtM m => F (fun i j => (Matrix.of x * g) i j)) :=
    hF.comp (measurable_rmulQ g)
  have hFgS : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G →
      (fun x : MtM m => F (fun i j => (Matrix.of x * g) i j)) (fun i j => (s * Matrix.of x) i j) =
        (fun x : MtM m => F (fun i j => (Matrix.of x * g) i j)) x := by
    intro s hs x hx
    have key := hFS s hs _ (hxg x hx)
    refine Eq.trans ?_ key
    show F _ = F _
    congr 1
    change (s * Matrix.of x) * g = s * (Matrix.of x * g)
    exact Matrix.mul_assoc _ _ _
  have e1 := lintegral_eq_cutoff h _ hφ' hφ'1 _ hFg hFgS
  have e2 := lintegral_eq_cutoff h φ hφ hφ1 F hF hFS
  refine e1.trans (Eq.trans ?_ e2.symm)
  calc ∫⁻ x, φ (fun i j => (Matrix.of x * g) i j) * F (fun i j => (Matrix.of x * g) i j) ∂μG
      = ∫⁻ x, (fun y => φ y * F y) (rmulQ g x) ∂μG := rfl
    _ = ∫⁻ x, (fun y => φ y * F y) x ∂(μG.map (rmulQ g)) :=
        (lintegral_map (hφ.mul hF) (measurable_rmulQ g)).symm
    _ = ∫⁻ x, φ x * F x ∂μG := by rw [h.2.2.2.2.2.1 g hg]

end GlobalTheory.QuotRightInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopNum
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TopNum

theorem hsq_le (r : ℕ) (T b C : ℝ) (hC : 0 ≤ C) (hb : 2 ≤ b)
    (hT : T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ))) :
    Hsq r T b ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have h1 : (1 : ℝ) ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) :=
    Real.one_le_rpow hb1 (mul_nonneg hC (Nat.cast_nonneg _))
  have h2 : max 1 T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) := max_le h1 hT
  have h3 : (C + 10) * ((2 * r + 2 : ℕ) : ℝ)
      = C * ((2 * r + 2 : ℕ) : ℝ) + ((20 * (r + 1) : ℕ) : ℝ) := by
    push_cast; ring
  rw [h3, Real.rpow_add hb0, Real.rpow_natCast]
  unfold Hsq
  exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hb0.le _)

theorem top_num : ∀ (r : ℕ) (T T' b C : ℝ), 0 ≤ C → 2 ≤ b → T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) → T' ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) → Real.sqrt (Hsq r T b * Hsq r T' b) ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := by
  intro r T T' b C hC hb hT hT'
  have hb0 : 0 < b := by linarith
  have h1 := hsq_le r T b C hC hb hT
  have h2 := hsq_le r T' b C hC hb hT'
  have hp : 0 ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := Real.rpow_nonneg hb0.le _
  have h0 : 0 ≤ Hsq r T' b := by
    unfold Hsq
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (pow_nonneg hb0.le _)
  rw [Real.sqrt_le_left hp, sq]
  exact mul_le_mul h1 h2 h0 hp

end GlobalTheory.TopNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslatePullbackEigensection
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelEigen

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem sval_act {n : ℤ} {θ : ThetaGrp A L n T} {s s' : LB.Sec (LPow A L n T)} (H : IsActOf A L n θ s s')
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J) (hJ : Good L z J) :
    sval s' r z J = (tval θ r z J).val * sval s (r ≫ (translT A θ.pt).left) z J := by
  have l₁ := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _)
  let j : Fin 2 → L.ι := fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)
  have hz : r z ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j := hJ.mem _ r
  have e : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left, translT, lift_snd]
  rw [sval_of s _ z J (fun _ => j 1) (fun _ => by rw [Category.assoc, e]; rfl)]
  exact (gs_res r z (chart_le_zero A L _ j) hz _).symm.trans ((congrArg (gs r z _) (H j)).trans
    ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _)
      ((gs_res r z (l₁ j) hz _).trans (gs_pull r (translT A θ.pt).left z
        (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1)) (l₁ j hz) _)))))

theorem translT_snd_comp (a : A ⟶ A) [IsMonHom a] {c : T ⟶ A} (hc : c ≫ a = 1) :
    translT A c ≫ snd T A ≫ a = snd T A ≫ a := by
  rw [← Category.assoc, translT, lift_snd]
  show ((fst T A ≫ c) * snd T A) ≫ a = _
  rw [MonObj.mul_comp, Category.assoc, hc, MonObj.comp_one, _root_.one_mul]

theorem translT_whisker (a : A ⟶ A) [IsMonHom a] {c : T ⟶ A} (hc : c ≫ a = 1) :
    translT A c ≫ T ◁ a = T ◁ a := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [Category.assoc, whiskerLeft_snd, translT_snd_comp a hc]

theorem translT_comm [IsCommMonObj A] (x y : T ⟶ A) : translT A x ≫ translT A y = translT A y ≫ translT A x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · apply Over.OverMorphism.ext
    simp only [Over.comp_left, Category.assoc, H1.transl_snd]
    exact H1.transl_comm x y

theorem exists_kernel_lift (hL : L.IsLB) (a : A ⟶ A) [IsMonHom a] {m k : ℤ}
    (mu : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ≫ a).left] ![m, -k])) (hmu : mu.IsGen)
    {c : T ⟶ A} (hc : c ≫ a = 1) :
    ∃ θ : ThetaGrp A L m T, θ.pt = c ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval θ r z J = val mu r z J * (val mu (r ≫ (translT A c).left) z J)⁻¹ := by
  have e₀ : (translT A c).left ≫ (snd T A).left = (translPt A c).left := by
    rw [← Over.comp_left, translT, lift_snd]
  have e₁ : (translT A c).left ≫ (snd T A ≫ a).left = (snd T A ≫ a).left := by
    rw [← Over.comp_left, translT_snd_comp a hc]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A c).left]) (ε' := ![m, -m])
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₀, e₁,
        zpow_neg, inv_inv, Pi.neg_apply]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L _ _ _ _ mu (LB.invGen L _ _ (LB.pullGen L _ _ mu (translT A c).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hmu (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hmu _)))
  refine ⟨⟨c, u, hu⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
  rw [val_mul hJ, val_inv, val_pull hJ]

theorem commIsOf_of_weilIs (hL : L.IsLB) [Unique T.left] {n : ℤ} (θx θy : ThetaGrp A L n T)
    {e : Γ(T.left, ⊤)ˣ} (H : WeilIs A L n θx.pt θy.pt e) : CommIsOf A L n θx θy e := by
  obtain ⟨V, hV, -, H⟩ := H default
  obtain rfl : V = ⊤ := top_le_iff.1 fun x _ => by rw [Subsingleton.elim x default]; exact hV
  let h := overResι (T := T) ⊤
  have : IsIso h.left := inferInstanceAs (IsIso (Scheme.topIso T.left).hom)
  have : IsIso ((Over.forget S).map h) := this
  have : IsIso h := isIso_of_reflects_iso h (Over.forget S)
  obtain ⟨θx', hx, vx⟩ := exists_pull hL h θx
  obtain ⟨θy', hy, vy⟩ := exists_pull hL h θy
  have H' := (commIsOf_iff hL _ _ _).1 (H θx' θy' hx hy)
  rw [commIsOf_iff hL]
  intro Z r z J hJ
  obtain ⟨r', rfl⟩ : ∃ r' : Z ⟶ (overRes (T := T) ⊤ ⊗ A).left, r = r' ≫ (h ▷ A).left :=
    ⟨r ≫ (inv (h ▷ A)).left, by rw [Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left,
      Category.comp_id]⟩
  have t : ∀ x : T ⟶ A, (r' ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r' ≫ (h ▷ A).left) ≫ (translT A x).left := fun x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have g : gm (r' ≫ (fst (overRes (T := T) ⊤) A).left) z ⊤ (Units.map h.left.appTop.hom.toMonoidHom e) =
      gm ((r' ≫ (h ▷ A).left) ≫ (fst T A).left) z ⊤ e := by
    refine (gm_pull (r' ≫ (fst (overRes (T := T) ⊤) A).left) h.left z ⊤ trivial e).trans ?_
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  have := H' Z r' z J hJ
  rw [vx _ _ z J hJ, vx _ _ z J hJ, vy _ _ z J hJ, vy _ _ z J hJ, hx, hy, t, t] at this
  exact this.trans (congrArg _ g)

end GlobalTheory.KernelEigen

namespace GlobalTheory


open KernelEigen CommPairing in
theorem translate_pullback_eigensection : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (K : Type) [Field K] (p : Spec (CommRingCat.of K) ⟶ S) (a : A ⟶ A), IsMonHom a → ∀ (N k : ℕ) (mu : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd (Over.mk p) A).left, (snd (Over.mk p) A ≫ a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)])), mu.IsGen → ∀ (s : LB.Sec (LPow A L (k : ℤ) (Over.mk p))) (t' t : LB.Sec (LPow A L ((k * N : ℕ) : ℤ) (Over.mk p))), (∀ (z : (Over.mk p ⊗ A).left) (J), Good L z J → sval t' (𝟙 _) z J = (val mu (𝟙 _) z J).val * sval s (Over.mk p ◁ a).left z J) → ∀ θ : ThetaGrp A L ((k * N : ℕ) : ℤ) (Over.mk p), IsActOf A L ((k * N : ℕ) : ℤ) θ t' t → ∀ (c : Over.mk p ⟶ A) (e : Γ((Over.mk p).left, ⊤)ˣ), c ≫ a = 1 → WeilIs A L ((k * N : ℕ) : ℤ) c θ.pt e → ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk p ⊗ A).left) (z : Z) (J), Good L z J → sval t (r ≫ (translT A c).left) z J * (val mu r z J).val = gs (r ≫ (fst (Over.mk p) A).left) z ⊤ e.val * (sval t r z J * (val mu (r ≫ (translT A c).left) z J).val) := by
  intro S A _ _ L hL K _ p a ha N k mu hmu s t' t ht' θ hθ c e hc hW Z r z J hJ
  haveI : Unique (Over.mk p).left := inferInstanceAs (Unique (PrimeSpectrum K))
  obtain ⟨θc, rfl, hv⟩ := exists_kernel_lift hL a mu hmu hc
  have hC := (commIsOf_iff hL _ _ _).1 (commIsOf_of_weilIs hL θc θ hW) Z r z J hJ
  have hs := ReciprocityTheory.ChartRestriction.G.Geo.Tor.secRel_iff hL _ _ t' _ _ s (Over.mk p ◁ a).left _ _ mu
  have ht := hs.1 (hs.2 fun y J hJ => by rw [ht' y J hJ, Category.id_comp, _root_.mul_comm])
  have e₁ : (r ≫ (translT A θc.pt).left) ≫ (translT A θ.pt).left =
      (r ≫ (translT A θ.pt).left) ≫ (translT A θc.pt).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, translT_comm]
  have e₂ : ((r ≫ (translT A θ.pt).left) ≫ (translT A θc.pt).left) ≫ (Over.mk p ◁ a).left =
      (r ≫ (translT A θ.pt).left) ≫ (Over.mk p ◁ a).left := by
    rw [Category.assoc, ← Over.comp_left, translT_whisker a hc]
  rw [sval_act hθ _ z J hJ, sval_act hθ _ z J hJ, e₁, ht _ _ z J hJ, ht _ _ z J hJ, e₂,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_unit _ z ⊤ trivial]
  rw [hv _ _ z J hJ, hv _ _ z J hJ] at hC
  generalize tval θ (r ≫ (translT A θc.pt).left) z J = x₁ at hC ⊢
  generalize tval θ r z J = x₂ at hC ⊢
  generalize val mu ((r ≫ (translT A θ.pt).left) ≫ (translT A θc.pt).left) z J = x₃ at hC ⊢
  generalize val mu (r ≫ (translT A θ.pt).left) z J = x₄ at hC ⊢
  generalize val mu (r ≫ (translT A θc.pt).left) z J = x₅ at hC ⊢
  generalize val mu r z J = x₆ at hC ⊢
  generalize ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm (r ≫ (fst (Over.mk p) A).left) z ⊤ e = x₇ at hC ⊢
  have key : x₁ * x₃ * x₆ = x₇ * x₂ * x₄ * x₅ := by
    apply Additive.ofMul.injective
    have a₀ := congrArg Additive.ofMul hC
    simp only [ofMul_mul, ofMul_inv] at a₀ ⊢
    linear_combination (norm := abel) a₀
  have key' := congrArg Units.val key
  simp only [Units.val_mul] at key'
  linear_combination (sval s ((r ≫ (translT A θ.pt).left) ≫ (Over.mk p ◁ a).left) z J) * key'

end GlobalTheory
end
end

