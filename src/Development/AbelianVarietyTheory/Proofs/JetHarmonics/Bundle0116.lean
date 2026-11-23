module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsIsEigenBasis
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem eigBasis_of_generic {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {A J : Type} [Fintype J] {m : J → ℕ} {d : ℕ} (M : A → Matrix (Fin d) (Fin d) V) (χ : J → A → K)
    (hsep : ∀ j j', j ≠ j' → ∃ a, χ j a ≠ χ j' a) (u : (Σ j, Fin (m j)) → Fin d → V)
    (heig : ∀ a ℓ i, ∑ k, algebraMap V K (M a i k) * algebraMap V K (u ℓ k) = χ ℓ.1 a * algebraMap V K (u ℓ i))
    (hbas : ∀ p : Fin d → K, ∃! b : (Σ j, Fin (m j)) → K, ∀ k, ∑ ℓ, b ℓ * algebraMap V K (u ℓ k) = p k)
    (τ : J) (t : A → V) (ht : ∀ a, algebraMap V K (t a) = χ τ a)
    (hsat : ∀ (v : Fin d → V) (a : V), a ≠ 0 →
      a • v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩) →
      v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩)) :
    (∀ i a, (M a).mulVec (u ⟨τ, i⟩) = t a • u ⟨τ, i⟩) ∧
      ∀ v : Fin d → V, (∀ a, (M a).mulVec v = t a • v) → ∃! c : Fin (m τ) → V, ∑ i, c i • u ⟨τ, i⟩ = v := by
  classical
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  have hext : ∀ (g : Fin (m τ) → K) (k : Fin d),
      ∑ ℓ : (Σ j, Fin (m j)), (if h : ℓ.1 = τ then g (h ▸ ℓ.2) else 0) * algebraMap V K (u ℓ k) =
        ∑ i, g i * algebraMap V K (u ⟨τ, i⟩ k) := by
    intro g k
    rw [Fintype.sum_sigma, Finset.sum_eq_single τ]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  refine ⟨fun i a => ?_, fun v hv => ?_⟩
  · funext k
    apply hinj
    have := heig a ⟨τ, i⟩ k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, ht]
    exact this
  obtain ⟨b, hb, -⟩ := hbas fun k => algebraMap V K (v k)
  have hb0 : ∀ ℓ : (Σ j, Fin (m j)), ℓ.1 ≠ τ → b ℓ = 0 := by
    intro ℓ hℓ
    obtain ⟨a, ha⟩ := hsep _ _ hℓ
    have h1 : ∀ k, ∑ ℓ', (b ℓ' * χ ℓ'.1 a) * algebraMap V K (u ℓ' k) = χ τ a * algebraMap V K (v k) := by
      intro k
      have h2 := congrArg (algebraMap V K) (congrFun (hv a) k)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, ht] at h2
      rw [← h2]
      simp only [← hb, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ℓ' _ => ?_
      rw [mul_assoc, ← heig, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      ring
    have h2 : ∀ k, ∑ ℓ', (χ τ a * b ℓ') * algebraMap V K (u ℓ' k) = χ τ a * algebraMap V K (v k) := by
      intro k
      rw [← hb, Finset.mul_sum]
      simp only [mul_assoc]
    have h3 := congrFun ((hbas fun k => χ τ a * algebraMap V K (v k)).unique h1 h2) ℓ
    have h4 : b ℓ * (χ ℓ.1 a - χ τ a) = 0 := by
      rw [mul_sub, h3]; ring
    exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 ha)
  have hb1 : ∀ k, ∑ i, b ⟨τ, i⟩ * algebraMap V K (u ⟨τ, i⟩ k) = algebraMap V K (v k) := by
    intro k
    rw [← hb k, Fintype.sum_sigma, Finset.sum_eq_single τ]
    · intro j _ hj
      exact Finset.sum_eq_zero fun i _ => by rw [hb0 ⟨j, i⟩ hj, zero_mul]
    · simp
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors V) fun i => b ⟨τ, i⟩
  choose g hg using hs
  have hmem : (s : V) • v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩) := by
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨g, funext fun k => hinj ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hg, ← hb1, Finset.mul_sum]
    simp only [Algebra.smul_def, mul_assoc]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 (hsat v s (nonZeroDivisors.ne_zero s.2) hmem)
  refine ⟨c, hc, fun c' hc' => ?_⟩
  have hK : ∀ c : Fin (m τ) → V, ∑ i, c i • u ⟨τ, i⟩ = v → ∀ k,
      ∑ ℓ : (Σ j, Fin (m j)), (if h : ℓ.1 = τ then algebraMap V K (c (h ▸ ℓ.2)) else 0) * algebraMap V K (u ℓ k) =
        algebraMap V K (v k) := by
    intro c hc k
    rw [hext (fun i => algebraMap V K (c i)) k, ← hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  have h5 := (hbas fun k => algebraMap V K (v k)).unique (hK c' hc') (hK c hc)
  funext i
  apply hinj
  simpa using congrFun h5 ⟨τ, i⟩

theorem isEigBasis_uvecT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (τ : E →+* ℂ)
      (τT : 𝓞 E →+* T.V), (∀ a, algebraMap T.V T.Fr (τT a) = io (embK c τ a)) →
      IsEigBasis Ch.actT τT (fun i : Fin (Dw.mult τ) => Ch.uvecT ⟨τ, i⟩) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch τ τT hτ
  letI := io.toAlgebra
  have hu : ∀ ℓ i, Ch.ch.uvec ℓ i = algebraMap T.V T.Fr (Ch.uvecT ℓ i) := Ch.gen.1.2.2.2.2.2.2
  have hA : ∀ a j, Ch.ch.B.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (Ch.actT a j) := Ch.gen.1.2.1
  refine eigBasis_of_generic (K := T.Fr) (m := Dw.mult) (fun a => ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (Ch.actT a))
    (fun τ a => io (embK c τ a)) ?_ Ch.uvecT ?_ ?_ τ τT hτ (SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ).2
  · intro j j' h
    obtain ⟨a, ha⟩ := GlobalTheory.EigDir.embK_sep c j j' h
    exact ⟨a, fun e => ha (io.injective e)⟩
  · intro a ℓ i
    have h := GlobalTheory.EigDir.linEig_holds E H Dw l Xo c T.Fr y.1 Ch.ch a ℓ i
    simp only [hu, ReciprocityTheory.ChartRestriction.G.TB.dLin, hA] at h
    exact h
  · intro p
    have h := Ch.ch.chart.basis p
    simp only [hu] at h
    exact h

end GlobalTheory.CharDepth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFramedPointOfLevelMove
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormTies.LevelMove

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg.ChartInhab

attribute [local instance] Over.cartesianMonoidalCategory

theorem gs_of_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {σ : LB.Sec L'} {s : LB.Sec (L.pull F)} (h : IsoMaps w σ s) (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι)
    (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs r z _ (s.f (fun _ => j)) = (Geo.Tor.gw w r z j k).val * gs r z _ (σ.f k) := by
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have a := congrArg (gs r z _) (h (fun _ => j) k)
  exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))

theorem integral_of_levR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ y y' : FrPt Xo c T.Fr, levR (Xo := Xo) (c := c) g y y' → Integral T io y → Integral T io y' := by
  intro E _ _ _ H Dw l Xo c gl T io
  letI := io.toAlgebra
  rintro y y' ⟨ρ, ν, -, -, hx, hu, pm, w, p₁, p₂, hw, hs⟩
    ⟨G, t', m1, m2, ⟨ub, b₁, b₂, b₃, b₄⟩, θ, hθ, w1, w2, σ, s1, θ2, r₁, r₂, i₁, i₂, hp, hg⟩
  obtain ⟨n, hn, w', hw', tri⟩ := exists_comp_rig ν m1 y'.x hx ⟨hw.1, hw.2.1⟩ r₁
  have g' := (isGen_iff w').1 hw'.1
  obtain ⟨s', hs'⟩ := thf_secUp g' Xo.univ.t.PP.isLB t'.PP.isLB σ
  refine ⟨G, t', n, m2, ⟨ub, b₁, b₂, b₃, fun τ i => ?_⟩, θ, hθ, w', w2, σ, s', θ2, hw', r₂, ?_, i₂, hp, ?_⟩
  · obtain ⟨u', h₁, h₂⟩ := b₄ τ i
    exact ⟨u', by rw [hn, ← Category.assoc, h₁, hu], h₂⟩
  · exact fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun p hp =>
      (gs_res _ p _ hp _).trans ((hs' _ (𝟙 _) p i k hp.1 hp.2).trans (Eq.symm ((gs_mul _ p _ hp _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))
  · intro q e₁ e₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    refine fn_ext fun p hp => ?_
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB p
    obtain ⟨i, hi⟩ := exists_chart Xo.univ.t.PP.isLB (m1.φ p)
    have hp' : ν.φ (m1.φ p) ∈ Xo.univ.t.PP.L.U (J PUnit.unit) :=
      (congrArg (fun q => q p ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) hn).mp (mem_pull.1 hp)
    have eg : 𝟙 _ ≫ q = (𝟙 _ ≫ toGx m1) ≫ pm := by
      rw [Category.id_comp, Category.id_comp]
      apply FramedBaseChange.pulledGroup_hom_ext
      · rw [Category.assoc, p₂, e₁, hn, ← Category.assoc, toGx_snd]
      · rw [Category.assoc, p₁, e₂, toGx_fst]
    let W : (Gx y.x).Opens := (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ
      ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => J PUnit.unit), i))
    have h₁ : W ≤ pm ⁻¹ᵁ (PPx y'.x).U (fun _ => J PUnit.unit) := fun z hz => Set.mem_iInter.2 fun _ =>
      (congrArg (fun u => u z ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) p₂).mpr (mem_pull.1 hz.1)
    have h₂ : W ≤ (PPx y.x).U (fun _ => i) := fun z hz => Set.mem_iInter.2 fun _ => hz.2
    have es : (𝟙 _ ≫ toGx m1) ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = 𝟙 _ ≫ m1.φ := by
      rw [Category.assoc, toGx_snd]
    have hz₀ : (𝟙 _ ≫ m1.φ) p ∈ (LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => J PUnit.unit), i) :=
      ⟨mem_pull.2 hp', hi⟩
    have hz : (𝟙 _ ≫ toGx m1) p ∈ W :=
      (congrArg (fun u => u p ∈ (LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => J PUnit.unit), i))
        es).mpr hz₀
    have e := congrArg (gs (𝟙 _ ≫ toGx m1) p W) (hs (J PUnit.unit) i W rfl le_rfl h₁ h₂)
    rw [gs_appLE pm _ _ h₁ _ p hz, gs_mul _ p W hz, gs_appLE _ _ _ _ _ p hz, gs_res _ p h₂ hz, es,
      gs_unit _ p _ hz₀] at e
    have le : (Xo.univ.t.PP.L.pull m1.φ).U (fun _ => i) ≤ toGx m1 ⁻¹ᵁ (PPx y.x).U (fun _ => i) :=
      fun z hz => le_toGx m1 i (mem_pull.1 hz)
    have k₂ : gs (𝟙 _) p _ (s1.f (fun _ => i)) = gs (𝟙 _ ≫ toGx m1) p ((PPx y.x).U (fun _ => i)) (y.s.f (fun _ => i)) :=
      (congrArg (gs (𝟙 _) p _) (hg (toGx m1) (toGx_snd m1) (toGx_fst m1) (fun _ => i) le)).trans
        (gs_appLE (toGx m1) _ _ le (𝟙 _) p (mem_pull.2 hi) _)
    have k₃ := gs_of_isoMaps i₁ _ (𝟙 _) p i k hi hk
    rw [hs' _ (𝟙 _) p J k hp hk, gs_appLE q _ _ hJ (𝟙 _) p hp, eg, e, ← k₂, k₃,
      tri _ (𝟙 _) p _ i k hp' hi hk, Units.val_mul, _root_.mul_assoc]
    rfl

end GlobalTheory.FormTies.LevelMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsEigenBasisMapFlatBaseChange
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigBaseChange

theorem piScalarRight_lTensor_mulVec {R O : Type} [CommRing R] [CommRing O] [Algebra R O]
    {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n R)
    (x : O ⊗[R] (n → R)) :
    TensorProduct.piScalarRight R O O m (LinearMap.lTensor O A.mulVecLin x) =
      (A.map (algebraMap R O)).mulVec (TensorProduct.piScalarRight R O O n x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Matrix.mulVec_add]
  | tmul o v =>
    ext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, Finset.sum_mul, mul_assoc]

theorem exact_mulVec_map {R O : Type} [CommRing R] [CommRing O] [Algebra R O] [Module.Flat R O]
    {k m n : Type} [Fintype k] [Fintype m] [Fintype n] (A : Matrix m n R) (B : Matrix k m R)
    (h : Function.Exact A.mulVec B.mulVec) :
    Function.Exact (A.map (algebraMap R O)).mulVec (B.map (algebraMap R O)).mulVec := by
  classical
  have h' : Function.Exact A.mulVecLin B.mulVecLin := h
  have h2 := Module.Flat.lTensor_exact O h'
  intro y
  obtain ⟨y, rfl⟩ := (TensorProduct.piScalarRight R O O m).surjective y
  rw [← piScalarRight_lTensor_mulVec, LinearEquiv.map_eq_zero_iff, h2 y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, (piScalarRight_lTensor_mulVec A x).symm⟩
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight R O O n).surjective x
    rw [← piScalarRight_lTensor_mulVec] at hx
    exact ⟨x, (TensorProduct.piScalarRight R O O m).injective hx⟩

theorem transpose_mulVec {R : Type} [CommRing R] {d s : ℕ} (w : Fin s → Fin d → R) (c : Fin s → R) :
    (Matrix.of w).transpose.mulVec c = ∑ i, c i • w i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

def eigMat {R : Type} [CommRing R] {d N : ℕ} (L : Fin N → Matrix (Fin d) (Fin d) R)
    (t : Fin N → R) : Matrix (Fin N × Fin d) (Fin d) R :=
  Matrix.of fun p j => (L p.1 - t p.1 • (1 : Matrix (Fin d) (Fin d) R)) p.2 j

theorem eigMat_mulVec_eq_zero {R : Type} [CommRing R] {d N : ℕ}
    (L : Fin N → Matrix (Fin d) (Fin d) R) (t : Fin N → R) (v : Fin d → R) :
    (eigMat L t).mulVec v = 0 ↔ ∀ k, (L k).mulVec v = t k • v := by
  have key : ∀ k i, (eigMat L t).mulVec v (k, i) = ((L k).mulVec v - t k • v) i := by
    intro k i
    have : (eigMat L t).mulVec v (k, i) =
        (L k - t k • (1 : Matrix (Fin d) (Fin d) R)).mulVec v i := rfl
    rw [this, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · intro h k
    rw [← sub_eq_zero]
    ext i
    rw [← key, h]; rfl
  · intro h
    ext ⟨k, i⟩
    rw [key, h k, sub_self]; rfl

theorem eigMat_map {R O : Type} [CommRing R] [CommRing O] (f : R →+* O) {d N : ℕ}
    (L : Fin N → Matrix (Fin d) (Fin d) R) (t : Fin N → R) :
    (eigMat L t).map f = eigMat (fun k => (L k).map f) (fun k => f (t k)) := by
  ext ⟨k, i⟩ j
  by_cases h : i = j <;> simp [eigMat, Matrix.one_apply, h]

theorem eig_of_span {R OE : Type} [CommRing R] [CommRing OE] {d N : ℕ}
    (L : OE → Matrix (Fin d) (Fin d) R) (hL : ∀ a b, L (a + b) = L a + L b) (τ : OE →+* R)
    (g : Fin N → OE) (hg : Submodule.span ℤ (Set.range g) = ⊤) (v : Fin d → R)
    (hv : ∀ k, (L (g k)).mulVec v = τ (g k) • v) (a : OE) : (L a).mulVec v = τ a • v := by
  let L' : OE →+ Matrix (Fin d) (Fin d) R := AddMonoidHom.mk' L hL
  change (L' a).mulVec v = _
  have ha : a ∈ Submodule.span ℤ (Set.range g) := hg ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hv k
  | zero => simp
  | add x y _ _ hx hy => simp [Matrix.add_mulVec, hx, hy, add_smul]
  | smul z x _ hx => rw [map_zsmul, map_zsmul, Matrix.smul_mulVec, hx, smul_assoc]

theorem linPart_map {R O : Type} [CommRing R] [CommRing O] (f : R →+* O) {d : ℕ}
    (φ : Fin d → PS R 1 d) :
    ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (fun i => MvPowerSeries.map f (φ i)) = (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart φ).map f := by
  ext i j
  simp [ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart, MvPowerSeries.coeff_map]

theorem isEigBasis_map : ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Flat R O] (OE : Type) [CommRing OE] [Module.Finite ℤ OE] (d s : ℕ) (act : OE → Fin d → PS R 1 d), (∀ a b, ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (act (a + b)) = ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (act a) + ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (act b)) → ∀ (τ : OE →+* R) (w : Fin s → Fin d → R), IsEigBasis act τ w → IsEigBasis (fun a i => MvPowerSeries.map (algebraMap R O) (act a i)) ((algebraMap R O).comp τ) (fun i j => algebraMap R O (w i j)) := by
  intro R O _ _ _ _ OE _ _ d s act hadd τ w hw
  obtain ⟨N, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := OE)
  have hadd' : ∀ a b, (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (act (a + b))).map (algebraMap R O) =
      (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (act a)).map (algebraMap R O) + (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (act b)).map (algebraMap R O) := by
    intro a b
    rw [hadd, Matrix.map_add _ (map_add _)]
  have hlin : ∀ (c : Fin s → R) a, (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (act a)).mulVec (∑ i, c i • w i) = τ a • ∑ i, c i • w i := by
    intro c a
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, hw.1, smul_comm]
  have ex1 : Function.Exact (Matrix.of w).transpose.mulVec
      (eigMat (fun k => ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (act (g k))) (fun k => τ (g k))).mulVec := by
    intro v
    rw [eigMat_mulVec_eq_zero]
    constructor
    · intro h
      obtain ⟨c, hc, -⟩ := hw.2 v (eig_of_span (fun a => ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (act a)) hadd τ g hg v h)
      exact ⟨c, by rw [transpose_mulVec, hc]⟩
    · rintro ⟨c, rfl⟩ k
      rw [transpose_mulVec]; exact hlin c _
  have ex0 : Function.Exact (0 : Matrix (Fin s) (Fin 0) R).mulVec (Matrix.of w).transpose.mulVec := by
    intro c
    rw [transpose_mulVec]
    constructor
    · intro h
      obtain ⟨c0, -, hu⟩ := hw.2 0 (by simp)
      exact ⟨0, by rw [hu c h, ← hu 0 (by simp)]; simp⟩
    · rintro ⟨x, rfl⟩
      simp
  have ex1' := exact_mulVec_map (O := O) _ _ ex1
  have ex0' := exact_mulVec_map (O := O) _ _ ex0
  have hT : ((Matrix.of w).transpose.map (algebraMap R O)) =
      (Matrix.of fun i j => algebraMap R O (w i j)).transpose := rfl
  rw [hT] at ex1' ex0'
  rw [eigMat_map] at ex1'
  constructor
  · intro i a
    rw [linPart_map]
    ext j
    have := congrArg (algebraMap R O) (congrFun (hw.1 i a) j)
    simpa [Matrix.mulVec, dotProduct] using this
  · intro v hv
    simp only [linPart_map] at hv
    obtain ⟨c, hc⟩ := (ex1' v).1 ((eigMat_mulVec_eq_zero _ _ _).2 fun k => hv (g k))
    rw [transpose_mulVec] at hc
    refine ⟨c, hc, fun c' hc' => ?_⟩
    obtain ⟨x, hx⟩ := (ex0' (c' - c)).1 (by
      rw [Matrix.mulVec_sub, transpose_mulVec, transpose_mulVec]
      exact sub_eq_zero.2 (hc'.trans hc.symm))
    rw [← sub_eq_zero, ← hx]
    simp

end GlobalTheory.EigBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegAtOfSabMap
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlphaPair

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] in
omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem _root_.GlobalTheory.AlphaPair.exists_ptEquiv {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (gp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f F) {Z : Scheme.{0}}
    (a : Z ⟶ S') (b : Z ⟶ S) (hb : b = a ≫ f) :
    ∃ ρ : (Over.mk a ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (ρ x).left = x.left ≫ F := by
  subst hb
  have hpb : IsPullback F G'.hom G.hom f := gp.1
  let φ : (Over.mk a ⟶ G') → (Over.mk (a ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ F) (by
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w x]
      rfl)
  let ψ : (Over.mk (a ≫ f) ⟶ G) → (Over.mk a ⟶ G') := fun y =>
    Over.homMk (hpb.lift y.left a (by simpa using Over.w y)) (by simp)
  refine ⟨{ toFun := φ, invFun := ψ, left_inv := ?_, right_inv := ?_, map_mul' := ?_ },
    fun x => rfl⟩
  · intro x
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · simp [φ, ψ]
    · simp [φ, ψ]
  · intro y
    apply Over.OverMorphism.ext
    simp [φ, ψ]
  · intro x y
    apply Over.OverMorphism.ext
    exact (gp.2 (Over.mk a) x y (φ x) (φ y) rfl rfl).symm

end GlobalTheory.AlphaPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuationBlockPolynomialGeProd
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem valuation_blockPoly_ge : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (Ty : Type) [Fintype Ty] [DecidableEq Ty] (r : Ty → ℕ) (n : ℕ) (β : (Σ τ : Ty, Fin (r τ)) → Fin n), Function.Injective β → ∀ (a : Ty → ℕ → ℕ), Crude.Dom r a → ∀ (yv : Letter Ty r n → O) (x : Ty → NNReal), (∀ τ, x τ ≤ 1) → (∀ τ (i : Fin (r τ)), x τ ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => yv ⟨τ, Fin.castLE i.isLt a, β ⟨τ, Fin.castLE i.isLt b⟩⟩).det)) → (∏ τ, x τ ^ (a τ 0) ≤ v (algebraMap O C (MvPolynomial.eval yv (Crude.crP r n O β a)))) ∧ ∀ mo ∈ (Crude.crP r n O β a).support, ∀ ℓ, mo ℓ ≠ 0 → ∃ i, β ⟨ℓ.1, i⟩ = ℓ.2.2 := by
  intro C _ v O _ _ _ Ty _ _ r n β _ a ha yv x hx hmin
  refine ⟨?_, fun mo hmo ℓ hℓ => ?_⟩
  · unfold Crude.crP
    rw [map_prod, map_prod, map_prod]
    refine Finset.prod_le_prod' fun τ _ => ?_
    rw [map_prod, map_prod, map_prod]
    have h1 : x τ ^ (a τ 0) ≤ ∏ kk : Fin (r τ), x τ ^ Crude.crExp r a τ kk := by
      rw [Finset.prod_pow_eq_pow_sum]
      refine pow_le_pow_of_le_one zero_le (hx τ) ?_
      rcases Nat.eq_zero_or_pos (r τ) with h0 | h0
      · haveI : IsEmpty (Fin (r τ)) := by rw [h0]; infer_instance
        simp
      · have := Crude.crExpSum a ha τ ⟨0, h0⟩
        simp only [Nat.zero_lt_succ, if_true] at this
        exact this.le
    refine h1.trans (Finset.prod_le_prod' fun kk _ => ?_)
    rw [map_pow, map_pow, map_pow]
    refine pow_le_pow_left₀ zero_le ?_ _
    have h2 : MvPolynomial.eval yv (Crude.crMinor r n O β τ kk).det =
        (Matrix.of fun a b : Fin (kk.val + 1) =>
          yv ⟨τ, Fin.castLE kk.isLt a, β ⟨τ, Fin.castLE kk.isLt b⟩⟩).det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [Crude.crMinor, RingHom.mapMatrix_apply]
    rw [h2]
    exact hmin τ kk
  · exact MvPolynomial.mem_supported.1 (Crude.crP_mem_supported O β a)
      ((MvPolynomial.mem_vars_iff_mem_support ℓ).2 ⟨mo, hmo, Finsupp.mem_support_iff.2 hℓ⟩)

end GlobalTheory.CharDepth
end

