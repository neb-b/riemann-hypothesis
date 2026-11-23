module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedOfChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ChartRig

variable {X Y : Scheme.{0}}

theorem res_pullU_eq (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU f U x) = Units.map (f.appLE U V h).hom.toMonoidHom x := by
  ext
  rfl

theorem res_res_pullU (f : Y ⟶ X) (U : X.Opens) (V W : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ V)
    (x : Γ(X, U)ˣ) : res h' (res h (pullU f U x)) = res (h'.trans h) (pullU f U x) := by
  rw [res_pullU_eq, res_pullU_eq]
  ext
  change (f.appLE U V h ≫ Y.presheaf.map (homOfLE h').op).hom x = _
  rw [Scheme.Hom.appLE_map]
  rfl

theorem res_pullU_res (f : Y ⟶ X) (U U' : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U') (h' : U' ≤ U)
    (h'' : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU f U' (res h' x)) = res h'' (pullU f U x) := by
  rw [res_pullU_eq, res_pullU_eq]
  ext
  change (X.presheaf.map (homOfLE h').op ≫ f.appLE U' V h).hom x = _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem exists_gen_pull (L : LB X) (f : Y ⟶ X) (i : L.ι) (hL : L.IsLB) (hi : ⊤ ≤ f ⁻¹ᵁ L.U i) :
    ∃ t : LB.Gen (L.pull f), t.IsGen := by
  have le1 : ∀ j : PUnit → L.ι, LB.wchart L (fun _ : PUnit => f) j ≤ f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U i) :=
    fun j => le_inf (LB.wchart_le L (fun _ : PUnit => f) j PUnit.unit) (le_top.trans hi)
  refine ⟨⟨fun j => res (le1 j) (pullU f _ (L.g (j PUnit.unit) i))⟩, fun j k => ?_⟩
  have le2 : LB.wchart L (fun _ : PUnit => f) j ⊓ LB.wchart L (fun _ : PUnit => f) k ≤
      f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (k PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => f) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => f) k PUnit.unit))
  have le3 : LB.wchart L (fun _ : PUnit => f) j ⊓ LB.wchart L (fun _ : PUnit => f) k ≤
      f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (k PUnit.unit) ⊓ L.U i) :=
    le_inf le2 (le_top.trans hi)
  have gg : (L.pull f).g j k = res le2 (pullU f _ (L.g (j PUnit.unit) (k PUnit.unit))) :=
    (Fintype.prod_unique (fun _ : PUnit =>
      (res le2 (pullU f _ (L.g (j PUnit.unit) (k PUnit.unit)))) ^ (1 : ℤ))).trans (zpow_one _)
  have c := congrArg (fun x => res le3 (pullU f _ x)) (hL.cocycle (j PUnit.unit) (k PUnit.unit) i)
  simp only [map_mul] at c
  rw [res_pullU_res f _ _ _ le3 _ le2, res_pullU_res f _ _ _ le3 _ (inf_le_right.trans (le1 k)),
    res_pullU_res f _ _ _ le3 _ (inf_le_left.trans (le1 j))] at c
  rw [gg]
  exact (res_res_pullU f _ _ _ (le1 j) inf_le_left _).trans
    (c.symm.trans (congrArg _ (res_res_pullU f _ _ _ (le1 k) inf_le_right _).symm))

end GlobalTheory.ChartRig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveFst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

noncomputable section

namespace GlobalTheory.WeierstrassLie

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

theorem equation_inr (c : R) : (W.map (algebraMap R (DualNumber R))).toProjective.Equation
    ![TrivSqZeroExt.inr c, -1, 0] := by
  rw [equation_origin_iff]
  simp [pow_succ, TrivSqZeroExt.inr_mul_inr]

def vec (c : R) : Spec (.of (DualNumber R)) ⟶ scheme W :=
  ptHom W (algebraMap R (DualNumber R)) ![TrivSqZeroExt.inr c, -1, 0]
    (isUnimodularSol_origin (equation_inr W c))

theorem scale_vec (c : R) : spMap (epsScaleR c) ≫ vec W 1 = vec W c := by
  refine (SpecMap_ptHom W _ _ _ (epsScaleR c)).trans (ptHom_congr W _ _ _ ?_ ?_ _)
  · ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext1 j
    fin_cases j
    · ext <;> simp [epsScaleR]
    · simp
    · simp

theorem vec_inj {c d : R} (e : vec W c = vec W d) : c = d := by
  rw [vec, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W c),
    ← SpecMap_originEval_chartY W _ _ _ (equation_inr W d), cancel_mono] at e
  have e' : originEval W _ _ _ (equation_inr W c) = originEval W _ _ _ (equation_inr W d) :=
    congrArg (·.hom) (Spec.map_injective e)
  have := RingHom.congr_fun e' (originZ W)
  rw [originEval_originZ, originEval_originZ] at this
  simpa using congrArg TrivSqZeroExt.snd this

theorem fst_vec (c : R) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ vec W c = zero W := by
  refine (SpecMap_ptHom W _ _ _ (TrivSqZeroExt.fstHom R R R).toRingHom).trans ?_
  rw [zero, ← pt_smul W (A := R) _ _ isUnit_one.neg]
  refine ptHom_congr W _ _ _ ?_ ?_ _
  · ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
  · ext1 j
    fin_cases j <;> simp

theorem surjective_fst :
    Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  intro p
  refine ⟨PrimeSpectrum.comap (algebraMap R (DualNumber R)) p, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change algebraMap R (DualNumber R) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal
  have h : (TrivSqZeroExt.inr a.snd : DualNumber R) ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact zero_mem _)
  conv_rhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a]
  exact (Ideal.add_mem_iff_left _ h).symm

theorem exists_eq_vec (g : Spec (.of (DualNumber R)) ⟶ scheme W)
    (hg : g ≫ toSpec W = spMap (algebraMap R (DualNumber R)))
    (h0 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g = zero W) : ∃ c, g = vec W c := by
  have hr : Set.range g ⊆ Set.range (chartY W) := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := surjective_fst p
    rw [← Scheme.Hom.coe_opensRange, opensRange_chartY]
    have : q ∈ zero W ⁻¹ᵁ coordOpen W 1 := by
      rw [zero_preimage_coordOpen_one]; trivial
    rw [← h0] at this
    exact this
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift _ _ hr)
  have hl : Spec.map φ ≫ chartY W = g := hφ ▸ IsOpenImmersion.lift_fac _ _ hr
  have hc : φ.hom.comp (algebraMap R (OriginRing W)) = algebraMap R (DualNumber R) := by
    rw [← hl, Category.assoc, chartY_toSpec, ← Spec.map_comp] at hg
    exact congrArg (·.hom) (Spec.map_injective hg)
  have ha : (TrivSqZeroExt.fstHom R R R).toRingHom.comp φ.hom =
      (originAug W : OriginRing W →+* R) := by
    rw [← hl, ← SpecMap_originAug_chartY, ← Category.assoc, cancel_mono] at h0
    exact congrArg (·.hom) (Spec.map_injective ((Spec.map_comp _ _).trans h0))
  have hz : (φ.hom (originZ W)).fst = 0 := (RingHom.congr_fun ha _).trans (originAug_originZ W)
  have hw : (φ.hom (originW W)).fst = 0 := (RingHom.congr_fun ha _).trans (originAug_originW W)
  have hw0 : φ.hom (originW W) = 0 := by
    have e := congrArg φ.hom ((equation_origin_iff _ _ _).mp (equation_originZ_originW W))
    simp only [map_add (f := _), map_mul, map_pow] at e
    ext
    · exact hw
    · rw [e]
      simp [pow_succ, hz, hw]
  have hz0 : φ.hom (originZ W) = TrivSqZeroExt.inr (φ.hom (originZ W)).snd := by
    ext <;> simp [hz]
  refine ⟨(φ.hom (originZ W)).snd, ?_⟩
  rw [← hl, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W _)]
  congr 2
  ext1
  refine origin_hom_ext W (fun r => ?_) ?_ ?_
  · exact (RingHom.congr_fun hc r).trans (originEval_algebraMap W _ _ _ (equation_inr W _) r).symm
  · exact hz0.trans (originEval_originZ W _ _ _ (equation_inr W _)).symm
  · exact hw0.trans (originEval_originW W _ _ _ (equation_inr W _)).symm

theorem isLieBasis_eps : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R)
    [GrpObj (schemeOver W)], η[schemeOver W].left = zero W → ∃ v : epsR R ⟶ schemeOver W,
      (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
        v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
      IsLieBasis ![v] := by
  intro R _ W _ hη
  let v : epsR R ⟶ schemeOver W := Over.homMk (vec W 1) (ptHom_toSpec ..)
  have key : ∀ (c : Fin 1 → R) (w : epsR R ⟶ schemeOver W),
      IsLieComb c ![v] w ↔ w.left = vec W (c 0) := by
    intro c w
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : (List.ofFn u).prod = u 0 := by simp
      rw [this]
      exact (hu 0).trans (scale_vec W _)
    · intro h
      refine ⟨fun _ => w, fun i => ?_, by simp⟩
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact h.trans (scale_vec W _).symm
  refine ⟨v, ⟨isUnimodularSol_origin (equation_inr W 1), rfl⟩, fun i => ?_, fun w hw => ?_⟩
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    exact (fst_vec W 1).trans hη.symm
  · obtain ⟨c, hc⟩ := exists_eq_vec W w.left (Over.w w) (hw.trans hη)
    refine ⟨fun _ => c, (key _ _).mpr hc, fun d hd => ?_⟩
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact vec_inj W (((key _ _).mp hd).symm.trans hc)

end GlobalTheory.WeierstrassLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.VolumeFundamentalDomainStdRealBasis
section
noncomputable section

open MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder

namespace GlobalTheory.UnimodVol

def stdRealBasis (g : ℕ) : Module.Basis (Σ _ : Fin g, Fin 2) ℝ (Fin g → ℂ) :=
  Pi.basis fun _ => Complex.basisOneI

theorem volume_fundamentalDomain_stdRealBasis (g : ℕ) :
    volume (ZSpan.fundamentalDomain (stdRealBasis g)) = 1 := by
  have h : ZSpan.fundamentalDomain (stdRealBasis g) =
      Set.pi Set.univ fun _ : Fin g =>
        Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    simp [ZSpan.fundamentalDomain, stdRealBasis, Pi.basis_repr, Sigma.forall, Fin.forall_fin_two]
  rw [h, volume_pi_pi]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  simp [Measure.volume_eq_prod]

theorem re_dotProduct_star {g : ℕ} (z w : Fin g → ℂ) :
    (z ⬝ᵥ star w).re = ∑ k, (stdRealBasis g).repr z k * (stdRealBasis g).repr w k := by
  simp [stdRealBasis, Pi.basis_repr, Fintype.sum_sigma, Fin.sum_univ_two, dotProduct]

theorem im_hermForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    (hermForm Hm z w).im = (z ⬝ᵥ star ((Complex.I • Hm.map star) *ᵥ w)).re := by
  have : star ((Complex.I • Hm.map star) *ᵥ w) = (-Complex.I) • Hm *ᵥ star w := by
    ext k
    simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [this, dotProduct_smul, hermForm]
  simp

theorem det_gram_im {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (v : (Σ _ : Fin g, Fin 2) → Fin g → ℂ) :
    (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im).det =
      ((stdRealBasis g).det v) ^ 2 * ‖Hm.det‖ ^ 2 := by
  set T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    (Matrix.toLin' (Complex.I • Hm.map star)).restrictScalars ℝ with hT
  have h : (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im) =
      ((stdRealBasis g).toMatrix v)ᵀ * (stdRealBasis g).toMatrix (T ∘ v) := by
    ext i j
    rw [Matrix.of_apply, im_hermForm, re_dotProduct_star, Matrix.mul_apply]
    rfl
  have hd : LinearMap.det T = ‖Hm.det‖ ^ 2 := by
    have : (Hm.map star).det = star Hm.det := ((starRingEnd ℂ).map_det Hm).symm
    rw [hT, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, Matrix.det_smul, this]
    simp
  rw [h, Matrix.det_mul, Matrix.det_transpose, ← Module.Basis.det_apply, ← Module.Basis.det_apply,
    Module.Basis.det_comp, hd]
  ring

theorem posDef_of_hermForm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) : Hm.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h1 := hpos (star x) (by simpa using hx)
  have h2 := hH.im_star_dotProduct_mulVec_self x
  rw [hermForm, star_star] at h1
  exact Complex.pos_iff.2 ⟨h1, h2.symm⟩

theorem det_re_pos {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    0 < Hm.det.re ∧ ‖Hm.det‖ = Hm.det.re := by
  have h := (posDef_of_hermForm hH hpos).det_pos
  exact ⟨(Complex.pos_iff.1 h).1, (Complex.re_eq_norm.2 h.le).symm⟩

end GlobalTheory.UnimodVol

namespace GlobalTheory

open UnimodVol

theorem volume_mul_det_eq_one_of_unimodular (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ))
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef)
    (hFd : IsAddFundamentalDomain Λ Fd volume) : (volume Fd).toReal * Hm.det.re = 1 := by
  have : IsZLattice ℝ Λ := ⟨hfull⟩
  let b₁ := Module.Free.chooseBasis ℤ Λ
  let b := b₁.reindex ((b₁.ofZLatticeBasis ℝ Λ).indexEquiv (stdRealBasis g))
  have hvol : (volume Fd).toReal = |(stdRealBasis g).det (Subtype.val ∘ b)| := by
    have h1 := ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hFd
    rw [ZLattice.covolume_eq_det_mul_measureReal Λ volume b (stdRealBasis g), Measure.real,
      volume_fundamentalDomain_stdRealBasis] at h1
    simpa [Measure.real] using h1.symm
  have hu := LinearEquiv.isUnit_det (LinearEquiv.ofBijective Ef hbij) b b.dualBasis
  set M := LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective Ef hbij : Λ →ₗ[ℤ] Module.Dual ℤ Λ)
    with hM
  have hG : (Matrix.of fun i j => (hermForm Hm ((Subtype.val ∘ b) i) ((Subtype.val ∘ b) j)).im) =
      ((Int.castRingHom ℝ).mapMatrix M)ᵀ := by
    ext i j
    simp [hM, LinearMap.toMatrix_apply, hE]
  have hdet := det_gram_im Hm (Subtype.val ∘ b)
  rw [hG, Matrix.det_transpose, ← RingHom.map_det] at hdet
  obtain ⟨hp, hn⟩ := det_re_pos hH hpos
  have habs : |((M.det : ℤ) : ℝ)| = 1 := by
    rcases Int.isUnit_iff.1 hu with h | h <;> simp [h]
  rw [hn, eq_intCast] at hdet
  rw [hdet, ← mul_pow, abs_of_nonneg (sq_nonneg _), ← sq_abs, abs_mul, abs_of_pos hp,
    pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero] at habs
  rw [hvol, habs]

end GlobalTheory
end
end

