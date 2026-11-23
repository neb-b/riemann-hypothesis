module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxMaps
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapIntegrabilityStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBes_bessel_integral_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ ξ : Wp, IsBes R z π (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ) := by
  first | exact @GlobalTheory.be_apply_isBes | exact GlobalTheory.be_apply_isBes | (intros; apply GlobalTheory.be_apply_isBes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingGapDecay
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselOrbital

theorem bessel_integral_eq_smul : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∃ OO : Mx k r → (Wq →L[ℂ] Wp), ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z', Integrable (JF.integrand D F γ) D.μSS ∧ B.JF D F γ = s • OO γ := by
  classical
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hok hl hl'
  have hpt : ∀ γ ∈ JF.Om k r D.z D.z', ∃ O : Wq →L[ℂ] Wp, ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ X : Wq →L[ℂ] Wp,
      B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ = ⟪l x, X (l' y)⟫_ℂ • O := by
    intro γ hγ
    obtain ⟨A, hA1, hA2⟩ := GlobalTheory.T.bessel_orbital_integral_factors_through_left_functional hH k r ε mu h R Wp Wq D l l' hDS hgap hok hl hl' γ hγ
    obtain ⟨Bb, hB1, hB2⟩ := GlobalTheory.T.bessel_orbital_integral_factors_through_right_functional hH k r ε mu h R Wp Wq D l l' hDS hgap hok hl hl' γ hγ
    obtain ⟨O, hO⟩ := _root_.GlobalTheory.factorisation_of_two_partial_integrations R.TK Wp Wq (fun x => l x) (fun y => l' y)
      (fun x y X => B.JF D (fun g => ⟪(x : R.H), R.σ g y⟫_ℂ • X) γ)
      (fun y => A y) (fun x => Bb x) (fun y => hA1 y) (fun x => hB1 x)
      (fun x y X c => hA2 x x.2 y y.2 X c) (fun x y X c => hB2 x x.2 y y.2 X c)
    exact ⟨O, fun x hx y hy X => hO ⟨x, hx⟩ ⟨y, hy⟩ X⟩
  choose! OO hOO using hpt
  have hint : ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z',
      Integrable (JF.integrand D F γ) D.μSS := by
    intro F s hF γ hγ
    exact (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ F (_root_.GlobalTheory.thresholds_of_gapOK k r h hok).1
      ((GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH k r ε mu h R Wp Wq l l' F s hDS hgap hok hF).2 0)).1 γ hγ
  refine ⟨OO, fun F s hF γ hγ => ⟨hint F s hF γ hγ, ?_⟩⟩
  obtain ⟨m, x, y, X, hxy, hFe, hs⟩ := hF
  have hγG : γ ∈ GG k r := hγ.1
  obtain ⟨hloc, -, hsum, -⟩ := GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum k r Wp Wq D γ hγG
  rw [(hloc F (fun g => ∑ i, ⟪x i, R.σ g (y i)⟫_ℂ • X i) hFe).1,
    hsum (Fin m) (fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i) ?_, hs, Finset.sum_smul]
  · exact Finset.sum_congr rfl fun i _ => hOO γ hγ _ (hxy i).1 _ (hxy i).2 _
  · intro i
    refine hint _ ⟪l (x i), X i (l' (y i))⟫_ℂ ⟨1, fun _ => x i, fun _ => y i, fun _ => X i,
      fun _ => hxy i, fun g _ => ?_, ?_⟩ γ hγ
    · simp
    · simp

end GlobalTheory.BesselOrbital
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralExpansion

section General

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ₁ : K → (Y' ⟶ X)}
  {ε₁ : K → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K' → (Y ⟶ X)} {ε₂ : K' → ℤ}

theorem sval_of_secScal {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have e := congrArg (gs r z _) (H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e))
  exact ((gs_res r z _ hm _).trans (gs_pull r h z
    (LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k))) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm.2 k) _)).symm.trans
    (e.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _))))

theorem secIsMul_of_secScal (hL : L.IsLB) {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) {a : R}
    {s s' : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} (hinj : ∀ W : Y.Opens, Function.Injective (h.app W))
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s h 1) (H' : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s' h (scal (h ≫ p) a)) :
    SecIsMul p a s' s := by
  intro j
  refine hinj _ (fn_ext fun y hy => ?_)
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
  have hJ' : Good L y J := hJ
  have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ₂ j := hy
  have m := hJ'.mem φ₂ (𝟙 Y' ≫ h)
  have e₁ := sval_scal H (𝟙 Y') y hJ'
  have e₂ := sval_of_secScal H' (𝟙 Y') y hJ'
  have e₃ : gs (𝟙 Y' ≫ h) y (LB.wchart L φ₂ j) (Out.resTop _ (scal p a)) = gs (𝟙 Y') y ⊤ (scal (h ≫ p) a) :=
    ((gs_res _ y le_top hy' _).trans (gs_pull _ p y ⊤ trivial _)).trans
      (((gs_pull _ (h ≫ p) y ⊤ trivial _).trans (by rw [Category.assoc])).symm)
  refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
  refine (sec_trans s' _ y hy' m).trans (Eq.trans ?_ ((gs_mul _ y _ hy' _ _).trans
    (congrArg₂ (· * ·) e₃ (sec_trans s _ y hy' m))).symm)
  exact (congrArg _ (e₂.trans (congrArg _ e₁))).trans (mul_left_comm _ _ _)

end General

theorem exists_secIsMul {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
    (a : R) (s : LB.Sec M) : ∃ s' : LB.Sec M, SecIsMul p a s' s :=
  ⟨SectionArithmetic.secCMul (V := ⊤) (fun _ => le_top) (scal p a) s, fun _ => rfl⟩

theorem SecIsMul.comp {R : Type} [CommRing R] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of R)} {M : LB Y}
    {a b : R} {s s' s'' : LB.Sec M} (h : SecIsMul p a s'' s') (h' : SecIsMul p b s' s) :
    SecIsMul p (a * b) s'' s := fun j => by
  rw [h j, h' j, ← _root_.mul_assoc]
  simp only [Out.resTop, scal, map_mul]

theorem prB_app_injective {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (W : D.P.A.left.Opens) :
    Function.Injective ((DegPre.prB D (FractionRing V)).left.app W) := by
  have := D.P.isAb.smooth
  have : Flat D.P.A.hom := inferInstance
  have e : (TF (R := V) (FractionRing V)).hom = jK V := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  have h := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  have : IsSchemeTheoreticallyDominant (TF (R := V) (FractionRing V)).hom := by rw [e]; exact h.2
  have : QuasiCompact (TF (R := V) (FractionRing V)).hom := by rw [e]; exact h.1
  exact (pullback.snd (TF (R := V) (FractionRing V)).hom D.P.A.hom).app_injective W

theorem exists_div_of_expandsAt {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G)
    (e k : ℕ) (σ : H0 U.LG.L k) (f f' : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hf : ∀ α, SecIsMul D.toPre.P.A.hom (ϖ ^ (e + 1)) (f' α) (f α)) (hE : U.ExpandsAt e k σ f') :
    ∃ τ : H0 U.LG.L k, SecIsMul G.hom (ϖ ^ (e + 1)) σ τ := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  refine (GlobalTheory.ThickDiv.main V ϖ hϖ G _ σ e).1 fun j => fn_ext fun y hy => ?_
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f' hE
  choose J hJ using fun ψ : (thickObj V (maximalIdeal V) e G).left ⟶ D.toPre.P.A.left =>
    exists_chart D.toPre.P.isLB (ψ y)
  have hJ' : Good D.toPre.P.L y J := hJ
  have H := (hS _ (𝟙 _) y J hJ').2 jL (Set.mem_iInter.1 hy 0)
  have hc : pGl U e ≫ D.toPre.P.A.hom = (thickObj V (maximalIdeal V) e G).hom ≫
      spMap (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))) := Over.w (U.gt e).pG
  have h0 : cst (pGl U e ≫ D.toPre.P.A.hom) y (ϖ ^ (e + 1)) = 0 := by
    rw [hc, cst_comp, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.pow_mem_pow ((mem_maximalIdeal _).2 hϖ.not_isUnit) _), cst, map_zero]
    exact gs_zero _ _ _ trivial
  have hF : ∀ α, sval (f' α) (𝟙 _ ≫ pGl U e) y J = 0 := fun α => by
    rw [Category.id_comp]
    exact (secIsMul_gs (hf α) (pGl U e) y _ (hJ'.mem _ _)).trans (by rw [h0, zero_mul])
  simp only [hF, zero_mul, Finset.sum_const_zero, Units.mul_right_eq_zero] at H
  exact (gs_pull (𝟙 _) _ y _ hy _).trans (H.trans (gs_zero (𝟙 _) y _ hy).symm)

theorem main : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (q : ℕ), 1 ≤ q → ∀ (Φ : Fam D.toPre (FractionRing V) q) (f : ∀ α, D.toPre.SecB q α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α) (D.toPre.famφB α) (DegPre.famε q) (f α) (DegPre.prB D.toPre (FractionRing V)).left 1) → ∃ σ : H0 U.LG.L q, ∀ e : ℕ, U.ExpandsAt e q σ f := by
  intro _ V _ _ _ D A G _ _ U q hq Φ f hf
  obtain ⟨s, ⟨r, hr, σ₁, f₁, -, hf₁, hE₁⟩, -⟩ := (U.expand q hq).2 Φ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hr hϖ
  have h₁ : ∀ α, SecIsMul D.toPre.P.A.hom r (f₁ α) (f α) := fun α =>
    secIsMul_of_secScal D.toPre.P.isLB _ (prB_app_injective D.toPre) (hf α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing V))]; exact hf₁ α)
  obtain ⟨σ₂, hσ₂⟩ := exists_secIsMul G.hom (u : V) σ₁
  choose f₂ hf₂ using fun α => exists_secIsMul D.toPre.P.A.hom (u : V) (f₁ α)
  have hE₂ : ∀ e, U.ExpandsAt e q σ₂ f₂ := fun e =>
    expandsAt_secIsMul V _ D A G U.toUnifPre e q u σ₁ σ₂ f₁ f₂ hσ₂ hf₂ (hE₁ e)
  have h₂ : ∀ α, SecIsMul D.toPre.P.A.hom (ϖ ^ n) (f₂ α) (f α) := fun α => by
    rw [← hu, mul_comm]; exact SecIsMul.comp (hf₂ α) (h₁ α)
  obtain ⟨σ, hσ⟩ : ∃ σ : H0 U.LG.L q, SecIsMul G.hom (ϖ ^ n) σ₂ σ := by
    cases n with
    | zero => exact ⟨σ₂, fun j => by rw [pow_zero, scal, map_one, map_one, Out.resTop, map_one, _root_.one_mul]⟩
    | succ m => exact exists_div_of_expandsAt hϖ U.toUnifPre m q σ₂ f f₂ h₂ (hE₂ m)
  exact ⟨σ, fun e => expandsAt_cancel_pow V ϖ hϖ D A G U.toUnifPre e n q σ σ₂ f f₂ hσ h₂ (hE₂ (e + n))⟩

end GlobalTheory.IntegralExpansion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsBoxQkToA
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnboxQk

open GlobalTheory.BoxFamily GlobalTheory.BoxQk GlobalTheory.TorusExt

section Deg

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D' D : DegPre R} (pD : IsPowDeg D' D j)
  {F : Type} [Field F] [Algebra (FractionRing R) F]

def intersection_update_fsHerm_neg_one (i : Fin j) (χ : D.X) : D'.X := pD.xe.symm (Pi.single i χ)

theorem xe_position (i : Fin j) (χ : D.X) : pD.xe (intersection_update_fsHerm_neg_one pD i χ) = Pi.single i χ := pD.xe.apply_symm_apply _

theorem xe_position_self (i : Fin j) (χ : D.X) : pD.xe (intersection_update_fsHerm_neg_one pD i χ) i = χ := by
  rw [xe_position, Pi.single_eq_same]

theorem xe_position_ne {i i' : Fin j} (h : i' ≠ i) (χ : D.X) : pD.xe (intersection_update_fsHerm_neg_one pD i χ) i' = 0 := by
  rw [xe_position, Pi.single_eq_of_ne h]

theorem position_add (i : Fin j) (χ χ' : D.X) : intersection_update_fsHerm_neg_one pD i (χ + χ') = intersection_update_fsHerm_neg_one pD i χ + intersection_update_fsHerm_neg_one pD i χ' := by
  rw [intersection_update_fsHerm_neg_one, Pi.single_add, map_add (f := _)]; rfl

theorem position_zero (i : Fin j) : intersection_update_fsHerm_neg_one pD i 0 = 0 := by
  rw [intersection_update_fsHerm_neg_one, Pi.single_zero, map_zero]

theorem sum_position (x : D'.X) : ∑ i, intersection_update_fsHerm_neg_one pD i (pD.xe x i) = x := by
  apply pD.xe.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [xe_position]
  exact Finset.univ_sum_single _

theorem exists_gt_at {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J) (b : TF (R := R) F ⟶ D.P.A)
    (f : D.X → ((TF (R := R) F).left.presheaf.stalk y)ˣ) (f₀ : f 0 = 1)
    (hf : ∀ χ χ', f (χ + χ') * th D y J (cP D _ χ) (cP D _ χ') b = f χ * f χ') :
    ∃ g : GtPtF D F, g.b = b ∧ ∀ χ, charVal g χ y J = f χ := by
  choose v hv vv using fun χ => exists_gen_val (F := F) D.P.isLB (DegPre.gtφ D F b χ) DegPre.gtε hJ (f χ)
  refine (exists_gt b v hv (fun _ _ _ _ => rfl) (fun y' J' hJ' => ?_) (fun χ χ' y' J' hJ' => ?_)).imp
    fun _ h => ⟨h.1, fun χ => (h.2 χ y J hJ).trans (vv χ)⟩
  · obtain rfl := pt_eq y y'
    refine (val_eq_of_val_eq (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => ?_) (hv 0) oneGen_isGen hJ hJ'
      ((vv 0).trans (f₀.trans (val_one _).symm))).trans (val_one _)
    rw [prod_gt, cPoint_zero, _root_.one_mul]; simp
  · obtain rfl := pt_eq y y'
    refine ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ' _ _ _))).symm.trans
      (Eq.trans (val_eq_of_val_eq (fun U _ h => ?_) (mulGen_isGen _ _ _ _ _ _ _ (hv _) (cubAt_isGen _ _ _))
        (mulGen_isGen _ _ _ _ _ _ _ (hv χ) (hv χ')) hJ hJ'
        (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vv _) (val_cubAt hJ _ _ _))).trans ((hf χ χ').trans
          ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vv _) (vv _))).symm))) (val_mul hJ' _ _ _))
    refine (prod_sum₂ (K := Fin 4) (K' := thK) (U := U) _ (prod_gt b (χ + χ') h)
      (prod_cub (cP D _ χ) (cP D _ χ') b h)).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gt b χ h) (prod_gt b χ' h)).symm)
    rw [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

section Values

variable {y : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}
  {J' : ((TF (R := R) F).left ⟶ D'.P.A.left) → D'.P.L.ι} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
include hJ

theorem prod_th_factor (i : Fin j) (χ : D.X) (x w : TF (R := R) F ⟶ D'.P.A) :
    ∏ i', th D y J (cP D' _ (intersection_update_fsHerm_neg_one pD i χ) ≫ pD.pw.pr i') (x ≫ pD.pw.pr i') (w ≫ pD.pw.pr i') =
      th D y J (cP D _ χ) (x ≫ pD.pw.pr i) (w ≫ pD.pw.pr i) := by
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [Finset.prod_eq_single i (fun i' _ h => by rw [cPoint_pr, xe_position_ne pD h, cPoint_zero, C.face]) (by simp),
    cPoint_pr, xe_position_self]

include hJ'

theorem position_val {g' : GtPtF D' F} {g : Fin j → GtPtF D F} (h : IsBoxGtF pD F g' g) (i : Fin j) (χ : D.X) :
    omL pD y J J' (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) g'.b * charVal g' (intersection_update_fsHerm_neg_one pD i χ) y J' = charVal (g i) χ y J := by
  have e₂ : ∏ i', charVal (g i') (pD.xe (intersection_update_fsHerm_neg_one pD i χ) i') y J = charVal (g i) χ y J := by
    rw [Finset.prod_eq_single i (fun i' _ h => by rw [xe_position_ne pD h, charVal_zero _ hJ]) (by simp), xe_position_self]
  exact (box_val pD hJ hJ' h (intersection_update_fsHerm_neg_one pD i χ)).trans e₂

theorem tau_position (hB : D.TauBimult) (i : Fin j) (χ : D.X) (z : D'.X) :
    omL pD y J J' (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) (cP D' _ z) * tauVal D' F z (intersection_update_fsHerm_neg_one pD i χ) y J' =
      tauVal D F (pD.xe z i) χ y J := by
  have e₂ : ∏ i', tauVal D F (pD.xe z i') (pD.xe (intersection_update_fsHerm_neg_one pD i χ) i') y J = tauVal D F (pD.xe z i) χ y J := by
    rw [Finset.prod_eq_single i (fun i' _ h => ?_) (by simp), xe_position_self]
    have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 (pD.xe z i')
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    rw [xe_position_ne pD h]
    exact (tau_symm (𝟙 (TF (R := R) F)) hJ _ _).trans (mul_eq_left.1 t.symm)
  exact (tau_box pD hJ hJ' z (intersection_update_fsHerm_neg_one pD i χ)).trans e₂

theorem exists_comp (hG : GlobalFnsSt) (g' : GtPtF D' F) (i : Fin j) :
    ∃ g : GtPtF D F, g.b = g'.b ≫ pD.pw.pr i ∧ ∀ χ, charVal g χ y J =
      omL pD y J J' (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) g'.b * charVal g' (intersection_update_fsHerm_neg_one pD i χ) y J' := by
  refine exists_gt_at hJ _ _ ?_ fun χ χ' => ?_
  · rw [position_zero, cPoint_zero, omL_one', charVal_zero g' hJ', _root_.one_mul]
  · have e := th_box pD hJ hJ' hG (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) (cP D' _ (intersection_update_fsHerm_neg_one pD i χ')) g'.b
    rw [prod_th_factor pD hJ, cPoint_pr, xe_position_self, ← cPoint_add, ← position_add] at e
    have e₂ := charVal_add g' hJ' (intersection_update_fsHerm_neg_one pD i χ) (intersection_update_fsHerm_neg_one pD i χ')
    rw [← position_add] at e₂
    have a₁ := congrArg Additive.ofMul e
    have a₂ := congrArg Additive.ofMul e₂
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₂ - a₁

end Values

theorem exists_unboxGt (hG : GlobalFnsSt) (g' : GtPtF D' F) : ∃ g : Fin j → GtPtF D F, IsBoxGtF pD F g' g := by
  obtain ⟨y, J, hJ⟩ := exists_good_chart D F
  obtain ⟨J', hJ'⟩ := exists_good_at D'.P.isLB y
  choose g hb hv using exists_comp pD hJ hJ' hG g'
  obtain ⟨g'', h⟩ := exists_boxGt pD hG g
  have eb : g''.b = g'.b := pt_ext pD fun i => (h.1 i).trans (hb i)
  have add : ∀ a b, charVal g'' a y J' = charVal g' a y J' → charVal g'' b y J' = charVal g' b y J' →
      charVal g'' (a + b) y J' = charVal g' (a + b) y J' := fun a b ha hb => by
    have e₁ := charVal_add g'' hJ' a b
    rw [eb, ha, hb, ← charVal_add g' hJ' a b] at e₁
    exact mul_right_cancel e₁
  have all : ∀ x, charVal g'' x y J' = charVal g' x y J' := fun x => by
    rw [← sum_position pD x]
    refine Finset.sum_induction _ (fun x => charVal g'' x y J' = charVal g' x y J') add
      ((charVal_zero g'' hJ').trans (charVal_zero g' hJ').symm) fun i _ => ?_
    have e := (position_val pD hJ hJ' h i (pD.xe x i)).trans (hv i _)
    rw [eb] at e
    exact mul_left_cancel e
  obtain rfl : g'' = g' := gt_ext_val_at eb hJ' all
  exact ⟨g, h⟩

theorem unbox_isZero {g' : GtPtF D' F} {g : Fin j → GtPtF D F} (h : IsBoxGtF pD F g' g) (hz : g'.IsZero)
    (i : Fin j) : (g i).IsZero := by
  haveI := pD.pw.hom i
  obtain ⟨b, v⟩ := (isZero_iff_val _).1 hz
  refine (isZero_iff_val _).2 ⟨by rw [← h.1, b, MonObj.one_comp], fun χ y J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_at D'.P.isLB y
  rw [← position_val pD hJ hJ' h, v _ y J' hJ', b, omL_one, _root_.mul_one]

theorem unbox_isAdd (hG : GlobalFnsSt) {g₁' g₂' g₃' : GtPtF D' F} {g₁ g₂ g₃ : Fin j → GtPtF D F}
    (h₁ : IsBoxGtF pD F g₁' g₁) (h₂ : IsBoxGtF pD F g₂' g₂) (h₃ : IsBoxGtF pD F g₃' g₃)
    (ha : g₁'.IsAdd g₂' g₃') (i : Fin j) : (g₁ i).IsAdd (g₂ i) (g₃ i) := by
  haveI := pD.pw.hom i
  obtain ⟨b, v⟩ := (isAdd_iff_val _ _ _).1 ha
  refine (isAdd_iff_val _ _ _).2 ⟨by rw [← h₃.1, ← h₁.1, ← h₂.1, b, MonObj.mul_comp], fun χ y J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_at D'.P.isLB y
  have e := th_box' pD hJ hJ' hG (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) g₁'.b g₂'.b
  rw [prod_th_factor pD hJ, ← b, h₁.1, h₂.1] at e
  rw [← position_val pD hJ hJ' h₁, ← position_val pD hJ hJ' h₂, ← position_val pD hJ hJ' h₃]
  have a₁ := congrArg Additive.ofMul e
  have a₂ := congrArg Additive.ofMul (v (intersection_update_fsHerm_neg_one pD i χ) y J' hJ')
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₂ - a₁

theorem unbox_isIota (hB : D.TauBimult) {g' : GtPtF D' F} {g : Fin j → GtPtF D F} (h : IsBoxGtF pD F g' g)
    {x : D'.X} (hι : GtPtF.IsIota x g') (i : Fin j) : GtPtF.IsIota (pD.xe x i) (g i) := by
  obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 hι
  refine (isIota_iff_val _ _).2 ⟨by rw [← h.1, b, cPoint_pr], fun χ y J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_at D'.P.isLB y
  rw [← position_val pD hJ hJ' h, v _ y J' hJ', b]
  exact tau_position pD hJ hJ' hB i χ x

theorem exists_unbox (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (p' : QkPt D' F k) :
    ∃ p : Fin j → QkPt D F k, IsBoxQk pD F k p' p := by
  choose ub hub using fun g' : GtPtF D' F => exists_unboxGt pD hG g'
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := p'.eq
  exact ⟨fun i => ⟨pD.xe p'.y i, ub p'.g i, ub h i,
    ⟨fun n => ub (gs n) i, unbox_isZero pD (hub _) g₀ i,
      fun n => unbox_isAdd pD hG (hub _) (hub _) (hub _) (gst n) i, congrArg (fun g => ub g i) gl⟩,
    unbox_isIota pD hB (hub _) hι i⟩, rfl, hub _⟩

end Deg


open FieldBaseChange TorsionImage in
theorem image_unique (hL : Laws) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ) (hn : 1 ≤ n)
    (p : QkPt D.toPre F n) (x x' : TFK (R := R) F ⟶ A.A) (hx : QkToAkU U.toUnifPre F n p x)
    (hx' : QkToAkU U.toUnifPre F n p x') : x = x' := by
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hL.globalFns U F hn w₀ hw₀
  obtain ⟨c, hc, hcs⟩ := exists_smul_of_phiVal p w w' hw hw'
  refine pt_eq_of_proportional hL.secBaseChange A _ hn θ θ'
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))
    fun t u u' hu hu' y J hJ => ?_
  have a := hcs _ _ _
    ((DVR.phiRel_iff hL.globalFns p w hw _ _).1 (h t u _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu))
    ((DVR.phiRel_iff hL.globalFns p w' hw' _ _).1 (h' t u' _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu'))
  obtain rfl := e.injective (a.trans (e.map_smul c u).symm)
  exact (sval_smul' hJ _ c _).trans (congrArg (· * _) (gs_unit _ y ⊤ trivial
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))))

theorem exists_isBoxQk_toA : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → ∀ (j : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre j) (pA : IsPowPolAV A' P.A j) (pG : IsPowGrp G' t.G j) (U' : Unif (maximalIdeal V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (k : ℕ), 1 ≤ k → ∀ p' : QkPt D'.toPre F k, ∃ p : Fin j → QkPt P.D.toPre F k, IsBoxQk pD F k p' p ∧ ∀ x' : TFK (R := V) F ⟶ A'.A, QkToAkU U'.toUnifPre F k p' x' → ∀ i, P.ToA F k (p i) (x' ≫ pA.pr i) := by
  intro hL _ _ _ V _ _ _ _ _ E _ _ _ H t P hT j D' A' G' _ _ pD pA pG U' PU F _ _ _ k hk p'
  obtain ⟨p, hp⟩ := exists_unbox pD hL.globalFns P.D.tau_bimult p'
  refine ⟨p, hp, fun x' hx' i => ?_⟩
  obtain ⟨f, hf, -⟩ := hT F k hk
  let x'' : TFK (R := V) F ⟶ A'.A := pA.lim.lift (Fan.mk _ fun i => f (p i))
  have hx : ∀ i, x'' ≫ pA.pr i = f (p i) := fun i => pA.lim.fac (Fan.mk _ fun i => f (p i)) ⟨i⟩
  have h := ProdTorsion.qkToAk_box hL V _ j P.D D' P.A A' t.G G' pD pA pG U' P.U PU
    (expansion_bijective_over_fields hL.globalFns V _ _ _ _ P.U)
    (expansion_bijective_over_fields hL.globalFns V _ _ _ _ U') F k hk p' p hp x'' (fun i => f (p i)) hx
    (fun i => (hf _ _).2 rfl)
  rw [image_unique hL U' F k hk p' x' x'' hx' h, hx]
  exact (hf _ _).2 rfl

end GlobalTheory.UnboxQk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaFrame
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_thetaFrame : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∃ θ : Fam D.toPre F 1, NuGe D Q F v 1 θ 0 ∧ ∃ (σ : D.toPre.SecB 1 0) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F 0) (DegPre.famε 1))), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F 0) (DegPre.famε 1) σF (D.toPre.famφB 0) (DegPre.famε 1) σ (DegPre.prB D.toPre F).left 1 ∧ (∀ j, (θ.s 0).f j = σF.f j) ∧ ¬ ∃ σ' : D.toPre.SecB 1 0, ∀ j, σ.f j = constFn D.toPre.P.A.hom _ ϖ * σ'.f j := by
  intro hL _ _ _ V _ _ _ ϖ hϖ D Q hQ F _ _ v hv
  obtain ⟨b, hb⟩ := IndivisibleSection.exists_secBGenerates hL.secBaseChange V (maximalIdeal V) D
  obtain ⟨Φ, f, hf, hf0, -, -⟩ := integralFamily_of_strictMin hL V ϖ hϖ D Q hQ 1 le_rfl 0 b (fun z hz => by
    have h := QForm.Q_pos hϖ (D := D) hQ hz
    rw [QForm.Q_zero hϖ (D := D) hQ, zero_add, one_smul]
    omega)
  obtain ⟨θ, hθ⟩ := FamBaseChange.main hL.globalFns V (maximalIdeal V) D 1 Φ f hf F
  refine ⟨θ, (integralFamily_levelOne V ϖ hϖ D Q hQ F v hv θ f hθ).1, b, θ.s 0, hf0 ▸ hθ 0, fun _ => rfl, ?_⟩
  rintro ⟨σ', hσ'⟩
  have h1 : SecIsMul D.toPre.P.A.hom ϖ b σ' := hσ'
  obtain ⟨a, ha, -⟩ := hb σ'
  have h2 : SecIsMul D.toPre.P.A.hom (ϖ * a) b b := fun j => by
    refine (h1 j).trans ?_
    rw [ha j]
    simp only [scal, resTop, map_mul, _root_.mul_assoc]
  have h3 : SecIsMul D.toPre.P.A.hom 1 b b := fun j => by
    simp only [scal, resTop, map_one, _root_.one_mul]
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one a ((hb b).unique h2 h3))

end GlobalTheory
end
end

