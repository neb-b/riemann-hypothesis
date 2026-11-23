module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGrpObjSplitExtensionOfGenerators
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharBundlePrimitive
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermExistsUniqueLinear
section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof pt)
open GlobalTheory GlobalTheory.FamGerm GlobalTheory.FieldBaseChange
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamGermExist

theorem exists_linear_extension {R K F : Type} [CommRing R] [IsDomain R] [Field K] [Field F] [Algebra R K]
    [IsFractionRing R K] [Algebra K F] {M N P : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module F P] (ρ : M →ₛₗ[algebraMap R K] N) (hρ : Function.Injective ρ)
    (a : N →ₛₗ[algebraMap K F] P) (ha : IsExtension a) {κ : Type} (g : M →ₗ[R] MvPowerSeries κ R) :
    ∃ Λ : P →ₗ[F] MvPowerSeries κ F, ∀ x, Λ (a (ρ x)) =
      MvPowerSeries.map ((algebraMap K F).comp (algebraMap R K)) (g x) := by
  classical
  let T₁ := Finsupp.linearCombination F fun x : M => a (ρ x)
  let T₂ := Finsupp.linearCombination F fun x : M =>
    MvPowerSeries.map ((algebraMap K F).comp (algebraMap R K)) (g x)
  have hk : LinearMap.ker T₁ ≤ LinearMap.ker T₂ := fun c hc => by
    rw [LinearMap.mem_ker, Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
    ext mo
    refine (Module.forall_dual_apply_eq_zero_iff K _).1 fun ℓ => ?_
    obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
    obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) c.support (fun x => ℓ (c x))
    choose! m hm using hr
    have h₁ : ∑ x ∈ c.support, m x • x = 0 := hρ (by
      have := congrArg (fun z => (algebraMap R K r) • Λ z) hc
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zero, smul_zero, Finset.smul_sum] at this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zero, ← this, map_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hΛ, map_smulₛₗ, hm x hx, smul_smul, Algebra.smul_def])
    have h₂ := congrArg (fun z => algebraMap R K (MvPowerSeries.coeff mo (g z))) h₁
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, smul_eq_mul, map_mul] at h₂
    have hr0 : algebraMap R K r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.coe_ne_zero r)
    refine mul_left_cancel₀ hr0 ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_zero, ← h₂, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hm x hx, map_smul, MvPowerSeries.coeff_map, smul_eq_mul, RingHom.comp_apply, mul_comm (c x),
      ← Algebra.smul_def (A := F), map_smul, Algebra.smul_def (r : R) (ℓ (c x)), smul_eq_mul]
    ring
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend
    ((LinearMap.ker T₁).liftQ T₂ hk ∘ₗ T₁.quotKerEquivRange.symm.toLinearMap)
  refine ⟨Λ, fun x => ?_⟩
  have e := LinearMap.congr_fun hΛ ⟨T₁ (Finsupp.single x 1), LinearMap.mem_range_self _ _⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply] at e
  simpa only [T₁, T₂, Finsupp.linearCombination_single, one_smul] using e

theorem exists_serHom (halg : JetSer.JetAlgSt) (hrep : JetSer.RepSt) (hser : JetSer.SerSt) (hex : JetSer.SerExSt)
    {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : JetSer.Fam G (Fin d)}
    (hx : Chart.IsUnivChart G d x) {U : G.left.Opens} (hU : ⊤ ≤ η[G].left ⁻¹ᵁ U) :
    ∃ τ : FnOver G.hom U →ₐ[R] PS R 1 d, ∀ f g, JetSer.IsSer1 x U f g ↔ g = τ f := by
  obtain ⟨h1, -, h3, -⟩ := hrep R G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := h1 (pt R (n := 1) d 0) (TB.WickVanishing.gp_pt 0)
  have hc := (h3 _ y hy).1
  have e : ∀ r : PS R 1 d, ev (n := 1) ![pt R (n := 1) d 0] r = r := fun r => by
    have : (![pt R d 0] : Fin 1 → Germ.Pt R 1 d) = fun j => pt R d j := by
      funext j; fin_cases j; rfl
    rw [this]
    unfold ev
    exact congrFun MvPowerSeries.subst_self r
  have hs : ∀ f g, JetSer.IsSer1 x U f g → JetSer.HasSer (fun m => (y m).left) U f g := fun f g h => by
    have := h 1 _ y hy
    rwa [e] at this
  have ex := (hex R G d x hx).1 U hU
  have hm : ∀ m, ⊤ ≤ (y m).left ⁻¹ᵁ U := fun m => (hs _ _ (ex 0).exists.choose_spec m).1
  obtain ⟨⟨τ, hτ⟩, -⟩ := hser R (Fin 1 × Fin d) G.left (fun m => (y m).left)
    (fun m => by rw [← Over.comp_left, hc m]) U (hm 0)
  refine ⟨⟨τ, fun c => Eq.symm ((hτ _ _).1 fun m => ⟨hm m, ?_⟩)⟩, fun f g => ⟨fun h => (hτ f g).1 (hs f g h), ?_⟩⟩
  · obtain ⟨t, ht, -⟩ := (halg R (Fin 1 × Fin d)).1 m
    rw [← ht, AlgHom.commutes]
    have h₁ := (JetSer.fnVal_comp (y m).left G.hom U ⊤ le_top (hm m)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)).2
    refine Eq.trans (Eq.symm h₁) ?_
    rw [Over.w (y m)]
    have h₂ := JetSer.fnVal_specMap (algebraMap R (Chart.JetR R (Fin 1 × Fin d) m)) (𝟙 _) ⊤ le_top
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
    rw [Category.comp_id] at h₂
    refine h₂.trans (congrArg _ ?_)
    rw [JetSer.fnVal_eq_fnValHom _ _ le_top]
    simp [JetSer.fnValHom, Scheme.Hom.appLE]
  · rintro rfl
    obtain ⟨g, hg⟩ := (ex f).exists
    exact (hτ f g).1 (hs f g hg) ▸ hg

section Group

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem genericSec_injective (k : ℕ) : Function.Injective (genericSec U k) := by
  have := U.smooth
  intro a b h
  refine SecOver.ext _ _ fun j => ExpInt.generic_app_injective G _ (fn_ext fun y hy => ?_)
  have hy' := (wchart_eq (L := U.LG.L) (φ := fun _ : Fin 1 => 𝟙 G.left) (p := pullback.fst G.hom (jK R))
    (φ' := fun _ => pullback.fst G.hom (jK R)) (fun _ => (Category.comp_id _).symm) j).ge hy
  have e := congrArg (fun s : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R))
    (fun _ => (k : ℤ))) => gs (𝟙 _) y _ (s.f j)) h
  exact (gs_res (𝟙 _) y _ hy' _).symm.trans (e.trans (gs_res (𝟙 _) y _ hy' _))

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem expandsG_sum {k n : ℕ} (c : Fin n → F) (σ : Fin n → IntSec U k) (f : Fin n → ∀ α, D.toPre.SecB k α)
    {s : Fam D.toPre F k} (h₁ : ∀ i e, U.ExpandsAt e k (σ i) (f i))
    (h₂ : ∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
      (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left
      (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i))) :
    U.ExpandsG F k (∑ i, c i • extendSec U F k (genericSec U k (σ i)) : GroupSec U F k) s :=
  ⟨n, c, σ, f, h₁, (secLin_iff U.LG.isLB _ σ
    (UnifPre.gFK (G := G) F) c (fun i => extendSec U F k (genericSec U k (σ i))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (σ i) q y J) (Category.assoc _ _ _))))).2 rfl, h₂⟩

theorem exists_linear_section (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (h : U.ExpBij k) :
    ∃ e : Fam D.toPre F k →ₗ[F] GroupSec U F k, ∀ v s, U.ExpandsG F k v s ↔ v = e s := by
  obtain ⟨-, h₂⟩ := expandsG_bijective U F hG hk h
  choose f hf using fun s => (h₂ s).exists
  have iff : ∀ v s, U.ExpandsG F k v s ↔ v = f s := fun v s =>
    ⟨fun h => (h₂ s).unique h (hf s), fun h => h ▸ hf s⟩
  have lin : ∀ (c : F) s s', f (c • s + s') = c • f s + f s' := fun c s s' =>
    ((iff _ _).1 (expandsG_lin U F k c (hf s) (hf s'))).symm
  have f0 : f 0 = 0 := by
    have := lin 1 0 0
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  exact ⟨{ toFun := f
           map_add' := fun t t' => by simpa only [one_smul] using lin 1 t t'
           map_smul' := fun c t => by simpa only [add_zero, f0, RingHom.id_apply] using lin c t 0 }, iff⟩

theorem exists_linear_series {k : ℕ} {κ : Type} (g : IntSec U k →ₗ[R] MvPowerSeries κ R) :
    ∃ Λ : GroupSec U F k →ₗ[F] MvPowerSeries κ F, ∀ (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k),
      Λ (∑ i, c i • extendSec U F k (genericSec U k (σ i))) = ∑ i, MvPowerSeries.C (c i) *
        MvPowerSeries.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) (g (σ i)) := by
  have : TopologicalSpace.NoetherianSpace ((Over.pullback (jK R)).obj G).left := noetherianSpace_generic U
  obtain ⟨Λ, hΛ⟩ := exists_linear_extension (genericSec U k) (genericSec_injective U k)
    (extendSec U F k) (isExtension_pullOver (isPullback_groupBase F) U.LG.isLB _ _) g
  refine ⟨Λ, fun n c σ => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hΛ, MvPowerSeries.smul_eq_C_mul]

theorem exists_linear_germ (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (h : U.ExpBij k) {κ : Type}
    (g : IntSec U k →ₗ[R] MvPowerSeries κ R) : ∃ gm : Fam D.toPre F k →ₗ[F] MvPowerSeries κ F,
    ∀ s f, (∃ (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k) (fi : Fin n → ∀ α, D.toPre.SecB k α),
      (∀ i e, U.ExpandsAt e k (σ i) (fi i)) ∧
      (∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
        (D.toPre.famφB α) (DegPre.famε k) (fun i => fi i α) (DegPre.prB D.toPre F).left
        (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i))) ∧
      f = ∑ i, MvPowerSeries.C (c i) *
        MvPowerSeries.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) (g (σ i))) ↔
      f = gm s := by
  obtain ⟨e, he⟩ := exists_linear_section U F hG hk h
  obtain ⟨Λ, hΛ⟩ := exists_linear_series U F g
  refine ⟨Λ ∘ₗ e, fun s f => ⟨?_, ?_⟩⟩
  · rintro ⟨n, c, σ, fi, h₁, h₂, rfl⟩
    rw [LinearMap.comp_apply, ← (he _ s).1 (expandsG_sum U F c σ fi h₁ h₂), hΛ]
  · rintro rfl
    obtain ⟨n, c, σ, fi, h₁, -, h₂⟩ := (he _ s).2 rfl
    exact ⟨n, c, σ, fi, h₁, h₂,
      (congrArg Λ ((he _ s).1 (expandsG_sum U F c σ fi h₁ h₂)).symm).trans (hΛ n c σ)⟩

theorem exists_linear_quotient (halg : JetSer.JetAlgSt) (hrep : JetSer.RepSt) (hser : JetSer.SerSt)
    (hex : JetSer.SerExSt) {d : ℕ} {x : JetSer.Fam G (Fin d)} (hx : Chart.IsUnivChart G d x) {j : U.LG.L.ι}
    (hj : ⊤ ≤ η[G].left ⁻¹ᵁ U.LG.L.U j) (k : ℕ) {r : PS R 1 d} (hr : IsUnit r) :
    ∃ g : IntSec U k →ₗ[R] PS R 1 d, ∀ (σ : IntSec U k) f,
      (∃ S, JetSer.IsSer1 x _ (LB.Sec.f σ (fun _ => j)) S ∧ f * r = S) ↔ f = g σ := by
  obtain ⟨τ, hτ⟩ := exists_serHom halg hrep hser hex hx
    (U := LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j))
    (GermExist.top_le_preimage_wchart _ _ j _ (fun _ => by rw [Category.comp_id]; exact hj))
  obtain ⟨u, rfl⟩ := hr
  refine ⟨LinearMap.mulRight R (u⁻¹).val ∘ₗ τ.toLinearMap ∘ₗ chartLin G.hom
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))) (fun _ => j), fun σ f => ⟨?_, ?_⟩⟩
  · rintro ⟨S, hS, e⟩
    exact (Units.eq_mul_inv_iff_mul_eq u).2 (e.trans ((hτ _ _).1 hS))
  · intro e
    exact ⟨_, (hτ _ _).2 rfl, (Units.eq_mul_inv_iff_mul_eq u).1 e⟩

end Group

theorem germ_exists_unique_linear : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt →
    JetSer.SerSt → JetSer.SerExSt → FamGerm.GermExSt := by
  intro hL _ _ halg hrep hser hex E _ _ _ H V _ _ _ F _ _ _ _ _ _ y q hq
  let _ := H.starRing
  have := y.t.act.hom H.w0
  obtain ⟨r, hr, ur⟩ := (hex V y.t.G y.d y.x y.hx).1
    (LB.wchart y.P.U.LG.L (JetSer.primφ (y.t.act.act H.w0)) (fun _ => y.j))
    (GermExist.top_le_preimage_wchart _ _ y.j _ (fun k => by
      rw [GermExist.unit_comp_primφ _ (IsMonHom.one_hom _) k]; exact y.hj)) (y.ρ.s (fun _ => y.j)).val
  obtain ⟨g, hg⟩ := exists_linear_quotient y.P.U.toUnifPre halg hrep hser hex y.hx y.hj q
    ((GermExist.isUnit_of_isSer1 hrep hser y.hx (Units.isUnit _) hr).pow q)
  obtain ⟨gm, h⟩ := exists_linear_germ y.P.U.toUnifPre F hL.globalFns hq (y.P.U.expand q hq) g
  refine ⟨gm, fun s f => Iff.trans ⟨?_, ?_⟩ (h s f)⟩
  · rintro ⟨n, c, σ, fi, g', r', h₁, h₂, hr', h₃, e⟩
    obtain rfl := ur r' hr'
    obtain rfl : g' = fun i => g (σ i) := funext fun i => (hg _ _).1 (h₃ i)
    exact ⟨n, c, σ, fi, h₁, h₂, e⟩
  · rintro ⟨n, c, σ, fi, h₁, h₂, e⟩
    exact ⟨n, c, σ, fi, fun i => g (σ i), r, h₁, h₂, hr, fun i => (hg _ _).2 rfl, e⟩

end GlobalTheory.FamGermExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormAdjointCompIsometryEquiv
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem norm_adjoint_comp_isometryEquiv {V₁ V₂ V₃ : Type} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [CompleteSpace V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [CompleteSpace V₂]
    [NormedAddCommGroup V₃] [InnerProductSpace ℂ V₃] [CompleteSpace V₃]
    (A : V₂ →L[ℂ] V₁) (φ : V₃ ≃ₗᵢ[ℂ] V₂) (v : V₁) :
    ‖ContinuousLinearMap.adjoint (A.comp (φ : V₃ →L[ℂ] V₂)) v‖ = ‖ContinuousLinearMap.adjoint A v‖ := by
  rw [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm]
  simp

theorem exists_wigMap_pair_of_isType : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (u up um : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → IsType k r z πp up → IsType k r z πm um → (∀ i ∈ Finset.Icc 1 k, up i = if i = l + 1 then u i + (n₀ : ℝ) else u i) → (∀ i ∈ Finset.Icc 1 k, um i = if i = l then u i - (n₀ : ℝ) else u i) → ∃ (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ Vp _ _ _ Vm _ _ _ k r z π πp πm u up um l n₀ b hz hT hπ hgap hl hlk hn hb hnb h1b hp hm hup hum
  obtain ⟨Vp', _, _, _, Vm', _, _, _, πp', πm', Ap', Am', hp', hm', hAp, hAm, hlb⟩ :=
    _root_.GlobalTheory.WigSh.exists_shifted_types_lower_bound V k r z π u l n₀ b hz hT hπ hgap hl hlk hn hb hnb h1b
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨φp, hφp⟩ := GlobalTheory.exists_isometry_of_isType_of_param_eq Vp Vp' n r z πp πp' _ _ hz hT hp hp' (by
    intro i hi
    rw [hup i hi, Function.update_apply]
    split_ifs with h
    · rw [h]
    · rfl)
  obtain ⟨φm, hφm⟩ := GlobalTheory.exists_isometry_of_isType_of_param_eq Vm Vm' n r z πm πm' _ _ hz hT hm hm' (by
    intro i hi
    rw [hum i hi, Function.update_apply]
    split_ifs with h
    · rw [h]
    · rfl)
  refine ⟨fun ω => (Ap' ω).comp (φp : Vp →L[ℂ] Vp'), fun ω => (Am' ω).comp (φm : Vm →L[ℂ] Vm'), ?_, ?_, ?_⟩
  · exact wigMap_comp V Vp' Vp (n + 1) r z π πp' πp n₀ 0 Ap' (fun _ => (φp : Vp →L[ℂ] Vp')) hAp
      (wigMap_zero_of_contraction Vp' Vp (n + 1) r z πp' πp _ (fun v => by simp)
        (fun h hh v => by simpa using hφp h hh v))
  · exact wigMap_comp V Vm' Vm (n + 1) r z π πm' πm n₀ 0 Am' (fun _ => (φm : Vm →L[ℂ] Vm')) hAm
      (wigMap_zero_of_contraction Vm' Vm (n + 1) r z πm' πm _ (fun v => by simp)
        (fun h hh v => by simpa using hφm h hh v))
  · intro ω hω hωz v
    rw [norm_adjoint_comp_isometryEquiv, norm_adjoint_comp_isometryEquiv]
    exact hlb ω hω hωz v

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusModel

open GlobalTheory.AdicColimit

section BaseChange

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem exists_isGt (hG : GlobalFnsSt) (E : SplitExt S) :
    ∃ (H : Over S) (_ : GrpObj H), IsCommMonObj H ∧ E.IsGt H := by
  letI := E.free
  letI := E.finite
  have hN : ∀ k, (E.O (E.basis k)).L.IsLB := fun k => (E.O (E.basis k)).isLB
  obtain ⟨G, q, u, hu⟩ := exists_generatorScheme E.B.left _ (fun k => (E.O (E.basis k)).L) hN
  obtain ⟨h₁, h₂, h₃, -, -⟩ :=
    generatorScheme_properties E.B.left _ (fun k => (E.O (E.basis k)).L) hN G q u hu
  obtain ⟨inst, hc, d, -⟩ := exists_grpObj_gtDatum_of_generators hG S E G q u hu h₁ inferInstance h₃
  exact ⟨Over.mk (q ≫ E.B.hom), inst, hc, ⟨d⟩⟩

def polPull [IsAffine S] (P : PolAV S) : PolAV S' :=
  have h := isGrpPullback_pullback P.A f
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom f)
  have hw := (isGen_iff _).1 (PolBaseChange.lbIso_refl hL').choose_spec
  { A := (Over.pullback f).obj P.A
    isAb := TLinPf.isAb_pullback f P.A P.isAb
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull (pullback.fst P.A.hom f)
    isLB := hL'
    rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym
    ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top S) (fun _ => trivial) P.ample
    ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }

theorem torsion_pullback (B : Over S) [GrpObj B] (N : ℕ) (h₁ : IsFinite (𝟙 B ^ N).left) (h₂ : Flat (𝟙 B ^ N).left) :
    IsFinite (torsion ((Over.pullback f).obj B) N).hom ∧ Flat (torsion ((Over.pullback f).obj B) N).hom := by
  rw [← MulEtaleDvr.mulN_eq_pow] at h₁ h₂
  have H := MulEtaleDvr.isPullback_torsion ((Over.pullback f).obj B) N
  rw [← MulEtaleDvr.pullback_map_mulN] at H
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) H
      (MorphismProperty.overPullbackMap (P := @IsFinite) f _ h₁),
    MorphismProperty.of_isPullback (P := @Flat) H (MorphismProperty.overPullbackMap (P := @Flat) f _ h₂)⟩

variable {H : Over S} [GrpObj H]

theorem exists_pushEquiv (T : Over S') (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ π : (T ⟶ (Over.pullback f).obj H) ≃* (Over.mk s ⟶ H), ∀ x, (π x).left = x.left ≫ pullback.fst H.hom f := by
  subst hs
  have h := isGrpPullback_pullback H f
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y => ?_⟩, fun x => rfl⟩
  exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

def actPull [IsCommMonObj H] {O : Type} [Ring O] (ρ : RingAct H O) : RingAct ((Over.pullback f).obj H) O where
  act a := (Over.pullback f).map (ρ.act a)
  hom a := by have := ρ.hom a; infer_instance
  map_one := by rw [ρ.map_one, CategoryTheory.Functor.map_id]
  map_mul a b := by rw [ρ.map_mul, CategoryTheory.Functor.map_comp]
  map_add a b := by
    rw [ρ.map_add a b]
    exact map_mul (Over.pullback f).homMonoidHom (ρ.act a) (ρ.act b)

end BaseChange

theorem exists_model (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
    {ιD : D.OAct O} {ιA : A.OAct O} {ιG : RingAct G O} (hO : U.OLinear O ιD ιA ιG)
    {S' : Scheme.{0}} (f : S' ⟶ Spec (CommRingCat.of R)) :
    ∃ (Gt : Over S') (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (ρ : RingAct Gt O)
      (J : ∀ (T : Over S') (s : T.left ⟶ Spec (CommRingCat.of R)), s = T.hom ≫ f → IsAdicColimit I (Over.mk s) →
        ((T ⟶ Gt) ≃* (Over.mk s ⟶ G))),
      (GtBaseChange.extBC f (splitExt D.toPre)).IsGt Gt ∧
      (∀ T T' s s' hs hs' hT hT' (k : T' ⟶ T) (x : T ⟶ Gt),
        (J T' s' hs' hT' (k ≫ x)).left = k.left ≫ (J T s hs hT x).left) ∧
      ∀ T s hs hT (x : T ⟶ Gt) (a : O), J T s hs hT (x ≫ ρ.act a) = J T s hs hT x ≫ ιG.act a := by
  obtain ⟨H, _, _, hH⟩ := exists_isGt hG (splitExt D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hG hH
  obtain ⟨ρ, hρ⟩ := exists_ringAct hG ιD (Φ := Φ) hΦ
  obtain ⟨J, hJ⟩ := exists_mulEquiv U hG (Φ := Φ) hΦ
  choose π hπ using exists_pushEquiv f (H := H)
  obtain ⟨d⟩ := hH
  refine ⟨(Over.pullback f).obj H, inferInstance, inferInstance, actPull f ρ,
    fun T s hs hT => (π T s hs).trans (J _ hT), GtBaseChange.isGt_extBC f _ H d, ?_, ?_⟩
  · intro T T' s s' hs hs' hT hT' k x
    let k₀ : Over.mk s' ⟶ Over.mk s := Over.homMk k.left (by
      change k.left ≫ s = s'
      rw [hs, hs', Over.w_assoc])
    have e : π T' s' hs' (k ≫ x) = k₀ ≫ π T s hs x := Over.OverMorphism.ext (by
      rw [hπ, Over.comp_left, Over.comp_left, hπ, Category.assoc]; rfl)
    have := (hJ _ hT' (k₀ ≫ π T s hs x) _).2 (((hJ _ hT (π T s hs x) _).1 rfl).pull k₀ (hΦ.1 _ _ k₀ _))
    rw [← e] at this
    exact congrArg (·.left) this
  · intro T s hs hT x a
    have e : π T s hs (x ≫ (actPull f ρ).act a) = π T s hs x ≫ ρ.act a := Over.OverMorphism.ext (by
      rw [hπ, Over.comp_left, Over.comp_left, hπ, Category.assoc, Category.assoc]
      exact congrArg (x.left ≫ ·) (pullback.lift_fst _ _ _))
    have := (hJ _ hT (π T s hs x ≫ ρ.act a) _).2 (((hJ _ hT (π T s hs x) _).1 rfl).smul hG hO a (hρ a _ _))
    rw [← e] at this
    exact this

theorem isAdicColimit_of_pow {R A : Type} [CommRing R] [CommRing A] (I : Ideal R) (φ : R →+* A) (n : ℕ)
    (h : ∀ a ∈ I ^ n, φ a = 0) : IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  refine isAdicColimit_of_factor n (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (n + 1)) φ
    fun a ha => h a (Ideal.pow_le_pow_right (Nat.le_succ n) ha)))) ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]
  rfl

theorem isAdicColimit_of_finite_flat {R O : Type} [CommRing R] [CommRing O] [IsLocalRing O] (I : Ideal R)
    (f : R →+* O) (hO : IsAdicComplete (I.map f) O) (hm : ∀ a ∈ maximalIdeal O, ∃ n : ℕ, a ^ n ∈ I.map f)
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] :
    IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)))) := by
  have := henselianLocalRing_of_le_radical (I.map f) hm
  refine isAdicColimit_finite_henselian_of_local isAdicColimit_spec_of_isLocalRing isAdicColimit_of_disjoint_cover
    R I O A _ ?_
  rw [← Ideal.map_map]
  exact GlobalTheory.FlatComplete.isAdicComplete_of_finite_flat O _ hO A

theorem main : Laws → Laws4 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (O : Type) [CommRing O] [IsLocalRing O] (f : V →+* O), IsLocalHom f → IsAdicComplete ((maximalIdeal V).map f) O → (∀ a ∈ maximalIdeal O, ∃ n : ℕ, a ^ n ∈ (maximalIdeal V).map f) → ∃ (Ex : SplitExt (Spec (CommRingCat.of O))) (B : PolAV (Spec (CommRingCat.of O))) (_ : B.A = Ex.B) (_ : HEq B.grp Ex.grpB) (Gt : Over (Spec (CommRingCat.of O))) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (ρ : RingAct Gt (𝓞 E)) (J : ∀ (A : Type) [CommRing A] [Algebra O A], ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) → (specO O A ⟶ Gt) → (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G)), Ex.IsGt Gt ∧ (∀ N : ℕ, 1 ≤ N → IsFinite (torsion Ex.B N).hom ∧ Flat (torsion Ex.B N).hom) ∧ (∀ (A A' : Type) [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A'] (hA : ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0)) (hA' : ((Module.Finite O A' ∧ Module.Free O A') ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A' (f a) = 0)) (φ : A →ₐ[O] A') (x : specO O A ⟶ Gt), (J A' hA' (ptMap φ ≫ x)).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (J A hA x).left) ∧ ∀ (A : Type) [CommRing A] [Algebra O A] (hA : ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0)), (∀ x x', J A hA (x * x') = J A hA x * J A hA x') ∧ (∀ x (a : 𝓞 E), J A hA (x ≫ ρ.act a) = J A hA x ≫ t.act.act a) ∧ Function.Injective (J A hA) ∧ ((∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) → Function.Surjective (J A hA)) ∧ ∀ (I : Ideal A) (g : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G), IsNilpotent I → Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g.left = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (1 : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G).left → ∃ x, J A hA x = g := by
  intro hL _ E _ _ _ H V _ _ _ _ t P O _ _ f _ hO hm
  letI := H.starRing
  obtain ⟨Gt, _, _, ρ, J, h₁, h₂, h₃⟩ := exists_model hL.globalFns P.U.toUnifPre P.lin (spMap f)
  have hs : ∀ (A : Type) [CommRing A] [Algebra O A],
      Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)) = (specO O A).hom ≫ spMap f := fun A _ _ => by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  have hc : ∀ (A : Type) [CommRing A] [Algebra O A], ((Module.Finite O A ∧ Module.Free O A) ∨
      ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) →
      IsAdicColimit (maximalIdeal V) (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)))) := by
    rintro A _ _ (⟨_, _⟩ | ⟨n, hn⟩)
    exacts [isAdicColimit_of_finite_flat _ f hO hm A, isAdicColimit_of_pow _ _ n hn]
  refine ⟨GtBaseChange.extBC (spMap f) (splitExt P.D.toPre), polPull (spMap f) P.D.toPre.P, rfl, HEq.rfl,
    Gt, inferInstance, inferInstance, ρ, fun A _ _ hA => J (specO O A) _ (hs A) (hc A hA), h₁, fun N hN => ?_,
    fun A A' _ _ _ _ hA hA' φ x => h₂ _ _ _ _ _ _ _ _ (ptMap φ) x,
    fun A _ _ hA => ⟨map_mul _, h₃ _ _ _ _, MulEquiv.injective _, fun _ => MulEquiv.surjective _,
      fun _ g _ _ => MulEquiv.surjective _ g⟩⟩
  obtain ⟨a, b, -⟩ := hL.mulN _ P.D.toPre.P N hN
  exact torsion_pullback (spMap f) P.D.toPre.P.A N a b

end GlobalTheory.TorusModel
end
end

