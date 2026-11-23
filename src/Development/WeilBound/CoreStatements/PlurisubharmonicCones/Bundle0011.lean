module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChart
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0008

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.FinrankOfLieMult
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open TensorProduct

namespace LevelTowerAlt

theorem mem_eigSp {R W O : Type} [CommRing R] [AddCommGroup W] [Module R W] [CommRing O] (ρ : O →+* Module.End R W)
    (σ : O →+* R) (x : W) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem eigSp_baseChange {E : Type} [Field E] [NumberField E] {O R M W : Type} [CommRing O] [CommRing R] [Algebra O R]
    [Module.Flat O R] [AddCommGroup M] [Module O M] [AddCommGroup W] [Module R W] [Module O W] [IsScalarTower O R W]
    (j : M →ₗ[O] W) (hj : IsBaseChange R j) (ρM : 𝓞 E →+* Module.End O M) (ρW : 𝓞 E →+* Module.End R W)
    (h : ∀ a z, ρW a (j z) = j (ρM a z)) (s : 𝓞 E →+* O) :
    eigSp ρW ((algebraMap O R).comp s) = Submodule.span R (j '' (eigSp ρM s : Set M)) := by
  classical
  refine le_antisymm (fun w hw => ?_) (Submodule.span_le.2 ?_)
  · let b := RingOfIntegers.basis E
    let Φ := fun i => ρM (b i) - s (b i) • (LinearMap.id : M →ₗ[O] M)
    have hker : LinearMap.ker (LinearMap.pi Φ) ≤ eigSp ρM s := by
      intro z hz
      have h1 : ∀ i, ρM (b i) z = s (b i) • z := fun i => sub_eq_zero.1 (congrFun hz i)
      rw [mem_eigSp]
      intro a
      rw [← b.sum_repr a]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, h1, Finset.sum_smul, smul_assoc]
    obtain ⟨u, rfl⟩ := hj.equiv.surjective w
    have h2 : ∀ i (u : R ⊗[O] M), hj.equiv ((Φ i).lTensor R u) =
        ρW (b i) (hj.equiv u) - algebraMap O R (s (b i)) • hj.equiv u := by
      intro i u
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r z =>
        rw [LinearMap.lTensor_tmul, hj.equiv_tmul, hj.equiv_tmul, map_smul, h, smul_comm, ← smul_sub, algebraMap_smul,
          ← j.map_smul, ← j.map_sub]
        rfl
      | add x y hx hy =>
        rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _), smul_add]
        abel
    have h3 : ∀ i, (Φ i).lTensor R u = 0 := fun i => by
      apply hj.equiv.injective
      rw [h2, map_zero, (mem_eigSp _ _ _).1 hw]
      exact sub_self _
    have h4 : LinearMap.pi Φ = ∑ i, LinearMap.single O (fun _ => M) i ∘ₗ Φ i := by
      ext z i
      simp [Finset.sum_apply, Pi.single_apply]
    have h5 : (LinearMap.pi Φ).lTensor R u = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h4, ← LinearMap.coe_lTensorHom, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.coe_lTensorHom, LinearMap.lTensor_comp, LinearMap.comp_apply, h3, map_zero]
    obtain ⟨u', rfl⟩ := (Module.Flat.lTensor_exact R (LinearMap.exact_subtype_ker_map (LinearMap.pi Φ)) u).1 h5
    clear hw h3 h5
    induction u' using TensorProduct.induction_on with
    | zero => simp
    | tmul r z =>
      rw [LinearMap.lTensor_tmul, hj.equiv_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hker z.2, rfl⟩)
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  · rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_eigSp] at hz ⊢
    intro a
    rw [h, hz, map_smul, RingHom.comp_apply, algebraMap_smul]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

theorem spDual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← spMap_comp]
  congr 1
  exact RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem spDual_alg {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ spMap (algebraMap A (DualNumber A)) = spMap (algebraMap B (DualNumber B)) ≫ spMap f := by
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  exact RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem left_eq_of_cart {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) {x : Sp A ⟶ S'} {x' : Sp B ⟶ S'} (hx : x' = spMap g ≫ x)
    (v : epsAt x ⟶ t'.G) (v' : epsAt x' ⟶ t'.G) (h : v'.left ≫ m.φ = spMap (dualMap g) ≫ v.left ≫ m.φ) :
    v'.left = spMap (dualMap g) ≫ v.left := by
  refine m.cart.1.hom_ext (h.trans (Category.assoc _ _ _).symm) ?_
  have h1 : v'.left ≫ t'.G.hom = spMap (algebraMap B (DualNumber B)) ≫ x' := Over.w v'
  have h2 : v.left ≫ t'.G.hom = spMap (algebraMap A (DualNumber A)) ≫ x := Over.w v
  rw [h1, Category.assoc, h2, ← Category.assoc, spDual_alg, hx, Category.assoc]

theorem push_model {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {R : Type} [CommRing R] {x' : Sp R ⟶ S'} {x : Sp R ⟶ S} (hx : x = x' ≫ f) {W : Type} [AddCommGroup W] [Module R W]
    (M' : LieModel t'.G x' W) (ρ : 𝓞 E →+* Module.End R W) (hρ : M'.IsActOf t'.act.act ρ) :
    ∃ M : LieModel t.G x W, M.IsActOf t.act.act ρ ∧ ∀ u, (M'.pt u).left ≫ m.φ = (M.pt u).left := by
  subst hx
  obtain ⟨M, hM⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback S S' t.G t'.G f m.φ m.cart R x' W).2 M'
  refine ⟨M, fun a e => Over.OverMorphism.ext ?_, hM⟩
  rw [← hM, hρ a e, Over.comp_left, Over.comp_left, ← hM, Category.assoc, Category.assoc, m.act a]

variable {L : Type} [Field L] [NumberField L] {t' : SAB H (Sp (𝓞 L))} {M : Type} [AddCommGroup M] [Module (𝓞 L) M]
  (MB : LieModel t'.G (𝟙 _) M) {ρM : 𝓞 E →+* Module.End (𝓞 L) M}

theorem exists_model (hρ : MB.IsActOf t'.act.act ρM) {S : Scheme.{0}} {t : SAB H S} {f : S ⟶ Sp (𝓞 L)}
    (m : SABMap t t' f) {R : Type} [CommRing R] [IsDomain R] (g : 𝓞 L →+* R) (hg : Function.Injective g)
    (x : Sp R ⟶ S) (hx : x ≫ f = spMap g) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W) (MW : LieModel t.G x W) (ρW : 𝓞 E →+* Module.End R W)
      (j : M →+ W), MW.IsActOf t.act.act ρW ∧
      (∀ z, (MW.pt (j z)).left ≫ m.φ = spMap (dualMap g) ≫ (MB.pt z).left) ∧ (∀ a z, j (a • z) = g a • j z) ∧
      ∀ (s : 𝓞 E →+* 𝓞 L) (n : ℕ) (y : Fin n → M), (∀ k, y k ∈ eigSp ρM s) → LinearIndependent (𝓞 L) y →
        (∀ z ∈ eigSp ρM s, ∃ u, IsUnit (g u) ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y)) →
        LinearIndependent R (fun k => j (y k)) ∧
          Submodule.span R (Set.range fun k => j (y k)) = eigSp ρW (g.comp s) := by
  letI : Algebra (𝓞 L) R := g.toAlgebra
  haveI : Smooth t'.G.hom := t'.semi.smooth
  obtain ⟨W, _, _, ⟨M₁⟩⟩ := lieModel_exists _ t'.G R (spMap g ≫ 𝟙 _)
  letI : Module (𝓞 L) W := Module.compHom W g
  haveI : IsScalarTower (𝓞 L) R W := ⟨fun a b e => by
    show (g a * b) • e = g a • b • e
    rw [mul_smul]⟩
  obtain ⟨j₀, hj₀, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts _ t'.G (𝓞 L) R g (𝟙 _) M W MB M₁
  let j : M →ₗ[𝓞 L] W := { toFun := j₀, map_add' := map_add j₀, map_smul' := fun a e => j₀.map_smulₛₗ a e }
  have hbc : IsBaseChange R j := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange _ t'.G (𝓞 L) R (𝟙 _) M W MB M₁ j hj₀
  have key : ∀ (x₀ : Sp R ⟶ Sp (𝓞 L)) (M₀ : LieModel t'.G x₀ W), x₀ = x ≫ f →
      ∃ M' : LieModel t.G x W, ∀ e, (M'.pt e).left ≫ m.φ = (M₀.pt e).left := by
    rintro _ M₀ rfl
    exact (_root_.GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ S t'.G t.G f m.φ m.cart R x W).1 M₀
  obtain ⟨MW, hMW⟩ := key _ M₁ (by rw [hx, Category.comp_id])
  have hl : ∀ z, (MW.pt (j z)).left ≫ m.φ = spMap (dualMap g) ≫ (MB.pt z).left := fun z =>
    (hMW _).trans ((Category.comp_id _).symm.trans (hj₀ z))
  obtain ⟨ρW, hρW, -⟩ := lieModel_exists_unique_act S t.G R x W MW _ t.act.act t.act.hom t.act.one t.act.mul t.act.add
  have heq : ∀ a z, ρW a (j z) = j (ρM a z) := by
    intro a z
    refine MW.inj ?_
    rw [hρW a (j z)]
    refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ?_)
    · have h1 : (MB.pt (ρM a z)).left = (MB.pt z).left ≫ (t'.act.act a).left := by
        rw [hρ a z]
        rfl
      change ((MW.pt (j z)).left ≫ (t.act.act a).left) ≫ m.φ = (MW.pt (j (ρM a z))).left ≫ m.φ
      rw [Category.assoc, m.act a, ← Category.assoc, hl z, hl (ρM a z), h1, Category.assoc]
    · rw [Over.w, Over.w]
  haveI : Module.IsTorsionFree (𝓞 L) R := .of_smul_eq_zero fun a r h =>
    (mul_eq_zero.1 h).imp_left fun h0 => hg (h0.trans (map_zero g).symm)
  refine ⟨W, inferInstance, inferInstance, MW, ρW, j.toAddMonoidHom, hρW, hl, fun a z => j.map_smul a z,
    fun s n y hy hli hsp => ⟨?_, ?_⟩⟩
  · have h1 := (Module.Flat.linearIndependent_one_tmul (S := R) hli).map' hbc.equiv.toLinearMap hbc.equiv.ker
    have h2 : (hbc.equiv.toLinearMap ∘ fun k => (1 : R) ⊗ₜ[𝓞 L] y k) = fun k => j (y k) := by
      funext k
      exact (hbc.equiv_tmul 1 (y k)).trans (one_smul _ _)
    rwa [h2] at h1
  · refine Eq.trans ?_ (eigSp_baseChange j hbc ρM ρW heq s).symm
    refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨k, rfl⟩
      exact ⟨y k, hy k, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨u, hu, h1⟩ := hsp z hz
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 L)).1 h1
      have h2 : g u • j z = ∑ k, g (c k) • j (y k) := by
        refine (j.map_smul u z).symm.trans ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hc, map_sum]
        exact Finset.sum_congr rfl fun k _ => j.map_smul _ _
      refine (Submodule.smul_mem_iff_of_isUnit _ hu).1 ?_
      rw [h2]
      exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem finrank_of_lieMult {S : Scheme.{0}} {t : SAB H S} {k : Type} [Field k] {x : Sp k ⟶ S} {W : Type}
    [AddCommGroup W] [Module k W] (MW : LieModel t.G x W) {ρW : 𝓞 E →+* Module.End k W}
    (hρ : MW.IsActOf t.act.act ρW) {τ : 𝓞 E →+* k} {n : ℕ} (h : LieMult t.act x τ n) :
    Module.finrank k (eigSp ρW τ) = n := by
  obtain ⟨v, hv⟩ := h
  have hv' : IsEigFrame t.act x τ v := hv
  choose u hu using fun i => MW.onto (v i) (hv'.1 i).1
  have e : v = fun i => MW.pt (u i) := funext fun i => (hu i).symm
  rw [e] at hv'
  obtain ⟨h1, h2⟩ := (((_root_.GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame S k t.G x W MW).2 _ t.act ρW τ hρ).2 n u).1 hv'
  rw [← h2, finrank_span_eq_card h1, Fintype.card_fin]

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.LeviNonnegSemipositiveLine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

section

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}

open MvPolynomial in
theorem coneTangent_inv (hP : IsMultiHomogIdeal P) {z w : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) (hw : IsConeTangent (Int.castRingHom ℂ) P (torusSmul c z) w) :
    IsConeTangent (Int.castRingHom ℂ) P z (torusSmul c⁻¹ w) := by
  obtain ⟨S, hS, hPS⟩ := hP
  have hle : Ideal.span S ≤ (tanIdeal z (torusSmul c⁻¹ w)).comap (MvPolynomial.map (Int.castRingHom ℂ)) := by
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨d, hd⟩ := hS f hf
    have hfP : f ∈ P := by rw [hPS]; exact Ideal.subset_span hf
    refine mem_tanIdeal.2 ⟨hz.2 f hfP, ?_⟩
    have hd' : ReciprocityTheory.AnForm.R.IsMultiHomog (MvPolynomial.map (Int.castRingHom ℂ) f) d :=
      fun m hm k => hd m (support_map_subset _ _ hm) k
    have hne : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
    apply mul_left_cancel₀ hne
    rw [mul_zero, Finset.mul_sum]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) (hw f hfP)
    rw [← _root_.mul_assoc, ← eval_pderiv_scale hd' c z q]
    have := hc q.1
    show c q.1 * eval (torusSmul c z) (pderiv q (MvPolynomial.map (Int.castRingHom ℂ) f)) * ((c q.1)⁻¹ * w q) = _
    field_simp
  intro f hf
  rw [hPS] at hf
  exact (mem_tanIdeal.1 (hle hf)).2

theorem levi_of_chart {n : ℕ} {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) {A : HermLine J}
    (hA : IsSmoothHerm A) {t u : Fin n → ℂ} (ht : t ∈ Metric.ball (0 : Fin n → ℂ) 1) {c c' : K → ℂ}
    (hc : ∀ k, c k ≠ 0) {w : (Σ k, J k) → ℂ}
    (hw : torusSmul c⁻¹ w = fderiv ℂ χ.γ t u + torusSmul c' (χ.γ t)) :
    levi (fun z => Real.log (A.h z)) (torusSmul c (χ.γ t)) w = levi (fun t' => Real.log (A.h (χ.γ t'))) t u := by
  have hγ := χ.analytic t ht
  have hz := (χ.mem t ht).1
  have hℓa : AnalyticAt ℂ (fun ζ : ℂ => t + ζ • u) 0 := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hℓ0 : t + (0 : ℂ) • u = t := by simp
  have hℓd : HasDerivAt (fun ζ : ℂ => t + ζ • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const u).const_add t
  have hγ' : AnalyticAt ℂ χ.γ (t + (0 : ℂ) • u) := by rw [hℓ0]; exact hγ
  have hga : AnalyticAt ℂ (fun ζ : ℂ => χ.γ (t + ζ • u)) 0 :=
    AnalyticAt.comp (g := χ.γ) (f := fun ζ : ℂ => t + ζ • u) hγ' hℓa
  have hgd : HasDerivAt (fun ζ : ℂ => χ.γ (t + ζ • u)) (fderiv ℂ χ.γ t u) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hγ.differentiableAt.hasFDerivAt hℓd hℓ0.symm
  have hψ : ContDiffAt ℝ 2 (fun t' => Real.log (A.h (χ.γ t'))) t := by
    have hR : AnalyticAt ℝ χ.γ t := hγ.restrictScalars
    exact ContDiffAt.comp (g := fun z => Real.log (A.h z)) t (contDiffAt_log_h hA hz) hR.contDiffAt
  let δ : ℂ → (Σ k, J k) → ℂ := fun ζ => torusSmul (fun k => c k * Complex.exp (ζ * c' k)) (χ.γ (t + ζ • u))
  have hδa : AnalyticAt ℂ δ 0 := analyticAt_pi_iff.2 fun p =>
    (analyticAt_const.mul (analyticAt_id.mul analyticAt_const).cexp).mul (analyticAt_pi_iff.1 hga p)
  have hδ0 : δ 0 = torusSmul c (χ.γ t) := by
    funext p
    simp [δ, torusSmul]
  have hδd : HasDerivAt δ w 0 := by
    refine hasDerivAt_pi.2 fun p => ?_
    have h1 := (((hasDerivAt_id (0 : ℂ)).mul_const (c' p.1)).cexp.const_mul (c p.1)).mul (hasDerivAt_pi.1 hgd p)
    have h2 : (c p.1)⁻¹ * w p = fderiv ℂ χ.γ t u p + c' p.1 * χ.γ t p := congrFun hw p
    have h3 : w p = c p.1 * (fderiv ℂ χ.γ t u p + c' p.1 * χ.γ t p) := by
      rw [← h2, mul_inv_cancel_left₀ (hc p.1)]
    refine HasDerivAt.congr_deriv h1 ?_
    rw [h3]
    simp
    ring
  have hcz : ∀ k, ∃ i, torusSmul c (χ.γ t) ⟨k, i⟩ ≠ 0 := fun k => (hz k).imp fun i hi => mul_ne_zero (hc k) hi
  rw [levi_disc hδa hδd hδ0 (contDiffAt_log_h hA hcz), levi_disc hℓa hℓd hℓ0 hψ]
  have hp : AnalyticAt ℂ (fun s : Fin 1 → ℂ => s 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0
  have hq : AnalyticAt ℂ (fun s : Fin 1 → ℂ => t + s 0 • u) 0 := analyticAt_const.add (hp.smul analyticAt_const)
  have hq0 : t + (0 : Fin 1 → ℂ) 0 • u = t := by simp
  refine levi_add_re (G := fun s => ∑ k, (A.a k : ℂ) * ((Real.log ‖c k‖ : ℝ) + s 0 * c' k)) ?_
    (Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul (analyticAt_const.add (hp.mul analyticAt_const))) ?_ _
  · have hR : AnalyticAt ℝ (fun s : Fin 1 → ℂ => t + s 0 • u) 0 := hq.restrictScalars
    exact ContDiffAt.comp (g := fun t' => Real.log (A.h (χ.γ t'))) (f := fun s : Fin 1 → ℂ => t + s 0 • u) 0
      (by rw [hq0]; exact hψ) hR.contDiffAt
  · have hq1 : t + (0 : Fin 1 → ℂ) 0 • u ∈ Metric.ball (0 : Fin n → ℂ) 1 := by rw [hq0]; exact ht
    filter_upwards [hq.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hq1)] with s hs
    rw [show δ (s 0) = torusSmul (fun k => c k * Complex.exp (s 0 * c' k)) (χ.γ (t + s 0 • u)) from rfl,
      log_h_smul A (χ.mem _ hs).1 fun k => mul_ne_zero (hc k) (Complex.exp_ne_zero _), Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)),
      Complex.norm_exp, Real.log_exp, ← Complex.ofReal_intCast, Complex.re_ofReal_mul, Complex.add_re,
      Complex.ofReal_re]

end

theorem levi_nonneg_semipositive_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (A : HermLine J), IsSmoothHerm A → (∀ a, ∀ t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, 0 ≤ levi (fun t' => Real.log (A.h ((D.chart a).γ t'))) t v) → IsSemipositiveH (mCoordIdeal D.y) A := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D A hA h
  refine ⟨hA, fun z hz w hw => ?_⟩
  obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover z hz
  have ht' : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 :=
    mem_ball_zero_iff.2 (ht.trans_lt (by norm_num))
  obtain ⟨u, c', hu⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.coneTangent_eq_fderiv_add_torusSmul K J II Ψ Ω W D a t ht' _
    (coneTangent_inv D.arith.2.1.2.1 ((D.chart a).mem t ht') hc hw)
  exact (h a t ht u).trans_eq (levi_of_chart (D.chart a) hA ht' hc hu).symm

end LevelTowerAlt
end

