module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticLineBundleFrameEqAppellHumbert
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructure
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameOfAppellHumbertFramePeriodFamily
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem form_eq_zero_of_im_span {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (B : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (h1 : ∀ z z' w, B (z + z') w = B z w + B z' w)
    (h2 : ∀ (r : ℂ) z w, B (r • z) w = r * B z w) (h3 : ∀ z w w', B z (w + w') = B z w + B z w')
    (h4 : ∀ (r : ℝ) z w, B z (r • w) = r * B z w) (h0 : ∀ z ∈ s, ∀ w ∈ s, (B z w).im = 0) (z w : Fin g → ℂ) :
    B z w = 0 := by
  have hA : ∀ z ∈ s, ∀ w, (B z w).im = 0 := by
    intro z hz w
    have hw : w ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => exact h0 z hz w hw
    | zero => simpa using congrArg Complex.im (h4 0 z 0)
    | add w w' _ _ e e' => rw [h3, Complex.add_im, e, e', add_zero]
    | smul r w _ e => rw [h4, Complex.im_ofReal_mul, e, mul_zero]
  have hB : ∀ z w, (B z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact hA z hz w
    | zero => simpa using congrArg Complex.im (h2 0 0 w)
    | add z z' _ _ e e' => rw [h1, Complex.add_im, e, e', add_zero]
    | smul r z _ e =>
      have : r • z = (r : ℂ) • z := by ext k; simp
      rw [this, h2, Complex.im_ofReal_mul, e, mul_zero]
  apply Complex.ext
  · have := hB (Complex.I • z) w
    rw [h2] at this
    simpa using this
  · simpa using hB z w

theorem hermForm_adj_of_im_span {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (A A' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (A z) w).im = (hermForm Hm z (A' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (A z) w = hermForm Hm z (A' w) := by
  have hr : ∀ (r : ℝ) (w : Fin g → ℂ), r • w = (r : ℂ) • w := fun r w => by ext k; simp
  have l1 : ∀ z z' w, hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := fun z z' w => by
    simp only [hermForm, add_dotProduct]
  have l2 : ∀ (r : ℂ) z w, hermForm Hm (r • z) w = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have l3 : ∀ z w w', hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := fun z w w' => by
    simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
  have l4 : ∀ (r : ℝ) z w, hermForm Hm z ((r : ℂ) • w) = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
  refine sub_eq_zero.mp (form_eq_zero_of_im_span s hs
    (fun z w => hermForm Hm (A z) w - hermForm Hm z (A' w)) ?_ ?_ ?_ ?_ ?_ z w)
  · intro z z' w
    simp only [map_add (f := _), l1]; ring
  · intro r z w
    simp only [map_smul, l2]; ring
  · intro z w w'
    simp only [map_add (f := _), l3]; ring
  · intro r z w
    simp only [hr, map_smul, l4]; ring
  · intro z hz w hw
    simp only [Complex.sub_im, h0 z hz w hw, sub_self]

theorem anPt_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (σ' : KA l →+* ℂ) (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (Pm : (F.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (F.Di i) ty Pm → y.x = F.u i Pm → AHFrame F i Pm Hm χl fr → (∀ ℓ : Lt1 Dw, IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single (el.symm ℓ) 1) (y.u ℓ.1 ℓ.2)) → ∃ Φ : AnPt y g ty el, Φ.OfFam F i Pm ∧ Φ.Hm = Hm ∧ Φ.χ = χl ∧ Φ.fr = fr ∧ (∀ (α : 𝓞 E) a, Pm (F.t i (α • a)) = tyAct ty α (Pm (F.t i a))) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • Pm (F.t i a)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el σ' F i Pm Hm χl fr hP hy hA hd
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y
  dsimp only at hy hd
  subst hy
  obtain ⟨hH, -, hE, f1, f2, f3, f4, f5⟩ := hA
  have hlin : ∀ (α : 𝓞 E) b, Pm (α • b) = tyAct ty α (Pm b) := fun α b => by
    ext k
    simpa [tyAct] using hP.1 α b k
  refine ⟨{ e := F.ex i Pm
            lat := Pm.range
            span := by simpa using hP.2.2.2.1
            e_add := F.ex_add i Pm hP
            e_onto := F.ex_onto i Pm hP
            e_ker := F.ex_ker i Pm hP
            hol := anHol F i Pm hP
            Hm := Hm
            herm := hH
            χ := χl
            fr := fr
            fr_hol := f1
            fr_ne := f2
            fr_g := f3
            fr_0 := f4
            χ_norm := ?_
            fr_per := ?_
            lin := fun a z => F.ex_lin i Pm hP a z
            adj := ?_
            der := hd }, ⟨fun _ => rfl, rfl, hE⟩, rfl, rfl, rfl, fun α a => by rw [map_smul, hlin],
          fun a ha => F.ex_eta i Pm hP a ha⟩
  · rintro _ ⟨a, rfl⟩
    have hc : (F.ex i Pm 0).left.base (IsLocalRing.closedPoint ℂ) ∈
        (⨆ j, Xo.univ.t.PP.L.U j : Xo.univ.t.G.left.Opens) := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact (f5 a j 0).1
  · rintro _ ⟨a, rfl⟩ j z hz
    exact (f5 a j z).2 hz
  · intro a
    refine hermForm_adj_of_im_span _ hP.2.2.2.1 Hm _ _ ?_
    rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    rw [← hlin, ← hlin, hE, hE, (F.Di i).adj]

end GlobalTheory.AnVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticLineBundleFrameEqAppellHumbertStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ (e : ∀ m, FrTy y g Φ.jx m) (wP : PrimTy H Xo), Φ.IsAnE e → IsPrim wP → (∀ (m k : ℕ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (eL y g Φ.jx (anFB ty).A.act e wP m) k)) ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (eL y g Φ.jx (anFB ty).A.act e wP 0) (homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) 0 →ₐ[ℂ] ℂ)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x ℂ) 1) := by
  first | exact @GlobalTheory.AnValEL.eL_appellHumbert | exact GlobalTheory.AnValEL.eL_appellHumbert | (intros; apply GlobalTheory.AnValEL.eL_appellHumbert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DatumNsmulEqZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem datum_nsmul_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {k : ℕ} (hk : k ≠ 0) {x : D.La} (h : k • x = 0) : x = 0 := by
  apply D.unimod.1
  ext y
  have h1 : D.EF (k • x) y = 0 := by rw [h, map_zero]; rfl
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h1
  rw [map_zero, LinearMap.zero_apply]
  exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hk)

theorem marking_iso_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (i : Fin F.n), (∀ a, (∃ b, F.t i a = l.M • b) → ∃ b, a = l.M • b) ∧ ∀ b, ∃ a e, b = F.t i a + l.M • e := by
  intro E _ _ _ H Dw l Xo _ σ' g ty F i
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact Nat.lcm_ne_zero hM l.A_pos.ne' (by simpa [Geo.Tor.Level.M'] using hk)
  refine ⟨?_, ?_⟩
  · rintro a ⟨b, hb⟩
    obtain ⟨c, hc⟩ := (F.t_inj i (k • a)).1 ⟨b, by rw [map_nsmul, hb, hk, mul_comm, mul_smul]⟩
    refine ⟨c, sub_eq_zero.1 (datum_nsmul_eq_zero Dw hk0 ?_)⟩
    rw [smul_sub, hc, hk, mul_comm, mul_smul, sub_self]
  · intro b
    obtain ⟨a, e, h⟩ := F.t_surj i b
    exact ⟨a, k • e, by rw [h, hk, mul_smul]⟩

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeterminantBlockProductRenameTorusPolynomial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BlockRen

section Deriv

open scoped ContDiff

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem polyDeriv_eq_sum {θ : W → ℂ} {x : W} (hθ : ContDiffAt ℂ ω θ x) {T : Type}
    (P : MvPolynomial T ℂ) (u : T → W) :
    I2.polyDeriv P u θ x =
      ∑ m ∈ P.support, P.coeff m * mD θ x ((Finsupp.toMultiset m).map u) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1

  have hs : (Finsupp.toMultiset m).map u = (((Finsupp.toMultiset m).toList.map u : List W) : Multiset W) := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  have hlen : ((Finsupp.toMultiset m).toList.map u).length = Multiset.card (Finsupp.toMultiset m) := by
    rw [List.length_map, Multiset.length_toList]
  rw [hs, mD_coe hθ, lD_eq θ x _ hlen]
  congr 1
  funext k
  simp [List.get_eq_getElem]

theorem polyDeriv_rename {θ : W → ℂ} {x : W} (hθ : ContDiffAt ℂ ω θ x) {T κ : Type} (ρ : T → κ)
    (hρ : Function.Injective ρ) (P : MvPolynomial T ℂ) (v : κ → W) :
    I2.polyDeriv (MvPolynomial.rename ρ P) v θ x = I2.polyDeriv P (v ∘ ρ) θ x := by
  classical
  rw [polyDeriv_eq_sum hθ, polyDeriv_eq_sum hθ, MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective hρ h]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain ρ hρ, ← Finsupp.toMultiset_map, Multiset.map_map]

theorem contDiffAt_of_diff [FiniteDimensional ℂ W]
    {F : W → ℂ} (hF : Differentiable ℂ F) (x : W) : ContDiffAt ℂ ω F x := by

  let e : W ≃L[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  have hG : AnalyticOnNhd ℂ (F ∘ e.symm) Set.univ :=
    ReciprocityTheory.AnForm.Osgood.osgood _ Set.univ _ isOpen_univ
      (hF.comp e.symm.differentiable).differentiableOn
  have hA := (hG (e x) (Set.mem_univ _)).comp
    ((e : W →L[ℂ] (Fin (Module.finrank ℂ W) → ℂ)).analyticAt x)
  have hFe : (F ∘ e.symm) ∘ e = F := by
    funext y
    simp
  rw [hFe] at hA
  exact hA.contDiffAt

end Deriv

theorem polyDeriv_scale {J W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {P : MvPolynomial J ℂ} {d : ℕ}
    (hP : P.IsHomogeneous d) (c : ℂ) (u : J → W) (F : W → ℂ) (x : W) :
    I2.polyDeriv P (fun l => c • u l) F x = c ^ d * I2.polyDeriv P u F x := by
  unfold I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_

  have hd : Multiset.card (Finsupp.toMultiset m) = d := by
    have h := hP (MvPolynomial.mem_support_iff.mp hm)
    simp [Finsupp.weight_apply] at h
    rw [Finsupp.card_toMultiset]
    exact h
  rw [ContinuousMultilinearMap.map_smul_univ (c := fun _ => c)]
  have hc : (∏ _k : Fin (Multiset.card (Finsupp.toMultiset m)), c) = c ^ d := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hd]
  rw [hc, smul_eq_mul]
  ring

theorem det_X_isHomogeneous {J K : Type} [CommRing K] (i : ℕ) (f : Fin i → Fin i → J) :
    (Matrix.of fun a b : Fin i => (MvPolynomial.X (f a b) : MvPolynomial J K)).det.IsHomogeneous i := by
  rw [Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun s _ => ?_

  have hprod : (∏ a, (Matrix.of fun a b : Fin i => (MvPolynomial.X (f a b) : MvPolynomial J K)) (s a) a).IsHomogeneous i := by
    have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin i))
      (fun a => (MvPolynomial.X (f (s a) a) : MvPolynomial J K)) (fun _ => 1)
      (fun a _ => MvPolynomial.isHomogeneous_X K _)
    simpa using h
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · rw [h, one_smul]
    exact hprod
  · rw [h, Units.neg_smul, one_smul]
    exact hprod.neg

theorem blockProd_rename : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (K : Type) [Field K] (σ : K →+* ℂ) (P : MvPolynomial (LtN Dw n) K), IsBlockProd P → ∀ (dim : (E →+* ℂ) → ℕ) (rl : (E →+* ℂ) → (E →+* ℂ)) (hd : ∀ τ, Dw.mult τ ≤ dim (rl τ)), Function.Injective rl → P ≠ 0 ∧ P.IsHomogeneous P.totalDegree ∧ ∃ (nb : ℕ) (bs : Fin nb → I2.Block E n dim), I2.Disj bs ∧ I2.DF bs = P.totalDegree ∧ ∀ (t : ℂ) (F : (Fin n → I2.Vsp dim) → ℂ), Differentiable ℂ F → I2.polyDeriv (MvPolynomial.map σ P) (fun ℓ => t • I2.dir ((ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩) : I2.Letter n dim)) F 0 = t ^ P.totalDegree * I2.polyDeriv (I2.P1 bs) I2.dir F 0 := by
  intro E _ _ _ H Dw n K _ σ P hP dim rl hd hrl
  obtain ⟨nb, bs0, hdisj, rfl⟩ := hP
  classical

  have hdeg : (∏ j, (bs0 j).poly K).IsHomogeneous (∑ j, (bs0 j).i * (bs0 j).c) := by
    refine MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => ?_
    exact (det_X_isHomogeneous (K := K) (bs0 j).i
      (fun a b => (⟨(bs0 j).τ, Fin.castLE (bs0 j).hi a, (bs0 j).col b⟩ : LtN Dw n))).pow (bs0 j).c
  have hne : (∏ j, (bs0 j).poly K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => GlobalTheory.BlockThInhab.poly_ne_zero Dw n K (bs0 j)
  have htot : (∏ j, (bs0 j).poly K).totalDegree = ∑ j, (bs0 j).i * (bs0 j).c :=
    hdeg.totalDegree hne

  let bs : Fin nb → I2.Block E n dim := fun j =>
    ⟨rl (bs0 j).τ, (bs0 j).i, (bs0 j).hi.trans (hd _), (bs0 j).c, (bs0 j).hc, (bs0 j).col, (bs0 j).col_inj⟩
  refine ⟨hne, htot ▸ hdeg, nb, bs, ?_, ?_, ?_⟩
  · intro j j' hjj' a a'
    exact hdisj j j' hjj' a a'
  · rw [htot]
    rfl
  · intro t F hF
    rw [htot]
    let ρ : LtN Dw n → I2.Letter n dim := fun ℓ => (ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩)
    have hρ : Function.Injective ρ := by
      rintro ⟨τ, a, b⟩ ⟨τ', a', b'⟩ h
      simp only [ρ, Prod.mk.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h1, h2⟩ := h
      obtain rfl := hrl h1
      have h3 := Fin.castLE_injective (hd τ) (eq_of_heq h2)
      subst h3
      rfl

    have hP1 : MvPolynomial.rename ρ (MvPolynomial.map σ (∏ j, (bs0 j).poly K)) = I2.P1 bs := by
      simp only [map_prod, I2.P1]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [Bk.poly, I2.Block.poly, map_pow, RingHom.map_det, AlgHom.map_det]
      congr 2
      ext a b
      simp [ρ, bs]
    have hhom : (I2.P1 bs).IsHomogeneous (∑ j, (bs0 j).i * (bs0 j).c) := by
      refine MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => ?_
      exact (det_X_isHomogeneous (K := ℂ) (bs0 j).i
        (fun a b => (((bs0 j).col b, ⟨rl (bs0 j).τ, Fin.castLE ((bs0 j).hi.trans (hd _)) a⟩) : I2.Letter n dim))).pow (bs0 j).c
    refine (polyDeriv_rename (contDiffAt_of_diff hF 0) ρ hρ _ (fun l => t • I2.dir l)).symm.trans ?_
    rw [hP1]
    exact polyDeriv_scale hhom t I2.dir F 0

end GlobalTheory.BlockRen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticDataUnitFrameFramedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticData_unitFrame_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ k (x : (U.X k).dom), IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ (W : UW U) (Dc : Dic Dw c σ (U.X k) W.g Dw.p n a) (A : AnFib (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x)) (θ : (Fin W.g → ℂ) → ℂ) (v : TF n W.g) (κ : ℂ), Dc.e = W.e ∧ W.g = fdeg E * r ∧ (H.w0 : E) + cc (H.w0 : E) = 1 ∧ SelfD (U.X k) (U.X k).Λ ∧ IsMark l (U.X k).Λ (W.mark k) ∧ A.Marked (W.mark k) ∧ A.Reads 1 (unC U k x).s θ ∧ IsTheta1 (U.X k) Dc.bas Dc.idx (H.w0 : E) x.1 (U.X k).Λ θ ∧ MeanOne (U.X k) Dc.bas Dc.idx x.1 (U.X k).Λ θ ∧ IsVac (U.X k) Dc.bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v ∧ ∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA (U.X k) Dc.bas Dc.idx v x.1 z := by
  first | exact @GlobalTheory.Dict.VSetup.exists_setup | exact GlobalTheory.Dict.VSetup.exists_setup | (intros; apply GlobalTheory.Dict.VSetup.exists_setup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatSplitIsotropicGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem map_sum_eq_prod_ofFn_of_add_eq_mul {A G : Type} [AddCommGroup A] [Group G] (ev : A → G)
    (h : ∀ a b, ev (a + b) = ev a * ev b) :
    ∀ (n : ℕ) (f : Fin n → A), ev (∑ j, f j) = (List.ofFn fun j => ev (f j)).prod := by
  have h0 : ev 0 = 1 := by
    have := h 0 0
    rw [add_zero] at this
    exact left_eq_mul.mp this
  intro n
  induction n with
  | zero => intro f; simp [h0]
  | succ n ih => intro f; rw [Fin.sum_univ_succ, h, ih, List.ofFn_succ, List.prod_cons]

theorem map_nsmul_eq_pow_of_add_eq_mul {A G : Type} [AddCommGroup A] [Group G] (ev : A → G)
    (h : ∀ a b, ev (a + b) = ev a * ev b) (a : A) (k : ℕ) : ev (k • a) = ev a ^ k := by
  induction k with
  | zero =>
    have := h 0 0
    rw [add_zero] at this
    simpa using left_eq_mul.mp this
  | succ k ih => rw [succ_nsmul, h, ih, pow_succ]

theorem exists_faithfullyFlat_split_Zh : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo (spMap φ ≫ x0) z := by
  intro hL E _ _ _ H Dw l Xo S _ x0 n Λ N hU hN hle
  obtain ⟨B, iB, φ, ev, hff, hadd, hsm, hk, hinj⟩ :=
    _root_.GlobalTheory.exists_faithfullyFlat_linear_level hL E H Dw l Xo S x0 (N ^ 2) (pow_pos hN 2)
  obtain ⟨zz, hz, hzi, -⟩ := _root_.GlobalTheory.ZCount.exists_class_representatives E H Dw n Λ N hU hN hle
  refine ⟨B, iB, φ, fun i b => ev (zz i b), hff, fun i => ⟨fun b => ?_, ?_⟩, ?_⟩
  · rw [← map_nsmul_eq_pow_of_add_eq_mul ev hadd, hk]
  · intro mu hmu cm hcm i'
    have h1 := hz i mu hmu cm hcm i'
    simp only [← hsm]
    rw [← map_sum_eq_prod_ofFn_of_add_eq_mul ev hadd]
    obtain ⟨y, hy⟩ := h1
    rw [hy]
    exact hk y
  · intro k _ ψ g hg i i' hii
    apply hzi
    intro b
    apply hinj k ψ
    have := congrArg (fun f => f.left) (congrFun hii b)
    simp only [Over.comp_left, hg] at this
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsOrthoFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem exists_ortho_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.Data E r), ∀ x ∈ X.dom, ∃ b ∈ FD.Bor X.Ψ r, FD.rmul x b ∈ X.dom ∧ X.IsOrtho (FD.rmul x b) ∧ (∀ τ i, ‖FD.dmin X.Gm (FD.rmul x b) τ i‖ = 1) ∧ (∀ th, I2.phiFD X th (FD.rmul x b) = I2.phiFD X th x) ∧ ∀ (la : FD.Wt X.Ψ r) (P : FD.Frame X.Ψ r → ℂ), X.IsSec la P → X.pnorm la P x = ‖P (FD.rmul x b)‖ := by
  intro E _ _ _ r X x hx
  have hb := FD.FrameDegreeData.bOf_mem X hx
  have ho := FD.FrameDegreeData.ortho_bOf X hx
  have hd : ∀ τ i, ‖FD.dmin X.Gm (FD.rmul x (FD.FrameDegreeData.bOf X x)) τ i‖ = 1 := by
    intro τ i
    unfold FD.dmin
    rw [ho τ, FD.FrameDegreeData.lminor_diagonal, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Complex.norm_real]
    rcases FD.FrameDegreeData.sgn_sq X.p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) j : Fin r) with h | h <;>
      rw [h] <;> simp
  have hl : X.la1 (FD.rmul x (FD.FrameDegreeData.bOf X x)) = X.la1 x := by
    unfold FD.Data.la1
    rw [ReciprocityTheory.ChartRestriction.G.AR.Inst.firstMinimumSq_rightBorel X hx hb]
  refine ⟨_, hb, FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb, ho, hd, fun th => ?_, fun la P hP => ?_⟩
  · unfold I2.phiFD
    rw [hl]
  · rw [← FD.FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx _ hb]
    unfold FD.Data.pnorm
    simp only [norm_div, hd, div_one, Real.one_rpow, Finset.prod_const_one, _root_.mul_one]

end GlobalTheory.AnVal
end

