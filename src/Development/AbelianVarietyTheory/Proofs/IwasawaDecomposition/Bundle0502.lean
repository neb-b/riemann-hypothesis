module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmLettersIsLieBasisAlongArc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankFixedSubmoduleComplexification
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartDirectionalDerivativeRegularCoordinate
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.ProjSpace
open scoped Matrix

namespace GlobalTheory.ProjPos

theorem leviV_log_pos {n N : ℕ} {w : Fin N → V n → ℂ} {x : V n} (hC : ∀ a, ContDiffAt ℂ 2 (w a) x) {j : Fin N}
    (hj : w j =ᶠ[𝓝 x] fun _ => 1) (ξ : V n) (h : ¬ ∀ a, fderiv ℂ (w a) x ξ = 0) :
    0 < (leviV n (fun z => ((Real.log (∑ a, ‖w a z‖ ^ 2) : ℝ) : ℂ)) x ξ.ofLp).re := by
  have hD : ∀ a, DifferentiableAt ℂ (w a) x := fun a => (hC a).differentiableAt (by simp)
  have h1 : w j x = 1 := hj.eq_of_nhds
  have hne : (fun i => w i x) ≠ 0 := fun e => one_ne_zero (h1.symm.trans (congrFun e j))
  have e1 : (fun z => ((Real.log (∑ a, ‖w a z‖ ^ 2) : ℝ) : ℂ)) =
      fun y => ((Real.log (sqNorm (fun i => w i y)) : ℝ) : ℂ) := by
    funext y; simp [sqNorm, Complex.normSq_eq_norm_sq]
  have hJ (a) : (wJac n N w x *ᵥ ξ.ofLp) a = fderiv ℂ (w a) x ξ := by
    have hξ : ξ = ∑ j, ξ.ofLp j • bas n j := by
      ext i
      simp [bas, Pi.single_apply]
    conv_rhs => rw [hξ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [wJac, Matrix.mulVec, dotProduct, wd_of_differentiableAt (hD a), map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e1, leviLogNormSq n N w x ξ.ofLp hC hne, Complex.ofReal_re]
  refine div_pos (sqNorm_pos fun hz => h fun a => ?_) (sqNorm_pos hne)
  rw [projPerp_mulVec, sub_eq_zero] at hz
  have h2 := congrFun hz j
  rw [hJ, hj.fderiv_eq, Pi.smul_apply, h1, smul_eq_mul, mul_one] at h2
  have h3 := congrFun hz a
  rw [hJ, ← h2] at h3
  simpa using h3

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {c : AlgChart p σ D} {y : CxPts p σ} {W : Y.Opens} {ξ : V D}


variable (c y ξ) in
def dirDer (f : Γ(Y, W)) : ℂ := fderiv ℂ (ev p σ W f ∘ c.e.symm) (c.e y) ξ

theorem dirDer_add (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) (f g : Γ(Y, W)) :
    dirDer c y ξ (f + g) = dirDer c y ξ f + dirDer c y ξ g := by
  have e : ev p σ W (f + g) ∘ c.e.symm = (ev p σ W f ∘ c.e.symm) + (ev p σ W g ∘ c.e.symm) :=
    funext fun v => ev_add _ _ _
  simp only [dirDer, e, fderiv_add (c.differentiableAt_ev f hy hW) (c.differentiableAt_ev g hy hW)]
  rfl

theorem dirDer_mul (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) (f g : Γ(Y, W)) :
    dirDer c y ξ (f * g) = ev p σ W f y * dirDer c y ξ g + ev p σ W g y * dirDer c y ξ f := by
  have e : ev p σ W (f * g) ∘ c.e.symm = (ev p σ W f ∘ c.e.symm) * (ev p σ W g ∘ c.e.symm) :=
    funext fun v => ev_mul _ _ _
  simp only [dirDer, e, fderiv_mul (c.differentiableAt_ev f hy hW) (c.differentiableAt_ev g hy hW),
    Function.comp_apply, c.e.left_inv hy]
  rfl

theorem dirDer_const (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) {f : Γ(Y, W)} {a : ℂ}
    (h : ∀ z ∈ ptsIn p σ W, ev p σ W f z = a) : dirDer c y ξ f = 0 := by
  have e : ev p σ W f ∘ c.e.symm =ᶠ[𝓝 (c.e y)] fun _ => a :=
    eventually_of_mem ((isOpen_over c.e (isOpen_ptsIn W)).mem_nhds (mem_over c.e hy hW)) fun v hv => h _ hv.2
  rw [dirDer, e.fderiv_eq]
  simp

theorem dirDer_res {W' : Y.Opens} (h : W' ≤ W) (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W') (f : Γ(Y, W)) :
    dirDer c y ξ (resG Y h f) = dirDer c y ξ f := by
  have e : ev p σ W' (resG Y h f) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] ev p σ W f ∘ c.e.symm :=
    eventually_of_mem ((isOpen_over c.e (isOpen_ptsIn W')).mem_nhds (mem_over c.e hy hW))
      fun v hv => ev_res h hv.2 _
  simp only [dirDer, e.fderiv_eq]

theorem chartDirectionalDerivativeRegular_coordinate (hy : y ∈ c.e.source) (a : Fin D) : dirDer c y ξ (c.x a) = ξ a := by
  have e : ev p σ _ (c.x a) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] (EuclideanSpace.proj (𝕜 := ℂ) a : V D →L[ℂ] ℂ) :=
    eventually_of_mem (c.e.open_target.mem_nhds (c.e.map_source hy)) fun v hv =>
      (c.apply_eq _ (c.e.map_target hv) a).symm.trans (by rw [c.e.right_inv hv]; rfl)
  rw [dirDer, e.fderiv_eq, ContinuousLinearMap.fderiv]
  rfl

theorem eq_zero_of_dirDer (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) (hU : IsAffineOpen W)
    (h0 : ∀ f : Γ(Y, W), dirDer c y ξ f = 0) : ξ = 0 := by
  ext b
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := c.U) ⟨_, mem_ptsIn.1 (c.source_subset hy)⟩ (mem_ptsIn.1 hW)
  have hB : y ∈ ptsIn p σ (Y.basicOpen h) := mem_ptsIn.2 hh
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG Y hhW (c.x b))
  have ha' : resG Y hhW (c.x b) * resG Y (Y.basicOpen_le h) (h ^ n) = resG Y (Y.basicOpen_le h) a := by
    rw [map_pow]; exact ha
  have e := congrArg (dirDer c y ξ) ha'
  rw [dirDer_mul hy hB, dirDer_res _ hy hB, dirDer_res _ hy hB, dirDer_res _ hy hB, h0, h0, chartDirectionalDerivativeRegular_coordinate hy, mul_zero,
    zero_add, ev_res _ hB, ev_eq hW, map_pow, ← ev_eq] at e
  exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero n ((mem_ptsIn_basicOpen hW h).1 hB))

variable {N : ℕ} (i : Y ⟶ PSpace k N) (hi : i ≫ PSpace.str k N = p)


include hi in
theorem eq_zero_of_dirDer_ratio [IsClosedImmersion i] (hy : y ∈ c.e.source) {j : Fin (N + 1)}
    (hW : y ∈ ptsIn p σ (i ⁻¹ᵁ chart k N j)) (h0 : ∀ a, dirDer c y ξ (i.app _ (ratio k N j a)) = 0) : ξ = 0 := by
  refine eq_zero_of_dirDer hy hW ((isAffineOpen_chart k N j).preimage i) fun f => ?_
  obtain ⟨g, rfl⟩ := i.app_surjective _ (isAffineOpen_chart k N j) f
  obtain ⟨P, rfl⟩ := aeval_ratio_surjective k N j g
  have hm : ∀ z : CxPts p σ, (PtsOver.map i hi _ z).1 = z.1 ≫ i := fun _ => rfl
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine dirDer_const hy hW (a := σ a) fun z hz => ?_
    rw [← ev_of_comp hm, MvPolynomial.aeval_C]
    exact ev_algX ((mem_ptsIn_preimage hm).1 hz) a
  | add P Q hP hQ => rw [map_add (f := _), map_add (f := _), dirDer_add hy hW, hP, hQ, add_zero]
  | mul_X P a hP => rw [map_mul, map_mul, dirDer_mul hy hW, hP, MvPolynomial.aeval_X, h0, mul_zero, mul_zero, add_zero]

theorem fubiniStudy_weight_pullback_chart_formula (j : Fin (N + 1)) (z : CxPts p σ) :
    ((ProjAn.fsO1 k σ N).pull i hi).φ (fun _ => j) z =
      Real.log (∑ a, ‖ev p σ (i ⁻¹ᵁ chart k N j) (i.app _ (ratio k N j a)) z‖ ^ 2) := by
  have hm : ∀ z : CxPts p σ, (PtsOver.map i hi _ z).1 = z.1 ≫ i := fun _ => rfl
  refine (Weight.pull_φ _ _ _ _ _).trans ((Weight.fsBasis_φ _ _ _ _ _ _ _).trans
    (congrArg _ (Finset.sum_congr rfl fun a _ => ?_)))
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← ev_of_comp hm]
  rfl

theorem fubiniStudy_weight_pullback_isSmooth (R : AnRead p σ D) : ((ProjAn.fsO1 k σ N).pull i hi).IsSmooth R :=
  Weight.IsSmooth.pull (R := .all _ σ N) (Weight.isSmooth_fsBasis _ _ _ _ _) i hi R

theorem fubiniStudy_weight_pullback_closed_immersion_strictPos [IsClosedImmersion i] (R : AnRead p σ D) :
    ((ProjAn.fsO1 k σ N).pull i hi).StrictPos R := by
  refine (fubiniStudy_weight_pullback_isSmooth i hi R).strictPos_of_exists fun y => ?_
  obtain ⟨l, hy⟩ := R.cover y
  obtain ⟨j, hj⟩ := exists_mem_chart k N (i (y.1 (IsLocalRing.closedPoint ℂ)))
  have hW : y ∈ ptsIn p σ (i ⁻¹ᵁ chart k N j) := mem_ptsIn.2 hj
  set c := R.chart l
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (i ⁻¹ᵁ chart k N j))
  have hn := ho.mem_nhds (mem_over c.e hy hW)
  refine ⟨c, fun _ => j, hy, mem_ptsIn.2 (Set.mem_iInter.2 fun _ => hj), fun ξ hξ => ?_⟩
  simp only [AlgChart.levi, fubiniStudy_weight_pullback_chart_formula]
  refine leviV_log_pos (w := fun a => ev p σ (i ⁻¹ᵁ chart k N j) (i.app _ (ratio k N j a)) ∘ c.e.symm)
    (fun a => ((contDiffOn_of_differentiableOn D _ _ ho (c.holo _ _)).contDiffAt hn).of_le
      (WithTop.coe_le_coe.2 le_top)) (j := j) (eventually_of_mem hn fun v hv => ?_) (WithLp.toLp 2 ξ) fun h => ?_
  · rw [Function.comp_apply, ratio, ratioOn_self, map_one, ev_eq hv.2, map_one]
  · exact hξ (congrArg WithLp.ofLp (eq_zero_of_dirDer_ratio i hi hy hW h))

end GlobalTheory.ProjPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantVectorsLieBasisOfComplexArc
section
noncomputable section

namespace GlobalTheory.CuspFromBasis

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
open Matrix GlobalTheory.LieEigen GlobalTheory.ConstBasis
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)

theorem exists_comb_of_type {I : Type} {m : I → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : I, Fin (m τ)) (τ : I) {w : Fin g → ℂ}
    (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∃ cf : Fin (m τ) → ℂ, w = ∑ k, cf k • (Pi.single (e.symm ⟨τ, k⟩) 1 : Fin g → ℂ) := by
  refine ⟨fun k => w (e.symm ⟨τ, k⟩), funext fun j => ?_⟩
  obtain ⟨⟨τ', i⟩, rfl⟩ := e.symm.surjective j
  rw [Finset.sum_apply]
  by_cases h : τ' = τ
  · subst h
    rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [Pi.smul_apply, Pi.single_eq_of_ne (by simpa using hk.symm), smul_zero]) (by simp)]
    simp
  · have h₀ : w (e.symm ⟨τ', i⟩) = 0 := by
      by_contra h₁
      exact h (by simpa using hw _ h₁)
    rw [h₀]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h₁ => h (congrArg Sigma.fst (e.symm.injective h₁))), smul_zero]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i j, z τ i j ≠ 0 → (Uw.e j).1 = τ) → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ArcBasis W (fun τ => σ.comp (embK c τ)) e := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw O _ β Y a χ W Ha e z hσ hz he
  have hG := GlobalTheory.ArcCM.known_holds.laws.globalFns
  obtain ⟨g, e₀, v, M, hev, hv, hu, hM⟩ := ConstLie.exists_const_basis hG E H Dw l Xo c O β Y ℂ _ a χ W
  have lin := ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y ℂ _ a χ W
  obtain ⟨an₁, an₂, an₃, an₄⟩ := ExpTan.anVec_bijective hG E H Dw l Xo c σ O β Y a χ W _ _ _ Ha
  have := flat_of_injective ℂ (PowerSeries ℂ) PowerSeries.C_injective
  let ρ : (E →+* ℂ) → 𝓞 E → ℂ := fun τ x => σ (embK c τ x)
  let M' : 𝓞 E → Matrix (Fin g) (Fin g) (PowerSeries ℂ) := fun x => (M x).map (PowerSeries.C (R := ℂ))
  have hM' : ∀ x i, IsLieComb (M' x i) v (v i ≫ W.t.act.act x) := hM
  choose zz hzz using fun i => (an₁ _ (hev i).1).exists
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin Uw.g → ℂ) := Fintype.linearCombination ℂ zz
  have comb : ∀ u ν, GtComb u e₀ ν ↔ AnVec Ha ν (L u) := fun u ν => an₄ g u e₀ zz ν hzz
  have img : ∀ u ν, AnVec Ha ν (L u) → LieImg W ν (prodPts (fun j => PowerSeries.C (R := ℂ) (u j)) v) :=
    fun u ν h => (lin g _ e₀ _ v _ (fun i => (hev i).2) ((comb u ν).2 h)).2 ((Chart.isLieComb_iff _ _ _).2 rfl)
  have inj : Function.Injective L := fun u u' h => by
    obtain ⟨ν, hν, -⟩ := an₂ (L u)
    exact (hu ν (an₃ _ _ hν)).unique ((comb _ _).2 hν) ((comb _ _).2 (h ▸ hν))
  have surj : Function.Surjective L := fun w => by
    obtain ⟨ν, hν, -⟩ := an₂ w
    obtain ⟨u, h, -⟩ := hu ν (an₃ _ _ hν)
    exact ⟨u, (an₁ ν (an₃ _ _ hν)).unique ((comb _ _).1 h) hν⟩
  have cm : ∀ x (u : Fin g → ℂ), (fun j => PowerSeries.C (R := ℂ) (u j)) ᵥ* M' x =
      fun j => PowerSeries.C (R := ℂ) ((u ᵥ* M x) j) := fun x u =>
    funext fun i => ((PowerSeries.C (R := ℂ)).map_vecMul (M x) u i).symm
  have act : ∀ (x : 𝓞 E) u, L (u ᵥ* M x) = fun k => Formalism.L2.PjFree.relab c σ (Uw.e k).1 (x : E) * L u k := fun x u => by
    by_cases hx : x = 0
    · subst hx
      obtain ⟨ρ', hρ'⟩ := exists_action hv W.t.act
      have h₁ := prodPts_injective hv ((hρ' 0 (fun j => PowerSeries.C (R := ℂ) (u j))).trans
        (prodPts_act hv hM' 0 _))
      rw [cm, map_zero] at h₁
      have h₂ : u ᵥ* M 0 = 0 := funext fun j => PowerSeries.C_injective (R := ℂ)
        ((congrFun h₁ j).symm.trans (map_zero _).symm)
      rw [h₂, map_zero]
      funext k
      simp
    · obtain ⟨ν, hν, -⟩ := an₂ (L u)
      obtain ⟨u₁, h₁⟩ := surj fun k => Formalism.L2.PjFree.relab c σ (Uw.e k).1 (x : E) * L u k
      obtain ⟨ν₁, hν₁, -⟩ := an₂ (L u₁)
      have h₂ := ArcType.act_eq Ha hx hν (img _ _ hν) (isTangent_prodPts hv.1 _) (h₁ ▸ hν₁) (img _ _ hν₁)
        (isTangent_prodPts hv.1 _)
      rw [prodPts_act hv hM', cm] at h₂
      have h₃ : u₁ = u ᵥ* M x := funext fun j => PowerSeries.C_injective (R := ℂ)
        (congrFun (prodPts_injective hv h₂) j)
      rw [← h₃, h₁]
  have typ : ∀ τ w, (∀ x, w ᵥ* M x = ρ τ x • w) ↔ ∀ j, L w j ≠ 0 → (Uw.e j).1 = τ := fun τ w => by
    refine ⟨fun h j hj => ?_, fun h x => inj ?_⟩
    · refine (GlobalTheory.Relab.relab_good E H l c σ hσ).1.1 ?_
      refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => ?_)
      have h₁ := congrFun (act x w) j
      rw [h x, map_smul] at h₁
      exact mul_right_cancel₀ hj h₁.symm
    · rw [act, map_smul]
      funext j
      by_cases hj : L w j = 0
      · simp [hj]
      · rw [h j hj]; rfl
  choose u hu using fun τ k => surj (z τ k)
  have imgu : ∀ τ k, LieImg W (e τ k) (prodPts (fun j => PowerSeries.C (R := ℂ) (u τ k j)) v) := fun τ k =>
    img _ _ ((hu τ k).symm ▸ he τ k)
  have eig : ∀ τ k x, u τ k ᵥ* M x = ρ τ x • u τ k := fun τ k =>
    (typ τ _).2 ((hu τ k).symm ▸ (hz τ).2 k)
  have key : ∀ τ (w : Fin g → PowerSeries ℂ), (∀ x, w ᵥ* M' x = PowerSeries.C (R := ℂ) (ρ τ x) • w) →
      ∃! cf : Fin (Dw.mult τ) → PowerSeries ℂ, w = ∑ k, cf k • (fun j => PowerSeries.C (R := ℂ) (u τ k j)) := by
    intro τ
    refine (commonEigenvectors_flat_baseChange ℂ (𝓞 E) g _ M (ρ τ)).1 ℂ (u τ) (eig τ) ?_ (PowerSeries ℂ)
    have : ∀ w : Fin g → ℂ, (∀ x, w ᵥ* M x = ρ τ x • w) →
        ∃! cf : Fin (Dw.mult τ) → ℂ, w = ∑ k, cf k • u τ k := fun w hw => by
      refine (existsUnique_congr fun cf => ?_).1 (LetterBasis.existsUnique_comb (hz τ).1
        (fun k => exists_comb_of_type Uw.e τ ((hz τ).2 k)) (exists_comb_of_type Uw.e τ ((typ τ w).1 hw)))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← inj.eq_iff, map_sum]
      simp only [map_smul, hu]
    simpa using this
  refine ⟨_, imgu, fun τ => ⟨fun k => ⟨isTangent_prodPts hv.1 _, fun x => ?_⟩, fun w hw he => ?_⟩⟩
  · rw [eig_iff hv hM']
    exact vecMul_map _ (eig τ k x)
  · obtain ⟨d, rfl⟩ := exists_prodPts hv hw
    refine (existsUnique_congr fun cf => ?_).1 (key τ d fun x => (eig_iff hv hM' _ _ _).1 (he x))
    rw [Chart.isLieComb_iff, prodPts_prodPts hv.1, (prodPts_injective hv).eq_iff]

end GlobalTheory.CuspFromBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAtScalar
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.ThetaScalar

open GlobalTheory.HolGen Formalism.L2.PjFree GlobalTheory.Frames

theorem continuousAt_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (x : (Fin m → ℂ) → (Fin T.m → ℂ)) (a : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → IsHolPeriods (F.Di k) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) B P → (∀ b ∈ B, x b ∈ T.co ⁻¹' (M.X k).dom ∧ T.Pf (T.co (x b)) = P b ∧ IsThetaPt T (x b) (a b) (y b)) → ∀ b₀ ∈ B, ContinuousAt x b₀ → ContinuousAt a b₀ := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T A _ _ yA m B ψ y P x a hB hψ hb hP hx b₀ hb₀ hx₀
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hxu : ∀ b ∈ B, (y b).x = F.u k (P b) := fun b h => by
    rw [← (hx b h).2.1]
    exact (hx b h).2.2.1
  let φ : (Fin m → ℂ) → (A →+* ℂ) := fun b => (ψ b).toRingHom
  have hux : ∀ b ∈ B, F.u k (P b) = (y b).x := fun b h => (hxu b h).symm
  obtain ⟨pm₀, p₁, p₂, p₃⟩ := (hb b₀ hb₀).2.2
  obtain ⟨e₀, j, hne⟩ := exists_val_ne hT (φ b₀) yA.x (y b₀).x _ (hux b₀ hb₀) yA.s (y b₀).s pm₀ p₁ p₂ p₃ (y b₀).gen
  obtain ⟨w₀, rfl⟩ := F.ex_onto k _ (hP.1 b₀ hb₀) e₀
  have hq₁ : ∀ b ∈ B, ∃ q : Sp ℂ ⟶ Gx yA.x, q ≫ Formalism.L2.PjFree.gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ Formalism.L2.PjFree.gxSnd yA.x = spMap (φ b) := fun b h =>
    exists_pt _ _ _ (((hb b h).1.symm.trans (hux b h).symm).trans (Over.w (F.ex k (P b) w₀)).symm)
  have hq₂ : ∀ b, ∃ q : Sp ℂ ⟶ Gx yA.x, b ∈ B → q ≫ Formalism.L2.PjFree.gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ Formalism.L2.PjFree.gxSnd yA.x = spMap (φ b) := fun b => by
    by_cases h : b ∈ B
    · exact (hq₁ b h).imp fun _ h' _ => h'
    · exact ⟨(hq₁ b₀ hb₀).choose, fun h' => absurd h' h⟩
  choose q hq using hq₂
  have hι : Differentiable ℂ (fun b : Fin m → ℂ => ((b, w₀) : (Fin m → ℂ) × (Fin g → ℂ))) := by fun_prop
  have hol : IsHolTo B q := by
    refine HolPullback.isHolTo_of_components _ B _ _ _ _ (Formalism.L2.PjFree.gxSnd yA.x) (Formalism.L2.PjFree.gxFst yA.x) yA.x Xo.univ.t.G.hom q
      (IsPullback.of_hasPullback yA.x Xo.univ.t.G.hom) hB ?_ ?_
    · exact LocLift.isHolTo_congr (ThetaValueCont.isHolTo_spMap hB φ hψ) fun b h => (hq b h).2
    · exact LocLift.isHolTo_congr (LocLift.isHolTo_comp (F.hol k _ B _ hB hP).2 hB hι.differentiableOn
        fun b h => ⟨h, trivial⟩) fun b h => (hq b h).1
  have hW := (hol ((Gx yA.x).basicOpen (yA.s.f (fun _ => j))) 0).1
  set W := {b ∈ B | ⊤ ≤ q b ⁻¹ᵁ (Gx yA.x).basicOpen (yA.s.f (fun _ => j))} with hWd
  have hb₀W : b₀ ∈ W := ⟨hb₀, (top_le_preimage_basicOpen_iff _ _ _).2 (hne _ (hq b₀ hb₀).1 (hq b₀ hb₀).2)⟩
  have vnz : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) ≠ 0 := fun b h =>
    (top_le_preimage_basicOpen_iff _ _ _).1 h.2
  have m₁ : ∀ b ∈ W, ⊤ ≤ q b ⁻¹ᵁ (PPx yA.x).U (fun _ => j) := fun b h =>
    top_le_preimage_of_valAt'_ne_zero _ (vnz b h)
  have m₂ : ∀ b ∈ W, ⊤ ≤ (F.ex k (P b) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [← (hq b h.1).1]
    exact (chart_iff _ _ _).1 (m₁ b h)
  have m₃ : ∀ b ∈ W, ⊤ ≤ (F.ex k (T.Pf (T.co (x b))) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [(hx b h.1).2.1]
    exact m₂ b h
  have hO : IsOpen (T.co ⁻¹' (M.X k).dom) := (FourierCoefficientDomain.isOpen_dom (M.X k)).preimage T.co.continuous
  have hθ := (ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).2 T.m _ T.h T.ta hO
    (fun b h => ⟨(T.norm b h).2.1, (T.norm b h).2.2.1⟩) T.hol
  have hκ : ContinuousWithinAt (fun b : Fin m → ℂ => ((x b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) W b₀ :=
    (hx₀.prodMk continuousAt_const).continuousWithinAt
  have d₁ : ContinuousWithinAt (fun b => thetaChar (T.ta (x b)) T.c₁ T.c₂ (T.h (x b) *ᵥ w₀)) W b₀ :=
    ContinuousWithinAt.comp (f := fun b : Fin m → ℂ => ((x b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin T.m → ℂ) × (Fin g → ℂ) => thetaChar (T.ta bz.1) T.c₁ T.c₂ (T.h bz.1 *ᵥ bz.2))
      (hθ.continuousOn _ ⟨(hx b₀ hb₀).1, trivial⟩) hκ fun b h => ⟨(hx b h.1).1, trivial⟩
  have d₂ : ContinuousWithinAt (fun b => T.fr j (x b, w₀)) W b₀ :=
    ContinuousWithinAt.comp (f := fun b : Fin m → ℂ => ((x b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) (g := T.fr j)
      ((T.fr_hol j).continuousOn _ ⟨(hx b₀ hb₀).1, m₃ b₀ hb₀W⟩) hκ fun b h => ⟨(hx b h.1).1, m₃ b h⟩
  have d₃ : DifferentiableOn ℂ (fun b => valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j))) W :=
    (hol _ _).2.mono fun b h => ⟨h.1, m₁ b h⟩
  have key : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) =
      a b * (thetaChar (T.ta (x b)) T.c₁ T.c₂ (T.h (x b) *ᵥ w₀) * T.fr j (x b, w₀)) := fun b h => by
    obtain ⟨-, -, pm, p₁, p₂, p₃⟩ := hb b h.1
    obtain ⟨pt, e₁, e₂⟩ := exists_pt (R := ℂ) (y b).x (𝟙 _) (F.ex k (P b) w₀).left
      (((Category.id_comp _).trans (hxu b h.1)).trans (Over.w (F.ex k (P b) w₀)).symm)
    have e₁' : pt ≫ Formalism.L2.PjFree.gxFst (y b).x = (F.ex k (T.Pf (T.co (x b))) w₀).left := by
      rw [(hx b h.1).2.1]
      exact e₁
    rw [← mul_assoc]
    refine Eq.trans ?_ ((hx b h.1).2.2.2.2 j w₀ pt e₁' e₂ (m₃ b h))
    refine (val_pull (φ b) yA.x (y b).x yA.s (y b).s pm p₁ p₂ p₃ _ pt (q b)
      ((hq b h.1).1.trans e₁.symm) e₂ (hq b h.1).2 ((chart_iff _ _ _).2 ?_)).symm
    rw [e₁]
    exact m₂ b h
  have nz : ∀ b ∈ W, thetaChar (T.ta (x b)) T.c₁ T.c₂ (T.h (x b) *ᵥ w₀) * T.fr j (x b, w₀) ≠ 0 := fun b h =>
    right_ne_zero_of_mul (key b h ▸ vnz b h)
  have d : ContinuousWithinAt a W b₀ :=
    ((d₃.continuousOn b₀ hb₀W).mul ((d₁.mul d₂).inv₀ (nz b₀ hb₀W))).congr
      (fun b h => ((mul_inv_eq_iff_eq_mul₀ (nz b h)).2 (key b h)).symm)
      ((mul_inv_eq_iff_eq_mul₀ (nz b₀ hb₀W)).2 (key b₀ hb₀W)).symm
  exact d.continuousAt (hW.mem_nhds hb₀W)

end GlobalTheory.ThetaScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseFieldMultipleOfNthRootComplexification
section
open scoped TensorProduct

namespace GlobalTheory.KeyFourth

theorem exists_eq_smul_of_pow_eq_pow {R : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R]
    {n : ℕ} (hn : 0 < n) {x y : R} (h : x ^ n = y ^ n) : ∃ z : ℂ, x = z • y := by
  have : NeZero n := ⟨hn.ne'⟩
  have h0 := Complex.isPrimitiveRoot_exp n hn.ne'
  have h1 := h0.map_of_injective (algebraMap ℂ R).injective
  have h2 := h1.pow_sub_pow_eq_prod_sub_mul x y hn
  rw [h, sub_self] at h2
  obtain ⟨ζ, hζ, hz⟩ := Finset.prod_eq_zero_iff.1 h2.symm
  rw [Polynomial.mem_nthRootsFinset hn] at hζ
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hζ
  refine ⟨Complex.exp (2 * Real.pi * Complex.I / n) ^ i, ?_⟩
  rw [Algebra.smul_def, map_pow, hi]
  exact sub_eq_zero.1 hz

theorem exists_eq_smul_pow_of_pow_eq_tmul :
    ∀ (K : Type) [Field K] [Algebra K ℂ] (A : Type) [CommRing A] [Algebra K A]
      [IsDomain (ℂ ⊗[K] A)] (n : ℕ) (w : ℂ ⊗[K] A) (C : ℂ) (u : A), 0 < n → C ≠ 0 → u ≠ 0 →
      w ^ n = C ⊗ₜ[K] u → ∃ (a : K) (b : A), a ≠ 0 ∧ u = a • b ^ n := by
  intro K _ _ A _ _ _ n w C u hn hC hu hw
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : ℂ) ≠ 0)
  let T : ℂ ⊗[K] A →ₗ[K] A := (TensorProduct.lid K A).toLinearMap ∘ₗ LinearMap.rTensor A f
  have hT : ∀ (c : ℂ) (a : A), T (c ⊗ₜ a) = f c • a := fun c a => by simp [T]
  have hne : ∀ (c : ℂ) (a : A), c ≠ 0 → a ≠ 0 → c ⊗ₜ[K] a ≠ 0 := by
    intro c a hc ha h
    have h1 : (1 : ℂ) ⊗ₜ[K] a = 0 := by
      have := congrArg (fun t : ℂ ⊗[K] A => c⁻¹ • t) h
      simpa [TensorProduct.smul_tmul', hc] using this
    have h2 := hT 1 a
    rw [h1, map_zero, hf, one_smul] at h2
    exact ha h2.symm
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hw
    exact hne C u hC hu hw.symm
  have hst : ∀ σ : ℂ ≃ₐ[K] ℂ, ∀ x ∈ Submodule.span ℂ {w},
      σ.toLinearMap.rTensor A x ∈ Submodule.span ℂ {w} := by
    intro σ x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    let S : ℂ ⊗[K] A →ₐ[K] ℂ ⊗[K] A := Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)
    have hS : ∀ t, σ.toLinearMap.rTensor A t = S t := by
      intro t
      induction t with
      | tmul b v => simp [S]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (σ C / C) hn
    have h1 : (S w) ^ n = (μ • w) ^ n := by
      rw [← map_pow, smul_pow, hw, hμ, TensorProduct.smul_tmul', smul_eq_mul,
        div_mul_cancel₀ _ hC]
      simp [S]
    obtain ⟨z, hz⟩ := exists_eq_smul_of_pow_eq_pow hn h1
    have h2 : c • w = (c ⊗ₜ[K] (1 : A)) * w := by
      rw [Algebra.smul_def]; rfl
    have h3 : S (c ⊗ₜ[K] (1 : A)) * S w = σ c • S w := by
      rw [Algebra.smul_def]
      simp [S]
    rw [hS, h2, map_mul, h3, hz, smul_smul, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  obtain ⟨N, hN, -⟩ := (GlobalTheory.GaloisDescent.complex_stable_iff_exists_baseChange _).1 hst
  have hN0 : N ≠ ⊥ := by
    rintro rfl
    rw [Submodule.baseChange_bot, eq_comm, Submodule.span_singleton_eq_bot] at hN
    exact hw0 hN
  obtain ⟨b, hbN, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hb : (1 : ℂ) ⊗ₜ[K] b ∈ Submodule.span ℂ {w} :=
    hN ▸ Submodule.tmul_mem_baseChange_of_mem 1 hbN
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 hb
  have hpow : (1 : ℂ) ⊗ₜ[K] (b ^ n) = (l ^ n * C) ⊗ₜ[K] u := by
    have := congrArg (· ^ n) hl
    simp only [smul_pow, hw, Algebra.TensorProduct.tmul_pow, one_pow, TensorProduct.smul_tmul',
      smul_eq_mul] at this
    exact this.symm
  have hbn : b ^ n ≠ 0 := by
    intro h
    have h1 : ((1 : ℂ) ⊗ₜ[K] b) ^ n = 0 := by
      rw [Algebra.TensorProduct.tmul_pow, h, TensorProduct.tmul_zero]
    exact hne 1 b one_ne_zero hb0 (pow_eq_zero_iff hn.ne' |>.1 h1)
  have h4 := congrArg T hpow
  rw [hT, hT, hf, one_smul] at h4
  have h5 : f (l ^ n * C) ≠ 0 := by
    intro h
    rw [h, zero_smul] at h4
    exact hbn h4
  exact ⟨(f (l ^ n * C))⁻¹, b, inv_ne_zero h5, by rw [h4, smul_smul, inv_mul_cancel₀ h5, one_smul]⟩

end GlobalTheory.KeyFourth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtPtFOfEigFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

theorem exists_frPt_ptF_of_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (L : Type) [Field L] (φ : c.F →+* L) (z : Sp L ⟶ Xo.XF c) (x : Sp L ⟶ Z.X) (g : EigFrame Z φ x), z ≫ pullback.snd _ _ = spMap φ → z ≫ Z.jQ ≫ genι Z = x → letI := φ.toAlgebra; ∃ y : FrPt Xo c L, GlobalTheory.AllWt.ptF y = z ∧ ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left, w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = g.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z L _ φ z x g hs hx
  letI := φ.toAlgebra
  obtain ⟨y, w, hy, hw⟩ := OpenReg.exists_frPt_of_eigFrame (Z := Z) z hs hx g
  refine ⟨y, pullback.hom_ext ?_ ?_, fun τ i => ⟨w τ i, (hw τ i).2⟩⟩
  · exact (pullback.lift_fst _ _ _).trans hy
  · exact (pullback.lift_snd _ _ _).trans hs.symm

end GlobalTheory.ShFam
end
end

