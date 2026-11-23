module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0889
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0884
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaleRootsProdIcc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqConstMulOfNormOne
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverConst

theorem eq_const_mul_of_norm_one : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} (U : Set V), IsOpen U → IsPreconnected U → ∀ (P₂ P : ι → V → ℂ) (g : V → ℂ), (∀ i, DifferentiableOn ℂ (P₂ i) U) → (∀ i, DifferentiableOn ℂ (P i) U) → (∀ x ∈ U, ‖g x‖ = 1) → (∀ i, ∀ x ∈ U, P₂ i x = g x * P i x) → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ i, ∀ x ∈ U, P₂ i x = u * P i x := by
  intro V _ _ ι U hU hc P₂ P g hP₂ hP hg1 hg
  by_cases h : ∃ i, ∃ x ∈ U, P i x ≠ 0
  swap
  · push_neg at h
    refine ⟨1, by simp, fun i x hx => ?_⟩
    rw [hg i x hx, h i x hx]
    simp
  obtain ⟨i₀, x₀, hx₀, hne⟩ := h
  have hcont : ContinuousAt (P i₀) x₀ := (hP i₀).continuousOn.continuousAt (hU.mem_nhds hx₀)
  have hnb : ∀ᶠ y in nhds x₀, y ∈ U ∧ P i₀ y ≠ 0 := (hU.eventually_mem hx₀).and (hcont.eventually_ne hne)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnb
  have hx₀b : x₀ ∈ Metric.ball x₀ ε := Metric.mem_ball_self hε
  let q : V → ℂ := fun y => P₂ i₀ y * (P i₀ y)⁻¹
  have hqd : DifferentiableOn ℂ q (Metric.ball x₀ ε) :=
    ((hP₂ i₀).mono (fun y hy => (hball y hy).1)).mul (((hP i₀).mono (fun y hy => (hball y hy).1)).inv
      (fun y hy => (hball y hy).2))
  have hqg : ∀ y ∈ Metric.ball x₀ ε, q y = g y := fun y hy => by
    simp only [q]
    rw [hg i₀ y (hball y hy).1, mul_assoc, mul_inv_cancel₀ (hball y hy).2, mul_one]
  have hmax : IsMaxOn (norm ∘ q) (Metric.ball x₀ ε) x₀ := fun y hy => by
    simp only [Set.mem_setOf_eq, Function.comp_apply]
    rw [hqg y hy, hqg x₀ hx₀b, hg1 _ (hball y hy).1, hg1 _ (hball x₀ hx₀b).1]
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball x₀ ε).isPreconnected
    Metric.isOpen_ball hqd hx₀b hmax
  refine ⟨g x₀, hg1 x₀ hx₀, fun i => ?_⟩
  have hzero : ∀ y ∈ U, (fun y => P₂ i y - g x₀ * P i y) y = 0 := by
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hU hc ((hP₂ i).sub ((hP i).const_mul (g x₀))) hx₀ ?_
    filter_upwards [Metric.ball_mem_nhds x₀ hε] with y hy
    have e : g y = g x₀ := by
      rw [← hqg y hy, ← hqg x₀ hx₀b]
      exact heq hy
    simp only [Pi.zero_apply]
    rw [hg i y (hball y hy).1, e]
    ring
  intro x hx
  have := hzero x hx
  simp only at this
  exact sub_eq_zero.1 this

theorem psi_and_weight_eq : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (k₂ : C.U₂.Comp) (k : (T.U j σ).Comp), (∀ τ : D.host.E →+* ℂ, τ ∈ (C.U₂.X k₂).Ψ ↔ τ ∈ ((T.U j σ).X k).Ψ) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ) (i : Fin D.R.r), laU C.U₂ a n k₂ ⟨τ, h₂⟩ i = laU (T.U j σ) a n k ⟨τ, h₁⟩ i := by
  intro D T hL j hj σ hσ C hC k₂ k
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ
  have hrel : relab C.d.c₂ C.σ₂ = relab T.Q.c σ := by
    funext τ
    ext x
    have e := congrArg (fun φ : T.Q.c.F →+* ℂ => φ (embF T.Q.c τ x)) hC.2.2.1
    simp only [RingHom.comp_apply] at e
    show C.σ₂ (embF C.d.c₂ τ x) = σ (embF T.Q.c τ x)
    rw [← e]
    congr 1
  refine ⟨fun τ => by rw [(hU₂.2.1 k₂).2 τ, (hU₁.2.1 k).2 τ], fun a n τ h₂ h₁ i => ?_⟩
  unfold laU
  rw [(hU₂.2.1 k₂).1, (hU₁.2.1 k).1, hrel]

theorem cover_scalar_const : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∀ k₂ : C.U₂.Comp, ∃ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X k₂).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X k).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X k₂).Gm v w) ∧ (∀ h, (C.dict₂ h).1 = k₂ → (T.dict j σ h).1 = k) ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = u * rdU (T.U j σ) f k x' := by
  intro D T hL j hj σ hσ C hC n k₂
  obtain ⟨k, γ, hΛ, hh, hd, hx⟩ := GlobalTheory.T.levelCover_component_readings_unit_modulus_scalar D T hL j hj σ hσ C hC k₂
  obtain ⟨hΨ, hla⟩ := psi_and_weight_eq D T hL j hj σ hσ C hC k₂ k
  refine ⟨k, γ, hΛ, hh, hd, ?_⟩
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ

  let G : Frame (C.U₂.X k₂).Ψ D.R.r → Frame ((T.U j σ).X k).Ψ D.R.r := fun x τ =>
    ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩ : Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hGrel : ∀ x (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ),
      mat (G x) ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩ := by
    intro x τ h₂ h₁
    rfl
  have hGdom : ∀ x ∈ (C.U₂.X k₂).dom, G x ∈ ((T.U j σ).X k).dom := fun x hx' => (hx x (G x) hx' (hGrel x)).1
  have hGdiff : Differentiable ℂ G := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    simp only [G, mat, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    fun_prop

  let ι := {p : ((D.host.E →+* ℂ) × ℕ → ℕ) × Rul (T.Q.Xo j) T.Q.c × Rul C.d.Xo₂ C.d.c₂ //
    Dom p.1 n ∧ p.2.1 ∈ sec (T.Q.Xo j) T.Q.c p.1 n ∧ p.2.2 ∈ sec C.d.Xo₂ C.d.c₂ p.1 n ∧ C.IsPull p.2.1 p.2.2}
  let P₂ : ι → Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun i => rdU C.U₂ i.1.2.2 k₂
  let P : ι → Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun i x => rdU (T.U j σ) i.1.2.1 k (G x)
  have hP₂d : ∀ i, DifferentiableOn ℂ (P₂ i) (C.U₂.X k₂).dom := fun i =>
    (hU₂.2.2.2.2.1 i.1.1 n i.2.1 i.1.2.2 i.2.2.2.1 k₂).1
  have hPd : ∀ i, DifferentiableOn ℂ (P i) (C.U₂.X k₂).dom := fun i =>
    (hU₁.2.2.2.2.1 i.1.1 n i.2.1 i.1.2.1 i.2.2.1 k).1.comp hGdiff.differentiableOn hGdom
  have hg : ∀ x ∈ (C.U₂.X k₂).dom, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i : ι, P₂ i x = c * P i x := by
    intro x hxd
    obtain ⟨b, hb, hyd, hyo⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_borel_orthonormal_move (C.U₂.X k₂) hxd
    obtain ⟨-, t, -, hmod, hrel⟩ := hx (rmul x b) (G (rmul x b)) hyd (hGrel _)
    have ht1 : ‖t‖ = 1 := hmod (fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_diagonal_minor_one _ hyo τ i)
    refine ⟨t ^ n, by rw [norm_pow, ht1, one_pow], ?_⟩
    rintro ⟨⟨a, f, f₂⟩, hDom, hf, hf₂, hP⟩
    let b₁ : Frame ((T.U j σ).X k).Ψ D.R.r := fun τ => b ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have hb₁ : b₁ ∈ Bor ((T.U j σ).X k).Ψ D.R.r := fun τ => hb ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have e1 := hrel n a hDom f hf f₂ hf₂ hP
    have e2 : rdU C.U₂ f₂ k₂ (rmul x b) = bchar (laU C.U₂ a n k₂) b * rdU C.U₂ f₂ k₂ x :=
      (hU₂.2.2.2.2.1 a n hDom f₂ hf₂ k₂).2.1 x hxd b hb
    have e3 : G (rmul x b) = rmul (G x) b₁ := by
      funext τ
      simp only [G, rmul, b₁, mat]
      exact (Matrix.mul_assoc ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1) (mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩) (mat b ⟨τ.1, (hΨ τ.1).2 τ.2⟩)).symm
    have e4 : rdU (T.U j σ) f k (rmul (G x) b₁) = bchar (laU (T.U j σ) a n k) b₁ * rdU (T.U j σ) f k (G x) :=
      (hU₁.2.2.2.2.1 a n hDom f hf k).2.1 (G x) (hGdom x hxd) b₁ hb₁
    have e5 : bchar (laU C.U₂ a n k₂) b = bchar (laU (T.U j σ) a n k) b₁ := by
      unfold bchar
      refine Fintype.prod_equiv (Equiv.subtypeEquivRight (fun τ => hΨ τ)) _ _ (fun τ => ?_)
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [hla a n τ.1 τ.2 ((hΨ τ.1).1 τ.2) i]
      rfl
    have e6 : bchar (laU C.U₂ a n k₂) b ≠ 0 := by
      unfold bchar
      refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
      have hdet : (mat b τ).det ≠ 0 := (hb τ).1
      rw [Matrix.det_of_upperTriangular (M := mat b τ) (fun a c h => (hb τ).2 a c h)] at hdet
      simpa [mat] using Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
    show rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k (G x)
    apply mul_left_cancel₀ e6
    rw [← e2, e1, e3, e4, ← e5]
    ring
  classical
  let g : Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun x => if h : x ∈ (C.U₂.X k₂).dom then (hg x h).choose else 1
  have hg1 : ∀ x ∈ (C.U₂.X k₂).dom, ‖g x‖ = 1 := fun x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.1
  have hgr : ∀ i, ∀ x ∈ (C.U₂.X k₂).dom, P₂ i x = g x * P i x := fun i x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.2 i
  obtain ⟨u, hu1, hu⟩ := eq_const_mul_of_norm_one (C.U₂.X k₂).dom (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected D.R.r (C.U₂.X k₂)).isPreconnected P₂ P g hP₂d hPd hg1 hgr
  refine ⟨u, hu1, fun x x' hxd hrel' => ⟨(hx x x' hxd hrel').1, ?_⟩⟩
  have hx' : x' = G x := by
    funext τ
    exact hrel' τ.1 ((hΨ τ.1).2 τ.2) τ.2
  intro a hDom f hf f₂ hf₂ hP
  rw [hx']
  exact hu ⟨(a, f, f₂), hDom, hf, hf₂, hP⟩ x hxd

end GlobalTheory.CoverConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactLocalConditionDataAtPlace
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section
namespace GlobalTheory.UseLocInst


set_option maxHeartbeats 1000000 in
theorem exists_setC : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i), tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π →
    TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i →
    D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d →
    (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool)
      (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ),
        ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      ∃ (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)) (_ : Irreducible lam)
        (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
        (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
        (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
        (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
        SetC HW r ρ π C hA lam θ h w' η typ U := by
  intro D HW F i r ρ π hB3 hJa hGood hZ hG2 hG3 hCont hDec hEps h5 hsm hq hd hPosition w hw
  obtain ⟨C, hA⟩ := GlobalTheory.UseLoc.exists_caseA_enl D i w hw hsm hq hd
  obtain ⟨lam, hlam⟩ := GlobalTheory.UseLocUnif.exists_uniformiser (D.nd.l i) C.LL
  obtain ⟨ep, hJ⟩ := hJa
  have hτ : ∀ a : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)),
      ∃ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, tableLineDegreeTwo.Over (embC HW C hA) a τ ∧
        ∀ τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, tableLineDegreeTwo.Over (embC HW C hA) a τ' → τ' = τ :=
    fun a => GlobalTheory.UseLoc.extendUnramEmb (D.nd.l i) (D.nbr i w hw).Kw C.LL hA.1 (embC HW C hA a)
  choose τa _hτa hτu using hτ
  have hJτ := fun a => hJ i r hGood w hw C (τa a)
  choose gA ρA _hRead hX hW using hJτ
  haveI := (Br.PD D.loc D.nbr i w hw).finK₀
  haveI : NeZero (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨h, w', η, typ, U, hS, hU⟩ := hPosition _ (fun a => decide (AdmissibleParameterJ.TypeU D ep (gA a))) ρA
  obtain ⟨θ, hθc, hθcr, hθj⟩ := (hB3 (D.nd.l i) (D.nbr i w hw).Kw C.LL hA).1 (fun a => (w' a : ℤ))
  have hθj' : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ → ∀ b,
      multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b =
        if b = (w' a : ℤ) then 1 else 0 := hθj
  have hθnz : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ →
      multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ (w' a) ≠ 0 := by
    intro a τ hO
    rw [hθj' a τ hO]
    simp
  have hWp : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ → ∀ b : ℤ,
      multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) τ b =
        ((U a).count (b + w' a) : ℤ) := by
    intro a τ hO b
    rw [hτu a τ hO, ((hW a) ρ π hZ hDec b).2.1]
    obtain ⟨h1, h2⟩ := hU a b
    by_cases hb : ((b : ℤ) : ℚ) ∈ AdmissibleParameterJ.JW D (decide (AdmissibleParameterJ.TypeU D ep (gA a))) (D.nd.j i) (ρA a)
    · rw [if_pos hb, h1.2 hb]
      simp
    · rw [if_neg hb]
      have : (U a).count (b + w' a) ≠ 1 := fun e => hb (h1.1 e)
      omega
  have hL6 := GlobalTheory.UseLoc.crys_Wp_rTw D i r ρ π w hw C hGood hZ hG2 hDec
  have hL4 := GlobalTheory.UseLoc.TwistCrysW.isCrys_and_multV D i w hw C
  have hL5 := GlobalTheory.UseLoc.twistM_repV_cont D i w hw C
  have hWcont : Continuous fun g => WpO D.nd i ρ π g :=
    (GlobalTheory.Pass.stepSub_holds D i r ρ hGood π hDec {π} rfl).1.1
  refine ⟨C, hA, lam, hlam, θ, h, w', η, typ, U, ?_, ?_⟩
  · refine ⟨D.R.t_odd.pos, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Br.PD_p]
      exact hS
    · exact hL5 _ (WpO D.nd i ρ π) θ hWcont hθc
    · exact (hL4 _ (WpO D.nd i ρ π) θ hL6.1 hθcr).1
    · intro a τ hO b
      have e := (hL4 _ (WpO D.nd i ρ π) θ hL6.1 hθcr).2 τ (w' a) (hθnz a τ hO) (b - w' a)
      rw [sub_add_cancel] at e
      rw [e, hWp a τ hO, sub_add_cancel]
    · intro c hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
      obtain ⟨k1, k2, k3⟩ := GlobalTheory.UseLoc.chiT_cont_isCrys_multV D i r ρ π w hw C θ c hc1 hc2 hG2 hθc hθcr
      refine ⟨GlobalTheory.UseLoc.chiT_cyc D i w hw C θ c hc1 hc2, k1, k2, ?_⟩
      intro a τ hO b
      have e := k3 τ (b - ((c : ℤ) - 1))
      rw [sub_add_cancel b ((c : ℤ) - 1)] at e
      rw [e, hθj' a τ hO]
      split_ifs <;> omega
  · intro x
    refine ⟨hL5 _ (rTwO D.nd i r x) θ (GlobalTheory.Pass.FamCont.stepCont D i r hGood x).1 hθc,
      (hL4 _ (rTwO D.nd i r x) θ (hL6.2 x) hθcr).1, ?_,
      GlobalTheory.UseLoc.InstPoly.charpoly_congr D i r ρ π w hw C θ lam hlam hG3 x⟩
    intro a τ hO b
    have e := (hL4 _ (rTwO D.nd i r x) θ (hL6.2 x) hθcr).2 τ (w' a) (hθnz a τ hO) (b - w' a)
    rw [sub_add_cancel] at e
    rw [e, hτu a τ hO, ((hX a) x (b - w' a)).2.1]
    have e2 := GlobalTheory.jTil_shift_block (D.nd.l i) _ D.R.t h w' η typ U hS a
      (AdmissibleParameterJ.JW D (decide (AdmissibleParameterJ.TypeU D ep (gA a))) (D.nd.j i) (ρA a)) (hU a) (b - w' a)
    rw [sub_add_cancel] at e2
    rw [← e2]
    exact if_congr (GlobalTheory.UseLoc.JumpBlock.jumps_iff D _ _ _ _) rfl rfl

end GlobalTheory.UseLocInst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeoHalfMove
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.Unframe

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Lev ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeSup GlobalTheory.RealGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev moveForms {LL Ks WL G : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] {W : (LL →+* ℂ) → Type}
    [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G]
    (B : Arith.FormsL LL Ks WL W G) (w : (LL →+* ℂ) → G) : Arith.FormsL LL Ks WL W G :=
  { B with j := fun σ => (B.j σ).comp (B.ρ (w σ)) }

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev moveR {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G) : RealDat D A Ks :=
  updFW R R.nW fun i => moveForms (R.FW i) (w i)

variable {T : CoreJ D} [iA : Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}


open Classical in
variable (T) in
def overEmb (w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : G :=
  if GoodEmb T.Q.c (res T σ) then w i (res T σ) else w i (resC T σ)

section Half

variable (B : GeoHalf T R fun _ => 1) (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ)
  (w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G)

def Moves : Prop :=
  ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (B.κ i)) (B.κ i).n,
      phiC (setCE T c') hV (wtA (B.κ i)) f = phiC T hV (wtA (B.κ i)) (actLev T.Q.c (B.O i).lev2 (w i σ) f)

variable {B c' w}

theorem rho_e (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (i : Fin D.R.m) (g : G) (f : Cu T B.κ i) :
    (R.FW i).ρ g ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) =
      (B.fw.e i ⟨actLev T.Q.c (B.O i).lev2 g f, hK i g f f.2⟩ : (R.FW i).WK) :=
  (((B.rhoGeo i).1 (hK i) g f).choose_spec).symm

set_option maxHeartbeats 1600000 in
theorem ev_move (hJ : JEvExists T R B.κ B.v₀) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (f : Cu T B.κ i) :
    (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ (overEmb T w i σ) ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)))
      (B.v₀ i σ) = phiC (setCE T c') hV (wtA (B.κ i)) (f : T.R ((i : ℕ) + 1)) := by
  rw [overEmb, if_pos hσ, rho_e hK, hM i _ hσ hV f f.2]
  exact B.fw.evaluates hJ i σ hσ hV ⟨_, hK i _ f f.2⟩

set_option maxHeartbeats 1600000 in
theorem bar_move (hJ : JEvBar T R B.κ) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i) :
    ∃ v : (R.MW i σ).Vec, IsUnitV v ∧ ∀ f : Cu T B.κ i,
      (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ (overEmb T w i σ) ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) v =
        fun g => starRingEnd ℂ (phiC (setCE T c') hV (wtA (B.κ i)) (f : T.R ((i : ℕ) + 1)) g) := by
  obtain ⟨v, hv, h⟩ := (B.bar i σ hσ hV).1 (hJ i σ hσ hV)
  refine ⟨v, hv, fun f => ?_⟩
  rw [overEmb, if_neg hσ, rho_e hK, hM i _ (good_resC T hσ) hV f f.2]
  exact h ⟨_, hK i _ f f.2⟩


set_option maxHeartbeats 3200000 in
def tieMove (hL : LawsJ (setCE T c')) (hJ : JEvExists T R B.κ B.v₀) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) :
    @FWTie D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) B.κ B.v₀ :=
  @FWTie.mk D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) B.κ B.v₀ B.fw.alg_eq B.fw.e B.fw.ks B.fw.kap B.fw.pt
    B.fw.nrm_eq hL B.fw.chiR B.fw.hv₀ B.fw.x0
    (fun i σ hσ hV h => absurd ⟨((R.FW i).j σ).comp ((R.FW i).ρ (overEmb T w i σ)), ev_move hJ hK hM i σ hσ hV⟩ h)
    (fun i σ hσ hV _ => ev_move hJ hK hM i σ hσ hV)


set_option maxHeartbeats 3200000 in
theorem exists_geoHalf_move (hL : LawsJ (setCE T c')) (hI : InGeo B) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w)
    (hF : @Fired D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ B.O fun _ => 1) :
    ∃ B' : @GeoHalf D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) fun _ => 1,
      @GeoHalf.v₀ D G _ _ Pl0 T0 A (setCE T c') iA _ _ B' = B.v₀ := by
  have hF' := @Half.fired_upd D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ R.nW (fun i => moveForms (R.FW i) (overEmb T w i)) B.O _ hF
  refine ⟨@GeoHalf.mk D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) _ B.κ B.v₀ (tieMove hL hI.jEvExists hK hM)
    (fun i σ hσ hV => ?_) (fun i => @Half.updO D G _ _ Pl0 T0 A (setCE T c') iA R _ _ _ _ _ (B.O i))
    (fun i => @Half.omPins_upd D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ _ _ B.O i (B.pins i)) B.rhoGeo
    (fun i σ hσ hV _ => hF'.2 i σ hσ hV) (fun i _ => ⟨1, hF'.1 i⟩) (fun i _ _ => hF'.1 i), rfl⟩
  obtain ⟨v, hv, h⟩ := bar_move hI.jEvBar hK hM i σ hσ hV
  exact ⟨fun _ => ⟨v, hv, h⟩, fun h' => absurd ⟨v, hv, (tieMove hL hI.jEvExists hK hM).jK i σ, h⟩ h'⟩

end Half

omit iA in
theorem phiC_setCE_of_eq {c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ} {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D}
    (hV : T.V j σ = W) (e : c' j σ = T.cE j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC (setCE T c') hV a f = phiC T hV a f := by
  funext h
  rw [phiC_apply, phiC_apply]
  exact congrArg (fun c => (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * adel W (castDict hV (T.dict j σ))
      (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) c) (rdU (T.U j σ) f) h) e


set_option maxHeartbeats 3200000 in
theorem exists_framed_half (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) {F : Face D A}
    (hC : GlobalTheory.Core5 R F) (B : GeoHalf T R fun _ => 1) (hU : R.LUnif) (hI : InGeo B) :
    ∃ (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G),
      (∀ i σ, w i σ ∈ Subgroup.center G) ∧
      (∀ (i : Fin D.R.m) hV, @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c') iA R i T.σ₀ hV) ∧
      ∃ B' : @GeoHalf D G _ _ Pl0 T0 A (setCE T c') iA (moveR R w) fun _ => 1,
        @GeoHalf.v₀ D G _ _ Pl0 T0 A (setCE T c') iA _ _ B' = B.v₀ := by
  classical
  choose c1 z hz hO hfr hs using exists_shift hP hsz hC B hU hI.jEvExists
  have ht : TieIn T R B.κ B.v₀ := ⟨B.fw.laws, B.fw.alg_eq, B.fw.kap, B.fw.hv₀, B.fw.chiR, B.fw.x0⟩
  have hpb : T.pb = R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R B.fw.laws.toLawsM hC.lev ((B.pins ⟨0, by have := D.R.two_le_m; omega⟩).2.tuple ()).half
  have hx := _root_.GlobalTheory.EquivConst.exists_equivariant_constants T R B.κ B.v₀ B.O hC.lev ht hpb B.pins
  have H : ∀ (n : ℕ) (σ : T.Q.c.F →+* ℂ), ∃ c : (T.U (n + 1) σ).Comp → ℂ, ∀ hn : n < D.R.m,
      (σ = T.σ₀ → HEq c (c1 ⟨n, hn⟩)) ∧ (σ ≠ T.σ₀ → c = T.cE (n + 1) σ) := by
    intro n σ
    by_cases hσ : σ = T.σ₀
    · subst hσ
      by_cases hn : n < D.R.m
      · exact ⟨c1 ⟨n, hn⟩, fun _ => ⟨fun _ => HEq.rfl, fun h => absurd rfl h⟩⟩
      · exact ⟨fun _ => 1, fun h => absurd h hn⟩
    · exact ⟨T.cE (n + 1) σ, fun _ => ⟨fun h => absurd h hσ, fun _ => rfl⟩⟩
  choose c hc using H
  have h0 : ∀ i : Fin D.R.m, c i T.σ₀ = c1 i := fun i => eq_of_heq ((hc i T.σ₀ i.2).1 rfl)
  have h1 : ∀ (i : Fin D.R.m) σ, σ ≠ T.σ₀ → c i σ = T.cE ((i : ℕ) + 1) σ := fun i σ => (hc i σ i.2).2
  let c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ :=
    fun j => Nat.casesOn (motive := fun j => ∀ σ : T.Q.c.F →+* ℂ, (T.U j σ).Comp → ℂ) j (fun _ _ => 1) c
  let w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G := fun i σ => if σ = T.σ₀ then z i else 1
  have hK : ∀ i, ActKeeps (κ := B.κ) B.O i := fun i g f hf => by
    obtain ⟨k, hk, -⟩ := (B.pins i).2.lift.lev g
    exact ((hO i).1 g k hk f hf).1
  have hL : LawsJ (setCE T c') := lawsJ_setCE B.fw.laws fun j hj σ hσ => by
    cases j with
    | zero => exact fun _ => norm_one
    | succ n =>
      by_cases e : σ = T.σ₀
      · subst e
        have h : CUnit (c1 ⟨n, hj.2⟩) := (hO ⟨n, hj.2⟩).2.1.2.2.2.1
        rw [← h0 ⟨n, hj.2⟩] at h
        exact h
      · have h := B.fw.laws.cUnit _ hj σ hσ
        have e2 : c n σ = T.cE (n + 1) σ := h1 ⟨n, hj.2⟩ σ e
        rw [← e2] at h
        exact h
  have hM : Moves B c' w := fun i σ hσ hV f hf => by
    by_cases e : σ = T.σ₀
    · subst e
      rw [show w i T.σ₀ = z i from if_pos rfl]
      funext h
      rw [phiC_apply, phiC_apply]
      have h2 := hs i f hf h
      rw [← h0 i] at h2
      exact congrArg (_ * ·) h2
    · rw [show w i σ = 1 from if_neg e, phiC_setCE_of_eq hV (h1 i σ e)]
      have h2 := rho_e hK i 1 ⟨f, hf⟩
      rw [map_one] at h2
      have h3 := congrArg Subtype.val ((B.fw.e i).injective (Subtype.ext h2))
      exact congrArg _ h3
  have hF : @Fired D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ B.O fun _ => 1 := by
    refine ⟨fun i => ?_, fun i σ hσ hV => ?_⟩
    · have h := hO i
      rw [← h0 i] at h
      exact h
    · by_cases e : σ = T.σ₀
      · subst e
        have h := GlobalTheory.RealGeoConst.eqAt_base T R B.κ B.v₀ hC.lev ht i (B.O i) (c1 i) (hO i).1 hV
        rw [← h0 i] at h
        exact h
      · have h := B.equivAll i σ hσ hV (hx i σ hσ hV)
        rw [← h1 i σ e] at h
        exact h
  refine ⟨c', overEmb T w, fun i σ => ?_, fun i hV => hfr i c' (h0 i) hV, exists_geoHalf_move hL hI hK hM hF⟩
  have key : ∀ s, w i s ∈ Subgroup.center G := fun s => by
    by_cases e : s = T.σ₀
    · rw [show w i s = z i from if_pos e]
      exact hz i
    · rw [show w i s = 1 from if_neg e]
      exact one_mem _
  unfold overEmb
  split_ifs
  · exact key _
  · exact key _

end GlobalTheory.Unframe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaLieAlgebraUnitaryGroupOfJacquetRallisStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis : (∀ r : ℕ, GlobalTheory.JR.UnitMatch r) → UnitLemmaLie ∧ UnitLemmaGroup := by
  first | exact @GlobalTheory.UnitLemma.unitLemma_lie_and_group | exact GlobalTheory.UnitLemma.unitLemma_lie_and_group | (intros; apply GlobalTheory.UnitLemma.unitLemma_lie_and_group <;> assumption)
end

