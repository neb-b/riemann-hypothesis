module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0232

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCharRat

variable {D : D7}

theorem symplOH_add_right {S T : HSp D} (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  simp only [symplOH, symplO, hO, Matrix.add_apply, RingHom.map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib,
    LinearMap.map_add]

theorem symplOH_isoPart_midPart (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) (x : WO V' W) :
    symplOH V W (isoPart V W C (q₀.map (incA D))) (midPart V V' W B x) = 0 := by
  set X : Mx D r V.rank := (adj D C * V.gram).map (incA D) with hXdef
  set M : Matrix (Fin V'.rank) (Fin V.rank) D.host.E := V'.gram⁻¹ * adj D B * V.gram with hMdef
  set Y : Mx D V'.rank V.rank := M.map (incA D) with hYdef
  have hM : Mᴴ = V.gram * B * V'.gram⁻¹ := by
    rw [hMdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose,
      GlobalTheory.MixModel.gramInv_conjTranspose]
    show V.gram * ((Bᴴ)ᴴ * V'.gram⁻¹) = _
    rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hX0 : X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj Y = 0 := by
    have e : GlobalTheory.MixModel.adj Y = GlobalTheory.MixModel.rat (V.gram * B * V'.gram⁻¹) := by
      rw [hYdef, ← hM]; rfl
    rw [e, hXdef]
    show GlobalTheory.MixModel.rat (adj D C * V.gram) * GlobalTheory.MixModel.rat V.gram⁻¹ * GlobalTheory.MixModel.rat (V.gram * B * V'.gram⁻¹) = 0
    rw [← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V.gram * B * V'.gram⁻¹) = adj D C * V.gram * B * V'.gram⁻¹ := by
      rw [Matrix.mul_assoc (adj D C * V.gram), ← Matrix.mul_assoc V.gram⁻¹, ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul, ← Matrix.mul_assoc]
    rw [this, hs.orth, Matrix.zero_mul]
    exact GlobalTheory.MixModel.rat_zero
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace]
  have e2 : isoPart V W C (q₀.map (incA D)) = q₀.map (incA D) * X := rfl
  have e3 : midPart V V' W B x = x * Y := rfl
  rw [e2, e3, GlobalTheory.MixModel.adj_mul]
  have e4 : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj Y * GlobalTheory.MixModel.adj x * (GlobalTheory.MixModel.gA W * (q₀.map (incA D) * X)))
      = (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj Y * GlobalTheory.MixModel.adj x * GlobalTheory.MixModel.gA W * q₀.map (incA D)) * X := by
    simp only [Matrix.mul_assoc]
  rw [e4, Matrix.trace_mul_comm]
  have e5 : X * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj Y * GlobalTheory.MixModel.adj x * GlobalTheory.MixModel.gA W * q₀.map (incA D))
      = (X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj Y) * (GlobalTheory.MixModel.adj x * GlobalTheory.MixModel.gA W * q₀.map (incA D)) := by
    simp only [Matrix.mul_assoc]
  rw [e5, hX0, Matrix.zero_mul, Matrix.trace_zero, map_zero]


set_option maxHeartbeats 1000000 in
theorem res_om_rat {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ}
    {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χS χT ω)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨)
    {γ : GA D W} (hγ : γ ∈ GQ W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    res V V' W C B μ 𝓨 (ω (1, γ) f) x = res V V' W C B μ 𝓨 f (Formalism.L2.Theta.mt W γ⁻¹ * x) := by
  have hrat := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω 1 (one_mem _) γ hγ f hf
  have hact : ∀ w : WO V W, actO V W 1 γ w = Formalism.L2.Theta.mt W γ * w := by
    intro w
    rw [GlobalTheory.MixModel.actO_eq, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have hQP : Formalism.L2.Theta.mt W γ * Formalism.L2.Theta.mt W γ⁻¹ = 1 := GlobalTheory.MixModel.mt_mul_inv W γ
  have hPQ : Formalism.L2.Theta.mt W γ⁻¹ * Formalism.L2.Theta.mt W γ = 1 := GlobalTheory.MixModel.mt_inv_mul W γ
  have hpt : ∀ a, ω (1, γ) f (isoPart V W C a + midPart V V' W B x) =
      f (isoPart V W C (Formalism.L2.Theta.mt W γ⁻¹ * a) + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ * x)) := by
    intro a
    rw [← hrat, hact]
    refine congrArg (ω (1, γ) f) ?_
    show a * (((adj D C * V.gram).map (incA D)) : Mx D r V.rank) +
        x * (((V'.gram⁻¹ * adj D B * V.gram).map (incA D)) : Mx D V'.rank V.rank) =
      Formalism.L2.Theta.mt W γ * (Formalism.L2.Theta.mt W γ⁻¹ * a * (((adj D C * V.gram).map (incA D)) : Mx D r V.rank) +
        Formalism.L2.Theta.mt W γ⁻¹ * x * (((V'.gram⁻¹ * adj D B * V.gram).map (incA D)) : Mx D V'.rank V.rank))
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP,
      Matrix.one_mul, Matrix.one_mul]
  show ∫ a in 𝓨, ω (1, γ) f (isoPart V W C a + midPart V V' W B x) ∂μ =
    ∫ a in 𝓨, f (isoPart V W C a + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ * x)) ∂μ
  simp only [hpt]
  have hper : ∀ q ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ a,
      f (isoPart V W C (q + a) + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ * x)) =
        f (isoPart V W C a + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ * x)) := by
    intro q hq a
    obtain ⟨q₀, rfl⟩ := hq
    have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
    rw [e3, GlobalTheory.TwistEquiRat.isoPart_add, add_assoc, ← GlobalTheory.TwistEquiRat.ratW_eq_isoPart, hf.quasi,
      GlobalTheory.TwistEquiRat.ratW_eq_isoPart, symplOH_add_right, GlobalTheory.TwistEquiRat.symplOH_isoPart V W C hs.frame,
      symplOH_isoPart_midPart V V' W C B hs, add_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
  have integral_mul_left {m n : ℕ} (μ : Measure (Mx D m n)) (𝓨 : Set (Mx D m n))
      (h : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓨) (P Q : Mx D m m)
      (hP : P ∈ GlobalTheory.MixModel.ratMx D m m) (hQ : Q ∈ GlobalTheory.MixModel.ratMx D m m)
      (hPQ : P * Q = 1) (hQP : Q * P = 1) (φ : Mx D m n → ℂ)
      (hφ : ∀ g ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (g + a) = φ a) :
      ∫ a in 𝓨, φ (P * a) ∂μ = ∫ a in 𝓨, φ a ∂μ := by
    obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
    have : BorelSpace (Mx D m n) := ⟨rfl⟩
    let eA : Mx D m n ≃+ Mx D m n :=
      { toFun := fun a => P * a
        invFun := fun a => Q * a
        left_inv := fun a => by show Q * (P * a) = a; rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
        right_inv := fun a => by show P * (Q * a) = a; rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
        map_add' := fun a b => Matrix.mul_add P a b }
    have hc : Continuous (fun a : Mx D m n => P * a) := continuous_const.matrix_mul continuous_id
    have hc' : Continuous (fun a : Mx D m n => Q * a) := continuous_const.matrix_mul continuous_id
    let eH : Mx D m n ≃ₜ Mx D m n := ⟨eA.toEquiv, hc, hc'⟩
    let eM : Mx D m n ≃ᵐ Mx D m n := eH.toMeasurableEquiv
    have := h.1
    have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hc hc'
    have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
    have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
    let eG : GlobalTheory.MixModel.ratMx D m n → GlobalTheory.MixModel.ratMx D m n :=
      fun g => ⟨P * (g : Mx D m n), GlobalTheory.MixModel.ratMx_mul hP g.2⟩
    have hbij : Function.Bijective eG := by
      refine ⟨fun g g' hg => ?_, fun g => ⟨⟨Q * (g : Mx D m n), GlobalTheory.MixModel.ratMx_mul hQ g.2⟩, ?_⟩⟩
      · have e := congrArg (fun x : GlobalTheory.MixModel.ratMx D m n => Q * (x : Mx D m n)) hg
        simp only [eG, ← Matrix.mul_assoc, hQP, Matrix.one_mul] at e
        exact Subtype.ext e
      · apply Subtype.ext
        show P * (Q * (g : Mx D m n)) = g
        rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    have hF : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) (eM.symm ⁻¹' 𝓨) (μ.map eM) := by
      refine h.2.1.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
      show Q * (P * (g : Mx D m n) + x) = (g : Mx D m n) + Q * x
      rw [Matrix.mul_add, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
    have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓨) = 𝓨 := by
      ext a; simp
    have hvol : (μ.map eM) (eM.symm ⁻¹' 𝓨) = 1 := by
      rw [MeasurableEquiv.map_apply, hpre]; exact h.2.2
    have e1 := hmp.setIntegral_preimage_emb eM.measurableEmbedding φ (eM.symm ⁻¹' 𝓨)
    rw [hpre] at e1
    exact e1.trans (GlobalTheory.MixModel.covolOne_integral_eq h ⟨hHaar, hF, hvol⟩ φ hφ)
  exact integral_mul_left μ 𝓨 hμ _ _ ((GlobalTheory.MixModel.mem_GQ_iff W γ⁻¹).1 (inv_mem hγ))
    ((GlobalTheory.MixModel.mem_GQ_iff W γ).1 hγ) hPQ hQP
    (fun a => f (isoPart V W C a + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ * x))) hper

theorem char_eq_one_of_rat : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ c : GA D W →* Circle, (∀ h f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f)) → ∀ γ ∈ GQ W, c γ = 1 := by
  intro D V V' W r C B hs ψ χS χT χS' χT' ω ω' hω hω' μ 𝓨 hμ c hc γ hγ
  obtain ⟨hall, f₀, hf₀, hne⟩ := _root_.GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hω.std μ 𝓨 hμ
  obtain ⟨x, hx⟩ : ∃ x, res V V' W C B μ 𝓨 f₀ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hres : IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 f₀) := ((hall f₀ hf₀).2.1)
  have h1 := congrFun (hc γ f₀ hf₀) (actO V' W 1 γ x)
  have hact : actO V' W 1 γ x = Formalism.L2.Theta.mt W γ * x := by
    rw [GlobalTheory.MixModel.actO_eq, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have hPQ : Formalism.L2.Theta.mt W γ⁻¹ * Formalism.L2.Theta.mt W γ = 1 := GlobalTheory.MixModel.mt_inv_mul W γ
  have h2 := GlobalTheory.WeilRat.om_rat_actO D ψ hω'.std V' W χS' χT' ω' hω' 1 (one_mem _) γ hγ _ hres x
  rw [Pi.smul_apply, h2, res_om_rat hs hω hμ hγ hf₀, hact, ← Matrix.mul_assoc, hPQ, Matrix.one_mul,
    smul_eq_mul] at h1
  have h3 : (c γ : ℂ) = 1 := by
    have := mul_right_cancel₀ hx (h1.symm.trans (one_mul _).symm)
    exact this
  exact Circle.ext (by simpa using h3)

end GlobalTheory.TwistCharRat

end
