module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameFrames

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmCurveHomExistsPureTypeVectorAnyLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveHomLiftAnyLevel

open UniformLift CurveHomLift

theorem exists_pure_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (φ : C.P.A.left ⟶ Xo.univ.t.G.left) (x : ℂ → (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ε : ℤˣ), (∀ z, (x z).left = C.pt z ≫ φ) → (∀ z w, x (z + w) = x z * x w) → (∀ z, x ((1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 * z) = x z ≫ Xo.univ.t.act.act H.w0) → ∃ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∀ z : ℂ, x z = F.ex i P (z • P a) := by
  intro E _ _ _ H D l Xo σ g ty F _ _ _ C i P hP φ x ε hx hadd hw
  obtain ⟨L, hL⟩ := exists_linear_lift_of_isHolTo F i P hP (m := 1) (fun z => x (z 0)) (fun z w => hadd _ _) (by
    simp only [hx]
    exact HolFibre.isHolTo_comp (isHolTo_pt C) φ)
  have hv : ∀ z : ℂ, x z = F.ex i P (z • L fun _ => 1) := fun z => by
    rw [← map_smul, hL]
    simp
  have h1 : x 1 = 1 := by
    rw [← map_zero_eq_one x hadd]
    exact Over.OverMorphism.ext (by rw [hx, hx, pt_one])
  rw [hv, one_smul, F.ex_ker i P hP] at h1
  obtain ⟨a, ha⟩ := h1
  rw [← ha] at hv
  refine ⟨a, fun j hj => ?_, hv⟩
  set w : ℂ := (1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 with hwdef
  have key : ∀ z : ℂ, z • (w • P a - P (H.w0 • a)) ∈ P.range := fun z => by
    have e1 := hw z
    rw [hv, hv, ← F.ex_lin i P hP] at e1
    have e2 : (fun k => ty k (H.w0 : E) * (z • P a) k) = z • P (H.w0 • a) := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, hP.1]
      ring
    have e3 := F.ex_add i P hP (z • (w • P a - P (H.w0 • a))) (z • P (H.w0 • a))
    rw [← smul_add, sub_add_cancel, smul_smul, mul_comm z w, e1, e2] at e3
    exact (F.ex_ker i P hP _).1 (mul_eq_right.1 e3.symm)
  obtain ⟨b, hb⟩ := key 1
  rw [one_smul] at hb
  have hb0 : b = 0 := eq_zero_of_line hP (hb ▸ key)
  rw [hb0, map_zero] at hb
  have e4 := congrFun hb j
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hP.1] at e4
  have e5 : 2 * ty j (H.w0 : E) = 1 + ty j (H.rt : E) := by
    have := congrArg (fun s : 𝓞 E => ty j (s : E)) H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  by_contra hne
  apply hj
  have e6 : w = ty j (H.w0 : E) := mul_right_cancel₀ hne (sub_eq_zero.1 e4.symm)
  rw [hwdef] at e6
  linear_combination -e5 - 2 * e6

end GlobalTheory.CurveHomLiftAnyLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyThetaDataFlagDomainModels
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem nonempty_thetaData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, Nonempty (ThetaData e F M k) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hσ hM hξ k
  obtain ⟨⟨idx, hty, -, hper⟩, hp0, hr, hcc, hpos, hφ⟩ :=
    _root_.GlobalTheory.FrameUnif.letter_column_dictionary E H Dw l Xo c σ g e F r M hσ hM hξ k
  obtain ⟨Pf, hPf, -, hisPer, hdiff, -⟩ := _root_.GlobalTheory.exists_framePeriods E H Dw l Xo c σ g e F r M hσ hM hξ k
  have htf : IsTypeFn H (F.Di k).p (F.Di k).q (fun j => relab c σ (e j).1) := by
    rw [(F.sig k).1, (F.sig k).2]
    exact (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw g e
  obtain ⟨hg, -⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H (F.Di k)).2.1 g _ htf
  obtain ⟨bas, hsym, had⟩ := GlobalTheory.exists_symplectic_basis_adapted_mod_eight E H (F.Di k) g hg
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hdom : (M.X k).dom = GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := by
    rw [← hp0]
  let co : (Fin (Module.finrank ℂ (Frame (M.X k).Ψ r)) → ℂ) ≃L[ℂ] Frame (M.X k).Ψ r :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨h, ta, c₁, c₂, hnorm, hhol, h1, h2, fr, hf1, hf2, hf3, hf4, hf5⟩ :=
    GlobalTheory.FrameTheta.exists_thetaFrame_frames E H Dw l Xo _ g _ F k r (-(M.X k).ξ0) (M.X k).Gm φ (M.X k).Ψ idx Pf
      (hM.type k).2 hty hcc hpos (hφ φ fun _ => rfl).2 hr (fun x v j => (hPf x v j).trans (hper x _ j))
      (hdom ▸ (GlobalTheory.frames_isConnected E r (M.X k)).isPreconnected) bas hsym _ co
  rw [← hdom] at hnorm hhol hf1 hf2 hf3 hf4 hf5
  exact ⟨{
    Pf := Pf
    per := hPf
    isPer := hisPer
    m := _
    co := co
    holPer := ⟨fun b hb => hisPer _ hb, fun v =>
      (hdiff v).comp co.differentiable.differentiableOn fun _ hb => hb⟩
    bas := bas
    sympl := hsym
    adapt := had
    h := h
    ta := ta
    norm := hnorm
    hol := hhol
    c₁ := c₁
    c₂ := c₂
    half₁ := h1
    half₂ := h2
    fr := fr
    fr_hol := hf1
    fr_ne := hf2
    fr_coc := hf3
    fr_rig := hf4
    fr_sec := hf5 }⟩

end GlobalTheory.FrameUnif
end

