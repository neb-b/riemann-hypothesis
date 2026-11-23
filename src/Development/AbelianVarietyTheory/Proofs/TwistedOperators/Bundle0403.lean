module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaTraceValuesAtComplexPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaValueIdentityUnitFrames
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

noncomputable section
namespace GlobalTheory.HeckeValueId

theorem core (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (P : Ideal (𝓞 E)) (p i : ℕ)
    (yx zx : Sp ℂ ⟶ Xo.X) (ys : LB.Sec (PPx yx)) (zs : LB.Sec (PPx zx)) (C : Subgroup (Over.mk yx ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom yx ⟶ pullback Xo.univ.t.G.hom zx)
    (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G))
    (cr : Fin (Ideal.absNorm P ^ i) → (Over.mk yx ⟶ Xo.univ.t.G))
    (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ) (t0 : ℂ)
    (hp : p.Prime) (hC2 : ∀ a ∈ C, a ^ p ^ 2 = 1) (hk : IsHkIsog p yx zx C ψ ψp)
    (hr : GlobalTheory.ThetaTrace.IsRepsModTors C p cr)
    (hb0 : ∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0)
    (hbt : ∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a)
    (hbr : ∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (hbh : ∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (hbv : ∀ (a : Over.mk yx ⟶ Xo.univ.t.G) q (jm : Fin (Ideal.absNorm P ^ i) → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U q →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk zx)) (ψp a)).left ((PPx zx).U (fun _ => q)) (zs.f (fun _ => q)) =
        ∑ m, b q (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk yx)) ((cr m * a) ^ p)).left ((PPx yx).U (fun _ => jm m)) (ys.f (fun _ => jm m)))
    (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (i₁ i₂ : Fin F.n) (Pm : (F.Di i₁).La →+ (Fin g → ℂ)) (Pm' : (F.Di i₂).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i₁) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm)
    (hP' : IsPeriod (F.Di i₂) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm')
    (hu : yx = F.u i₁ Pm) (hu' : zx = F.u i₂ Pm')
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ)
    (hH : Hm.IsHermitian)
    (him : ∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di i₁).EF a b)
    (hd : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (hn : ∀ j z, ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (hc : ∀ j j' z, ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex i₁ Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z)
    (h0 : ∀ j, ⊤ ≤ (F.ex i₁ Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (ha : ∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a)))
    (hv : ∀ j z (pt : Sp ℂ ⟶ Gx yx),
      pt ≫ Formalism.L2.PjFree.gxFst yx = (F.ex i₁ Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd yx = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx yx).U (fun _ => j)) (ys.f (fun _ => j)) = θ z * fr j z)
    (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ' : (Fin g → ℂ) → ℂ)
    (him' : ∀ a b, (hermForm Hm' (Pm' a) (Pm' b)).im = (F.Di i₂).EF a b)
    (hd' : ∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (hc' : ∀ j j' z, ⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (F.ex i₂ Pm' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr' j' z)
    (h0' : ∀ j, ⊤ ≤ (F.ex i₂ Pm' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (ha' : ∀ a j z, ‖χl' (Pm' a)‖ = 1 ∧ (⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' (Pm' a) * Complex.exp (Real.pi * hermForm Hm' z (Pm' a) +
        Real.pi / 2 * hermForm Hm' (Pm' a) (Pm' a)) * fr' j (z + Pm' a)))
    (hv' : ∀ j z (pt : Sp ℂ ⟶ Gx zx),
      pt ≫ Formalism.L2.PjFree.gxFst zx = (F.ex i₂ Pm' z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd zx = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx zx).U (fun _ => j)) (zs.f (fun _ => j)) = t0 * (θ' z * fr' j z)) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (wm : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)),
      (∀ a, ∃ b, h (Pm a) = Pm' b) ∧ (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) ∧
      (∀ m, ∃ b, h (wm m) = Pm' b) ∧
      ∀ w, ∃ j, ⊤ ≤ (F.ex i₂ Pm' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j ∧
        t0 * θ' (h w) * fr' j (h w) = ∑ m, θ ((p : ℂ) • (w + wm m)) * fr' j (h w + h (wm m)) := by
  subst hu hu'
  have hCk : ψp.ker = C := hk.2.2.2.2.2.1
  obtain ⟨gam, h, hg1, hg2, -, hex⟩ := GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog E H Dw l Xo _ g _ F i₁ i₂ Pm Pm' p C
    ψ ψp hP hP' hp hC2 hk
  have eadd := F.ex_add i₁ Pm hP
  have eadd' := F.ex_add i₂ Pm' hP'
  have eker := F.ex_ker i₁ Pm hP
  have eker' := F.ex_ker i₂ Pm' hP'
  have hspan : Submodule.span ℝ (Pm.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hP.2.2.2.1
  have hsmul : ∀ (d : ℂ) z w, hermForm (d • Hm) z w = d * hermForm Hm z w := fun d z w => by
    simp only [hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin g) (Fin g) ℂ, ∀ z, M *ᵥ z = h z :=
    ⟨LinearMap.toMatrix' h.toLinearMap, fun z => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
  have hpR : ((p : ℂ) ^ 2) = (((p : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hHH : ∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w := by
    have key := GlobalTheory.UnitFrameGen.hermForm_eq_of_im _ hspan (((p : ℂ) ^ 2) • Hm) Hm' M (by
      rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
      rw [hM, hM, ← hg2, ← hg2, him', hg1, hsmul, hpR, Complex.im_ofReal_mul, him]
      push_cast; ring)
    intro z w
    rw [← hM, ← hM, key, hsmul]
  have hpow : ∀ (m : ℕ) w, F.ex i₁ Pm (m • w) = F.ex i₁ Pm w ^ m := fun m w => by
    induction m with
    | zero => rw [zero_smul, pow_zero]; exact (eker 0).2 ⟨0, map_zero Pm⟩
    | succ m ih => rw [succ_nsmul, eadd, ih, pow_succ]
  have hL : ∀ a ∈ Pm.range, h a ∈ Pm'.range := by
    rintro _ ⟨a, rfl⟩; exact ⟨gam a, hg2 a⟩
  have hhol := GlobalTheory.ClassUniq.isHolTo_ex F i₁ Pm hP
  have hhol' := GlobalTheory.ClassUniq.isHolTo_ex F i₂ Pm' hP'
  have hfr := _root_.GlobalTheory.HeckeEx.frame_pull_eq_transition_mul E H Dw l Xo (F.u i₁ Pm) (F.u i₂ Pm') p ψp b g Pm.range Pm'.range (F.ex i₁ Pm)
    (F.ex i₂ Pm') h hspan hhol hhol' eadd (fun a ha => (eker a).2 ha) hex hL hb0 hbt hbr (hbh g _ hhol) Hm χl fr hH
    hd hn hc h0 (by rintro _ ⟨a, rfl⟩ j z; exact ha a j z) Hm' χl' fr' hHH hd' hc' h0'
    (by rintro _ ⟨a, rfl⟩ j z; exact ha' a j z)
  choose wm hwm using fun m => F.ex_onto i₁ Pm hP (cr m)
  have hwmΛ : ∀ m, ∃ b', h (wm m) = Pm' b' := fun m => by
    have e1 : F.ex i₂ Pm' (h (wm m)) = 1 := by
      rw [hex, hwm, ← MonoidHom.mem_ker, hCk]; exact hr.1 m
    obtain ⟨b', hb'⟩ := (eker' _).1 e1
    exact ⟨b', hb'.symm⟩
  refine ⟨h, wm, fun a => ⟨gam a, (hg2 a).symm⟩, hHH, hwmΛ, fun w => ?_⟩
  obtain ⟨j, hj⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (F.ex i₂ Pm' (h w)).left
  refine ⟨j, hj, ?_⟩
  have hjz : ⊤ ≤ (ψp (F.ex i₁ Pm w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [← hex]; exact hj
  choose jm hjm using fun m => GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((cr m * F.ex i₁ Pm w) ^ p).left
  have hsum := hbv (F.ex i₁ Pm w) j jm hjz hjm
  have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk (F.u i₂ Pm'))) (ψp (F.ex i₁ Pm w)))
  have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk (F.u i₂ Pm'))) (ψp (F.ex i₁ Pm w)))
  rw [← hex] at hsum e1 e2
  rw [hv' j (h w) _ e1 e2 hj] at hsum
  rw [_root_.mul_assoc, hsum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hq : cr m * F.ex i₁ Pm w = F.ex i₁ Pm (w + wm m) := by rw [← hwm, ← eadd, add_comm]
  have hpw : F.ex i₁ Pm (w + wm m) ^ p = F.ex i₁ Pm ((p : ℂ) • (w + wm m)) := by
    rw [Nat.cast_smul_eq_nsmul, hpow]
  have hjm' := hjm m
  rw [hq, hpw] at hjm' ⊢
  have f1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk (F.u i₁ Pm))) (F.ex i₁ Pm ((p : ℂ) • (w + wm m))))
  have f2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk (F.u i₁ Pm))) (F.ex i₁ Pm ((p : ℂ) • (w + wm m))))
  rw [hv (jm m) _ _ f1 f2 hjm']
  obtain ⟨b', hb'⟩ := hwmΛ m
  have hjw : ⊤ ≤ (F.ex i₂ Pm' (h (w + wm m))).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
    rw [map_add (f := _), eadd', hb', (eker' _).2 ⟨b', rfl⟩, _root_.mul_one]; exact hj
  have hf := hfr (w + wm m) j (jm m) hjw hjm'
  rw [map_add (f := _)] at hf
  rw [hf]; ring

theorem hecke_theta_value_identity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U →
  ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
    admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z →
  ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (Pm : (F.Di (ik k)).La →+ (Fin g → ℂ)) (Pm' : (F.Di (ik k')).La →+ (Fin g → ℂ)),
    IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm →
    IsPeriod (F.Di (ik k')) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm' →
    (U.un k x).x = F.u (ik k) Pm → (U.un k' x').x = F.u (ik k') Pm' →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di (ik k)).EF a b) →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex (ik k) Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (F.ex (ik k) Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) →
    (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
      pt ≫ Formalism.L2.PjFree.gxFst (U.un k x).x = (F.ex (ik k) Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ' : (Fin g → ℂ) → ℂ),
    Hm'.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) →
    (∀ a b, (hermForm Hm' (Pm' a) (Pm' b)).im = (F.Di (ik k')).EF a b) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (F.ex (ik k') Pm' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (F.ex (ik k') Pm' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' (U.un k' x').x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a j z, ‖χl' (Pm' a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' (Pm' a) * Complex.exp (Real.pi * hermForm Hm' z (Pm' a) +
        Real.pi / 2 * hermForm Hm' (Pm' a) (Pm' a)) * fr' j (z + Pm' a))) →
    (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k' x').x),
      pt ≫ Formalism.L2.PjFree.gxFst (U.un k' x').x = (F.ex (ik k') Pm' z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (U.un k' x').x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k' x').x).U (fun _ => j)) ((U.un k' x').s.f (fun _ => j)) = θ' z * fr' j z) →
  ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (wm : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)),
    (∀ a, ∃ b, h (Pm a) = Pm' b) ∧ (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) ∧
    (∀ m, ∃ b, h (wm m) = Pm' b) ∧
    ∀ w, ∃ j, ⊤ ≤ (F.ex (ik k') Pm' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j ∧
      Formalism.L2.PjFree.toC (t none : CAt σ) * θ' (h w) * fr' j (h w) =
        ∑ m, θ ((p : ℂ) • (w + wm m)) * fr' j (h w + h (wm m)) := by
  intro E _ _ _ H Dw l Xo c σ r U _ _ P p i k k' x x' C z t hA hK hz hb g e F ik Pm Pm' hP hP' hu hu'
    Hm χl fr θ hH _ him hd hn hc h0 ha hv Hm' χl' fr' θ' _ _ him' hd' _ hc' h0' ha' hv'
  obtain ⟨ψ, ψp, n, cr, b, hk, hr, hb0, hbt, hbr, hbh, hbv⟩ := _root_.GlobalTheory.HeckeValues.hkPtC_values E H Dw l Xo c σ p (U.un k x) z C hz
  have hcard : n = Ideal.absNorm P ^ i := by
    letI := fieldCAt σ
    haveI := algClosedCAt σ
    exact GlobalTheory.ThetaTrace.card_reps hA.2.2.1.pos hK hr
  subst hcard
  obtain ⟨hzx, -, hbc⟩ := hb
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) (U.un k' x').x z.x
      (U.un k' x').s z.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have hv'' : ∀ j w (pt : Sp ℂ ⟶ Gx z.x), pt ≫ Formalism.L2.PjFree.gxFst z.x = (F.ex (ik k') Pm' w).left →
      pt ≫ Formalism.L2.PjFree.gxSnd z.x = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex (ik k') Pm' w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx z.x).U (fun _ => j)) (z.s.f (fun _ => j)) =
        Formalism.L2.PjFree.toC (t none : CAt σ) * (θ' w * fr' j w) := by
    intro j w pt e1 e2 hj
    have hw0' : (F.ex (ik k') Pm' w).left ≫ Xo.univ.t.G.hom = ((U.un k' x').x : Sp ℂ ⟶ Xo.X) :=
      (Over.w (F.ex (ik k') Pm' w)).trans hu'.symm
    exact GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hzx _ _ _ hbc'
      (Over.homMk (F.ex (ik k') Pm' w).left hw0') j _ _
      (fun pt' h1 h2 => hv' j w pt' h1 h2 hj)
      (fun pt' h1 h2 => by
        obtain rfl : pt' = pt := Limits.pullback.hom_ext (h2.trans e2.symm) (h1.trans e1.symm)
        rfl)
  exact core E H Dw l Xo c σ P p i (U.un k x).x z.x (U.un k x).s z.s C ψ ψp cr b _ hA.2.2.1
    (fun a ha => GlobalTheory.HkPts.pow_eq_one hA.2.2.2.1 hK ha) hk hr hb0 hbt hbr hbh hbv g e F (ik k) (ik k') Pm Pm' hP hP'
    hu (hzx.trans hu') Hm χl fr θ hH him hd hn hc h0 ha hv Hm' χl' fr' θ' him' hd' hc' (by rw [hzx]; exact h0') ha' hv''

end GlobalTheory.HeckeValueId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresLinearAtRingPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

open GlobalTheory.HeckeFrCompare (gx_ext toFib_fst toFib_fst_assoc toFib_snd)
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (push toFib)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

def overCast {T' X : Scheme.{0}} {u v : T' ⟶ X} (e : u = v) : (Over.mk u : Over X) ⟶ Over.mk v :=
  Over.homMk (𝟙 _) (by simp [e])

@[simp] theorem overCast_left {T' X : Scheme.{0}} {u v : T' ⟶ X} (e : u = v) : (overCast e).left = 𝟙 _ := rfl

theorem overCast_comp_left {T' X : Scheme.{0}} {u v : T' ⟶ X} (e : u = v) {G : Over X} (a : Over.mk v ⟶ G) :
    (overCast e ≫ a).left = a.left := by
  rw [Over.comp_left, overCast_left, Category.id_comp]

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

@[reassoc] theorem hkLift_act (hx : x = h ≫ Z.π₁) (r : 𝓞 E) :
    (Over.mk x ◁ Xo.univ.t.act.act r).left ≫ hkLift Z h hx = hkLift Z h hx ≫ (Z.o₁.t.act.act r).left := by
  refine Z.m₁.cart.1.hom_ext ?_ ?_
  · rw [Category.assoc, hkLift_φ, Category.assoc, Z.m₁.act, hkLift_φ_assoc, ← Over.comp_left, whiskerLeft_snd,
      Over.comp_left]
  · rw [Category.assoc, hkLift_hom, Category.assoc, Over.w, hkLift_hom, ← Category.assoc, ← Over.comp_left,
      whiskerLeft_fst]

def hkLiftPt (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (Over.mk (t ≫ h) : Over Z.Hk) ⟶ Z.o₁.t.G :=
  Over.homMk (toFib x t a ≫ hkLift Z h hx) (by
    rw [Category.assoc, hkLift_hom, toFib_fst_assoc]; rfl)

theorem hkLiftPt_left (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (hkLiftPt Z hx t a).left = toFib x t a ≫ hkLift Z h hx := rfl

theorem hkLiftPt_φ (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (hkLiftPt Z hx t a).left ≫ Z.m₁.cm.F = a.left := by
  rw [hkLiftPt_left, Category.assoc, hkLift_φ, toFib_snd]

theorem hkLiftPt_mul (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a₁ a₂ : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    hkLiftPt Z hx t (a₁ * a₂) = hkLiftPt Z hx t a₁ * hkLiftPt Z hx t a₂ := by
  have e : (t ≫ h) ≫ Z.π₁ = t ≫ x := by rw [hx, Category.assoc]
  have key := Z.m₁.cart.2 (Over.mk (t ≫ h)) (hkLiftPt Z hx t a₁) (hkLiftPt Z hx t a₂) (overCast e ≫ a₁)
    (overCast e ≫ a₂) (by rw [overCast_comp_left, hkLiftPt_φ]) (by rw [overCast_comp_left, hkLiftPt_φ])
  refine Over.OverMorphism.ext (Z.m₁.cart.1.hom_ext ?_ ?_)
  · rw [hkLiftPt_φ, ← key, ← MonObj.comp_mul, overCast_comp_left]
  · rw [Over.w, Over.w]

theorem push_hkMap (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) {T' : Scheme.{0}} (t : T' ⟶ Sp T)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    push (hkMap Z hx hx') t a = (hkLiftPt Z hx t a ≫ Z.ψ).left ≫ Z.m₂.cm.F := by
  rw [push, hkMap_snd, Over.comp_left, hkLiftPt_left]
  simp only [Category.assoc]

theorem isLinHom_hkMap (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : IsLinHom (hkMap Z hx hx') := by
  haveI : IsMonHom Z.ψ := Z.isog.1.1
  refine ⟨hkMap_fst Z hx hx', fun T' t a₁ a₂ b₁ b₂ h₁ h₂ => ?_, fun r => ?_⟩
  · have e : (t ≫ h) ≫ Z.π₂ = t ≫ x' := by rw [hx', Category.assoc]
    have key := Z.m₂.cart.2 (Over.mk (t ≫ h)) (hkLiftPt Z hx t a₁ ≫ Z.ψ) (hkLiftPt Z hx t a₂ ≫ Z.ψ) (overCast e ≫ b₁)
      (overCast e ≫ b₂) (by rw [overCast_comp_left, h₁, push_hkMap]) (by rw [overCast_comp_left, h₂, push_hkMap])
    rw [push_hkMap, hkLiftPt_mul, MonObj.mul_comp, ← key, ← MonObj.comp_mul, overCast_comp_left]
  · have w : ∀ z : Sp T ⟶ Xo.X, (Over.mk z ◁ Xo.univ.t.act.act r).left ≫ (snd (Over.mk z) Xo.univ.t.G).left =
        (snd (Over.mk z) Xo.univ.t.G).left ≫ (Xo.univ.t.act.act r).left := fun z => by
      rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
    have w₀ : ∀ z : Sp T ⟶ Xo.X, (Over.mk z ◁ Xo.univ.t.act.act r).left ≫ (fst (Over.mk z) Xo.univ.t.G).left =
        (fst (Over.mk z) Xo.univ.t.G).left := fun z => by
      rw [← Over.comp_left, whiskerLeft_fst]
    have hψ : (Z.o₁.t.act.act r).left ≫ Z.ψ.left = Z.ψ.left ≫ (Z.o₂.t.act.act r).left := by
      rw [← Over.comp_left, Z.isog.1.2.2.2.2.1 r, Over.comp_left]
    refine gx_ext ?_ ?_
    · rw [Category.assoc, hkMap_fst, w₀, Category.assoc, w₀, hkMap_fst]
    · rw [Category.assoc, hkMap_snd, hkLift_act_assoc, reassoc_of% hψ, Z.m₂.act, Category.assoc, w,
        hkMap_snd_assoc]

end GlobalTheory.HeckeEx

end

theorem GlobalTheory.HeckeEx.isLinHom_hkMap_target : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), IsLinHom (hkMap Z hx hx') :=
  fun _ _ _ _ _ _ _ _ _ _ _ Z _ _ _ _ _ hx hx' => GlobalTheory.HeckeEx.isLinHom_hkMap Z hx hx'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresPreservesOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

private theorem one_left_eq_eSec {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {Y : Scheme.{0}} (y : Y ⟶ S) :
    (1 : Over.mk y ⟶ G).left = y ≫ eSec G := by
  rw [eSec]
  show (toUnit _ ≫ η[G]).left = _
  rw [Over.comp_left]
  congr 1

private theorem eSec_hom {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : eSec G ≫ G.hom = 𝟙 _ := by
  rw [eSec]
  have := Over.w η[G]
  simpa using this

theorem hkMap_ptSec_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkMap Z hx hx' = (ptSecT Xo.univ.t.G (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := by
  intro E _ _ _ H Dw l Xo P p i Z T _ h x x' hx hx'
  have key₁ : (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkLift Z h hx = h ≫ eSec Z.o₁.t.G := by
    apply Z.m₁.cart.1.hom_ext
    · rw [Category.assoc, hkLift_φ, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec, Category.assoc,
        Z.m₁.cm.e_comm, Z.m₁.base, ← Category.assoc, ← hx]
    · rw [Category.assoc, hkLift_hom, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst_assoc, Category.assoc, eSec_hom]
      simp
  haveI := Z.isog.1.1
  have hψ : eSec Z.o₁.t.G ≫ Z.ψ.left = eSec Z.o₂.t.G := by
    rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  apply GlobalTheory.HeckeFrCompare.gx_ext
  · rw [Category.assoc, hkMap_fst, ptSecT, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst, GlobalTheory.HeckeFrCompare.lift_l_fst]
    rfl
  · rw [Category.assoc, hkMap_snd, ← Category.assoc, key₁, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec,
      Category.assoc, ← Category.assoc (eSec _), hψ, Z.m₂.cm.e_comm, Z.m₂.base, ← Category.assoc, ← hx']

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstanceIotaReadoutRealTrivialStabilizerUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjReadIota

variable {D : D7}

theorem mem_Kset_iff_mem_St (β : GL (Fin (Yc D 0).rank) (EAf D))
    (hβ : IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) :
    x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset ↔ (x.1 : GL (Fin (Yc D 0).rank) (EAf D)) ∈ St β := by
  rw [GlobalTheory.ConjPlaceRed.crdLat_eq_latFrame] at hβ
  refine ⟨GlobalTheory.ConjPlaceRed.mem_St_of_Kset D β x hβ, fun hx => ?_⟩
  obtain ⟨h1, h2⟩ := (GlobalTheory.LevSplit.mem_St_iff β _ hβ (x.1 : GL (Fin (Yc D 0).rank) (EAf D))).1 hx
  intro v
  constructor
  · intro hv
    exact (GlobalTheory.ConjPlaceRed.mem_Lf D _).1 (h1 v ((GlobalTheory.ConjPlaceRed.mem_Lf D v).2 hv))
  · intro hv
    have h3 := h2 _ ((GlobalTheory.ConjPlaceRed.mem_Lf D _).2 hv)
    have e : Matrix.mulVec ((x.1 : GL (Fin (Yc D 0).rank) (EAf D))⁻¹).val
        (Matrix.mulVec (x.1 : GL (Fin (Yc D 0).rank) (EAf D)).val v) = v := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have h4 : v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.PlaceModel.latFrame (Yc D 0)) := e ▸ h3
    exact (GlobalTheory.ConjPlaceRed.mem_Lf D v).1 h4

theorem instanceIota_real_finite_stabilizer_unitary_characterization {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (hβ : IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) (κ : GA D (Yc D 0)) :
    ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) κ).1 = 1 ↔ κ ∈ GfC (Yc D 0)) ∧
    ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) κ).2 ∈ I.Kset ↔ finE (Yc D 0) κ ∈ St β) ∧
    finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram := by
  subst h
  have e : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D κ) = κ := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ
  have h1 := Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  have hf := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  rw [e] at h1 hf
  change ((Formalism.IndefR.RationalEmbedding.iota D κ).1 = 1 ↔ κ ∈ GfC (Yc D 0)) ∧
    ((Formalism.IndefR.RationalEmbedding.iota D κ).2 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset ↔ finE (Yc D 0) κ ∈ St β) ∧
    finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram
  refine ⟨h1.symm, ?_, ?_⟩
  · rw [mem_Kset_iff_mem_St β hβ]
    exact iff_of_eq (congrArg (· ∈ St β) hf.symm)
  · have := ((Formalism.IndefR.RationalEmbedding.iota D κ).2).2
    exact hf ▸ this

theorem read_iota : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ κ : GA D (Yc D 0), (((iotaX X h).toMulEquiv κ).1 = 1 ↔ κ ∈ GfC (Yc D 0)) ∧ (((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset ↔ finE (Yc D 0) κ ∈ St β) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram := by
  intro D X h β hβ κ
  exact instanceIota_real_finite_stabilizer_unitary_characterization h β hβ κ

end GlobalTheory.SeeConjReadIota
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfHarishChandra
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ArchRec

theorem itLine_of_hypotheses :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D :=
  _root_.GlobalTheory.Chain.RealLine.itLine_of_discreteSeries

end GlobalTheory.ArchRec
end

