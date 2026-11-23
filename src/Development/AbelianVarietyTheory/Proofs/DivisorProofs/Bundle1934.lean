module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionCoordinatesEqDegenerationSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0055
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricThetaTranslatesExpandSeriesFamilies
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefBasic GlobalTheory.UT.SymFrame GlobalTheory.Ex.GtValues GlobalTheory.Ex.CoordSeries

theorem symTranslate_expandsF : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1) (c : C), U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → ∀ m : ℕ, Odd m → ∀ (p : QkPt D.toPre C (m ^ 2)) (q : N.QT (m ^ 2)) (z : TFK (R := V) C ⟶ A.A), ν.QPt p q → QkToAkU U.toUnifPre C (m ^ 2) p z → ∃ (Θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) C)) (t : GlobalTheory.UT.SecA A C (m ^ 2)) (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C), SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) z Θ ∧ Tr A ρ m th Θ t ∧ U.ExpandsF C (m ^ 2) w₀ t s ∧ IsEvFam N m q f ∧ ν.FamV s (c • f) := by
  intro V _ _ _ _ hcpl D A G _ _ hG U C _ _ _ _ _ _ hC N ν _ w₀ ρ hN th ϑ c hth hϑ m hm p q z hq hz
  have hL : GlobalTheory.UT.LL := GlobalTheory.Ex.hv_holds.1
  have hfam : BrFamSt := GlobalTheory.Ex.brFam hL.1 hL.2.1
  have hB : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  have hLB := A.isLB
  let y : Sp C := IsLocalRing.closedPoint C

  have hgt : ∀ b : N.A, ∃ h : N.Gt, h.b = b := fun b => by
    obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_lift (D := D.toPre) (F := C) (ν.eA b)
    obtain ⟨h, hh⟩ := GtValues.exists_val ν g
    exact ⟨h, ν.eA.injective (hh.1.trans hg)⟩
  have main : ∀ (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1) (c : C), U.ExpandsF C 1 w₀ th ϑ →
      ν.FamV ϑ (c • N.vth) → ∃ (Θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) C)) (t : GlobalTheory.UT.SecA A C (m ^ 2))
        (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C),
        SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) z Θ ∧ Tr A ρ m th Θ t ∧ U.ExpandsF C (m ^ 2) w₀ t s ∧ ν.FamV s f ∧
        (∀ (h : N.Gt) (χ : N.X), f (q.1.1.toAdd + m • χ) h.b * h.s (q.1.1.toAdd + m • χ) = c * N.evT m q h χ) ∧
        ∀ β, (∀ χ, β ≠ q.1.1.toAdd + m • χ) → ∀ x, f β x = 0 := by
    intro th ϑ c hth hϑ
    obtain ⟨⟨_, _⟩, ⟨α, s₁, -, hα, hαn, hs₁, -⟩, -⟩ :=
      GlobalTheory.existsUnique_thetaConst hL V A C ρ hN.2.1 m hm th 1 (one_pow _)
    have hbij := (expBijF_and_expandsF_lin hL V _ hB D A G hG U).1 C (m ^ 2) hm2 w₀ hN.1
    obtain ⟨σ₁, hσ₁, -⟩ := hbij.1 s₁
    obtain ⟨hv₁, -, -, -, -, hv₂⟩ := hfam V D.toPre D.psi_even D.tau_bimult C N ν (m ^ 2) hm2
    obtain ⟨f₁, hf₁, -⟩ := hv₁ σ₁
    obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (IntEnd.exists_nsmul_and_neg hL V _ hB D A G hG U).1 m
    have hsm : ∀ {X : Type} [AddCommGroup X] [Module.Free ℤ X], Function.Injective fun χ : X => m • χ := by
      intro X _ _ a b h
      have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using h
      exact smul_right_injective _ (Int.natCast_ne_zero.2 hm0) h'
    have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
    have hpull := (PullExp.main hL V _ hB D A G hG U C E hinj (m ^ 2) 1 le_rfl hm2
      (exists_gen_pow U.LG U.cubG U.symG U.symG_gen m E.aG hEG)).2 w₀ ρ hN (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _)
      (lift_fst _ _) (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α hα hαn th s₁ ϑ σ₁ hth hσ₁ hs₁
    rw [hEB] at hpull
    obtain ⟨κ, hκ⟩ := exists_kap (D := D.toPre) hL.1.mulPull m
    have pull : ∀ h : N.Gt, (∀ χ, f₁ (m • χ) h.b * h.s (m • χ) =
        c * N.vt (h ^ m) χ * ((mulq N.θ N.σ m h.b)⁻¹ : Cˣ)) ∧ ∀ β, (∀ χ, β ≠ m • χ) → f₁ β h.b = 0 := fun h => by
      obtain ⟨g, hg⟩ := GtValues.exists_pt ν h
      obtain ⟨g', hg'⟩ := GtValues.exists_pt ν (h ^ m)
      have act := (hEact C g g').2 ((isNsmul_val ν m hg hg').2 rfl)
      obtain ⟨W, hW⟩ := (coef_basic V D.toPre C (m ^ 2) g).1
      obtain ⟨w, hw, hwv⟩ := exists_frm_kap (act.1.trans (congrArg _ hEB)) W hW κ hκ.1
      obtain ⟨r₁, r₂⟩ := hpull κ hκ g g' act W w hW hw hwv
      have hJ := good ν y
      have e₁ : val κ g.b.left y ν.J = _ := hg.1 ▸ kap_eq ν hL.1.globalFns hκ y h.b
      have e₂ : vF w (𝟙 (Sp C)) ν.J = vF W (𝟙 (Sp C)) ν.J * ((mulq N.θ N.σ m h.b)⁻¹ : Cˣ) :=
        (toStk y).injective ((GtValues.toStk_vF _ _ hJ).trans ((congrArg Units.val (hwv y ν.J hJ)).symm.trans
          (((Units.val_mul _ _).trans (congrArg₂ (· * ·) (GtValues.toStk_vF _ _ hJ).symm (congrArg Units.val e₁))).trans
            (map_mul (toStk y) _ _).symm)))
      refine ⟨fun χ => mul_right_cancel₀ (vF_ne ν W) ?_, fun β hβ => ?_⟩
      · have a := r₁ (ν.eX χ)
        rw [hEh, ← map_nsmul, coef_val ν hf₁ hg hW, coef_theta ν hϑ hg' hw, e₂] at a
        rw [a]; ring
      · have a := r₂ (ν.eX β) (by
          rintro ⟨χ, e⟩
          exact hβ (ν.eX.symm χ) (ν.eX.injective (by rw [map_nsmul, ν.eX.apply_symm_apply, ← hEh, e])))
        rw [coef_val ν hf₁ hg hW] at a
        exact (mul_eq_zero.1 ((mul_eq_zero.1 a).resolve_right (vF_ne ν W))).resolve_right (Units.ne_zero _)
    obtain ⟨⟨_, _⟩, ⟨_, _, θ, -, -, -, hθ, -⟩, -⟩ :=
      GlobalTheory.existsUnique_thetaConst hL V A C ρ hN.2.1 m hm th z (hz w₀ hN.1).1
    obtain ⟨t, ht⟩ := ThetaPtExist.exists_isTwistPull hLB (translT A.A θ.pt) (translPt A.A θ.pt) (lift_snd _ _)
      ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) θ.φ θ.isGen s₁
    obtain ⟨σ, hσ, -⟩ := hbij.1 t
    obtain ⟨f, hf, -⟩ := hv₁ σ
    obtain ⟨w, hw⟩ := (SymFrame.main hL V _ hB D C (m ^ 2) hm.pow p).1
    have hΦ := symLift_acts_as_phi hL V _ hB D A G hG U C (m ^ 2) hm.pow p z hz θ hθ w₀ hN.1 w hw s₁ t σ₁ σ
      hσ₁ hσ ht
    obtain rfl := (hv₂ p q w _ σ₁ σ f₁ f hq hw.1 (txFrame_val ν hL.1 hm.pow hq hw) hf₁ hf).1 hΦ
    have on : ∀ (h : N.Gt) (χ : N.X), N.phi q (N.wQ q) f₁ (q.1.1.toAdd + m • χ) h.b * h.s (q.1.1.toAdd + m • χ) =
        c * N.evT m q h χ := fun h χ => by
      rw [add_comm]
      exact phi_term N m q h f₁ c χ ((pull _).1 χ)
    have off : ∀ β, (∀ χ, β ≠ q.1.1.toAdd + m • χ) → ∀ x, N.phi q (N.wQ q) f₁ β x = 0 := fun β hβ x => by
      obtain ⟨h, hh⟩ := hgt (x * q.1.2.b)
      have a := (pull h).2 (β - q.1.1.toAdd) fun χ e => hβ χ (by rw [← e, add_sub_cancel])
      rw [hh] at a
      rw [NumD.phi, a, mul_zero]
    exact ⟨θ, t, σ, _, hθ, ⟨α, s₁, hα, hαn, hs₁, ht⟩, hσ, hf, on, off⟩
  obtain ⟨Θ, t, s, f, h1, h2, h3, h4, h5, h6⟩ := main th ϑ c hth hϑ
  refine ⟨Θ, t, s, ?_⟩
  by_cases hc : c = 0
  · subst hc
    obtain ⟨th', ϑ', c₀, hc₀, hth', hϑ', -⟩ := exists_theta hL hfam U hN.1 ν
    obtain ⟨-, -, -, f', -, -, -, -, h5', h6'⟩ := main th' ϑ' c₀ hth' hϑ'
    refine ⟨c₀⁻¹ • f', h1, h2, h3, ⟨fun h χ => ?_, fun β hβ x => ?_⟩, ?_⟩
    · rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, h5', inv_mul_cancel_left₀ hc₀]
    · rw [Pi.smul_apply, Pi.smul_apply, h6' β hβ x, smul_zero]
    · rw [zero_smul]
      convert h4 using 1
      funext β x
      rw [Pi.zero_apply, Pi.zero_apply]
      by_cases hβ : ∃ χ, β = q.1.1.toAdd + m • χ
      · obtain ⟨χ, rfl⟩ := hβ
        obtain ⟨h, rfl⟩ := hgt x
        have e := h5 h χ
        rw [zero_mul] at e
        exact ((mul_eq_zero.1 e).resolve_right (Units.ne_zero _)).symm
      · push_neg at hβ
        exact (h6 β hβ x).symm
  · refine ⟨c⁻¹ • f, h1, h2, h3, ⟨fun h χ => ?_, fun β hβ x => ?_⟩, ?_⟩
    · rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, h5, inv_mul_cancel_left₀ hc]
    · rw [Pi.smul_apply, Pi.smul_apply, h6 β hβ x, smul_zero]
    · rwa [smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentLettersIntegralLieBasisEigenframeRelation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM fullB tv)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LamT.TanRel

open MonoidalCategory CartesianMonoidalCategory GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.IntLie GlobalTheory.LamT.LetterInt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem tvOf_congr {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {v v' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : v = v') (hv : IsTanAt x v) (hv' : IsTanAt x v') :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf hv = ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf hv' := by
  subst h; rfl

theorem bc_tan {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap ψ ≫ x) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}
    (hπ : IsGrpPullback A Xo.univ.t.G x π) (w : epsR S ⟶ A) (ht : IsTangent w) :
    IsTanAt x' (spMap (dualMap ψ) ≫ w.left ≫ π) := by
  subst hx
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tan_bc ψ ((GlobalTheory.KSExist.FrameLift.tan_iff hπ w).2 ht)

theorem bc_comb {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap ψ ≫ x) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}
    (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (v : Fin n → (epsR S ⟶ A))
    (hvt : ∀ k, IsTanAt x' (spMap (dualMap ψ) ≫ (v k).left ≫ π)) (cf : Fin n → S) (w : epsR S ⟶ A)
    (h : IsLieComb cf v w) (hw : IsTanAt x' (spMap (dualMap ψ) ≫ w.left ≫ π)) :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf hw = ∑ k, ψ (cf k) • ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (hvt k) :=
  (ReciprocityTheory.ChartRestriction.G.PullbackSections.combAt_iff _ hvt _ hw).1
    (GlobalTheory.Frames.ChgBC.isCombAt_pull ψ hx (fun _ => rfl) rfl (GlobalTheory.LieBasisRing.isCombAt_of_isLieComb hπ v cf w h))

end GlobalTheory.LamT.TanRel

namespace GlobalTheory.LamT.TanRel

open MonoidalCategory CartesianMonoidalCategory GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.IntLie GlobalTheory.LamT.LetterInt


set_option maxHeartbeats 1000000 in
theorem tangent_letter_model_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : GlobalTheory.LamT.LocMod z T iK),
    (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) →
    ∀ A : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) z.K, GlobalTheory.LamF.IsModelAt z.B.pol z.Φ.key z.m'.φ p A →
    letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
    ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
      (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
      φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → (∀ b, IsUnit (g b).det) →
      GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u →
      ∃ (nu mu : Fin z.Φ.T.g → TanM yT.x Xo.univ.t.G) (C : (Σ b : E →+* ℂ, Fin (Dw.mult b)) → Fin z.Φ.T.g → T.Fr),
        (∀ σ k, C σ k ∈ Set.range (algebraMap T.V T.Fr)) ∧
        (∀ σ, fullB yT σ = ∑ k, iK (z.U (z.e σ) k) • nu k) ∧
        (∀ k, mu k = ∑ l, iK (A k l) • nu l) ∧
        ∀ b i, ∑ j, g b i j • fullB yT ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k := by
  intro E _ _ _ H Dw l Xo c _ z f La hz p T iK M hval A hA
  letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
  intro φ yT y' g a hφ hmap hchg hg hint
  obtain ⟨-, hlet, -, hx, -, hu⟩ := hz
  obtain ⟨vV, hvV, hvw⟩ := _root_.GlobalTheory.LamT.exists_isLieBasis_locMod E H Dw l Xo c z p T iK M hval A hA
  choose wK hwK hwV using hvw
  have hxT : yT.x = spMap iK ≫ z.x := by rw [hmap.1, hφ, hx]
  have hK := LieComb.lieComb_algebra z.K z.Φ.T.t.G _ z.Φ.v z.Φ.basis.1
  have tv0 : ∀ w : epsR z.K ⟶ z.Φ.T.t.G, IsTangent w →
      IsTanAt yT.x (spMap (dualMap iK) ≫ w.left ≫ z.Φ.m.φ) := fun w ht =>
    bc_tan iK hxT z.Φ.m.cart w ht
  have hvt : ∀ k, IsTanAt yT.x (spMap (dualMap iK) ≫ (z.Φ.v k).left ≫ z.Φ.m.φ) := fun k =>
    tv0 (z.Φ.v k) (z.Φ.basis.1 k)
  have key : ∀ (cf : Fin z.Φ.T.g → z.K) (w : epsR z.K ⟶ z.Φ.T.t.G), IsLieComb cf z.Φ.v w →
      ∀ hw : IsTanAt yT.x (spMap (dualMap iK) ≫ w.left ≫ z.Φ.m.φ),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf hw = ∑ k, iK (cf k) • ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (hvt k) :=
    fun cf w h hw => bc_comb iK hxT z.Φ.m.cart z.Φ.v hvt cf w h hw
  have hmt : ∀ k, IsTanAt yT.x (spMap (dualMap iK) ≫ (wK k).left ≫ z.Φ.m.φ) := fun k =>
    tv0 (wK k) (hK.2.1 _ _ (hwK k))

  obtain ⟨ub, hubt, -, -, hl⟩ := hint
  choose u' hu1 hu2 using hl
  let ubR : ∀ b i, epsR T.V ⟶ M.G.t.G := fun b i => Over.homMk (ub b i).left (Over.w (ub b i))
  have hubR : ∀ b i, IsTangent (ubR b i) := fun b i => by
    have h := hubt b i
    unfold IsTan at h
    unfold IsTangent
    refine h.trans ?_
    have e : (1 : ptOver T.V T.V ⟶ M.G.t.G) = toUnit _ ≫ η[M.G.t.G] := rfl
    rw [e, Over.comp_left]
    have e2 : (toUnit (ptOver T.V T.V)).left = 𝟙 (Sp T.V) := by
      have := Over.w (toUnit (ptOver T.V T.V))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact Category.id_comp _
  choose C' hC' using fun b i => (hvV.2 (ubR b i) (hubR b i)).exists

  have hsq : ∀ k, (spMap (dualMap iK) ≫ (wK k).left) ≫ z.Φ.T.t.G.hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap iK := fun k => by
    rw [Category.assoc, Over.w (wK k)]
    exact (spMap_comp₂ _ _).trans ((congrArg spMap (IntLie.dualMap_alg iK)).trans (spMap_comp₂ _ _).symm)
  let s' : Fin z.Φ.T.g → (Sp (DualNumber T.Fr) ⟶ M.t'.t.G.left) := fun k => M.n'.cart.1.lift _ _ (hsq k)
  have hs1 : ∀ k, s' k ≫ M.n'.φ = spMap (dualMap iK) ≫ (wK k).left := fun k => M.n'.cart.1.lift_fst _ _ _
  have hs2 : ∀ k, s' k ≫ M.t'.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := fun k =>
    M.n'.cart.1.lift_snd _ _ _
  let vV' : Fin z.Φ.T.g → (epsOver T.V T.V ⟶ M.G.t.G) := fun k => Over.homMk (vV k).left (Over.w (vV k))
  have hm2 : ∀ k, s' k ≫ M.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (vV' k).left := fun k => by
    apply M.n.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      refine Eq.trans ?_ (hwV k).symm
      exact (congrArg (s' k ≫ ·) M.h2).trans (by rw [reassoc_of% (hs1 k)])
    · rw [Category.assoc, M.m2.cart.1.w, reassoc_of% (hs2 k), Category.assoc, Over.w (vV' k)]
      exact (spMap_comp₂ _ _).trans ((congrArg spMap (IntLie.dualMap_alg _).symm).trans (spMap_comp₂ _ _).symm)
  have hm1 : ∀ k, s' k ≫ M.m1.φ = spMap (dualMap iK) ≫ (wK k).left ≫ z.Φ.m.φ := fun k => by
    rw [M.h1, reassoc_of% (hs1 k)]
  have hcomb : ∀ b i, IsComb vV' (C' b i) (ub b i) := fun b i => by
    obtain ⟨u, hu, he⟩ := hC' b i
    refine ⟨fun k => Over.homMk (u k).left (Over.w (u k)), fun k => hu k, ?_⟩
    exact he
  have hy't : ∀ b i, IsTanAt yT.x (y'.u b i) := fun b i => by
    rw [← hchg.1]; exact y'.tan b i
  have hgen : ∀ b i, IsCombAt yT.x (fun k => spMap (dualMap iK) ≫ (wK k).left ≫ z.Φ.m.φ)
      (fun k => algebraMap T.V T.Fr (C' b i k)) (y'.u b i) := fun b i => by
    have h := comb_generic M.m1 M.m2 vV' s' hm2 (ub b i) (u' b i) (hu2 b i) (C' b i) (hcomb b i)
    rw [hu1 b i] at h
    simp only [hm1] at h
    rw [hxT]
    exact h
  refine ⟨fun k => ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (hvt k), fun k => ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (hmt k),
    fun σ k => algebraMap T.V T.Fr (C' σ.1 σ.2 k), fun σ k => ⟨_, rfl⟩, ?_, fun k => key _ _ (hwK k) _, ?_⟩
  · rintro ⟨b, j⟩
    obtain ⟨w, hw, hwu⟩ := hu b j
    obtain ⟨w₀, hw₀, hU⟩ := hlet.2.2.1 (z.e ⟨b, j⟩)
    obtain rfl : w₀ = w := by
      refine Over.OverMorphism.ext (z.m'.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
      unfold LamF.LamLetters.IsLetter at hw hw₀
      generalize z.letters.src (z.e ⟨b, j⟩) = s at hw hw₀
      rcases s with q | q
      · exact hw₀.trans hw.symm
      · exact hw₀.trans hw.symm
    have hyu : yT.u b j = spMap (dualMap iK) ≫ w₀.left ≫ z.Φ.m.φ := by
      rw [hmap.2.1 b j, hφ, hwu]
    show ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (yT.tan b j) = _
    rw [tvOf_congr hyu (yT.tan b j) (tv0 w₀ (hK.2.1 _ _ hU))]
    exact key _ _ hU _
  · intro b i
    have h5 := (ReciprocityTheory.ChartRestriction.G.PullbackSections.combAt_iff (yT.u b) (yT.tan b) (g b i) (hy't b i)).1 (hchg.2.1 b i)
    have h4 := (ReciprocityTheory.ChartRestriction.G.PullbackSections.combAt_iff _ hmt _ (hy't b i)).1 (hgen b i)
    exact h5.symm.trans h4

end GlobalTheory.LamT.TanRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentLinearCombinationIsTangent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.SecJet GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.SecJet.TanComb

variable {R : Type} [CommRing R]

theorem zeroPt_w : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (epsR R).hom = (𝟙_ (Over (Sp R))).hom := by
  show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [← Spec.map_id]
  congr 1

def zeroPt : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) zeroPt_w

variable {G : Over (Sp R)} [GrpObj G]

theorem isTangent_iff (v : epsR R ⟶ G) : IsTangent v ↔ zeroPt ≫ v = 1 := by
  have h1 : (1 : 𝟙_ (Over (Sp R)) ⟶ G) = η[G] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [h1, IsTangent]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    simpa [zeroPt] using h
  · intro h
    simpa [zeroPt] using congrArg (fun q => q.left) h

theorem zeroPt_epsScale (c : R) : zeroPt ≫ epsScale R c = zeroPt := by
  apply Over.OverMorphism.ext
  show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (epsScaleR c) = spMap (TrivSqZeroExt.fstHom R R R).toRingHom
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro r
  simp [epsScaleR]

theorem zeroPt_prod (l : List (epsR R ⟶ G)) (hl : ∀ x ∈ l, zeroPt ≫ x = 1) : zeroPt ≫ l.prod = 1 := by
  induction l with
  | nil =>
    rw [List.prod_nil, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (zeroPt ≫ toUnit _) (toUnit _)]
  | cons a l ih =>
    rw [List.prod_cons, MonObj.comp_mul, hl a (List.mem_cons_self ..), ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)), _root_.mul_one]

end GlobalTheory.SecJet.TanComb

namespace GlobalTheory.SecJet

theorem isTangent_tanComb (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (m : ℕ) (v : Fin m → (epsR R ⟶ G))
    (c : Fin m → R) : (∀ i, IsTangent (v i)) → IsTangent (tanComb c v) := by
  intro hv
  rw [TanComb.isTangent_iff, tanComb]
  refine TanComb.zeroPt_prod _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  rw [← Category.assoc, TanComb.zeroPt_epsScale, ← TanComb.isTangent_iff]
  exact hv i

end GlobalTheory.SecJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTranslateLiftsSemiAbelianTripleMap
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.TransLift

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem lift_isTranslate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ X) (x' : Sp R' ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (u : Sp (DualNumber R) ⟶ t.G.left) (u' : Sp (DualNumber R') ⟶ t'.G.left), IsTanAtG t x u → IsTanAtG t' x' u' → u' ≫ m.φ = spMap (dualMap ψ) ≫ u → ∀ (S : Type) [CommRing S] (φS : R' →+* S) (g₀' : Sp S ⟶ t'.G.left), g₀' ≫ t'.G.hom = spMap φS ≫ x' → ∀ w : Sp (DualNumber S) ⟶ t.G.left, IsTranslate t (φS.comp ψ) (g₀' ≫ m.φ) u w → ∃ w' : Sp (DualNumber S) ⟶ t'.G.left, w' ≫ m.φ = w ∧ IsTranslate t' φS g₀' u' w' := by
  intro E _ _ _ H X X' t t' j m R R' _ _ ψ x x' hx u u' hu hu' huu S _ φS g₀' hg₀' w hw
  obtain ⟨w', hw', -⟩ := existsUnique_isTranslate t' φS hg₀' hu'
  refine ⟨w', ?_, hw'⟩
  have hsq : m.φ ≫ t.G.hom = t'.G.hom ≫ j := m.cart.1.w
  have hg : (g₀' ≫ m.φ) ≫ t.G.hom = spMap (φS.comp ψ) ≫ x := by
    rw [Category.assoc, hsq, ← Category.assoc, hg₀', Category.assoc, hx, ← Category.assoc, spMap_comp'']
  obtain ⟨g', v', h₁, h₂, h₃⟩ := hw'
  have ht : IsTranslate t (φS.comp ψ) (g₀' ≫ m.φ) u (w' ≫ m.φ) := by
    let T : Over X' := tEpsG (g₀' ≫ t'.G.hom)
    have heq : (tEpsG ((g₀' ≫ m.φ) ≫ t.G.hom)).hom = T.hom ≫ j := by
      show spMap _ ≫ (g₀' ≫ m.φ) ≫ t.G.hom = (spMap _ ≫ g₀' ≫ t'.G.hom) ≫ j
      rw [Category.assoc, Category.assoc, Category.assoc, hsq]
    let e : tEpsG ((g₀' ≫ m.φ) ≫ t.G.hom) ⟶ Over.mk (T.hom ≫ j) :=
      Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact heq.symm)
    refine ⟨e ≫ pushHom m.cart T g', e ≫ pushHom m.cart T v', ?_, ?_, ?_⟩
    · show 𝟙 _ ≫ g'.left ≫ m.φ = _
      rw [Category.id_comp, h₁, Category.assoc]
    · show 𝟙 _ ≫ v'.left ≫ m.φ = _
      rw [Category.id_comp, h₂, Category.assoc, huu, ← Category.assoc, spMap_comp'', dualMap_comp'']
    · rw [← MonObj.comp_mul, ← map_mul]
      show 𝟙 _ ≫ (g' * v').left ≫ m.φ = _
      rw [Category.id_comp, h₃]
  exact (existsUnique_isTranslate t (φS.comp ψ) hg hu).unique ht hw

end GlobalTheory.TransLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharEntireNeZeroAutomorphy
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem thetaChar_entire_ne_zero_automorphy : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → Half a → Half b → Differentiable ℂ (thetaChar τ a b) ∧ (∃ z, thetaChar τ a b z ≠ 0) ∧ ∀ M N z, thetaChar τ a b (z + perV τ M N) = autV τ a b M N z * thetaChar τ a b z := by
  intro g τ a b hs hp ha hb
  obtain ⟨h1, -⟩ := GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g a b ha hb
  obtain ⟨hd, hne⟩ := h1 τ hs hp
  refine ⟨hd, hne, fun M N z => ?_⟩
  rw [perV, autV]
  unfold cv
  rw [GlobalTheory.ThetaAH.thetaChar_add_period hs a b z M N]
  congr 1
  rw [dotProduct_comm b]
  ring_nf

end GlobalTheory.MBLow.Cl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairLocalSchwartzActionStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pair_local_schwartz_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ (v : Pl (F := F)) (x : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (φ φ₁ φ₂ φ₃ φ₄ : (Fin n × Fin d → Fv F v) → ℂ), φ ∈ SB (Fin n × Fin d → Fv F v) → φ₁ ∈ SB (Fin n × Fin d → Fv F v) →
    φ₂ ∈ SB (Fin n × Fin d → Fv F v) → Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → Acts (evFin F v) (om x) φ φ₂ →
    Acts (evFin F v) (om x) φ₁ φ₃ → Acts (evFin F v) (M.co.rho B.ψ (mat x.1 * u * (mat x.2)ᵀ)) φ₂ φ₄ → φ₄ = φ₃ := by
  first | exact @GlobalTheory.IntertwLocal.local_intertw | exact GlobalTheory.IntertwLocal.local_intertw | (intros; apply GlobalTheory.IntertwLocal.local_intertw <;> assumption)
end

