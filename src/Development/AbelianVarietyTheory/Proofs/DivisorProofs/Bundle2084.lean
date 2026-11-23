module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheafA
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationTower
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem GlobalTheory.FormalAlg.alg_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), Alg f I → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ j : ∀ e, (Y e).left ⟶ W, (∀ e, IsClosedImmersion (j e)) → (∀ e, j e ≫ f = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ j (e + 1) = j e) → ∃ (T : Scheme.{0}) (i : T ⟶ W) (c : ∀ e, (Y e).left ⟶ T), IsClosedImmersion i ∧ IsProper (i ≫ f) ∧ (∀ e, c e ≫ i = j e) ∧ ∀ e, IsPullback (c e) (Y e).hom (i ≫ f) (thick R I e) := by
  intro R _ I W f hA Y β hβ hY j hj hjf hβj
  have hP := (_root_.GlobalTheory.FormalAlg.towerSquares R I Y β hβ).1
  have key : ∀ e (T : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i →
      ((∃ b : (Y e).left ⟶ T, b ≫ i = j e ∧ IsPullback b (Y e).hom (i ≫ f) (thick R I e)) ↔
        i.ker ⊔ baseIdeal f (I ^ (e + 1)) = (j e).ker) :=
    fun e T i hi => _root_.GlobalTheory.FormalAlg.reduces_iff_ker_eq R (I ^ (e + 1)) W T (Y e).left f i (j e) (Y e).hom hi (hj e) (hjf e)
  have hsys : IsSystem f I (fun e => (j e).ker) := by
    intro e
    exact ((key e _ (j (e + 1)) (hj (e + 1))).1 ⟨β e, hβj e, by rw [hjf (e + 1)]; exact hP e⟩).symm
  have hprop : ∀ e, IsProper ((j e).ker.subschemeι ≫ f) := by
    intro e
    have h0 : (j e).toImage ≫ ((j e).ker.subschemeι ≫ f) = (Y e).hom ≫ thick R I e := by
      rw [← hjf e, ← Category.assoc]
      exact congrArg (· ≫ f) (Scheme.Hom.toImage_imageι (j e))
    have h1 : (j e).ker.subschemeι ≫ f = inv (j e).toImage ≫ (Y e).hom ≫ thick R I e := by
      rw [← h0, IsIso.inv_hom_id_assoc]
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [h1]
    infer_instance
  obtain ⟨T, hTp, hTr⟩ := hA _ hsys hprop
  have hc : ∀ e, ∃ b : (Y e).left ⟶ T.subscheme, b ≫ T.subschemeι = j e ∧
      IsPullback b (Y e).hom (T.subschemeι ≫ f) (thick R I e) := fun e =>
    (key e _ T.subschemeι inferInstance).2 (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hTr e)
  choose c hc1 hc2 using hc
  exact ⟨T.subscheme, T.subschemeι, c, inferInstance, hTp, hc1, hc2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffBoundedByDeterminantsStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePolynomial_coeff_bounded_by_determinants : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr), T.FinRes →
      (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ (M : GlobalTheory.LamT.LocMod z T iK),
      letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
      ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
        (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
        φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → a ≠ 0 → (∀ b, IsUnit (g b).det) →
        GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → GlobalTheory.LamT.SecInt T M.m1 M.m2 y'.s →
        ∀ cl : ∀ b : E →+* ℂ, Fin (Dw.mult b) → T.Fr,
          (∀ b j i, cl b j * (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr)) →
        ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
        ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, ∃ w : T.V, iK (AddMonoidAlgebra.coeff G μ) * ∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v =
          (∏ b, (g b).det ^ k b) * algebraMap T.V T.Fr w := by
  first | exact @GlobalTheory.FrameCoeffLoc.coeff_mul_prod_mem_det | exact GlobalTheory.FrameCoeffLoc.coeff_mul_prod_mem_det | (intros; apply GlobalTheory.FrameCoeffLoc.coeff_mul_prod_mem_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratesOfCloseLocalEquationClassicalPoint
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.Poinc

theorem nnnorm_le_of_mem_span {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] (v : R →+* K)
    (hv : ∀ r, ‖v r‖₊ ≤ 1) {s : Set R} {ρ : NNReal} (hs : ∀ c ∈ s, ‖v c‖₊ ≤ ρ) :
    ∀ c ∈ Ideal.span s, ‖v c‖₊ ≤ ρ := by
  intro c hc
  induction hc using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    rw [smul_eq_mul, map_mul, nnnorm_mul]
    exact (mul_le_mul' (hv a) hx).trans (by rw [one_mul])

theorem nnnorm_le_pow_of_mem_pow {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] (v : R →+* K)
    (hv : ∀ r, ‖v r‖₊ ≤ 1) {I : Ideal R} {ρ : NNReal} (hI : ∀ c ∈ I, ‖v c‖₊ ≤ ρ) :
    ∀ k : ℕ, ∀ b ∈ I ^ k, ‖v b‖₊ ≤ ρ ^ k := by
  intro k
  induction k with
  | zero => intro b _; simpa using hv b
  | succ k ih =>
    intro b hb
    rw [pow_succ] at hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro a ha c hc
      rw [map_mul, nnnorm_mul, pow_succ]
      exact mul_le_mul' (ih a ha) (hI c hc)
    · intro a c ha hc
      rw [map_add (f := _)]
      exact (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le ha hc)

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem generates_of_close : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (∀ x ∈ D.idealSheaf.support, x ∉ U) → ∀ (x : M.Z) (p : ℕ) [Fact p.Prime] (y₀ : Sp (OO p) ⟶ M.Z), M.Cen U x y₀ → ∀ f, EqAt M D x f → ∃ k : ℕ, ∀ (G b : M₁.O (π x)), ‖M.val (gPt p ≫ y₀) ((G : Ω) + b)‖ = ‖M.val (gPt p ≫ y₀) f‖ → b ∈ Ideal.span {c : M₁.O (π x) | ¬ IsUnit c} ^ k → (G : Ω) / f ∈ M.O x → (G : Ω) ≠ 0 ∧ f / G ∈ M.O x := by
  intro o Ω _ _ _ _ M₁ M π hπ U D hD x p _ y₀ hy f hf
  obtain ⟨i, hxi, rfl⟩ := hf
  set F : Ω := valF M.pt (D.U i) (D.f i) with hFdef
  set y : Sp (PadicAlgCl p) ⟶ M.Z := gPt p ≫ y₀ with hydef

  have hFO : F ∈ M.O x := RatModel.valF_mem_O hxi _
  have hwx : y (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ x := RatModel.gPt_specializes hy.1 _
  have hwU : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ U := hy.2 ⟨_, rfl⟩
  have hwi : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ D.U i := hwx.mem_open (D.U i).isOpen hxi
  have hwb : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ M.Z.basicOpen (D.f i) := by
    by_contra h
    exact hD _ ((D.mem_support_iff i hwi).2 h) hwU
  have hF0 : M.val y F ≠ 0 :=
    (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton y (IsLocalRing.closedPoint (PadicAlgCl p)))
      ⟨_, RatModel.valF_mem_O hwi _⟩).2 ((RatModel.isUnit_valF_iff hwi (D.f i)).2 hwb)
  have hFpos : 0 < ‖M.val y F‖₊ := nnnorm_pos.2 hF0

  have hle : M₁.O (π x) ≤ M.O x := fun c hc => hπ.map_mem_O hc
  let v : M₁.O (π x) →+* PadicAlgCl p :=
    (RatModel.valHomOf y x (RatModel.gPt_specializes hy.1)).comp (Subalgebra.inclusion hle).toRingHom
  have hv_apply : ∀ c : M₁.O (π x), v c = M.val y c := fun c => rfl
  have hv1 : ∀ c, ‖v c‖₊ ≤ 1 := fun c => by
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, hv_apply]
    exact RatModel.norm_val_le_one hy.1 (hle c.2)
  have hvlt : ∀ c : M₁.O (π x), ¬ IsUnit c → ‖v c‖₊ < 1 := by
    intro c hc
    have hc' : (c : Ω) ∈ M₁.O (π (y (IsLocalRing.closedPoint (PadicAlgCl p)))) :=
      RatModel.O_le_of_specializes (hwx.map π.continuous) c.2
    have e := hπ.val_comp y (IsLocalRing.closedPoint (PadicAlgCl p)) hc'
    have hc0 : (y₀ ≫ π) (cPt p) = π x := by rw [Scheme.Hom.comp_apply, hy.1]
    have h1 := (RatModel.norm_val_lt_one_iff hc0 c.2).2 hc
    rw [← Category.assoc, ← hydef, e] at h1
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one, hv_apply]
    exact h1

  haveI : IsDedekindDomain o := ArithBase.ded (Ω := Ω)
  haveI := M₁.lft
  haveI : IsLocallyNoetherian M₁.Z := LocallyOfFiniteType.isLocallyNoetherian M₁.s
  haveI : IsNoetherianRing (M₁.O (π x)) := isNoetherianRing_of_ringEquiv _ (M₁.stalkEquiv (π x))
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (maximalIdeal (M₁.O (π x)))
  set ρ : NNReal := s.sup fun c => ‖v c‖₊
  have hρ : ρ < 1 := by
    refine (Finset.sup_lt_iff (by simp)).2 fun c hc => hvlt c ?_
    have : c ∈ maximalIdeal (M₁.O (π x)) := hs ▸ Submodule.subset_span hc
    exact (mem_maximalIdeal c).1 this
  have hm : ∀ c ∈ maximalIdeal (M₁.O (π x)), ‖v c‖₊ ≤ ρ := by
    rw [← hs]
    exact nnnorm_le_of_mem_span v hv1 fun c hc => Finset.le_sup (f := fun c => ‖v c‖₊) hc
  have hspan : Ideal.span {c : M₁.O (π x) | ¬ IsUnit c} = maximalIdeal (M₁.O (π x)) := by
    have : {c : M₁.O (π x) | ¬ IsUnit c} = (maximalIdeal (M₁.O (π x)) : Set (M₁.O (π x))) :=
      Set.ext fun c => (mem_maximalIdeal c).symm
    rw [this, Ideal.span_eq]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hFpos hρ
  refine ⟨k, fun G b hGb hb hGf => ?_⟩

  rw [hspan] at hb
  have hbk : ‖M.val y b‖₊ < ‖M.val y F‖₊ :=
    lt_of_le_of_lt (nnnorm_le_pow_of_mem_pow v hv1 hm k b hb) hk
  have hadd : M.val y ((G : Ω) + b) = M.val y G + M.val y b :=
    RatModel.val_add (RatModel.gPt_specializes hy.1) (hle G.2) (hle b.2)
  have hGb' : ‖M.val y G + M.val y b‖₊ = ‖M.val y F‖₊ := by
    rw [← hadd]
    exact NNReal.eq hGb
  have hG : ‖M.val y G‖₊ = ‖M.val y F‖₊ := by
    refine le_antisymm ?_ ?_
    · have e : M.val y G = (M.val y G + M.val y b) + -M.val y b := by ring
      rw [e]
      refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le hGb'.le ?_)
      rw [nnnorm_neg]
      exact hbk.le
    · rw [← hGb']
      refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le le_rfl ?_)
      by_contra h
      push_neg at h
      have := (IsUltrametricDist.nnnorm_add_le_max (M.val y G) (M.val y b)).trans
        (max_le h.le le_rfl)
      rw [hGb'] at this
      exact absurd hbk (not_lt.2 this)
  have hG0 : (G : Ω) ≠ 0 := by
    intro h
    rw [h, RatModel.val_zero, nnnorm_zero] at hG
    exact hFpos.ne hG
  have hFne : F ≠ 0 := by
    intro h
    rw [h, RatModel.val_zero] at hF0
    exact hF0 rfl
  refine ⟨hG0, ?_⟩
  have hmul : M.val y ((G : Ω) / F * F) = M.val y ((G : Ω) / F) * M.val y F :=
    RatModel.val_mul (RatModel.gPt_specializes hy.1) hGf hFO
  rw [div_mul_cancel₀ _ hFne] at hmul
  have hq : ‖M.val y ((G : Ω) / F)‖₊ = 1 := by
    have h2 : ‖M.val y ((G : Ω) / F)‖₊ * ‖M.val y F‖₊ = 1 * ‖M.val y F‖₊ := by
      rw [one_mul, ← nnnorm_mul, ← hmul, hG]
    exact mul_right_cancel₀ hFpos.ne' h2
  have hq' : ‖M.val (gPt p ≫ y₀) ((G : Ω) / F)‖ = 1 := by
    rw [← coe_nnnorm]
    exact congrArg NNReal.toReal hq
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.norm_val_eq_one_iff hy.1 hGf).1 hq')
  simpa [inv_div] using hu.2

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreBaseChangeGrpPullbackDomains
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
namespace GlobalTheory.GenFibreBaseChange

theorem genFibre_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ → ∀ (G : Over (Sp R)) [GrpObj G], ∃ π₀ : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶ ((Over.pullback (jK R)).obj G).left, IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) ((Over.pullback (jK R)).obj G) (spMap a) π₀ ∧ ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (spMap ρ))).pull (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R'))) ((L.pull (pullback.fst G.hom (jK R))).pull π₀) := by
  intro R R' _ _ _ _ ρ a ha G _
  have hsq : jK R' ≫ spMap ρ = spMap a ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ha]
  have hw : (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R') ≫ pullback.fst G.hom (spMap ρ)) ≫ G.hom =
      (pullback.snd (pullback.snd G.hom (spMap ρ)) (jK R') ≫ spMap a) ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hsq,
      Category.assoc]
  let π₀ : pullback (pullback.snd G.hom (spMap ρ)) (jK R') ⟶ pullback G.hom (jK R) := pullback.lift _ _ hw
  have e₁ : π₀ ≫ pullback.fst G.hom (jK R) =
      pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R') ≫ pullback.fst G.hom (spMap ρ) := pullback.lift_fst _ _ _
  have e₂ : π₀ ≫ pullback.snd G.hom (jK R) = pullback.snd (pullback.snd G.hom (spMap ρ)) (jK R') ≫ spMap a :=
    pullback.lift_snd _ _ _
  refine ⟨π₀, ?_, fun L hL => ?_⟩
  · have n := (isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap ρ))
    rw [hsq] at n
    have n' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) G (spMap a ≫ jK R)
        (π₀ ≫ pullback.fst G.hom (jK R)) := by
      rw [e₁]; exact n
    exact IsGrpPullback.cancel (isGrpPullback_pullback G (jK R)) n' e₂
  · have h₁ := GlobalTheory.Spread.lbIso_pull_pull hL (a := pullback.fst G.hom (spMap ρ))
      (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R')) rfl
    have h₂ := GlobalTheory.Spread.lbIso_pull_pull hL (a := pullback.fst G.hom (jK R)) π₀ e₁.symm
    exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)
      (LBIso.symm h₁) h₂

end GlobalTheory.GenFibreBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemIdealSheafStalkOfClosedFibreUnivClosed
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.SpreadIdeal

theorem exists_open_nhds_mem_stalkId (P : Scheme.{0}) (I : P.IdealSheafData) (s : Γ(P, ⊤)) (v : P)
    (hv : (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) :
    ∃ O : P.Opens, v ∈ O ∧ ∀ y ∈ O, (P.presheaf.germ ⊤ y trivial).hom s ∈ FinalTheorems.stalkId I y := by
  obtain ⟨U, hU, hvU, -⟩ := exists_isAffineOpen_mem_and_subset (x := v) (U := ⊤) trivial
  letI : Algebra Γ(P, U) (P.presheaf.stalk v) := P.presheaf.algebra_section_stalk ⟨v, hvU⟩
  haveI hlocv := hU.isLocalization_stalk ⟨v, hvU⟩
  set t : Γ(P, U) := P.presheaf.map (homOfLE le_top).op s with ht
  have hgerm : ∀ (y : P) (hy : y ∈ U), (P.presheaf.germ ⊤ y trivial).hom s =
      (P.presheaf.germ U y hy).hom t := fun y hy => by
    rw [ht, ← CommRingCat.comp_apply, P.presheaf.germ_res]
  rw [hgerm v hvU, ds_stalkId_eq_map I ⟨U, hU⟩ v hvU] at hv
  change algebraMap Γ(P, U) (P.presheaf.stalk v) t ∈
    Ideal.map (algebraMap Γ(P, U) (P.presheaf.stalk v)) (I.ideal ⟨U, hU⟩) at hv
  obtain ⟨⟨a, w⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff
    (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl _).mp hv
  rw [← map_mul] at e
  obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl) e
  set σ : Γ(P, U) := (c : Γ(P, U)) * w with hσ
  have hσt : σ * t ∈ I.ideal ⟨U, hU⟩ := by
    rw [hσ, show (c : Γ(P, U)) * w * t = c * (t * w) by ring, hc]
    exact Ideal.mul_mem_left _ _ a.2
  have hσunit : IsUnit (algebraMap Γ(P, U) (P.presheaf.stalk v) σ) :=
    IsLocalization.map_units (M := (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl) _
      (c * w : (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl)
  refine ⟨P.basicOpen σ, ?_, fun y hy => ?_⟩
  · exact (P.mem_basicOpen σ v hvU).mpr hσunit
  · have hyU : y ∈ U := P.basicOpen_le σ hy
    have hyu : IsUnit ((P.presheaf.germ U y hyU).hom σ) := (P.mem_basicOpen σ y hyU).mp hy
    rw [hgerm y hyU, ← Ideal.unit_mul_mem_iff_mem _ hyu, ← map_mul,
      ds_stalkId_eq_map I ⟨U, hU⟩ y hyU]
    exact Ideal.mem_map_of_mem _ hσt

end GlobalTheory.SpreadIdeal

namespace GlobalTheory.SpreadIdeal

theorem mem_stalkId_of_closedFibre : ∀ (P : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (p : P ⟶ Sp R) [UniversallyClosed p] (I : P.IdealSheafData) (s : Γ(P, ⊤)), (∀ v : P, p v = closedPoint R → (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) → ∀ v : P, (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v := by
  intro P R _ _ p _ I s hs v
  by_contra hv
  set Z : Set P := {y | (P.presheaf.germ ⊤ y trivial).hom s ∉ FinalTheorems.stalkId I y} with hZ
  have hZc : IsClosed Z := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    have hy' : (P.presheaf.germ ⊤ y trivial).hom s ∈ FinalTheorems.stalkId I y := by
      simpa [hZ] using hy
    obtain ⟨O, hyO, hO⟩ := exists_open_nhds_mem_stalkId P I s y hy'
    exact ⟨O, fun z hz => by simpa [hZ] using hO z hz, O.2, hyO⟩
  have himg : IsClosed (p.base '' Z) := p.isClosedMap _ hZc
  have hmem : closedPoint R ∈ p.base '' Z :=
    (IsLocalRing.specializes_closedPoint (p.base v)).mem_closed himg ⟨v, hv, rfl⟩
  obtain ⟨w, hwZ, hw⟩ := hmem
  exact hwZ (hs w hw)

end GlobalTheory.SpreadIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermSystemHeightFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}} {N : ℕ}
  {s : S ⟶ Sp R}

theorem act_zero_eq_one_wvs (o : Obj b N s) : o.act.act 0 = 1 := by
  have h := o.act.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

def ptModuleWvs (o : Obj b N s) (T : Over S) : Module (𝓞 D.F) (Additive (T ⟶ o.A)) where
  smul a g := Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
  one_smul g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 1)) = g
    rw [map_one, o.act.one, Category.comp_id]; rfl
  mul_smul a c g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a * c))) =
      Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
    rw [map_mul, o.act.mul, Category.assoc]
  smul_zero a := by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    show Additive.ofMul ((1 : T ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) = Additive.ofMul 1
    rw [one_comp]
  smul_add a g h := by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    show Additive.ofMul ((g.toMul * h.toMul) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) =
      Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) * (h.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)))
    rw [mul_comp]
  add_smul a c g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a + c))) =
      Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) * (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)))
    rw [map_add (f := _), o.act.add, comp_mul]
  zero_smul g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 0)) = Additive.ofMul 1
    rw [map_zero, act_zero_eq_one_wvs, comp_one]

attribute [local instance] ptModuleWvs

def kerWSubWvs (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) [IsMonHom ψ]
    (hl : ∀ a : 𝓞 D.F, o.act.act (algebraMap (𝓞 D.F) D.O a) ≫ ψ = ψ ≫ o'.act.act (algebraMap (𝓞 D.F) D.O a))
    (w : Ideal (𝓞 D.F)) (T : Over S) : Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) where
  carrier := {g | g.toMul ≫ ψ = 1 ∧ KilledBy o w g.toMul}
  zero_mem' := by
    refine ⟨one_comp ψ, fun a _ => ?_⟩
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    exact one_comp _
  add_mem' {g h} hg hh := by
    refine ⟨?_, fun a ha => ?_⟩
    · show (g.toMul * h.toMul) ≫ ψ = 1
      rw [mul_comp, hg.1, hh.1, _root_.mul_one]
    · haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
      show (g.toMul * h.toMul) ≫ _ = 1
      rw [mul_comp, hg.2 a ha, hh.2 a ha, _root_.mul_one]
  smul_mem' c g hg := by
    refine ⟨?_, fun a ha => ?_⟩
    · show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ ψ = 1
      haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, hl, ← Category.assoc, hg.1, one_comp]
    · show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm, map_mul, o.act.mul, ← Category.assoc, hg.2 a ha,
        one_comp]

theorem card_kerW_eq_pow : ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {S : Scheme.{0}} {N : ℕ} {s : S ⟶ Sp R} (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsMonHom ψ →
    (∀ a : 𝓞 D.F, o.act.act (algebraMap (𝓞 D.F) D.O a) ≫ ψ = ψ ≫ o'.act.act (algebraMap (𝓞 D.F) D.O a)) →
    ∀ (w : Ideal (𝓞 D.F)), w.IsMaximal → ∀ {k : Type} [Field k] (y : Sp k ⟶ S),
    Finite {g : Over.mk y ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} →
    ∃ j' : ℕ, Nat.card {g : Over.mk y ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ j' := by
  intro p _ D R _ b S N s o o' ψ hψ hl w hw k _ y hfin
  haveI := hψ
  let K := kerWSubWvs o o' ψ hl w (Over.mk y)
  let e : K ≃ {g : Over.mk y ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} :=
    { toFun := fun x => ⟨x.1.toMul, x.2⟩
      invFun := fun g => ⟨Additive.ofMul g.1, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Finite K := Finite.of_equiv _ e.symm
  have htor : Module.IsTorsionBySet (𝓞 D.F) K (w : Set (𝓞 D.F)) := by
    intro x a
    apply Subtype.ext
    show Additive.ofMul (x.1.toMul ≫ o.act.act (algebraMap _ _ a.1)) = Additive.ofMul 1
    rw [x.2.2 a.1 a.2]
  letI := Ideal.Quotient.field w
  letI : Module (𝓞 D.F ⧸ w) K := htor.module
  have hne : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw (NumberField.RingOfIntegers.not_isField D.F)
  haveI : Finite (𝓞 D.F ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hne
  letI := Fintype.ofFinite (𝓞 D.F ⧸ w)
  letI := Fintype.ofFinite K
  refine ⟨Module.finrank (𝓞 D.F ⧸ w) K, ?_⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓞 D.F ⧸ w),
    Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongLocalSpecVanishingIdealComplEqSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PolDeg

theorem idlAlong_vanishingIdeal_compl (S : Scheme.{0}) (U : S.Opens) (R : Type) [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S) (f : R) (hf : (Ideal.span {f}).IsRadical) (hU : ∀ p : Sp R, ξ p ∈ (U : Set S) ↔ f ∉ p.asIdeal)
    (hrad : ∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical →
      (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) :
    idlAlong (Scheme.IdealSheafData.vanishingIdeal U.compl) ξ = Ideal.span {f} := by
  have hs := GlobalTheory.VanStalk.van_spec U.compl (ξ (closedPoint R))
  refine GlobalTheory.VanStalk.eq_of_forall_prime (hrad _ hs.1) hf fun q => ?_
  rw [idlAlong, Ideal.map_le_iff_le_comap, Ideal.span_singleton_le_iff_mem]
  refine (hs.2 (PrimeSpectrum.comap (Scheme.stalkClosedPointTo ξ).hom q)).symm.trans ?_
  have e := congrArg (fun g => g q) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)
  change (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk (ξ (closedPoint R))) q ∈ (U.compl : Set S) ↔ _
  rw [e]
  change ξ q ∉ (U : Set S) ↔ _
  rw [hU q, not_not]

end GlobalTheory.PolDeg
end
end

