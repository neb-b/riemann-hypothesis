module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralElemOfIsAlgebraicInt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecThroughUp
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumSectionValueArcFramedPointStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_sectionValue_arc_framedPoint : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)), GlobalTheory.Reg.EvLaws Xo c → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ k, AnVec Ha (e τ k) (z τ k)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ a' n (F : Rul Xo c), F ∈ sec Xo c a' n → HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (Formalism.L2.PjFree.toC (evR Xo c F yw)) := by
  first | exact @GlobalTheory.ArcQ.hasSum_evR_arc | exact GlobalTheory.ArcQ.hasSum_evR_arc | (intros; apply GlobalTheory.ArcQ.hasSum_evR_arc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IntegralOfFrChg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ.IntChg

section Sec

variable {X Y : Scheme.{0}}

def mulSec {L : LB X} (r : Γ(X, ⊤)) (s : LB.Sec L) : LB.Sec L where
  f i := resG X le_top r * s.f i
  compat i j := by
    have e : ∀ (U : X.Opens) (h : L.U i ⊓ L.U j ≤ U),
        (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) r) = resG X le_top r := fun U h => by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [map_mul, map_mul, s.compat i j, e, e, mul_left_comm]

theorem res_res {U V : X.Opens} (h : V ≤ U) (r : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) r) = resG X le_top r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem appLE_res (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (r : Γ(X, ⊤)) :
    (f.appLE U V h).hom (resG X le_top r) = resG Y le_top (f.appTop.hom r) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

theorem isoMaps_mul {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoMaps w s s')
    (r : Γ(X, ⊤)) : IsoMaps w (mulSec r s) (mulSec r s') := by
  intro i k
  have := h i k
  simp only [mulSec, map_mul, res_res]
  rw [this, mul_left_comm]

theorem pullSec_mul {L : LB X} {f : Y ⟶ X} {s : LB.Sec L} {s' : LB.Sec (L.pull f)} (h : PullSec f s s')
    (r : Γ(X, ⊤)) : PullSec f (mulSec r s) (mulSec (f.appTop.hom r) s') := by
  intro j hj
  simp only [mulSec, map_mul, appLE_res]
  rw [h j hj]

theorem appTop_toΓ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (a : A) :
    (spMap φ).appTop.hom (toΓ A a) = toΓ B (φ a) := by
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact this.symm

end Sec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem integral_scal (T : CDVR) (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ (y : FrPt Xo c T.Fr) (a : T.Vˣ) (s' : LB.Sec (PPx y.x))
      (hg : ∀ s'' : LB.Sec (PPx y.x), ∃! b : T.Fr, ∀ i, s''.f i = scal y.x b i * s'.f i),
      (∀ i, s'.f i = scal y.x (algebraMap T.V T.Fr a) i * y.s.f i) → Integral T io y →
      Integral T io { y with s := s', gen := hg } := by
  let _ := io.toAlgebra
  intro y a s' hg hs h
  obtain ⟨G, t', m1, m2, hu, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, hp, hl⟩ := h
  have hc : m2.φ.appTop.hom (G.G.hom.appTop.hom (toΓ T.V a)) =
      t'.G.hom.appTop.hom (toΓ T.Fr (algebraMap T.V T.Fr a)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, m2.cart.1.w, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
    exact congrArg _ (appTop_toΓ _ _)
  refine ⟨G, t', m1, m2, hu, mulSec (G.G.hom.appTop.hom (toΓ T.V a)) θ, fun τ => ?_, w1, w2, _, _, _, r1, r2,
    isoMaps_mul i1 _, isoMaps_mul i2 _, pullSec_mul hp _, ?_⟩
  · obtain ⟨b, hb, hbu⟩ := hθ τ
    have key : ∀ (d : T.V) i, resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V d)) *
        (mulSec (G.G.hom.appTop.hom (toΓ T.V a)) θ).f i =
        resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V (d * a))) * θ.f i := fun d i => by
      simp only [mulSec, map_mul, _root_.mul_assoc]
    refine ⟨b * ↑a⁻¹, fun i => ?_, fun d hd => ?_⟩
    · rw [key, Units.inv_mul_cancel_right]; exact hb i
    · rw [← hbu (d * a) fun i => by rw [← key]; exact hd i, Units.mul_inv_cancel_right]
  · intro g e1 e2 j hj
    have e3 := hl g e1 e2 j hj
    show resG _ le_top _ * s1.f j = (g.appLE _ _ hj).hom (s'.f _)
    refine Eq.symm ((congrArg _ (hs _)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ e3.symm)))
    refine (appLE_res g _ _ hj _).trans (congrArg _ ?_)
    rw [hc, ← e2, Scheme.Hom.comp_appTop]
    rfl

theorem integral_chg (T : CDVR) (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ (y y' : FrPt Xo c T.Fr) (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (a : T.Vˣ),
      (∀ τ, IsUnit (k τ).det) → FrChg (fun τ => (k τ).map (algebraMap T.V T.Fr)) (algebraMap T.V T.Fr a) y y' →
      Integral T io y → Integral T io y' := by
  let _ := io.toAlgebra
  intro y y' k a hk ⟨hx, hu, pm, h1, h2, h3⟩ hy
  have hk' : ∀ τ, IsUnit (k τ).transpose.det := fun τ => by rw [Matrix.det_transpose]; exact hk τ
  have hK : ∀ τ, IsUnit ((k τ).transpose.map (algebraMap T.V T.Fr)).det := fun τ => by
    have e : ((k τ).transpose.map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr (k τ).transpose.det :=
      (RingHom.map_det _ _).symm
    rw [e]
    exact (hk' τ).map _
  have hr := GlobalTheory.IntRebase.integral_reb T io y hy (fun τ => (k τ).transpose) hk' hK
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := y'
  simp only at hx
  subst hx
  have eu : zu = (GlobalTheory.IntRebase.rebase₂ y _ hK).u := by
    funext τ i
    exact Formalism.L2.PjFree.isCombAt_unique (hu τ i)
      ((GlobalTheory.IntRebase.isCombAtG_iff Xo.univ.t y.x (fun j => GlobalTheory.IntRebase.ovT (t := Xo.univ.t) (y.tan τ j)) _ _).2 rfl)
  subst eu
  have ep : pm = 𝟙 _ := by
    apply pullback.hom_ext
    · refine h2.trans ?_
      simp only [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, Category.id_comp]
      rfl
    · exact h1.trans (Category.id_comp _).symm
  subst ep
  refine integral_scal T io (GlobalTheory.IntRebase.rebase₂ y _ hK) a zs zg (fun i => ?_) hr
  exact (h3 i le_rfl).symm.trans (GlobalTheory.IntRebase.id_appLE_apply _ _ _ _)

theorem integral_of_frChg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (s : T.V), (∀ τ, IsUnit (g τ).det) → IsUnit s → letI := io.toAlgebra; ∀ y y' : FrPt Xo c T.Fr, FrChg (fun τ => (g τ).map (algebraMap T.V T.Fr)) (algebraMap T.V T.Fr s) y y' → Integral T io y → Integral T io y' := by
  intro E _ _ _ H Dw l Xo c T io g s hg hs y y' h hy
  obtain ⟨a, rfl⟩ := hs
  exact integral_chg T io y y' g a hg h hy

end GlobalTheory.ArcQ.IntChg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LcoeffPolyConstMul
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ.FrameCut

theorem lcoeffPoly_coeff {ι K₁ : Type} [Field K₁] (P : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ)
    (μ : ι →₀ ℕ) : (GlobalTheory.ArcQ.lcoeffPoly P m).coeff μ = (P.coeff μ).coeff m := by
  classical
  simp only [GlobalTheory.ArcQ.lcoeffPoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h]; rfl

theorem lcoeffPoly_add {ι K₁ : Type} [Field K₁] (P Q : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (P + Q) m = GlobalTheory.ArcQ.lcoeffPoly P m + GlobalTheory.ArcQ.lcoeffPoly Q m := by
  ext μ
  simp only [lcoeffPoly_coeff, MvPolynomial.coeff_add, HahnSeries.coeff_add]

theorem lcoeffPoly_monomial {ι K₁ : Type} [Field K₁] (μ : ι →₀ ℕ) (f : LaurentSeries K₁) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.monomial μ f) m = MvPolynomial.monomial μ (f.coeff m) := by
  classical
  ext ν
  simp only [lcoeffPoly_coeff, MvPolynomial.coeff_monomial]
  split_ifs
  · rfl
  · rfl

theorem lcoeffPoly_C_mul_map {ι L : Type} [Field L] (g : LaurentSeries L) (Q : MvPolynomial ι L) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.C g * MvPolynomial.map (HahnSeries.C (Γ := ℤ)) Q) m =
      MvPolynomial.C (g.coeff m) * Q := by
  ext ν
  rw [lcoeffPoly_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm g,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, mul_comm]

theorem lcoeffPoly_const_mul {ι L : Type} [Field L] (x : L) (P : MvPolynomial ι (LaurentSeries L)) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.C (HahnSeries.C (Γ := ℤ) x) * P) m =
      MvPolynomial.C x * GlobalTheory.ArcQ.lcoeffPoly P m := by
  ext ν
  rw [lcoeffPoly_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, lcoeffPoly_coeff,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem exists_subst {ι K₁ L S : Type} [Field K₁] [Field L] [CommRing S] (io : K₁ →+* L)
    (Φ : MvPolynomial ι (LaurentSeries K₁) →+* S) (j : MvPolynomial ι (LaurentSeries L) →+* S)
    (q : ι → MvPolynomial ι L)
    (hC : ∀ f : LaurentSeries K₁, ∃ g : LaurentSeries L, (∀ m, g.coeff m = io (f.coeff m)) ∧
      Φ (MvPolynomial.C f) = j (MvPolynomial.C g))
    (hX : ∀ x, Φ (MvPolynomial.X x) = j (MvPolynomial.map (HahnSeries.C (Γ := ℤ)) (q x)))
    (P : MvPolynomial ι (LaurentSeries K₁)) :
    ∃ P₁ : MvPolynomial ι (LaurentSeries L), j P₁ = Φ P ∧ ∀ m, GlobalTheory.ArcQ.lcoeffPoly P₁ m =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp io) q (GlobalTheory.ArcQ.lcoeffPoly P m) := by
  induction P using MvPolynomial.induction_on' with
  | monomial μ f =>
    obtain ⟨g, hg, hΦ⟩ := hC f
    refine ⟨MvPolynomial.C g * MvPolynomial.map (HahnSeries.C (Γ := ℤ)) (μ.prod fun x e => q x ^ e), ?_, fun m => ?_⟩
    · rw [MvPolynomial.monomial_eq, map_mul, map_mul, hΦ]
      simp only [Finsupp.prod, map_prod, map_pow, hX]
    · rw [lcoeffPoly_C_mul_map, lcoeffPoly_monomial, MvPolynomial.eval₂Hom_monomial, hg]
      rfl
  | add P Q hP hQ =>
    obtain ⟨P₁, h1, h2⟩ := hP
    obtain ⟨Q₁, h3, h4⟩ := hQ
    exact ⟨P₁ + Q₁, by rw [map_add (f := _), map_add (f := _), h1, h3], fun m => by
      rw [lcoeffPoly_add, lcoeffPoly_add, map_add (f := _), h2, h4]⟩

theorem eval_subst {ι K₁ L K : Type} [Field K₁] [Field L] [Field K] (io : K₁ →+* L) (ιT : L →+* K)
    (q : ι → MvPolynomial ι L) (Y : ι → K) (R : MvPolynomial ι K₁) :
    MvPolynomial.eval Y (MvPolynomial.map ιT (MvPolynomial.eval₂Hom (MvPolynomial.C.comp io) q R)) =
      MvPolynomial.eval (fun x => MvPolynomial.eval Y (MvPolynomial.map ιT (q x)))
        (MvPolynomial.map (ιT.comp io) R) := by
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p x hp => simp only [map_mul, hp, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, MvPolynomial.eval_X]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem arcNum_of_poly {K₁ : Type} [Field K₁] (P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) :
    arcNum (algebraMap _ (ArcS Dw K₁) P) = P := by
  have hs : ∃ Q, algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) Q =
      algebraMap _ (ArcS Dw K₁) P := ⟨P, rfl⟩
  rw [arcNum, dite_eq_left hs]
  exact GlobalTheory.ArcConst.algebraMap_injective Dw K₁ hs.choose_spec

theorem wchar_gen {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t : Ix Dw → Sˣ)
    (h : ∀ x, t (some x) = 1) : wchar (ex Dw a n) t = (t none : S) ^ n := by
  rw [wchar, Fintype.prod_option]
  simp [h, ex]


set_option maxHeartbeats 1600000 in
theorem frameBound_of_cut (hL : Out.Laws) (hL2 : Out.Laws2) {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hev : GlobalTheory.Reg.EvLaws Xo c) {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] {d : ArcDatum Xo c K₁}
    {w : HeightOneSpectrum (𝓞 K₁)} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {Fs : Set (Rul Xo c)}
    (hFs : ∀ F ∈ Fs, F ∈ sec Xo c a n) (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr)
    (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr) (hγ : γ ≠ 0)
    (hBc : BcRigidAt Dv γ lam Bm) (hRec : RecordAt Dv Fs) :
    FrameBound Z (Dv.ιT γ) (fun τ k => Dv.ιT (lam τ k)) (fun τ => (Bm τ).map Dv.ιT) n d Fs := by
  intro F hF t ht Y hY hdet
  obtain ⟨φ, ψ, z₁, z₂, tγ, hφC, hφX, hψC, hψX, htγ, htγ', hm1, hm2, hb⟩ := hBc
  have hϖ : Dv.ϖ ≠ 0 := Dv.ϖ_irr.ne_zero
  obtain ⟨hdomR, -, -, -, hdiv⟩ := GlobalTheory.T.arcLetterRingOverDVR_polynomial_denominators E H Dw Dv.Tv Dv.ϖ hϖ
  have hdom1 := GlobalTheory.ArcConst.isDomain Dw K₁
  have hdom2 := GlobalTheory.ArcConst.isDomain Dw Dv.Tv.Fr
  have hinj := GlobalTheory.ArcConst.algebraMap_injective Dw Dv.Tv.Fr
  have hsec := hFs F hF
  obtain ⟨P, hP, -⟩ := _root_.GlobalTheory.ArcQ.evR_arc_isHomogeneous hL hL2 E H Dw l Xo c hev K₁ d a n F hsec
  have e1 := (_root_.GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcS Dw K₁)).1 _ φ _ _ hm1
  have e2 := (_root_.GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcSR Dw Dv.Tv.V Dv.ϖ)).1 _ ψ _ _ hm2
  have e3 := ((_root_.GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcS Dw Dv.Tv.Fr)).2 hdom2).1 tγ _ _ hb
  rw [wchar_gen a n tγ htγ', e1, e2, htγ, ← hP] at e3
  set f := evR Xo c F Dv.yR with hf
  let q : ArcLt Dw → MvPolynomial (ArcLt Dw) Dv.Tv.Fr := fun x =>
    ∑ l : Fin (Dw.mult x.1), MvPolynomial.X ⟨x.1, x.2.1, l⟩ * MvPolynomial.C (Bm x.1 l x.2.2 * (lam x.1 x.2.2)⁻¹)
  obtain ⟨P₁, hP₁, hco⟩ := exists_subst Dv.io (φ.toRingHom.comp (algebraMap _ (ArcS Dw K₁)))
    (algebraMap _ (ArcS Dw Dv.Tv.Fr)) q hφC (fun x => by
      refine (hφX x).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [q, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, arcX]) P
  have hγn : γ ^ n ≠ 0 := pow_ne_zero _ hγ
  let P₂ : MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr) :=
    MvPolynomial.C (HahnSeries.C (Γ := ℤ) (γ ^ n)⁻¹) * P₁
  have hP₂ : algebraMap _ (ArcS Dw Dv.Tv.Fr) P₂ = ψ.toRingHom f := by
    have : algebraMap _ (ArcS Dw Dv.Tv.Fr) P₁ = _ := hP₁.trans e3
    simp only [P₂]
    rw [map_mul, this, ← mul_assoc, ← map_pow, ← map_mul, ← map_pow, ← map_mul, ← map_pow, ← map_mul,
      inv_mul_cancel₀ hγn, map_one, map_one, map_one, one_mul]
    rfl
  have hψι : ψ.toRingHom.comp (arcιR Dw Dv.Tv.V Dv.ϖ) =
      (arcι Dw Dv.Tv.Fr).comp (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr)) := RingHom.ext fun p => hψC p
  obtain ⟨N, G, hG⟩ := hdiv ψ.toRingHom hψι hψX f ⟨P₂, hP₂⟩
  have hψalg : ψ.toRingHom.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Dv.Tv.V)) _) =
      (algebraMap _ (ArcS Dw Dv.Tv.Fr)).comp (MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr).comp
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr)))) := by
    refine MvPolynomial.ringHom_ext (fun p => ?_) (fun x => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      exact hψC p
    · simp only [RingHom.comp_apply, MvPolynomial.map_X]
      exact hψX x
  have hPG : P₂ * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr (PowerSeries.C (R := Dv.Tv.Fr)
      (algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ) * PowerSeries.X)) ^ N =
      MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr).comp
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr))) G := by
    apply hinj
    have h1 := congrArg ψ.toRingHom hG
    have h2 := RingHom.congr_fun hψalg G
    have h3 := RingHom.congr_fun hψι (PowerSeries.C (R := Dv.Tv.V) Dv.ϖ * PowerSeries.X)
    simp only [RingHom.comp_apply] at h2 h3
    rw [h2, map_mul, map_pow, h3, ← hP₂, map_mul (PowerSeries.map _), PowerSeries.map_C, PowerSeries.map_X] at h1
    rw [← h1, map_mul, map_pow]
    rfl
  have hdet0 : (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨ev, hevC, hevX, hevf⟩ := GlobalTheory.T.exists_eval_arcLetterRingOverDVR_disc E H Dw Dv.Tv Dv.ϖ Z.K Dv.ιT hϖ Dv.norm_le t Y
    (Z.S_disc t ht).1 (Z.S_disc t ht).2 hdet0
  obtain ⟨hT, hS⟩ := hevf f N G P₂ hG hPG
  have hbd := hRec F hF t ht Y hY hdet ev hevC hevX
  have hq : (fun x => MvPolynomial.eval Y (MvPolynomial.map Dv.ιT (q x))) =
      frameSub (fun τ => (Bm τ).map Dv.ιT) (fun τ k => Dv.ιT (lam τ k)) Y := by
    funext x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [q, frameSub, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.map_apply, map_inv₀, Finset.sum_mul, mul_assoc]
  have hterm : ∀ k : ℤ, MvPolynomial.eval Y (MvPolynomial.map Dv.ιT (GlobalTheory.ArcQ.lcoeffPoly P₂ k)) * t ^ k =
      (Dv.ιT γ ^ n)⁻¹ * (MvPolynomial.eval (frameSub (fun τ => (Bm τ).map Dv.ιT) (fun τ k => Dv.ιT (lam τ k)) Y)
        (MvPolynomial.map Z.ι (GlobalTheory.ArcQ.lcoeffPoly P k)) * t ^ k) := fun k => by
    simp only [P₂]
    rw [lcoeffPoly_const_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C, hco, eval_subst, hq,
      Dv.ιT_io, map_inv₀, map_pow, mul_assoc]
  have hγK : Dv.ιT γ ^ n ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 hγ)
  rw [← hP, arcNum_of_poly]
  simp only [hterm] at hT hS
  refine ⟨?_, ?_⟩
  · have := hT.const_mul ‖Dv.ιT γ ^ n‖
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    rw [← norm_mul, mul_inv_cancel_left₀ hγK]
  · rw [tsum_mul_left] at hS
    rw [← hS]
    exact hbd

theorem frame_of_cut : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (Fs : Set (Rul Xo c)), (∀ F ∈ Fs, F ∈ sec Xo c a n) → (∀ (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr) (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr), γ ≠ 0 → (∀ τ k, lam τ k ≠ 0) → BcRigidAt Dv γ lam Bm → RecordAt Dv Fs → FrameBound Z (Dv.ιT γ) (fun τ k => Dv.ιT (lam τ k)) (fun τ => (Bm τ).map Dv.ιT) n d Fs) ∧ ∀ (vth : ℤ) (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (m : ℕ), FinLocalCutAt d w vth vη m Fs → FinLocalAt d w n vth vη m Fs := by
  intro hL hL2 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d w a n Fs hFs
  refine ⟨fun Z Dv γ lam Bm hγ _ hBc hRec => frameBound_of_cut hL hL2 hev hFs Z Dv γ lam Bm hγ hBc hRec, ?_⟩
  rintro vth vη m ⟨Z, Dv, γ, lam, A, Bm, ⟨hγ, hγn⟩, hlam, ⟨hAB, hA⟩, hBc, hRec⟩
  refine ⟨Z, Dv.ιT γ, fun τ k => Dv.ιT (lam τ k), fun τ => (A τ).map Dv.ιT, fun τ => (Bm τ).map Dv.ιT,
    ⟨(map_ne_zero _).2 hγ, hγn⟩, fun τ k => ⟨(map_ne_zero _).2 (hlam τ k).1, (hlam τ k).2⟩,
    ⟨fun τ => ?_, fun τ k l => hA τ k l⟩, frameBound_of_cut hL hL2 hev hFs Z Dv γ lam Bm hγ hBc hRec⟩
  beta_reduce
  rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.ArcQ.FrameCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyChainArcWitnessUniversalFamily
section
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem algebraMap_laurent_comp_C :
    (algebraMap ℂ⟦X⟧ ℂ⸨X⸩).comp (PowerSeries.C (R := ℂ)) = algebraMap ℂ ℂ⸨X⸩ :=
  RingHom.ext fun _ => rfl

theorem X_not_mem_gen (p : Sp ℂ⸨X⸩) : PowerSeries.X ∉ (gen p).asIdeal := by
  intro h
  have h' : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ∈ p.asIdeal := h
  have hne : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℂ⟦X⟧ ℂ⸨X⸩)).2 PowerSeries.X_ne_zero
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (IsUnit.mk0 _ hne))

theorem exists_generic_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (bF : c.F →+* ℂ) (χ : Sp ℂ⟦X⟧ ⟶ Y.X)
    (hχ : χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp β))
    (hab : ∀ x : Sp ℂ⟦X⟧, PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) :
    ∃ yF : Sp ℂ⸨X⸩ ⟶ Xo.XF c, yF ≫ Y.j = gen ≫ χ ∧
      yF ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF) := by
  have h : (gen ≫ χ) ≫ Y.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF) ≫ spMap β := by
    rw [Category.assoc, hχ, ← algebraMap_laurent_comp_C, spMap_comp, spMap_comp, spMap_comp]
    simp only [Category.assoc]
  have := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ h) ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := hab _ (X_not_mem_gen p)
    have hz : Y.jQ q ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    have hz' : Y.j q ∈ abLocus Y.t.G := by
      simpa only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage] using hz
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, ← hq]
    exact hz'
  have hτ := IsOpenImmersion.lift_fac Y.jQ _ hr
  refine ⟨IsOpenImmersion.lift Y.jQ _ hr, ?_, ?_⟩
  · rw [Model.j, ← Category.assoc, hτ, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, hτ, pullback.lift_snd]

theorem nonempty_chain : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) , χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp β) → (∀ x : Sp ℂ⟦X⟧, PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Nonempty (Chain W Λ) := by
  intro L₁ L₂ E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ hχ hab
  obtain ⟨Ξ⟩ := GlobalTheory.ConstPoint.nonempty_constPts L₁ L₂ E H D l Xo c O β Y _ a χ W Λ
  obtain ⟨ΦW, hW⟩ := GlobalTheory.T.genericPoints_constantPoints_formalSum_values L₁ L₂ E H D l Xo c O β Y _ a χ W Λ Ξ
  obtain ⟨yF, hj, ho⟩ := exists_generic_point Y bF χ hχ hab
  obtain ⟨w₂, r₂⟩ := (_root_.GlobalTheory.RigIso.main L₁ L₂ E H _ _ Y.t W.t χ W.m).1
  obtain ⟨w₁, r₁⟩ := (_root_.GlobalTheory.RigIso.main L₁ L₂ E H _ _ Y.t Y.oF.t _ Y.m).1
  obtain ⟨w₀, r₀⟩ := (_root_.GlobalTheory.RigIso.main L₁ L₂ E H _ _ Xo.univ.t Y.oF.t _ Y.m0.toSABMap).1
  obtain ⟨ΦY, e₂⟩ := (GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Y.t W.t χ W.m w₂ gen (gen ≫ χ) r₂ rfl).1 ΦW
  obtain ⟨ΦF, e₁⟩ := (GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Y.t Y.oF.t _ Y.m w₁ yF (gen ≫ χ) r₁ hj).2 ΦY
  obtain ⟨Φ, e₀⟩ := (GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Xo.univ.t Y.oF.t _ Y.m0.toSABMap w₀ yF
    (yF ≫ pullback.fst _ _) r₀ rfl).1 ΦF
  exact ⟨⟨Ξ, ΦW, hW, yF, hj, ho, ΦY, ΦF, Φ, w₂, w₁, w₀, r₂, r₁, r₀, e₂, e₁, e₀⟩⟩

end GlobalTheory.ArcPts
end
end

