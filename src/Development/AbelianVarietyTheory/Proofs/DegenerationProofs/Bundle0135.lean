module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AnalyticDictionaryIsPointPeriodOrigin
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch

theorem exists_log_of_character {X : Type} [AddCommGroup X] [Module.Free ℤ X] (φ : X → ℂˣ)
    (h : ∀ x y, φ (x + y) = φ x * φ y) : ∃ l : X →+ ℂ, ∀ x, (φ x : ℂ) = eTwoPi (l x) := by
  classical
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h0 : φ 0 = 1 := by
    have h00 := h 0 0
    rw [add_zero] at h00
    exact mul_left_cancel (h00.symm.trans (mul_one _).symm)
  let b := Module.Free.chooseBasis ℤ X
  let l : X →+ ℂ :=
    (b.constr ℤ fun i => Complex.log (φ (b i)) / (2 * Real.pi * Complex.I)).toAddMonoidHom
  refine ⟨l, fun x => ?_⟩
  let f₁ : X →+ Additive ℂˣ :=
    { toFun := fun x => Additive.ofMul (φ x)
      map_zero' := by simp [h0]
      map_add' := fun x y => by simp [h] }
  let f₂ : X →+ Additive ℂˣ :=
    { toFun := fun x => Additive.ofMul (Units.mk0 (eTwoPi (l x)) (AnArc.e_ne_zero _))
      map_zero' := by
        apply Additive.toMul.injective
        ext
        simp
      map_add' := fun x y => by
        apply Additive.toMul.injective
        ext
        simp [AnArc.e_add] }
  have key : f₁.toIntLinearMap = f₂.toIntLinearMap := by
    refine b.ext fun i => ?_
    show Additive.ofMul (φ (b i)) = Additive.ofMul (Units.mk0 (eTwoPi (l (b i))) (AnArc.e_ne_zero _))
    congr 1
    ext
    rw [Units.val_mk0]
    have hl : l (b i) = Complex.log (φ (b i)) / (2 * Real.pi * Complex.I) := by
      simp [l]
    rw [hl, eTwoPi, mul_div_cancel₀ _ hπ, Complex.exp_log (Units.ne_zero _)]
  have hx := congrArg (fun u : Additive ℂˣ => ((Additive.toMul u : ℂˣ) : ℂ)) (LinearMap.congr_fun key x)
  simpa [f₁, f₂] using hx

variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O} (d : Dict N B)

theorem Dict.cube_val (x y z : Fin B.gB → ℂ) :
    (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) =
      d.fr (x + y + z) * d.fr x * d.fr y * d.fr z := by
  have h := congrArg Units.val (d.ab.2.2.2.2.2.1 x y z)
  push_cast at h
  exact h

theorem Dict.existsUnique_isPt (v : B.V) : ∃! g, d.IsPt v g := by
  let E : B.X → ℂˣ := fun x => Units.mk0 (eTwoPi (v.1 x)) (AnArc.e_ne_zero _)
  let s : N.X → ℂˣ := fun χ =>
    E (d.eX.symm χ) * d.fr (B.ct (d.eX.symm χ)) * d.fr v.2 * (d.fr (B.ct (d.eX.symm χ) + v.2))⁻¹
  have hs : ∀ χ χ', s (χ + χ') * N.θ (N.c χ) (N.c χ') (d.ex v.2) = s χ * s χ' := by
    intro χ χ'
    obtain ⟨x, rfl⟩ := d.eX.surjective χ
    obtain ⟨x', rfl⟩ := d.eX.surjective χ'
    rw [← map_add d.eX, d.c_eq, d.c_eq]
    have h := d.cube_val (B.ct x) (B.ct x') v.2
    ext
    simp only [s, E, AddEquiv.symm_apply_apply, map_add (f := _), Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0, AnArc.e_add]
    have hθ : (N.θ (d.ex (B.ct x)) (d.ex (B.ct x')) (d.ex v.2) : ℂ) =
        d.fr (B.ct x + B.ct x' + v.2) * d.fr (B.ct x) * d.fr (B.ct x') * d.fr v.2 /
          (d.fr (B.ct x + B.ct x') * d.fr (B.ct x + v.2) * d.fr (B.ct x' + v.2)) := by
      rw [eq_div_iff (by simp)]
      linear_combination h
    rw [hθ]
    field_simp
  refine ⟨⟨d.ex v.2, s, hs⟩, ⟨rfl, fun x => ?_⟩, ?_⟩
  · simp only [s, E, AddEquiv.symm_apply_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [inv_mul_cancel_right₀ (Units.ne_zero _)]
  · rintro g ⟨hb, hg⟩
    refine NumD.Gt.ext hb (funext fun χ => ?_)
    obtain ⟨x, rfl⟩ := d.eX.surjective χ
    apply Units.ext
    have h := hg x
    simp only [s, E, AddEquiv.symm_apply_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [eq_mul_inv_iff_mul_eq₀ (Units.ne_zero _)]
    exact h

theorem Dict.exists_isPt (g : N.Gt) : ∃ v, d.IsPt v g := by
  obtain ⟨w, hw⟩ := d.ab.2.1 g.b
  let φ : B.X → ℂˣ := fun x => g.s (d.eX x) * d.fr (B.ct x + w) * (d.fr (B.ct x) * d.fr w)⁻¹
  have hφ : ∀ x y, φ (x + y) = φ x * φ y := by
    intro x y
    have hm := g.mult (d.eX x) (d.eX y)
    rw [d.c_eq, d.c_eq, ← hw] at hm
    have hm' := congrArg Units.val hm
    push_cast at hm'
    have h := d.cube_val (B.ct x) (B.ct y) w
    ext
    simp only [φ, map_add (f := _), Units.val_mul, Units.val_inv_eq_inv_val, mul_inv]
    have hS : (g.s (d.eX x + d.eX y) : ℂ) =
        g.s (d.eX x) * g.s (d.eX y) / N.θ (d.ex (B.ct x)) (d.ex (B.ct y)) (d.ex w) := by
      rw [eq_div_iff (Units.ne_zero _)]
      exact hm'
    have hθ : (N.θ (d.ex (B.ct x)) (d.ex (B.ct y)) (d.ex w) : ℂ) =
        d.fr (B.ct x + B.ct y + w) * d.fr (B.ct x) * d.fr (B.ct y) * d.fr w /
          (d.fr (B.ct x + B.ct y) * d.fr (B.ct x + w) * d.fr (B.ct y + w)) := by
      rw [eq_div_iff (by simp)]
      linear_combination h
    rw [hS, hθ]
    field_simp
  obtain ⟨l, hl⟩ := exists_log_of_character φ hφ
  refine ⟨(l, w), hw.symm, fun x => ?_⟩
  show (g.s (d.eX x) : ℂ) * d.fr (B.ct x + w) = eTwoPi (l x) * d.fr (B.ct x) * d.fr w
  rw [← hl x]
  simp only [φ, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem Dict.IsPt.add {d : Dict N B} {v v' : B.V} {g g' : N.Gt} (h : d.IsPt v g) (h' : d.IsPt v' g') :
    d.IsPt (v + v') (g * g') := by
  obtain ⟨hb, hs⟩ := h
  obtain ⟨hb', hs'⟩ := h'
  refine ⟨?_, fun x => ?_⟩
  · rw [NumD.Gt.mul_b, hb, hb', Prod.snd_add, d.ab.1]
  · have e1 := hs x
    have e2 := hs' x
    have hc := d.cube_val (B.ct x) v.2 v'.2
    rw [NumD.Gt.mul_s, d.c_eq, hb, hb']
    simp only [Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply, AnArc.e_add, Units.val_div_eq_div_val,
      Units.val_mul, ← add_assoc]
    have h1 : (g.s (d.eX x) : ℂ) = eTwoPi (v.1 x) * d.fr (B.ct x) * d.fr v.2 / d.fr (B.ct x + v.2) := by
      rw [eq_div_iff (Units.ne_zero _)]
      exact e1
    have h2 : (g'.s (d.eX x) : ℂ) = eTwoPi (v'.1 x) * d.fr (B.ct x) * d.fr v'.2 / d.fr (B.ct x + v'.2) := by
      rw [eq_div_iff (Units.ne_zero _)]
      exact e2
    have hθ : (N.θ (d.ex (B.ct x)) (d.ex v.2) (d.ex v'.2) : ℂ) =
        d.fr (B.ct x + v.2 + v'.2) * d.fr (B.ct x) * d.fr v.2 * d.fr v'.2 /
          (d.fr (B.ct x + v.2) * d.fr (B.ct x + v'.2) * d.fr (v.2 + v'.2)) := by
      rw [eq_div_iff (by simp)]
      linear_combination hc
    rw [h1, h2, hθ]
    field_simp

theorem Dict.analyticDictionary_isPoint_period_origin (la : B.La) : d.IsPt (B.P0 la) (N.io (d.eX la.y)) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [NumD.io_b, d.c_eq, AnArc.degeneratingTori_basePeriodMap_snd, d.ab.1, (d.ab.2.2.1 _).mpr la.l.2, mul_one]
  · rw [NumD.io_s, AnArc.degeneratingTori_basePeriodMap_snd, AnArc.degeneratingTori_basePeriodMap_fst_apply, sub_eq_add_neg, AnArc.e_add, AnArc.e_add,
      AnArc.e_intCast, AnArc.e_neg_div, Complex.exp_neg, mul_one]
    have h1 := congrArg Units.val (N.ψ_add (d.eX la.y) (d.eX x))
    have h2 := congrArg Units.val (d.ψ_eq (la.y + x))
    have h3 := B.psi_add la.y x
    have h4 := congrArg Units.val (d.ψ_eq la.y)
    have h5 := congrArg Units.val (d.ψ_eq x)
    have h6 := d.ab.2.2.2.2.1 la.l (B.ct la.y + B.ct x)
    have h7 := d.ab.2.2.2.2.1 la.l (B.ct la.y)
    have h8 := B.ah_add la.l (B.ct la.y) (B.ct x)
    push_cast at h1 h2 h4 h5
    rw [map_add d.eX, map_add B.ct] at h2
    rw [show B.ct la.y + B.ct x + (la.l : Fin B.gB → ℂ) = B.ct x + (B.ct la.y + la.l) by abel] at h6
    have key : ((N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) *
          Complex.exp (Real.pi * B.H (B.ct x) la.l) -
        eTwoPi (B.T la.y x) * d.fr (B.ct x) * d.fr (B.ct la.y + la.l)) *
        ((N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * B.ah la.l (B.ct la.y)) = 0 := by
      linear_combination
        (-((d.fr (B.ct x + (B.ct la.y + la.l)) : ℂ) * Complex.exp (Real.pi * B.H (B.ct x) la.l) *
            B.ah la.l (B.ct la.y))) * h1
        - (N.ψ (d.eX la.y + d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) * h8
        - (N.ψ (d.eX la.y + d.eX x) : ℂ) * h6 + h2 + h3
        - (B.psi la.y : ℂ) * eTwoPi (B.T la.y x) * h5
        - (N.ψ (d.eX x) : ℂ) * d.fr (B.ct x) * eTwoPi (B.T la.y x) * h4
        + (N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * d.fr (B.ct x) * eTwoPi (B.T la.y x) * h7
    have hne : ((N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * B.ah la.l (B.ct la.y)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (B.ah_ne_zero _ _)
    have hD := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)
    have hQ : Complex.exp (Real.pi * B.H (B.ct x) la.l) ≠ 0 := Complex.exp_ne_zero _
    calc (N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l))
        = (N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) *
            Complex.exp (Real.pi * B.H (B.ct x) la.l) * (Complex.exp (Real.pi * B.H (B.ct x) la.l))⁻¹ := by
          rw [mul_inv_cancel_right₀ hQ]
      _ = _ := by rw [hD]; ring

theorem Dict.isPt_one_iff (v : B.V) : d.IsPt v 1 ↔ ∃ la : B.La, la.y = 0 ∧ v = B.P0 la := by
  constructor
  · rintro ⟨hb, hs⟩
    rw [NumD.Gt.one_b] at hb
    have hl : v.2 ∈ B.abelian₂ := (d.ab.2.2.1 v.2).mp hb.symm
    let l : B.abelian₂ := ⟨v.2, hl⟩
    have hp0 : (1 : ℂ) = B.ah l 0 * d.fr v.2 := by
      have h0 : (d.fr 0 : ℂ) = B.ah l 0 * d.fr (0 + v.2) := d.ab.2.2.2.2.1 l 0
      rwa [zero_add, d.ab.2.2.2.1, Units.val_one] at h0
    have hhalf : ∀ z : ℂ, eTwoPi (z / (2 * Complex.I)) = Complex.exp (Real.pi * z) := by
      intro z
      have := AnArc.e_neg_div (-z)
      rwa [neg_div, neg_neg, mul_neg, neg_neg] at this
    have hint : ∀ x, ∃ m : ℤ, (m : ℂ) = v.1 x + B.H (B.ct x) v.2 / (2 * Complex.I) := by
      intro x
      have hsx := hs x
      rw [NumD.Gt.generator_inv_base, Units.val_one, one_mul] at hsx
      have hp1 : (d.fr (B.ct x) : ℂ) = B.ah l (B.ct x) * d.fr (B.ct x + v.2) := d.ab.2.2.2.2.1 l (B.ct x)
      have hq := B.ah_add l 0 (B.ct x)
      rw [zero_add] at hq
      have hF : (d.fr (B.ct x + v.2) : ℂ) *
          (1 - eTwoPi (v.1 x) * Complex.exp (Real.pi * B.H (B.ct x) v.2)) = 0 := by
        linear_combination hsx + eTwoPi (v.1 x) * d.fr v.2 * hp1 +
          eTwoPi (v.1 x) * d.fr v.2 * d.fr (B.ct x + v.2) * hq -
          eTwoPi (v.1 x) * Complex.exp (Real.pi * B.H (B.ct x) v.2) * d.fr (B.ct x + v.2) * hp0
      have h1 := sub_eq_zero.mp ((mul_eq_zero.mp hF).resolve_left (Units.ne_zero _))
      have he : eTwoPi (v.1 x + B.H (B.ct x) v.2 / (2 * Complex.I)) = 1 := by
        rw [AnArc.e_add, hhalf]
        exact h1.symm
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
      refine ⟨m, ?_⟩
      have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      apply mul_left_cancel₀ hπ
      rw [hm]
      ring
    let n : B.X →+ ℤ :=
      { toFun := fun x => (hint x).choose
        map_zero' := Int.cast_injective (α := ℂ) (by
          rw [(hint 0).choose_spec, Int.cast_zero]
          simp)
        map_add' := fun x y => Int.cast_injective (α := ℂ) (by
          rw [Int.cast_add, (hint (x + y)).choose_spec, (hint x).choose_spec, (hint y).choose_spec]
          simp only [map_add (f := _), AnArc.H_add_left]
          ring) }
    refine ⟨AnArc.La.mk 0 n l, AnArc.La.mk_y _ _ _, ?_⟩
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · rw [AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.La.mk_y, AnArc.La.mk_n, AnArc.La.mk_l, map_zero,
        AddMonoidHom.zero_apply, zero_add]
      show v.1 x = ((hint x).choose : ℂ) - B.H (B.ct x) v.2 / (2 * Complex.I)
      rw [(hint x).choose_spec]
      ring
    · rw [AnArc.degeneratingTori_basePeriodMap_snd, AnArc.La.mk_y, AnArc.La.mk_l, map_zero, zero_add]
  · rintro ⟨la, hy, rfl⟩
    have h := d.analyticDictionary_isPoint_period_origin la
    rwa [hy, map_zero, NumD.io_zero] at h

theorem ptSt : PtSt := fun _ _ _ _ _ d =>
  ⟨d.existsUnique_isPt, d.exists_isPt, fun _ _ _ _ h h' => h.add h', d.isPt_one_iff, d.analyticDictionary_isPoint_period_origin⟩

end GlobalTheory.Ex.Arch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumPullbackRescaledMatches
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.RescaleMatch

theorem genRel_rescale {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg f D D') (q : D'.X → (FractionRing R')ˣ) (F : Type) [Field F]
    [Algebra (FractionRing R') F] [Algebra (FractionRing R) F]
    (hF : ∀ x, algebraMap (FractionRing R) F (algebraMap R _ x) = algebraMap (FractionRing R') F (algebraMap R' _ (f x)))
    (x : D'.X) :
    GenRel hD.w (LB.pullGen _ _ _ ((TauTwist.rescale D' q).psi x) (jFK (R := R') F))
      (LB.pullGen _ _ _ (D.psi (hD.xe x)) (jFK (R := R) F)) (algebraMap (FractionRing R') F (q x)) := by
  have hj : jFK (R := R') F ≫ jK R' ≫ spMap f = jFK (R := R) F ≫ jK R :=
    (congrArg (_ ≫ ·) (Geo.Tor.spMap_comp f _).symm).trans ((Geo.Tor.spMap_comp _ _).symm.trans
      ((congrArg spMap (RingHom.ext fun x => (hF x).symm)).trans (Geo.Tor.spMap_comp _ _)))
  have hx : D'.xK x ≫ PsiEvenPull.proj hD = jK R' ≫ specOf f ≫ (D.c (hD.xe x)).left := by
    rw [← hD.c_pr x, ← Category.assoc]; rfl
  have hpt : (jFK (R := R') F ≫ D'.xK x) ≫ PsiEvenPull.proj hD = jFK (R := R) F ≫ D.xK (hD.xe x) := by
    rw [Category.assoc, hx, ← Category.assoc (jK R'), ← Category.assoc]
    exact (congrArg (· ≫ _) hj).trans (Category.assoc _ _ _)
  have z : Sp F := (default : PrimeSpectrum F)
  refine (ArcPsiOn.genRel_iff_val D'.P.isLB D.P.isLB hD.w _ _ _ z).2 ⟨hpt, fun J J' hJ hJ' => ?_⟩
  have e := ArcPull.psi_val hD (jFK (R := R) F) (jFK (R := R') F) hj hJ hJ' x
  have e₁ := TauTwist.val_psi_rescale q x (jFK (R := R') F) hJ'
  have e₂ := TauTwist.unitAt_spMap (𝟙 (Sp F)) (algebraMap (FractionRing R') F) z (q x)
  rw [Category.id_comp] at e₂
  have e₃ : (TauTwist.unitAt (𝟙 (Sp F)) z (Units.map (algebraMap (FractionRing R') F).toMonoidHom (q x))).val =
      toStk z (algebraMap (FractionRing R') F (q x)) := gm_val _ z ⊤ trivial _
  rw [zpow_neg_one, ← e₃, ← Units.val_mul]
  exact congrArg Units.val ((congrArg₂ (· * ·) rfl (((val_pull hJ' _ _ _).trans (by rw [Category.id_comp])).trans e₁)).trans
    ((mul_left_comm _ _ _).trans (congrArg₂ (· * ·) e₂
      (e.symm.trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])).symm))))

theorem exists_match_rescale : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] (f : O' →+* R) (D' : DegPre R) (hD : IsPullDeg f a.D₀ D') (u₀ : R) (uK : (FractionRing R)ˣ), (uK : FractionRing R) = algebraMap R _ u₀ → ∀ (q : D'.X → (FractionRing R)ˣ) (Φ : D'.P.A.left ⟶ a.D₀.P.A.left), Φ = PsiEvenPull.proj hD → (∀ y, q y = uK ^ (a.be (hD.xe y) (hD.xe y) / 2)) → ∃ (_ : Module (𝓞 E) (TauTwist.rescale D' q).X) (oW : letI := H.starRing; (TauTwist.rescale D' q).OAct (𝓞 E)) (he : _) (w : _) (e : _), GlobalTheory.LN.Match a f u₀ (TauTwist.rescale D' q) oW Φ he w e ∧ (∀ y, hD.xe (e y) = y) ∧ (TauTwist.rescale D' q).PsiEven ∧ (TauTwist.rescale D' q).TauBimult := by
  intro hG E _ _ _ H D l c O _ β O' _ _ b a R _ _ f D' hD u₀ uK hu q Φ hΦ hq
  subst hΦ
  letI := H.starRing
  obtain ⟨inst, o', hs, ho⟩ := exists_oAct_of_isPullDeg hG O' R f a.D₀ D' hD (𝓞 E) a.oa
  have hw := TauTwist.halfUnit_add_star H
  have ht : TauTwist.IsScalarForm (𝓞 E) fun y x : D'.X => uK ^ a.be (hD.xe y) (hD.xe x) :=
    ⟨fun y x x' => by rw [map_add (f := _), map_add (f := _), zpow_add], fun y x => by rw [a.be_symm],
      fun r y x => by rw [hs, hs, a.be_adj]; rfl⟩
  obtain rfl : q = fun y => uK ^ a.be (hD.xe y) (hD.xe (H.w0 • y)) := funext fun y => by
    have h₁ : a.be (hD.xe y) (H.bar H.w0 • hD.xe y) = a.be (hD.xe y) (H.w0 • hD.xe y) := by
      rw [← a.be_adj, a.be_symm]
    have h₂ : a.be (hD.xe y) ((H.w0 + H.bar H.w0) • hD.xe y) = a.be (hD.xe y) (hD.xe y) := by
      rw [show H.w0 + H.bar H.w0 = 1 from hw, one_smul]
    rw [add_smul, map_add (f := _), h₁] at h₂
    rw [hq, hs, ← h₂]
    congr 1
    omega
  let e : D'.X ≃ₗ[𝓞 E] a.D₀.X := { hD.xe with map_smul' := hs }
  have he : ∀ y, hD.xe (e.symm y) = y := fun y => e.apply_symm_apply y
  let oW : (TauTwist.rescale D' fun y => uK ^ a.be (hD.xe y) (hD.xe (H.w0 • y))).OAct (𝓞 E) :=
    (TauTwist.twistAct (D := D') hw ht o' :)
  have ev := TauTwist.psiEven_twist (D := D') ht H.w0 (PsiEvenPull.psiEven_pull hG _ _ f _ _ hD a.even)
  have bi := TauTwist.tauBimult_twist (D := D') hw ht (tauBimult_of_isPullDeg hG _ _ f _ _ hD a.bimult)
  refine ⟨inst, oW, hD.he, hD.w, e.symm,
    ⟨pull_grp hD, hD.w_gen, hD.w_rig, fun x => ?_, fun y => ?_, fun F _ _ _ _ uF hF huF y => ?_⟩, he, ev, bi⟩
  · have e₀ := congrArg (fun z => z.left ≫ pullback.fst a.D₀.P.A.hom (specOf f)) (ho x)
    have e₂ : ((Over.pullback (specOf f)).map (a.oa.onB.act x)).left ≫
        pullback.fst a.D₀.P.A.hom (specOf f) = pullback.fst _ _ ≫ (a.oa.onB.act x).left :=
      pullback.lift_fst _ _ _
    simp only [Over.comp_left, Category.assoc, e₂] at e₀
    exact e₀.trans (Category.assoc _ _ _).symm
  · exact (hD.c_pr (e.symm y)).trans (by rw [he])
  · have k := genRel_rescale hD (fun y => uK ^ a.be (hD.xe y) (hD.xe (H.w0 • y))) F hF (e.symm y)
    have v : algebraMap (FractionRing R) F ((uK ^ a.be (hD.xe (e.symm y)) (hD.xe (H.w0 • e.symm y)) : (FractionRing R)ˣ) :
        FractionRing R) = uF ^ (a.be y y / 2) := by
      rw [show uK ^ a.be (hD.xe (e.symm y)) (hD.xe (H.w0 • e.symm y)) = _ from hq (e.symm y), he,
        Units.val_zpow_eq_zpow_val, map_zpow₀, hu, huF]
    beta_reduce at k
    rw [v, he] at k
    exact k

end GlobalTheory.RescaleMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.AbVal

theorem cmField_host_element_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have h2 : 2 * H.bar H.w0 = 1 + H.bar H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  have h3 : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
    · exfalso
      have e' : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, e]
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have c := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
      rw [e'] at c
      have r : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
        simpa using this
      obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 c.symm
      rw [hx] at r
      have r' : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast r
      have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [sq_nonneg x]
    · exact e
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, h2, H.two_weight_eq_one_add_root, h3]; ring
  exact mul_left_cancel₀ two_ne_zero this

theorem rg_ne_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) : ν.rg ≠ 0 := fun h =>
  (((Units.isUnit _).map _).map _).ne_zero ((dif_pos (fun z _ =>
    Good.mem (L := D.P.L) (z := z) (J := ν.J) (fun ψ => ν.good ψ trivial) (fun _ : PUnit => eSec D.P.A)
      (TF (R := R) F).hom)).symm.trans h)

theorem exists_ringHom_lift {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {O : Type} [CommRing O]
    (act : RingAct A O) {V : Type} [AddCommGroup V] [Module ℂ V] (ex : V → (T ⟶ A))
    (hadd : ∀ z w, ex (z + w) = ex z * ex w)
    (hlift : ∀ f : A ⟶ A, IsMonHom f → ∃! F : V →ₗ[ℂ] V, ∀ z, ex (F z) = ex z ≫ f) :
    ∃ F : O →+* Module.End ℂ V, ∀ a z, ex (F a z) = ex z ≫ act.act a := by
  choose F hF hU using fun a => hlift (act.act a) (act.hom a)
  have add : ∀ a b, F (a + b) = F a + F b := fun a b => (hU _ _ fun z => by
    rw [LinearMap.add_apply, hadd, hF, hF, act.map_add]
    exact (MonObj.comp_mul _ _ _).symm).symm
  refine ⟨RingHom.mk' ⟨⟨F, (hU _ _ fun z => ?_).symm⟩, fun a b => (hU _ _ fun z => ?_).symm⟩ add, hF⟩
  · rw [act.map_one, Category.comp_id]; rfl
  · rw [act.map_mul, Module.End.mul_apply, hF, hF, Category.assoc]

theorem valSt (hL : Laws) (hFam : BrFamSt) (hEx : FibExSt) (hGrp : FibGrpSt) (hCube : FibCubeSt) (hSym : FibSymSt)
    (hRos : FibRosSt) (hPrim : FibPrimSt) (hSec : FibSecSt) (hLie : FibLieSt) : ValSt := by
  intro E _ _ _ H D R _ _ _ A
  letI := H.starRing
  obtain ⟨g, Λ, Hm, χ, Ef, ex, fr, hf, hEf, hbij⟩ := hEx R A.D₀.P A.ν.J A.ν.good
  obtain ⟨hdisc, hfull, hherm, hpos, hnorm, hχ, hadd, hsurj, hker, hfr, hlift⟩ := hGrp R A.D₀ _ g Λ Hm χ ex fr hf
  have hcube := hCube R A.D₀ _ g Λ Hm χ ex fr hf
  obtain ⟨hsym, hneg⟩ := hSym R A.D₀ _ g Λ Hm χ ex fr hf
  have hros := hRos R A.D₀ _ g Λ Hm χ ex fr hf
  have hprim := hPrim R A.D₀ _ g Λ Hm χ ex fr hf
  obtain ⟨θ, hθ, hθv⟩ := hSec R A.D₀ _ g Λ Hm χ ex fr hf A.ν.th
  have hlie := hLie R A.D₀ _ g Λ Hm χ ex fr hf
  obtain ⟨F, hF⟩ := exists_ringHom_lift A.oa.onB.toRingAct ex hadd hlift
  have hmem : ∀ a, ∀ l ∈ Λ, F a l ∈ Λ := fun a l hl => by
    haveI := A.oa.onB.hom a
    rw [← hker, hF, (hker l).2 hl, MonObj.one_comp]
  have hadj : ∀ a z w, hermForm Hm (F a z) w = hermForm Hm z (F (star a) w) := fun a => by
    haveI := A.oa.onB.hom a
    haveI := A.oa.onB.hom (star a)
    obtain ⟨r, hr⟩ := exists_ros hL.globalFns A.D₀.P.isAb A.D₀.P.isLB _ _ (A.oa.onB.rosati a)
    exact (hros _ _ (A.oa.onB.hom a) (A.oa.onB.hom (star a)) _ _ (hF a) (hF (star a)) r hr).1
  let B : An H :=
    { gB := g, abelian₂ := Λ, discrete := hdisc, full := hfull, Hm := Hm, Hm_herm := hherm, Hm_pos := hpos, Ef := Ef,
      Ef_eq := hEf, Ef_bij := hbij, chi := χ, chi_norm := hnorm, chi_add := hχ, chi_neg := hneg, F := F,
      F_mem := hmem, F_adj := hadj, X := PUnit, ct := 0, ct_smul := fun a _ => (map_zero (F a)).symm, T := 0,
      T_symm := fun _ _ => rfl, T_adj := fun _ _ _ => rfl, psi := fun _ => 1, psi_neg := fun _ => rfl,
      psi_add := fun _ _ => by simp, be := 0, be_symm := fun _ _ => rfl, be_pos := fun _ h => (h rfl).elim,
      be_adj := fun _ _ _ => rfl, be_even := fun _ => dvd_zero _ }
  have hrg := rg_ne_zero A.ν
  have h0 := (fr 0).ne_zero
  have hw : ∀ z w, hermForm Hm z w = hermForm Hm z (F H.w0 w) + hermForm Hm (F H.w0 z) w := fun z w => by
    rw [hadj]
    refine Eq.trans ?_ (B.H_add_right z (F H.w0 w) (F (star H.w0) w))
    rw [← LinearMap.add_apply, ← map_add (f := _), show H.w0 + star H.w0 = 1 from cmField_host_element_add_conj_eq_one H, map_one]
    rfl
  have hp := hprim _ (A.oa.onB.hom H.w0) (F H.w0) (hmem H.w0) (hF H.w0) hw Ef hEf
  have hth : ∀ z, A.N.th (A.ν.eA.symm (ex z)) = θ z * fr 0 / A.ν.rg * ((fr z / fr 0 : ℂˣ) : ℂ) := fun z => by
    have e := A.ν.th_eq (A.ν.eA.symm (ex z))
    rw [MulEquiv.apply_symm_apply, hθv] at e
    change _ * A.ν.rg = _ at e
    rw [Units.val_div_eq_div_val, eq_div_of_mul_eq hrg e]
    field_simp
  refine ⟨B, fun z => A.ν.eA.symm (ex z), fun z => fr z / fr 0, fun z => θ z * fr 0 / A.ν.rg,
    ⟨fun z w => (congrArg A.ν.eA.symm (hadd z w)).trans (map_mul _ _ _), A.ν.eA.symm.surjective.comp hsurj,
      fun z => (map_eq_one_iff _ A.ν.eA.symm.injective).trans (hker z), div_self' _, fun l z => ?_, fun x y z => ?_,
      fun x => ?_, ⟨by simp only [div_eq_mul_inv]; exact (hθ.mul_const _).mul_const _, fun l z => ?_⟩, hth⟩, ?_, ?_, fun τ => ?_, fun a z => ?_,
      fun a b r hr x z => ?_, fun t ht z => ?_⟩
  · beta_reduce
    rw [Units.val_div_eq_div_val, Units.val_div_eq_div_val, hfr l z, mul_div_assoc]
    rfl
  · refine Units.ext ?_
    have e := hcube x y z
    simp only [Units.val_mul, Units.val_div_eq_div_val, A.ν.θ_eq, MulEquiv.apply_symm_apply]
    field_simp
    linear_combination e
  · refine Units.ext ?_
    have e := hsym x
    simp only [Units.val_mul, Units.val_div_eq_div_val, A.ν.σ_eq, MulEquiv.apply_symm_apply]
    rw [← e, mul_div_assoc]
  · have e₁ := hθv (z + l)
    rw [hadd, (hker l).2 l.2, _root_.mul_one, hθv, hfr l z, ← _root_.mul_assoc] at e₁
    have e₂ := mul_right_cancel₀ (fr (z + l)).ne_zero e₁
    change θ (z + l) * fr 0 / A.ν.rg = (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ 1 *
      Complex.exp (Real.pi * B.H 0 l) * (θ z * fr 0 / A.ν.rg)
    rw [← e₂, B.H_zero_left, mul_zero, Complex.exp_zero]
    ring
  · intro hz
    haveI := A.closed
    obtain ⟨-, -, -, ⟨s, f, hs, hf0⟩, hv, -⟩ := hFam R A.D₀ A.even A.bimult ℂ A.N A.ν 1 le_rfl
    obtain ⟨c, rfl⟩ := hv s f hs
    refine hf0 (funext fun α => funext fun x => ?_)
    obtain ⟨z, hz'⟩ := hsurj (A.ν.eA (x * A.N.c α))
    have e := hth z
    rw [hz', MulEquiv.symm_apply_apply, congrFun hz z] at e
    simp [NumD.vth, e]
  · obtain ⟨t, h₁, h₂, -⟩ := A.w0
    exact (hp t ⟨h₁, h₂⟩).1
  · obtain ⟨n, h₁, h₂⟩ := A.det τ
    rw [← h₂]
    exact congrArg (· + _) (hlie _ (ofRingAct A.oa.onB.toRingAct) (fun a => F a) hF τ n h₁)
  · simp only [MulEquiv.apply_symm_apply]
    exact hF a z
  · have e := (hros _ _ (A.oa.onB.hom a) (A.oa.onB.hom b) _ _ (hF a) (hF b) r hr).2 x z
    simp only [Units.val_div_eq_div_val, MulEquiv.apply_symm_apply]
    change _ * ((fr (F a x) : ℂ) / _) * _ * ((fr (x + F b z) : ℂ) / _) = (fr (F a x + z) : ℂ) / _ * _ * ((fr (F b z) : ℂ) / _)
    field_simp
    linear_combination e
  · have e := (hp t ht).2 z
    simp only [Units.val_div_eq_div_val, MulEquiv.apply_symm_apply]
    change _ * _ * ((fr (F H.w0 z) : ℂ) / _) = (fr (z + F H.w0 z) : ℂ) / _
    field_simp
    linear_combination e

end GlobalTheory.Ex.Arch.AbVal
end
end

