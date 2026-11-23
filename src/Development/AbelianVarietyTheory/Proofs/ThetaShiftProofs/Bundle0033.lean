module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowMulEqSumConstantExpansion
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstExpSpan

open GlobalTheory.ConstFam GlobalTheory.FieldBaseChange

theorem exists_rep (M : Type) [AddCommGroup M] (j : ℕ) :
    ∃ (C : Type) (rep : C → M), ∀ α, ∃! x, ∃ mu, rep x + j • mu = α := by
  refine ⟨M ⧸ (nsmulAddMonoidHom j : M →+ M).range, Quotient.out, fun α => ⟨QuotientAddGroup.mk α, ?_, ?_⟩⟩
  · obtain ⟨mu, h⟩ := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk α :
      M ⧸ (nsmulAddMonoidHom j : M →+ M).range))
    exact ⟨mu, by rw [show j • mu = _ from h, add_neg_cancel_left]⟩
  · rintro x ⟨mu, rfl⟩
    exact (QuotientAddGroup.out_eq' x).symm.trans (QuotientAddGroup.eq.2 ⟨mu, (neg_add_cancel_left _ _).symm⟩)

def valLin {R Z : Type} [CommRing R] [CommRing Z] [IsLocalRing Z] {Y : Scheme.{0}} (π : Y ⟶ Sp R) (M : LB Y)
    (κ : R →+* Z) (p : Sp Z ⟶ Y) (hp : p ≫ π = spMap κ) (i : M.ι) (hi : ⊤ ≤ p ⁻¹ᵁ M.U i) :
    SecOver π M →ₛₗ[κ] Z where
  toFun s := valR p (M.U i) (LB.Sec.f s i)
  map_add' s t := toStkA_injective (by
    rw [map_add (f := _), FormalValue.toStkA_valR_eq_gs _ _ _ hi, FormalValue.toStkA_valR_eq_gs _ _ _ hi,
      FormalValue.toStkA_valR_eq_gs _ _ _ hi]
    exact gs_add p _ _ (hi trivial) _ _)
  map_smul' r s := toStkA_injective (by
    have H : constVal (p ≫ π) (cpt Z) r = toStkA (cpt Z) (κ r) := by
      rw [hp, ← Category.id_comp (spMap κ)]
      exact (constVal_specMap _ κ _ r).trans (gs_eq (𝟙 _) _ ⊤ trivial _)
    rw [smul_eq_mul, map_mul, FormalValue.toStkA_valR_eq_gs _ _ _ hi, FormalValue.toStkA_valR_eq_gs _ _ _ hi, ← H]
    exact gs_smul π p _ _ (hi trivial) r _)

theorem exists_pow_mul_eq_sum : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), 1 ≤ j → ∃ (N n : ℕ) (r : Fin n → ℂ⟦X⟧) (s : Fin n → Out.H0 W.P.U.LG.L j), (∀ i, HasConstExp W (s i)) ∧ ∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (κ : ℂ⟦X⟧ →+* Z) (p : Sp Z ⟶ W.t.G.left) (k : W.P.U.LG.L.ι), p ≫ W.t.G.hom = spMap κ → ⊤ ≤ p ⁻¹ᵁ W.P.U.LG.L.U k → κ PowerSeries.X ^ N * FormalValue.secVal W.P.U.toUnifPre σ p k = ∑ i, κ (r i) * FormalValue.secVal W.P.U.toUnifPre (s i) p k := by
  intro hL E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W j σ hj
  have hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e :=
    ⟨W.spec.1, W.spec.2.1, W.spec.2.2.1, W.spec.2.2.2.1, W.spec.2.2.2.2.1,
      fun F _ _ _ _ uF h₁ h₂ => (W.spec.2.2.2.2.2 F uF h₁ h₂).1⟩
  obtain ⟨C, rep, hrep⟩ := exists_rep a.D₀.X j
  let bas := fun x => Module.Basis.ofVectorSpace ℂ (SecBMod a.D₀ j (rep x))
  have ex := fun i : Σ x, Module.Basis.ofVectorSpaceIndex ℂ (SecBMod a.D₀ j (rep x)) =>
    exists_expandsAt hW hL.globalFns hj W.P.U (rep i.1) (bas i.1 i.2)
  choose m hm using ex
  choose f s hf hE using fun i => hm i (m i) le_rfl
  obtain ⟨N, hN⟩ := exists_pow_smul_mem_span hW hL.globalFns hj W.P.U rep hrep bas m f s hf hE σ
  obtain ⟨n, r, t, ht⟩ := Submodule.mem_span_set'.1 hN
  refine ⟨N, n, r, fun i => (t i).1, fun i => ?_, fun Z _ _ κ p k hp hk => ?_⟩
  · obtain ⟨q, hq⟩ := (t i).2
    refine (congrArg (HasConstExp W) hq).mp ⟨f q, hE q, fun x => ?_⟩
    rcases eq_or_off W.e j (rep q.1) (W.e x) with ⟨mu, h⟩ | h
    · obtain rfl := W.e.injective h
      refine ⟨feTranslate a.D₀ j mu _ (bas q.1 q.2), PowerSeries.X ^ ((m q : ℤ) + expo a j (rep q.1) mu).toNat,
        fun Z _ _ p κ jf j₀ hp hi => ?_⟩
      rw [((hf q).1 mu).2]
      exact ConstThetaSections.valR_smul_pullB hW j _ _ _ Z p κ jf j₀ hp hi
    · refine ⟨(0 : SecBMod a.D₀ j x), 0, fun Z _ _ p κ jf j₀ hp hi => ?_⟩
      rw [(hf q).2 _ h, ← zero_smul ℂ⟦X⟧ (pullB hW j x 0)]
      exact ConstThetaSections.valR_smul_pullB hW j _ _ _ Z p κ jf j₀ hp hi
  · let v := valLin W.t.G.hom
      (LB.LinComb W.P.U.LG.L (K := Fin 1) (fun _ => 𝟙 W.t.G.left) (fun _ => (j : ℤ))) κ p hp (fun _ => k)
      (FormalValue.top_le_secChart hk)
    refine (congrArg (· * _) (map_pow κ _ N).symm).trans ((v.map_smulₛₗ _ σ).symm.trans
      ((congrArg v ht.symm).trans ((map_sum v _ _).trans (Finset.sum_congr rfl fun i _ => v.map_smulₛₗ _ _))))

end GlobalTheory.ConstExpSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSectionValuesFormalThetaSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.ConstThetaSections

open ConstFam FormalValue

theorem exists_vals_fsum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) [NeZero j] (α : Λ.A.X), ∀ th ∈ Λ.A.Theta j α, ∃ (m : ℕ) (σ : Out.H0 W.P.U.LG.L j), Ξ.Vals σ (fun v => HahnSeries.single (m : ℤ) (1 : ℂ) * Λ.A.FSum j α th v) := by
  intro hL hL₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ j _ α th hth
  have hj : 1 ≤ j := NeZero.one_le
  obtain ⟨s₀, hs₀, -⟩ := ((ArcThetaSpaces.sections_theta hL hL₂ E H D l c O β b a Λ).1 j α hj).2 th hth
  have hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e := ⟨W.spec.1, W.spec.2.1, W.spec.2.2.1, W.spec.2.2.2.1,
    W.spec.2.2.2.2.1, fun F _ _ _ _ uF h₁ h₂ => (W.spec.2.2.2.2.2 F uF h₁ h₂).1⟩
  obtain ⟨m, hm⟩ := exists_expandsAt hW hL.globalFns hj W.P.U (Λ.ε α) s₀
  obtain ⟨f, σ, hf, hE⟩ := hm m le_rfl
  have ex : ∀ mu, expo a j (Λ.ε α) (Λ.ε mu) = Λ.A.exponent j α mu := fun mu => by
    rw [expo, AnArc.exponent, AnArc.q, Λ.be_eq, Λ.be_eq]
  have hpos : ∀ mu, 0 ≤ (m : ℤ) + Λ.A.exponent j α mu := fun mu => ex mu ▸ (hf.1 (Λ.ε mu)).1
  have comp : ∀ mu, ∃ t : SecBMod a.D₀ j (Λ.ε (α + j • mu)), f (W.e (Λ.ε (α + j • mu))) =
      (PowerSeries.X : ℂ⟦X⟧) ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat • pullB hW j _ t ∧
      ∀ z, Λ.fn j (α + j • mu) t z = Λ.A.psi mu ^ j * eTwoPi (Λ.A.T mu α) * th (z + Λ.A.ct mu) := fun mu => by
    have cast : ∀ x, Λ.ε α + j • Λ.ε mu = x → ∃ t : SecBMod a.D₀ j x, f (W.e x) =
        (PowerSeries.X : ℂ⟦X⟧) ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat • pullB hW j _ t ∧
        ∀ z, FrameValue.secVal Λ.u a.D₀.P.isLB t (Λ.u.ex z).left
          ![z, z + (Λ.A.ct α + j • Λ.A.ct mu), Λ.A.ct α + j • Λ.A.ct mu, 0] =
            Λ.A.psi mu ^ j * eTwoPi (Λ.A.T mu α) * th (z + Λ.A.ct mu) := by
      rintro _ rfl
      refine ⟨_, ex mu ▸ (hf.1 (Λ.ε mu)).2, fun z => ?_⟩
      have es := Λ.psi (mu + α)
      rw [map_add Λ.ε, map_add Λ.A.ct] at es
      refine (secVal_feTranslate Λ.ah Λ.rig j (Λ.ct α) (Λ.ct mu) (Λ.psi α) (Λ.psi mu) es s₀ z).trans ?_
      refine (congrArg (· * _) (congrFun hs₀ (z + Λ.A.ct mu))).trans ?_
      have := (Λ.A.psi mu).ne_zero
      have := (Λ.A.psi α).ne_zero
      push_cast
      rw [Λ.A.psi_add]
      field_simp
    obtain ⟨t, h₁, h₂⟩ := cast (Λ.ε (α + j • mu)) (by rw [map_add (f := _), map_nsmul])
    refine ⟨t, h₁, fun z => Eq.trans ?_ (h₂ z)⟩
    exact congrArg (fun q => FrameValue.secVal Λ.u a.D₀.P.isLB t (Λ.u.ex z).left ![z, z + q, q, 0])
      ((map_add Λ.A.ct _ _).trans (congrArg _ (map_nsmul Λ.A.ct _ _)))
  refine ⟨m, σ, fun v jL hjL => ?_⟩
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB (basePt (Ξ.g v) (cpt ℂ⟦X⟧))
  obtain ⟨j₀, h₀⟩ := exists_chart a.D₀.P.isLB (W.φ (basePt (Ξ.g v) (cpt ℂ⟦X⟧)))
  have hM' := (top_le_iff_cpt _ _).2 hM
  have hw : ⊤ ≤ (Ξ.g v).b.left ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) :=
    (top_le_iff_cpt (A := ℂ⟦X⟧) _ _).2 ⟨mem_pull.2 h₀, hM⟩
  choose jf jt hc using exists_cohCharts (Ξ.g v) jM hM'
  obtain ⟨w, hw'⟩ := isUnit_valR (A := ℂ⟦X⟧) _ _ hw (W.w.s (fun _ => j₀, jM))
  have hτ := Ξ.τ_eq v jL jM j₀ hjL hw
  have hI : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} :=
    Ideal.map_id _
  have hx := Ξ.x_fm v
  rw [hI, ← hw'] at hτ
  rw [hI] at hx
  let i : Λ.A.X → W.P.D.toPre.X := fun mu => W.e (Λ.ε (α + j • mu))
  have hi : Function.Injective i := fun mu mu' h =>
    smul_right_injective Λ.A.X (Int.natCast_ne_zero.2 (NeZero.ne j)) ((natCast_zsmul mu j).trans
      ((add_left_cancel (Λ.ε.injective (W.e.injective h))).trans (natCast_zsmul mu' j).symm))
  let h : W.P.D.toPre.X → ℂ⟦X⟧ := fun x => w.val ^ j * (famVal (Ξ.g v) (f x) (jf x) * coordVal (Ξ.g v) x (jt x))
  have h₁ : ∀ mu, h (i mu) = PowerSeries.X ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat *
      PowerSeries.C (Λ.A.term j α th mu v * Λ.u.fr j₀ v.2 ^ j) := fun mu => by
    obtain ⟨t, e₁, e₂⟩ := comp mu
    have := GlobalTheory.ConstTerm.main hL hL₂ E H D l Xo c O β Y b a χ W Λ Ξ j (α + j • mu) t (f (i mu)) _
      (fun Z _ _ p κ jf j₀ hp hi => by
        rw [show f (i mu) = _ from e₁]
        exact valR_smul_pullB hW j _ t _ Z p κ jf j₀ hp hi) v jM j₀ _ _ (hc (i mu)) hw
    rw [← hw', e₂] at this
    refine this.trans (congrArg _ (congrArg _ ?_))
    rw [AnArc.term]; ring
  have h₂ : ∀ x, (∀ mu, i mu ≠ x) → h x = 0 := fun x hx => by
    have e₁ : f x = 0 := hf.2 x fun y e => hx (Λ.ε.symm (W.e.symm y)) (by
      rw [← e]
      show W.e (Λ.ε _) = _
      rw [map_add (f := _), map_add (f := _), map_nsmul, map_nsmul, Λ.ε.apply_symm_apply, W.e.apply_symm_apply])
    have e₂ : famVal (Ξ.g v) (f x) (jf x) = 0 := by
      rw [e₁]
      exact (dif_pos (hc x).1).trans ((congrArg _ (map_zero _)).trans (map_zero _))
    show _ * (_ * _) = _
    rw [e₂, zero_mul, mul_zero]
  beta_reduce
  rw [← algebraMap_mk_eq Λ.A j α th v hpos, ← map_pow, ← map_mul]
  refine congrArg _ ((Units.mul_right_inj (w ^ j)).1 (eq_of_forall_mk_eq (Ideal.span {PowerSeries.X}) fun e => ?_))
  have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)})) e
  obtain ⟨F, hF⟩ := map_secVal_eq W.P.U.toUnifPre (hE e)
  obtain ⟨F', hF', hd⟩ := exists_sum_sub_mem hi h₁ h₂ (L := fun k => Λ.A.level j α ((k : ℤ) - m)) (fun k mu => by
    have := hpos mu
    rw [Λ.A.mem_level]
    omega) (e + 1) F
  have H := (hF _ _ _ _ _ hx _ (Ideal.Quotient.mk (Ideal.span {PowerSeries.X} ^ (e + 1))) Ideal.mk_ker.ge).2
    F' jL jM jf jt hF' hjL hM' fun x _ => hc x
  rw [map_mul, H, ← map_mul, Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have e₁ : (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v * Λ.u.fr j₀ v.2 ^ j) =
      (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v) *
        PowerSeries.C (Λ.u.fr j₀ v.2) ^ j := by
    ext k
    rw [← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_mk, Finset.sum_mul]
  rw [e₁, show ∑ x ∈ F', h x = w.val ^ j * ∑ x ∈ F', famVal (Ξ.g v) (f x) (jf x) * coordVal (Ξ.g v) x (jt x) from
    (Finset.mul_sum _ _ _).symm] at hd
  refine (congrArg (_ ∣ ·) ?_).mp (hd.mul_left ((tau W.P.U.toUnifPre (Ideal.span {PowerSeries.X}) (Ξ.x v).left jL jM).val ^ j))
  rw [Units.val_pow_eq_pow_val]
  have := congrArg (· ^ j) hτ
  simp only [mul_pow] at this
  linear_combination (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v) * this

end GlobalTheory.ConstThetaSections
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOf
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.ThetaOfArc

open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam GlobalTheory.IndivisibleSection GlobalTheory.ThetaUnit IsLocalRing

section General

variable {X : Scheme.{0}} {L : LB X}

theorem sectionOfLineBundleOne_iff_germs_eq {σ : H0 L 1} {θ : L.Sec} : SectionOfLineBundleOne σ θ ↔ ∀ (y : X) (k : L.ι), y ∈ L.U k →
    gs (𝟙 X) y (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k)) (σ.f fun _ => k) = gs (𝟙 X) y (L.U k) (θ.f k) := by
  refine ⟨fun h y k hy => ?_, fun h j hj => ?_⟩
  · rw [h (fun _ => k) (fun z hz => Set.mem_iInter.1 hz 0)]
    exact gs_res (𝟙 X) y _ (mem_chart_one (𝟙 X) y hy) _
  · obtain ⟨k, rfl⟩ : ∃ k', j = fun _ => k' := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
    exact fn_ext fun y hy => (h y k (hj hy)).trans (gs_res (𝟙 X) y hj hy _).symm

theorem exists_h0Sec_left (θ : L.Sec) : ∃ σ : H0 L 1, SectionOfLineBundleOne σ θ := by
  obtain ⟨t, ht⟩ := exists_powerSection_of_chartFunctions θ
  exact ⟨t, sectionOfLineBundleOne_iff_germs_eq.2 fun y k hy => ht _ (𝟙 X) y k hy⟩

theorem exists_h0Sec_right (σ : H0 L 1) : ∃ θ : L.Sec, SectionOfLineBundleOne σ θ := by
  have le : ∀ k : L.ι, L.U k ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) :=
    fun k y hy => mem_chart_one (𝟙 X) y hy
  refine ⟨⟨fun k => resG X (le k) (σ.f fun _ => k), fun i j => fn_ext fun y hy => ?_⟩,
    sectionOfLineBundleOne_iff_germs_eq.2 fun y k hy => (gs_res (𝟙 X) y (le k) hy _).symm⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.1 _)).trans
    ((gs_compat σ (𝟙 X) y (le i hy.1) (le j hy.2)).trans (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (Eq.symm ?_)))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.2 _))))))
  refine (gm_linComb L _ _ (𝟙 X) y _ _ (le i hy.1) (le j hy.2)).trans ?_
  simp

def Same {L' : LB X} (σ : H0 L 1) (θ : L'.Sec) : Prop := ∃ θ' : L.Sec, SectionOfLineBundleOne σ θ' ∧ HEq θ θ'

variable {L' : LB X}

theorem exists_same_left (h : L = L') (θ : L'.Sec) : ∃ σ : H0 L 1, Same σ θ := by
  subst h
  obtain ⟨σ, hσ⟩ := exists_h0Sec_left θ
  exact ⟨σ, θ, hσ, HEq.rfl⟩

theorem exists_same_right (h : L = L') (σ : H0 L 1) : ∃ θ : L'.Sec, Same σ θ := by
  subst h
  obtain ⟨θ, hθ⟩ := exists_h0Sec_right σ
  exact ⟨θ, θ, hθ, HEq.rfl⟩

theorem Same.unique (h : L = L') {σ : H0 L 1} {θ₁ θ₂ : L'.Sec} (h₁ : Same σ θ₁) (h₂ : Same σ θ₂) : θ₁ = θ₂ := by
  subst h
  obtain ⟨_, a₁, ⟨⟩⟩ := h₁
  obtain ⟨_, a₂, ⟨⟩⟩ := h₂
  have e : θ₁.f = θ₂.f := funext fun k => fn_ext fun y hy =>
    (sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hy).symm.trans (sectionOfLineBundleOne_iff_germs_eq.1 a₂ y k hy)
  cases θ₁
  cases θ₂
  cases e
  rfl

theorem Same.mul_iff (h : L = L') {R : Type} [CommRing R] (p : X ⟶ Sp R) (r : R) {σ σ' : H0 L 1} {θ θ' : L'.Sec}
    (h₁ : Same σ θ) (h₂ : Same σ' θ') : SecIsMul p r σ' σ ↔ ∀ i, θ'.f i = constFn p _ r * θ.f i := by
  subst h
  obtain ⟨_, a₁, ⟨⟩⟩ := h₁
  obtain ⟨_, a₂, ⟨⟩⟩ := h₂
  refine ⟨fun hm k => fn_ext fun y hy => ?_, fun hm j => ?_⟩
  · refine (sectionOfLineBundleOne_iff_germs_eq.1 a₂ y k hy).symm.trans
      ((secIsMul_gs hm (𝟙 X) y (fun _ => k) (mem_chart_one (𝟙 X) y hy)).trans (Eq.symm ?_))
    exact (gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_constFn p _ (𝟙 X) y hy r) (sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hy).symm)
  · obtain ⟨k, rfl⟩ : ∃ k', j = fun _ => k' := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
    rw [ThickDiv.resTop_scal]
    refine fn_ext fun y hy => ?_
    have hk : y ∈ L.U k := Set.mem_iInter.1 hy 0
    refine (sectionOfLineBundleOne_iff_germs_eq.1 a₂ y k hk).trans ((congrArg _ (hm k)).trans ((gs_mul (𝟙 X) y _ hk _ _).trans
      (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·) ?_ (sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hk))))))
    exact (gs_constFn p _ (𝟙 X) y hy r).trans (gs_constFn p _ (𝟙 X) y hk r).symm

theorem Same.mem_nonzeroLocus (h : L = L') {σ : H0 L 1} {θ : L'.Sec} (h₁ : Same σ θ) {y : X}
    (hy : y ∈ nonzeroLocus σ) : y ∈ nonzeroLocus θ := by
  subst h
  obtain ⟨_, a₁, ⟨⟩⟩ := h₁
  obtain ⟨j, hj, hu⟩ := (SectionBaseChange.mem_nonzeroLocus σ _).1 hy
  obtain ⟨k, rfl⟩ : ∃ k', j = fun _ => k' := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  have hk : y ∈ L.U k := Set.mem_iInter.1 hj 0
  exact (SectionBaseChange.mem_nonzeroLocus θ _).2 ⟨k, hk, sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hk ▸ hu⟩

end General

theorem isPullTerm_mul {R A : Type} [CommRing R] [IsDomain R] [CommRing A] {D : DegPre R} {B₀ : Scheme.{0}}
    {M₀ : LB B₀} {φ : D.P.A.left ⟶ B₀} {w : LB.Iso D.P.L (M₀.pull φ)} {th th' : M₀.Sec} (q : B₀ ⟶ Sp A)
    (f : A →+* R) (hq : φ ≫ q = D.P.A.hom ≫ spMap f) (r : A) (hm : ∀ j, th'.f j = constFn q _ r * th.f j)
    {t t' : D.SecB 1 0} (h : IsPullTerm D φ w th t) (ht : SecIsMul D.P.A.hom (f r) t' t) :
    IsPullTerm D φ w th' t' := by
  refine isPullTerm_iff.2 fun y J j₀ hJ hy => ?_
  rw [hm, gs_mul φ y _ hy, gs_constFn q _ φ y hy, isPullTerm_iff.1 h y J j₀ hJ hy, sval_of_secIsMul ht _ y hJ, hq,
    cst_comp, Category.id_comp, mul_left_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X}

theorem thetaOf_iff (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (θ : LB.Sec W.t.PP.L) : ThetaOf W th θ ↔
    ∃ (σ : H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x), (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 σ fam) ∧
      IsPullTerm W.P.D.toPre W.φ W.w th (fam 0) ∧ Same σ θ :=
  ⟨fun ⟨σ, fam, θ', h₁, h₂, h₃⟩ => ⟨σ, fam, h₁, h₂, θ', h₃⟩, fun ⟨σ, fam, h₁, h₂, θ', h₃⟩ => ⟨σ, fam, θ', h₁, h₂, h₃⟩⟩

theorem secIsMul_of_weight_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {P : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D P G)
    (σ σ' : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))))
    (f f' : ∀ α, SecBMod D.toPre 1 α) (hE : ∀ e, U.ExpandsAt e 1 σ f) (hE' : ∀ e, U.ExpandsAt e 1 σ' f')
    (hu : ∀ (σ₁ : H0 U.LG.L 1) (f₁ : ∀ α, D.toPre.SecB 1 α), f₁ 0 = f 0 → (∀ e, U.ExpandsAt e 1 σ₁ f₁) → σ₁ = σ)
    (r : R) (h : SecIsMul D.toPre.P.A.hom r (f' 0) (f 0)) : SecIsMul G.hom r σ' σ := by
  have h₀ : f' 0 = r • f 0 := (secIsMul_iff _ _ _ _).1 h
  have h₁ : (f' + (1 - r) • f) 0 = f 0 := by
    rw [Pi.add_apply, Pi.smul_apply, h₀, ← add_smul, add_sub_cancel, one_smul]
  have h₂ : σ' + (1 - r) • σ = σ :=
    hu _ _ h₁ fun e => expandsAt_add U (hE' e) (expandsAt_smul U (1 - r) (hE e))
  refine (secIsMul_iff _ _ _ _).2 ?_
  rw [sub_smul, one_smul] at h₂
  rw [← sub_eq_zero, ← add_left_inj σ, zero_add]
  refine Eq.trans ?_ h₂
  abel

end GlobalTheory.ThetaOfArc

namespace GlobalTheory

open GlobalTheory.ThetaUnit GlobalTheory.ThetaOfArc IsLocalRing

theorem existsUnique_thetaOf : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec), ThNZ th → (∃! θ : LB.Sec W.t.PP.L, ThetaOf W th θ) ∧ ∀ θ, ThetaOf W th θ → (∀ s : LB.Sec W.t.PP.L, ∃! r : PowerSeries A, ∀ i, s.f i = constFn W.t.G.hom _ r * θ.f i) ∧ (∃ g : W.t.G.left, W.t.G.hom g = IsLocalRing.closedPoint (PowerSeries A) ∧ g ∈ Out.nonzeroLocus θ) ∧ ∀ (r : A) (th' : a.D₀.P.L.Sec) (θ' : LB.Sec W.t.PP.L), ThMul r th th' → (ThetaOf W th' θ' ↔ ∀ i, θ'.f i = constFn W.t.G.hom _ (PowerSeries.C (R := A) r) * θ.f i) := by
  intro hL _ E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W th hth
  have hI : Ideal.span {(PowerSeries.X : PowerSeries A)} ≤ maximalIdeal (PowerSeries A) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have hb : W.P.U.LG.L = W.t.PP.L := congrArg (fun q => q.L) W.P.bundle
  obtain ⟨⟨t, ht, htu⟩, hnz⟩ := existsUnique_pullTerm W th
  have ht₀ := hnz t ht hth (closedPoint _)
  obtain ⟨σ, fam, rfl, hE, hmem, huq, hgen, -⟩ := exists_theta_arc hL.globalFns hL.secBaseChange hI W t ht₀
  have key : ∀ θ, ThetaOf W th θ ↔ Same σ θ := fun θ => by
    rw [thetaOf_iff]
    refine ⟨fun ⟨σ₁, f₁, h₁, h₂, h₃⟩ => huq σ₁ f₁ (htu _ h₂) h₁ ▸ h₃, fun h => ⟨σ, fam, hE, ht, h⟩⟩
  refine ⟨?_, fun θ hθ => ⟨fun s => ?_, ?_, fun r th' θ' hm => ?_⟩⟩
  · obtain ⟨θ, hθ⟩ := exists_same_right hb σ
    exact ⟨θ, (key θ).2 hθ, fun θ' h => ((key θ').1 h).unique hb hθ⟩
  · obtain ⟨s', hs'⟩ := exists_same_left hb s
    simpa only [((key θ).1 hθ).mul_iff hb W.t.G.hom _ hs'] using hgen s'
  · obtain ⟨g, hg, hn⟩ := exists_mem_nonzeroLocus hI W.P.U.toUnifPre (hE 0) ht₀ hmem
    exact ⟨g, hg, ((key θ).1 hθ).mem_nonzeroLocus hb hn⟩
  · choose fam' hfam' using fun α =>
      IntegralExpansion.exists_secIsMul W.P.D.toPre.P.A.hom (PowerSeries.C (R := A) r) (fam α)
    have hp : IsPullTerm W.P.D.toPre W.φ W.w th' (fam' 0) :=
      isPullTerm_mul a.D₀.P.A.hom _ W.spec.1.1.w r hm ht (hfam' 0)
    rw [thetaOf_iff]
    refine ⟨fun ⟨σ₁, f₁, h₁, h₂, h₃⟩ => (((key θ).1 hθ).mul_iff hb W.t.G.hom _ h₃).1 ?_, fun h => ?_⟩
    · exact secIsMul_of_weight_zero W.P.U.toUnifPre σ σ₁ fam f₁ hE h₁ huq _
        (h₂.unique a.D₀.P.isLB hp ▸ hfam' 0)
    · obtain ⟨σ', hσ'⟩ := exists_same_left hb θ'
      exact ⟨σ', fam', fun n => expandsAt_secIsMul _ _ _ _ _ _ n 1 _ σ σ' fam fam'
        ((((key θ).1 hθ).mul_iff hb W.t.G.hom _ hσ').2 h) hfam' (hE n), hp, hσ'⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FirstOrderJetConstSectionMulCoordinate
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanJet

open FrameValue

theorem jet_comp_equiv {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    (e : V' ≃L[ℂ] V) (F : V → ℂ) (z : V') : jet (fun w => F (e w)) z = jet F (e z) := by
  have h := e.comp_right_fderiv (f := F) (x := 0)
  rw [map_zero] at h
  ext
  · simp
  · rw [snd_jet, snd_jet]
    exact congrArg (fun q : V' →L[ℂ] ℂ => q z) h

theorem valR_eq_jet {g : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {z : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hd : IsDerivAt0 e z v) (U : X.Opens) (hU : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR v U f = jet (fun w => valAt' (e w) U f) z := by
  ext
  · rw [fst_jet, ← hd.1]
    exact (FormalValue.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom v U hU f).symm
  · rw [snd_jet, ← hd.2 U hU f, valR, dite_eq_left hU]

theorem frameProd_mul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {n : ℕ} (u : HolUnif A L n) (j : ℕ)
    (c z : Fin n → ℂ) (k : Fin 4 → L.ι) (hk : ∀ i, ⊤ ≤ (u.ex (![c + z, c, z, 0] i)).left ⁻¹ᵁ L.U (k i)) :
    GlobalTheory.FrameValue.frameProd u (Out.DegPre.famε j) ![z, z + c, c, 0] ![k 2, k 0, k 1, k 3] *
      GlobalTheory.FrameValue.frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k = u.fr (k 2) z ^ j := by
  have n₀ : u.fr (k 0) (c + z) ≠ 0 := u.fr_ne _ _ (hk 0)
  have n₁ : u.fr (k 1) c ≠ 0 := u.fr_ne _ _ (hk 1)
  have n₂ : u.fr (k 2) z ≠ 0 := u.fr_ne _ _ (hk 2)
  have n₃ : u.fr (k 3) 0 ≠ 0 := u.fr_ne _ _ (hk 3)
  simp only [GlobalTheory.FrameValue.frameProd, Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub₀ n₂,
    zpow_neg, zpow_one, zpow_natCast, add_comm z c]
  field_simp

theorem jet_sec_mul_coord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (j : ℕ) (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (jt₀ : Fin 4 → a.D₀.P.L.ι), IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (h.symm z)).b.left)) z₀ ν.b.left → (∀ x j, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (Λ.ex0 (h.symm 0)) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (Λ.ex0 (h.symm z)) x j) 0 z₀)) → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀ → valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀) ((ν.s (Λ.ε α)).s jt₀).val = jet (fun v : Λ.A.V => Λ.fn j α s₀ v.2 * eTwoPi (v.1 α)) (h.symm z₀) * jet (fun v : Λ.A.V => Λ.u.fr (jt₀ 2) v.2) (h.symm z₀) ^ j := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ g h z₀ ν j α s₀ jt hd hs hj
  have hU : ⊤ ≤ (show Sp (DualNumber ℂ) ⟶ _ from ν.b.left) ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] := by
    intro y hy
    refine Set.mem_iInter.2 fun i => ?_
    have h₁ := Set.mem_iInter.1 (hj hy) (![2, 0, 1, 3] i)
    have h₂ : (![jt 2, jt 0, jt 1, jt 3] : Fin 4 → _) i = jt (![2, 0, 1, 3] i) := by fin_cases i <;> rfl
    rw [h₂]
    exact (congrArg (fun q => q y ∈ a.D₀.P.L.U (jt (![2, 0, 1, 3] i)))
      (ConstTerm.comp_famφB a.D₀ ν.b (Λ.ε α) i)).mpr h₁
  have h0 : ⊤ ≤ (Λ.u.ex (0 : Λ.A.V).2).left ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] := by
    have h₁ := FormalValue.top_le_comp hU (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    have h₂ := hd.1.trans (Λ.ex0_b (h.symm 0))
    rw [map_zero] at h₂
    exact h₂ ▸ h₁
  obtain ⟨ho, hh⟩ := Λ.u.hol _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])
  have hn : ∀ᶠ v : Λ.A.V in nhds 0, ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] :=
    (ho.preimage continuous_snd).mem_nhds h0
  have lf := ConstTerm.isLift_famφB Λ.u (Λ.ct α)
  have hk : ∀ z, ⊤ ≤ (Λ.u.ex z).left ⁻¹ᵁ LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] →
      ∀ i, ⊤ ≤ (Λ.u.ex (![Λ.A.ct α + z, Λ.A.ct α, z, 0] i)).left ⁻¹ᵁ a.D₀.P.L.U (jt i) := fun z hz i => by
    have h₁ := ((lf z).le_iff _).1 hz
    fin_cases i
    exacts [add_comm z (Λ.A.ct α) ▸ h₁ 1, h₁ 2, h₁ 0, h₁ 3]
  have hg : ∀ᶠ v : Λ.A.V in nhds 0, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 v).b (Λ.ε α)) jt :=
    hn.mono fun v hv => ((gtHol_isLift a.D₀ Λ.u _ _ _ _ (Λ.ct α) (Λ.ex0_b v)).le_iff jt).2 (hk _ hv)
  obtain ⟨hc₁, hc₂⟩ := (analyticDictionaryExp_holomorphic_over_unif E H D l c O β b a Λ).2 (Λ.ε α) jt
  simp only [LinearEquiv.symm_apply_apply] at hc₂
  have dF : DifferentiableAt ℂ (fun v : Λ.A.V => valAt' (Λ.u.ex v.2).left _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])) 0 :=
    (hh.differentiableAt (ho.mem_nhds h0)).comp (0 : Λ.A.V) differentiableAt_snd
  have dG : DifferentiableAt ℂ (fun v : Λ.A.V => chiVal (Λ.ex0 v) (Λ.ε α) jt) 0 := hc₁.differentiableAt hg
  have dfn : Differentiable ℂ (Λ.fn j α s₀) := by
    have := differentiable_secVal a.D₀.P.isLB s₀ (𝟙 _) (q := id) differentiable_id
      (z := fun z => ![z, z + Λ.A.ct α, Λ.A.ct α, 0])
      (fun k => by fin_cases k <;> simp <;> fun_prop) (fun w => by rw [id, Category.comp_id]; exact lf w)
    simp only [id, Category.comp_id] at this
    exact this
  have dP : DifferentiableAt ℂ (fun v : Λ.A.V => Λ.fn j α s₀ v.2 * eTwoPi (v.1 α)) 0 := by
    have : Differentiable ℂ (fun z : Λ.A.V => z.1 α) := (Λ.A.evalCLM α).differentiable.comp differentiable_fst
    exact ((dfn.comp differentiable_snd).fun_mul (this.const_mul _).cexp) 0
  have dQ : DifferentiableAt ℂ (fun v : Λ.A.V => Λ.u.fr (jt 2) v.2) 0 :=
    ((Λ.u.fr_hol (jt 2)).differentiableAt ((Λ.u.hol _ 0).1.mem_nhds (hk _ h0 2))).comp (0 : Λ.A.V)
      differentiableAt_snd
  have e₁ := valR_eq_jet hd _ hU (s₀.f ![jt 2, jt 0, jt 1, jt 3])
  simp only [Λ.ex0_b] at e₁
  replace e₁ := e₁.trans (jet_comp_equiv h.symm
    (fun v : Λ.A.V => valAt' (Λ.u.ex v.2).left _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])) z₀)
  have e₂ := (hs (Λ.ε α) jt hj).trans (jet_comp_equiv h.symm (fun v : Λ.A.V => chiVal (Λ.ex0 v) (Λ.ε α) jt) z₀)
  refine (congrArg₂ (· * ·) e₁ e₂).trans ?_
  rw [← jet_mul dF dG, ← jet_pow dQ, ← jet_mul dP (dQ.fun_pow j)]
  refine jet_congr ?_ _
  filter_upwards [hn, hg] with v hv hv'
  refine (congrArg₂ (· * ·) (valAt'_sec a.D₀.P.isLB s₀ (lf v.2) hv) (hc₂ v hv')).trans ?_
  rw [← frameProd_mul Λ.u j (Λ.A.ct α) v.2 jt (hk _ hv), _root_.mul_mul_mul_comm]
  rfl

end GlobalTheory.ConstTanJet
end
end

