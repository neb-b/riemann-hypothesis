module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ChartCoordinatesHasSum
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArchBoundFlow
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

theorem nfac_of_add {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la l₁ l₂ : Wt X.Ψ r) (h : ∀ τ i, la τ i = l₁ τ i + l₂ τ i) :
    X.nfac la x = X.nfac l₁ x * X.nfac l₂ x := by
  simp only [Data.nfac, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_add (norm_pos_iff.mpr
    (div_ne_zero (FlowCoefficientBounds.dmin_ne X hx τ _) (FlowCoefficientBounds.dmin_ne X hx τ _))), h]
  congr 1
  push_cast
  ring

theorem arch_bound_flow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : (U.X k).dom) (C ep xi : ℝ) (κ : ℂ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → 0 < C → 0 < ep → Even n → (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xi) → ‖κ‖ = (C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x.1 → ∃ hx : (U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1 ∈ (U.X k).dom, (∀ τ, (U.X k).tt ξ' ((U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1) τ = ep) ∧ (∀ (P : Frame (U.X k).Ψ r → ℂ) (ν : (U.X k).Ψ → ℝ), (U.X k).IsBddSec (laU U a' n k) P → ‖(U.X k).fj (laU U a' n k) ξ' ν P x.1‖ = Real.exp (4 * Real.pi * ∑ τ, ν τ * (ep - (U.X k).tt ξ' x.1 τ)) * ‖(U.X k).fj (laU U a' n k) ξ' ν P ((U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1)‖) ∧ ∀ Hm, IsRiem Uw.F (Uw.ik k) (Uw.Pm k ⟨_, hx⟩) Hm → ‖κ‖ / (lieFac Dw xi a' * (U.X k).nfac (laU U a' n k) ((U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1)) ≤ (C * (ep⁻¹) ^ (U.X k).Ψ.card) ^ ((n : ℝ) / 2) * ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), (Real.pi * (Hm (Uw.e.symm ⟨τ, i⟩) (Uw.e.symm ⟨τ, i⟩)).re) ^ ((a' (τ, (i : ℕ)) : ℝ) / 2) := by
  intro E _ _ _ H Dw l Xo c σ r U Uw k ξ' x C ep xi κ a' n hσ hU hξ hC hep hn hxi hκ
  have him : ∀ τ, (U.X k).tt ξ' x.1 τ +
      ((((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I)).im = ep := by
    intro τ; simp
  have hd := GlobalTheory.FjCauchy.flow_mem_dom (U.X k) hξ x.2
    (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) (fun τ => by rw [him]; exact hep)
  have ht : ∀ τ, (U.X k).tt ξ' ((U.X k).flow ξ'
      (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1) τ = ep := fun τ => by
    rw [GlobalTheory.FjCauchy.tt_flow (U.X k) hξ x.2 _ hd, him]
  refine ⟨hd, ht, ?_, ?_⟩
  · intro P ν hP
    rw [GlobalTheory.FjCauchy.fj_flow (U.X k) hP hξ ν x.2 _ hd, norm_mul, ← mul_assoc, Complex.norm_exp,
      ← Real.exp_add]
    have hs : ∑ τ, (ν τ : ℂ) * (((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) =
        ((∑ τ, ν τ * (ep - (U.X k).tt ξ' x.1 τ) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Complex.ofReal_mul, mul_assoc]
    rw [hs]
    generalize (∑ τ, ν τ * (ep - (U.X k).tt ξ' x.1 τ) : ℝ) = S
    have : (4 * (Real.pi : ℂ) * Complex.I * ((S : ℂ) * Complex.I)).re = -(4 * Real.pi * S) := by
      simp
    rw [this, add_neg_cancel, Real.exp_zero, one_mul]
  · intro Hm hH
    have hb := (_root_.GlobalTheory.RiemMaj.riemann_eq_majorant E H Dw l Xo c σ r U Uw k ⟨_, hd⟩ Hm hσ hU hH).2.2 xi a' hxi
    have hf := nfac_parallel_flow E H Dw l Xo c σ r U k n ξ' hn hξ x.1 x.2 _ hd
    have hadd := nfac_of_add (U.X k) hd (laU U a' n k) (laU U a' 0 k) (laU U 0 n k) (by
      intro τ j
      simp only [laU]
      split_ifs <;> simp <;> ring)
    have hN := FlowCoefficientBounds.nfac_pos (U.X k) hd (laU U 0 n k)
    have hA := FlowCoefficientBounds.nfac_pos (U.X k) hd (laU U a' 0 k)
    have hL := lieFac_pos Dw xi a'
    simp only [ht, Finset.prod_const, Finset.card_univ, Fintype.card_coe] at hf
    have hp : 0 ≤ ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹ :=
      Finset.prod_nonneg fun τ _ => (inv_pos.mpr (GlobalTheory.FjCauchy.tt_pos (U.X k) hξ x.2 τ)).le
    have he : 0 ≤ (ep⁻¹) ^ (U.X k).Ψ.card := by positivity
    rw [hκ, hadd, Real.mul_rpow hC.le hp, mul_assoc, mul_comm _ ((U.X k).nfac (laU U 0 n k) x.1), ← hf,
      Real.mul_rpow hC.le he]
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hb (by positivity))
    dsimp only
    generalize (U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1 = y at hN hA ⊢
    field_simp

end GlobalTheory.ArcQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CardQkOfTateIsoQ
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.ArcPts
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem card_qk_pre (hL : Out.Laws) (hL2 : Out.Laws2) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (D₀ : Out.DegPre R) (hB : D₀.TauBimult) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
    (k : ℕ) (hk : (k : F) ≠ 0) :
    Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) = k ^ (2 * (D₀.rank + D₀.P.g)) := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  have h₁ := (GlobalTheory.GtCount.card_gtTors hL hL2 R D₀ F k hk).1
  simp only [GlobalTheory.GtCount.gtTors_iff] at h₁
  open ReciprocityTheory.ChartRestriction.G.Out in
  have hc : Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) =
      k ^ D₀.rank * Nat.card {g : GtPtF D₀ F // k • g = 0} := by
    open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR in
      let iota : D₀.X →+ GtPtF D₀ F := AddMonoidHom.mk' (fun x => (exists_iota (F := F) hB x).choose) fun x x' => by
        obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x).choose_spec
        obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x').choose_spec
        obtain ⟨b'', v''⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB (x + x')).choose_spec
        refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
        have C : IsCub (th D₀ (T := TF (R := R) F) y J) := isCub_cubV D₀.cub hJ
        rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
        exact tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
      have hi (x : D₀.X) : GtPtF.IsIota x (iota x) := (exists_iota (F := F) hB x).choose_spec
      have he (x : D₀.X) (g : GtPtF D₀ F) : GtPtF.IsIota x g ↔ g = iota x :=
        ⟨fun h => isIota_unique h (hi x), fun h => h ▸ hi x⟩
      let qkMk (y : D₀.X) (g : GtPtF D₀ F) (h : k • g = iota y) : QkPt D₀ F k :=
        ⟨y, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, (he _ _).2 h⟩
      have qk_nsmul (p : QkPt D₀ F k) : k • p.g = iota p.y := by
        obtain ⟨h, h₁, h₂⟩ := p.eq
        exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((he _ _).1 h₂)
      have equiv_iff (p p' : QkPt D₀ F k) : QkPt.Equiv D₀ F p p' ↔ ∃ z : D₀.X, p'.y = p.y + k • z ∧ p'.g = p.g + iota z :=
        exists_congr fun z => and_congr Iff.rfl
          ⟨fun ⟨_, h₁, h₂⟩ => ((isAdd_iff_eq _ _ _).1 h₂).trans (congrArg (p.g + ·) ((he _ _).1 h₁)),
           fun h => ⟨_, hi z, (isAdd_iff_eq _ _ _).2 h⟩⟩
      have hd : ∀ y : D₀.X, ∃ g : GtPtF D₀ F, k • g = iota y :=
        fun y => exists_nsmul_eq hL.mulN (Or.inl inferInstance) hk0 _
      choose r hr using hd
      let K : AddSubgroup D₀.X := (nsmulAddMonoidHom k : D₀.X →+ D₀.X).range
      have hK : Nat.card (D₀.X ⧸ K) = k ^ D₀.rank := AddSubgroup.index_range_nsmul D₀.X k
      let f : (D₀.X ⧸ K) × {g : GtPtF D₀ F // k • g = 0} → Quot (Out.QkPt.Equiv D₀ F (k := k)) := fun x =>
        Quot.mk _ (qkMk x.1.out (r x.1.out + x.2.1) (by rw [nsmul_add, hr, x.2.2, add_zero]))
      rw [← hK, ← Nat.card_prod]
      refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
      · rintro ⟨c, t⟩ ⟨c', t'⟩ h
        obtain ⟨z, hy, hg⟩ := (equiv_iff _ _).1 ((equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact h))
        change c'.out = c.out + k • z at hy
        change r c'.out + t'.1 = r c.out + t.1 + iota z at hg
        obtain rfl : c = c' := by
          rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq]
          exact ⟨z, by rw [hy, neg_add_cancel_left]; rfl⟩
        have hz : z = 0 := by
          have h0 : (k : ℤ) • z = 0 := by rw [natCast_zsmul]; exact left_eq_add.1 hy
          exact (smul_eq_zero.1 h0).resolve_left (by exact_mod_cast hk0)
        rw [hz, map_zero, add_zero, add_right_inj] at hg
        exact Prod.ext rfl (Subtype.ext hg.symm)
      · rintro ⟨p⟩
        obtain ⟨z, hz⟩ : -p.y + (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out ∈ K := by
          rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
        have hy : (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out = p.y + k • z := by
          rw [show k • z = _ from hz, add_neg_cancel_left]
        refine ⟨⟨QuotientAddGroup.mk p.y, p.g + iota z - r (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out, ?_⟩,
          (Quot.sound ((equiv_iff _ _).2 ⟨z, hy, ?_⟩)).symm⟩
        · rw [nsmul_sub, hr, hy, nsmul_add, qk_nsmul, map_add (f := _), map_nsmul, sub_self]
        · exact add_sub_cancel _ _
  rw [hc, h₁, ← pow_add]
  congr 1
  ring

theorem card_qk_of_tateIsoQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {R : Type} [CommRing R] [IsDomain R] {D₀ : Out.DegPre R} [Module (𝓞 E) D₀.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (hB : D₀.TauBimult) (I : TateIsoQ D D₀ oa F) (k : ℕ) (hk : 0 < k) :
    Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) = k ^ Module.finrank ℤ D.La := by
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have := datum_free_int D
  let K : AddSubgroup D.La := (nsmulAddMonoidHom k : D.La →+ D.La).range
  have hK : Nat.card (D.La ⧸ K) = k ^ Module.finrank ℤ D.La := AddSubgroup.index_range_nsmul D.La k
  have hE := equiv_equivalence (D := D₀) (F := F) (k := k) hB
  let f : D.La ⧸ K → Quot (Out.QkPt.Equiv D₀ F (k := k)) := fun x => Quot.mk _ (I.ev k x.out)
  rw [← hK]
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · intro x x' h
    obtain ⟨e, he⟩ := (I.ker k hk _ _).1 (hE.symm (hE.eqvGen_iff.1 (Quot.eqvGen_exact h)))
    rw [← QuotientAddGroup.out_eq' x, ← QuotientAddGroup.out_eq' x', QuotientAddGroup.eq]
    exact ⟨e, by rw [he, neg_add_cancel_left]; rfl⟩
  · rintro ⟨p⟩
    obtain ⟨v, hv⟩ := I.onto k hk p
    obtain ⟨e, he⟩ : -v + (QuotientAddGroup.mk v : D.La ⧸ K).out ∈ K := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    refine ⟨QuotientAddGroup.mk v, Quot.sound (hE.trans ((I.ker k hk _ _).2 ⟨e, ?_⟩) hv)⟩
    rw [show k • e = _ from he, add_neg_cancel_left]

theorem finrank_V_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → (∃ r z : O, ((β r : c.F) : ℂ) = H.rt0 ∧ ((β z : c.F) : ℂ) = zeta l.A) → Module.finrank ℂ Λ.A.V = g := by
  intro hL hL2 E _ _ _ H _ D l c O _ β _ _ b a Λ g ty hty ⟨r, z, hr, hz⟩
  obtain ⟨-, I, -⟩ := a.geom ℂ r z hr hz _ rfl
  have h₁ := card_qk_pre hL hL2 a.D₀ a.bimult ℂ 2 (by norm_num)
  rw [card_qk_of_tateIsoQ a.bimult I 2 two_pos, datum_finrank_int,
    ← (GlobalTheory.PeriodExists.period_of_isTypeFn H D g ty hty).1] at h₁
  have h₂ := Nat.pow_right_injective le_rfl h₁
  have h₃ : Module.finrank ℤ Λ.A.X = a.D₀.rank := (Λ.ε.toAddEquiv.toIntLinearEquiv).finrank_eq
  rw [Λ.A.finrank_V, h₃, Λ.gB_eq]
  omega

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ChartCoordinatesHasSumStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holArc_chart_coordinates_hasSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (φ : p.R →ₐ[c.F] ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → IsOpenImmersion j → j ≫ pullback.snd _ _ = spMap (algebraMap c.F p.R) → spMap φ.toRingHom ≫ j ≫ Y.j = spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∃ ψ : p.R →ₐ[c.F] CAt σ, spMap ψ.toRingHom ≫ j ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) ∧ ∀ f : p.R, HasSum (fun m : ℤ => (φ f).coeff m * eTwoPi w ^ m) (toC (ψ f)) := by
  first | exact @GlobalTheory.ArcPoint.chart_coordinates_hasSum | exact GlobalTheory.ArcPoint.chart_coordinates_hasSum | (intros; apply GlobalTheory.ArcPoint.chart_coordinates_hasSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffMulFSum
section
noncomputable section
namespace GlobalTheory.ArcPts.WeightZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

def chr (x : A.X) : Multiplicative (A.X →+ ℂ) →* ℂ where
  toFun l := eTwoPi (l.toAdd x)
  map_one' := AnArc.e_zero
  map_mul' l l' := AnArc.e_add _ _

theorem chr_injective : Function.Injective (chr A) := by
  intro x y hxy
  by_contra hne
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨i, hi⟩ : ∃ i, (Module.Free.chooseBasis ℤ A.X).repr (x - y) i ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hd
    apply (Module.Free.chooseBasis ℤ A.X).repr.map_eq_zero_iff.mp
    ext j
    simpa using hall j
  let k : ℤ := (Module.Free.chooseBasis ℤ A.X).repr (x - y) i
  let g : A.X →+ ℂ := (Int.castAddHom ℂ).comp ((Module.Free.chooseBasis ℤ A.X).coord i).toAddMonoidHom
  have hg : g (x - y) = k := by simp [g, k]
  have hk : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hi
  let l : A.X →+ ℂ := (2 * (k : ℂ))⁻¹ • g
  have hl : l (x - y) = 1 / 2 := by
    simp only [l, AddMonoidHom.smul_apply, hg, smul_eq_mul]
    field_simp
  have h1 : eTwoPi (l x) = eTwoPi (l y) := congrArg (fun χ => χ (Multiplicative.ofAdd l)) hxy
  have h2 : eTwoPi (l x) = eTwoPi (l (x - y)) * eTwoPi (l y) := by
    rw [← AnArc.e_add, map_sub, sub_add_cancel]
  rw [hl, h1] at h2
  have h3 : eTwoPi (1 / 2) = 1 :=
    mul_right_cancel₀ (AnArc.e_ne_zero (l y)) (h2.symm.trans (one_mul _).symm)
  have h4 : eTwoPi (1 / 2) = -1 := by
    simp only [eTwoPi]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 / 2) = Real.pi * Complex.I by ring, Complex.exp_pi_mul_I]
  rw [h4] at h3
  norm_num at h3

theorem coeff_zero_eq {F G : Finset A.X} {b c : A.X → ℂ} (hF : 0 ∈ F) (hG : 0 ∈ G)
    (h : ∀ l : A.X →+ ℂ, ∑ x ∈ F, b x * eTwoPi (l x) = ∑ x ∈ G, c x * eTwoPi (l x)) : b 0 = c 0 := by
  classical
  have hli : LinearIndependent ℂ (fun x : A.X =>
      ((chr A x : Multiplicative (A.X →+ ℂ) →* ℂ) : Multiplicative (A.X →+ ℂ) → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative (A.X →+ ℂ)) ℂ).comp (chr A) (chr_injective A)
  let g : A.X → ℂ := fun x => (if x ∈ F then b x else 0) - (if x ∈ G then c x else 0)
  have hsum : ∑ x ∈ F ∪ G, g x • ((chr A x : Multiplicative (A.X →+ ℂ) →* ℂ) :
      Multiplicative (A.X →+ ℂ) → ℂ) = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, g, sub_mul, ite_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.union_inter_cancel_left,
      Finset.union_inter_cancel_right]
    exact sub_eq_zero.mpr (h (Multiplicative.toAdd m))
  have h0 := linearIndependent_iff'.mp hli (F ∪ G) g hsum 0 (Finset.mem_union_left _ hF)
  simpa [g, hF, hG, sub_eq_zero] using h0

theorem exponent_one (α μ : A.X) : A.exponent 1 α μ = A.q (α + μ) - A.q α := by
  rw [AnArc.exponent, AnArc.q_add, A.be_symm μ α]
  push_cast
  ring

theorem FSum_shift (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum 1 α th v = HahnSeries.single (-A.q α) ((A.psi α : ℂ)⁻¹) * A.FSum 1 0 (fun z => th (z - A.ct α)) v := by
  ext n
  rw [HahnSeries.coeff_single_mul, AnArc.coeff_FSum, AnArc.coeff_FSum, Finset.mul_sum, sub_neg_eq_add]
  refine Finset.sum_nbij' (fun μ => α + μ) (fun ν => ν - α) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [AnArc.mem_level, exponent_one A, zero_add, AnArc.q_zero, sub_zero] at hμ ⊢
    linarith
  · intro ν hν
    simp only [AnArc.mem_level, exponent_one A, zero_add, AnArc.q_zero, sub_zero] at hν ⊢
    rw [show α + (ν - α) = ν by abel]
    linarith
  · intro μ _
    simp
  · intro ν _
    simp
  · intro μ _
    have hu : (A.psi α : ℂ) ≠ 0 := (A.psi α).ne_zero
    have hc : v.2 + A.ct (α + μ) - A.ct α = v.2 + A.ct μ := by rw [map_add (f := _)]; abel
    simp only [AnArc.term, pow_one, one_smul, zero_add, map_zero, AnArc.e_zero, A.psi_add,
      A.T_symm α μ, hc]
    rw [eq_inv_mul_iff_mul_eq₀ hu]
    ring

theorem coeff_mul_FSum (r : ℂ⸨X⸩) (n : ℤ) : ∃ G₀ : Finset A.X, ∀ G, G₀ ⊆ G → ∀ (th : (Fin A.gB → ℂ) → ℂ) (v : A.V),
    (r * A.FSum 1 0 th v).coeff n = ∑ μ ∈ G, r.coeff (n - A.q μ) * A.term 1 0 th μ v := by
  classical
  refine ⟨(A.finite_be_le (2 * (n - r.order))).toFinset, fun G hG th v => ?_⟩
  have hq : ∀ μ, A.exponent 1 0 μ = A.q μ := fun μ => by
    rw [exponent_one A, zero_add, AnArc.q_zero, sub_zero]
  have hq0 : ∀ μ, 0 ≤ A.q μ := fun μ => by
    have h1 := A.two_mul_q μ
    have h2 := A.be_self_nonneg μ
    linarith
  have hpwo : (Set.Ici (0 : ℤ)).IsPWO := bddBelow_Ici.isWF.isPWO
  have hsupp : (A.FSum 1 0 th v).support ⊆ Set.Ici 0 := by
    intro k hk
    rw [Set.mem_Ici]
    by_contra hlt
    exact hk (A.coeff_FSum_eq_zero 1 0 th v (by simpa using not_le.mp hlt))
  rw [HahnSeries.coeff_mul_right' hpwo hsupp]
  simp only [AnArc.coeff_FSum, Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij_ne_zero (fun a _ _ => a.2) ?_ ?_ ?_ ?_
  · rintro ⟨⟨i, k⟩, μ⟩ h₁ h₂
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq] at h₁
    obtain ⟨⟨-, -, hik⟩, hμ⟩ := h₁
    have ho := HahnSeries.order_le_of_coeff_ne_zero (left_ne_zero_of_mul h₂)
    apply hG
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ← A.two_mul_q]
    simp only at hμ hik ho ⊢
    linarith
  · rintro ⟨⟨i, k⟩, μ⟩ h₁ _ ⟨⟨i', k'⟩, μ'⟩ h₁' _ heq
    simp only at heq
    subst heq
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq] at h₁ h₁'
    obtain ⟨⟨-, -, hik⟩, hμ⟩ := h₁
    obtain ⟨⟨-, -, hik'⟩, hμ'⟩ := h₁'
    simp only at hik hμ hik' hμ'
    have hk : k = k' := by rw [← hμ, ← hμ']
    subst hk
    have hi : i = i' := by omega
    subst hi
    rfl
  · intro μ _ hne
    refine ⟨⟨(n - A.q μ, A.q μ), μ⟩, ?_, hne, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq]
    exact ⟨⟨(HahnSeries.mem_support _ _).mpr (left_ne_zero_of_mul hne), Set.mem_Ici.mpr (hq0 μ), by simp⟩, rfl⟩
  · rintro ⟨⟨i, k⟩, μ⟩ h₁ _
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq] at h₁
    obtain ⟨⟨-, -, hik⟩, hμ⟩ := h₁
    simp only at hik hμ ⊢
    rw [show i = n - A.q μ by omega]

theorem eq_FSum {f : A.V → ℂ⸨X⸩} (hf : ArcPts.IsComb A 1 Set.univ f) (θ : (Fin A.gB → ℂ) → ℂ)
    (h : ∀ (z : Fin A.gB → ℂ) (n : ℤ), ∃ (F : Finset A.X) (b : A.X → ℂ), 0 ∈ F ∧ b 0 = (if n = 0 then θ z else 0) ∧
      ∀ l : A.X →+ ℂ, (f (l, z)).coeff n = ∑ x ∈ F, b x * eTwoPi (l x)) (v : A.V) : f v = A.FSum 1 0 θ v := by
  classical
  obtain ⟨m, r, α, th, -, hfe⟩ := hf
  obtain ⟨s, ph, hfe'⟩ : ∃ (s : Fin m → ℂ⸨X⸩) (ph : Fin m → (Fin A.gB → ℂ) → ℂ),
      ∀ w, f w = ∑ i, s i * A.FSum 1 0 (ph i) w :=
    ⟨fun i => r i * HahnSeries.single (-A.q (α i)) ((A.psi (α i) : ℂ)⁻¹), fun i z => th i (z - A.ct (α i)),
      fun w => by
        rw [hfe w]
        exact Finset.sum_congr rfl fun i _ => by simp only [FSum_shift A (α i) (th i) w, mul_assoc]⟩
  have hq : ∀ μ, A.exponent 1 0 μ = A.q μ := fun μ => by
    rw [exponent_one A, zero_add, AnArc.q_zero, sub_zero]
  have hexp : ∀ n : ℤ, ∃ G : Finset A.X, 0 ∈ G ∧ A.level 1 0 n ⊆ G ∧ ∀ w : A.V,
      (f w).coeff n = ∑ μ ∈ G, ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ w := by
    intro n
    choose G₀ hG₀ using fun i => coeff_mul_FSum A (s i) n
    have hsub : ∀ i, G₀ i ⊆ insert 0 (A.level 1 0 n ∪ Finset.univ.biUnion G₀) := fun i =>
      (Finset.subset_biUnion_of_mem G₀ (Finset.mem_univ i)).trans
        (Finset.subset_union_right.trans (Finset.subset_insert _ _))
    refine ⟨insert 0 (A.level 1 0 n ∪ Finset.univ.biUnion G₀), Finset.mem_insert_self _ _,
      fun μ hμ => Finset.mem_insert_of_mem (Finset.mem_union_left _ hμ), fun w => ?_⟩
    rw [hfe' w, HahnSeries.coeff_sum, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => hG₀ i _ (hsub i) (ph i) w
  have hkey : ∀ (z : Fin A.gB → ℂ) (n : ℤ), ∑ i, (s i).coeff n * ph i z = if n = 0 then θ z else 0 := by
    intro z n
    obtain ⟨G, hG0, -, hG⟩ := hexp n
    obtain ⟨F, b, hF0, hb0, hFb⟩ := h z n
    have hc := coeff_zero_eq A (F := F) (G := G) (b := b)
      (c := fun μ => (A.psi μ : ℂ) * ∑ i, (s i).coeff (n - A.q μ) * ph i (z + A.ct μ)) hF0 hG0 (fun l => by
        rw [← hFb l, hG (l, z)]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [AnArc.term, pow_one, one_smul, zero_add, map_zero, AnArc.e_zero]
        ring)
    rw [← hb0, hc]
    simp
  ext n
  obtain ⟨G, -, hlev, hG⟩ := hexp n
  have hK : ∀ (μ : A.X) (g : (Fin A.gB → ℂ) → ℂ),
      A.term 1 0 g μ v = A.term 1 0 (fun _ => 1) μ v * g (v.2 + A.ct μ) := by
    intro μ g
    simp only [AnArc.term, mul_one]
  have hterm : ∀ μ, ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ v =
      if A.q μ = n then A.term 1 0 θ μ v else 0 := by
    intro μ
    calc ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ v
        = A.term 1 0 (fun _ => 1) μ v * ∑ i, (s i).coeff (n - A.q μ) * ph i (v.2 + A.ct μ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hK μ (ph i)]; ring
      _ = if A.q μ = n then A.term 1 0 θ μ v else 0 := by
          rw [hkey, hK μ θ]
          by_cases hμ : A.q μ = n
          · rw [if_pos (by omega), if_pos hμ]
          · rw [if_neg (by omega), if_neg hμ, mul_zero]
  rw [hG v, AnArc.coeff_FSum]
  simp only [hterm]
  rw [← Finset.sum_filter]
  congr 1
  ext μ
  simp only [Finset.mem_filter, AnArc.mem_level, hq]
  exact ⟨fun hμ => hμ.2, fun hμ => ⟨hlev (by rw [AnArc.mem_level, hq]; exact hμ), hμ⟩⟩

end GlobalTheory.ArcPts.WeightZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffMemSubfield
section
noncomputable section

namespace GlobalTheory.ArcPts

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory Filter
open scoped LaurentSeries PowerSeries

theorem exists_coeff_mem_subfield {k L V ι : Type*} [Field k] [Field L] [Algebra k L] [Fintype ι]
    (K : IntermediateField k L) (r : ι → L) (g : ι → V → L) (f : V → L) (hg : ∀ i v, g i v ∈ K)
    (hf : ∀ v, f v ∈ K) (h : ∀ v, f v = ∑ i, r i * g i v) :
    ∃ s : ι → L, (∀ i, s i ∈ K) ∧ ∀ v, f v = ∑ i, s i * g i v := by
  obtain ⟨π, hπ⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  refine ⟨fun i => π (r i), fun i => (π (r i)).2, fun v => ?_⟩
  have h1 : π (f v) = ⟨f v, hf v⟩ := LinearMap.congr_fun hπ ⟨f v, hf v⟩
  have h2 : π (f v) = ∑ i, π (r i) * ⟨g i v, hg i v⟩ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : r i * g i v = (⟨g i v, hg i v⟩ : K) • r i := by
      rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have h3 := congrArg (fun x : K => (x : L)) (h1.symm.trans h2)
  simpa using h3

theorem exists_isComb_halfRing : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), AnFin A →
    ∀ (j : ℕ) [NeZero j] (f : A.V → ℂ⸨X⸩), IsComb A j Set.univ f → (∀ v, f v ∈ Conv.convLaurent) →
    ∃ T : ℝ, IsComb A j (Conv.halfRing T) f ∧ ∀ v, f v ∈ Conv.halfRing T := by
  rintro O _ _ A - j _ f ⟨n, r, α, th, h1, h2⟩ hf
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  have hm : ∀ i v, A.FSum j (α i) (th i) v ∈ Conv.halfRing T₀ := fun i v _ hw =>
    (AnArc.hasSum_coeff_FSum h₀ (h1 i).2 hw v).summable
  obtain ⟨s, hs, hfs⟩ := exists_coeff_mem_subfield Conv.convLaurent r (fun i v => A.FSum j (α i) (th i) v) f
    (fun i v => Conv.halfRing_le_convLaurent T₀ (hm i v)) hf h2
  obtain ⟨T, hT, hT₀⟩ := ((eventually_all.2 fun i => Conv.eventually_mem_halfRing (hs i)).and
    (eventually_ge_atTop T₀)).exists
  refine ⟨T, ⟨n, s, α, th, fun i => ⟨hT i, (h1 i).2⟩, hfs⟩, fun v => ?_⟩
  rw [hfs v]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hT i) (Conv.halfRing_mono hT₀ (hm i v))

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSumStatement
section
alias GlobalTheory.T.frame_matrix_hasSum_alt := GlobalTheory.ArcLie.frame_matrix_hasSum
end

