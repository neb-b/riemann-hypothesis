module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionCoordinatesEqDegenerationSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuesIsoRespectsEndomorphismOfTorsionCompat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceValuesIntegralTorsionBoundShortestVec
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PowerSeriesAlgebraicClosureCompatible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel

theorem actCompat_of_match (hL : Laws) (hL2 : Laws2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O']
    [IsDomain O'] [IsLocalRing O'] [IsNoetherianRing O'] {b : O →+* O'} (a : ArcIn D l β O' b)
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing O') C]
    (hO : CExt O' ⊥ C) (A : Lift a C) {u : Cˣ} {r : ℕ → Cˣ} {o : Full D C} (M : Mdl o) (hTI : M.P.TorsionIso)
    {f : O' →+* M.W} {u₀ : M.W}
    (hint : A.ν.IntN) (hr : Roots u r) {n : ℕ} (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1)
    {N' : NumD C} (ν' : NumOf M.P.D.toPre C N') (J : NumD.Iso (A.N.twist A.be u) N')
    (hX : ∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y))
    (hlab : ∀ j x (p : (A.N.twist A.be u).QT (n ^ j)) (q' : N'.QT (n ^ j)) p' z,
      TwRel A.be u (r (n ^ j)) (A.q _ x) p → q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' →
      z.left = (o.I.ev (n ^ j) x).left ≫ M.φ → M.P.ToA C (n ^ j) p' z)
    {DW : DegPre M.W} [Module (𝓞 E) DW.X] (oW : letI := H.starRing; DW.OAct (𝓞 E)) (φ : _) (he : _) (w : _) (e : _)
    (νW : NumOf DW C (A.N.twist A.be u)) (hm : GlobalTheory.LN.Match a f u₀ DW oW φ he w e)
    (hA : ∀ x, (νW.eA x).left ≫ φ = (A.ν.eA x).left) (hg : GeoIso νW ν' J.toIso) :
    letI := H.starRing
    ActCompat A.ν a.oa ν' M.P.oD A.be u r J := by
  letI := H.starRing
  have hG := hL.globalFns
  have hnC : (n : C) ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
  obtain ⟨hp, hw, -, hact, -⟩ := hm
  have hT := _root_.GlobalTheory.ValuesTorsion.tors_of_integral hL hL2 (_root_.GlobalTheory.ThetaInValues.brUth_of_laws hL) O' a.D₀ a.even a.bimult C hO A.N A.ν hint n hn ho h1
  have eW : ∀ x (y : A.N.A), actV (N := A.N.twist A.be u) νW oW.onB x y = actV A.ν a.oa.onB x y := fun x y => by
    refine νW.eA.injective (Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w])))
    refine Eq.trans ?_ (hA _).symm
    have a₁ : νW.eA (actV (N := A.N.twist A.be u) νW oW.onB x y) = _ := νW.eA.apply_symm_apply _
    have a₂ : A.ν.eA (actV A.ν a.oa.onB x y) = _ := A.ν.eA.apply_symm_apply _
    refine (congrArg (fun q => q.left ≫ φ) a₁).trans (Eq.trans ?_ (congrArg (fun q => q.left) a₂).symm)
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hact x)).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (hA y))))
  have hB : ∀ x (y : A.N.A), J.φ (actV (N := A.N) A.ν a.oa.onB x y) = actV ν' M.P.oD.onB x (J.φ y) := fun x y => by
    rw [← eW]
    refine _root_.GlobalTheory.Relabel.actV_compat_of_torsion hL _ _ _ C _ _ νW ν' J.toIso hg _ oW.onB M.P.oD.onB n hn hnC x (fun j y hy => ?_) y
    refine (congrArg J.φ (eW x y)).trans ?_
    exact GlobalTheory.T.arcTorsionLabels_action_compat hL _root_.GlobalTheory.Ex.GtValues.points_correspond E H D O' C A.arc o M hTI N' ν' _ A.be u (r (n ^ j)) J (n ^ j) (pow_pos hn.pos j)
      (hr.pow (pow_pos hn.pos j)) (hlab j) x y hy
  refine GlobalTheory.T.torsionQuotientAction_compat_of_rosatiValues hG _root_.GlobalTheory.Ex.GtValues.points_correspond E H D O' M.W C A.arc M.P.D.toPre M.P.oD M.P.D.psi_even M.P.D.tau_bimult N' ν' _ A.be u r J hr
    (fun x y z => ?_) hX hB fun x => ?_
  · refine (A.be_eq _ _).trans (Eq.trans ?_ (A.be_eq _ _).symm)
    simp only [ArcF.act]
    erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact a.be_adj _ _ _
  obtain ⟨ρ, hρ⟩ := (_root_.GlobalTheory.Relabel.gtAct_values hG _ _ C _ A.ν (𝓞 E)).1 a.oa.onB x
  obtain ⟨ρW, hρW⟩ := (_root_.GlobalTheory.Relabel.gtAct_values hG _ _ C _ νW (𝓞 E)).1 oW.onB x
  obtain ⟨ρ', hρ'⟩ := (_root_.GlobalTheory.Relabel.gtAct_values hG _ _ C _ ν' (𝓞 E)).1 M.P.oD.onB x
  refine ⟨ρ, ρ', hρ, hρ', fun (y y' : A.N.A) => ?_⟩
  obtain ⟨w', κ, hw', hκ⟩ := GlobalTheory.T.lineBundleIso_values_constant_of_same_cube_theta hL _ _ f DW a.D₀ C A.N _ A.be u νW A.ν φ w hp hw hA n hT.div (fun t => by
    obtain ⟨s, h₁, h₂⟩ := hT.good t
    exact ⟨s, h₁, fun h => by rw [h, norm_zero] at h₂; exact zero_ne_one h₂⟩)
  have hTF : (TF (R := M.W) C).hom ≫ spMap f = (TF (R := O') C).hom := by
    have := congrArg (· ≫ a.D₀.P.A.hom) (hA 1)
    rwa [Category.assoc, hp.1.w, ← Category.assoc, Over.w, Over.w] at this
  have e₁ := GlobalTheory.T.normalisedRosatiGenerator_values_move_along_iso hL _ _ DW a.D₀ C _ A.N νW A.ν (𝓞 E) oW.onB a.oa.onB _ w' (MonoidHom.id A.N.A) (fun _ => κ) hw'
    (by rw [Category.assoc, hp.1.w, ← hTF, ← Category.assoc, ← Category.assoc, Over.w, Over.w])
    (fun y => by rw [← Category.assoc, ← Over.comp_left, lift_snd]; exact hA y) (fun y => (hκ y).symm) eW x ρW ρ hρW hρ y y'
  have e₂ : ρ y y' = ρW y y' := mul_right_cancel₀ (by simp) e₁
  obtain ⟨Φ, w₂, wv, g₁, g₂, g₃, g₄, g₅⟩ := hg
  have e₃ := GlobalTheory.T.normalisedRosatiGenerator_values_move_along_iso hL _ _ DW M.P.D.toPre C _ N' νW ν' (𝓞 E) oW.onB M.P.oD.onB _ w₂ J.φ.toMonoidHom wv g₂
    (by rw [Over.w, Over.w]) (fun y => by rw [← Over.comp_left, ← Category.assoc, g₃, lift_snd]; rfl) g₄
    (fun x y => (congrArg J.φ (eW x y)).trans (hB x y)) x ρW ρ' hρW hρ' y y'
  have h0 : wv 1 ≠ 0 := by
    have hU : ⊤ ≤ (lift (𝟙 (TF (R := M.W) C)) (νW.eA 1)).left ⁻¹ᵁ (LB.div _ _).U
        (fun _ => ν'.J (ν'.eA (J.φ 1)).left, fun _ => νW.J (νW.eA 1).left) := fun p _ => by
      refine (⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩ : _ ∈ (LB.div
        (M.P.D.toPre.P.L.pull (Φ.hom ≫ snd (TF (R := M.W) C) M.P.D.toPre.P.A).left)
        (DW.P.L.pull (snd (TF (R := M.W) C) DW.P.A).left)).U _)
      · have := ν'.good (ν'.eA (J.φ 1)).left (Set.mem_univ p)
        have e : (lift (𝟙 (TF (R := M.W) C)) (νW.eA 1)).left ≫ (Φ.hom ≫ snd _ _).left = (ν'.eA (J.φ 1)).left := by
          rw [← Over.comp_left, ← Category.assoc, g₃, lift_snd]
        exact (congrArg (fun t => t p ∈ M.P.D.toPre.P.L.U (ν'.J (ν'.eA (J.φ 1)).left)) e).mpr this
      · have := νW.good (νW.eA 1).left (Set.mem_univ p)
        have e : (lift (𝟙 (TF (R := M.W) C)) (νW.eA 1)).left ≫ (snd (TF (R := M.W) C) DW.P.A).left = (νW.eA 1).left := by
          rw [← Over.comp_left, lift_snd]
        exact (congrArg (fun t => t p ∈ DW.P.L.U (νW.J (νW.eA 1).left)) e).mpr this
    rw [g₄, valF, dite_eq_left hU]
    exact (((Units.isUnit _).map _).map _).ne_zero
  have key : ∀ (s t : A.N.A) (p q : C), p * (wv s * wv y' * wv (y * t)) = q * (wv (s * y') * wv y * wv t) →
      p * (J.h s * J.h y' * J.h (y * t) : Cˣ) = q * (J.h (s * y') * J.h y * J.h t : Cˣ) := fun s t p q h => by
    refine mul_right_cancel₀ (pow_ne_zero 3 h0) ?_
    have b₁ := g₅ s
    have b₂ := g₅ y'
    have b₃ := g₅ (y * t)
    have b₄ := g₅ (s * y')
    have b₅ := g₅ y
    have b₆ := g₅ t
    have alg : ∀ p q a₁ a₂ a₃ c₁ c₂ c₃ a₁' a₂' a₃' c₁' c₂' c₃' t : C, a₁ * t = a₁' → a₂ * t = a₂' → a₃ * t = a₃' →
        c₁ * t = c₁' → c₂ * t = c₂' → c₃ * t = c₃' → p * (a₁' * a₂' * a₃') = q * (c₁' * c₂' * c₃') →
        p * (a₁ * a₂ * a₃) * t ^ 3 = q * (c₁ * c₂ * c₃) * t ^ 3 := by
      rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl h
      linear_combination h
    exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b₁ b₂ b₃ b₄ b₅ b₆ h
  have e₄ := key _ _ _ _ e₃
  rw [← e₂] at e₄
  erw [eW (star x) y, eW x y'] at e₄
  exact e₄

theorem exists_has : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n : ℕ), n.Prime → Odd n → IsUnit (n : O') → ∀ o₀ : Full D K, o₀.ρ = S.A.ρ → (∀ j, o₀.I.ζ (n ^ j) = S.A.I.ζ (n ^ j) ∧ o₀.Theta (n ^ j) (S.v (n ^ j))) → ∃ o, S.Has o := by
  intro hV h6 hU hH hT hE hA E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb K _ _ _ _ _ _ hK S n hn ho hu o₀ hρ h₀
  letI := H.starRing
  have hL := hV.1.1
  have hL2 := hV.1.2.1
  have hGt := _root_.GlobalTheory.Ex.GtValues.points_correspond
  have hFam := _root_.GlobalTheory.Ex.brFam hL hL2
  haveI := o₀.charZero
  obtain ⟨W, _, _, _, φ, K₁, _, _, _, e, hW, hX, he⟩ := _root_.GlobalTheory.HasFields.exists_cdv_over_powerSeries O' K
  haveI := hW.1
  obtain ⟨C, _, _, _, _, _, g₁, hg₁, hC⟩ := _root_.GlobalTheory.Ex.exists_complete_isAlgClosed_cExt W K₁
  let gam : K →+* C := g₁.comp e
  haveI : CharZero C := (RingHom.charZero_iff gam.injective).1 inferInstance
  letI : Algebra (FractionRing O') C := (gam.comp (algebraMap (FractionRing O') K)).toAlgebra
  have hgam : ∀ x, gam (algebraMap (PowerSeries O') K x) = algebraMap (FractionRing W) C (algebraMap W _ (φ x)) :=
    fun x => (congrArg g₁ (he x)).trans (hg₁ _)
  have hOC : ∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) =
      algebraMap (FractionRing W) C (algebraMap W _ (φ (PowerSeries.C x))) := fun x =>
    (congrArg gam (hK x)).trans (hgam _)
  let u : Cˣ := Units.map gam.toMonoidHom (S.r 1)
  have huv : (u : C) = gam (algebraMap (PowerSeries O') K PowerSeries.X) := congrArg gam S.r_one
  have hu1 : ‖(u : C)‖ < 1 := by rw [huv, hgam]; exact hC.2 _ hX
  obtain ⟨A, r, hint, ⟨-, hAρ, hAζ, -⟩, hr', hser⟩ := S.val C gam u (fun x => congrArg gam (hK x))
    (fun x => by rw [hgam]; exact hC.1 _) huv hu1
  have hr : Roots u r := ⟨Units.ext (hr' 1), fun n m hn hm => Units.ext (by
    rw [Units.val_pow_eq_pow_val, hr', hr', ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.2 n m hn hm])⟩
  obtain ⟨o, hext, hθ, -⟩ := _root_.GlobalTheory.FullExtend.main hV h6 hU hH hT hE hA E H D K C gam o₀
  obtain ⟨M, f, hf⟩ := _root_.GlobalTheory.Ex.ExtModel.exists_mdl_ext hV h6 hU hH hT hE hA E H D l Xo c W₀ Y O' b ϖ a hb K S.A o₀ hρ C W hW hC K₁ g₁ e
    (φ.comp PowerSeries.C) hg₁ (fun x => (congrArg e (hK x)).trans (he _)) o hext
  have hO : CExt O' ⊥ C := ⟨fun x => by rw [hOC]; exact hC.1 _, fun x hx => by
    rw [Ideal.mem_bot.1 hx, map_zero, map_zero, norm_zero]; exact one_pos⟩
  have h1 : ‖(n : C)‖ = 1 := by
    obtain ⟨m, hm⟩ := hu.exists_right_inv
    have a₁ := hO.1 n
    have a₂ := hO.1 m
    have a₃ := congrArg (fun x => ‖algebraMap (FractionRing O') C (algebraMap O' _ x)‖) hm
    simp only [map_mul, map_natCast, map_one, norm_mul, norm_one] at a₁ a₃
    refine le_antisymm a₁ ?_
    calc (1 : ℝ) = _ := a₃.symm
      _ ≤ ‖(n : C)‖ * 1 := by gcongr
      _ = _ := mul_one _
  obtain ⟨N', ν', J, hJX, hlab, DW, _, oW, ψ, he', w, e', νW, hm, -, hA', hgeo⟩ :=
    GlobalTheory.T.lift_valuation_integral_norm hV h6 hU hH hT hE hA E H D l Xo c W₀ Y O' b ϖ a hb C A u r o M (f.comp (φ.comp PowerSeries.C))
      (f (φ PowerSeries.X)) hint hr hu1 (by rw [hf, huv, hgam]) (fun x => (hf _).trans (hOC x).symm) n hn ho h1 fun j => by
      refine ⟨Units.ext ?_, fun p hp => ?_⟩
      · rw [hext.2.1 _ (pow_pos hn.pos j), (h₀ j).1]
        exact hAζ _ (pow_pos hn.pos j)
      · obtain ⟨s, hs⟩ := (hser _ ho.pow p hp).1
        have hc := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C _ o.P (𝟙 _) (n ^ j) ho.pow (Nat.cast_ne_zero.2 (pow_pos hn.pos j).ne') _
          (o.I.ev ((n ^ j) ^ 2)) fun x => (o.I.onto _ (pow_pos (pow_pos hn.pos j) 2) _).2 ⟨x, rfl⟩
        refine (hc.2.2.1 _).2 ((hc.2.1 1 _ _ ((hc.2.2.1 _).1 (hθ _ _ (h₀ j).2))).2 ⟨s⁻¹, funext fun x => ?_⟩)
        rw [Pi.smul_apply, hs, smul_eq_mul, Units.inv_mul_cancel_left]
  have hloc : IsLocalRing O' ∧ IsNoetherianRing O' := by
    rcases hb with h | h
    · letI := h.1.toField
      exact ⟨inferInstance, inferInstance⟩
    · haveI := h.1
      exact ⟨inferInstance, inferInstance⟩
  haveI := hloc.1
  haveI := hloc.2
  have hTI : M.P.TorsionIso := haveI := M.admissible_base_of_complete_dvr.2
    _root_.GlobalTheory.UT.torsionIso_of_pelUnif hV.1 hV.2.1 hV.2.2.1 hV.2.2.2.1 hV.2.2.2.2 E H M.W _ M.admissible_base_of_complete_dvr.1 M.t M.P
  have hac := actCompat_of_match hL hL2 a hO A M hTI hint hr hn ho h1 ν' J hJX hlab oW ψ he' w e' νW hm hA' hgeo
  obtain ⟨I', hI'ζ, hI'⟩ := GlobalTheory.T.exists_torsionIsometry_twistByRoots_of_dataIso hGt (_root_.GlobalTheory.WeilValues.weil_eq_values hGt hFam) E H D O' M.W C A.arc M.P.D.toPre M.P.oD M.P.D.psi_even
    M.P.D.tau_bimult N' ν' _ A.be u r J hr hac
  obtain ⟨I, hIζ, hI⟩ := GlobalTheory.T.exists_full_torsion_isometry_of_tateIsoQ hV.1 E H D C o M I'
  have hco := GlobalTheory.T.thetaPoints_coords_relabelled_twistedData_series hV.1 hGt (_root_.GlobalTheory.Ex.ThetaSeries.theta_const_eq_series hV hGt hFam) (_root_.GlobalTheory.Ex.CoordSeries.coord_eq_series hV hGt hFam) E H D C o M I A.N N' ν' _ A.be u r J A.q
    fun j hj x => by
      obtain ⟨q', a₁, a₂⟩ := hI' j hj x
      obtain ⟨z, a₃, a₄⟩ := hI j hj x
      exact ⟨q', _, z, a₁, a₂, a₃, a₄⟩
  obtain ⟨I₀, hζ, hd⟩ := _root_.GlobalTheory.DescendIso.exists_descend hL E H D K C gam o₀ o hext I S.A.I.ζ fun n hn => by
    rw [hIζ, hI'ζ]; exact (hAζ n hn).symm
  refine ⟨withI o₀ I₀, hρ, hζ, fun m hm => ?_⟩
  choose p hp using fun x => (existsUnique_twRel A.be u (r (m ^ 2)) (hr.pow (pow_pos hm.pos 2)) (A.q _ x)).exists
  obtain ⟨⟨s, hs⟩, hw⟩ := hser m hm p hp
  refine ⟨(hd m hm).1 _ _ s hs (hco m hm p hp).1, fun j hj z => ?_⟩
  obtain ⟨q, hq⟩ := (existsUnique_twRel A.be u (r j) (hr.pow hj) (A.q j z)).exists
  obtain ⟨s', hs'⟩ := hw j hj z q hq
  exact (hd m hm).2 j hj z _ _ s' hs' ((hco m hm p hp).2 j hj z q hq)

end GlobalTheory.Relabel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem hasTests_of_real : GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.HasTests ∧ ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀), l.Match τ ∧ ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  intro hS hU hL hL2 hT o Ω _ _ _ _ S ρ
  have key : ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)),
      (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) →
      ∃ (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀), l.Match τ ∧
        ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
    intro p _ y₀ Fs hy
    obtain ⟨u, hu⟩ := _root_.GlobalTheory.exists_uniformised_model hS hU hL.polBaseChange o Ω S ρ p y₀ Fs
    obtain ⟨l⟩ := _root_.GlobalTheory.ZH.labels_exist hL hL2 hT o Ω S ρ p y₀ u hy
    obtain ⟨τ, hτ⟩ := exists_test_match o Ω S ρ p y₀ u l
      (_root_.GlobalTheory.ZH.TestVal.main hL hL2 hT o Ω S ρ p y₀ u l hy)
      (_root_.GlobalTheory.UnitTheta.closure_unit_theta hL hL2 hT o Ω S ρ p y₀ u l hy)
      (_root_.GlobalTheory.ZH.WeightBound.main hL hL2 hT o Ω S ρ p y₀ u l hy)
      (_root_.GlobalTheory.TestFibre.exists_norm_FF_eq hL hL2 hT o Ω S ρ p y₀ u l hy)
      (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hT o Ω S ρ p y₀ u l hy)
    exact ⟨u, l, τ, hτ, hu⟩
  refine ⟨?_, key⟩
  intro p _ y hy
  obtain ⟨_, _, τ, _⟩ := key p y ∅ hy
  exact ⟨τ⟩

end GlobalTheory.ZH
end

