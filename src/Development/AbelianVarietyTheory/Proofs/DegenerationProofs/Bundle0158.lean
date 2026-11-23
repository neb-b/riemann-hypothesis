module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxNest
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsAllPrimePowerLevelsOfSingleObject
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AllLevels

theorem ser_nested {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    {a : ArcIn D l β O' b} {K : Type} [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K]
    [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K] (S : Ser a K (algebraMap _ K))
    (r m : ℕ) (hr : Odd r) (hm : Odd m) : ∃ c : Kˣ, ∀ x, S.v (r * m) (r • x) = c * S.v m x := by
  obtain ⟨C, _, _, _, _, _, gam, u, h₁, h₂, h₃, h₄⟩ := _root_.GlobalTheory.Ex.exists_complete_isAlgClosed_powerSeries O' K
  obtain ⟨A, ρ, -, -, hρ, hv⟩ := S.val C gam u h₁ h₂ h₃ h₄
  have hR : Roots u ρ := ⟨Units.ext ((hρ 1).trans ((congrArg gam S.r_one).trans h₃.symm)), fun n k hn hk => Units.ext (by
    rw [Units.val_pow_eq_pow_val, hρ, hρ, ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.2 n k hn hk])⟩
  obtain ⟨b₁, -, b₃, -, b₅⟩ := _root_.GlobalTheory.Ex.GtValues.points_correspond O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨q₁, q₂⟩ := GlobalTheory.T.qval_add_of_tower E H D O' a.D₀ a.oa a.even a.bimult C A.I A.N A.ν A.q b₁ b₃
    (fun k => ⟨(b₅ k).1, (b₅ k).2.2⟩) A.hq
  have hrm : Odd (r * m) := hr.mul hm
  choose p hp _ using fun x => existsUnique_twRel A.be u (ρ (m ^ 2)) (hR.pow (pow_pos hm.pos 2)) (A.q _ x)
  choose p' hp' _ using fun x => existsUnique_twRel A.be u (ρ ((r * m) ^ 2)) (hR.pow (pow_pos hrm.pos 2)) (A.q _ x)
  obtain ⟨s, hs⟩ := (hv m hm p hp).1
  obtain ⟨s', hs'⟩ := (hv _ hrm p' hp').1
  have key : ∀ x, gam (S.v (r * m) (r • x)) = (s' * s⁻¹ : Cˣ) * gam (S.v m x) := fun x => by
    rw [hs, hs', _root_.GlobalTheory.Ex.twist_tx_nest C A.N D.La A.q q₁ q₂ _ A.be u ρ hR r m hr hm x _ _ (hp' _) (hp x), Units.val_mul,
      _root_.mul_assoc, Units.inv_mul_cancel_left]
  by_cases h : ∃ x, S.v m x ≠ 0
  · obtain ⟨x₀, h₀⟩ := h
    have e : gam (S.v (r * m) (r • x₀) / S.v m x₀) = (s' * s⁻¹ : Cˣ) := by
      rw [map_div₀, key, mul_div_cancel_right₀ _ ((map_ne_zero gam).2 h₀)]
    refine ⟨Units.mk0 (S.v (r * m) (r • x₀) / S.v m x₀) fun h => (s' * s⁻¹).ne_zero (by rw [← e, h, map_zero]),
      fun x => gam.injective ?_⟩
    rw [map_mul, Units.val_mk0, e, key]
  · simp only [not_exists, not_not] at h
    exact ⟨1, fun x => gam.injective (by rw [key, h, mul_zero, map_zero, mul_zero])⟩

theorem one_object : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n : ℕ), n.Prime → Odd n → (∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j))) → ∃ o : Full D K, o.ρ = S.A.ρ ∧ ∀ j, o.I.ζ (n ^ j) = S.A.I.ζ (n ^ j) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  intro hV _ _ _ h₁ h₂ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ K _ _ _ _ _ _ _ S n hn ho h
  exact exists_full_all hV.1.1 h₁ h₂ S.A.ρ S.A.I.ζ S.A.I.ζ_pow S.v (ser_nested S) hn ho h

end GlobalTheory.Ex.AllLevels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsSeriesScalarIndependentOfLeveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabelSystems_series_scalar_independent_of_level : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), Odd n → Labels N EF ζ lab → Labels N' EF ζ' lab' → (∀ j, ∃ c : Cˣ, ∀ x, N'.tx (n ^ j) (lab' _ x) = c * N.tx (n ^ j) (lab _ x)) → (∃ x, N.tx (n ^ 1) (lab _ x) ≠ 0) → ∃ c₀ : C, c₀ ≠ 0 ∧ ∀ j x, N'.tx (n ^ j) (lab' _ x) = c₀ * N.tx (n ^ j) (lab _ x) := by
  first | exact @GlobalTheory.ModelData.Scalar.scalar_const | exact GlobalTheory.ModelData.Scalar.scalar_const | (intros; apply GlobalTheory.ModelData.Scalar.scalar_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionQuotientActionCompatOfRosatiValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.Relabel

theorem c_smul_val {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N : NumD F} {O : Type} [CommRing O] [StarRing O] [Module O D.X]
    (ν : NumOf D F N) (oa : D.OAct O) (x : O) (χ : N.X) :
    N.c (ν.eX.symm (x • ν.eX χ)) = actV ν oa.onB x (N.c χ) := by
  rw [actV, ν.eA.eq_symm_apply, ν.c_eq, ν.c_eq, ν.eX.apply_symm_apply, DegPre.cF, oa.c_lin, Category.assoc]

theorem actq_cancel {F : Type} [Field F] {s s' s₀ s₀' t h₁ h₂ h₃ h₄ h₅ h₆ : Fˣ} {ρ ρ' : F}
    (e₁ : (s : F) = s₀ * ρ) (e₂ : s' * h₃ = s * t * h₅ * h₆) (e₃ : s₀' * h₄ = s₀ * t * h₁ * h₂)
    (e₄ : ρ' * (h₁ * h₂ * h₃ : Fˣ) = ρ * (h₄ * h₅ * h₆ : Fˣ)) : (s' : F) = s₀' * ρ' := by
  have a := congrArg Units.val e₂
  have b := congrArg Units.val e₃
  simp only [Units.val_mul] at a b e₄
  refine mul_right_cancel₀ (mul_ne_zero h₃.ne_zero h₄.ne_zero) ?_
  rw [e₁] at a
  linear_combination (h₄ : F) * a - ρ' * h₃ * b - (s₀ : F) * t * e₄

theorem actCompat_of_rosV : GlobalFnsSt → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → A.Bal β → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.act x y)) = x • ν'.eX (J.e y)) → (∀ (x : 𝓞 E) b, J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' oa'.onB x (J.φ b)) → (∀ a : 𝓞 E, ∃ ρ ρ', RosV A.ν A.oa.onB a ρ ∧ RosV ν' oa'.onB a ρ' ∧ ∀ b b' : A.N.A, ρ' (J.φ b) (J.φ b') * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b) * J.h b' * J.h (b * actV (N := A.N) A.ν A.oa.onB a b') : Fˣ) = ρ b b' * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b * b') * J.h b * J.h (actV (N := A.N) A.ν A.oa.onB a b') : Fˣ)) → ActCompat A.ν A.oa ν' oa' β u r J := by
  intro hG hB E _ _ _ H D
  letI := H.starRing
  intro R R' _ _ _ _ F _ _ _ _ A D' _ oa' he' hb' N' ν' k β u r J hr hbal hX hA hρ
  intro j hj x p₀ p₁ p₀' p₁' q₀ q₁ q₀' q₁' ⟨q, hqy, hqg, hqe⟩ h₀ h₁ t₀ t₁ h₀' h₁'
  obtain ⟨-, -, -, -, B⟩ := hB R A.D₀ A.even A.bimult F A.N A.ν
  obtain ⟨-, -, -, -, B'⟩ := hB R' D' he' hb' F N' ν'
  obtain ⟨τ, hτ, hτe, -⟩ := (twJ_mulEquiv F A.N N' k β u J).1 (r j) j (hr.pow hj)
  obtain ⟨qv, hqv, -⟩ := (B j).1 q
  obtain ⟨q', hq'⟩ := (B' j).2.1 (τ qv)
  have tq := (hτ qv _).1 rfl
  obtain ⟨ρ, ρ', hρ₁, hρ₂, hρ₃⟩ := hρ x
  obtain ⟨vb, vs⟩ := ((gtAct_values hG R A.D₀ F A.N A.ν (𝓞 E)).2 A.oa x ρ hρ₁ _ _ _ _ h₀.2 hqv.2).1 hqg
  have hy : qv.1.1.toAdd = A.act x q₀.1.1.toAdd := by
    rw [ArcF.act, A.ν.eX.eq_symm_apply, hqv.1, h₀.1, hqy]
  obtain ⟨P, ⟨Py, Pb, Ps⟩, Py', Pb', Ps'⟩ := tq
  obtain ⟨P₀, ⟨P₀y, P₀b, P₀s⟩, P₀y', P₀b', P₀s'⟩ := t₀
  refine ⟨q', ?_, ?_, ?_⟩
  · rw [← hq'.1, ← h₀'.1, Py', P₀y', Py, P₀y]
    exact (congrArg (fun y => ν'.eX (J.e y)) hy).trans (hX _ _)
  · refine ((gtAct_values hG R' D' F N' ν' (𝓞 E)).2 oa' x ρ' hρ₂ _ _ _ _ h₀'.2 hq'.2).2 ⟨?_, ?_⟩
    · rw [Pb', P₀b', Pb, P₀b, vb]
      exact hA _ _
    · rw [J.e.surjective.forall]
      intro (χ : A.N.X)
      have e₁ := vs χ
      have e₂ := Ps' χ
      have e₃ := P₀s' (A.act (star x) χ)
      have e₄ := hρ₃ (A.N.c χ) q₀.1.2.b
      have c₁ : (A.N.twist β u).c (A.act (star x) χ) = actV (N := A.N) A.ν A.oa.onB (star x) (A.N.c χ) :=
        c_smul_val A.ν A.oa (star x) χ
      rw [Ps, Pb, vb, hy, hbal] at e₂
      rw [P₀s, P₀b, c₁] at e₃
      have l : ν'.eX.symm (star x • ν'.eX (J.e χ)) = J.e (A.act (star x) χ) := by
        rw [ν'.eX.symm_apply_eq, hX]
      have c₂ : N'.c (J.e χ) = J.φ (A.N.c χ) := J.c_eq χ
      rw [l, c₂, P₀b', P₀b]
      exact actq_cancel e₁ e₂ e₃ e₄
  · refine ((B' j).2.2 q' p₁' _ _ hq' h₁').2 ?_
    rw [← (hτ q₁ q₁').2 t₁]
    exact (hτe _ _).1 (((B j).2.2 q p₁ _ _ hqv h₁).1 hqe)

end GlobalTheory.Relabel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationGenericFibreCartesianToModelBundleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), ∃ (w₀ : W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))), IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧ NormW U w₀ ρ ∧ w.IsGen ∧ IsRigidificationPullbackCompatibleIso w (jK R) ρ U.LG.rig ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : H0 U.LG.L k) (th : SecA A F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J) (J'), Good U.LG.L z J → Good A.L z J' → sval σ (r ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) z J = (wVal w z J J' (r ≫ (snd (TFK (R := R) F) A.A).left) ^ (k : ℤ)).val * VVRank.sv A.A th r z J') → ∃ σ' : U.SecGF F k, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) ∧ ∀ s, U.ExpandsG F k σ' s → U.ExpandsF F k w₀ th s := by
  first | exact @GlobalTheory.Ex.GenericFibre.exists_isoData | exact GlobalTheory.Ex.GenericFibre.exists_isoData | (intros; apply GlobalTheory.Ex.GenericFibre.exists_isoData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuesIsoCommActionAbelianPartTorsionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuesIso_comm_action_abelianPart_torsion : GlobalTheory.UT.LL → BrGtSt → AllS fun {E} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → ∀ k : ℕ, 0 < k → Labels A u r M ν' J k → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) → ∀ (x : 𝓞 E) (y y' : A.N.A), y ^ k = 1 → (letI := H.starRing; A.ν.eA y' = A.ν.eA y ≫ a.oa.onB.act x → ν'.eA (J.φ y') = ν'.eA (J.φ y) ≫ M.P.oD.onB.act x) := by
  first | exact @GlobalTheory.Ex.ActPt.main | exact GlobalTheory.Ex.ActPt.main | (intros; apply GlobalTheory.Ex.ActPt.main <;> assumption)
end

