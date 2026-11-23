module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedPrimeLogSumOscillationBoundLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsBigSmallFactorBounds
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaGeneratorsLeastValueOverLevelPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafPullbackRelationsBasic
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem restrictO_bijective_of_basis {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    {C' : Type} [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X')
    (hcov : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u)
    (hdir : ∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) :
    Function.Bijective (CoefMap.restrict (OAff s') G).pull1 ∧
      Function.Bijective (CoefMap.restrict (OAff s') G).pull2 := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') G H hcov hdir
  have hv2 := _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt (OAff s') G H hcov hdir
  exact ⟨⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩,
    _root_.GlobalTheory.CatCoh.pull2_restrict_injective_of_comma _ _ hs hg hv, _root_.GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma _ _ hs hg hv hv2⟩

section

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}

theorem pairResO_bijective (φ : X' ⟶ X) (s' : X' ⟶ Sp R') :
    Function.Bijective (pairRes φ s').pull1 ∧ Function.Bijective (pairRes φ s').pull2 :=
  restrictO_bijective_of_basis s' (pairFst φ) (pair_cover_affine φ s') (exists_pair_below_two φ s')

theorem triResO_injective (ψ : X'' ⟶ X') (φ : X' ⟶ X) (s'' : X'' ⟶ Sp R'') :
    Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 := by
  have key : ∀ c : HO1 s'', (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull1 c := fun c ↦ by
    rw [← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c
  intro x y e
  obtain ⟨x0, rfl⟩ := (pairResO_bijective (ψ ≫ φ) s'').1.2 x
  obtain ⟨y0, rfl⟩ := (pairResO_bijective (ψ ≫ φ) s'').1.2 y
  rw [key, key] at e
  rw [(restrictO_bijective_of_basis s'' _ (triple_cover_affine ψ φ s'')
    (exists_triple_below_two ψ φ s'')).1.1 e]

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem isPullO_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO1 s) (a' : HO1 s') (a'' : HO1 s'')
    (p : IsPullO h a a') (p' : IsPullO h' a' a'') : IsPullO h'' a a'' := by
  refine triResO_injective ψ φ s'' ?_
  have p0 : (pairPull h).pull1 a = (pairRes φ s').pull1 a' := p
  have p1 : (pairPull h').pull1 a' = (pairRes ψ s'').pull1 a'' := p'
  have e1 : (cechTripleRestrictComposite ψ φ s'').pull1 ((pairPull h'').pull1 a) =
      (cechTriplePullbackSecond h').pull1 ((pairPull h).pull1 a) := by
    rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
      ((pairPull h).comp (cechTriplePullbackSecond h')) { app U := 𝟙 _ } (fun U b ↦ by
        erw [mp_id]
        exact congrArg (fun q ↦ q.hom b) (Scheme.Hom.appLE_comp_appLE ψ φ U.unop.1.2.2.1 U.unop.1.2.1.1
          U.unop.1.1.1 U.unop.2.2 U.unop.2.1)) a
  have e2 : (cechTriplePullbackSecond (φ := φ) h').pull1 ((pairRes φ s').pull1 a') =
      (cechTripleRestrictFirst ψ φ s'').pull1 ((pairPull h').pull1 a') := by
    rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) a'
  have e3 : (cechTripleRestrictFirst ψ φ s'').pull1 ((pairRes ψ s'').pull1 a'') =
      (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 a'') := by
    rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a''
  rw [e1, p0, e2, p1, e3]

theorem isPullO2_cup (h : φ ≫ s = s' ≫ spMap σ) (a b : HO1 s) (a' b' : HO1 s')
    (p : IsPullO h a a') (q : IsPullO h b b') :
    IsPullbackH2Structure h (GlobalTheory.CatCoh.cup _ a b) (GlobalTheory.CatCoh.cup _ a' b') := by
  have p0 : (pairPull h).pull1 a = (pairRes φ s').pull1 a' := p
  have q0 : (pairPull h).pull1 b = (pairRes φ s').pull1 b' := q
  unfold IsPullbackH2Structure
  rw [CoefMap.pullCohomologyTwo_cup, CoefMap.pullCohomologyTwo_cup, p0, q0]

end

theorem pullO_basic : ∀ (R : Type) [CommRing R] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R) (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap (RingHom.id R)), Function.Bijective (pairRes φ s').pull2 ∧ (∀ a b a' b', IsPullO h a a' → IsPullO h b b' → IsPullbackH2Structure h (GlobalTheory.CatCoh.cup _ a b) (GlobalTheory.CatCoh.cup _ a' b')) ∧ ∀ (X'' : Scheme.{0}) (s'' : X'' ⟶ Sp R) (ψ : X'' ⟶ X') (h' : ψ ≫ s' = s'' ≫ spMap (RingHom.id R)) (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (RingHom.id R)) a a' a'', IsPullO h a a' → IsPullO h' a' a'' → IsPullO h'' a a'' :=
  fun _ _ _ _ _ s' φ h ↦ ⟨(pairResO_bijective φ s').2, fun a b a' b' p q ↦ isPullO2_cup h a b a' b' p q,
    fun _ _ _ h' h'' a a' a'' p p' ↦ isPullO_comp h h' h'' a a' a'' p p'⟩

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfWeightNumerical
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.RefSum

theorem len_mul_total_le {T F m q N B Sg b l x C₁ C₂ K U : ℝ} (hT : 1 ≤ T) (hF : 1 ≤ F) (hm : 1 ≤ m) (hq : q ≤ m)
    (hB : 0 ≤ B) (hb : 1 ≤ b) (hl : 1 ≤ l) (hx : 1 ≤ x) (h1 : 0 ≤ C₁) (h2 : 0 ≤ C₂) (hK : 0 ≤ K)
    (a1 : T * (B + 1) ≤ C₁ * b) (a2 : T * Sg ≤ C₁ * b) (a3 : T * N ^ 3 ≤ C₂ * b) (a4 : F * m * b * l * x ≤ C₂ * U) :
    T * (40 * ((F * m * (B + 1) + F * (Sg + 2 * q * B)) * (K * l) * (K * x) + F * N ^ 3 * (K * l) + (2 * B + 1))) ≤
      40 * (4 * C₁ * K ^ 2 + C₂ * K + 2 * C₁) * C₂ * U := by
  have hcb : 0 ≤ C₁ * b := by positivity
  have b1 : T * B ≤ C₁ * b := by nlinarith
  have b2 : q * (T * B) ≤ m * (C₁ * b) := mul_le_mul hq b1 (by positivity) (by positivity)
  have b3 : m * (T * (B + 1)) ≤ m * (C₁ * b) := mul_le_mul_of_nonneg_left a1 (by positivity)
  have b4 : C₁ * b ≤ m * (C₁ * b) := le_mul_of_one_le_left hcb hm
  have b5 : T * (m * (B + 1) + (Sg + 2 * q * B)) ≤ 4 * (m * (C₁ * b)) := by nlinarith
  have c1 : T * (m * (B + 1) + (Sg + 2 * q * B)) * (F * (K * l) * (K * x)) ≤
      4 * (m * (C₁ * b)) * (F * (K * l) * (K * x)) := mul_le_mul_of_nonneg_right b5 (by positivity)
  have hmx : 1 ≤ m * x := one_le_mul_of_one_le_of_one_le hm hx
  have c2 : T * N ^ 3 * (F * (K * l)) ≤ C₂ * b * (F * (K * l)) := mul_le_mul_of_nonneg_right a3 (by positivity)
  have c3 : C₂ * b * (F * (K * l)) ≤ C₂ * b * (F * (K * l)) * (m * x) := le_mul_of_one_le_right (by positivity) hmx
  have hall : 1 ≤ F * l * (m * x) := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hF hl) hmx
  have c4 : C₁ * b ≤ C₁ * b * (F * l * (m * x)) := le_mul_of_one_le_right hcb hall
  have c5 : T * (2 * B + 1) ≤ 2 * (C₁ * b) := by nlinarith
  have c6 : (4 * C₁ * K ^ 2 + C₂ * K + 2 * C₁) * (F * m * b * l * x) ≤ (4 * C₁ * K ^ 2 + C₂ * K + 2 * C₁) * (C₂ * U) :=
    mul_le_mul_of_nonneg_left a4 (by positivity)
  nlinarith

theorem log_top_le {T B b l C₁ C₂ : ℝ} (hT : 1 ≤ T) (hB : 0 ≤ B) (hb : 1 ≤ b) (hl : 1 ≤ l) (h1 : 0 ≤ C₁)
    (a1 : T * (B + 1) ≤ C₁ * b) (a2 : Real.log b ≤ C₂ * l) : Real.log (2 * B + 1) ≤ (2 * C₁ + C₂ + 1) * l := by
  have b1 : B + 1 ≤ C₁ * b := by nlinarith
  have b2 : Real.log (2 * B + 1) ≤ Real.log ((2 * C₁ + 1) * b) := Real.log_le_log (by positivity) (by nlinarith)
  rw [Real.log_mul (by positivity) (by positivity)] at b2
  have b3 : Real.log (2 * C₁ + 1) ≤ 2 * C₁ + 1 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  nlinarith

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem sumAt_of_sizes {PP C₁ C₂ : ℝ} (h1 : 0 ≤ C₁) (h2 : 0 ≤ C₂) (u1 : Weight (dat p i))
    (hw : WtAt p i PP C₁ u1) (hn : NumAt p i PP C₂) :
    GlobalTheory.RefSum.SumAt p i PP
      (40 * (4 * C₁ * (2 * C₁ + C₂ + 1) ^ 2 + C₂ * (2 * C₁ + C₂ + 1) + 2 * C₁) * C₂) u1 := by
  obtain ⟨hs, hk, B, Sg, hwt, a1, a2, hT1⟩ := hw
  obtain ⟨hl, hb, n1, hx, n2, n3, n4, n5, n6, n7⟩ := hn
  have hT1' : (1 : ℝ) ≤ lenT p i PP := by exact_mod_cast hT1
  have hexp := _root_.GlobalTheory.RefSum.ThetaExp.expBd_thA _ _ (dat p i) D.R.f D.R.k D.R.m (nCol (dat p i)) B Sg u1 hs hk hwt
  have hd : p.T.Q.H.d = D.host.d := p.fw.laws.pins.1.1
  have htwo := GlobalTheory.CharDepth.twoPlaces_host D p.T.Q.H hd
  have hvd : ∀ q, 0 ≤ D.host.vdH q := D.host.vdH_nonneg
  obtain ⟨hsum, h2S, hunr⟩ := UpperTheory.KR.small_vd_sum D.host.toHostAx
  have hN : (dat p i).p + (dat p i).q = D.R.r := by
    have := hs.1
    unfold Ranks.r
    omega
  have hF : (1 : ℝ) ≤ D.R.f := by
    have hn : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hs.2.2.2.1
  have hq : ((dat p i).q : ℝ) ≤ D.R.m := by exact_mod_cast hs.2.1
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  set K : ℝ := 2 * C₁ + C₂ + 1 with hK
  have hK1 : 1 ≤ K := by linarith
  have hK2 : C₂ ≤ K := by linarith
  have hKl : C₂ * L.sc.L ≤ K * L.sc.L := mul_le_mul_of_nonneg_right hK2 (by linarith)
  have hnum := _root_.GlobalTheory.SumBound.primeSum_eOf D.R.f D.R.r D.R.k D.R.m (2 * B + 1) (B + 1) (D.R.f * (Sg + 2 * (dat p i).q * B))
    D.host.vdH (K * L.sc.L) (K * Real.log (Real.log L.sc.x)) D.host.small {D.host.q, D.host.d} hexp.1
    ((Nat.cast_nonneg _).trans hexp.2.2.1) hvd (hN ▸ hs.1) hs.2.2.1 hs.2.2.2.1
    (one_le_mul_of_one_le_of_one_le hK1 hl) (one_le_mul_of_one_le_of_one_le hK1 hx)
    (by push_cast; exact log_top_le hT1' hB hb hl h1 a1 n1) (n4.trans hKl)
    (hsum.trans (mul_le_mul_of_nonneg_left (n5.trans hKl) (by norm_num)))
    (n3.trans (mul_le_mul_of_nonneg_right hK2 (by linarith))) Finset.card_le_two
    (fun q hq => (n7 q hq).trans (by nlinarith))
  refine ⟨_, _, _, hnum, ?_, fun q hqp _ => ?_⟩
  · push_cast
    exact len_mul_total_le hT1' hF hm hq hB hb hl hx h1 h2 (by linarith) a1 a2 n6 n2
  · have := _root_.GlobalTheory.RefSum.oscLe_eOf _ _ (dat p i) _ (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c D.R.f D.R.k D.R.m (2 * B + 1) (B + 1) _ _ hs hexp
      D.host.vdH D.host.small {D.host.q, D.host.d} hvd (fun r _ hr => (htwo r hr).2.1) h2S (by simp [hd])
      (fun r hr hr2 hrR => hunr r hr hr2
        (fun h => hrR (by simp [h])) (fun h => hrR (by simp [h]))) q
    rw [hN] at this
    simpa only [if_pos hqp.out] using this

end Point

end GlobalTheory.RefSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulEqZeroOfFlatLinearlyDisjointSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

open scoped TensorProduct

namespace GlobalTheory.Desc

theorem tmul_sum_eq_zero_of_linDisj {R R₁ F K : Type} [CommRing R] [CommRing R₁] [Field F] [Field K] [Algebra R R₁]
    [Algebra R F] (c : R₁ →+* K) (θ : F →+* K) (hc₀ : Function.Injective (algebraMap R F))
    (hθ : θ.comp (algebraMap R F) = c.comp (algebraMap R R₁)) (hL : LinDisj (algebraMap R F) c θ) :
    ∀ (n : ℕ) (u : Fin n → F) (r : Fin n → R₁), ∑ i, θ (u i) * c (r i) = 0 → ∑ i, u i ⊗ₜ[R] r i = 0 := by
  have hθ' : ∀ b : R, θ (algebraMap R F b) = c (algebraMap R R₁ b) := fun b => RingHom.congr_fun hθ b
  intro n
  induction n with
  | zero => intro u r _; simp
  | succ n ih =>
    intro u r h
    by_cases hind : ∀ b : Fin (n+1) → R, ∑ i, algebraMap R F (b i) * u i = 0 → b = 0
    · have hr := hL (n+1) u hind r (by rw [← h]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
      subst hr; simp
    · push_neg at hind
      obtain ⟨b, hb, hb0⟩ := hind
      obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
        by_contra hc; push_neg at hc; exact hb0 (funext hc)
      have hdj : algebraMap R F (b j) ≠ 0 := by
        intro h0; apply hj; apply hc₀; rw [h0, map_zero]
      obtain ⟨w, hw⟩ : ∃ w : Fin n → F, ∀ i, w i = u (j.succAbove i) / algebraMap R F (b j) := ⟨_, fun _ => rfl⟩
      have hrel : algebraMap R F (b j) * u j +
          ∑ i : Fin n, algebraMap R F (b (j.succAbove i)) * u (j.succAbove i) = 0 := by
        rw [← Fin.sum_univ_succAbove (fun i => algebraMap R F (b i) * u i) j]; exact hb
      have hu : ∀ i, u (j.succAbove i) = b j • w i := by
        intro i; rw [Algebra.smul_def, hw i]; field_simp
      have hsum : ∑ i : Fin n, algebraMap R F (b (j.succAbove i)) * w i = - u j := by
        have : ∑ i : Fin n, algebraMap R F (b (j.succAbove i)) * w i =
            (∑ i : Fin n, algebraMap R F (b (j.succAbove i)) * u (j.succAbove i)) / algebraMap R F (b j) := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by rw [hw i]; ring
        rw [this, eq_neg_of_add_eq_zero_right hrel]; field_simp
      have huj : u j = - ∑ i : Fin n, b (j.succAbove i) • w i := by
        simp only [Algebra.smul_def]; rw [hsum, neg_neg]
      have key : ∑ i, u i ⊗ₜ[R] r i =
          ∑ i : Fin n, w i ⊗ₜ[R] (b j • r (j.succAbove i) - b (j.succAbove i) • r j) := by
        rw [Fin.sum_univ_succAbove _ j]
        simp only [TensorProduct.tmul_sub, Finset.sum_sub_distrib, ← TensorProduct.smul_tmul, ← hu]
        rw [huj, TensorProduct.neg_tmul, TensorProduct.sum_tmul]
        abel
      rw [key]
      apply ih
      have e1 : ∀ i, θ (w i) * c (b j • r (j.succAbove i) - b (j.succAbove i) • r j) =
          θ (u (j.succAbove i)) * c (r (j.succAbove i)) - c (r j) * θ (algebraMap R F (b (j.succAbove i)) * w i) := by
        intro i
        rw [hu i]
        simp only [Algebra.smul_def, map_sub, map_mul, hθ']
        ring
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum, hsum, map_neg]
      have h' := h
      rw [Fin.sum_univ_succAbove _ j] at h'
      linear_combination h'

theorem tmul_sum_eq_zero_of_flat_linDisj : ∀ (R R₁ A F K : Type) [CommRing R] [CommRing R₁] [CommRing A] [Field F] [Field K] [Algebra R A] [Algebra R R₁], Module.Flat R R₁ → ∀ (c₀ : R →+* F) (e : A →+* F) (c : R₁ →+* K) (θ : F →+* K), Function.Injective c₀ → Function.Injective e → e.comp (algebraMap R A) = c₀ → θ.comp c₀ = c.comp (algebraMap R R₁) → LinDisj c₀ c θ → ∀ (n : ℕ) (a : Fin n → A) (r : Fin n → R₁), ∑ i, θ (e (a i)) * c (r i) = 0 → ∑ i, a i ⊗ₜ[R] r i = 0 := by
  intro R R₁ A F K _ _ _ _ _ _ _ hflat c₀ e c θ hc₀ he hec hθ hL n a r h
  letI : Algebra R F := c₀.toAlgebra
  let eA : A →ₐ[R] F := { e with commutes' := fun x => RingHom.congr_fun hec x }
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := R₁) eA.toLinearMap he
  apply hinj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero]
  simp only [LinearMap.rTensor_tmul]
  exact tmul_sum_eq_zero_of_linDisj (R := R) c θ hc₀ hθ hL n (fun i => e (a i)) r h

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeReferenceExponentThetaWeightLevelLeOne
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RefLevel

theorem lattice_terms_le {κ R s N d g' V r φ cst : ℝ} (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hs : 0 ≤ s) (hsN : s ≤ N) (hV : 0 < V)
    (hr : 0 < r) (hφ : 0 ≤ φ) (hg' : 0 < g') (hc : κ * N ^ 3 * (R * N / 4 + 2 * d ^ 2) / g' ≤ cst) :
    (R * s * (κ * s ^ 3 * (r * φ)) / (4 * g') + 2 * d ^ 2 * (κ * s ^ 3 * (r * φ)) / g') / (r * V) ≤ cst * φ / V := by
  have hN : 0 ≤ N := hs.trans hsN
  calc (R * s * (κ * s ^ 3 * (r * φ)) / (4 * g') + 2 * d ^ 2 * (κ * s ^ 3 * (r * φ)) / g') / (r * V)
      = κ * s ^ 3 * (R * s / 4 + 2 * d ^ 2) / g' * φ / V := by field_simp
    _ ≤ κ * N ^ 3 * (R * N / 4 + 2 * d ^ 2) / g' * φ / V := by gcongr
    _ ≤ cst * φ / V := by gcongr

theorem not_isUnit_of_vV_ne_zero (S : CDVR) (N : ℕ) (h : vV S.V ((N : ℕ) : S.Fr) ≠ 0) : ¬ IsUnit ((N : ℕ) : S.V) := by
  intro hu
  apply h
  have h2 : valV S.V (algebraMap S.V S.Fr ((N : ℕ) : S.V)) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (mem_nonunits_iff.1 h) hu
  rw [map_natCast] at h2
  unfold vV
  rw [h2]
  simp

theorem vV_pos {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p ≠ 0) {la : HeightOneSpectrum (𝓞 K)}
    (hla : (p : 𝓞 K) ∈ la.asIdeal) {T : CDVR} {io : K →+* T.Fr} {k : ℕ} (ho : OverLa la T.V io k) :
    0 < vV T.V (p : T.Fr) := by
  have h := ho.2 (p : K)
  rw [map_natCast] at h
  rw [h]
  refine mul_pos (by exact_mod_cast ho.1) ?_
  have h1 : la.valuation K (p : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) (p : 𝓞 K)).2 hla
    have e : ((p : 𝓞 K) : K) = (p : K) := map_natCast (algebraMap (𝓞 K) K) p
    rw [← e]
    exact this
  have h0 : la.valuation K (p : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hp)
  have := (WithZero.log_lt_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at this
  unfold vLa
  omega

theorem coprime_level (D : D7) (k : Fin 2) : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
  have hc : D.host.g k % (D.host.QS * D.host.q * D.host.d) = 1 := D.ntypes.g_cond k
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc]
  simp

theorem refExp_le_of_halfSplit (D : D7) (T : Core D) (hM : LawsM T) (j : ℕ) (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ) (hDom : Dom a n) (hLast : LastPos (T.Q.Dw j) a)
    (hrn : 2 * D.R.r ≤ n) (g g' : ℕ) (ρ ρ' : 𝓞 D.host.E) (hH : HalfSplit T.Q.l g g' ρ ρ')
    (hcop : Nat.Coprime (g * g') (D.host.QS * D.host.q * D.host.d)) (hg : 4 * DF (T.Q.Dw j) a + 4 ≤ g)
    (hg' : 4 * DF (T.Q.Dw j) a + 4 ≤ g') (hM0 : (DF (T.Q.Dw j) a : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < g')
    (hc : rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 *
      ((D.R.r : ℝ) * (2 * D.R.f * D.R.m) / 4 + 2 * (DF (T.Q.Dw j) a : ℝ) ^ 2) / g' ≤ cst) :
    refExp_vp (T.U j) cst (wtZ a n) g ≤ ((1 : ℝ) : EReal) := by
  rw [refExp_vp_le_iff]
  intro la S io e ho y hy φ hφ
  obtain ⟨st, nab, hn⟩ :=
    GlobalTheory.CanonConn.exists_isNab_uncond D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  have hst := GlobalTheory.PowGerm.starSt _ T.Q.H st hn.1
  subst hst
  letI := T.Q.H.starRing
  obtain ⟨-, -, -, -, -, hE, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hM.pins
  obtain ⟨hpq, hr1, -⟩ := hnum j hj
  have hq : (T.Q.Dw j).q = D.R.m - j := (hM.pins.2.2.2 j hj).2.1
  obtain ⟨hTot, hcusp⟩ := GlobalTheory.thetaRules_exist_and_cusp D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) hr1
    (hM.unf j hj) nab hn
  obtain ⟨S', io', y', r, C, P, hy', hr, hFT, hTI, hφ', hOv, hvv, hnv⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisedChart_scale D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io y hy φ hφ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S'.V
  obtain ⟨⟨Q, hQ⟩, -⟩ :=
    GlobalTheory.PowData.exists_powData D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' C P ϖ hϖ
  obtain ⟨s, hs, hΦ, b, hb1, hb2⟩ :=
    GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' _ hφ' C P ϖ hϖ Q hQ
  obtain ⟨m, hmfin, hmle, hmeq⟩ :=
    GlobalTheory.ThetaLow.thetaRule_bounded_below D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hn g g' ρ ρ' hH hcop a n
  obtain ⟨hgp, hgp', hne, hMl, hρ, hρ', hMb, hsp, -⟩ := hH
  have hρs : ρ * star ρ = (g : 𝓞 D.host.E) := hρ
  have hρs' : ρ' * star ρ' = (g' : 𝓞 D.host.E) := hρ'
  have hV : 0 < vV S.V (g : S.Fr) := vV_pos hgp.ne_zero la.2 ho
  have hV' := hvv g hgp.ne_zero
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  have hsN : (s : ℝ) ≤ 2 * D.R.f * D.R.m := by
    rw [hE, hq] at hs
    exact_mod_cast hs.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℕ, vV S.V (g : S.Fr) = e₀ := ⟨_, (Int.toNat_of_nonneg hV.le).symm⟩
  have he₀0 : 0 < e₀ := by omega
  have hA := GlobalTheory.LevelPrimePoint.least_value_le GlobalTheory.ChF.hodgeTate_inclusion_chart D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c nab hn hTot S' io' y' C hFT P hTI hy' ϖ hϖ Q hQ _ _ s b hΦ hb1 hb2 g g' hgp hgp' hne hMl ρ ρ'
    hρs hρs' hMb hsp.1 hsp.2 (not_isUnit_of_vV_ne_zero S' g (by rw [hV']; exact (mul_pos hrZ hV).ne')) a n (r * e₀)
    hDom.1 (by rw [hpq]; exact hrn) (by omega) (Nat.mul_pos hr he₀0) (by omega) hg'
    (lt_of_le_of_lt (by gcongr) hM0)
  have hν : (∏ τ : D.host.E →+* ℂ, (io' (embK T.Q.c τ (star ρ * star ρ'))) ^ (∑ i : Fin ((T.Q.Dw j).mult τ), a (τ, i))) =
      io' (nrm (T.Q.Dw j) T.Q.c a (star ρ * star ρ')) := by
    unfold nrm
    simp only [map_prod, map_pow]
  have hν0 : nrm (T.Q.Dw j) T.Q.c a (star ρ * star ρ') ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ fun h0 => ?_
    have h1 : (star ρ * star ρ') * (ρ * ρ') = ((g * g' : ℕ) : 𝓞 D.host.E) := by
      rw [Nat.cast_mul, ← hρs, ← hρs']; ring
    have h2 := congrArg (embK T.Q.c τ) h1
    rw [map_mul, h0, zero_mul, map_natCast] at h2
    exact (Nat.cast_ne_zero.2 (Nat.mul_ne_zero hgp.ne_zero hgp'.ne_zero)) h2.symm
  rw [hν, hpq, hV', he₀, nval_of_ne ((map_ne_zero io').2 hν0)] at hA
  generalize nrm (T.Q.Dw j) T.Q.c a (star ρ * star ρ') = ν at hA hν0 hmeq
  generalize hN : ((vV S'.V (io' ν) : ℝ) / ((r * e₀ : ℕ) : ℝ) : ℝ) = N at hA
  have hlt : (⨅ f ∈ thGen (T.Q.Xo j) T.Q.c nab a n, nval S'.V (r * e₀) (evI y' f)) <
      ((1 + cst * φ / e₀ - N : ℝ) : EReal) := by
    rw [← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_sub] at hA
    refine hA.trans_lt (EReal.coe_lt_coe_iff.2 (sub_lt_sub_right ?_ _))
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have heR : (0 : ℝ) < e₀ := by exact_mod_cast he₀0
    have hgR : (4 : ℝ) * DF (T.Q.Dw j) a + 4 ≤ g := by exact_mod_cast hg
    have hd0 : (0 : ℝ) ≤ DF (T.Q.Dw j) a := Nat.cast_nonneg _
    rw [add_assoc, add_div]
    push_cast
    refine add_lt_add_of_lt_of_le ?_ (lattice_terms_le (by positivity) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsN heR hrR
      hφ.nonneg (by exact_mod_cast hgp'.pos) hc)
    rw [mul_div_assoc, mul_div_cancel_left₀ _ (mul_pos hrR heR).ne', div_lt_one (by linarith)]
    linarith
  simp only [iInf_lt_iff] at hlt
  obtain ⟨f, hf, hlt⟩ := hlt
  obtain ⟨t, ht0, htv, w, hw, hwe⟩ := GlobalTheory.T.cuspForm_clear_denominators_away_from_place D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j)
    (wtZ a n) ⟨f, hcusp a n hDom hLast f hf⟩ m hmfin (hmle f hf) la.1 (-vLa la.1 ν) fun v hv => by
      have h := hmle f hf la.1 v hv
      rw [hmeq la.1 (Or.inl la.2)] at h
      rw [Int.cast_neg]
      exact h
  have ho' := hOv la.1 e ho
  refine (iInf₂_le w hw).trans ?_
  show nval S.V (vV S.V (g : S.Fr)).toNat (evI y (w : Rul (T.Q.Xo j) T.Q.c)) ≤ _
  rw [hwe, evI_smul, he₀, Int.toNat_natCast, ← hnv nab hn a n e₀ t f hf, nval_mul, nval_of_ne ((map_ne_zero io').2 ht0),
    ho'.2 t, htv, neg_neg, ← ho'.2 ν, hN]
  refine (add_le_add le_rfl hlt.le).trans (le_of_eq ?_)
  rw [← EReal.coe_add, ← EReal.coe_add]
  congr 1
  push_cast
  ring

theorem refExp_level_le_one : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ k : Fin 2, refExp_vp (T.U j) cst (wtZ a n) (D.host.g k) ≤ ((1 : ℝ) : EReal) := by
  intro D T hM EX j hj a n cst hDom hLast _ hrn hJ k
  obtain ⟨π, π', hH⟩ := GlobalTheory.SplitLevel.level_halfSplit D T hM EX
  obtain ⟨k', ρ, ρ', hk⟩ : ∃ (k' : Fin 2) (ρ ρ' : 𝓞 D.host.E), HalfSplit T.Q.l (D.host.g k) (D.host.g k') ρ ρ' := by
    fin_cases k
    · exact ⟨1, π, π', hH⟩
    · exact ⟨0, π', π, hH.symm⟩
  exact refExp_le_of_halfSplit D T hM j hj a n cst hDom hLast hrn _ _ ρ ρ' hk
    (Nat.Coprime.mul_left (coprime_level D k) (coprime_level D k')) (hJ k).1 (hJ k').1 (hJ k').2.1 (hJ k').2.2

end GlobalTheory.RefLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMulSymPairMemSpanBalancedTensorsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transpose_mul_symPair_mem_span_balancedTensors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (R : Type) [CommRing R] (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (B : Matrix (Fin n) (Fin n') R), (∀ (τ σ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (Dw.mult σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0) → ∀ P : GlobalTheory.LogKSDiv.PairIx H Dw, ∃ cf : Fin Dw.dim → R, _root_.Matrix.transpose B * GlobalTheory.LogKSDiv.symPair (R := R) e P * B = ∑ k, cf k • GlobalTheory.LogKSDiv.symPair (R := R) e' (ε' k) := by
  first | exact @GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span | exact GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span | (intros; apply GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span <;> assumption)
end

