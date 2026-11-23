module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3123
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GensOfPsiUnitOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemExactOfGeometricUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.GSep.ExactSums

theorem congMod_pi_iff {X : Type} [AddCommGroup X] {s : ℕ} (N : ℕ) (a b : Fin s → X) :
    CongMod N a b ↔ ∀ v, CongMod N (a v) (b v) := by
  constructor
  · rintro ⟨w, hw⟩ v
    exact ⟨w v, by rw [hw]; rfl⟩
  · intro h
    choose w hw using h
    exact ⟨w, funext fun v => by rw [hw v]; rfl⟩

theorem labels {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (H : AddSubgroup S.Gam)
    {X : Type} [AddCommGroup X] (YY : S.Gam → X → Prop)
    (h1 : ∀ a, ∃ mu, YY a mu) (h2 : ∀ mu, ∃ a, YY a mu)
    (h3 : ∀ a mu mu', YY a mu → (YY a mu' ↔ CongMod (S.r * S.N) mu' mu))
    (h4 : ∀ a a' mu mu', YY a mu → YY a' mu' → YY (a + a') (mu + mu'))
    (hH : ∀ a, a ∈ H ↔ YY a 0) :
    ∃ l : X → S.Gam, (∀ mu, YY (l mu) mu) ∧
      (∀ τ ∈ S.perp H, ∀ a mu, YY a mu → eStd S.g _ τ a = eStd S.g _ τ (l mu)) ∧
      ∀ mu κ, (∀ τ ∈ S.perp H, eStd S.g _ τ (l mu) = eStd S.g _ τ (l κ)) ↔ CongMod (S.r * S.N) mu κ := by
  obtain ⟨l, hl⟩ : ∃ l : X → S.Gam, ∀ mu, YY (l mu) mu := ⟨fun mu => (h2 mu).choose, fun mu => (h2 mu).choose_spec⟩
  have sub : ∀ a a' mu, YY a mu → YY a' mu → a - a' ∈ H := by
    intro a a' mu ha ha'
    obtain ⟨b, hb⟩ := h2 (-mu)
    have e1 := h4 _ _ _ _ ha hb
    have e2 := h4 _ _ _ _ ha' hb
    rw [add_neg_cancel] at e1 e2
    have := H.sub_mem ((hH _).2 e1) ((hH _).2 e2)
    simpa using this
  have D1 : ∀ τ ∈ S.perp H, ∀ a mu, YY a mu → eStd S.g _ τ a = eStd S.g _ τ (l mu) := by
    intro τ hτ a mu ha
    have h0 : eStd S.g _ τ (a - l mu) = 0 := hτ _ (sub a (l mu) mu ha (hl mu))
    have e : a = (a - l mu) + l mu := (sub_add_cancel a (l mu)).symm
    conv_lhs => rw [e]
    rw [eStd_add_right, h0, zero_add]
  refine ⟨l, hl, D1, fun mu κ => ⟨fun h => ?_, fun h τ hτ => ?_⟩⟩
  · have hb : l mu - l κ ∈ H := by
      rw [← TestBasis.perp_perp S H]
      intro τ hτ
      have e : eStd S.g _ τ (l mu) = eStd S.g _ τ (l mu - l κ) + eStd S.g _ τ (l κ) := by
        rw [← eStd_add_right, sub_add_cancel]
      have h0 : eStd S.g _ τ (l mu - l κ) = 0 := by rw [h τ hτ] at e; simpa using e.symm
      rw [eStd_swap, h0, neg_zero]
    have e1 := h4 _ _ _ _ (hl κ) ((hH _).1 hb)
    rw [add_sub_cancel, add_zero] at e1
    obtain ⟨w, hw⟩ := (h3 _ _ _ (hl mu)).1 e1
    exact ⟨-w, by rw [hw, smul_neg, add_neg_cancel_right]⟩
  · exact (D1 τ hτ (l κ) mu ((h3 _ _ _ (hl κ)).2 h)).symm


open Classical GlobalTheory.Poinc.Sep.ExactSums in
theorem exact_of_isGeo : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : O → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (Φ : VPre bar q W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam), GlobalTheory.GSep.IsGeo X₁ z₁ act x₀ Φ lab → Φ.Exact (X₁.S.r * X₁.S.N) := by
  intro O _ bar q s W X₁ z₁ act x₀ Φ lab hG
  obtain ⟨hdiv, hlab, hmem⟩ := hG
  obtain ⟨sg, eps, hlink⟩ := GlobalTheory.T.thetaConstants_translate_eq_twisted_sums O X₁ z₁ act x₀ hdiv
  intro y κ c
  obtain ⟨𝔪, hT⟩ := hmem y
  haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)⟩
  haveI : IsDomain X₁.o₁ := X₁.ar.ded.toIsDomain
  obtain ⟨yy1, yy2, yy3, yy4⟩ := _root_.GlobalTheory.GSep.Labels.yy_hom O X₁ z₁ act (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) _ _ 𝔪
  have hH := _root_.GlobalTheory.GSep.mem_HH_iff_yy_zero O X₁ z₁ act x₀ hdiv (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) _ _ 𝔪
  obtain ⟨l, -, hlY, hlC⟩ := labels X₁.S (X₁.S.HH X₁.M z₁) 𝔪.YY yy1 yy2 yy3 yy4 hH

  let φ : X₁.o₁ →+* X₁.M.Z.presheaf.stalk z₁ :=
    (X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))
  have hsh : ∀ b : X₁.M.O z₁, X₁.M.stalkHom z₁ ((X₁.M.stalkEquiv z₁).symm b) = b := fun b => by
    rw [← RatModel.coe_stalkEquiv (M := X₁.M), RingEquiv.apply_symm_apply]
  have hφ : ∀ a, X₁.M.stalkHom z₁ (φ a) = algebraMap X₁.o₁ X₁.Ω₁ a := fun a => hsh _

  let zt := φ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))
  have hzt : X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) := hφ _
  have hunitV : IsUnit (((X₁.S.r * X₁.S.N : ℕ) : Φ.V y)) := by
    have := X₁.S.unit.map ((Φ.ev y).comp φ)
    rwa [map_natCast] at this
  have hω : IsPrimitiveRoot (Φ.ev y zt) (X₁.S.r * X₁.S.N) := by
    have h0 : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
      X₁.S.prim.pow (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) 2) (sq _)
    exact isPrimitiveRoot_map' ((Φ.ev y).comp φ) hunitV.ne_zero h0

  let TT := X₁.S.TT X₁.M z₁
  have hmemO : ∀ τ : TT, algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ ∈ X₁.M.O z₁ :=
    fun τ => by rw [mul_div_assoc]; exact mul_mem (Subalgebra.algebraMap_mem _ _) (hdiv.2 _)
  let hτ : TT → X₁.M.Z.presheaf.stalk z₁ := fun τ => (X₁.M.stalkEquiv z₁).symm ⟨_, hmemO τ⟩
  have hhτ : ∀ τ : TT, X₁.M.stalkHom z₁ (hτ τ) =
      algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ := fun τ => hsh _

  have hcard : IsUnit ((Fintype.card TT : ℕ) : X₁.o₁) := by
    have h1 : Fintype.card TT ∣ Fintype.card X₁.S.Gam := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact AddSubgroup.card_addSubgroup_dvd_card _
    have h2 : IsUnit ((Fintype.card X₁.S.Gam : ℕ) : X₁.o₁) := by
      rw [Fintype.card_fun, ZMod.card, Nat.cast_pow]; exact X₁.S.unit.pow _
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast h1) h2
  obtain ⟨u, hu⟩ := hcard.map φ
  let d := ((u⁻¹ : (X₁.M.Z.presheaf.stalk z₁)ˣ) : X₁.M.Z.presheaf.stalk z₁)
  have hd : Φ.ev y d * (Fintype.card TT : Φ.V y) = 1 := by
    rw [← map_natCast (Φ.ev y), ← map_mul, ← map_natCast φ, ← hu, Units.inv_mul, map_one]

  let w : (Fin s → Φ.X y) → TT → ZMod (X₁.S.r * X₁.S.N) := fun mu τ => (sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) (l mu)
  have hw : ∀ mu τ τ', w mu (τ + τ') = w mu τ + w mu τ' := fun mu τ τ' => by
    simp only [w, AddSubgroup.coe_add, eStd_add_left, smul_add]
  have hsg : ∀ a b : ZMod (X₁.S.r * X₁.S.N), (sg : ℤ) • a = (sg : ℤ) • b → a = b := fun a b h => by
    have := congrArg (fun t => (sg : ℤ) • t) h
    have e : ((sg : ℤ) * sg) = 1 := by rcases Int.units_eq_one_or sg with h | h <;> simp [h]
    simpa only [smul_smul, e, one_smul] using this
  have hwκ : ∀ mu, (∀ τ, w mu τ = w κ τ) ↔ ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu v) (κ v) := fun mu => by
    rw [← congMod_pi_iff, ← hlC mu κ]
    exact ⟨fun h τ hτ' => hsg _ _ (h ⟨τ, hτ'⟩), fun h τ => by simp only [w, h τ τ.2]⟩
  have hlab' : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁ := fun c => by
    rw [← SetLike.mem_coe, ← hlab]; exact Set.mem_range_self c
  have hsum : ∀ τ : TT, SumI (maximalIdeal (Φ.V y)) (fun mu => Φ.ev y zt ^ (w mu τ).val * Φ.term y mu c) (Φ.ev y (hτ τ)) :=
    fun τ => hlink (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) _ _ 𝔪 Φ.Q lab hlab' (Φ.term y) hT c τ τ.2 zt (hτ τ) hzt
      (hhτ τ) (fun mu => w mu τ) (fun a mu hY => by simp only [w, hlY τ τ.2 a mu hY])
  let f : (Fin s → Φ.X y) → Φ.V y := fun mu => if ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu v) (κ v) then Φ.term y mu c else 0
  have hf := sumI_fourier (maximalIdeal (Φ.V y)) hω (Φ.ev y d) hd w hw κ (fun mu => Φ.term y mu c) (fun τ => Φ.ev y (hτ τ))
    hsum f (fun mu h => if_pos ((hwκ mu).1 h)) (fun mu h => if_neg fun h' => h ((hwκ mu).2 h'))
  refine ⟨d * ∑ τ : TT, zt ^ (-(w κ τ)).val * hτ τ, isClassSum_of_sumI Φ y _ κ c (RingHom.id _) _ f
    (fun mu h => if_pos h) (fun mu h => if_neg h) ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_mul, map_sum, map_pow] using hf

end GlobalTheory.GSep.ExactSums
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftSquareZeroArtinianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ t)), ∃ o : GlobalTheory.UPel.HT.Obj b N t, Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)) := by
  first | (exact @GlobalTheory.UPel.HT.exists_sqZero_lift) | (exact GlobalTheory.UPel.HT.exists_sqZero_lift) | (intros; apply GlobalTheory.UPel.HT.exists_sqZero_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationsBasisCount
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTCount

theorem count : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ f : Fin (D.a * (D.n - 1)) → (HdR o₀.A →ₗ[k] HdR o₀.A), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) ∧ ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃! c : Fin (D.a * (D.n - 1)) → k, ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (∑ j, c j • f j x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, t = spMap β := ⟨(Spec.preimage t).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.UPel.HT.CorrForm.exists_isCorrForm_obj p D R b N hN hNp k t o₀
  obtain ⟨f, hfKS, huniq⟩ := GlobalTheory.T.harrisTaylor_kodairaSpencer_directions_dim p D R b N hN hNp k t o₀ β hβ φ hφ
  refine ⟨f, fun j => GlobalTheory.T.harrisTaylor_realise_kodairaSpencer_direction p D R b N hN hNp k t o₀ β hβ φ hφ (f j) (hfKS j), fun o' m' => ?_⟩
  obtain ⟨g, hgKS, hg⟩ := GlobalTheory.T.harrisTaylor_firstOrder_hodge_eq_kodairaSpencer_graph p D R b N hN hNp k t o₀ β hβ φ hφ o' m'
  obtain ⟨c, hc, hcu⟩ := huniq g hgKS
  refine ⟨c, fun x hx => ?_, fun c' hc' => hcu c' fun x hx => ?_⟩
  · refine (_root_.GlobalTheory.KSGraph.isFilLift_iff_sub_mem k o₀.A o'.A m'.φ m'.cart o'.ab x hx (g x) _ (hg x hx)).2 ?_
    rw [← neg_sub]; exact neg_mem (hc x hx)
  · have := (_root_.GlobalTheory.KSGraph.isFilLift_iff_sub_mem k o₀.A o'.A m'.φ m'.cart o'.ab x hx (g x) _ (hg x hx)).1 (hc' x hx)
    rw [← neg_sub]; exact neg_mem this

end GlobalTheory.HTCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialCohomologyVanishing
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem laurentPolynomial_cohomology_strictlyHenselian_vanishing : GlobalTheory.EtC.C5 := fun q _ A _ hA hq n i => GlobalTheory.T.multiplicativeGroup_cohomology_strictlyHenselian q A hA hq n i

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFamilyFromRegularBaseCoordinates
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.FamFrom

theorem rescale_inv_psi {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (χ : D.X) :
    (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) (fun y => (g y)⁻¹)).psi χ = D.psi χ := by
  show GlobalTheory.UU.scaleGen _ (GlobalTheory.UU.scaleGen _ _) = _
  unfold GlobalTheory.UU.scaleGen
  generalize D.psi χ = b
  cases b
  congr 1
  funext j
  have h1 : unitOn ((g χ)⁻¹) * unitOn (g χ) = 1 := by
    have hu : unitOn ((g χ)⁻¹ * g χ) = unitOn ((g χ)⁻¹) * unitOn (g χ) := map_mul _ _ _
    rw [← hu, inv_mul_cancel]
    exact Units.ext (map_one _)
  rw [← _root_.mul_assoc, ← map_mul, h1, map_one, _root_.one_mul]

theorem isPullDeg_rescale_inv {W R : Type} [CommRing W] [IsDomain W] [CommRing R] [IsDomain R] (φ : W →+* R)
    (D₀ : DegPre W) (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (hD : IsPullDeg φ D₀ D) :
    ∃ h : IsPullDeg φ D₀ (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) (fun y => (g y)⁻¹)),
      (∀ y, h.xe y = hD.xe y) ∧ h.e.hom.left = hD.e.hom.left :=
  ⟨{ hD with psi_pr := fun x => (rescale_inv_psi D g x).symm ▸ hD.psi_pr x }, fun _ => rfl, rfl⟩

end GlobalTheory.UCanon.FamFrom

namespace GlobalTheory.UCanon.FamFrom

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (iw : L.W →+* R), Function.Injective iw → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, s (.inl i) ∈ maximalIdeal R ∧ s (.inl i) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → (∀ i y, 0 ≤ ε (.inl i) y y) → (∀ y, y ≠ 0 → 0 < ∑ i, ε (.inl i) y y) → Nontrivial L.D.X → ∃ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), DivFrom L P.D.toPre P.oD iw s ε e ∧ IsMonomial P.D.toPre (fun i => s (.inl i)) (fun i => (l.M' : ℤ) • pull e.toLinearMap (ε (.inl i))) := by
  intro E _ _ _ H Dl l c L R _ _ _ hB iw hiw m N s ε hε hs hu hpos hdef hnt
  letI := H.starRing
  have hw : H.w0 + star H.w0 = 1 := GlobalTheory.TauTwist.halfUnit_add_star H
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  letI iD : Module (𝓞 E) (mulDeg L.D l.M').X := L.mod
  obtain ⟨he0, hb0, hU0, oa0, hoa0, hW0⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws L.W L.D (𝓞 E) L.oa H.w0 l.M' L.even L.bimult L.w0 L.gen
  have hne : ∃ i, ε (.inl i) ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_ne (0 : L.D.X)
    have h := hdef y hy
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
    exact ⟨i, fun h0 => hi (by rw [h0]; rfl)⟩
  obtain ⟨D'', hD, iM, e, hxe, hPE, hTB, hPI, hfin, ⟨oa1, hoa1, hPW⟩, hmono, -, -, -⟩ :=
    GlobalTheory.UTautData.main L.W R (maximalIdeal R) iw hiw (mulDeg L.D l.M') (𝓞 E) oa0 H.w0 hw he0 hb0 hW0 hU0
      (fun i => s (.inl i)) (fun i => (hs i).2) (fun i => (hs i).1) (fun j => (hu j).unit) l.M' hM
      (fun i => ε (.inl i)) (fun j => ε (.inr j)) (fun i => hε _) hpos (fun j => hε _) hdef hne

  set T := GlobalTheory.UTautData.taut D'' e H.w0 (fun i => s (.inl i)) (fun i => (hs i).2) (fun j => (hu j).unit) l.M'
    (fun i => ε (.inl i)) (fun j => ε (.inr j)) with hT
  let D1 : DegData R (maximalIdeal R) := ⟨T, hPE, hTB, hPI, hfin⟩
  obtain ⟨t, P, hPD, hmod, hoD⟩ := GlobalTheory.T.exists_semiAbelian_pelUniformisation_of_norm H R hB D1 (inst := iM) oa1 hPW
  have key : ∀ (Dd : DegData R (maximalIdeal R)) [im : Module (𝓞 E) Dd.toPre.X] (od : Dd.toPre.OAct (𝓞 E)),
      Dd = D1 → HEq im iM → HEq od oa1 → ∃ e' : Dd.toPre.X ≃ₗ[𝓞 E] L.D.X,
        DivFrom L Dd.toPre od iw s ε e' ∧
        IsMonomial Dd.toPre (fun i => s (.inl i)) (fun i => (l.M' : ℤ) • pull e'.toLinearMap (ε (.inl i))) := by
    rintro Dd im od rfl h1 h2
    have h1' := eq_of_heq h1
    subst im
    have h2' := eq_of_heq h2
    subst od
    letI : Module (𝓞 E) D1.toPre.X := iM
    let e₁ : D1.toPre.X ≃ₗ[𝓞 E] L.D.X := e
    refine ⟨e₁, ?_, hmono⟩
    obtain ⟨h2p, hx2, he2⟩ := isPullDeg_rescale_inv iw (mulDeg L.D l.M') D''
      (GlobalTheory.UTautData.scaleFn (GlobalTheory.UTautData.coordsK (fun i => s (.inl i)) (fun i => (hs i).2) (fun j => (hu j).unit))
        H.w0 (GlobalTheory.UTautData.forms l.M' (fun i => pull e.toLinearMap (ε (.inl i)))
          (fun j => pull e.toLinearMap (ε (.inr j))))) hD
    refine ⟨_, h2p, fun y => ?_, fun y => (hx2 y).trans (hxe y).symm, fun x => ?_⟩
    · rw [inv_inv]
      refine (GlobalTheory.UTautData.scaleFn_coe _ _ _ _ _ _ _ _).trans ?_
      rw [Fintype.prod_sum_type]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        have h3 : e₁ (H.w0 • y) = H.w0 • e₁ y := e₁.map_smul H.w0 y
        show _ = algebraMap R (FractionRing R) (s (.inl i)) ^ ((l.M' : ℤ) * ε (.inl i) (e₁ y) (H.w0 • e₁ y))
        rw [← h3]
        rfl
      · refine Finset.prod_congr rfl fun j _ => ?_
        have h3 : e₁ (H.w0 • y) = H.w0 • e₁ y := e₁.map_smul H.w0 y
        show _ = algebraMap R (FractionRing R) (s (.inr j)) ^ ((l.M' : ℤ) * ε (.inr j) (e₁ y) (H.w0 • e₁ y))
        rw [← h3, (hu j).unit_spec]
        rfl
    · rw [he2]
      have h := hoa1 x
      rw [hoa0] at h
      exact h
  obtain ⟨e', h1, h2⟩ := key P.D P.oD hPD hmod hoD
  exact ⟨t, P, e', h1, h2⟩

end GlobalTheory.UCanon.FamFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparateTwoPointsNefBigStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separate_two_points_nef_big : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsNef ℂ N → IsBig ℂ N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → 0 < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  first | exact @GlobalTheory.NefBigSep.separate_nef_big | exact GlobalTheory.NefBigSep.separate_nef_big | (intros; apply GlobalTheory.NefBigSep.separate_nef_big <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioInEmbeddingRange
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2 Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigTop.Fun

theorem sqRatio_mem_of {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T)
    (W : G.Weil) (S : GridChoice W Set.univ) (ρ : RealMatch W) (c : Fin D.R.m → Fin D.R.m → T → ℂ)
    (hstd : IsStdChar D W.ψ (-1)) (hN : NumbersIn D.what₂.embLL S μ₀)
    (hC : ∀ i j t, SquareNonzero W S.B ρ t i j ∧ c i j t ≠ 0) (hK : ∀ i j t, IsSquareConst W S.B ρ t i j (c i j t))
    (hLN : ∀ i j : Fin D.R.m, (∀ t, ∃ Λ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ ∧
      ∀ s : ℤ, 1 - (GlobalTheory.SqTop.e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0))
    (hTX : ∀ i j : Fin D.R.m, ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X ∧ X.IsConst W.ψ W.θ c0)
    (hTW : ∀ (i j : Fin D.R.m) (t : T) (c c₀ : ℂ) (A A' WW : HSp D) (X : Tri T A A' WW)
      (c0 : T → ℂ) (Λ Λ₀ : ℂ → ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c → SquareNonzero W S.B ρ μ₀ i j →
      IsSquareConst W S.B ρ μ₀ i j c₀ → IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 → GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
      GlobalTheory.CMVal.IsHeckeL (nuH G μ₀ i j) Λ₀ → ∃ u : Fin (pp D j + qq D j) → ℂ,
        (∀ k, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (u k) 1) ∧
        ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧
          c / c₀ * ∏ k ∈ range (qq D j), Λ (eTop D i j + k + 1 : ℕ) / Λ₀ (eTop D i j + k + 1 : ℕ) =
            D.what₂.embLL ζ * (∏ k, u k) * (c0 t / c0 μ₀) *
              ∏ k ∈ range (pp D j), Λ (eTop D i j + qq D j - k : ℕ) / Λ₀ (eTop D i j + qq D j - k : ℕ))
    (hBF : ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
      ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam)
    (i j : Fin D.R.m) (t : T) : c i j t / c i j μ₀ ∈ Set.range D.what₂.embLL := by
  have hF : ∀ z : ℂ, z ∈ Set.range D.what₂.embLL ↔ z ∈ D.what₂.embLL.fieldRange := fun z => Iff.rfl

  obtain ⟨A₀, A₀', WW₀, X₀, -, hX₀, -⟩ := hTX i j
  obtain ⟨A, A', WW, X, hX, hS⟩ := hN.bottom i j ⟨A₀, A₀', WW₀, X₀, hX₀⟩
  obtain ⟨lam, hlam⟩ := hBF i j A A' WW X hX
  have hI := hX.is
  have hi' : ∀ t P g, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P g) X.fd' X.m' := fun t P g =>
    (_root_.GlobalTheory.DefSourceInt.theta_integral_source_definite D W.ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (hI.weil' t) (GlobalTheory.ConstRatio.posDef_of_std hX.std')
      hI.meas'.1 hI.meas'.2 (GlobalTheory.Chain.InnerSteps.theta_pureTensorO hI.isVac.1 hI.isVac.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f hI t).2 P)).1 g
  have hr := hS.rationalSums (fun t P g => hlam.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1 t P g) hi'
  have hrat := GlobalTheory.ConstRatio.ratIn_of_definite hI (GlobalTheory.ConstRatio.posDef_of_std hX.std) (GlobalTheory.ConstRatio.posDef_of_std hX.std')
    (GlobalTheory.ConstRatio.posDef_of_std hX.stdW) hlam hr μ₀
  haveI : Nonempty T := ⟨μ₀⟩
  have hcst : X.IsConst W.ψ W.θ lam := hlam.isConst

  obtain ⟨Λ, hΛ, hΛne⟩ := hLN i j t
  obtain ⟨Λ₀, hΛ₀, hΛ₀ne⟩ := hLN i j μ₀
  obtain ⟨u, hu, ζ, -, heq⟩ := hTW i j t (c i j t) (c i j μ₀) A A' WW X lam Λ Λ₀ (hC i j t).1 (hK i j t) (hC i j μ₀).1
    (hK i j μ₀) hX hcst hΛ hΛ₀
  rw [hF]
  obtain ⟨hn1, -, -, hn4, -, -, -, hn8, hn9⟩ := Model.tower_numbers (D := D) i j
  have hne : ∀ L : ℂ → ℂ, (∀ s : ℤ, 1 - (e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → L s ≠ 0) →
      ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j → L (n : ℂ) ≠ 0 := fun L h n h1 h2 => by
    have := h n (by omega) (by exact_mod_cast h2)
    simpa using this
  have hs : ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j →
      Λ (n : ℂ) / Λ₀ (n : ℂ) ∈ D.what₂.embLL.fieldRange ∧ Λ (n : ℂ) / Λ₀ (n : ℂ) ≠ 0 := fun n h1 h2 =>
    ⟨(hF _).1 (hN.ratios i j t Λ Λ₀ hΛ hΛ₀ n h1 (by omega) (hne Λ₀ hΛ₀ne n h1 h2)),
      div_ne_zero (hne Λ hΛne n h1 h2) (hne Λ₀ hΛ₀ne n h1 h2)⟩
  have hP1 : ∀ k ∈ range (qq D j), Λ ((eTop D i j + k + 1 : ℕ) : ℂ) / Λ₀ ((eTop D i j + k + 1 : ℕ) : ℂ) ∈
      D.what₂.embLL.fieldRange ∧ Λ ((eTop D i j + k + 1 : ℕ) : ℂ) / Λ₀ ((eTop D i j + k + 1 : ℕ) : ℂ) ≠ 0 := fun k hk =>
    hs _ (by omega) (by have := mem_range.1 hk; omega)
  have hP2 : ∀ k ∈ range (pp D j), Λ ((eTop D i j + qq D j - k : ℕ) : ℂ) / Λ₀ ((eTop D i j + qq D j - k : ℕ) : ℂ) ∈
      D.what₂.embLL.fieldRange := fun k hk =>
    (hs _ (by have := mem_range.1 hk; omega) (by omega)).1
  have hU : (∏ k, u k) ∈ D.what₂.embLL.fieldRange := prod_mem fun k _ => by
    obtain ⟨b, g, g', -, -, h⟩ := hu k
    rw [h, mul_one]
    exact RingHom.mem_fieldRange.2 ⟨_, rfl⟩
  have hl : lam t / lam μ₀ ∈ D.what₂.embLL.fieldRange := by
    obtain ⟨-, y, hy⟩ := hrat t
    exact RingHom.mem_fieldRange.2 ⟨_, hy⟩
  rw [eq_div_of_mul_eq (prod_ne_zero_iff.2 fun k hk => (hP1 k hk).2) heq]
  exact div_mem (mul_mem (mul_mem (mul_mem (RingHom.mem_fieldRange.2 ⟨ζ, rfl⟩) hU) hl) (prod_mem hP2))
    (prod_mem fun k hk => (hP1 k hk).1)


end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifPullbackOfCanonicalOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TChart.Taut

theorem unif_pull_of_canonOn : ∀ {g n : ℕ} {φ : InvFun ℤ} (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  intro g n φ C G₁ _ _ P hM hC V' _ _ _ θ hV hθ hs D' e hD
  obtain ⟨Q', e', hr, hd⟩ := hD
  have h₁ := _root_.GlobalTheory.PullFrom.pullData_of_dataFrom C.T C.R V' θ C.iw C.s C.form n C.Q C.e Q' _ hs C.data hd
  have h₂ := GlobalTheory.Mum.pullData_refines C.R V' θ C.Q Q' _ D'.toPre D'.tau_bimult e' h₁ hr
  refine _root_.GlobalTheory.Mum.canon_pull_unif C.R V' θ hM.1 hV hθ C.Q _ G₁ P hM.2.2.1 hC ?_ D' _ h₂
  rw [genericPoint_eq_bot_of_affine]
  show (∏ k, C.t k) ∉ Ideal.comap θ (⊥ : PrimeSpectrum V').asIdeal
  rw [Ideal.mem_comap, map_prod]
  exact Finset.prod_ne_zero_iff.2 fun k _ => hs (.inl k)

end GlobalTheory.TChart.Taut
end

