module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRankEqRankThetaGroupOfPointPerp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeUnitaryClassicalTraitCentre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzLieConditionModuleIffIdealLeKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section
namespace GlobalTheory.UPel.HT.LieLin
open Matrix

theorem ringHom_mapMatrix_algebraMap_scalar {B T : Type} [CommRing B] [CommRing T] (f : B →+* T) {n : ℕ} (x : B) :
    f.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) x) = algebraMap T (Matrix (Fin n) (Fin n) T) (f x) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

theorem list_prod_matrixActionAfterRingHom_sub_apply {O T : Type} [CommRing O] [CommRing T] {n : ℕ} {B : Type} [CommRing B]
    (M : O →+* Matrix (Fin n) (Fin n) B) (f : B →+* T) {a : ℕ} (c : Fin a → O) (τ : Fin a → (O →+* T))
    (v : Fin n → T) :
    (List.ofFn fun i => matAct M f (c i) - algebraMap T (Module.End T (Fin n → T)) (τ i (c i))).prod v =
      (List.ofFn fun i => (M (c i)).map f - algebraMap T (Matrix (Fin n) (Fin n) T) (τ i (c i))).prod *ᵥ v := by
  have h : (List.ofFn fun i => matAct M f (c i) - algebraMap T (Module.End T (Fin n → T)) (τ i (c i))) =
      (List.ofFn fun i => (M (c i)).map f - algebraMap T (Matrix (Fin n) (Fin n) T) (τ i (c i))).map
        (Matrix.toLinAlgEquiv' (R := T) (n := Fin n)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply, map_sub, AlgEquiv.commutes]
    rfl
  rw [h, ← map_list_prod]
  rfl

theorem lieMod_matAct_iff_lieIdeal_le_ker : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
  (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (T : Type) [CommRing T] (f : B →+* T),
    LieMod (matAct M f) D.ω (f (βB b.ρ)) (fun i => (f.comp βB).comp (b.t i)) ↔ lieIdeal b βB M ≤ RingHom.ker f := by
  intro p _ D R _ b B _ βB n M T _ f
  set g : R →+* T := f.comp βB with hg
  set τ : Fin D.a → (𝓞 D.F →+* T) := fun i => g.comp (b.t i) with hτ
  set ρ' : T := g b.ρ with hρ'
  set Nh : 𝓞 D.F →+* Matrix (Fin n) (Fin n) T := f.mapMatrix.comp M with hNh
  let Am : T →+* Matrix (Fin n) (Fin n) T := algebraMap T (Matrix (Fin n) (Fin n) T)
  set P : (Fin D.a → 𝓞 D.F) → Matrix (Fin n) (Fin n) T :=
    fun c => (List.ofFn fun i => (M (c i)).map f - Am (τ i (c i))).prod with hP
  set Q : Matrix (Fin n) (Fin n) T := Nh D.ω - Am (g ((D.tr : R) - b.ρ)) with hQ

  have hmap : ∀ c, f.mapMatrix (lieMat b βB M c) = P c * Q := by
    intro c
    rw [lieMat, map_mul, map_list_prod, List.map_ofFn]
    congr 1
    · congr 2; funext i; rw [Function.comp_apply, map_sub, ringHom_mapMatrix_algebraMap_scalar]; rfl
    · rw [map_sub, ringHom_mapMatrix_algebraMap_scalar]; rfl
  have hdec : ∀ v, (∃ w : Fin D.a → (Fin n → T), (∀ i, w i ∈ eigSub (matAct M f) (τ i)) ∧ v = ∑ i, w i) ↔
      ∀ c, P c *ᵥ v = 0 := by
    intro v
    have hcomax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => τ i x - τ j x) = ⊤ := by
      intro i j hij
      have h := congrArg (Ideal.map g) (b.comax i j hij)
      rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
      convert h using 3
      funext x
      simp [hτ]
    rw [GlobalTheory.T.eigenDecomposition_iff_shiftedProducts_kill_comaximal (𝓞 D.F) T (Fin n → T) (matAct M f) D.a τ hcomax v]
    simp only [list_prod_matrixActionAfterRingHom_sub_apply, hP]
    rfl

  have hω : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hρ : ρ' * ρ' - (D.tr : T) * ρ' + (D.nm : T) = 0 := by
    have := congrArg g b.ρ_root
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    rw [hρ']; linear_combination this
  have hquad : (Nh D.ω - Am ρ') * Q = 0 := by
    have hX : Nh D.ω * Nh D.ω - Am (D.tr : T) * Nh D.ω + Am (D.nm : T) = 0 := by
      have := congrArg Nh hω
      simpa [map_intCast] using this
    have hs : g ((D.tr : R) - b.ρ) = (D.tr : T) - ρ' := by simp [hρ']
    rw [hQ, hs]
    calc (Nh D.ω - Am ρ') * (Nh D.ω - Am ((D.tr : T) - ρ'))
        = Nh D.ω * Nh D.ω - Am (ρ' + ((D.tr : T) - ρ')) * Nh D.ω + Am (ρ' * ((D.tr : T) - ρ')) := by
          rw [map_add (f := _), map_mul, sub_mul, mul_sub, mul_sub, add_mul, ← Algebra.commutes ((D.tr : T) - ρ') (Nh D.ω)]
          abel
      _ = Nh D.ω * Nh D.ω - Am (D.tr : T) * Nh D.ω + Am (D.nm : T) := by
          congr 2
          · congr 2; ring
          · congr 1; linear_combination -hρ
      _ = 0 := hX
  have hAm : ∀ (x : T) (v : Fin n → T), Am x *ᵥ v = x • v := by
    intro x v
    simp only [Am, Algebra.algebraMap_eq_smul_one]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hact : ∀ v, matAct M f D.ω v = Nh D.ω *ᵥ v := fun v => rfl
  have hs : g ((D.tr : R) - b.ρ) = (D.tr : T) - ρ' := by simp [hρ']

  have hu : IsUnit (ρ' - ((D.tr : T) - ρ')) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = 4 * D.nm - D.tr ^ 2 := ⟨(4 * D.nm - D.tr ^ 2).toNat,
      Int.toNat_of_nonneg (by have := D.disc_neg; omega)⟩
    have hkp : k.Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
      intro hd
      apply D.disc_p
      have : (p : ℤ) ∣ (k : ℤ) := Int.natCast_dvd_natCast.2 hd
      rw [hk] at this
      have h2 : D.tr ^ 2 - 4 * D.nm = -(4 * D.nm - D.tr ^ 2) := by ring
      rw [h2]; exact (dvd_neg).2 this
    have hkT : IsUnit (k : T) := by
      have := (b.unit k hkp).map g
      simpa using this
    have hsq : (ρ' - ((D.tr : T) - ρ')) * (ρ' - ((D.tr : T) - ρ')) = -(k : T) := by
      have : ((k : ℤ) : T) = ((4 * D.nm - D.tr ^ 2 : ℤ) : T) := by rw [hk]
      push_cast at this
      rw [this]; linear_combination 4 * hρ
    have : IsUnit ((ρ' - ((D.tr : T) - ρ')) * (ρ' - ((D.tr : T) - ρ'))) := by
      rw [hsq]; exact hkT.neg
    exact isUnit_of_mul_isUnit_left this
  constructor
  · intro hL
    rw [lieIdeal, Ideal.span_le]
    rintro x ⟨c, i, j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have he : f (lieMat b βB M c i j) = ((P c * Q) *ᵥ Pi.single j 1) i := by
      rw [Matrix.mulVec_single_one, ← hmap]
      rfl
    rw [he, ← Matrix.mulVec_mulVec]
    set w := Q *ᵥ Pi.single j 1 with hw
    have hwe : matAct M f D.ω w = ρ' • w := by
      have h0 : ((Nh D.ω - Am ρ') * Q) *ᵥ Pi.single j 1 = 0 := by rw [hquad, Matrix.zero_mulVec]
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, hAm, sub_eq_zero] at h0
      rw [hact, ← hw] at *
      exact h0
    obtain ⟨w', hw'⟩ := hL w hwe
    have := (hdec w).1 ⟨w', hw'⟩ c
    rw [this]; rfl
  · intro hI v hv
    apply (hdec v).2
    intro c
    have hz : P c * Q = 0 := by
      ext i j
      have := hI (Ideal.subset_span ⟨c, i, j, rfl⟩)
      rw [RingHom.mem_ker] at this
      rw [← hmap]
      simpa using this
    have hQv : Q *ᵥ v = (ρ' - ((D.tr : T) - ρ')) • v := by
      rw [hQ, Matrix.sub_mulVec, hAm, ← hact, hv, hs]
      change ρ' • v - ((D.tr : T) - ρ') • v = _
      rw [← sub_smul]
    have h1 : (ρ' - ((D.tr : T) - ρ')) • (P c *ᵥ v) = 0 := by
      rw [← Matrix.mulVec_smul, ← hQv, Matrix.mulVec_mulVec, hz, Matrix.zero_mulVec]
    exact (hu.smul_eq_zero).1 h1

end GlobalTheory.UPel.HT.LieLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelledUnitaryTraitsLatticesEquivConnectedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.Poinc.FibLat

namespace GlobalTheory.UPoinc.GFib

theorem TT_le_HH_of_uIsLab {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf} (X : USetup C) {p : ℕ} [Fact p.Prime]
    {z : X.M.Z} (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (h : UIsLab X ct yy)
    (hker : yy.ker = X.S.HH X.M z) : X.S.TT X.M z ≤ X.S.HH X.M z := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, -, G, _, α, β, -, -, -, y₀, -, u, lb, j, -, hlab, -⟩ := h
  have hk : lb.yy.ker ≤ yy.ker := fun a ha => by
    have h0 : lb.yy a = QuotientAddGroup.mk 0 := by rw [AddMonoidHom.mem_ker.1 ha]; rfl
    have := hlab a 0 h0
    rw [map_zero] at this
    exact AddMonoidHom.mem_ker.2 this
  intro t ht
  rw [← hker]
  refine hk ?_
  have h1 : t ∈ (X.S.rechart c₀ hc R' fg frac hth hev).perp lb.yy.ker := fun h hh => ht h (hker ▸ hk hh)
  have h2 := lb.isoFree.1 h1
  rwa [ThetaSys.perp_perp] at h2

end GlobalTheory.UPoinc.GFib

theorem GlobalTheory.UPoinc.GFib.labelled_lattices_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (_ : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → ∀ (ct ct' : UCTrait X p z) (y y' : Sp (OO p) ⟶ Y.Z), y ≫ q = ct.y → y' ≫ q = ct'.y → ∀ (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct'.T.P.D.toPre.X), UIsLabW X wi ct yy → UIsLabW X wi ct' yy' → ∃ θ : ct.T.P.D.toPre.X ≃+ ct'.T.P.D.toPre.X, (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (θ μ)) ∧ ∀ (a : 𝓞 E) v, θ (a • v) = a • θ v := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi Y U₀ EE FinalForm q hO hE hP hpt p _ z hz ct ct' y y' hy hy' yy yy' hl hl'
  have hker := _root_.GlobalTheory.UPoinc.uIsLab_onto_and_ker E H Dw hpq l Xo cf C X p z ct yy hl.uIsLab
  have hker' := _root_.GlobalTheory.UPoinc.uIsLab_onto_and_ker E H Dw hpq l Xo cf C X p z ct' yy' hl'.uIsLab
  have hTH := GlobalTheory.UPoinc.GFib.TT_le_HH_of_uIsLab X ct yy hl.uIsLab hker.2
  obtain ⟨f, gγ, hf, hg⟩ := _root_.GlobalTheory.UPoinc.GFib.endo_torsion_ext E H Dw l Xo cf C X wi Y U₀ EE FinalForm q hO hE hpt z hTH
  have hL : 0 < X.S.r * X.S.N := Nat.mul_pos (by have := X.S.r_pos; omega) (by have := X.S.N_ge; omega)
  have hprim : IsPrimitiveRoot (X.S.ζ ^ (X.S.r * X.S.N)) (X.S.r * X.S.N) :=
    X.S.prim.pow (by positivity) (by ring)
  let ζ : X.o₁ˣ := (hprim.isUnit hL.ne').unit
  have hζ : IsPrimitiveRoot (ζ : X.o₁) (X.S.r * X.S.N) := hprim
  obtain ⟨s, σ, hs, hσ, hc⟩ :=
    _root_.GlobalTheory.UPoinc.GFibCentre.latAt_centre E H Dw hpq l Xo cf C X wi Y U₀ EE FinalForm q hO hE hP hpt p z f gγ hf hg ζ hζ
  obtain ⟨c, hc1, hc2⟩ := hc ct y hy yy hl
  obtain ⟨c', hc1', hc2'⟩ := hc ct' y' hy' yy' hl'
  have hx : q.base (y (cPt p)) = z := by
    rw [← Scheme.Hom.comp_apply, hy, ct.cen]
  have hx' : q.base (y' (cPt p)) = z := by
    rw [← Scheme.Hom.comp_apply, hy', ct'.cen]

  have hrk : ∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt FinalForm.G w r₀ := by
    obtain ⟨r₀, -, ⟨e₀⟩⟩ := _root_.GlobalTheory.ThetaDvr.TorRank.rkAt_tt_equiv X.o₁ X.Ω₁ X.S X.ρ Y U₀ EE FinalForm X.big hO hE (y (cPt p))
    refine ⟨r₀, fun w hw => ?_⟩
    obtain ⟨r, hr, ⟨e⟩⟩ := _root_.GlobalTheory.ThetaDvr.TorRank.rkAt_tt_equiv X.o₁ X.Ω₁ X.S X.ρ Y U₀ EE FinalForm X.big hO hE w
    have hT : X.S.TT Y w = X.S.TT Y (y (cPt p)) := by
      simp only [ThetaSys.TT]
      rw [_root_.GlobalTheory.Poinc.HHFibre.HH_eq_of_hom X.o₁ X.Ω₁ X.S X.M Y q hpt X.hasDiv w,
        _root_.GlobalTheory.Poinc.HHFibre.HH_eq_of_hom X.o₁ X.Ω₁ X.S X.M Y q hpt X.hasDiv (y (cPt p))]
      simp only [hw, hx]
    have e₁ : (Fin r → ZMod (X.S.r * X.S.N)) ≃ (Fin r₀ → ZMod (X.S.r * X.S.N)) :=
      (e.symm.toEquiv.trans (by rw [hT])).trans
        e₀.toEquiv
    haveI : NeZero (X.S.r * X.S.N) := ⟨hL.ne'⟩
    have hcard := Fintype.card_congr e₁
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
    have h2 : 2 ≤ X.S.r * X.S.N := by
      have := X.S.r_pos; have := X.S.N_ge; nlinarith
    rwa [Nat.pow_right_injective h2 hcard] at hr
  have hmove := _root_.GlobalTheory.UPoinc.GFib.latAt_const_on_fibre X.o₁ X.Ω₁ Y FinalForm.G FinalForm.semi _ q z hz hrk (𝓞 E) _ f (fun a => (hf a).1) gγ ζ
    (X.S.r * X.S.N) hL (Units.ext (by simpa using hζ.pow_eq_one)) X.S.unit (fun t => (hg t).1)
    (fun t w hw => (hg t).2.2 w hw) ct.T.P.D.toPre.X _ c _ _ hx hx' hc1
  haveI : IsDomain X.o₁ := (inferInstance : GlobalTheory.ZH.ArithBase X.o₁ X.Ω₁).ded.toIsDomain
  obtain ⟨θ, hθm, hθc⟩ := _root_.GlobalTheory.UPoinc.GFibUniq.latAt_unique X.o₁ X.Ω₁ Y FinalForm.G FinalForm.semi (𝓞 E) _ f gγ ζ (X.S.r * X.S.N) hL hζ
    X.S.unit ct.T.P.D.toPre.X ct'.T.P.D.toPre.X _ c _ c' _ hmove hc1'
  refine ⟨θ, fun a v hv => ?_, fun a v => ?_⟩
  · obtain ⟨a', ha'⟩ := hker'.1 (QuotientAddGroup.mk (θ v))
    have hd : a' - a ∈ X.S.HH X.M z := by
      rw [← ThetaSys.perp_TT]
      refine ThetaSys.mem_perp'.2 fun t ht => ?_
      have e1 := hc2' a' (θ v) ⟨t, ht⟩ ha'
      rw [hθc, hc2 a v ⟨t, ht⟩ hv] at e1
      have e2 := hs.mul_left_cancel e1
      rw [sub_eq_add_neg, eStd_add_right, eStd_neg_right, ← e2]
      exact add_neg_cancel _
    rw [← hker'.2, AddMonoidHom.mem_ker, map_sub, sub_eq_zero] at hd
    rw [← hd, ha']
  · obtain ⟨b, rfl⟩ := hσ a
    exact hθm b v
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LaHatMod

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

theorem valued_algebraMap (w : HeightOneSpectrum ℤ) (q : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) q) = w.valuation ℚ q :=
  valuedAdicCompletion_eq_valuation' w q

theorem exists_int_valued_sub_le (w : HeightOneSpectrum ℤ) {x : w.adicCompletion ℚ} (hx : Valued.v x ≤ 1)
    {c : ℚ} (hc0 : c ≠ 0) (hc : w.valuation ℚ c ≤ 1) :
    ∃ r : ℤ, Valued.v (x - (r : w.adicCompletion ℚ)) ≤ w.valuation ℚ c := by
  set c' : w.adicCompletion ℚ := algebraMap ℚ (w.adicCompletion ℚ) c
  have hc' : c' ≠ 0 := by
    simp only [c', ne_eq, map_eq_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective]; exact hc0
  have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v c' := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc')
  have hU : IsOpen ((fun y => (y - x) / c') ⁻¹' (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) :=
    (Valued.isOpen_valuationSubring _).preimage ((continuous_id.sub continuous_const).div_const c')
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (K := ℚ) w).exists_mem_open hU
    ⟨x, by simp [SetLike.mem_coe, sub_self, zero_div]⟩
  have hk' : Valued.v (x - algebraMap ℚ (w.adicCompletion ℚ) k) ≤ w.valuation ℚ c := by
    have h : Valued.v ((algebraMap ℚ (w.adicCompletion ℚ) k - x) / c') ≤ 1 := hk
    rw [map_div₀, div_le_one₀ hpos] at h
    rw [Valuation.map_sub_swap, ← valued_algebraMap]; exact h
  have hk1 : w.valuation ℚ k ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap ℚ (w.adicCompletion ℚ) k = x - (x - algebraMap ℚ (w.adicCompletion ℚ) k) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hx (hk'.trans hc))
  have hne : w.valuation ℚ c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer w hk1 (Units.mk0 _ hne)
  refine ⟨r, ?_⟩
  have hr' : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (k - algebraMap ℤ ℚ r)) ≤ w.valuation ℚ c := by
    rw [valued_algebraMap, Valuation.map_sub_swap]; exact hr.le
  have e : x - (r : w.adicCompletion ℚ) =
      (x - algebraMap ℚ (w.adicCompletion ℚ) k) + algebraMap ℚ (w.adicCompletion ℚ) (k - algebraMap ℤ ℚ r) := by
    rw [map_sub, algebraMap_int_eq, eq_intCast, map_intCast]; ring
  rw [e]
  exact (Valuation.map_add _ _ _).trans (max_le hk' hr')

variable {p : ℕ} [Fact p.Prime]

theorem valued_intCast (w : HeightOneSpectrum ℤ) (z : ℤ) :
    Valued.v ((z : w.adicCompletion ℚ)) ≤ 1 := by
  rw [← map_intCast (algebraMap ℚ (w.adicCompletion ℚ)), valued_algebraMap]
  have := w.valuation_le_one (K := ℚ) z
  simpa using this

theorem exists_int_add_prime_mul (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) (a : AfP p) (ha : IsIntAf a) :
    ∃ (z : ℤ) (a' : AfP p), IsIntAf a' ∧ a = (z : AfP p) + (l : AfP p) * a' := by
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hl).irreducible
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  let w0 : HeightOneSpectrum ℤ := ⟨Ideal.span {(l : ℤ)}, hmax.isPrime, by simpa using hl0⟩
  have hw0 : w0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    have hp : (p : ℤ) ∈ Ideal.span {(l : ℤ)} := by
      change (p : ℤ) ∈ w0.asIdeal; rw [h]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at hp
    have hd : l ∣ p := by exact_mod_cast hp
    rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) l hd) with h1 | h1
    · exact hl.ne_one h1
    · exact hlp h1
  let v0 : AwayP p := ⟨w0, hw0⟩
  have hlq0 : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hlv : ∀ w : HeightOneSpectrum ℤ, w.valuation ℚ (l : ℚ) ≤ 1 := fun w => by
    have := w.valuation_le_one (K := ℚ) (l : ℤ); simpa using this
  obtain ⟨z, hz⟩ := exists_int_valued_sub_le w0 (ha v0) hlq0 (hlv w0)
  refine ⟨z, (a - (z : AfP p)) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹, ?_, ?_⟩
  · intro v
    rw [mem_adicCompletionIntegers, map_mul, map_sub, map_intCast, AlgHom.commutes, Valuation.map_mul,
      valued_algebraMap, map_inv₀]
    have hne : v.1.valuation ℚ (l : ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 hlq0
    by_cases hv : v = v0
    · subst hv
      rw [mul_inv_le_iff₀ (zero_lt_iff.2 hne), _root_.one_mul]
      exact hz
    · have hnot : (l : ℤ) ∉ v.1.asIdeal := by
        intro hm
        apply hv
        have hle : Ideal.span {(l : ℤ)} ≤ v.1.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hm
        have heq := hmax.eq_of_le v.1.isPrime.ne_top hle
        exact Subtype.ext (HeightOneSpectrum.ext heq.symm)
      have h1 : v.1.valuation ℚ (l : ℚ) = 1 := by
        have := (valuation_eq_one_iff_notMem (v := v.1) (K := ℚ) (r := (l : ℤ))).2 hnot
        simpa using this
      rw [h1, inv_one, _root_.mul_one]
      exact (Valuation.map_sub _ _ _).trans (max_le (ha v) (valued_intCast v.1 z))
  · have e : (l : AfP p) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹ = 1 := by
      rw [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, mul_inv_cancel₀ hlq0, map_one]
    calc a = (z : AfP p) + (a - (z : AfP p)) * ((l : AfP p) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹) := by
          rw [e, _root_.mul_one]; ring
      _ = _ := by ring

theorem exists_int_add_mul (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (a : AfP p) (ha : IsIntAf a) :
    ∃ (z : ℤ) (a' : AfP p), IsIntAf a' ∧ a = (z : AfP p) + (n : AfP p) * a' := by
  induction n using Nat.recOnMul generalizing a with
  | zero => exact absurd hn (lt_irrefl 0)
  | one => exact ⟨0, a, ha, by simp⟩
  | prime l hl =>
    exact exists_int_add_prime_mul l hl (fun h => by
      subst h; exact hl.ne_one ((Nat.coprime_self _).1 hnp)) a ha
  | mul m k ihm ihk =>
    have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
    have hk : 0 < k := Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
    obtain ⟨hmp, hkp⟩ := Nat.coprime_mul_iff_left.1 hnp
    obtain ⟨z1, a1, h1, e1⟩ := ihm hm hmp a ha
    obtain ⟨z2, a2, h2, e2⟩ := ihk hk hkp a1 h1
    exact ⟨z1 + m * z2, a2, h2, by rw [e1, e2]; push_cast; ring⟩

end GlobalTheory.LKGeo.LaHatMod

namespace GlobalTheory.LKGeo

theorem exists_inAf_add_nsmul_of_mem_laHat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ), 0 < n → n.Coprime p →
    ∀ v ∈ LaHat D, ∃ (x : D.La) (w : TensorProduct ℚ (AfP p) (VQ D)), w ∈ LaHat D ∧ v = inAf D x + n • w := by
  intro p _ D n hn hnp v hv
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a, x, ha, rfl⟩ := hu
    obtain ⟨z, a', ha', e⟩ := LaHatMod.exists_int_add_mul n hn hnp a ha
    refine ⟨z • x, a' ⊗ₜ ((1 : ℚ) ⊗ₜ x), AddSubgroup.subset_closure ⟨a', x, ha', rfl⟩, ?_⟩
    have h1 : ((z : AfP p)) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = (1 : AfP p) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] (z • x)) := by
      rw [show (z : AfP p) = (z : ℚ) • (1 : AfP p) by rw [← Algebra.algebraMap_eq_smul_one, map_intCast],
        TensorProduct.smul_tmul, TensorProduct.smul_tmul',
        show (z : ℚ) • (1 : ℚ) = z • (1 : ℚ) by simp, TensorProduct.smul_tmul]
    have h2 : ((n : AfP p) * a') ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = n • (a' ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x)) := by
      rw [← nsmul_eq_mul, TensorProduct.smul_tmul']
    rw [e, TensorProduct.add_tmul, h1, h2, inAf]
  | zero => exact ⟨0, 0, zero_mem _, by simp [inAf]⟩
  | add u u' _ _ ih ih' =>
    obtain ⟨x, w, hw, e⟩ := ih
    obtain ⟨x', w', hw', e'⟩ := ih'
    refine ⟨x + x', w + w', add_mem hw hw', ?_⟩
    rw [e, e', inAf, inAf, inAf, TensorProduct.tmul_add, TensorProduct.tmul_add, smul_add]
    abel
  | neg u _ ih =>
    obtain ⟨x, w, hw, e⟩ := ih
    refine ⟨-x, -w, neg_mem hw, ?_⟩
    rw [e, inAf, inAf, TensorProduct.tmul_neg, TensorProduct.tmul_neg, smul_neg, neg_add]

end GlobalTheory.LKGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompPG
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp.LevelCmp

theorem lift_comp_pG {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ b.left)
    {A₂ : PolAV (Sp (FractionRing R))} {D₂ : DegData R (maximalIdeal R)} (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (β : D₂.toPre.P.A ≅ D.toPre.P.A) (hβ : ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left)
    (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left) (hh' : h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left) :
    h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom b 0 := by
  classical
  haveI := GlobalTheory.TorsionTranslate.mono_fst (I := maximalIdeal R) e G
  have hs : (thick R (maximalIdeal R) e ≫ a.left) ≫ G.hom = 𝟙 (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, Over.w a]; simp
  let ae : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶ thickObj R (maximalIdeal R) e G :=
    Over.homMk (pullback.lift (thick R (maximalIdeal R) e ≫ a.left) (𝟙 (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left) hs) (pullback.lift_snd _ _ _)
  have hae : ae.left ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left := pullback.lift_fst _ _ _
  have heq : h = (GlobalTheory.MumCmp.Transl.tr ae).left :=
    (cancel_mono (fstG (maximalIdeal R) e G).left).1 (by rw [hh', GlobalTheory.MumCmp.Transl.tr_fst hae])
  have h₁ := GlobalTheory.TorusCoord.im_mul (U.gt e) (toUnit (thickObj R (maximalIdeal R) e G) ≫ ae) (𝟙 (thickObj R (maximalIdeal R) e G))
  have h₂ : GlobalTheory.TorusCoord.im (U.gt e) (toUnit (thickObj R (maximalIdeal R) e G) ≫ ae) = toUnit _ ≫ b := by
    ext
    have := hab e ae.left (Over.w ae) hae
    simp [GlobalTheory.TorusCoord.im] at this ⊢
    rw [this]
  have h₃ : GlobalTheory.TorusCoord.im (U.gt e) (𝟙 (thickObj R (maximalIdeal R) e G)) = (U₂.gt e).pG ≫ β.hom := by
    ext
    have := (hβ e).symm
    simp [GlobalTheory.TorusCoord.im] at this ⊢
    exact this
  have h₅ : GlobalTheory.TorusCoord.im (U.gt e) (GlobalTheory.MumCmp.Transl.tr ae) = (U₂.gt e).pG ≫ (β.hom * (toUnit D₂.toPre.P.A ≫ b)) := by
    rw [GlobalTheory.MumCmp.Transl.tr, h₁, h₂, h₃, comp_mul, comp_toUnit_assoc, mul_comm]
  rw [heq]
  exact congrArg Over.Hom.left h₅

end GlobalTheory.MumCmp.LevelCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAdditiveCubicalStructureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_additive_cubicalStructure : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (x x' y : Z ⟶ D.P.A) (x₀ x₀' y₀ : Over.mk (Z.hom ≫ spMap ω) ⟶ T.B), x.left ≫ β = x₀.left → x'.left ≫ β = x₀'.left → y.left ≫ β = y₀.left → ∀ (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (x * x') y).left z J J' * cubV D.cub z J' x x' y = lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J x₀ x₀' y₀) ∧ lamVal w (lift y (x * x')).left z J J' * cubV D.cub z J' y x x' = lamVal w (lift y x).left z J J' * lamVal w (lift y x').left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J y₀ x₀ x₀') := by
  first | exact @GlobalTheory.TInj.lamVal_add_cub | exact GlobalTheory.TInj.lamVal_add_cub | (intros; apply GlobalTheory.TInj.lamVal_add_cub <;> assumption)
end

