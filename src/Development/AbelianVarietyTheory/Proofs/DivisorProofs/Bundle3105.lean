module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3098
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickActionsIsomorphic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemClassSumsValuesOfFunctions
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.Sep.ExactSums

theorem sumI_fourier {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) {n : ℕ} [NeZero n] {ω : V}
    (hω : IsPrimitiveRoot ω n) {G : Type} [AddCommGroup G] [Fintype G] (d : V) (hd : d * (Fintype.card G : V) = 1)
    {Ix : Type} (w : Ix → G → ZMod n) (hw : ∀ mu τ τ', w mu (τ + τ') = w mu τ + w mu τ') (κ : Ix)
    (x : Ix → V) (s : G → V) (h : ∀ τ, SumI I (fun mu => ω ^ (w mu τ).val * x mu) (s τ))
    (f : Ix → V) (hf1 : ∀ mu, (∀ τ, w mu τ = w κ τ) → f mu = x mu)
    (hf0 : ∀ mu, ¬ (∀ τ, w mu τ = w κ τ) → f mu = 0) :
    SumI I f (d * ∑ τ, ω ^ (-(w κ τ)).val * s τ) := by
  classical
  have pw : ∀ a b : ZMod n, ω ^ a.val * ω ^ b.val = ω ^ (a + b).val := fun a b => by
    rw [← pow_add, ZMod.val_add]
    conv_lhs => rw [← Nat.mod_add_div (a.val + b.val) n, pow_add, pow_mul, hω.pow_eq_one, one_pow, _root_.mul_one]
  have hchar : ∀ mu, ∑ τ, ω ^ (-(w κ τ)).val * ω ^ (w mu τ).val =
      if (∀ τ, w mu τ = w κ τ) then (Fintype.card G : V) else 0 := by
    intro mu
    simp_rw [pw]
    split_ifs with hmu
    · simp [hmu]
    · push_neg at hmu
      obtain ⟨τ₀, h0⟩ := hmu
      set χ : G → V := fun τ => ω ^ (-(w κ τ) + w mu τ).val with hχ
      have hmul : ∀ τ, χ (τ + τ₀) = χ τ * χ τ₀ := fun τ => by
        simp only [χ, hw, pw]; congr 2; ring
      have hne : χ τ₀ ≠ 1 := by
        intro h1
        rw [hχ, hω.pow_eq_one_iff_dvd] at h1
        have hv : (-(w κ τ₀) + w mu τ₀).val ≠ 0 := by
          rw [ne_eq, ZMod.val_eq_zero]
          intro h
          exact h0 (neg_add_eq_zero.1 h).symm
        exact hv (Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _))
      have hsum : ∑ τ, χ τ = χ τ₀ * ∑ τ, χ τ := by
        calc ∑ τ, χ τ = ∑ τ, χ (τ + τ₀) := (Equiv.sum_comp (Equiv.addRight τ₀) χ).symm
          _ = ∑ τ, χ τ * χ τ₀ := Finset.sum_congr rfl fun τ _ => hmul τ
          _ = χ τ₀ * ∑ τ, χ τ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
      have h2 : (χ τ₀ - 1) * ∑ τ, χ τ = 0 := by rw [sub_mul, ← hsum, _root_.one_mul, sub_self]
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)
  have hT : ∀ T : Finset G, SumI I (fun mu => ∑ τ ∈ T, ω ^ (-(w κ τ)).val * (ω ^ (w mu τ).val * x mu))
      (∑ τ ∈ T, ω ^ (-(w κ τ)).val * s τ) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨⊥, Submodule.fg_bot, Submodule.zero_mem _, fun _ => Submodule.zero_mem _, fun _ => ⟨∅, fun _ _ => by simp⟩⟩
    | insert a T ha ih =>
      simp only [Finset.sum_insert ha]
      exact GlobalTheory.AdicSum.sumI_add (GlobalTheory.AdicSum.sumI_map (LinearMap.mulLeft V (ω ^ (-(w κ a)).val)) (h a)) ih
  have hS := GlobalTheory.AdicSum.sumI_map (LinearMap.mulLeft V d) (hT Finset.univ)
  simp only [LinearMap.mulLeft_apply] at hS
  convert hS using 1
  funext mu
  have e : ∑ τ, ω ^ (-(w κ τ)).val * (ω ^ (w mu τ).val * x mu) =
      (∑ τ, ω ^ (-(w κ τ)).val * ω ^ (w mu τ).val) * x mu := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun τ _ => (_root_.mul_assoc _ _ _).symm
  rw [e, hchar]
  split_ifs with hmu
  · rw [hf1 mu hmu, ← _root_.mul_assoc, hd, _root_.one_mul]
  · rw [hf0 mu hmu, zero_mul, mul_zero]

theorem labels {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (H : AddSubgroup S.Gam)
    {X : Type} [AddCommGroup X] (YY : S.Gam → (Fin 8 → X) → Prop)
    (h1 : ∀ a, ∃ mu, YY a mu) (h2 : ∀ mu, ∃ a, YY a mu)
    (h3 : ∀ a mu mu', YY a mu → (YY a mu' ↔ ∀ v, CongMod (S.r * S.N) (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', YY a mu → YY a' mu' → YY (a + a') (mu + mu'))
    (hH : ∀ a, a ∈ H ↔ YY a 0) :
    ∃ l : (Fin 8 → X) → S.Gam, (∀ mu, YY (l mu) mu) ∧
      (∀ τ ∈ S.perp H, ∀ a mu, YY a mu → eStd S.g _ τ a = eStd S.g _ τ (l mu)) ∧
      ∀ mu κ, (∀ τ ∈ S.perp H, eStd S.g _ τ (l mu) = eStd S.g _ τ (l κ)) ↔ ∀ v, CongMod (S.r * S.N) (mu v) (κ v) := by
  obtain ⟨l, hl⟩ : ∃ l : (Fin 8 → X) → S.Gam, ∀ mu, YY (l mu) mu := ⟨fun mu => (h2 mu).choose, fun mu => (h2 mu).choose_spec⟩
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
    intro v
    obtain ⟨w, hw⟩ := ((h3 _ _ _ (hl mu)).1 e1) v
    exact ⟨-w, by rw [hw, smul_neg, add_neg_cancel_right]⟩
  · exact (D1 τ hτ (l κ) mu ((h3 _ _ _ (hl κ)).2 h)).symm

theorem isClassSum_of_sumI {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ}
    {A : Type} [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (y : Φ.Y) (N : ℕ) (κ : Fin s → Φ.X y) (c : Φ.Q)
    {V' : Type} [CommRing V'] [IsLocalRing V'] (io : Φ.V y →+* V') (x : V') (f : (Fin s → Φ.X y) → V')
    (hf1 : ∀ mu, (∀ v, CongMod N (mu v) (κ v)) → f mu = io (Φ.term y mu c))
    (hf0 : ∀ mu, ¬ (∀ v, CongMod N (mu v) (κ v)) → f mu = 0)
    (h : SumI (maximalIdeal V') f x) : Φ.IsClassSum y N κ c io x := by
  classical
  intro j
  obtain ⟨M, -, -, -, hS⟩ := h
  obtain ⟨S₀, hS₀⟩ := hS j
  let P : (Fin s → Φ.X y) → Prop := fun mu => ∀ v, CongMod N (mu v) (κ v)
  let L := (PreModel.low_finite Φ y P j).toFinset
  let T := S₀ ∪ L
  refine ⟨T.filter P, fun mu hmu => (Finset.mem_filter.1 hmu).2, fun mu hP hn => ?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    exact hn (Finset.mem_filter.2 ⟨Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 ⟨hP, hlt⟩), hP⟩)
  · have h1 := hS₀ T Finset.subset_union_left
    have h2 : ∑ mu ∈ T, f mu = io (∑ mu ∈ T.filter P, Φ.term y mu c) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun mu _ => ?_
      split_ifs with hP
      · exact hf1 mu hP
      · exact hf0 mu hP
    rw [← h2]
    have hle : maximalIdeal V' ^ j • M ≤ maximalIdeal V' ^ j := by
      calc maximalIdeal V' ^ j • M ≤ maximalIdeal V' ^ j • (⊤ : Submodule V' V') := Submodule.smul_mono le_rfl le_top
        _ = maximalIdeal V' ^ j := by rw [smul_eq_mul, Ideal.mul_top]
    exact hle h1

theorem isPrimitiveRoot_map' {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) {n : ℕ}
    (hn : (n : V) ≠ 0) {ζ : R} (hζ : IsPrimitiveRoot ζ n) : IsPrimitiveRoot (φ ζ) n := by
  have : NeZero (n : V) := ⟨hn⟩
  have h₀ : 0 < n := Nat.pos_of_ne_zero fun e => hn (by rw [e, Nat.cast_zero])
  have h := (hζ.isRoot_cyclotomic h₀).map (f := φ)
  rw [Polynomial.map_cyclotomic] at h
  exact Polynomial.isRoot_cyclotomic_iff.1 h

end GlobalTheory.Poinc.Sep.ExactSums

namespace GlobalTheory.Poinc.Sep.ExactSums

open Classical in
theorem exact_of_isGeo : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam), IsGeo X₁ z₁ act x₀ Φ lab → Φ.Exact (X₁.S.r * X₁.S.N) := by
  intro g n F W Z i X₁ z₁ act x₀ Φ lab hG
  obtain ⟨hdiv, hlab, hmem⟩ := hG
  intro y κ c
  obtain ⟨𝔪, hT⟩ := hmem y
  haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)⟩
  haveI : IsDomain X₁.o₁ := X₁.ar.ded.toIsDomain
  obtain ⟨yy1, yy2, yy3, yy4⟩ := _root_.GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act (Φ.V y) (Φ.ev y) (Φ.X y) (Φ.m y) (Φ.t y) (Φ.δ y) 𝔪
  have hH := _root_.GlobalTheory.Poinc.Sep.mem_HH_iff_yy_zero g n F W Z i X₁ z₁ act x₀ hdiv (Φ.V y) (Φ.ev y) (Φ.X y) (Φ.m y) (Φ.t y) (Φ.δ y) 𝔪
  obtain ⟨l, -, hlY, hlC⟩ := labels X₁.S (X₁.S.HH X₁.M z₁) 𝔪.YY yy1 yy2 yy3 yy4 hH
  obtain ⟨sg, eps, hlink⟩ := GlobalTheory.T.theta_constants_torus_translates_twisted_sums g n F W Z i X₁ z₁ act x₀ hdiv

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

  let w : (Fin 8 → Φ.X y) → TT → ZMod (X₁.S.r * X₁.S.N) := fun mu τ => (sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) (l mu)
  have hw : ∀ mu τ τ', w mu (τ + τ') = w mu τ + w mu τ' := fun mu τ τ' => by
    simp only [w, AddSubgroup.coe_add, eStd_add_left, smul_add]
  have hsg : ∀ a b : ZMod (X₁.S.r * X₁.S.N), (sg : ℤ) • a = (sg : ℤ) • b → a = b := fun a b h => by
    have := congrArg (fun t => (sg : ℤ) • t) h
    have e : ((sg : ℤ) * sg) = 1 := by rcases Int.units_eq_one_or sg with h | h <;> simp [h]
    simpa only [smul_smul, e, one_smul] using this
  have hwκ : ∀ mu, (∀ τ, w mu τ = w κ τ) ↔ ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu v) (κ v) := fun mu => by
    rw [← hlC mu κ]
    exact ⟨fun h τ hτ' => hsg _ _ (h ⟨τ, hτ'⟩), fun h τ => by simp only [w, h τ τ.2]⟩
  have hlab' : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁ := fun c => by
    rw [← SetLike.mem_coe, ← hlab]; exact Set.mem_range_self c
  have hsum : ∀ τ : TT, SumI (maximalIdeal (Φ.V y)) (fun mu => Φ.ev y zt ^ (w mu τ).val * Φ.term y mu c) (Φ.ev y (hτ τ)) :=
    fun τ => hlink (Φ.V y) (Φ.ev y) (Φ.X y) (Φ.m y) (Φ.t y) (Φ.δ y) 𝔪 Φ.Q lab hlab' (Φ.term y) hT c τ τ.2 zt (hτ τ) hzt
      (hhτ τ) (fun mu => w mu τ) (fun a mu hY => by simp only [w, hlY τ τ.2 a mu hY])
  let f : (Fin 8 → Φ.X y) → Φ.V y := fun mu => if ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu v) (κ v) then Φ.term y mu c else 0
  have hf := sumI_fourier (maximalIdeal (Φ.V y)) hω (Φ.ev y d) hd w hw κ (fun mu => Φ.term y mu c) (fun τ => Φ.ev y (hτ τ))
    hsum f (fun mu h => if_pos ((hwκ mu).1 h)) (fun mu h => if_neg fun h' => h ((hwκ mu).2 h'))
  refine ⟨d * ∑ τ : TT, zt ^ (-(w κ τ)).val * hτ τ, isClassSum_of_sumI Φ y _ κ c (RingHom.id _) _ f
    (fun mu h => if_pos h) (fun mu h => if_neg h) ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_mul, map_sum, map_pow] using hf

end GlobalTheory.Poinc.Sep.ExactSums
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionStepLogCanonical
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.PairStep

theorem topologicalKrullDim_closure_closedPt_le_zero {X : Scheme.{0}} {x : X}
    (hx : IsClosed ({x} : Set X)) : topologicalKrullDim (closure ({x} : Set X)) ≤ 0 := by
  have hsing : ∀ a b : closure ({x} : Set X), a = b := by
    intro a b
    apply Subtype.ext
    have ha : (a : X) = x := Set.mem_singleton_iff.mp (hx.closure_subset a.2)
    have hb : (b : X) = x := Set.mem_singleton_iff.mp (hx.closure_subset b.2)
    rw [ha, hb]
  have hirr : ∀ s t : IrreducibleCloseds (closure ({x} : Set X)), s = t := by
    intro s t
    apply SetLike.ext
    intro a
    obtain ⟨b, hb⟩ := s.isIrreducible.nonempty
    obtain ⟨c, hc⟩ := t.isIrreducible.nonempty
    constructor
    · intro _
      rw [hsing a c]
      exact hc
    · intro _
      rw [hsing a b]
      exact hb
  unfold topologicalKrullDim
  rw [Order.krullDim_nonpos_iff_forall_isMax]
  intro s t _
  rw [hirr t s]

theorem eq_of_closedPt_specializes {X : Scheme.{0}} {x y : X} (hx : IsClosed ({x} : Set X))
    (h : x ⤳ y) : y = x := by
  exact Set.mem_singleton_iff.mp (hx.closure_subset (specializes_iff_mem_closure.mp h))

private lemma two_mul_lt_pow_mul_of_le (a t t' c : ℚ) (k : ℕ) (ha : 0 ≤ a) (ht : 0 < t) (htt : t ≤ t')
    (h : 2 * a < t ^ k * c) : 2 * a < t' ^ k * c ∧ a < t' ^ k * c := by
  have htk : 0 < t ^ k := pow_pos ht k
  have hc : 0 < c := by
    by_contra hc
    push_neg at hc
    have : t ^ k * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htk.le hc
    linarith
  have hpow : t ^ k ≤ t' ^ k := by
    first
    | exact pow_le_pow_left ht.le htt k
    | exact pow_le_pow_left₀ ht.le htt k
  have : t ^ k * c ≤ t' ^ k * c := mul_le_mul_of_nonneg_right hpow hc.le
  constructor <;> linarith

theorem twoPoint_step : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (d ε : ℚ) (h : ℕ → ℚ) (x x' : X) (j : ℕ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x} : Set X) → IsClosed ({x'} : Set X) → x ≠ x' → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x ∨ z ⤳ x' → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → 0 < ε → QNum p N d D → 0 ≤ d → LcCut p n (Δ + D) x j → ¬ KltAt p n (Δ + D) x' → LcCut p n (Δ + D) x 0 ∨ ∃ (i : ℕ) (D' : X → ℚ) (d' : ℚ), i < j ∧ 0 ≤ d' ∧ d' ≤ d + (h (i + 1) + ε) ∧ QNum p N d' D' ∧ ((LcCut p n (Δ + D') x i ∧ ¬ KltAt p n (Δ + D') x') ∨ (LcCut p n (Δ + D') x' i ∧ ¬ KltAt p n (Δ + D') x)) := by
  intro hP hNV hNef X _ _ _ p n hp hn Δ m G N D d ε h x x' j hΔ hklt hm hG hN hx hx' hxx' hpos hbig
    hε hD hd hcut hnk
  obtain ⟨hlcx, hnkx, hdim⟩ := hcut
  by_cases h0 : LcCut p n (Δ + D) x 0
  · exact Or.inl h0
  right

  have hex : ∃ z, z ⤳ x ∧ ¬ KltAt p n (Δ + D) z ∧
      ¬ topologicalKrullDim (closure ({z} : Set X)) ≤ 0 := by
    by_contra hne
    push_neg at hne
    apply h0
    unfold LcCut
    refine ⟨hlcx, hnkx, fun z hz hkz => ?_⟩
    have := hne z hz hkz
    simpa using this
  obtain ⟨z, hzx, hkz, hz0⟩ := hex
  have hzne : z ≠ x := by
    rintro rfl
    exact hz0 (topologicalKrullDim_closure_closedPt_le_zero hx)
  have hDq : IsQCart D := hD.isQCart

  obtain ⟨w, hwz, hw⟩ := _root_.GlobalTheory.PairStep.Centre.exists_isNkltCentre X p n hp hn Δ D z hDq (hklt z) hkz
  have hwx : w ⤳ x := hwz.trans hzx
  have hwne : w ≠ x := by
    rintro rfl
    exact hzne (eq_of_closedPt_specializes hx hwz)
  obtain ⟨e, -, hdw, he1⟩ := _root_.GlobalTheory.closure_point_topologicalKrullDim X n w hn
  have he1' : 1 ≤ e := he1 x hwx hwne.symm
  have hkw : ¬ KltAt p n (Δ + D) w :=
    not_kltAt_of_isNkltCentre X p n hp hn (Δ + D) w w hw (specializes_refl w)
  have hej : e ≤ j := by
    have hle := hdim w hwx hkw
    rw [hdw] at hle
    exact_mod_cast hle
  obtain ⟨i, rfl⟩ : ∃ i, e = i + 1 := ⟨e - 1, by omega⟩
  have hwN := hbig w (i + 1) (Or.inl hwx) he1' hdw
  by_cases hlx' : LcAt p n (Δ + D) x'
  ·
    obtain ⟨w', hw'x', hw'⟩ := _root_.GlobalTheory.PairStep.Centre.exists_isNkltCentre X p n hp hn Δ D x' hDq (hklt x') hnk
    by_cases hw'x : w' ⤳ x
    ·
      have hkw' : ¬ KltAt p n (Δ + D) w' :=
        not_kltAt_of_isNkltCentre X p n hp hn (Δ + D) w' w' hw' (specializes_refl w')
      obtain ⟨e', -, hdw', he1''⟩ := _root_.GlobalTheory.closure_point_topologicalKrullDim X n w' hn
      have h1e' : 1 ≤ e' := by
        by_cases hxw : x = w'
        · refine he1'' x' hw'x' ?_
          intro h2
          exact hxx' (hxw.trans h2.symm)
        · exact he1'' x hw'x hxw
      have he'j : e' ≤ j := by
        have hle := hdim w' hw'x hkw'
        rw [hdw'] at hle
        exact_mod_cast hle
      obtain ⟨i', rfl⟩ : ∃ i', e' = i' + 1 := ⟨e' - 1, by omega⟩
      have hw'N := hbig w' (i' + 1) (Or.inl hw'x) h1e' hdw'
      have hnum := two_mul_lt_pow_mul_of_le _ (h (i' + 1)) (h (i' + 1) + ε) _ (i' + 1) (by positivity)
        (hpos _) (by linarith) hw'N
      obtain ⟨D', d', hd'0, hd'le, hD', hfin⟩ := GlobalTheory.T.lc_cut_two_closed_points_one_centre hP hNV hNef X p n hp hn Δ m G N D d
        (h (i' + 1) + ε) x x' w' i' hΔ hklt hm hG hN hD hd hx hx' hlcx hlx' hw'x hw'x' (Or.inr hw')
        hdw' (by linarith [hpos (i' + 1)]) hnum.1
      exact ⟨i', D', d', by omega, hd'0, hd'le, hD', hfin⟩
    ·
      obtain ⟨b, A, hb0, hbε, hA, hAx, hAw'⟩ := _root_.GlobalTheory.PairStep.exists_small_ample_through_off X p hp N x w' ε hN hw'x hε
      have hAq : IsQCart A := hA.isQCart
      have hsum : Δ + D + (1 : ℚ) • A = Δ + (D + A) := by
        rw [one_smul, add_assoc]
      have hoff := off_add_smul X p n (Δ + D) A 1 x hAx
      rw [hsum] at hoff
      obtain ⟨hkltiff, hlciff, -, hoffz⟩ := hoff
      have hcut' : LcCut p n (Δ + (D + A)) x j := by
        unfold LcCut
        refine ⟨hlciff.mpr hlcx, fun hk => hnkx (hkltiff.mp hk), fun y hy hky => ?_⟩
        have h2 := (off_add_smul X p n (Δ + D) A 1 y (hoffz y hy)).1
        rw [hsum] at h2
        exact hdim y hy (fun hk => hky (h2.mpr hk))
      have hw2 : IsNkltCentre p n (Δ + (D + A)) w := by
        have h3 := (off_add_smul X p n (Δ + D) A 1 w (hoffz w hwx)).2.2.1
        rw [hsum] at h3
        exact h3.mpr hw
      have hnlc : ¬ LcAt p n (Δ + (D + A)) x' := by
        have h4 := _root_.GlobalTheory.PairStep.not_lcAt_add_of_isNkltCentre X p n hp hn (Δ + D) A w' x' hw' hAq hAw' hw'x'
        rw [add_assoc] at h4
        exact h4
      have hDA : QNum p N (d + b) (D + A) := qNum_add X p hp N d b D A hD hA
      have hnum := two_mul_lt_pow_mul_of_le _ (h (i + 1)) (h (i + 1) + ε - b) _ (i + 1) (by positivity)
        (hpos _) (by linarith) hwN
      obtain ⟨hlcx2, -, -⟩ := hcut'
      obtain ⟨D', d', hd'0, hd'le, hD', hcutD', hnkD'⟩ := GlobalTheory.T.exists_lc_cut_point_of_not_lc_other hP hNV hNef X p n hp hn Δ m G
        N (D + A) (d + b) (h (i + 1) + ε - b) x x' w i hΔ hklt hm hG hN hDA (by linarith) hx hlcx2
        hnlc hwx hw2 hdw (by linarith [hpos (i + 1)]) hnum.2
      exact ⟨i, D', d', by omega, hd'0, by linarith, hD', Or.inl ⟨hcutD', hnkD'⟩⟩
  ·
    have hnum := two_mul_lt_pow_mul_of_le _ (h (i + 1)) (h (i + 1) + ε) _ (i + 1) (by positivity)
      (hpos _) (by linarith) hwN
    obtain ⟨D', d', hd'0, hd'le, hD', hcutD', hnkD'⟩ := GlobalTheory.T.exists_lc_cut_point_of_not_lc_other hP hNV hNef X p n hp hn Δ m G
      N D d (h (i + 1) + ε) x x' w i hΔ hklt hm hG hN hD hd hx hlcx hlx' hwx hw hdw
      (by linarith [hpos (i + 1)]) hnum.2
    exact ⟨i, D', d', by omega, hd'0, hd'le, hD', Or.inl ⟨hcutD', hnkD'⟩⟩

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickActionsIsomorphicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinTrick_actions_isomorphic : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)) (inc₁ : c.A ⟶ z₁.A) (pr₁ : z₁.A ⟶ c.A) (inc₂ : c.A ⟶ z₂.A) (pr₂ : z₂.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → IsMonHom inc₁ → IsMonHom pr₁ → inc₁ ≫ pr₁ = 𝟙 c.A → pr₁ ≫ inc₁ = act₁ (GlobalTheory.ZarhinFam.idem d) → IsMonHom inc₂ → IsMonHom pr₂ → inc₂ ≫ pr₂ = 𝟙 c.A → pr₂ ≫ inc₂ = act₂ (GlobalTheory.ZarhinFam.idem d) → (∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc₁ ≫ act₁ (GlobalTheory.ZarhinFam.polUnit d) = 1 ↔ x ≫ inc₂ ≫ act₂ (GlobalTheory.ZarhinFam.polUnit d) = 1) → ∃ e : z₁.A ≅ z₂.A, IsMonHom e.hom ∧ inc₁ ≫ e.hom = inc₂ ∧ ∀ o, act₁ o ≫ e.hom = e.hom ≫ act₂ o := by
  first | (exact @GlobalTheory.ZarhinUniqIso.zarhin_uniq_iso) | (exact GlobalTheory.ZarhinUniqIso.zarhin_uniq_iso) | (intros; apply GlobalTheory.ZarhinUniqIso.zarhin_uniq_iso  <;> assumption)
end

