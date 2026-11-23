module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0010
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLFlatten
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0030
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLNormExists
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0031
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0033
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpairGeo

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenChart
section
noncomputable section

namespace PositivityTheory.HtPt.Hcptgen

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ChartFin ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isUnit_iff_unitAt {q : Cpt ξ} (hi : Function.Injective (genMap ξ q)) (s : X.presheaf.stalk q.1) :
    IsUnit s ↔ unitAt ξ q (genMap ξ q s) := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : genMap ξ q (u : X.presheaf.stalk q.1) * genMap ξ q (↑u⁻¹ : X.presheaf.stalk q.1) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact ⟨left_ne_zero_of_mul_eq_one h, ⟨_, rfl⟩, ⟨_, eq_inv_of_mul_eq_one_right h⟩⟩
  · rintro ⟨h0, -, t, ht⟩
    refine IsUnit.of_mul_eq_one t (hi ?_)
    rw [map_mul, ht, mul_inv_cancel₀ h0, map_one]

theorem overZp_iff {p : ℕ} (hp : p.Prime) (q : Cpt ξ) :
    (∀ r : ℕ, r.Prime → InFibre ξ r q → r = p) ↔ ∀ b : ℕ, ¬ p ∣ b → unitAt ξ q (b : Ω) := by
  constructor
  · intro hq b hb
    induction b using Nat.recOnMul with
    | zero => exact absurd (dvd_zero p) hb
    | one =>
      rw [Nat.cast_one]
      exact ⟨one_ne_zero, one_mem _, by rw [inv_one]; exact one_mem _⟩
    | prime r hr =>
      by_contra h
      exact hb (by rw [hq r hr h])
    | mul a b iha ihb =>
      have ha := iha fun h => hb (h.mul_right b)
      have hb' := ihb fun h => hb (h.mul_left a)
      rw [Nat.cast_mul]
      exact ⟨mul_ne_zero ha.1 hb'.1, mul_mem ha.2.1 hb'.2.1, by
        rw [mul_inv]; exact mul_mem ha.2.2 hb'.2.2⟩
  · intro h r hr hf
    by_contra hne
    exact hf (h r fun hd => hne ((Nat.prime_dvd_prime_iff_eq hp hr).1 hd).symm)

theorem mem_adjoin_loc [CharZero Ω] {p : ℕ} (hp : p.Prime) {o : Type} [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    (T : Set Ω) {a : Ω} (ha : a ∈ Algebra.adjoin o T) :
    ∃ b : ℕ, ¬ p ∣ b ∧ a * b ∈ Algebra.adjoin ℤ T := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, hp.not_dvd_one, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨m, b, hb, e⟩ := (ho _).1 ⟨r, rfl⟩
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 fun h => hb (h ▸ dvd_zero p)
    exact ⟨b, hb, by rw [e, div_mul_cancel₀ _ hb0]; exact intCast_mem _ m⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, hx⟩ := hx
    obtain ⟨b', hb', hy⟩ := hy
    refine ⟨b * b', hp.not_dvd_mul hb hb', ?_⟩
    have : (x + y) * ((b * b' : ℕ) : Ω) = x * b * b' + y * b' * b := by push_cast; ring
    rw [this]
    exact add_mem (mul_mem hx (natCast_mem _ _)) (mul_mem hy (natCast_mem _ _))
  | mul x y _ _ hx hy =>
    obtain ⟨b, hb, hx⟩ := hx
    obtain ⟨b', hb', hy⟩ := hy
    refine ⟨b * b', hp.not_dvd_mul hb hb', ?_⟩
    have : (x * y) * ((b * b' : ℕ) : Ω) = x * b * (y * b') := by push_cast; ring
    rw [this]
    exact mul_mem hx hy

theorem chart_int {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) (hn : IsNormalScheme X) {c : κ} (hc : x c ≠ 0) :
    IsFractionRing (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω ∧
      IsIntegrallyClosed (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) := by
  have hf : IsFractionRing (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω := by
    refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, hg, h, hh, -, e⟩ := FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ κ x c T hc a
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩, e⟩
  refine ⟨hf, (isIntegrallyClosed_iff Ω).2 fun {a} ha => ?_⟩
  refine ⟨⟨a, (T.ring c hc a).2 fun q hq => ?_⟩, rfl⟩
  obtain ⟨h1, -, h3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring X Ω ξ T.gen q
  have h4 := h3 (hn q.1).2
  let φ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* regAt ξ q :=
    (algebraMap (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω).codRestrict _
      fun r => (T.ring c hc r).1 r.2 q hq
  have h5 : IsIntegral (regAt ξ q) a := ha.map_of_comp_eq φ (RingHom.id Ω) rfl
  obtain ⟨r, rfl⟩ := (isIntegrallyClosed_iff Ω).1 h4 h5
  exact r.2

theorem chart_loc [CharZero Ω] {κ : Type} [Finite κ] {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q)
    (T : CoordTie ℤ ξ x) (hn : IsNormalScheme X) {p : ℕ} (hp : p.Prime) {o : Type} [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {c : κ} (hc : x c ≠ 0) (B : Subalgebra o Ω) (hB : B = Algebra.adjoin o (Set.range fun j => x j / x c)) :
    IsNoetherianRing B ∧ IsIntegrallyClosed B ∧ IsFractionRing B Ω ∧
      ∃ z : Sp B ⟶ X, spMap (algebraMap B Ω) ≫ z = ξ ∧
        ∀ q : Cpt ξ, q.1 ∈ Set.range z ↔ (InChart ξ x c q ∧ ∀ r : ℕ, r.Prime → InFibre ξ r q → r = p) := by
  obtain ⟨U, hUa, hUm⟩ := T.affine c hc
  have hg : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, inChart_genPt T.gen hc⟩
  obtain ⟨E, hE⟩ := ChartSmooth.exists_secEquiv hall T hc hUm hg
  obtain ⟨hAf, hAi⟩ := chart_int T hn hc
  have hAB : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), a ∈ B := by
    intro a ha
    have : Algebra.adjoin ℤ (Set.range fun j => x j / x c) ≤ subalgebraOfSubring B.toSubring :=
      Algebra.adjoin_le (by rw [hB]; exact Algebra.subset_adjoin)
    exact this ha
  have hinj := secVal_injective hall T.gen.inj U hg
  let ψ : Γ(X, U) →+* B := (secVal ξ U hg).codRestrict _ fun s => hAB _ (hE s ▸ (E s).2)
  have hψ : ∀ s, (ψ s : Ω) = secVal ξ U hg s := fun _ => rfl
  letI : Algebra Γ(X, U) B := ψ.toAlgebra
  let M : Submonoid Γ(X, U) :=
    { carrier := {r | ∃ b : ℕ, ¬ p ∣ b ∧ r = b}
      one_mem' := ⟨1, hp.not_dvd_one, Nat.cast_one.symm⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
        exact ⟨b * b', hp.not_dvd_mul hb hb', (Nat.cast_mul _ _).symm⟩ }
  have hb0 : ∀ b : ℕ, ¬ p ∣ b → (b : Ω) ≠ 0 := fun b hb => Nat.cast_ne_zero.2 fun h => hb (h ▸ dvd_zero p)
  haveI hloc : IsLocalization M B := by
    refine ⟨?_, fun a => ?_, fun {r s} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, b, hb, rfl⟩
      obtain ⟨r, hr⟩ := (ho ((1 : ℤ) / (b : Ω))).2 ⟨1, b, hb, rfl⟩
      refine IsUnit.of_mul_eq_one (algebraMap o B r) (Subtype.ext ?_)
      have h1 : ((algebraMap o B r : B) : Ω) = algebraMap o Ω r := rfl
      simp only [map_natCast, MulMemClass.coe_mul, SubringClass.coe_natCast, h1, hr, OneMemClass.coe_one]
      rw [Int.cast_one, mul_one_div_cancel (hb0 b hb)]
    · obtain ⟨b, hb, hab⟩ := mem_adjoin_loc hp ho _ (hB.le a.2)
      refine ⟨⟨E.symm ⟨_, hab⟩, ⟨b, b, hb, rfl⟩⟩, Subtype.ext ?_⟩
      show (a : Ω) * secVal ξ U hg (b : Γ(X, U)) = secVal ξ U hg _
      rw [← hE (E.symm _), E.apply_symm_apply, map_natCast]
    · have h' : secVal ξ U hg r = secVal ξ U hg s := (hψ r).symm.trans ((congrArg Subtype.val h).trans (hψ s))
      rw [hinj h']
  haveI : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) := by
    refine (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => x j / x c).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset]
  haveI : IsNoetherianRing (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :=
    Algebra.FiniteType.isNoetherianRing ℤ _
  have hRN : IsNoetherianRing Γ(X, U) := isNoetherianRing_of_ringEquiv _ E.symm
  haveI : IsDomain Γ(X, U) := hinj.isDomain _
  haveI : IsIntegrallyClosed Γ(X, U) := IsIntegrallyClosed.of_equiv E.symm
  have hM : M ≤ nonZeroDivisors Γ(X, U) := by
    rintro _ ⟨b, hb, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => hb0 b hb ?_
    rw [← map_natCast (secVal ξ U hg), h, map_zero]
  refine ⟨IsLocalization.isNoetherianRing M B hRN, isIntegrallyClosed_of_isLocalization B M hM, ?_,
    Spec.map (CommRingCat.ofHom ψ) ≫ hUa.fromSpec, ?_, fun q => ?_⟩
  · refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, hg, h, hh, -, e⟩ := FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ κ x c T hc a
    exact ⟨⟨g, hAB g hg⟩, ⟨h, hAB h hh⟩, e⟩
  · have e0 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have e1 : X.fromSpecStalk (genPt ξ) = Spec.map (X.presheaf.germ U _ hg) ≫ hUa.fromSpec :=
      (hUa.fromSpecStalk_eq_fromSpecStalk hg).symm
    have e2 : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B Ω) =
        X.presheaf.germ U _ hg ≫ Scheme.stalkClosedPointTo ξ := rfl
    refine Eq.trans ?_ e0
    rw [e1, ← Spec.map_comp_assoc]
    exact (congrArg (fun m => Spec.map m ≫ hUa.fromSpec) e2).trans (Spec.map_comp_assoc _ _ _)
  · have hunit : ∀ (P : PrimeSpectrum Γ(X, U)) (hP : hUa.fromSpec P = q.1) (b : ℕ),
        (b : Γ(X, U)) ∉ P.asIdeal ↔ unitAt ξ q (b : Ω) := by
      intro P hP b
      have hq : q.1 ∈ U := by
        rw [← hP, ← SetLike.mem_coe, ← hUa.range_fromSpec]
        exact ⟨P, rfl⟩
      have h1 : P ∈ hUa.fromSpec ⁻¹ᵁ X.basicOpen (b : Γ(X, U)) ↔ q.1 ∈ X.basicOpen (b : Γ(X, U)) := by
        rw [← hP]; rfl
      rw [hUa.fromSpec_preimage_basicOpen, X.mem_basicOpen _ _ hq, isUnit_iff_unitAt (T.gen.inj q), map_natCast,
        map_natCast] at h1
      exact h1
    have hrange := PrimeSpectrum.localization_comap_range B M
    rw [overZp_iff hp]
    constructor
    · rintro ⟨P, hP⟩
      have hP' : hUa.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, U) B) P) = q.1 := hP
      have hq : q.1 ∈ U := by
        rw [← hP', ← SetLike.mem_coe, ← hUa.range_fromSpec]
        exact ⟨_, rfl⟩
      refine ⟨((hUm _).1 hq).2, fun b hb => (hunit _ hP' b).1 fun hm => ?_⟩
      have hd := hrange.subset ⟨P, rfl⟩
      exact Set.disjoint_left.1 hd ⟨b, hb, rfl⟩ hm
    · rintro ⟨hq, hu⟩
      have hqU : q.1 ∈ (U : Set X) := (hUm _).2 ⟨q.2, hq⟩
      rw [← hUa.range_fromSpec] at hqU
      obtain ⟨P, hP⟩ := hqU
      have hd : (P : PrimeSpectrum Γ(X, U)) ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(X, U) B)) := by
        rw [hrange]
        refine Set.disjoint_left.2 ?_
        rintro _ ⟨b, hb, rfl⟩
        exact (hunit P hP b).2 (hu b hb)
      obtain ⟨Q, rfl⟩ := hd
      exact ⟨Q, hP⟩

end PositivityTheory.HtPt.Hcptgen
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLTopCommon
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LTopCommon

theorem exists_common_normal_model : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ _ Ω _ _ κ _ x M A _ κa _ w B _ E _ _ L V _ hw hL hV
  choose κb hκb v hv0 hv1 hv2 using fun b => PositivityTheory.HtPt.Mb.flatten o Ω κ x M (E b) (L b) (V b) (hL b) (hV b)
  let κs : A ⊕ B → Type := fun s => match s with
    | .inl a => κa a
    | .inr b => κb b
  let ws : ∀ s, κs s → Ω := fun s => match s with
    | .inl a => w a
    | .inr b => v b
  haveI : ∀ s, Finite (κs s) := fun s => match s with
    | .inl a => inferInstanceAs (Finite (κa a))
    | .inr b => hκb b
  have hws : ∀ s, ∃ l, ws s l ≠ 0 := fun s => match s with
    | .inl a => hw a
    | .inr b => hv0 b
  obtain ⟨κ₁, _, y₁, M₁, f, hf, hch, hiso⟩ := PositivityTheory.HtPt.Mb.join_many o Ω κ x M (A ⊕ B) κs ws hws
  obtain ⟨κ₂, hκ₂, y₂, M₂, g, hg, hN, -, hnorm⟩ := PositivityTheory.HtPt.Mb.norm_exists o Ω κ₁ y₁ M₁ Ω
  replace hg : Dominates M₂.ξ M₁.ξ g (RingHom.id Ω) := hg
  replace hnorm : ∀ p, NormAt M₂.ξ g (RingHom.id Ω) p := hnorm
  have hgf : Dominates M₂.ξ M.ξ (g ≫ f) (RingHom.id Ω) := by
    unfold Dominates at *
    rw [← Category.assoc, hg, Category.assoc, hf]
    simp
  have hch₂ : ∀ s (p' : Cpt M₂.ξ), ∃ l, InChart M₂.ξ (ws s) l p' := by
    intro s p'
    obtain ⟨h, h1, -⟩ := PositivityTheory.HtPt.Mb.dom_local _ Ω M₁.ξ _ Ω M₂.ξ _ g hg p'
    obtain ⟨l, hl⟩ := hch s ⟨_, h⟩
    exact ⟨l, hl.1, fun c => h1 _ (hl.2 c)⟩
  refine ⟨κ₂, hκ₂, y₂, M₂, g ≫ f, hgf, hN, fun a => hch₂ (.inl a), fun b => ?_, fun p hp hfr => ?_⟩
  · obtain ⟨e, hc⟩ := PositivityTheory.HtPt.Mb.pull_eq o Ω κ x M (E b) (L b) _ Ω M₂.ξ _ (E b) (AddMonoidHom.id _) (g ≫ f) (hL b) hgf
    have key := hv2 b _ Ω M₂.ξ (RingHom.id Ω) (E b) (AddMonoidHom.id _) ⟨fun _ _ => rfl, fun _ _ h => h⟩
    have hu : {p' | p' ∈ ctrSet o x (RingHom.id Ω) M₂.ξ ∧ ∃ l, InChart M₂.ξ (fun l => RingHom.id Ω (v b l)) l p'}
        = Set.univ := Set.eq_univ_of_forall fun p' => ⟨hc p', hch₂ (.inr b) p'⟩
    have hs : Submodule.span Ω (AddMonoidHom.id (E b) '' (V b : Set (E b))) = V b := by simp
    rw [hu, hs] at key
    rw [e]
    exact key
  · refine (PositivityTheory.HtPt.Mb.iso_comp _ Ω M.ξ _ _ Ω (RingHom.id Ω) p).1 M₁.ξ M₂.ξ f g hg (hiso p ?_) fun p₁ _ => hnorm p₁
    rintro (a | b)
    · exact hp a
    · exact hv1 b p (hfr b)

end PositivityTheory.HtPt.Mb.LTopCommon


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.top_common : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LTopCommon.exists_common_normal_model
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ReTens
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Re

theorem tens_hopf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), ∃ AA : HopfOrder (C := C) R (N₁ × N₂), AA.carrier = tens A₁.carrier A₂.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (z.1, 0)) ∈ AA.carrier) ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (0, z.2)) ∈ AA.carrier) ∧ ∀ c₁ c₂, HasColen R v A₁.carrier c₁ → HasColen R v A₂.carrier c₂ → HasColen R v AA.carrier (c₁ ^ Fintype.card N₂ * c₂ ^ Fintype.card N₁) := by
  intro p _ C _ _ _ v R _ _ _ _ N₁ _ _ _ N₂ _ _ _ A₁ A₂
  refine ⟨PositivityTheory.HtPt.Re.hopfProd A₁ A₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; rfl
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_inl A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_inr A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_stab₁ A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_stab₂ A₁ A₂
  · intro c₁ c₂ h₁ h₂
    rw [PositivityTheory.HtPt.Re.hopfProd_carrier]
    exact PositivityTheory.HtPt.Re.hasColen_tn h₁ h₂

end PositivityTheory.HtPt.Re
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Twpair
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Twpair

theorem tw_pair : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, ζ n ^ p ^ n = 1) → X.PairingRegular B ζ → ∀ n, ∃ s ∈ prodSpan ((X.Γ n).btOrder ⊤), ∀ a b, s (lev p n a, lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p hpp C _ _ _ v O _ _ _ hv _ _ S _ G _ _ _ y La _ _ _ X B ζ hζ hreg n
  have : ValuationRing O := ValuationRing.of_integers v hv
  have := finite_levGrp (La := La) hpp.out.ne_zero n
  obtain ⟨β, hβ⟩ := exists_bichar p n B (ζ n) (hζ n)
  obtain ⟨s, hs⟩ := hreg n
  refine ⟨_, bichar_mem_prodSpan (henselian hv) (fun P => ?_) (X.Γ n) β s fun a b => ?_, fun a b => ?_⟩
  · exact (prime_eq_bot_or_maximal hv P.asIdeal).imp id fun h => PrimeSpectrum.ext h
  · obtain ⟨a, rfl⟩ := lev_surjective p n a
    obtain ⟨b, rfl⟩ := lev_surjective p n b
    rw [hβ]
    exact hs a b
  · exact congrArg Units.val (hβ a b)

end PositivityTheory.HtPt.Twpair
end

