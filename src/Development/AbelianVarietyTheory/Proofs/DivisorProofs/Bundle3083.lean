module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThetaFourierClassSumsDeeperIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliPointCompCompactificationStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndependentMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.Sep.TwistIndep

theorem isUnit_one_sub_pow {o : Type} [CommRing o] [IsDomain o] {ζ : o} {M : ℕ} (hζ : IsPrimitiveRoot ζ M)
    (hM : IsUnit (M : o)) {d : ℕ} (hd : ζ ^ d ≠ 1) : IsUnit (1 - ζ ^ d) := by
  have hη : (ζ ^ d) ^ M = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hsum : ∑ k ∈ Finset.range M, (ζ ^ d) ^ k = 0 := by
    have h := mul_geom_sum (ζ ^ d) M
    rw [hη, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hd)
  have hdiv : (1 - ζ ^ d) ∣ (M : o) := by
    have h : (M : o) = ∑ k ∈ Finset.range M, (1 - (ζ ^ d) ^ k) := by
      rw [Finset.sum_sub_distrib, hsum]; simp
    rw [h]
    exact Finset.dvd_sum fun k _ => by simpa using sub_dvd_pow_sub_pow (1 : o) (ζ ^ d) k
  exact isUnit_of_dvd_unit hdiv hM

theorem mem_maximalIdeal_of_map {R V : Type} [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V]
    (ev : R →+* V) {x : R} (h : ev x ∈ maximalIdeal V) : x ∈ maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h ⊢
  exact fun hu => h (hu.map ev)

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem stalk_isUnit (X₁ : Setup F W i) (z₁ : X₁.M.Z) {s : X₁.M.Z.presheaf.stalk z₁} {x : X₁.o₁}
    (hs : X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ x) (hx : IsUnit x) : IsUnit s := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨t, ht⟩ := exists_stalk_zeta X₁ z₁ y
  refine IsUnit.of_mul_eq_one t (X₁.M.stalkHom_injective z₁ ?_)
  rw [map_mul, hs, ht, ← map_mul, hy, map_one, map_one]

theorem pow_eq_of_sub_mem (X₁ : Setup F W i) (z₁ : X₁.M.Z) {s₁ s₂ : X₁.M.Z.presheaf.stalk z₁} {e₁ e₂ : ℕ}
    (h₁ : X₁.M.stalkHom z₁ s₁ = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e₁))
    (h₂ : X₁.M.stalkHom z₁ s₂ = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e₂))
    (hm : s₁ - s₂ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁)) : X₁.S.ζ ^ e₁ = X₁.S.ζ ^ e₂ := by
  haveI : IsDomain X₁.o₁ := by haveI := X₁.ar.ded; infer_instance
  by_contra hne
  obtain ⟨M, hM⟩ : ∃ M, M = (X₁.S.r * X₁.S.N) ^ 2 := ⟨_, rfl⟩
  have hζ : IsPrimitiveRoot X₁.S.ζ M := hM ▸ X₁.S.prim
  have hM0 : M ≠ 0 := by
    rw [hM]; exact pow_ne_zero _ (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  have hMu : IsUnit (M : X₁.o₁) := by rw [hM, Nat.cast_pow]; exact X₁.S.unit.pow 2
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  have hd : X₁.S.ζ ^ e₂ * X₁.S.ζ ^ (e₁ + k * e₂) = X₁.S.ζ ^ e₁ := by
    have h1 : e₂ + (e₁ + k * e₂) = e₁ + M * e₂ := by rw [hk, Nat.succ_eq_add_one]; ring
    rw [← pow_add, h1, pow_add, pow_mul, hζ.pow_eq_one, one_pow, _root_.mul_one]
  have hd1 : X₁.S.ζ ^ (e₁ + k * e₂) ≠ 1 := fun h => hne (by rw [← hd, h, _root_.mul_one])
  have hu : IsUnit (X₁.S.ζ ^ e₁ - X₁.S.ζ ^ e₂) := by
    have h3 : X₁.S.ζ ^ e₁ - X₁.S.ζ ^ e₂ = -(X₁.S.ζ ^ e₂ * (1 - X₁.S.ζ ^ (e₁ + k * e₂))) := by
      rw [← hd]; ring
    rw [h3]
    exact ((((hζ.isUnit hM0).pow e₂).mul (isUnit_one_sub_pow hζ hMu hd1))).neg
  have hs : IsUnit (s₁ - s₂) := stalk_isUnit X₁ z₁ (by rw [map_sub, h₁, h₂, map_sub]) hu
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  exact hm hs

theorem pow_eq_iff_cast (X₁ : Setup F W i) (a b : ℕ) :
    X₁.S.ζ ^ a = X₁.S.ζ ^ b ↔ (a : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = (b : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) := by
  have hpos : 0 < (X₁.S.r * X₁.S.N) ^ 2 :=
    pow_pos (Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)) 2
  have hord := X₁.S.prim.eq_orderOf
  rw [ZMod.natCast_eq_natCast_iff']
  constructor
  · intro h
    apply X₁.S.prim.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
    rw [hord, pow_mod_orderOf, pow_mod_orderOf]
    exact h
  · intro h
    calc X₁.S.ζ ^ a = X₁.S.ζ ^ (a % orderOf X₁.S.ζ) := (pow_mod_orderOf _ _).symm
      _ = X₁.S.ζ ^ (b % orderOf X₁.S.ζ) := by rw [← hord, h]
      _ = X₁.S.ζ ^ b := pow_mod_orderOf _ _

theorem affine_zero {G : Type} [AddCommGroup G] {M : ℕ} (hM : Odd M) (S : Set G) (hS : ∀ s ∈ S, -s ∈ S)
    (hne : S.Nonempty) (κ : ZMod M) (h : AddSubgroup.closure S →+ ZMod M)
    (hz : ∀ s (hs : s ∈ S), κ + h ⟨s, AddSubgroup.subset_closure hs⟩ = 0) :
    ∀ a (ha : a ∈ AddSubgroup.closure S), κ + h ⟨a, ha⟩ = 0 := by
  obtain ⟨s₀, hs₀⟩ := hne
  have h1 := hz s₀ hs₀
  have h2 := hz (-s₀) (hS s₀ hs₀)
  have hneg : (⟨-s₀, AddSubgroup.subset_closure (hS s₀ hs₀)⟩ : AddSubgroup.closure S) =
      -⟨s₀, AddSubgroup.subset_closure hs₀⟩ := rfl
  rw [hneg, map_neg] at h2
  have h2κ : (2 : ZMod M) * κ = 0 := by linear_combination h1 + h2
  have hcop : Nat.Coprime 2 M := (Nat.coprime_two_left).2 hM
  have hκ : κ = 0 := by
    have hu : IsUnit (2 : ZMod M) := by
      have := (ZMod.unitOfCoprime 2 hcop).isUnit
      rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
    exact hu.mul_right_eq_zero.1 h2κ
  subst hκ
  intro a ha
  rw [zero_add]
  refine AddSubgroup.closure_induction (p := fun x hx => h ⟨x, hx⟩ = 0) (fun x hx => ?_) ?_
    (fun x y hx hy h1 h2 => ?_) (fun x hx h1 => ?_) ha
  · simpa using hz x hx
  · exact map_zero h
  · have : (⟨x + y, add_mem hx hy⟩ : AddSubgroup.closure S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add (f := _), h1, h2, add_zero]
  · have : (⟨-x, neg_mem hx⟩ : AddSubgroup.closure S) = -⟨x, hx⟩ := rfl
    rw [this, map_neg, h1, neg_zero]

end GlobalTheory.Poinc.Sep.TwistIndep

namespace GlobalTheory.Poinc.Sep
open GlobalTheory.Poinc.Sep.TwistIndep

theorem twistSum_indep : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (Y₁ : Type) [AddCommGroup Y₁] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ Y₁) (𝔪₁ : UMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁) (C₁ : Type) (lab₁ : C₁ → X₁.S.Gam), (∀ c, lab₁ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₁ : (Fin 8 → Y₁) → C₁ → V₁, 𝔪₁.Terms x₀ lab₁ T₁ → ∀ c₁ : C₁, ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (Y₂ : Type) [AddCommGroup Y₂] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ Y₂) (𝔪₂ : UMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂) (C₂ : Type) (lab₂ : C₂ → X₁.S.Gam), (∀ c, lab₂ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₂ : (Fin 8 → Y₂) → C₂ → V₂, 𝔪₂.Terms x₀ lab₂ T₂ → ∀ c₂ : C₂, lab₁ c₁ = lab₂ c₂ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e₁ e₂ : ℕ, TwistSum X₁ z₁ act x₀ 𝔪₁ lab₁ T₁ sg c₁ τ e₁ → TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₂ → (∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab₁ c₁ + τ) / X₁.S.th x₀ ∧ ev₁ r ≠ 0) → TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₁ := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv sg hsg hpin V₁ _ _ _ ev₁ Y₁ _ m₁ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁
    V₂ _ _ _ ev₂ Y₂ _ m₂ t₂ δ₂ 𝔪₂ C₂ lab₂ hlab₂ T₂ hT₂ c₂ hlab τ hτ e₁ e₂ hS₁ _ hr'
  obtain ⟨r, hr, hr0⟩ := hr'
  obtain ⟨ε₁, ε₂, h1, h2, haff⟩ := GlobalTheory.T.twistedSum_exponents_affine_two_members g n F W Z i X₁ z₁ act x₀ hdiv sg hsg hpin V₁ ev₁ Y₁ m₁ t₁ δ₁ 𝔪₁ V₂ ev₂ Y₂ m₂ t₂ δ₂ 𝔪₂

  have hφ : ∀ b ∈ X₁.S.HH X₁.M z₁, X₁.S.ζ ^ ε₁ b τ = X₁.S.ζ ^ ε₂ b τ := by
    obtain ⟨κ, h, hκ⟩ := haff τ hτ
    have hsup : ∀ s (hs : s ∈ X₁.S.supI X₁.M z₁), κ + h ⟨s, AddSubgroup.subset_closure hs⟩ = 0 := by
      intro s hs
      have hsH : s ∈ X₁.S.HH X₁.M z₁ := AddSubgroup.subset_closure hs
      obtain ⟨U₁, hU₁⟩ := _root_.GlobalTheory.Poinc.Sep.exists_terms_single g n F W Z i X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ m₁ t₁ δ₁ 𝔪₁ s hsH
      obtain ⟨U₂, hU₂⟩ := _root_.GlobalTheory.Poinc.Sep.exists_terms_single g n F W Z i X₁ z₁ act x₀ hdiv V₂ ev₂ Y₂ m₂ t₂ δ₂ 𝔪₂ s hsH
      have hw₁ := h1 Unit (fun _ => s) (fun _ => hsH) U₁ hU₁ () τ hτ
      have hw₂ := h2 Unit (fun _ => s) (fun _ => hsH) U₂ hU₂ () τ hτ
      obtain ⟨q₁, hq₁⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ ε₁ s τ)
      obtain ⟨q₂, hq₂⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ ε₂ s τ)
      obtain ⟨u, hu⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨_, hs.2 (s + τ)⟩
      have hu' : X₁.M.stalkHom z₁ u = X₁.S.th (s + τ) / X₁.S.th s := by rw [← RatModel.coe_stalkEquiv, hu]
      have r₁ := _root_.GlobalTheory.Poinc.Sep.TwistResid.twist_resid g n F W Z i X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ m₁ t₁ δ₁ 𝔪₁ Unit (fun _ => s) (fun _ => hsH) U₁ hU₁ ()
        hs τ hτ sg _ hw₁ q₁ u hq₁ hu'
      have r₂ := _root_.GlobalTheory.Poinc.Sep.TwistResid.twist_resid g n F W Z i X₁ z₁ act x₀ hdiv V₂ ev₂ Y₂ m₂ t₂ δ₂ 𝔪₂ Unit (fun _ => s) (fun _ => hsH) U₂ hU₂ ()
        hs τ hτ sg _ hw₂ q₂ u hq₂ hu'
      have m₁' : q₁ * u - 1 ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
        mem_maximalIdeal_of_map ev₁ (by rwa [map_sub, map_one])
      have m₂' : q₂ * u - 1 ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
        mem_maximalIdeal_of_map ev₂ (by rwa [map_sub, map_one])
      have hunit : IsUnit u := by
        have hqu : IsUnit (q₁ * u) := by
          by_contra hn
          have hmem : q₁ * u ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := (IsLocalRing.mem_maximalIdeal _).2 hn
          have h1m : (1 : X₁.M.Z.presheaf.stalk z₁) ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := by
            simpa using sub_mem hmem m₁'
          exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1m)
        exact isUnit_of_mul_isUnit_right hqu
      have hdiff : (q₁ - q₂) * u ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := by
        have h3 := sub_mem m₁' m₂'
        rwa [show q₁ * u - 1 - (q₂ * u - 1) = (q₁ - q₂) * u by ring] at h3
      have hq : q₁ - q₂ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := by
        obtain ⟨v, hv⟩ := hunit.exists_right_inv
        have h4 := Ideal.mul_mem_right v _ hdiff
        rwa [_root_.mul_assoc, hv, _root_.mul_one] at h4
      have heq := (pow_eq_iff_cast X₁ _ _).1 (pow_eq_of_sub_mem X₁ z₁ hq₁ hq₂ hq)
      rw [← hκ s hsH, heq, sub_self]
    have hodd : Odd ((X₁.S.r * X₁.S.N) ^ 2) := by
      have h5 : Odd (X₁.S.r * X₁.S.N) := by
        obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
        rw [hj, X₁.ρ.N_eq]
        exact X₁.ρ.n_odd.pow.mul X₁.ρ.n_odd.pow.pow
      exact h5.pow
    have hz := affine_zero hodd (X₁.S.supI X₁.M z₁) (_root_.GlobalTheory.Poinc.Sep.neg_mem_supI g n F W Z i X₁ z₁) ⟨x₀, hdiv⟩ κ h hsup
    intro b hb
    rw [pow_eq_iff_cast, ← sub_eq_zero, hκ b hb]
    exact hz b hb

  obtain ⟨zt, hzt⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))
  obtain ⟨wt, hwt⟩ := _root_.GlobalTheory.Poinc.Sep.WtWd.wt_wd g n F W Z i X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ m₁ t₁ δ₁ 𝔪₁ sg τ hτ
  obtain ⟨s₁, hs₁⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ e₁)
  obtain ⟨s₀, hs₀⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ ε₁ (lab₁ c₁) τ)
  have hA := hS₁ zt (s₁ * r) hzt (by rw [map_mul, hs₁, hr, mul_div_assoc]) wt hwt
  have hB := h1 C₁ lab₁ hlab₁ T₁ hT₁ c₁ τ hτ zt (s₀ * r) hzt (by rw [map_mul, hs₀, hr, mul_div_assoc]) wt hwt
  haveI : IsNoetherianRing V₁ := 𝔪₁.cn.1
  have unique_sum {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
      {E Ix : Type} [AddCommGroup E] [Module R E] (hI : I ≤ Ideal.jacobson ⊥)
      {x : Ix → E} {s s' : E} (h : SumI I x s) (h' : SumI I x s') : s = s' := by
    classical
    obtain ⟨N, hN, hs, -, hconv⟩ := h

    obtain ⟨N', hN', hs', -, hconv'⟩ := h'
    set M := N ⊔ N' with hM
    have hMfg : M.FG := hN.sup hN'
    haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hMfg
    have hmem : s - s' ∈ M := M.sub_mem (Submodule.mem_sup_left hs) (Submodule.mem_sup_right hs')
    have hpow : ∀ n : ℕ, (⟨s - s', hmem⟩ : M) ∈ I ^ n • (⊤ : Submodule R M) := by
      intro n
      obtain ⟨S, hS⟩ := hconv n
      obtain ⟨S', hS'⟩ := hconv' n
      have h1 := hS (S ∪ S') Finset.subset_union_left
      have h2 := hS' (S ∪ S') Finset.subset_union_right
      have h3 : s - s' ∈ I ^ n • M := by
        have e : s - s' = (s - ∑ i ∈ S ∪ S', x i) - (s' - ∑ i ∈ S ∪ S', x i) := by abel
        rw [e]
        exact Submodule.sub_mem _ (Submodule.smul_mono le_rfl le_sup_left h1)
          (Submodule.smul_mono le_rfl le_sup_right h2)
      rw [← Submodule.map_subtype_top M, ← Submodule.map_smul''] at h3
      obtain ⟨y, hy, hyeq⟩ := h3
      have hy' : y = ⟨s - s', hmem⟩ := Subtype.ext hyeq
      rwa [← hy']
    have h0 : (⟨s - s', hmem⟩ : M) = 0 := by
      rw [Ideal.jacobson_bot] at hI
      have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) I hI
      rw [← Submodule.mem_bot R, ← hK, Submodule.mem_iInf]
      exact hpow
    exact sub_eq_zero.mp (congrArg Subtype.val h0)
  have hE := unique_sum (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hA hB
  rw [map_mul, map_mul] at hE
  have hE' : ev₁ s₁ = ev₁ s₀ := mul_right_cancel₀ hr0 hE
  have hm : s₁ - s₀ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
    mem_maximalIdeal_of_map ev₁ (by rw [map_sub, hE', sub_self]; exact zero_mem _)
  have hpe : X₁.S.ζ ^ e₁ = X₁.S.ζ ^ ε₁ (lab₁ c₁) τ := pow_eq_of_sub_mem X₁ z₁ hs₁ hs₀ hm

  have hpe2 : X₁.S.ζ ^ ε₂ (lab₂ c₂) τ = X₁.S.ζ ^ e₁ := by
    rw [hpe, ← hlab]
    exact (hφ _ (hlab₁ c₁)).symm
  have hF := h2 C₂ lab₂ hlab₂ T₂ hT₂ c₂ τ hτ
  intro zt' h' hzt' hh' wt' hwt'
  exact hF zt' h' hzt' (by rw [hpe2]; exact hh') wt' hwt'

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelGeometricCore
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UCore

theorem qW_one {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (μ : Fin 1 → X) :
    qW !![(1 : ℤ)] β μ = β (μ 0) (μ 0) := by
  simp [qW]

theorem classSums_core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y) (Q : Type) (F : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → F c κ = F c' κ) ∧ (∀ y c κ (μ : Fin 1 → Φ.X y), (∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → qW !![(1 : ℤ)] (Φ.β y) μ ≤ qW !![(1 : ℤ)] (Φ.β y) μ') → ‖ev' y (F c κ)‖ ≤ Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ (∀ y (μ : Fin 1 → Φ.X y), (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → μ' ≠ μ → qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ') → ∃ c κ, (∀ u, CongMod N (μ u) (k y (c u))) ∧ ‖ev' y (F c κ)‖ = Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀, (N : ℤ) ∣ LinearMap.det (γ.toLinearMap.restrictScalars ℤ) - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (F c κ) = F (fun u => γ (c u)) κ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ p _ z₁ Φ hΦ y₀ N₀
  choose ct hct using hΦ
  have hev : ∀ y a, Φ.ev y a = (ct y).val a := fun y => (hct y).1
  choose e he using fun y => (hct y).2
  obtain ⟨D, hD, hproj⟩ := GlobalTheory.UPoinc.UDeepP.exists_udeep_proj E H Dw hpq l Xo cf C X₁ N₀
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := fun x => ⟨D.X.normal.isDomain_stalk x, D.X.normal.isIntegrallyClosed_stalk x⟩
  obtain ⟨w₁⟩ := nonempty_uWit X₁
  obtain ⟨w₂, htie⟩ := GlobalTheory.UPoinc.UDeep.exists_tie E H Dw hpq l Xo cf C X₁ D w₁
  refine ⟨D.m, hD, D.dvd, D.X.Ω₁, inferInstance, D.alg, D.fd, D.gal, ?_⟩
  intro 𝔷 h𝔷 ev' hev' hle hlt
  obtain ⟨hB, hmax, -, hlift⟩ := GlobalTheory.Poinc.integralClosure_stalk_fibre X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q
    hN D.fin D.gen z₁
  obtain ⟨z₂, hz₂, h𝔷z⟩ := hmax 𝔷 h𝔷
  haveI := D.fd
  haveI := D.gal
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ := ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  have hl : ∀ y, ∃ y₂ : Sp (OO p) ⟶ D.X.M.Z, y₂ ≫ D.q = (ct y).y ∧
      ∀ b, ev' y b = D.X.M.val (gPt p ≫ y₂) (b : D.X.Ω₁) :=
    fun y => hlift p (ct y).y (ct y).cen (ev' y) (fun a => by rw [hev', hev]; rfl)
  choose y₂ hq hval using hl
  have hcen : ∀ y, y₂ y (cPt p) = z₂ := by
    intro y
    refine GlobalTheory.UPoinc.cPt_eq_of_norm_val_lt_one X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q hN D.fin D.gen z₁ 𝔷 h𝔷 z₂ hz₂ h𝔷z p (y₂ y) ?_ ?_
    · rw [← Scheme.Hom.comp_apply, hq]; exact (ct y).cen
    · intro b hb; rw [← hval]; exact hlt y b hb
  let ct₂ : ∀ y, UCTrait D.X p z₂ := fun y => { D.lift (ct y) (y₂ y) (hq y) with cen := hcen y }
  choose yy₁ hyy₁ using fun y => _root_.GlobalTheory.UPoinc.exists_uIsLabW E H Dw hpq l Xo cf C X₁ w₁ p z₁ (ct y)
  choose yy hyy hcomp using fun y => _root_.GlobalTheory.UPoinc.ULift.labels_lift E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ (ct y) (yy₁ y) (hyy₁ y) (y₂ y) (hq y)
  have hyy₂ : ∀ y, UIsLabW D.X w₂ (ct₂ y) (yy y) := fun y => hyy y
  choose d hd using fun y => _root_.GlobalTheory.UPoinc.exists_linearEquiv_labelled_of_uIsLabW E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ (ct₂ y₀) (ct₂ y) (yy y₀) (yy y) (hyy₂ y₀) (hyy₂ y)
  let k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y := fun y =>
    if h : y = y₀ then (by subst h; exact LinearEquiv.refl _ _) else (e y₀).trans ((d y).trans (e y).symm)
  have hk0 : k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) := by simp [k]
  have hk : ∀ y a x, yy y₀ a = QuotientAddGroup.mk (e y₀ x) → yy y a = QuotientAddGroup.mk (e y (k y x)) := by
    intro y a x hax
    by_cases h : y = y₀
    · subst h; simpa [hk0] using hax
    · simp only [k, dif_neg h, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      exact hd y a _ hax
  have hsurj := (GlobalTheory.UPoinc.uIsLab_onto_and_ker E H Dw hpq l Xo cf C D.X p z₂ (ct₂ y₀) (yy y₀) (hyy₂ y₀).uIsLab).1
  choose A hA using fun x : (ct y₀).T.P.D.toPre.X =>
    hsurj (QuotientAddGroup.mk x : ModN (D.X.S.r * D.X.S.N) (ct y₀).T.P.D.toPre.X)
  obtain ⟨f, t, hfO, hft⟩ := _root_.GlobalTheory.UPoinc.USum.main E H Dw hpq l Xo cf C X₁ D p z₁ z₂ hz₂
  have hfapp : (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ) := fun ct yy₁ h1 => (hft ct yy₁ h1).2.2
  let F : (Fin 1 → Φ.X y₀) → ↥(X₁.S.HH X₁.M z₁) → integralClosure (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ :=
    fun c κ => ⟨f (A (e y₀ (c 0))) κ, (hB _).2 fun z' hz' => hfO _ κ z' hz'⟩
  have hF : ∀ c κ, ((F c κ : integralClosure (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁) : D.X.Ω₁) = f (A (e y₀ (c 0))) κ :=
    fun _ _ => rfl
  refine ⟨k, ↥(X₁.S.HH X₁.M z₁), F, hk0, ?_, ?_, ?_, ?_⟩
  ·
    intro c c' κ hcc
    apply Subtype.ext
    rw [hF, hF]
    obtain ⟨w, hw⟩ := hcc 0
    refine GlobalTheory.UPoinc.DeepSame.deep_eq_of_congMod E H Dw hpq l Xo cf C X₁ D p z₁ z₂ hz₂ f t hfO hfapp w₁ w₂ htie hproj (ct₂ y₀) (yy y₀) (hyy₂ y₀) _ _ _ _
      (hA _) (hA _) ⟨e y₀ w, ?_⟩ κ
    rw [hw, map_add (f := _), map_nsmul]
  ·
    intro y c κ μ hμ hmin
    rw [hval y, qW_one]
    obtain ⟨hle_t, -, -⟩ := hft (ct y) (yy₁ y) (hyy₁ y).uIsLab
    have hyyA : yy y (A (e y₀ (c 0))) = QuotientAddGroup.mk (e y (k y (c 0))) := hk y _ _ (hA _)
    refine GlobalTheory.UPoinc.class_limit_norm_le p (Φ.X y) (ct y).T.P.D.toPre.X (e y).toAddEquiv (Φ.β y) (ct y).T.be (Φ.sc y) (ct y).sc
      (Φ.sc_pos y) (he y) D.m (fun μ' => t (ct y) (yy₁ y) μ' κ) (fun μ' => hle_t μ' κ) _ _
      (hfapp (ct y) (yy₁ y) (hyy₁ y).uIsLab (y₂ y) (hq y) (hcen y) (yy y) (hyy y).uIsLab (hcomp y) _ _ κ hyyA) (μ 0) ?_ ?_
    · obtain ⟨w, hw⟩ := hμ 0
      exact ⟨e y w, by simp [hw, map_add (f := _), map_nsmul]⟩
    · intro x' hx'
      have := hmin (fun _ => x') (fun u => by rw [Subsingleton.elim u 0]; exact hx')
      simpa [qW_one] using this
  ·
    intro y μ huniq
    obtain ⟨-, heq_t, -⟩ := hft (ct y) (yy₁ y) (hyy₁ y).uIsLab
    obtain ⟨κ, hκ⟩ := heq_t (e y (μ 0))
    refine ⟨fun u => (k y).symm (μ u), κ, fun u => ⟨0, by simp⟩, ?_⟩
    rw [hval y, qW_one]
    have hyyA : yy y (A (e y₀ ((k y).symm (μ 0)))) = QuotientAddGroup.mk (e y (μ 0)) := by
      simpa using hk y _ _ (hA (e y₀ ((k y).symm (μ 0))))
    refine GlobalTheory.UPoinc.classSum_norm_eq_of_unique_least p (Φ.X y) (ct y).T.P.D.toPre.X (e y).toAddEquiv (Φ.β y) (ct y).T.be (Φ.sc y) (ct y).sc
      (Φ.sc_pos y) (he y) D.m (fun μ' => t (ct y) (yy₁ y) μ' κ) (fun μ' => (hft (ct y) (yy₁ y) (hyy₁ y).uIsLab).1 μ' κ) _ _
      (hfapp (ct y) (yy₁ y) (hyy₁ y).uIsLab (y₂ y) (hq y) (hcen y) (yy y) (hyy y).uIsLab (hcomp y) _ _ κ hyyA) (μ 0)
      ⟨0, by simp⟩ hκ ?_
    intro x' hx' hne
    have := huniq (fun _ => x') (fun u => by rw [Subsingleton.elim u 0]; exact hx')
      (fun h => hne (congrFun h 0))
    simpa [qW_one] using this
  ·
    intro σ hσ
    obtain ⟨σ', hσ'⟩ := GlobalTheory.UPoinc.intClosure_aut_extends X₁.o₁ X₁.Ω₁ D.X.Ω₁ X₁.M z₁ σ
    obtain ⟨s, hs_pt, hs_q, hs_val⟩ := GlobalTheory.Poinc.GalAut.autAct X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q
      hN D.fin D.gen σ'
    have hcs : (y₂ y₀ ≫ s) (cPt p) = z₂ := by
      refine GlobalTheory.UPoinc.cPt_eq_of_norm_val_lt_one X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q hN D.fin D.gen z₁ 𝔷 h𝔷 z₂ hz₂ h𝔷z p _ ?_ ?_
      · rw [← Scheme.Hom.comp_apply, Category.assoc, hs_q, hq]; exact (ct y₀).cen
      · intro b hb
        rw [← Category.assoc, hs_val, hσ', ← hval]
        apply hlt y₀
        have h2 : b ∈ 𝔷.comap σ := by rw [hσ]; exact hb
        exact h2
    have hsz : s z₂ = z₂ := by
      have h3 := hcs
      rw [Scheme.Hom.comp_apply, hcen y₀] at h3
      exact h3
    obtain ⟨aσ, -, haσ⟩ := _root_.GlobalTheory.UPoinc.UGalLab.main E H Dw hpq l Xo cf C X₁ D σ' s hs_pt
    have hqs : (y₂ y₀ ≫ s) ≫ D.q = (ct y₀).y := by rw [Category.assoc, hs_q, hq]
    obtain ⟨yy', hyy', hcomp'⟩ := _root_.GlobalTheory.UPoinc.ULift.labels_lift E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ (ct y₀) (yy₁ y₀) (hyy₁ y₀) (y₂ y₀ ≫ s) hqs
    let ct₂' : UCTrait D.X p z₂ := { D.lift (ct y₀) (y₂ y₀ ≫ s) hqs with cen := hcs }
    have hyy'₂ : UIsLabW D.X w₂ ct₂' yy' := hyy'
    obtain ⟨g, hg⟩ := _root_.GlobalTheory.UPoinc.exists_linearEquiv_labelled_of_uIsLabW E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ (ct₂ y₀) ct₂' (yy y₀) yy' (hyy₂ y₀) hyy'₂
    have hrel : ∀ x, yy' x = yy y₀ (aσ x) :=
      haσ p z₁ (ct y₀) (yy₁ y₀) (hyy₁ y₀).uIsLab (y₂ y₀) (hq y₀) hqs (yy y₀) yy' (hyy y₀).uIsLab (hcomp y₀) hyy'.uIsLab hcomp'
    let γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀ := (e y₀).trans (g.trans (e y₀).symm)
    have hL : 3 ≤ X₁.S.r * X₁.S.N := by
      have h6 := X₁.big.2.2
      have : 1 ≤ X₁.S.N ^ X₁.S.g * X₁.S.g.factorial :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (by have := X₁.S.N_ge; omega)) (Nat.factorial_ne_zero _))
      omega
    have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
      rw [D.sq]; exact D.dvd.trans ((dvd_pow_self _ two_ne_zero).trans (dvd_mul_left _ _))
    have hLpos : 0 < D.X.S.r * D.X.S.N :=
      Nat.mul_pos (by have := D.X.S.r_pos; omega) (by have := D.X.S.N_ge; omega)
    have htf : ∀ (n : ℕ) (x : (ct y₀).T.P.D.toPre.X), 0 < n → n • x = 0 → x = 0 := by
      intro n x hn hx
      have h1 : ((n : ℤ)) • (e y₀).symm x = 0 := by
        rw [natCast_zsmul, ← map_nsmul, hx, map_zero]
      rcases smul_eq_zero.1 h1 with h | h
      · omega
      · simpa using congrArg (e y₀) h
    have hcongY := GlobalTheory.UPoinc.compat_forces_congMod X₁.S.Gam D.X.S.Gam (ct y₀).T.P.D.toPre.X (X₁.S.r * X₁.S.N) (D.X.S.r * D.X.S.N)
      (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) (Nat.div_mul_cancel hdvd) hLpos htf D.lab (yy₁ y₀)
      (GlobalTheory.UPoinc.uIsLab_onto_and_ker E H Dw hpq l Xo cf C X₁ p z₁ (ct y₀) (yy₁ y₀) (hyy₁ y₀).uIsLab).1 (yy y₀) yy' (hcomp y₀) hcomp'
      g.toLinearMap.toAddMonoidHom (fun a μ h => hg a μ h)
    have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x := by
      intro x
      obtain ⟨w, hw⟩ := hcongY (e y₀ x)
      have hw' : g (e y₀ x) = e y₀ x + (X₁.S.r * X₁.S.N) • w := hw
      refine ⟨(e y₀).symm w, ?_⟩
      simp only [γ, LinearEquiv.trans_apply]
      rw [hw', map_add (f := _), map_nsmul, LinearEquiv.symm_apply_apply]
    refine ⟨γ, GlobalTheory.UPoinc.dvd_det_sub_one_of_congMod_three_le (Φ.X y₀) (X₁.S.r * X₁.S.N) D.m hL (γ.restrictScalars ℤ) hcong, hcong, ?_⟩
    · intro c κ
      apply Subtype.ext
      rw [← hσ']
      show σ' (f (A (e y₀ (c 0))) κ) = f (A (e y₀ (γ (c 0)))) κ
      refine GlobalTheory.UPoinc.GalLab.main E H Dw hpq l Xo cf C X₁ D p z₁ z₂ hz₂ f t hfO hfapp w₁ w₂ htie hproj σ' s hs_q hs_val hsz aσ
        (fun ct yy₁ h1 y h h' yy yy' h2 h3 h4 h5 => haσ p z₁ ct yy₁ h1 y h h' yy yy' h2 h3 h4 h5)
        (ct₂ y₀) (yy y₀) (hyy₂ y₀) _ _ _ _ (by rw [← hrel]; exact hg _ _ (hA _)) (hA _) ⟨0, ?_⟩ κ
      simp [γ]

end GlobalTheory.UPoinc.UCore
end
end

