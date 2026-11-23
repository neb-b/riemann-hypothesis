module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjOfLawUnitInverseAgreeAway
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.SpreadGrp

theorem grpObj_of_agree : ∀ (R : Type) [CommRing R] [IsDomain R] (f g : R), f ≠ 0 → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), Flat q → IsSeparated q → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsCommMonObj A → ∀ i : A.left ⟶ X, IsPullback i A.hom q (awayMap f) → ∀ (H : Over (Sp (Localization.Away g))) (h : H.left ⟶ X), IsPullback h H.hom q (awayMap g) → ∀ (m : H ⊗ H ⟶ H) (n : H ⟶ H) (o : 𝟙_ (Over (Sp (Localization.Away g))) ⟶ H), (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a b : Over.mk t₁ ⟶ H) (a' b' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → b.left ≫ h = b'.left ≫ i → (lift a b ≫ m).left ≫ h = (a' * b').left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a : Over.mk t₁ ⟶ H) (a' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → (a ≫ n).left ≫ h = (a'⁻¹).left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)), t₁ ≫ awayMap g = t₀ ≫ awayMap f → t₁ ≫ o.left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i) → ∃ _ : GrpObj H, MulAgree H A h i := by
  intro R _ _ f g hf X q hq hs A _ _ i hA H h hH m n o hm hn ho
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsSchemeTheoreticallyDominant (awayMap f) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective
      (CommRingCat.ofHom (algebraMap R (Localization.Away f))) hinj
  have : Flat (awayMap g) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (Submonoid.powers g))
  have : Flat H.hom := MorphismProperty.of_isPullback hH hq
  have : IsSeparated H.hom := MorphismProperty.of_isPullback hH hs
  have := ExtUnique.flat_tensorUnit (S := Sp (Localization.Away g))
  have := ExtUnique.flat_tensorObj H H
  have := ExtUnique.flat_tensorObj (𝟙_ _) H
  have := ExtUnique.flat_tensorObj H (𝟙_ _)
  have := ExtUnique.flat_tensorObj (H ⊗ H) H
  let j := pullback.fst (awayMap g) (awayMap f)
  let k := pullback.snd (awayMap g) (awayMap f)
  have w : ∀ T : Over (pullback (awayMap g) (awayMap f)), (T.hom ≫ j) ≫ awayMap g = (T.hom ≫ k) ≫ awayMap f := by
    intro T; simp only [Category.assoc, j, k, pullback.condition]

  have key : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} {t₀ : T ⟶ Sp (Localization.Away f)},
      t₁ ≫ awayMap g = t₀ ≫ awayMap f → ∀ a : Over.mk t₁ ⟶ H, ∃ a' : Over.mk t₀ ⟶ A, a.left ≫ h = a'.left ≫ i := by
    intro T t₁ t₀ e a
    have e' : (a.left ≫ h) ≫ q = t₀ ≫ awayMap f := by
      rw [Category.assoc, hH.w, ← Category.assoc, Over.w a]; exact e
    exact ⟨Over.homMk (hA.lift (a.left ≫ h) t₀ e') (hA.lift_snd _ _ _), (hA.lift_fst _ _ _).symm⟩

  have inj : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} (a b : Over.mk t₁ ⟶ H),
      a.left ≫ h = b.left ≫ h → a = b := by
    intro T t₁ a b e
    exact Over.OverMorphism.ext (hH.hom_ext e (by rw [Over.w a, Over.w b]))
  have hone : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} {t₀ : T ⟶ Sp (Localization.Away f)},
      t₁ ≫ awayMap g = t₀ ≫ awayMap f → (toUnit (Over.mk t₁) ≫ o).left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i := by
    intro T t₁ t₀ e
    simpa using ho T t₁ t₀ e
  letI : MonObj H :=
    { one := o
      mul := m
      one_mul := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ snd _ _ = x := ⟨_, rfl⟩
        have ht : t = lift (toUnit _) x :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        rw [lift_whiskerRight_assoc, lift_leftUnitor_hom]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hone (w T)) hx', _root_.one_mul, hx']
      mul_one := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ fst _ _ = x := ⟨_, rfl⟩
        have ht : t = lift x (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        rw [lift_whiskerLeft_assoc, lift_rightUnitor_hom]
        apply inj
        rw [hm _ _ _ _ _ _ _ hx' (hone (w T)), _root_.mul_one, hx']
      mul_assoc := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ fst _ _ ≫ fst _ _ = x := ⟨_, rfl⟩
        obtain ⟨y, hy⟩ : ∃ y, t ≫ fst _ _ ≫ snd _ _ = y := ⟨_, rfl⟩
        obtain ⟨z, hz⟩ : ∃ z, t ≫ snd _ _ = z := ⟨_, rfl⟩
        have ht : t = lift (lift x y) z := by
          ext <;> simp [← hx, ← hy, ← hz]
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        obtain ⟨y', hy'⟩ := key (w T) y
        obtain ⟨z', hz'⟩ := key (w T) z
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hm _ _ _ _ _ _ _ hx' hy') hz', hm _ _ _ _ _ _ _ hx' (hm _ _ _ _ _ _ _ hy' hz'),
          _root_.mul_assoc] }
  letI : GrpObj H :=
    { inv := n
      left_inv := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x', hx'⟩ := key (w T) t
        change _ ≫ lift n (𝟙 H) ≫ m = _ ≫ toUnit H ≫ o
        rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hn _ _ _ _ _ hx') hx', inv_mul_cancel, hone (w T)]
      right_inv := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x', hx'⟩ := key (w T) t
        change _ ≫ lift (𝟙 H) n ≫ m = _ ≫ toUnit H ≫ o
        rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ hx' (hn _ _ _ _ _ hx'), mul_inv_cancel, hone (w T)] }
  exact ⟨inferInstance, fun T t₁ t₂ a b a' b' ha hb => hm T t₁ t₂ a b a' b' ha hb⟩

end GlobalTheory.Desc.SpreadGrp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasApproxPoincareSeriesNatMultiple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem approxAt_mul_of_one_le (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0})
    (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ) (hm : 1 ≤ m) (hd : ApproxAt X₁ φ d) :
    ApproxAt X₁ φ (d * m) := by
  intro p _ z₁ c₀ e
  obtain ⟨f, hf0, hf⟩ := hd p z₁ c₀ e
  have hpow : ∀ c : CTrait X₁ p z₁, ‖c.val (f ^ m)‖ = ‖c.val f‖ ^ m := fun c => by
    rw [CTrait.val_eq_valInt, CTrait.val_eq_valInt, map_pow]
    push_cast
    exact norm_pow _ _
  have hexp : ∀ c : CTrait X₁ p z₁, Real.exp (-(c.sc * (((d * m : ℕ) : ℝ) * φ.evalZ c.T.β))) =
      Real.exp (-(c.sc * (d * φ.evalZ c.T.β))) ^ m := fun c => by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨f ^ m, ?_, fun c => ?_⟩
  · rw [hpow, hf0, hexp]
  · rcases hf c with h1 | ⟨h, hh, h2⟩
    · left
      rw [hpow, hexp]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 m
    · right
      refine ⟨h, hh, ?_⟩
      rw [hpow]
      exact (pow_le_of_le_one (norm_nonneg _) (c.norm_val_le f) (by omega)).trans h2

theorem approxAt_mul : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ), 1 ≤ m → ApproxAt X₁ φ d → ApproxAt X₁ φ (d * m) := approxAt_mul_of_one_le

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyHeightOnePrimesOfFlat
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtale

theorem hart_of_flat : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (B : Type) [CommRing B] [Algebra A B] [Module.Flat A B], GlobalTheory.GoodEtale.Hart A B B := by
  intro A _ _ _ _ B _ _ _ a ha m hm
  classical
  let I : Ideal A := Ideal.comap (algebraMap A B) ((Ideal.span {algebraMap A B a}).colon {m})
  have hI : ∀ u, u ∈ I ↔ ∃ m' : B, algebraMap A B u * m = algebraMap A B a * m' := by
    intro u
    simp only [I, Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [← hc, mul_comm]⟩
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [hc, mul_comm]⟩
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
  have hm' : ∀ s : S, ∃ m' : B, algebraMap A B s * m = algebraMap A B a * m' := fun s =>
    (hI s).1 (hS ▸ Submodule.subset_span s.2)
  choose m' hm'' using hm'
  let f : (S → A) →ₗ[A] A × (S → A) :=
    LinearMap.prod (∑ s : S, (LinearMap.proj s).smulRight (s : A)) (a • LinearMap.id)
  let x : A × (S → A) →ₗ[A] B := (LinearMap.fst A A (S → A)).smulRight m -
    ∑ s : S, ((LinearMap.proj s).comp (LinearMap.snd A A (S → A))).smulRight (m' s)
  have hxf : x ∘ₗ f = 0 := by
    apply LinearMap.ext
    intro c
    have e : ∀ s : S, (c s * s) • m = (a * c s) • m' s := by
      intro s
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, mul_assoc, hm'' s]; ring
    simp [x, f, Finset.sum_smul, e]
  obtain ⟨k, α, y, hxy, hαf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  set v := α ((1 : A), (0 : S → A)) with hvdef
  have hsv : ∀ s : S, ∀ j, (s : A) * v j ∈ Ideal.span {a} := by
    intro s j
    have e : f (Pi.single s 1) = (s : A) • ((1 : A), (0 : S → A)) + a • ((0 : A), Pi.single s 1) := by
      ext t
      · simp [f, Pi.single_apply]
      · simp [f]
    have h0 : α (f (Pi.single s 1)) = 0 := by
      simpa using congrArg (fun g => g (Pi.single s 1)) hαf
    rw [e, map_add (f := _), map_smul, map_smul] at h0
    have h1 := congrArg (fun w => w j) h0
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero,
      Pi.zero_apply] at h1
    rw [Ideal.mem_span_singleton']
    exact ⟨-(α ((0 : A), Pi.single s 1)) j, by rw [← hvdef] at h1; linear_combination -h1⟩
  have hv : ∀ j, v j ∈ Ideal.span {a} := by
    intro j
    apply GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one
    intro q hq h1
    obtain ⟨u, hu, m'', h⟩ := hm q hq h1
    refine ⟨u, hu, ?_⟩
    have huI : u ∈ I := (hI u).2 ⟨m'', by simpa [smul_eq_mul] using h⟩
    have hle : I ≤ (Ideal.span {a}).colon {v j} := by
      rw [← hS, Submodule.span_le]
      intro s hs
      rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul]
      exact hsv ⟨s, hs⟩ j
    have := hle huI
    rwa [Submodule.mem_colon_singleton, smul_eq_mul] at this
  choose z hz using fun j => Ideal.mem_span_singleton'.mp (hv j)
  refine ⟨y (Finsupp.equivFunOnFinite.symm z), ?_⟩
  have hv' : v = a • Finsupp.equivFunOnFinite.symm z := by
    ext j; simp [← hz j, mul_comm]
  have hmx : m = x ((1 : A), (0 : S → A)) := by simp [x]
  rw [hmx, hxy, LinearMap.comp_apply, ← hvdef, hv', map_smul, Algebra.smul_def, smul_eq_mul]

end GlobalTheory.GoodEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyQuotientSpanPowRetraction
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem hartRep_one (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (a : A) (r : R)
    (h : ∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : R, algebraMap A R u * r - algebraMap A R a * m' ∈ Ideal.span {t}) :
    ∃ r' : R, r - algebraMap A R a * r' ∈ Ideal.span {t} := by
  have hρa : ∀ b, ρ (algebraMap A R b) = b := fun b => by simpa using congrArg (fun f => f b) hρ
  have hmem : ρ r ∈ Ideal.span {a} := by
    refine GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one a (ρ r) fun p hp hp1 => ?_
    obtain ⟨u, hu, m', hm⟩ := h p hp hp1
    refine ⟨u, hu, Ideal.mem_span_singleton.2 ⟨ρ m', ?_⟩⟩
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, map_mul, hρa, hρa, sub_eq_zero] at hm
    exact hm
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hmem
  refine ⟨algebraMap A R b, ?_⟩
  rw [← hker, RingHom.mem_ker, map_sub, map_mul, hρa, hρa, hb, sub_self]

theorem hartRep (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R) (a : A) (ha : a ≠ 0) :
    ∀ n : ℕ, ∀ r : R, (∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : R, algebraMap A R u * r - algebraMap A R a * m' ∈ Ideal.span {t ^ n}) →
    ∃ r' : R, r - algebraMap A R a * r' ∈ Ideal.span {t ^ n} := by
  have hρa : ∀ b, ρ (algebraMap A R b) = b := fun b => by simpa using congrArg (fun f => f b) hρ
  have ht0 : ρ t = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self t
  intro n
  induction n with
  | zero => intro r _; exact ⟨0, by simp⟩
  | succ n ih =>
    intro r hr
    obtain ⟨x, hx⟩ := hartRep_one A R ρ hρ t hker a r fun p hp hp1 => by
      obtain ⟨u, hu, m', hm⟩ := hr p hp hp1
      exact ⟨u, hu, m', Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self t n.succ_ne_zero) hm⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hx
    obtain ⟨y', hy'⟩ := ih y fun p hp hp1 => by
      obtain ⟨u, hu, m', hm⟩ := hr p hp hp1
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hm
      have key : t * (algebraMap A R u * y) - algebraMap A R a * (m' - algebraMap A R u * x)
          = t ^ (n + 1) * q := by
        linear_combination hq - (algebraMap A R u) * hy
      have h2 : a * ρ (m' - algebraMap A R u * x) = 0 := by
        have := congrArg ρ key
        rw [map_sub] at this
        simp only [map_mul, map_pow, ht0, hρa, zero_mul, zero_sub, zero_pow n.succ_ne_zero,
          neg_eq_zero] at this
        exact this
      have h3 : m' - algebraMap A R u * x ∈ Ideal.span {t} := by
        rw [← hker, RingHom.mem_ker]
        exact (mul_eq_zero.1 h2).resolve_left ha
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 h3
      refine ⟨u, hu, z, Ideal.mem_span_singleton.2 ⟨q, ?_⟩⟩
      have h4 : t * (algebraMap A R u * y - algebraMap A R a * z - t ^ n * q) = 0 := by
        rw [hz] at key
        linear_combination key
      exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff ht).1 h4)
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.1 hy'
    refine ⟨x + t * y', Ideal.mem_span_singleton.2 ⟨s, ?_⟩⟩
    linear_combination hy + t * hs

theorem hart_quot : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    ∀ n : ℕ, GlobalTheory.GoodEtale.Hart A R (R ⧸ Ideal.span {t} ^ n) := by
  intro A R _ _ _ _ _ _ ρ hρ t hker ht n a ha m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨r', hr'⟩ := hartRep A R ρ hρ t hker ht a ha n r fun p hp hp1 => by
    obtain ⟨u, hu, m', hm'⟩ := hm p hp hp1
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m'
    refine ⟨u, hu, s, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
      Ideal.Quotient.eq, Ideal.span_singleton_pow] at hm'
    exact hm'
  refine ⟨Ideal.Quotient.mk _ r', ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq, Ideal.span_singleton_pow]
  exact hr'

end GlobalTheory.GoodEtaleSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffExistsSmallSectionDiffe
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LeIff

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nonzeroLocus_zero {M : LB X} : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (0 : LB.Sec M) = ⊥ := by
  simp [ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus]

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem dict_zero (P : Pair p) (a b : ℤ) {M : HermLB p} (e : M.B.Sec → X.functionField)
    (he : ∀ (u : M.B.Sec) (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j →
      (x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u ↔ UnitAt x (P.loc a b (e u) i j))) : e 0 = 0 := by
  by_contra h
  obtain ⟨i, hi⟩ := exists_chart P.L.isLB (genericPoint X)
  obtain ⟨j, hj⟩ := exists_chart P.A.isLB (genericPoint X)
  have hne : P.loc a b (e 0) i j ≠ 0 := by
    simp only [Pair.loc]
    exact mul_ne_zero (mul_ne_zero h (zpow_ne_zero _ (P.r i).ne_zero)) (zpow_ne_zero _ (P.r' j).ne_zero)
  have hmem := (he 0 _ i j hi hj).2 (unitAt_genericPoint hne)
  rw [nonzeroLocus_zero] at hmem
  simp at hmem

theorem rep_diff (P : Pair p) : P.Rep 1 (-1) (P.L.tens P.A.dual) := by
  obtain ⟨h1, h2, -⟩ := Pair.rep_base k X p P
  have h3 : P.Rep 0 (-1) P.A.dual := by
    have := Pair.rep_dual k X p P 0 1 _ h2
    rwa [neg_zero] at this
  have := Pair.rep_tens k X p P 1 0 0 (-1) _ _ h1 h3
  rwa [add_zero, zero_add] at this

def scaleL (P : Pair p) (f : X.functionFieldˣ) : Pair p :=
  ⟨P.L, P.A, fun i => f * P.r i, P.r', fun i j h => by
    simp only [Units.val_mul]
    rw [P.hr i j h]
    ring, P.hr'⟩

theorem scaleL_loc (P : Pair p) (f : X.functionFieldˣ) (i : P.L.B.ι) (j : P.A.B.ι) :
    (scaleL P f).loc 1 (-1) 1 i j = P.loc 1 (-1) f i j := by
  simp only [Pair.loc, scaleL, Units.val_mul, zpow_one, one_mul]

end GlobalTheory.HSNef.LeIff


open GlobalTheory.HSNef.LeIff in
theorem GlobalTheory.HSNef.le_iff_exists_smallSec : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B : HermLB p, Le B A ↔ ∃ s ∈ (A.tens B.dual).smallSec, s ≠ 0 := by
  intro k _ X _ p A B
  constructor
  · rintro ⟨P, rfl, rfl, h1H, h1n⟩
    obtain ⟨e, -, hrange, hnorm, hloc⟩ := RepDict.rep_dict k X p P 1 (-1) _ (rep_diff P)
    obtain ⟨u, hu⟩ : (1 : X.functionField) ∈ Set.range e := by rw [hrange]; exact h1H
    refine ⟨u, fun σ y => ?_, ?_⟩
    · rw [← hnorm, hu]
      have h0 := nu_nonneg P 1 (-1) σ y 1
      have h1 := h1n σ y
      nlinarith
    · rintro rfl
      rw [dict_zero P 1 (-1) e hloc] at hu
      exact zero_ne_one hu
  · rintro ⟨s, hs, hs0⟩
    obtain ⟨P, hPL, hPA⟩ := exists_pair A B
    subst hPL hPA
    obtain ⟨e, hinj, hrange, hnorm, hloc⟩ := RepDict.rep_dict k X p P 1 (-1) _ (rep_diff P)
    have hfH : e s ∈ P.H 1 (-1) := by
      have : e s ∈ Set.range e := ⟨s, rfl⟩
      rw [hrange] at this
      exact this
    have hf0 : e s ≠ 0 := fun h => hs0 (hinj (h.trans (dict_zero P 1 (-1) e hloc).symm))
    have hfn : ∀ σ (y : CxPts p σ), P.nu 1 (-1) σ y (e s) ≤ 1 := fun σ y => by
      have h := hnorm s σ y
      have h' := hs σ y
      have h0 := nu_nonneg P 1 (-1) σ y (e s)
      nlinarith
    refine ⟨scaleL P (Units.mk0 _ hf0), rfl, rfl, fun x i j hi hj => ?_, fun σ y => ?_⟩
    · rw [show (scaleL P (Units.mk0 _ hf0)).loc 1 (-1) 1 i j = P.loc 1 (-1) (e s) i j from
        scaleL_loc P (Units.mk0 _ hf0) i j]
      exact hfH x i j hi hj
    · have := hfn σ y
      simp only [Pair.nu] at this ⊢
      rw [show ∀ i j, (scaleL P (Units.mk0 _ hf0)).loc 1 (-1) 1 i j = P.loc 1 (-1) (e s) i j from
        scaleL_loc P (Units.mk0 _ hf0)]
      exact this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyRestrictAdjointBijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdjHyp

def counitCoef {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) {G : C' ⥤ C} {H : C ⥤ C'} (adj : G ⊣ H) :
    CoefMap (RingHom.id R) (G ⋙ F) F where
  G := H
  α V := (mp F (adj.counit.app V)).toRingHom
  naturality {V V'} φ b := by
    change mp F (adj.counit.app V') (mp F (G.map (H.map φ)) b) = mp F φ (mp F (adj.counit.app V) b)
    rw [← mp_comp, ← mp_comp]
    have e := adj.counit.naturality φ
    simp only [Functor.comp_map, Functor.id_map] at e
    rw [e]
  smul V r b := by
    change mp F (adj.counit.app V) (r • b) = r • mp F (adj.counit.app V) b
    exact map_smul _ r b

theorem main : ∀ (R : Type) [CommRing R] (C C' : Type) [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C'), (G ⊣ H) →
    Function.Bijective (pullHyp1 (CoefMap.restrict F G)) := by
  intro R _ C C' _ _ F G H adj
  have hl : ∀ c, pullHyp1 (counitCoef F adj) (pullHyp1 (CoefMap.restrict F G) c) = c := by
    intro c
    rw [← pullHyp1_comp]
    exact (pullHyp1_eq_of_natTrans _ (CoefMap.id F) adj.counit (fun T b ↦ rfl) c).trans
      (pullHyp1_id c)
  have hr : ∀ c, pullHyp1 (CoefMap.restrict F G) (pullHyp1 (counitCoef F adj) c) = c := by
    intro c
    rw [← pullHyp1_comp]
    refine ((pullHyp1_eq_of_natTrans (CoefMap.id (G ⋙ F))
      ((counitCoef F adj).comp (CoefMap.restrict F G)) adj.unit (fun T b ↦ ?_) c).symm.trans
      (pullHyp1_id c))
    change mp F (adj.counit.app (G.obj T)) (mp F (G.map (adj.unit.app T)) b) = b
    exact (mp_comp F (G.map (adj.unit.app T)) (adj.counit.app (G.obj T)) b).symm.trans
      ((congrArg (fun ξ ↦ mp F ξ b) (adj.left_triangle_components T)).trans (mp_id F (G.obj T) b))
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

end GlobalTheory.AdjHyp
end
end

