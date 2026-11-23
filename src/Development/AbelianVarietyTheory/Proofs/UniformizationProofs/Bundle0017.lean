module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFactorThroughCubicalEvenIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem addition_factor_through_cubical_even_iso : ∀ (H U : Type) [CommGroup H] [CommGroup U] (W sL sM : H → U) (cL cM : H → H → H → U) (rL rM : U), rM = W 1 * rL → (∀ x, sM x * W x = W x⁻¹ * sL x) → (∀ x y u, cM x y u * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * cL x y u) → ∀ x y, W x ^ 2 * W y ^ 2 * (cL x y y⁻¹ * (sL y)⁻¹ * rL ^ 2) = cM x y y⁻¹ * (sM y)⁻¹ * rM ^ 2 * (W (x * y) * W (x * y⁻¹)) := by
  intro H U _ _ W sL sM cL cM rL rM hr hs hc x y
  have h1 := hc x y y⁻¹
  rw [mul_inv_cancel, mul_inv_cancel_right] at h1
  have h2 : sM y = W y⁻¹ * sL y * (W y)⁻¹ := eq_mul_inv_of_mul_eq (hs y)
  have h3 : cM x y y⁻¹ = W x * W x * W y * W y⁻¹ * cL x y y⁻¹ *
      (W (x * y) * W (x * y⁻¹) * W 1 * W 1)⁻¹ := by
    apply eq_mul_inv_of_mul_eq
    rw [← h1]
    simp only [_root_.mul_assoc]
  rw [h2, h3, hr]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AppWhiskerRightInjectiveOfFlat
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem app_whiskerRight_injective_of_flat :
    ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (φ : T' ⟶ T), Function.Injective φ.left.appTop.hom → ∀ U : (T ⊗ B).left.Opens, Function.Injective ((φ ▷ B).left.app U).hom := by
  intro S B T T' _ _ _ φ hφ U
  have hd : IsSchemeTheoreticallyDominant φ.left := by
    refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
    rw [Scheme.Hom.ker_apply]
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    rw [← RingHom.injective_iff_ker_eq_bot]
    exact hφ
  have pb : IsPullback (pullback.fst T'.hom B.hom) (φ ▷ B).left φ.left (pullback.fst T.hom B.hom) := by
    refine (IsPullback.of_right (h₁₁ := (φ ▷ B).left) (v₁₁ := pullback.fst T'.hom B.hom)
      (h₂₁ := φ.left) (v₁₂ := pullback.fst T.hom B.hom) ?_ (Over.whiskerRight_left_fst φ)
      (IsPullback.of_hasPullback T.hom B.hom).flip).flip
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom B.hom).flip
  have : IsSchemeTheoreticallyDominant (φ ▷ B).left := .of_isPullback pb
  have : QuasiCompact (φ ▷ B).left := MorphismProperty.of_isPullback pb inferInstance
  exact (φ ▷ B).left.app_injective U

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ClassSubStructure
section
noncomputable section

namespace GlobalTheory.ClassWeight

abbrev TorChar (X : Type) [AddCommGroup X] (F : Type) [Field F] (N : ℕ) : Subgroup (Multiplicative X →* Fˣ) :=
  (powMonoidHom N : (Multiplicative X →* Fˣ) →* (Multiplicative X →* Fˣ)).ker

variable {X : Type} [AddCommGroup X] {F : Type} [Field F] {N : ℕ}

def evalChar (F : Type) [Field F] (N : ℕ) (α : X) : TorChar X F N →* Fˣ :=
  MonoidHom.mk' (fun τ => τ.1 (Multiplicative.ofAdd α)) fun _ _ => rfl

theorem evalChar_add (α β : X) (τ : TorChar X F N) :
    evalChar F N (α + β) τ = evalChar F N α τ * evalChar F N β τ := map_mul τ.1 _ _

theorem evalChar_add_nsmul (α mu : X) (τ : TorChar X F N) : evalChar F N (α + N • mu) τ = evalChar F N α τ := by
  have h : evalChar F N (N • mu) τ = 1 :=
    (map_pow τ.1 (Multiplicative.ofAdd mu) N).trans (DFunLike.congr_fun (show τ.1 ^ N = 1 from τ.2) _)
  rw [evalChar_add, h, mul_one]

theorem exists_evalChar_ne [Module.Finite ℤ X] [IsAlgClosed F] (hN : (N : F) ≠ 0) {α β : X}
    (h : ¬ ∃ mu, β = α + N • mu) : ∃ τ : TorChar X F N, evalChar F N β τ ≠ evalChar F N α τ := by
  have : NeZero (N : F) := ⟨hN⟩
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  have : NeZero N := ⟨hN0⟩
  let K : AddSubgroup X := (nsmulAddMonoidHom N : X →+ X).range
  have hK : ∀ q : X ⧸ K, N • q = 0 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨x, rfl⟩
  have : Module.Finite ℤ (X ⧸ K) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' K).toIntLinearMap (QuotientAddGroup.mk'_surjective K)
  have : Finite (X ⧸ K) := Module.finite_of_fg_torsion _ fun q =>
    ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN0)⟩, (natCast_zsmul q N).trans (hK q)⟩
  have h0 : HasEnoughRootsOfUnity F N := inferInstance
  have : HasEnoughRootsOfUnity F (Monoid.exponent (Multiplicative (X ⧸ K))) :=
    h0.of_dvd F (Monoid.exponent_dvd_of_forall_pow_eq_one fun q => hK q.toAdd)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative (X ⧸ K)) F
    (a := Multiplicative.ofAdd ((β - α : X) : X ⧸ K)) fun e => by
      obtain ⟨mu, hmu⟩ := (QuotientAddGroup.eq_zero_iff _).1 (show ((β - α : X) : X ⧸ K) = 0 from e)
      exact h ⟨mu, (sub_eq_iff_eq_add'.1 hmu.symm)⟩
  let τ : TorChar X F N := ⟨φ.comp (QuotientAddGroup.mk' K).toMultiplicative, MonoidHom.ext fun x =>
    (map_pow φ _ N).symm.trans ((congrArg φ (show (Multiplicative.ofAdd (x.toAdd : X ⧸ K)) ^ N = 1 from hK (x.toAdd : X ⧸ K))).trans (map_one φ))⟩
  refine ⟨τ, fun e => hφ ?_⟩
  have e₂ := evalChar_add (β - α) α τ
  rw [sub_add_cancel, e] at e₂
  exact right_eq_mul.1 e₂

variable {E : Type} [AddCommGroup E] [Module F E] {W : X → Type} [∀ α, AddCommGroup (W α)] [∀ α, Module F (W α)]

def classSub (S : ∀ α, E →ₗ[F] W α) (N : ℕ) (α : X) : Submodule F E where
  carrier := {v | ∀ β, (¬ ∃ mu, β = α + N • mu) → S β v = 0}
  add_mem' := fun {v v'} h h' β hβ => by rw [map_add (f := _), h β hβ, h' β hβ, add_zero]
  zero_mem' := fun β _ => map_zero _
  smul_mem' := fun c v h β hβ => by rw [map_smul, h β hβ, smul_zero]

theorem exists_proj [Module.Finite ℤ X] [IsAlgClosed F] (hN : (N : F) ≠ 0) (S : ∀ α, E →ₗ[F] W α)
    (hc : (Nat.card (TorChar X F N) : F) ≠ 0) (l : TorChar X F N → E → E)
    (hl : ∀ τ v β, S β (l τ v) = (evalChar F N β τ : F) • S β v) (α : X) (v : E) :
    ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v := by
  have : Finite (TorChar X F N) := Nat.finite_of_card_ne_zero fun e => hc (by rw [e, Nat.cast_zero])
  have := Fintype.ofFinite (TorChar X F N)
  have key : ∀ β, S β ((Nat.card (TorChar X F N) : F)⁻¹ • ∑ τ, (((evalChar F N α τ)⁻¹ : Fˣ) : F) • l τ v) =
      ((Nat.card (TorChar X F N) : F)⁻¹ * ∑ τ, ((Units.coeHom F).comp (evalChar F N β / evalChar F N α)) τ) • S β v :=
    fun β => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum, mul_smul, Finset.sum_smul]
      refine congrArg _ (Finset.sum_congr rfl fun τ _ => ?_)
      rw [map_smul, hl, smul_smul, ← Units.val_mul, mul_comm, ← div_eq_mul_inv]
      rfl
  refine ⟨_, fun β hβ => (key β).trans ?_, fun mu => (key _).trans ?_⟩
  · obtain ⟨τ, hτ⟩ := exists_evalChar_ne hN hβ
    rw [sum_hom_units_eq_zero _ fun e => hτ (div_eq_one.1 (Units.ext (DFunLike.congr_fun e τ))), mul_zero, zero_smul]
  · have e : ∀ τ, ((Units.coeHom F).comp (evalChar F N (α + N • mu) / evalChar F N α)) τ = 1 := fun τ =>
      congrArg Units.val (div_eq_one.2 (evalChar_add_nsmul α mu τ))
    rw [Finset.sum_congr rfl fun τ _ => e τ, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_one, inv_mul_cancel₀ hc, one_smul]

theorem classSub_structure [Module.Finite ℤ X] [IsAlgClosed F] [FiniteDimensional F E] (hN : (N : F) ≠ 0)
    {A : Type} [CommGroup A] [Finite A] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)) (hA : (Nat.card A : F) ≠ 0)
    (hd : Module.finrank F E ^ 2 = Nat.card A) (hm : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hn : ∀ a, (∀ b, e a b = 1) → a = 1)
    (S : ∀ α, E →ₗ[F] W α) (hS : ∀ v, (∀ α, S α v = 0) → v = 0)
    (a : TorChar X F N →* A) (ha : Function.Injective a)
    (hT : ∀ τ, ∃ c : Fˣ, ∀ v α, S α (Φ (a τ) v) = ((c * evalChar F N α τ : Fˣ) : F) • S α v)
    (H : Subgroup A) (hH : ∀ h ∈ H, ∀ α v v' (c : F), S α v = c • S α v' → S α (Φ h v) = c • S α (Φ h v'))
    (hcard : Nat.card (TorChar X F N) * Nat.card H = Nat.card A) (α : X) :
    (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
    Module.finrank F (classSub S N α) * Nat.card (TorChar X F N) = Module.finrank F E ∧
    ∀ U : Submodule F E, U ≤ classSub S N α → (∀ h ∈ H, ∀ v ∈ U, Φ h v ∈ U) → U = ⊥ ∨ U = classSub S N α := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  have : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := F)
    rcases Nat.eq_zero_or_pos (Module.finrank F E) with h | h
    · rw [h] at hd
      omega
    · exact h
  have ext : ∀ v v', (∀ α, S α v = S α v') → v = v' := fun v v' h =>
    sub_eq_zero.1 (hS _ fun α => by rw [map_sub, h, sub_self])
  choose c hcT using hT
  let l₀ : TorChar X F N → (E ≃ₗ[F] E) := fun τ => (Φ (a τ)).trans (LinearEquiv.smulOfUnit (c τ)⁻¹)
  have l₀e : ∀ τ v, l₀ τ v = (((c τ)⁻¹ : Fˣ) : F) • Φ (a τ) v := fun _ _ => rfl
  have hl : ∀ τ v β, S β (l₀ τ v) = (evalChar F N β τ : F) • S β v := fun τ v β => by
    rw [l₀e, map_smul, hcT, smul_smul, ← Units.val_mul, inv_mul_cancel_left]
  let l : TorChar X F N →* (E ≃ₗ[F] E) := MonoidHom.mk' l₀ fun τ τ' => LinearEquiv.ext fun v => ext _ _ fun β => by
    rw [LinearEquiv.mul_apply, hl, hl, hl, smul_smul, map_mul, Units.val_mul]
  let i : TorChar X F N ≃* a.range := MonoidHom.ofInjective ha
  let lam : a.range →* (E ≃ₗ[F] E) := l.comp i.symm.toMonoidHom
  have hlam : ∀ t : a.range, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v := fun t => by
    obtain ⟨τ, rfl⟩ := i.surjective t
    refine ⟨(c τ)⁻¹, fun v => ?_⟩
    show l₀ (i.symm (i τ)) v = _
    rw [i.symm_apply_apply]; rfl
  let Wt : (a.range →* Fˣ) → Submodule F E := fun χ =>
    { carrier := {v | ∀ t, lam t v = (χ t : F) • v}
      add_mem' := fun {v v'} h h' t => by rw [map_add (f := _), h t, h' t, smul_add]
      zero_mem' := fun t => by rw [map_zero, smul_zero]
      smul_mem' := fun r v h t => by rw [map_smul, h t, smul_comm] }
  have hWt : ∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v := fun _ _ => Iff.rfl
  let χ : a.range →* Fˣ := (evalChar F N α).comp i.symm.toMonoidHom
  have hW : Wt χ = classSub S N α := Submodule.ext fun v => ⟨fun h β hβ => by
      obtain ⟨τ, hτ⟩ := exists_evalChar_ne (F := F) hN hβ
      have h₁ : l₀ (i.symm (i τ)) v = (evalChar F N α (i.symm (i τ)) : F) • v := h (i τ)
      have h₂ := congrArg (S β) h₁
      rw [i.symm_apply_apply, hl, map_smul] at h₂
      by_contra h₃
      exact hτ (Units.ext (smul_left_injective F h₃ h₂)), fun h t => ext _ _ fun β => by
      refine (hl (i.symm t) v β).trans ?_
      rw [map_smul]
      by_cases hβ : ∃ mu, β = α + N • mu
      · obtain ⟨mu, rfl⟩ := hβ
        rw [evalChar_add_nsmul]; rfl
      · rw [h β hβ, smul_zero, smul_zero]⟩
  have hci : Nat.card a.range = Nat.card (TorChar X F N) := (Nat.card_congr i.toEquiv).symm
  have hTH : ∀ t ∈ a.range, ∀ h ∈ H, e t h = 1 := by
    rintro _ ⟨τ, rfl⟩ h hh
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have h₁ : Φ (a τ) (Φ h v) = Φ h (Φ (a τ) v) := ext _ _ fun β =>
      (hcT τ _ β).trans (hH h hh β _ _ _ (hcT τ v β)).symm
    have h₂ : Φ h (Φ (a τ) v) ≠ 0 := by simpa using hv
    apply HeisenbergWeightDim.units_eq_of_smul_eq h₂
    rw [← hc, h₁, Units.val_one, one_smul]
  have hperp := (perfectPairing_orthogonal_of_card F A e (HeisenbergWeightDim.comm_mul_left hm hc)
    (HeisenbergWeightDim.comm_mul_right hm hc) hn a.range H hTH (by rw [hci, hcard])).2.1
  refine ⟨exists_proj hN S (fun h => hA (by rw [← hcard, Nat.cast_mul, h, zero_mul])) (fun τ v => l₀ τ v) hl α, ?_,
    fun U hU hst => ?_⟩
  · rw [← hW, ← hci]
    exact (heisenberg_weightSpace_finrank F A E e Φ hA hd hm hc hn a.range lam hlam Wt hWt).2 χ
  · rw [← hW] at hU ⊢
    exact heisenberg_weightSpace_irreducible F A E e Φ hA hd hm hc hn a.range lam hlam Wt hWt χ U hU
      fun h hh => hst h ((hperp h).1 fun t ht => hh ⟨t, ht⟩)

end GlobalTheory.ClassWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubCoordMulMulInv
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cub_coord_mul_mul_inv : ∀ (A U X : Type) [CommGroup A] [CommGroup U] [AddCommGroup X] (θ : A → A → A → U), IsCub θ → ∀ (H : Type) [CommGroup H] (q : H →* A) (c : X → A), (∀ a b, c (a + b) = c a * c b) → ∀ t : X → H → U, (∀ a b x, t (a + b) x * θ (c a) (c b) (q x) = t a x * t b x) → (∀ a x y, t a (x * y) * θ (c a) (q x) (q y) = t a x * t a y) → ∀ a b x y, t a (x * y) * t b (x * y⁻¹) * (θ (c a) (q x) (q y) * θ (c b) (q x) (q y)⁻¹ * θ (c (a - b)) (c b) (q y)) = t (a + b) x * t (a - b) y * (θ (c a) (c b) (q x) * θ (c b) (q y) (q y)⁻¹) := by
  intro A U X _ _ _ θ h H _ q c _ t h₁ h₂ a b x y
  have e₀ : t b 1 = 1 := by
    have e := h₂ b 1 1
    rw [_root_.mul_one, map_one, h.face₃, _root_.mul_one] at e
    exact (mul_eq_left.mp e.symm)
  have e₁ := h₂ a x y
  have e₂ := h₂ b x y⁻¹
  have e₃ := h₂ b y y⁻¹
  have e₄ := h₁ a b x
  have e₅ := h₁ (a - b) b y
  rw [map_inv] at e₂ e₃
  rw [_root_.mul_inv_cancel, e₀, _root_.one_mul] at e₃
  rw [sub_add_cancel] at e₅
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅
  simp only [ofMul_mul] at a₁ a₂ a₃ a₄ a₅ ⊢
  linear_combination (norm := abel) a₁ + a₂ - a₃ - a₄ + a₅

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNDescentTelescope
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cubN_descent_telescope {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (θ : A → A → A → U)
    (θ' : A' → A' → A' → U) (q : A →* A') (W : A → U) (hc : IsCub θ')
    (h : ∀ x y u, θ' (q x) (q y) (q u) * W (x * y) * W (x * u) * W (y * u) * W 1 =
      W (x * y * u) * W x * W y * W u * θ x y u) (k : ℕ) (x y : A) (hx : q x = 1) :
    cubN θ k 1 x y * W (x ^ k * y) * W x ^ k * W y ^ k * W 1 = W (x ^ k) * W y * W (x * y) ^ k * W 1 ^ k := by
  induction k with
  | zero => simp [cubN, mul_comm]
  | succ k ih =>
    have e := h (x ^ k) x y
    rw [hx, hc.face₂, _root_.one_mul, ← pow_succ] at e
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ (W x), pow_succ (W y), pow_succ (W (x * y)), pow_succ (W 1)]
    generalize (∏ i ∈ Finset.range k, θ (x ^ i) x y) = P at ih ⊢
    apply Additive.ofMul.injective
    have a1 := congrArg Additive.ofMul ih
    have a2 := congrArg Additive.ofMul e
    simp only [ofMul_mul] at a1 a2 ⊢
    linear_combination (norm := abel) a1 - a2

theorem cubN_descent_opposite : ∀ (A A' U : Type) [CommGroup A] [CommGroup A'] [CommGroup U] (θ : A → A → A → U) (θ' : A' → A' → A' → U) (q : A →* A') (W : A → U), IsCub θ' → (∀ x y u, θ' (q x) (q y) (q u) * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * θ x y u) → ∀ (k : ℕ) (x y : A), q x = 1 → cubN θ k 1 x y * θ y (x ^ k) (x ^ k)⁻¹ * W y ^ (k + 1) * W x ^ k * W (x ^ k)⁻¹ = W (x * y) ^ k * W (y * (x ^ k)⁻¹) * W 1 ^ (k + 1) := by
  intro A A' U _ _ _ θ θ' q W hc h k x y hx
  have t := cubN_descent_telescope θ θ' q W hc h k x y hx
  have e := h y (x ^ k) (x ^ k)⁻¹
  rw [map_pow, hx, one_pow, hc.face₂, _root_.one_mul, mul_inv_cancel, mul_inv_cancel_right, mul_comm y (x ^ k)] at e
  rw [pow_succ (W y), pow_succ (W 1)]
  apply Additive.ofMul.injective
  have a1 := congrArg Additive.ofMul t
  have a2 := congrArg Additive.ofMul e
  simp only [ofMul_mul] at a1 a2 ⊢
  linear_combination (norm := abel) a1 - a2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenQuadraticPosOfFiniteNonpos
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cubeRel_even_nsmul {X : Type} [AddCommGroup X] (φ : X → ℤ)
    (h : ∀ a b c, φ (a + b + c) + φ a + φ b + φ c = φ (a + b) + φ (a + c) + φ (b + c))
    (he : ∀ a, φ (-a) = φ a) (a : X) (n : ℕ) : φ (n • a) = (n : ℤ) ^ 2 * φ a := by
  have h0 : φ 0 = 0 := by
    have := h 0 0 0
    simp only [add_zero] at this
    linarith
  have key : ∀ n : ℕ, φ (n • a) = (n : ℤ) ^ 2 * φ a ∧
      φ ((n + 1) • a) = ((n + 1 : ℕ) : ℤ) ^ 2 * φ a := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h1 := h ((n + 1) • a) a (-a)
      have e1 : (n + 1) • a + a + -a = (n + 1) • a := by abel
      have e2 : (n + 1) • a + a = (n + 1 + 1) • a := (succ_nsmul a (n + 1)).symm
      have e3 : (n + 1) • a + -a = n • a := by rw [succ_nsmul]; abel
      rw [e1, e2, e3, add_neg_cancel, he, h0, ih.1, ih.2] at h1
      push_cast at h1 ⊢
      linear_combination -h1
  exact (key n).1

theorem even_quadratic_pos_of_finite_nonpos : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (φ : X → ℤ), (∀ a b c, φ (a + b + c) + φ a + φ b + φ c = φ (a + b) + φ (a + c) + φ (b + c)) → (∀ a, φ (-a) = φ a) → {a | φ a ≤ 0}.Finite → ∀ a, a ≠ 0 → 0 < φ a := by
  intro X _ _ φ h he hfin a ha
  by_contra hle
  rw [not_lt] at hle
  have hinj : Function.Injective (fun n : ℕ => n • a) := by
    intro m n hmn
    have h1 : ((m : ℤ) - (n : ℤ)) • a = 0 := by
      rw [sub_smul, natCast_zsmul, natCast_zsmul]
      exact sub_eq_zero.mpr hmn
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact_mod_cast sub_eq_zero.mp h2
    · exact absurd h2 ha
  refine Set.infinite_of_injective_forall_mem hinj ?_ hfin
  intro n
  show φ (n • a) ≤ 0
  rw [cubeRel_even_nsmul φ h he a n]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBasisOfFormEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowBasis

theorem gs_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {m : ℕ} (a : Fin m → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by simp only [gs_eq f y U h, map_sum]

theorem comb_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {m : ℕ} (s : LB.Sec (LB.LinComb L φ ε)) (b : Fin m → LB.Sec (LB.LinComb L φ ε)) (r : Fin m → Γ(Y, ⊤)) :
    (∀ j, s.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (r i) * (b i).f j) ↔
      ∀ y J, Good L y J → sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (r i) * sval (b i) (𝟙 Y) y J := by
  have key : ∀ (j : K → L.ι) (y : Y) (hy : y ∈ LB.wchart L φ j),
      gs (𝟙 Y) y (LB.wchart L φ j)
        (∑ i, (Y.presheaf.map (homOfLE (le_top : (LB.LinComb L φ ε).U j ≤ ⊤)).op).hom (r i) * (b i).f j :
          Γ(Y, (LB.LinComb L φ ε).U j)) =
      ∑ i, gs (𝟙 Y) y ⊤ (r i) * gs (𝟙 Y) y (LB.wchart L φ j) ((b i).f j) := fun j y hy =>
    (gs_sum (𝟙 Y) y _ hy _).trans (Finset.sum_congr rfl fun i _ =>
      (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg (· * _) (gs_res (𝟙 Y) y le_top hy _)))
  constructor
  · intro h y J hJ
    exact (congrArg (gs (𝟙 Y) y _) (h _)).trans (key _ y (hJ.mem φ (𝟙 Y)))
  · intro h j
    refine fn_ext fun y hy => ?_
    choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
    refine ((sec_trans s (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).trans ((congrArg _ (h y I hI)).trans ?_)).trans
      (key j y hy).symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sec_trans (b i) (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y)), mul_left_comm]
    rfl

theorem exists_basis_of_formEq {S : Scheme.{0}} {A T : Over S} {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((T ⊗ A).left ⟶ X)} {ε : K → ℤ}
    {φ' : K' → ((T ⊗ A).left ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε') {m : ℕ}
    {b : Fin m → LB.Sec (LB.LinComb L φ ε)} (hb : IsSecBasis _ b) :
    ∃ b' : Fin m → LB.Sec (LB.LinComb L φ' ε'), IsSecBasis _ b' := by
  choose b' hb' using fun i => exists_sec hL h (b i)
  refine ⟨b', fun t => ?_⟩
  obtain ⟨s, hs⟩ := exists_sec hL (φ := φ') (ε := ε') (φ' := φ) (ε' := ε) (fun U _ g => (h U g).symm) t
  refine (existsUnique_congr fun r => ?_).1 (hb s)
  refine (comb_iff hL s b fun i => (fst T A).left.appTop.hom (r i)).trans
    (Iff.trans ?_ (comb_iff hL t b' fun i => (fst T A).left.appTop.hom (r i)).symm)
  refine forall_congr' fun y => forall_congr' fun J => forall_congr' fun hJ => ?_
  rw [hs _ _ y J hJ]
  simp only [hb' _ _ _ y J hJ]

theorem translPt_one {S : Scheme.{0}} (A : Over S) [GrpObj A] (T : Over S) :
    translPt A (1 : T ⟶ A) = snd T A := by
  have e : translPt A (1 : T ⟶ A) = (fst T A ≫ (1 : T ⟶ A)) * snd T A := rfl
  rw [e, MonObj.comp_one, _root_.one_mul]

theorem exists_basis_pow (hT : SecTwistSt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (hk : 1 ≤ k) (R : Type) [CommRing R]
    [IsLocalRing R] (t : Spec (CommRingCat.of R) ⟶ S) :
    ∃ b : Fin (k ^ P.g) → LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk t)), IsSecBasis _ b := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT S P k hk R t 1
  refine exists_basis_of_formEq P.isLB (fun U _ g => ?_) hb
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, translPt_one, Fintype.prod_unique]
  rw [← zpow_add, sub_add_cancel]

theorem exists_basis_pow_field : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∃ b : Fin (k ^ A.g) → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∀ t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∃! c : Fin (k ^ A.g) → F, ∀ j, t.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (b i).f j := by
  intro hT R _ _ A F _ _ k hk
  obtain ⟨b, hb⟩ := exists_basis_pow hT A k hk F (jFK (R := R) F)
  refine ⟨b, fun t => ?_⟩
  obtain ⟨r, hr, hu⟩ := hb t
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (r i), fun j => ?_, fun c hc => ?_⟩
  · refine (hr j).trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (fun x => liftFun A.A _ x * (b i).f j)
      ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply (r i)).symm
  · have e := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) hc
    funext i
    rw [← congrFun e i]
    exact ((Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply (c i)).symm

end GlobalTheory.PowBasis
end
end

