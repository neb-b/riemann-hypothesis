module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EndoConstantFamilyDualNumbersEqBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.ConstEndo

theorem unit_comp {S S₀ : Scheme.{0}} {f : S ⟶ S₀} {X : Over S} {X₀ : Over S₀} [GrpObj X] [GrpObj X₀]
    {φ : X.left ⟶ X₀.left} (h : IsGrpPullback X X₀ f φ) :
    (η[X]).left ≫ φ = f ≫ (η[X₀]).left := by
  obtain ⟨hpb, hmul⟩ := h

  have hw : ((η[X]).left ≫ φ) ≫ X₀.hom = (𝟙_ (Over S)).hom ≫ f := by
    rw [Category.assoc, hpb.w, ← Category.assoc, Over.w]
  let x₀ : Over.mk ((𝟙_ (Over S)).hom ≫ f) ⟶ X₀ := Over.homMk ((η[X]).left ≫ φ) hw

  have hηη : (η[X] : 𝟙_ (Over S) ⟶ X) * η[X] = η[X] := by
    rw [MonObj.one_eq_one, _root_.one_mul]
  have hx : x₀ * x₀ = x₀ := by
    ext1
    rw [hmul (𝟙_ (Over S)) η[X] η[X] x₀ x₀ rfl rfl, hηη]
    rfl
  have h1 : x₀ = 1 := by
    simpa using hx
  have h2 := congrArg CommaMorphism.left h1
  simp only [x₀, Over.homMk_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom,
    Over.tensorUnit_hom] at h2
  exact h2

private theorem surjective_of_isPullback_dualNumber_fst {A₀ : Over (Sp ℂ)} {A' : Over (Sp (DualNumber ℂ))} (j : A₀.left ⟶ A'.left)
    (h : IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) :
    Function.Surjective j := by

  have hc : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    intro p
    have hp : p ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
      rw [range_comap_of_surjective _ _ (fun x => ⟨TrivSqZeroExt.inl x, rfl⟩)]
      intro x hx
      have hx0 : x.fst = 0 := hx
      apply p.isPrime.mem_of_pow_mem 2
      have hx' : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext hx0 rfl
      rw [hx', pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem
    exact hp
  have hs : Surjective (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := ⟨hc⟩
  exact (MorphismProperty.of_isPullback h.flip hs).surj

private theorem exists_unit_mul_eq_mul_uniformizer_pow {X S Y : Scheme.{0}} [IsAffine Y] (π : X ⟶ S)
    (hπ : Function.Bijective (π.appTop).hom) (g : X ⟶ Y) : ∃ c : S ⟶ Y, g = π ≫ c := by

  have : IsIso π.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hπ
  refine ⟨S.toSpecΓ ≫ Spec.map (inv π.appTop) ≫ Spec.map g.appTop ≫ inv Y.toSpecΓ, ?_⟩
  rw [← cancel_mono Y.toSpecΓ]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc,
    IsIso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem endo_comp_proj : Out.Laws → Out.Laws2 → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (f' : A' ⟶ A') (f₀ : P₀.A ⟶ P₀.A), IsAbelianScheme A' → IsMonHom f' → IsMonHom f₀ → j ≫ f'.left = f₀.left ≫ j → f'.left ≫ ρ = ρ ≫ f₀.left := by
  intro hL _ P₀ A' _ ρ j hc f' f₀ hab hf' hf₀ hj
  obtain ⟨hρ, hjp, hjρ⟩ := hc
  set ic : Sp (DualNumber ℂ) ⟶ Sp ℂ := spMap (algebraMap ℂ (DualNumber ℂ)) with hic
  have hwρ : ρ ≫ P₀.A.hom = A'.hom ≫ ic := hρ.1.w

  let T : Over (Sp ℂ) := Over.mk (A'.hom ≫ ic)
  let D : T ⟶ P₀.A := Over.homMk (f'.left ≫ ρ) (by
    simp only [T, Over.mk_hom, Category.assoc, hwρ]
    rw [← Category.assoc, Over.w])
  let E : T ⟶ P₀.A := Over.homMk (ρ ≫ f₀.left) (by
    simp only [T, Over.mk_hom, Category.assoc, Over.w, hwρ])
  suffices hDE : D = E from congrArg CommaMorphism.left hDE
  rw [← _root_.mul_inv_eq_one]
  set δ := D * E⁻¹ with hδ

  have hjT : j ≫ T.hom = P₀.A.hom := by
    simp only [T, Over.mk_hom]
    rw [← hwρ, ← Category.assoc, hjρ, Category.id_comp]
  let jT : P₀.A ⟶ T := Over.homMk j hjT
  have h1 : jT ≫ δ = 1 := by
    have hh : jT ≫ D = jT ≫ E := by
      ext1
      simp only [jT, D, E, Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, hj, Category.assoc, hjρ, Category.comp_id, ← Category.assoc, hjρ,
        Category.id_comp]
    rw [hδ, MonObj.comp_mul, GrpObj.comp_inv, hh, _root_.mul_inv_cancel]

  have hη : (η[A']).left ≫ ρ = ic ≫ (η[P₀.A]).left := unit_comp hρ
  have hηA : (η[A']).left ≫ A'.hom = 𝟙 _ := by
    rw [Over.w]; rfl
  let eT : Over.mk ic ⟶ T := Over.homMk (η[A']).left (by
    simp only [T, Over.mk_hom]
    rw [← Category.assoc, hηA]
    exact Category.id_comp _)
  have h2 : (eT ≫ δ).left = ic ≫ (η[P₀.A]).left := by
    have hh : eT ≫ D = eT ≫ E := by
      ext1
      simp only [eT, D, E, Over.comp_left, Over.homMk_left]
      have e1 : (η[A']).left ≫ f'.left = (η[A']).left := by
        rw [← Over.comp_left, IsMonHom.one_hom]
      have e2 : (η[P₀.A]).left ≫ f₀.left = (η[P₀.A]).left := by
        rw [← Over.comp_left, IsMonHom.one_hom]
      rw [← Category.assoc, e1, hη, ← Category.assoc, hη, Category.assoc, e2]
    rw [hδ, MonObj.comp_mul, GrpObj.comp_inv, hh, _root_.mul_inv_cancel]
    simp [Hom.one_def]

  have hsurj := surjective_of_isPullback_dualNumber_fst j hjp.1
  obtain ⟨p₀⟩ : Nonempty (Sp ℂ) := inferInstance
  obtain ⟨_, ⟨V₀, hV, rfl⟩, hxV, -⟩ :=
    P₀.A.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show (η[P₀.A]).left p₀ ∈ (⊤ : P₀.A.left.Opens) from trivial) (⊤ : P₀.A.left.Opens).2
  let V : P₀.A.left.Opens := V₀
  have hrange : Set.range δ.left ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hsurj x
    have e1 : (jT ≫ δ).left = (1 : P₀.A ⟶ P₀.A).left := by rw [h1]
    have e2 : δ.left (j y) = (η[P₀.A]).left (P₀.A.hom y) := by
      have := congrArg (fun m => m y) e1
      simpa [jT, Hom.one_def] using this
    rw [e2, Subsingleton.elim (P₀.A.hom y) p₀]
    exact hxV
  have : IsAffine V := hV
  have hG : Function.Bijective (A'.hom.appTop).hom := by
    have hgl := hL.globalFns
    unfold Out.GlobalFnsSt at hgl
    exact hgl _ A' hab
  obtain ⟨c, hc⟩ := exists_unit_mul_eq_mul_uniformizer_pow A'.hom hG (IsOpenImmersion.lift V.ι δ.left hrange)
  have hδc : δ.left = A'.hom ≫ c ≫ V.ι := by
    rw [← Category.assoc, ← hc, IsOpenImmersion.lift_fac]

  have h3 : c ≫ V.ι = ic ≫ (η[P₀.A]).left := by
    rw [← h2]
    simp only [eT, Over.comp_left, Over.homMk_left, hδc]
    rw [← Category.assoc, hηA]
    exact (Category.id_comp (c ≫ V.ι)).symm
  ext1
  rw [hδc, h3]
  simp [T, Hom.one_def]

end GlobalTheory.ConstEndo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

abbrev Mc (l : Level H) : Ideal (𝓞 E) := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)

theorem exists_idem (l : Level H) : ∃ e ∈ Mc l, 1 - e ∈ l.Mb := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  exact ⟨y, hy, by rw [← hxy, add_sub_cancel_right]; exact hx⟩

theorem M_pos (l : Level H) : 0 < l.M := by
  have := l.three_le
  omega

theorem modN_of_mem_span {n : ℕ} {a : D.La}
    (h : a ∈ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN n a := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨b, -, hb⟩ := h
  exact ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩

theorem modN_smul_Mb (l : Level H) {c : 𝓞 E} (hc : c ∈ Mc l) {a : D.La}
    (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M (c • a) := by
  apply modN_of_mem_span
  have h1 : c • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • l.Mb • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hc ha
  rwa [← Submodule.mul_smul, mul_comm, l.prod] at h1

theorem modN_smul_Mc (l : Level H) {c : 𝓞 E} (hc : c ∈ l.Mb) {a : D.La}
    (ha : a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M (c • a) := by
  apply modN_of_mem_span
  have h1 : c • a ∈ l.Mb • l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hc ha
  rwa [← Submodule.mul_smul, l.prod] at h1

theorem modN_of_mem_both (l : Level H) {a : D.La} (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La))
    (ha' : a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M a := by
  obtain ⟨e, he, he'⟩ := exists_idem l
  obtain ⟨b₁, hb₁⟩ := modN_smul_Mb l he ha
  obtain ⟨b₂, hb₂⟩ := modN_smul_Mc l he' ha'
  refine ⟨b₁ + b₂, ?_⟩
  rw [smul_add, ← hb₁, ← hb₂, ← add_smul]
  simp

theorem nsmul_M_mem (l : Level H) (a : D.La) : l.M • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  have hM : (l.M : 𝓞 E) ∈ l.Mb := by
    have h1 : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf.trans inf_le_left) h1
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hM Submodule.mem_top

theorem add_map_zero {M Q : Type} [AddCommGroup M] [Group Q] {f : M → Q} (hf : ∀ a c, f (a + c) = f a * f c) :
    f 0 = 1 := by
  have h := hf 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := f 0) (by rw [_root_.mul_one]; exact h.symm)

theorem add_map_nsmul {M Q : Type} [AddCommGroup M] [Group Q] {f : M → Q} (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : M) : f (n • a) = f a ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; exact add_map_zero hf
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_pow_div (I : TateIso D k Q act e) {n N : ℕ} (hN : 0 < N) (h : n ∣ N) (a : D.La) :
    I.ev N a ^ (N / n) = I.ev n a := by
  have hn : 0 < n := Nat.pos_of_dvd_of_pos h hN
  have hq : 0 < N / n := Nat.div_pos (Nat.le_of_dvd hN h) hn
  have := I.tower n (N / n) hn hq a
  rwa [Nat.mul_div_cancel' h] at this

theorem zeta_pow_div (I : TateIso D k Q act e) {n N : ℕ} (hN : 0 < N) (h : n ∣ N) :
    I.ζ N ^ (N / n) = I.ζ n := by
  have hn : 0 < n := Nat.pos_of_dvd_of_pos h hN
  have hq : 0 < N / n := Nat.div_pos (Nat.le_of_dvd hN h) hn
  have := I.ζ_pow n (N / n) hn hq
  rwa [Nat.mul_div_cancel' h] at this

theorem exists_coprime_zpow {N : ℕ} (hN : 0 < N) {ζ ξ : kˣ} (hζ : IsPrimitiveRoot ζ N) (hξ : IsPrimitiveRoot ξ N) :
    ∃ ν : ℤ, IsCoprime ν (N : ℤ) ∧ ξ = ζ ^ ν := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one (ξ := (ξ : k))
    (by rw [← Units.val_pow_eq_pow_val, hξ.pow_eq_one, Units.val_one])
  have hξi : ξ = ζ ^ i := Units.ext (by rw [Units.val_pow_eq_pow_val, hi])
  have hcop : i.Coprime N := (hζ.pow_iff_coprime hN i).1 (by rw [← hξi]; exact hξ)
  exact ⟨i, Nat.isCoprime_iff_coprime.2 hcop, by rw [hξi, zpow_natCast]⟩

theorem exists_adjust
    (hν : ∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (l : Level H) (N : ℕ)
    (hM : ∀ ν : ℤ, 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 → ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν ∧
      (l.A : ℤ) ∣ g.ν l.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
      ∀ a, D.ModN l.A (g.f l.A a - a))
    (I : TateIso D k Q act e) (hN : 0 < N) (hA : l.A ∣ N) {ξ : kˣ} (hξ : IsPrimitiveRoot ξ N)
    (h : ξ ^ (N / l.A) = I.ζ l.A) :
    ∃ I' : TateIso D k Q act e, I'.ζ N = ξ ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La), I'.ev l.M a = I.ev l.M a := by
  obtain ⟨ν, hνc, hξν⟩ := exists_coprime_zpow hN (I.ζ_prim N hN) hξ
  have hA0 := l.A_pos
  have h1 : I.ζ l.A ^ ν = I.ζ l.A := by
    calc I.ζ l.A ^ ν = ((I.ζ N) ^ (N / l.A)) ^ ν := by rw [zeta_pow_div I hN hA]
      _ = ((I.ζ N) ^ ν) ^ (N / l.A) := by simp only [← zpow_natCast, ← zpow_mul, mul_comm]
      _ = I.ζ l.A := by rw [← hξν, h]
  have hA1 : (l.A : ℤ) ∣ ν - 1 := by
    refine ((I.ζ_prim l.A hA0).zpow_eq_one_iff_dvd _).1 ?_
    rw [zpow_sub, zpow_one, h1, mul_inv_cancel]
  obtain ⟨g, hgN, -, hgM, hgA⟩ := hM ν hN hνc hA1
  refine ⟨LevelTwist.twist I g (hν g), ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [LevelTwist.twist_ζ, hξν]
    exact LevelTwist.zeta_zpow_congr I hN hgN
  · rw [LevelTwist.twist_ev]
    exact LevelTwist.ev_congr I hA0 (hgA a)
  · rw [LevelTwist.twist_ev]
    refine LevelTwist.ev_congr I (M_pos l) (modN_of_mem_both l (hgM a) ?_)
    exact Submodule.sub_mem _ (LevelTwist.map_mem_smul_top _ _ ha) ha

theorem exists_of_level
    (hν : ∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (N : ℕ)
    (hL : ∀ (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) →
      (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) →
      ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν)
    (he : ∀ x y c c', e N x y c → e N x y c' → c = c')
    (I : TateIso D k Q act e) (hN : 0 < N) {ξ : kˣ} (hξ : IsPrimitiveRoot ξ N) (α : D.La → Q)
    (hadd : ∀ a c, α (a + c) = α a * α c) (hpow : ∀ a, α a ^ N = 1) (hlin : ∀ c a, α (c • a) = act c (α a))
    (hiso : ∀ a b, e N (α a) (α b) (ξ ^ D.EF a b)) :
    ∃ I' : TateIso D k Q act e, I'.ζ N = ξ ∧ ∀ a, I'.ev N a = α a := by
  classical
  choose b hb using fun a => (I.onto N hN (α a)).1 (hpow a)
  let K : Submodule (𝓞 E) D.La := LinearMap.range ((N : 𝓞 E) • LinearMap.id)
  have memK : ∀ x y, I.ev N x = I.ev N y → x - y ∈ K := by
    intro x y hxy
    obtain ⟨z, hz⟩ := (tateIso_ev_eq_iff I hN x y).1 hxy
    exact LinearMap.mem_range.2
      ⟨z, by rw [hz, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]⟩
  let β : D.La →ₗ[𝓞 E] D.La ⧸ K :=
    { toFun := fun a => Submodule.Quotient.mk (b a)
      map_add' := fun a c => by
        rw [← Submodule.Quotient.mk_add]
        refine (Submodule.Quotient.eq K).2 (memK _ _ ?_)
        rw [hb, I.add, hb, hb, hadd]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        refine (Submodule.Quotient.eq K).2 (memK _ _ ?_)
        rw [hb, I.lin, hb, hlin] }
  have := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property K.mkQ β K.mkQ_surjective
  have hfα : ∀ a, I.ev N (f a) = α a := by
    intro a
    have h1 : (Submodule.Quotient.mk (f a) : D.La ⧸ K) = Submodule.Quotient.mk (b a) :=
      LinearMap.congr_fun hf a
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.eq K).1 h1)
    rw [← hb a]
    exact (tateIso_ev_eq_iff I hN _ _).2
      ⟨z, by rw [← hz, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]⟩
  obtain ⟨ν, hνc, hξν⟩ := exists_coprime_zpow hN (I.ζ_prim N hN) hξ
  have hEF : ∀ a c, (N : ℤ) ∣ D.EF (f a) (f c) - ν * D.EF a c := by
    intro a c
    have h1 := I.isom N hN (f a) (f c)
    rw [hfα, hfα] at h1
    have h2 := he _ _ _ _ (hiso a c) h1
    rw [hξν, ← zpow_mul] at h2
    refine ((I.ζ_prim N hN).zpow_eq_one_iff_dvd _).1 ?_
    rw [zpow_sub, ← h2, mul_inv_cancel]
  obtain ⟨g, hgf, hgν⟩ := hL f ν hN hνc hEF
  refine ⟨LevelTwist.twist I g (hν g), ?_, fun a => ?_⟩
  · rw [LevelTwist.twist_ζ, hξν]
    exact LevelTwist.zeta_zpow_congr I hN hgν
  · rw [LevelTwist.twist_ev, ← hfα a]
    exact LevelTwist.ev_congr I hN (hgf a)

theorem exists_root_ext (B : Type) [Field B] [CharZero B] {A N : ℕ} (hN : 0 < N) (hA : A ∣ N) {ζ : B}
    (hζ : IsPrimitiveRoot ζ A) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra B L) (ξ : Lˣ), FiniteDimensional B L ∧ IsPrimitiveRoot ξ N ∧
      (ξ : L) ^ (N / A) = algebraMap B L ζ := by
  classical
  have : NeZero N := ⟨hN.ne'⟩
  have hA0 : 0 < A := Nat.pos_of_dvd_of_pos hA hN
  have : NeZero A := ⟨hA0.ne'⟩
  have hω := IsCyclotomicExtension.zeta_spec N B (CyclotomicField N B)
  set ω := IsCyclotomicExtension.zeta N B (CyclotomicField N B)
  have hq : 0 < N / A := Nat.div_pos (Nat.le_of_dvd hN hA) hA0
  have hω' : IsPrimitiveRoot (ω ^ (N / A)) A := by
    have := hω.pow_of_dvd hq.ne' (Nat.div_dvd_of_dvd hA)
    rwa [Nat.div_div_self hA hN.ne'] at this
  have hη : IsPrimitiveRoot (algebraMap B (CyclotomicField N B) ζ) A :=
    hζ.map_of_injective (algebraMap B (CyclotomicField N B)).injective
  obtain ⟨i, hiA, hi⟩ := hω'.eq_pow_of_pow_eq_one hη.pow_eq_one
  have hic : i.Coprime A := (hω'.pow_iff_coprime hA0 i).1 (by rw [hi]; exact hη)
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hA (ZMod.unitOfCoprime i hic)
  have hji : (v : ZMod N).val % A = i % A := by
    have h1 := congrArg (fun u : (ZMod A)ˣ => (u : ZMod A)) hv
    simp only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime] at h1
    rw [← ZMod.natCast_val] at h1
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 h1
  have hξ : IsPrimitiveRoot (ω ^ (v : ZMod N).val) N := hω.pow_of_coprime _ (ZMod.val_coe_unit_coprime v)
  refine ⟨CyclotomicField N B, inferInstance, inferInstance, (hξ.isUnit hN.ne').unit, ?_, ?_, ?_⟩
  · exact IsCyclotomicExtension.finiteDimensional {N} B (CyclotomicField N B)
  · exact IsPrimitiveRoot.coe_units_iff.1 (by rw [IsUnit.unit_spec]; exact hξ)
  · rw [IsUnit.unit_spec, ← pow_mul, mul_comm, pow_mul, pow_eq_pow_mod _ hω'.pow_eq_one, hji,
      Nat.mod_eq_of_lt hiA, hi]

end GlobalTheory.LevCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescOfIsFiniteOfDensePart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isFinite_graphClosure_fst_of_isFinite {S X X' Y : Scheme.{0}} (π : X ⟶ X') (s' : X' ⟶ S)
    (p : Y ⟶ S) (f : X ⟶ Y) (h : π ≫ s' = f ≫ p) [IsFinite π] [IsSeparated p]
    [LocallyOfFiniteType p] : IsFinite (graphClosure.fst s' p π f h) := by
  have e := graphClosure.incl_fst s' p π f h
  have : IsFinite (graphClosure.incl s' p π f h ≫ graphClosure.fst s' p π f h) := by
    rw [e]; infer_instance
  have : IsFinite (graphClosure.incl s' p π f h) :=
    IsFinite.of_comp _ (graphClosure.fst s' p π f h)
  have : Surjective (graphClosure.incl s' p π f h) :=
    surjective_of_isDominant_of_isClosed_range _
      (graphClosure.incl s' p π f h).isClosedMap.isClosed_range
  have : UniversallyClosed (graphClosure.fst s' p π f h) :=
    .of_comp_surjective (graphClosure.incl s' p π f h) _
  have : IsProper (graphClosure.fst s' p π f h) := {}
  have : LocallyQuasiFinite (graphClosure.fst s' p π f h) := by
    refine .of_finite_preimage_singleton _ fun s ↦ ?_
    refine (((graphClosure.incl s' p π f h ≫ graphClosure.fst s' p π f h).finite_preimage_singleton
      s).image (graphClosure.incl s' p π f h)).subset fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := (graphClosure.incl s' p π f h).surjective x
    exact ⟨y, by simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using hx, rfl⟩
  exact .of_isProper_of_locallyQuasiFinite _

theorem exists_desc_of_isFinite_of_densePart : ∀ (S X X' U U' Y : Scheme.{0}) [IsLocallyNoetherian X'] (π : X ⟶ X') (j : U ⟶ X) (j' : U' ⟶ X') (r : U ⟶ U') (s' : X' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) (f₀ : U' ⟶ Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → IsReduced X → IsFinite π → Surjective π → Surjective r → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsSeparated p → LocallyOfFiniteType p → j ≫ π = r ≫ j' → j ≫ f = r ≫ f₀ → f ≫ p = π ≫ s' → f₀ ≫ p = j' ≫ s' → ∃ f' : X' ⟶ Y, j' ≫ f' = f₀ ∧ π ≫ f' = f := by
  intro S X X' U U' Y _ π j j' r s' p f f₀ hX' _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄
  have := GlobalTheory.IsNormalScheme.of_pred hX'
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j'
  have : GlobalTheory.IsNormalScheme U' := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j'
  have := IsSchemeTheoreticallyDominant.of_isDominant r
  have := isFinite_graphClosure_fst_of_isFinite π s' p f h₃.symm
  let g := graphClosure.lift s' p π f h₃.symm j' f₀ h₄.symm r j h₁.symm h₂.symm
  have hg₁ : g ≫ graphClosure.fst s' p π f h₃.symm = j' := graphClosure.lift_fst ..
  have hg₂ : g ≫ graphClosure.snd s' p π f h₃.symm = f₀ := graphClosure.lift_snd ..
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, -⟩ := existsUnique_lift_of_densePart X' U' X' _ j' hX' ‹_› ‹_› ‹_› ‹_›
    (graphClosure.fst s' p π f h₃.symm) (𝟙 X') g inferInstance (by rw [hg₁, Category.comp_id])
  have h₅ : j' ≫ σ ≫ graphClosure.snd s' p π f h₃.symm = f₀ := by rw [reassoc_of% hσ₁, hg₂]
  refine ⟨σ ≫ graphClosure.snd s' p π f h₃.symm, h₅,
    ext_of_isDominant_of_isSeparated p ?_ j ?_⟩
  · rw [Category.assoc, Category.assoc, ← graphClosure.condition, reassoc_of% hσ₂, h₃]
  · rw [reassoc_of% h₁, h₅, h₂]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSquareOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_square_of_isGrpPullback {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S)
    [GrpObj G] (f : S' ⟶ S) (m : G'.left ⟶ G.left) (h : IsGrpPullback G' G f m) :
    ∃ m₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare m m₂ ∧
      m₂ ≫ (fst G G * snd G G).left = (fst G' G' * snd G' G').left ≫ m ∧
      m₂ ≫ (G ⊗ G).hom = (G' ⊗ G').hom ≫ f := by
  have hw : m ≫ G.hom = G'.hom ≫ f := h.1.w
  let a : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G := Over.homMk ((fst G' G').left ≫ m) (by
    simp only [Category.assoc, hw, Over.mk_hom]
    rw [← Category.assoc, Over.w])
  let b : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G := Over.homMk ((snd G' G').left ≫ m) (by
    simp only [Category.assoc, hw, Over.mk_hom]
    rw [← Category.assoc, Over.w])
  refine ⟨(lift a b).left, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact congrArg Over.Hom.left (lift_fst a b)
  · exact congrArg Over.Hom.left (lift_snd a b)
  · rw [← h.2 (G' ⊗ G') (fst G' G') (snd G' G') a b rfl rfl]
    have : lift a b ≫ (fst G G * snd G G) = a * b := by
      rw [MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left this
  · exact Over.w (lift a b)

theorem square_fibre_affine_opens : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A (spMap x₀) m → (∃ m₂ : (P₀.A ⊗ P₀.A).left ⟶ (P.A ⊗ P.A).left, IsSquare m m₂ ∧ m₂ ≫ (fst P.A P.A * snd P.A P.A).left = (fst P₀.A P₀.A * snd P₀.A P₀.A).left ≫ m ∧ m₂ ≫ (P.A ⊗ P.A).hom = (P₀.A ⊗ P₀.A).hom ≫ spMap x₀) ∧ IsSeparated P₀.A.hom ∧ IsPullback (fst P₀.A P₀.A).left (snd P₀.A P₀.A).left P₀.A.hom P₀.A.hom ∧ (∀ W : P.A.left.Opens, IsAffineOpen W → IsAffineOpen (m ⁻¹ᵁ W)) ∧ ∀ W W' : P.A.left.Opens, IsAffineOpen W → IsAffineOpen W' → IsAffineOpen (W ⊓ W') := by
  intro K _ P₀ R _ x₀ P m h
  have hp₀ : IsProper P₀.A.hom := P₀.isAb.proper
  have hp : IsProper P.A.hom := P.isAb.proper
  refine ⟨exists_square_of_isGrpPullback _ _ _ _ h, inferInstance,
    IsPullback.of_hasPullback _ _, fun W hW => ?_, fun W W' hW hW' => ?_⟩
  · have : IsAffineHom m :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) h.1.flip inferInstance
    exact hW.preimage m
  · have : IsSeparated (terminal.from P.A.left) := by
      rw [← terminal.comp_from P.A.hom]; infer_instance
    exact hW.inf hW'

end GlobalTheory.KS
end

