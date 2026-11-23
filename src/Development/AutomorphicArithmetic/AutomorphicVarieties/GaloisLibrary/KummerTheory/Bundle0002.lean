module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0028
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

open KStar.TotallyRealRoots in
private theorem eg_pow_mem {l : ℕ} [Fact l.Prime] {a : ℕ} (ha : 1 ≤ a) {u : ℤ_[l]ˣ} (hu : u ∈ princ l a) :
    u ^ l ∈ princ l (a + 1) := by
  rw [mem_princ] at hu ⊢
  obtain ⟨c, hc⟩ := hu
  obtain ⟨f, hf⟩ := sq_dvd_add_pow_sub_sub ((l : ℤ_[l]) ^ a * c) 1 l
  have hw : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ a * c := by rw [← hc]; ring
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  refine ⟨c + (l : ℤ_[l]) ^ m * c ^ 2 * f, ?_⟩
  rw [Units.val_pow_eq_pow_val, hw]
  simp only [one_pow, one_mul] at hf
  linear_combination hf

open KStar.TotallyRealRoots in
private theorem eg_exists_not_mem {l : ℕ} [Fact l.Prime] {u : ℤ_[l]ˣ} (hu : u ≠ 1) :
    ∃ a, u ∉ princ l a := by
  by_contra h
  push Not at h
  apply hu
  have hb : IsClosed ((⊥ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_bot]
    exact isClosed_singleton
  have := mem_of_isClosed hb (x := u) fun b => ⟨1, Subgroup.one_mem _, by
    rw [map_one]; exact (MonoidHom.mem_ker.1 (h b)).symm⟩
  exact Subgroup.mem_bot.1 this

theorem UpperTheory.V.Kum.existsGen :
    ∀ (l : ℕ) [Fact l.Prime] (V : Subgroup ℤ_[l]ˣ), IsClosed (V : Set ℤ_[l]ˣ) → (l ≠ 2 ∨ V ≤ KStar.TotallyRealRoots.princ l 2) → ∃ γ ∈ V, V ≤ (Subgroup.zpowers γ).topologicalClosure := by
  classical
  intro l _ V _ hl
  have hp : l.Prime := Fact.out
  obtain ⟨⟨_, g, hg, rfl⟩, hgen⟩ := IsCyclic.exists_generator (α := V.map (KStar.TotallyRealRoots.red l))
  have key : ∀ γ ∈ V, KStar.TotallyRealRoots.red l γ = KStar.TotallyRealRoots.red l g →
      V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ (Subgroup.zpowers γ).topologicalClosure →
      V ≤ (Subgroup.zpowers γ).topologicalClosure := by
    intro γ hγ e h v hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨_, Subgroup.mem_map_of_mem _ hv⟩)
    have hk' : KStar.TotallyRealRoots.red l g ^ k = KStar.TotallyRealRoots.red l v := congrArg Subtype.val hk
    have h1 : v * (γ ^ k)⁻¹ ∈ V ⊓ KStar.TotallyRealRoots.princ l 1 := by
      refine Subgroup.mem_inf.2 ⟨V.mul_mem hv (V.inv_mem (V.zpow_mem hγ k)), ?_⟩
      rw [KStar.TotallyRealRoots.princ_one_eq_ker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, e, hk',
        mul_inv_cancel]
    have h2 : γ ^ k ∈ (Subgroup.zpowers γ).topologicalClosure :=
      Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers γ k)
    simpa using Subgroup.mul_mem _ (h h1) h2
  by_cases hW : V ⊓ KStar.TotallyRealRoots.princ l 1 = ⊥
  · exact ⟨g, hg, key g hg rfl (by rw [hW]; exact bot_le)⟩
  have hex : ∃ b, ¬ V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ KStar.TotallyRealRoots.princ l b := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW
    obtain ⟨b, hb⟩ := eg_exists_not_mem (u := w) (fun h => hw1 (Subtype.ext h))
    exact ⟨b, fun h => hb (h hw)⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ KStar.TotallyRealRoots.princ l m :=
    fun m hm => not_not.1 (Nat.find_min hex hm)
  have h1 : 1 < Nat.find hex := by
    by_contra h
    exact hspec (inf_le_right.trans (KStar.TotallyRealRoots.princ_anti (by omega)))
  have h2 : l = 2 → 2 < Nat.find hex := by
    intro h2
    by_contra h
    exact hspec (inf_le_left.trans ((hl.resolve_left (not_not.2 h2)).trans (KStar.TotallyRealRoots.princ_anti (by omega))))
  obtain ⟨a, ha⟩ : ∃ a, Nat.find hex = a + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [ha] at hspec hmin h1 h2
  have hle := hmin a (Nat.lt_succ_self a)
  obtain ⟨u, hu, hua⟩ := SetLike.not_le_iff_exists.1 hspec
  have fin : ∀ γ ∈ V, KStar.TotallyRealRoots.red l γ = KStar.TotallyRealRoots.red l g → γ ^ (l - 1) ∉ KStar.TotallyRealRoots.princ l (a + 1) →
      V ≤ (Subgroup.zpowers γ).topologicalClosure := by
    intro γ hγ e h
    refine key γ hγ e (hle.trans ?_)
    have hm : γ ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l a := by
      refine hle (Subgroup.mem_inf.2 ⟨V.pow_mem hγ _, ?_⟩)
      rw [KStar.TotallyRealRoots.princ_one_eq_ker, MonoidHom.mem_ker, map_pow, ZMod.units_pow_card_sub_one_eq_one]
    refine KStar.TotallyRealRoots.princ_le_of_isClosed (u := γ ^ (l - 1)) (by omega) (fun h => by have := h2 h; omega)
      (Subgroup.isClosed_topologicalClosure _)
      (Subgroup.le_topologicalClosure _ (Subgroup.npow_mem_zpowers γ _)) ?_
    exact emultiplicity_eq_coe.2 ⟨KStar.TotallyRealRoots.mem_princ.1 hm, fun h' => h (KStar.TotallyRealRoots.mem_princ.2 h')⟩
  by_cases hga : g ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l (a + 1)
  · refine ⟨g * u, V.mul_mem hg hu.1, fin _ (V.mul_mem hg hu.1) ?_ ?_⟩
    · have : u ∈ (KStar.TotallyRealRoots.red l).ker := by
        rw [← KStar.TotallyRealRoots.princ_one_eq_ker]
        exact (Subgroup.mem_inf.1 hu).2
      rw [map_mul, MonoidHom.mem_ker.1 this, mul_one]
    · intro h
      rw [mul_pow] at h
      have h3 := (mul_mem_cancel_left hga).1 h
      have h4 := eg_pow_mem (by omega) (hle hu)
      have h5 : u ^ l = u ^ (l - 1) * u := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
      rw [h5] at h4
      exact hua ((mul_mem_cancel_left h3).1 h4)
  · exact ⟨g, hg, fin g hg rfl hga⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FunRepMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.funRepMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) (U : Subgroup (G F Ω)) [U.Normal] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M],
    (∀ g, ∀ φ ∈ XDual N U R M, funRep (R := R) (M := M) U g φ ∈ XDual N U R M) ∧
    (∀ g ∈ U, ∀ φ ∈ XDual N U R M, funRep (R := R) (M := M) U g φ = φ) ∧
    ∀ (ρ : Representation R (G F Ω) M) (φ : U → M), φ ∈ EqHom N U ρ ↔
      φ ∈ XDual N U R M ∧ ∀ g u, ρ g (funRep (R := R) (M := M) U g φ u) = φ u := by
  intro F Ω _ _ _ _ _ N U _ R M _ _ _
  have hf : ∀ (g : G F Ω) (φ : U → M) (u : U),
      funRep (R := R) (M := M) U g φ u = φ (UpperTheory.V.Base.conjHom U g u) := fun _ _ _ => rfl
  have hc : ∀ (g : G F Ω) (u : U), (UpperTheory.V.Base.conjHom U g u).1 = g⁻¹ * u.1 * g := fun _ _ => rfl
  refine ⟨fun g φ hφ => ?_, fun g hg φ hφ => ?_, fun ρ φ => ?_⟩
  · have h : IsLift (RingEquiv.refl F) g.toRingEquiv := fun x => g.commutes x
    have e1 : ∀ x : G F Ω, conjGal h x = g⁻¹ * x * g := fun _ => rfl
    have hA : ∀ (A : ValuationSubring Ω) x, g.toRingEquiv x ∈ A ↔ x ∈ A.comap g.toRingEquiv.toRingHom :=
      fun _ _ => Iff.rfl
    obtain ⟨h1, h2, h3, h4⟩ := hφ
    refine ⟨h1.comp_continuous (continuous_conjHom U g), fun a b => ?_, fun A u hu => ?_, fun A hN u hu => ?_⟩
    · rw [hf, hf, hf, map_mul, h2]
    · rw [hf]
      refine h3 (A.comap g.toRingEquiv.toRingHom) _ ?_
      rw [hc, ← e1]
      exact conjGal_mem_Ine h (hA A) hu
    · rw [hf]
      refine h4 (A.comap g.toRingEquiv.toRingHom) ?_ _ ?_
      · rw [← val_lt_one (hA A), map_natCast]
        exact hN
      · rw [hc, ← e1]
        exact conjGal_mem_Dec h (hA A) hu
  · funext u
    have e : (⟨g, hg⟩ : U) * UpperTheory.V.Base.conjHom U g u = u * ⟨g, hg⟩ :=
      Subtype.ext (by simp [hc, mul_assoc])
    have e2 := congrArg φ e
    rw [hφ.2.1, hφ.2.1, add_comm] at e2
    rw [hf]
    exact add_right_cancel e2
  · unfold EqHom
    rw [Submodule.mem_inf, Submodule.mem_iInf]
    refine and_congr_right fun _ => forall_congr' fun g => ⟨fun h u => ?_, fun h u u' hu => ?_⟩
    · rw [hf]
      refine (h _ u fun x => ?_).symm
      show u.1 (g x) = g (g.symm (u.1 (g x)))
      rw [g.apply_symm_apply]
    · have e : UpperTheory.V.Base.conjHom U g u' = u := Subtype.ext (AlgEquiv.ext fun x => by
        show g.symm (u'.1 (g x)) = u.1 x
        exact g.symm_apply_eq.2 (hu x))
      rw [← h u', hf, e]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.galOfCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (E K : Type) [Field E] [Field K] [Algebra E K] [Algebra E Ω] [Algebra K Ω] [IsScalarTower E K Ω] [IsCyclotomicExtension {l ^ n} E K], galOf F K Ω = levU l (galOf F E Ω) n := by
  intro F Ω _ _ _ _ _ l _ n E K _ _ _ _ _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  ext σ
  have key : ∀ t : Ω, t ^ (l ^ n) = 1 →
      σ t = t ^ ((cycZ F Ω l σ).val.toZModPow n).val := fun t ht =>
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω σ) t ht
  show σ ∈ galOf F K Ω ↔ σ ∈ galOf F E Ω ⊓ Subgroup.comap (cycZ F Ω l) (KStar.TotallyRealRoots.princ l n)
  rw [Subgroup.mem_inf, Subgroup.mem_comap, KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, KStar.TotallyRealRoots.redPow]
  constructor
  · intro h
    have hE : σ ∈ galOf F E Ω := fun x => by
      have hx := h (algebraMap E K x)
      rwa [← IsScalarTower.algebraMap_apply] at hx
    refine ⟨hE, ?_⟩
    have hζ : IsPrimitiveRoot (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) (l ^ n) :=
      (IsCyclotomicExtension.zeta_spec (l ^ n) E K).map_of_injective (algebraMap K Ω).injective
    have h1 := key _ hζ.pow_eq_one
    rw [h (IsCyclotomicExtension.zeta (l ^ n) E K)] at h1
    have hfin : IsOfFinOrder (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) :=
      orderOf_pos_iff.mp (by rw [← hζ.eq_orderOf]; exact Nat.pos_of_neZero _)
    have e : (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) ^
        ((cycZ F Ω l σ).val.toZModPow n).val =
        (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) ^ 1 := by
      rw [pow_one]
      exact h1.symm
    have h3 : ((cycZ F Ω l σ).val.toZModPow n).val ≡ 1 [MOD l ^ n] := by
      have h5 := hfin.pow_eq_pow_iff_modEq.mp e
      rwa [← hζ.eq_orderOf] at h5
    ext
    have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h3
    rw [ZMod.natCast_zmod_val, Nat.cast_one] at h4
    simpa using h4
  · rintro ⟨hE, hc⟩
    have hc' : (cycZ F Ω l σ).val.toZModPow n = 1 := by
      have := congrArg Units.val hc
      simpa using this
    intro x
    let f1 : K →ₐ[E] Ω := IsScalarTower.toAlgHom E K Ω
    let f2 : K →ₐ[E] Ω :=
      { toRingHom := (σ : Ω →+* Ω).comp (algebraMap K Ω)
        commutes' := fun r => by
          show σ (algebraMap K Ω (algebraMap E K r)) = algebraMap E Ω r
          rw [← IsScalarTower.algebraMap_apply]
          exact hE r }
    have hx := IsCyclotomicExtension.adjoin_roots (S := {l ^ n}) (A := E) (B := K) x
    have hmem : x ∈ AlgHom.equalizer f1 f2 := by
      refine Algebra.adjoin_le (fun b hb => ?_) hx
      obtain ⟨m, hm, -, hbm⟩ := hb
      rw [Set.mem_singleton_iff] at hm
      subst hm
      have ht : (algebraMap K Ω b) ^ (l ^ n) = 1 := by rw [← map_pow, hbm, map_one]
      show algebraMap K Ω b = σ (algebraMap K Ω b)
      rw [key _ ht, hc', ZMod.val_one_eq_one_mod]
      conv_lhs => rw [← pow_one (algebraMap K Ω b), ← Nat.mod_add_div 1 (l ^ n), pow_add, pow_mul, ht, one_pow, mul_one]
    exact ((AlgHom.mem_equalizer f1 f2 x).mp hmem).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Imports
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.h90 :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (f : G K Ω → Ω), IsLocallyConstant f → (∀ g, f g ≠ 0) → (∀ g h, f (g * h) = f g * g (f h)) → ∃ β : Ω, β ≠ 0 ∧ ∀ g : G K Ω, g β = f g * β :=
  _root_.UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.h90
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.IsCMOfConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem isCM_of_conj (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (h : ∀ x : K, ∃ y : K, ∀ φ : K →+* ℂ, φ y = starRingEnd ℂ (φ x)) : IsCMField K := by
  classical
  choose c hc using h
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hcc : ∀ x, c (c x) = x := fun x => φ.injective (by rw [hc, hc, Complex.conj_conj])
  let τ : K ≃+* K :=
    { toFun := c
      invFun := c
      left_inv := hcc
      right_inv := hcc
      map_mul' := fun x y => φ.injective (by simp only [hc, map_mul])
      map_add' := fun x y => φ.injective (by simp only [hc, map_add (f := _)]) }
  let σ : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := τ) (fun q => by simp)
  have hσ : ∀ ψ : K →+* ℂ, ComplexEmbedding.IsConj ψ σ := fun ψ => by
    ext x
    exact (hc x ψ).symm
  have hσ' : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers, ComplexEmbedding.orderOf_isConj_two_of_ne_one (hσ φ)]
    exact (ComplexEmbedding.isConj_ne_one_iff (hσ φ)).mpr <| IsTotallyComplex.complexEmbedding_not_isReal φ
  let L := (FixedPoints.intermediateField (Subgroup.zpowers σ) : IntermediateField ℚ K)
  have : IsTotallyReal L := ⟨fun w ↦ by
    obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
    dsimp only
    rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
      ComplexEmbedding.isReal_iff]
    ext x
    have hx : c x.1 = x.1 := x.2 ⟨σ, Subgroup.mem_zpowers σ⟩
    have := hc x.1 W.embedding
    rw [hx] at this
    exact this.symm⟩
  have : Algebra.IsQuadraticExtension L K := ⟨by
    have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
    rw [← hσ', Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card (Subgroup.zpowers σ) K⟩
  exact IsCMField.ofCMExtension L K
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenDirected
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.lenDirected :
    ∀ (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (W : Submodule R X) (P : ℕ → Submodule R X) (Bd : ℕ∞), Monotone P → W ≤ ⨆ n, P n →
    (∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length R (P n) ≤ Bd) → Module.length R W ≤ Bd := by
  intro R X _ _ _ W P Bd hP hW hBd
  classical
  rw [← WithBot.coe_le_coe, Module.coe_length, Order.krullDim, iSup_le_iff]
  intro p
  have hstep : ∀ i : Fin p.length, ∃ x : W, x ∈ p i.succ ∧ x ∉ p i.castSucc := by
    intro i
    exact SetLike.exists_of_lt (p.step i)
  choose x hx1 hx2 using hstep
  have hdir : Directed (· ≤ ·) P := hP.directed_le
  have hmem : ∀ i : Fin p.length, ∃ n, (x i : X) ∈ P n := by
    intro i
    exact (Submodule.mem_iSup_of_directed P hdir).mp (hW (x i).2)
  choose m hm using hmem
  obtain ⟨n, hn, hlen⟩ := hBd (Finset.univ.sup m)
  have hxn : ∀ i, (x i : X) ∈ P n := by
    intro i
    exact hP ((Finset.le_sup (Finset.mem_univ i)).trans hn) (hm i)
  let f : Submodule R W → Submodule R (P n) := fun S => (S.map W.subtype).comap (P n).subtype
  have hfmono : Monotone f := by
    intro S T hST
    exact Submodule.comap_mono (Submodule.map_mono hST)
  let q : LTSeries (Submodule R (P n)) :=
    { length := p.length
      toFun := fun i => f (p i)
      step := by
        intro i
        refine lt_of_le_of_ne (hfmono (p.step i).le) ?_
        intro heq
        have h1 : (⟨(x i : X), hxn i⟩ : P n) ∈ f (p i.succ) := by
          simp only [f, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map]
          exact ⟨x i, hx1 i, rfl⟩
        rw [← heq] at h1
        simp only [f, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map] at h1
        obtain ⟨y, hy, hyx⟩ := h1
        have : y = x i := Subtype.ext hyx
        exact hx2 i (this ▸ hy) }
  have hq := Order.LTSeries.length_le_krullDim q
  rw [← Module.coe_length] at hq
  exact hq.trans (WithBot.coe_le_coe.mpr hlen)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenOfCard
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem card_simple (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    [h : IsSimpleModule ℤ_[l] M] : Nat.card M = l := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp h
  have hIm : I = IsLocalRing.maximalIdeal ℤ_[l] := IsLocalRing.eq_maximalIdeal hI
  subst hIm
  rw [Nat.card_congr e.toEquiv]
  have f := RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZMod (p := l)))
  have g := Ideal.quotEquivOfEq (PadicInt.ker_toZMod (p := l))
  rw [← Nat.card_congr g.toEquiv, Nat.card_congr f.toEquiv, Nat.card_zmod]

private theorem aux (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (h : IsFiniteLength ℤ_[l] M) : ∃ k : ℕ, Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k := by
  induction h with
  | of_subsingleton =>
    exact ⟨0, by rw [Module.length_eq_zero]; rfl, by rw [Nat.card_of_subsingleton (0 : _)]; simp⟩
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨k, hk, hc⟩ := ih
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype N)
        (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N), hk, Module.length_eq_one]
      rfl
    · rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
      have h1 : Nat.card (M ⧸ N.toAddSubgroup) = l := card_simple l (M ⧸ N)
      have h2 : Nat.card N.toAddSubgroup = l ^ k := hc
      rw [h1, h2, pow_succ, mul_comm]

theorem UpperTheory.V.Kum.lenOfCard :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M], ∃ k : ℕ, Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k := by
  intro l _ M _ _ _
  exact aux l M (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LevCompact
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem mem_princ_iff_norm_sub_one_le (l : ℕ) [Fact l.Prime] (a : ℕ) (x : ℤ_[l]ˣ) :
    x ∈ KStar.TotallyRealRoots.princ l a ↔ ‖(x : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(a : ℤ)) := by
  have h : x ∈ KStar.TotallyRealRoots.princ l a ↔ PadicInt.toZModPow a (x : ℤ_[l]) = 1 := by
    simp [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff]
  rw [h, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, map_one, sub_eq_zero]

private theorem princ_isClosed (l : ℕ) [Fact l.Prime] (a : ℕ) :
    IsClosed ((KStar.TotallyRealRoots.princ l a : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
  have e : ((KStar.TotallyRealRoots.princ l a : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) =
      {x : ℤ_[l]ˣ | ‖(x : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(a : ℤ))} := by
    ext x
    exact mem_princ_iff_norm_sub_one_le l a x
  rw [e]
  exact isClosed_le (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const

private theorem princ_antitone (l : ℕ) [Fact l.Prime] {a b : ℕ} (hab : a ≤ b) (x : ℤ_[l]ˣ)
    (hx : x ∈ KStar.TotallyRealRoots.princ l b) : x ∈ KStar.TotallyRealRoots.princ l a := by
  rw [mem_princ_iff_norm_sub_one_le] at hx ⊢
  refine hx.trans (zpow_le_zpow_right₀ ?_ (by omega))
  exact_mod_cast (Fact.out : l.Prime).one_lt.le

private theorem eq_one_of_mem_all_princ (l : ℕ) [Fact l.Prime] (x : ℤ_[l]ˣ)
    (hx : ∀ a, x ∈ KStar.TotallyRealRoots.princ l a) : x = 1 := by
  apply Units.ext
  refine (PadicInt.ext_of_toZModPow (x := (x : ℤ_[l])) (y := 1)).mp fun a => ?_
  have h := hx a
  simp only [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff] at h
  simpa using h

theorem UpperTheory.V.Kum.levCompact :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G F Ω)) (n : ℕ) (T : Type) [TopologicalSpace T] [CompactSpace T] (M : Type) [Zero M] (ψ : T × levU l U n → M), IsClosed (U : Set (G F Ω)) → IsLocallyConstant ψ →
    (∀ t (u : levU l U n), u.1 ∈ cycU l U → ψ (t, u) = 0) → ∃ m, n ≤ m ∧ ∀ t (u : levU l U n), u.1 ∈ levU l U m → ψ (t, u) = 0 := by
  intro F Ω _ _ _ _ _ l _ U n T _ _ M _ ψ hU hψ h0
  have memL : ∀ (m : ℕ) (x : G F Ω), x ∈ levU l U m ↔ x ∈ U ∧ cycZ F Ω l x ∈ KStar.TotallyRealRoots.princ l m := by
    intro m x
    simp [UpperTheory.V.Base.levU, Subgroup.mem_inf, Subgroup.mem_comap]
  have memC : ∀ x : G F Ω, x ∈ cycU l U ↔ x ∈ U ∧ cycZ F Ω l x = 1 := by
    intro x
    simp [UpperTheory.V.Base.cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
  have closedL : ∀ m : ℕ, IsClosed ((levU l U m : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro m
    have e : ((levU l U m : Subgroup (G F Ω)) : Set (G F Ω)) =
        (U : Set (G F Ω)) ∩ (cycZ F Ω l) ⁻¹' ((KStar.TotallyRealRoots.princ l m : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
      ext x
      exact memL m x
    rw [e]
    exact hU.inter ((princ_isClosed l m).preimage (continuous_cycZ F Ω l))
  haveI : CompactSpace (levU l U n) := isCompact_iff_compactSpace.mp (closedL n).isCompact
  let K : Set (T × levU l U n) := {p | ψ p ≠ 0}
  have hKc : IsClosed K := by
    have ho : IsOpen (ψ ⁻¹' {0}) := hψ.isOpen_fiber 0
    exact ho.isClosed_compl
  let t : ℕ → Set (T × levU l U n) := fun m => {p | (p.2 : G F Ω) ∈ levU l U m}
  have htc : ∀ m, IsClosed (t m) := fun m =>
    (closedL m).preimage (continuous_subtype_val.comp continuous_snd)
  have hst : K ∩ ⋂ m, t m = ∅ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hall
    apply hp
    obtain ⟨s, u⟩ := p
    apply h0 s u
    rw [memC]
    refine ⟨((memL n u.1).1 u.2).1, eq_one_of_mem_all_princ l _ fun a => ((memL a u.1).1 (hall a)).2⟩
  obtain ⟨v, hv⟩ := hKc.isCompact.elim_finite_subfamily_closed t htc (Set.disjoint_iff_inter_eq_empty.mpr hst)
  refine ⟨max n (v.sup id), le_max_left _ _, ?_⟩
  intro s u hu
  by_contra hne
  have hmem : (s, u) ∈ K ∩ ⋂ i ∈ v, t i := by
    refine ⟨hne, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    show (u : G F Ω) ∈ levU l U i
    rw [memL] at hu ⊢
    refine ⟨hu.1, princ_antitone l ?_ _ hu.2⟩
    exact (Finset.le_sup (f := id) hi).trans (le_max_right _ _)
  exact Set.disjoint_left.mp hv hmem.1 hmem.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.radConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (ζ β : Ω) (σ : Ω ≃+* Ω) (k : ZMod n) (φ φ' : U → ZMod n), ζ ^ n = 1 → σ ζ = ζ ^ k.val → IsRad ζ U φ β →
    (∀ u' : U, ∃ u : U, (∀ x, u'.1 (σ x) = σ (u.1 x)) ∧ φ' u' = k * φ u) → IsRad ζ U φ' (σ β) := by
  intro F Ω _ _ _ _ _ U n _ ζ β σ k φ φ' hζ hσ hβ h
  refine ⟨fun h0 => hβ.1 (σ.injective (by rw [h0, map_zero])), fun u' => ?_⟩
  obtain ⟨u, hu, hφ⟩ := h u'
  rw [hu β, hβ.2 u, map_mul, map_pow, hσ, hφ, ZMod.val_mul, ← pow_mul, ← pow_eq_pow_mod _ hζ]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.resInfConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ) (τ : F ≃+* F) (σ : Ω ≃+* Ω), IsLift τ σ → ∀ (x : H1 (qzTw D e)) (u u' : Uinf F Ω l), (∀ y, u'.1 (σ y) = σ (u.1 y)) → resInf D e (galoisActionOnCohomology D e τ x) u' = twScal l σ e • resInf D e x u := by
  intro F Ω _ _ _ _ _ l _ D e τ σ h x u u' hu
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h z
  have hc : conjGal h u'.1 = u.1 :=
    AlgEquiv.ext fun y => by rw [conjGal_apply, hu, RingEquiv.symm_apply_apply]
  rw [galois_action_cohomology_eq_conj D e h, e₁, resInf_mk, resInf_mk, f₁, conjGS_toGS, hc]
end

