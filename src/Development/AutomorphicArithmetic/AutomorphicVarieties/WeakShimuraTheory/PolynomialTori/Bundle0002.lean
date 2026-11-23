module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.OnCompClosed
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lift_map_id {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R) :
    Lift.map (AlgHom.id O R) r = r := by
  apply Lift.ext
  ext g a b
  simp [Lift.map]

private theorem lift_map_map {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R S T : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing S] [Algebra O S] [IsCO O S]
    [CommRing T] [Algebra O T] [IsCO O T] (f : R →ₐ[O] S) (g : S →ₐ[O] T) (r : Lift O rbar R) :
    Lift.map g (Lift.map f r) = Lift.map (g.comp f) r := by
  apply Lift.ext
  ext x a b
  simp [Lift.map]

private theorem cond_map_of_isClosed {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    (P : Cond O rbar) (hP : P.IsClosed)
    {R S : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing S] [Algebra O S] [IsCO O S]
    (r : Lift O rbar R) (hr : P R r) (f : R →ₐ[O] S) : P S (Lift.map f r) := by
  obtain ⟨I, hI⟩ := hP R r
  have h0 := (hI R (AlgHom.id O R)).1 (by rw [lift_map_id]; exact hr)
  refine (hI S f).2 fun x hx => ?_
  have := h0 x hx
  simp only [AlgHom.id_apply] at this
  rw [this, map_zero]

theorem UpperTheory.V.Ws.Po.onCompClosed :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι]
      (rbar : Γ →* Matrix ι ι (ResidueField O)) (P : Cond O rbar) (ρ₀ : Γ →* Matrix ι ι O), P.IsClosed →
      ∀ (U : Type) [CommRing U] [Algebra O U] [IsCO O U] (ρ : Lift O rbar U), Represents P ρ → ∀ J : Ideal U,
      (∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : U →ₐ[O] C), OnComp P ρ₀ (ρ.map f) ↔ J ≤ RingHom.ker f) →
      Cond.IsClosed (rbar := rbar) fun _ _ _ _ r => OnComp P ρ₀ r := by
  intro O _ _ Γ ι _ _ _ _ rbar P ρ₀ hP U _ _ _ ρ hρ J hJ
  intro R _ _ _ r
  have onP : ∀ (S : Type) [CommRing S] [Algebra O S] [IsCO O S] (s : Lift O rbar S),
      OnComp P ρ₀ s → P S s := by
    intro S _ _ _ s hs
    obtain ⟨B, _, _, _, _, ρ', hP', -, y, hy⟩ := hs
    subst hy
    exact cond_map_of_isClosed P hP ρ' hP' y
  obtain ⟨I0, hI0⟩ := hP R r
  by_cases htop : I0 = ⊤
  · refine ⟨⊤, fun R' _ _ _ f => ⟨fun h x _ => ?_, fun h => ?_⟩⟩
    · exact (hI0 R' f).1 (onP _ _ h) x (by rw [htop]; exact Submodule.mem_top)
    · exfalso
      have h1 := h 1 Submodule.mem_top
      rw [map_one] at h1
      exact one_ne_zero h1
  · haveI : Nontrivial (R ⧸ I0) := Ideal.Quotient.nontrivial_iff.2 htop
    haveI : IsCO O (R ⧸ I0) :=
      co_quot O R (R ⧸ I0) (Ideal.Quotient.mkₐ O I0) (Ideal.Quotient.mkₐ_surjective O I0)
    have hPπ : P (R ⧸ I0) (Lift.map (Ideal.Quotient.mkₐ O I0) r) :=
      (hI0 _ (Ideal.Quotient.mkₐ O I0)).2 fun x hx => by
        rw [Ideal.Quotient.mkₐ_eq_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.2 hx
    obtain ⟨u, hu, -⟩ := (hρ (R ⧸ I0)).2 _ hPπ
    refine ⟨I0 ⊔ (J.map u).comap (Ideal.Quotient.mkₐ O I0), fun R' _ _ _ f => ?_⟩
    have key : ∀ hf : ∀ a ∈ I0, f a = 0, (OnComp P ρ₀ (Lift.map f r) ↔
        ∀ x ∈ I0 ⊔ (J.map u).comap (Ideal.Quotient.mkₐ O I0), f x = 0) := by
      intro hf
      set g := Ideal.Quotient.liftₐ I0 f hf with hg
      have hgπ : ∀ x, g (Ideal.Quotient.mkₐ O I0 x) = f x := fun x => rfl
      have hfg : f = g.comp (Ideal.Quotient.mkₐ O I0) := by
        ext x
        exact (hgπ x).symm
      have hmap : Lift.map f r = Lift.map (g.comp u) ρ := by
        rw [hfg, ← lift_map_map, ← hu, lift_map_map]
      rw [hmap, hJ]
      constructor
      · intro hJk x hx
        have hle : J.map u ≤ RingHom.ker g := by
          rw [Ideal.map_le_iff_le_comap]
          intro z hz
          exact hJk hz
        have hsup : I0 ⊔ (J.map u).comap (Ideal.Quotient.mkₐ O I0) ≤ RingHom.ker f := by
          refine sup_le (fun a ha => RingHom.mem_ker.2 (hf a ha)) ?_
          intro y hy
          have hy' : Ideal.Quotient.mkₐ O I0 y ∈ J.map u := hy
          have := hle hy'
          rw [RingHom.mem_ker, hgπ] at this
          exact RingHom.mem_ker.2 this
        exact RingHom.mem_ker.1 (hsup hx)
      · intro h y hy
        obtain ⟨x, hx⟩ := Ideal.Quotient.mkₐ_surjective O I0 (u y)
        have hxm : x ∈ (J.map u).comap (Ideal.Quotient.mkₐ O I0) := by
          show Ideal.Quotient.mkₐ O I0 x ∈ J.map u
          rw [hx]
          exact Ideal.mem_map_of_mem _ hy
        have := h x (Ideal.mem_sup_right hxm)
        rw [RingHom.mem_ker, AlgHom.comp_apply, ← hx, hgπ]
        exact this
    constructor
    · intro h
      exact (key fun x hx => (hI0 R' f).1 (onP _ _ h) x hx).1 h
    · intro h
      exact (key fun a ha => h a (Ideal.mem_sup_left ha)).2 h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.OnCompTorus
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem wv_map {A B : Type} [CommRing A] [CommRing B] (F : A →+* B) (t : Aˣ × Aˣ) (s : Bˣ × Bˣ)
    (h1 : F t.1 = s.1) (h2 : F t.2 = s.2) (w : ℤ × ℤ) : F (wv t w : Aˣ) = (wv s w : Bˣ) := by
  have e1 : Units.map (F : A →* B) t.1 = s.1 := Units.ext h1
  have e2 : Units.map (F : A →* B) t.2 = s.2 := Units.ext h2
  have : Units.map (F : A →* B) (wv t w) = wv s w := by
    unfold wv
    rw [map_mul, map_zpow, map_zpow, e1, e2]
  exact congrArg Units.val this

private theorem wv_one {A B : Type} [CommRing A] [CommRing B] (F : A →+* B) (t : Aˣ × Aˣ)
    (h1 : F t.1 = 1) (h2 : F t.2 = 1) (w : ℤ × ℤ) : F (wv t w : Aˣ) = 1 := by
  rw [wv_map F t (1, 1) h1 h2]
  simp [wv]

private theorem conj_lift {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {rbar : Γ →* M4 (ResidueField O)} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R)
    (s : Rˣ × Rˣ) (h1 : res O R s.1 = 1) (h2 : res O R s.2 = 1) :
    ∃ r' : Lift O rbar R, ∀ g, r'.hom g = tconj s (r.hom g) := by
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, -⟩ := grp R
  refine ⟨{ hom := ⟨⟨fun g => tconj s (r.hom g), by rw [map_one, hone]⟩, fun g h => ?_⟩
            cont := fun a b N => ?_
            red := fun g a b => ?_ }, fun _ => rfl⟩
  · show tconj s _ = _
    rw [map_mul, hmul]
  · show IsLocallyConstant fun g => Ideal.Quotient.mk _ ((wv s (wt a b) : R) * r.hom g a b)
    simp only [map_mul]
    exact (IsLocallyConstant.const _).mul (r.cont a b N)
  · show res _ _ ((wv s (wt a b) : R) * r.hom g a b) = _
    have := wv_one (res O R : R →+* ResidueField O) s h1 h2 (wt a b)
    rw [RingHom.coe_coe] at this
    rw [map_mul, this, one_mul, r.red]

theorem UpperTheory.V.Ws.Po.onCompTorus :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (Γ : Type) [Group Γ] [TopologicalSpace Γ]
      (rbar : Γ →* M4 (ResidueField O)) (P : Cond O rbar) (ρ₀ : Γ →* M4 O),
      (∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (r : Lift O rbar R), P R r → P R' (r.map f)) →
      (∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r r' : Lift O rbar R) (s : Rˣ × Rˣ), (∀ g, r'.hom g = tconj s (r.hom g)) → P R r → P R r') →
      ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r r' : Lift O rbar R) (s : Rˣ × Rˣ), res O R s.1 = 1 → res O R s.2 = 1 →
        (∀ g, r'.hom g = tconj s (r.hom g)) → OnComp P ρ₀ r → OnComp P ρ₀ r' := by
  intro O _ _ _ _ Γ _ _ rbar P ρ₀ hmap htor R _ _ _ r r' s h1 h2 hr ⟨B, _, _, _, _, ρ, hP, ⟨x, hx⟩, y, hy⟩
  haveI : IsCO O (MvPowerSeries (Fin 2) B) := co_mvps O B (Fin 2)
  haveI : IsDomain (MvPowerSeries (Fin 2) B) := NoZeroDivisors.to_isDomain _
  let c : B →ₐ[O] MvPowerSeries (Fin 2) B := IsScalarTower.toAlgHom O B _
  have hu : ∀ i : Fin 2, IsUnit (1 + MvPowerSeries.X i : MvPowerSeries (Fin 2) B) := fun i => by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  let t : (MvPowerSeries (Fin 2) B)ˣ × (MvPowerSeries (Fin 2) B)ˣ := ((hu 0).unit, (hu 1).unit)
  have ht1 : (t.1 : MvPowerSeries (Fin 2) B) = 1 + MvPowerSeries.X 0 := rfl
  have ht2 : (t.2 : MvPowerSeries (Fin 2) B) = 1 + MvPowerSeries.X 1 := rfl
  obtain ⟨x', ⟨xC, xX⟩, -⟩ := co_ev O B O (Fin 2) x (fun _ => 0) fun _ => zero_mem _
  have x1 : x' t.1 = 1 := by rw [ht1, map_add (f := _), map_one, xX, add_zero]
  have x2 : x' t.2 = 1 := by rw [ht2, map_add (f := _), map_one, xX, add_zero]
  obtain ⟨y', ⟨yC, yX⟩, -⟩ := co_ev O B R (Fin 2) y ![(s.1 : R) - 1, (s.2 : R) - 1] fun i => by
    rw [← res_eq_zero_iff O]
    fin_cases i
    · simp [h1]
    · simp [h2]
  have y1 : y' t.1 = s.1 := by rw [ht1, map_add (f := _), map_one, yX]; simp
  have y2 : y' t.2 = s.2 := by rw [ht2, map_add (f := _), map_one, yX]; simp
  obtain ⟨ρ', hρ'⟩ := conj_lift (ρ.map c) t (by rw [← UpperTheory.V.Alg.res_map x' _, x1, map_one]) (by rw [← UpperTheory.V.Alg.res_map x' _, x2, map_one])
  have he : ∀ g a b, ρ'.hom g a b = (wv t (wt a b)).val * MvPowerSeries.C (ρ.hom g a b) :=
    fun g a b => by rw [hρ']; rfl
  refine ⟨MvPowerSeries (Fin 2) B, inferInstance, inferInstance, inferInstance, inferInstance, ρ',
    htor _ _ _ t hρ' (hmap _ _ c ρ hP), ⟨x', fun g a b => ?_⟩, y', ?_⟩
  · have := wv_one (x' : MvPowerSeries (Fin 2) B →+* O) t x1 x2 (wt a b)
    rw [RingHom.coe_coe] at this
    rw [he, map_mul, this, one_mul, xC, hx]
  · ext g a b
    have := wv_map (y' : MvPowerSeries (Fin 2) B →+* R) t s y1 y2 (wt a b)
    rw [RingHom.coe_coe] at this
    rw [Lift.map_hom, he, map_mul, this, yC, hr, ← hy]
    rfl
end

