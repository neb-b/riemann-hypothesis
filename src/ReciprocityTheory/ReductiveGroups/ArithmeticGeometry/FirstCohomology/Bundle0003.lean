module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Act

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S}

theorem comp_mulMon (f : A ⟶ A) [IsMonHom f] (x y : T ⟶ A) : (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem one_compMon (f : A ⟶ A) [IsMonHom f] : (1 : T ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem comp_padd (x : T ⟶ A) (f g : A ⟶ A) : x ≫ padd A f g = (x ≫ f) * (x ≫ g) := by
  simp only [padd]
  rw [← Category.assoc, comp_lift, Hom.mul_def]

variable {O : Type} [Ring O] (ρ : RingAct A O)

theorem act_add_apply (x : T ⟶ A) (a b : O) : x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b) := by
  rw [ρ.map_add, comp_padd]

theorem act_mul_apply (x : T ⟶ A) (a b : O) : x ≫ ρ.act (a * b) = (x ≫ ρ.act b) ≫ ρ.act a := by
  rw [ρ.map_mul, Category.assoc]

theorem act_one_apply (x : T ⟶ A) : x ≫ ρ.act 1 = x := by
  rw [ρ.map_one, Category.comp_id]

theorem act_zero_apply (x : T ⟶ A) : x ≫ ρ.act 0 = 1 := by
  have h := act_add_apply ρ x 0 0
  rw [add_zero] at h
  exact (_root_.mul_left_cancel (a := x ≫ ρ.act 0) (by rw [_root_.mul_one]; exact h)).symm

theorem act_nat_apply (x : T ⟶ A) (n : ℕ) : x ≫ ρ.act (n : O) = x ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero_apply, _root_.pow_zero]
  | succ n ih => rw [Nat.cast_succ, act_add_apply, ih, act_one_apply, _root_.pow_succ]

theorem pow_eq_one_of_kill {a b : O} {N : ℕ} (hab : a * b = (N : O)) (x : T ⟶ A) (hx : x ≫ ρ.act b = 1) :
    x ^ N = 1 := by
  rw [← act_nat_apply ρ x N, ← hab, act_mul_apply, hx]
  haveI := ρ.hom a
  exact one_compMon (ρ.act a)

end Act

theorem unitOn_injective {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := by
  intro u v h
  apply Units.ext
  have h1 := congrArg (fun w : (Γ(Sp K, ⊤))ˣ =>
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w : Γ(Sp K, ⊤))) h
  simpa [unitOn] using h1

section Sep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem mem_nsmul_of_dvd (Dw : Datum H) (N : ℕ) (d : Dw.La)
    (h : ∀ b, (N : ℤ) ∣ Dw.EF b d) : ∃ f : Dw.La, d = N • f := by
  have skew : ∀ x y, Dw.EF x y = - Dw.EF y x := by
    intro x y
    have hxy := Dw.alt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt] at hxy
    linarith
  have hdiv : ∀ y, (N : ℤ) ∣ Dw.EF d y := fun y => by
    rw [skew]
    exact dvd_neg.mpr (h y)
  let φ : Dw.La →ₗ[ℤ] ℤ :=
    { toFun := fun y => Dw.EF d y / N
      map_add' := fun y z => by
        simp only [map_add (f := _)]
        exact Int.add_ediv_of_dvd_left (hdiv y)
      map_smul' := fun m y => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc _ (hdiv y) }
  obtain ⟨f, hf⟩ := Dw.unimod.2 φ
  refine ⟨f, Dw.unimod.1 (LinearMap.ext fun y => ?_)⟩
  rw [map_nsmul, LinearMap.smul_apply, hf]
  show Dw.EF d y = N • (Dw.EF d y / N)
  rw [nsmul_eq_mul, Int.mul_ediv_cancel' (hdiv y)]

theorem sep_core (A : PolAV (Sp (FractionRing R))) : letI := H.starRing
    ∀ (oA : A.OAct (𝓞 E)) (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a g => g ≫ oA.act a)
        (fun n g g' c => WeilIs A.A A.L n g g' (unitOn c))) (N : ℕ), 1 ≤ N →
      ∀ β u u' : 𝓞 E, β * star β = (N : 𝓞 E) → u * β + u' * star β = 1 →
      ∀ x x' : TFK (R := R) F ⟶ A.A, x ≫ oA.act (star β) = 1 → x' ≫ oA.act (star β) = 1 → x ≠ x' →
        ∃ z : TFK (R := R) F ⟶ A.A, z ≫ oA.act β = 1 ∧
          ∃ c c' : Γ((TFK (R := R) F).left, ⊤)ˣ,
            WeilIs A.A A.L N z x c ∧ WeilIs A.A A.L N z x' c' ∧ c ≠ c' := by
  let _ := H.starRing
  intro oA Dw I N hN β u u' hβ huu x x' hx hx' hne
  have hN0 : 0 < N := hN
  have hlin : ∀ (c : 𝓞 E) b, I.ev N (c • b) = I.ev N b ≫ oA.act c := fun c b => I.lin N c b
  obtain ⟨a, rfl⟩ := (I.onto N hN0 x).1 (pow_eq_one_of_kill oA.toRingAct hβ x hx)
  obtain ⟨a', rfl⟩ := (I.onto N hN0 x').1 (pow_eq_one_of_kill oA.toRingAct hβ x' hx')
  obtain ⟨e, he⟩ := (I.ker N hN0 (star β • a)).1 (by rw [hlin]; exact hx)
  obtain ⟨e', he'⟩ := (I.ker N hN0 (star β • a')).1 (by rw [hlin]; exact hx')
  have hdN : ∀ f : Dw.La, a - a' ≠ N • f := by
    intro f hf
    apply hne
    have : a = a' + N • f := by rw [← hf]; abel
    rw [this, I.add, (I.ker N hN0 _).2 ⟨f, rfl⟩, _root_.mul_one]
  obtain ⟨b0, hb0⟩ : ∃ b0 : Dw.La, ¬ ((N : ℤ) ∣ Dw.EF b0 (a - a')) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨f, hf⟩ := mem_nsmul_of_dvd Dw N (a - a') hcon
    exact hdN f hf
  have h1 : Dw.EF b0 (a - a') = Dw.EF ((u * β) • b0) (a - a') + Dw.EF ((u' * star β) • b0) (a - a') := by
    rw [← LinearMap.add_apply, ← map_add (f := _), ← add_smul, huu, one_smul]
  have h2 : (N : ℤ) ∣ Dw.EF ((u * β) • b0) (a - a') := by
    have hd' : H.bar (u * β) • (a - a') = N • (H.bar u • (e - e')) := by
      rw [map_mul, mul_smul, smul_sub]
      change H.bar u • (star β • a - star β • a') = _
      rw [he, he', ← smul_sub]
      exact smul_comm _ _ _
    rw [Dw.adj, hd', map_nsmul, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  have hb : ¬ (N : ℤ) ∣ Dw.EF ((u' * star β) • b0) (a - a') := fun h => hb0 (by rw [h1]; exact dvd_add h2 h)
  refine ⟨I.ev N ((u' * star β) • b0), ?_, ?_⟩
  · rw [← hlin, smul_smul, show β * (u' * star β) = (N : 𝓞 E) * u' by rw [← hβ]; ring, mul_smul,
      Nat.cast_smul_eq_nsmul]
    exact (I.ker N hN0 _).2 ⟨_, rfl⟩
  · refine ⟨unitOn (I.ζ N ^ Dw.EF ((u' * star β) • b0) a), unitOn (I.ζ N ^ Dw.EF ((u' * star β) • b0) a'),
      I.isom N hN0 _ _, I.isom N hN0 _ _, fun hc => hb ?_⟩
    have hc' := unitOn_injective hc
    rw [← (I.ζ_prim N hN0).zpow_eq_one_iff_dvd, map_sub, zpow_sub, hc', _root_.mul_inv_cancel]

end Sep

theorem alphaPair_holds : AlphaPairStatement := by
  intro E _ _ _ H V _ _ _ t P _ α N hN hαN hu _ F _ _ _ Dw I x x' hx hx' hne
  obtain ⟨u, u', hu⟩ := hu
  exact sep_core (H := H) (R := V) (F := F) P.A P.oA Dw I N hN α u u' hαN hu x x' hx hx' hne

end ReciprocityTheory.ChartRestriction.G.H1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ClosedPointWeilPower
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section Grp

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}

lemma one_comp_hom (f : A ⟶ A) (hf : IsMonHom f) : (1 : T ⟶ A) ≫ f = 1 := by
  haveI := hf
  exact MonObj.one_comp f

lemma comp_act_nat {O : Type} [Ring O] (ρ : RingAct A O) (x : T ⟶ A) :
    ∀ n : ℕ, 1 ≤ n → x ≫ ρ.act (n : O) = x ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [ρ.map_one]
    · rw [Nat.cast_succ, ρ.map_add, ρ.map_one, padd, ← Category.assoc,
        CartesianMonoidalCategory.comp_lift, Category.comp_id, ih hpos, pow_succ, Hom.mul_def]

end Grp

section Weil

lemma weil_one_left (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (y : T ⟶ P.A) (hy : y ^ k = 1) : WeilIs P.A P.L k 1 y 1 := by
  obtain ⟨H1, H2, -, -⟩ := hW S P k T
  obtain ⟨c, hc, -⟩ := H1 1 y (one_pow k) hy
  have hcc : WeilIs P.A P.L k 1 y (c * c) := by simpa using H2 1 1 y c c hc hc
  have huniq := (H1 1 y (one_pow k) hy).unique hc hcc

  have hc1 : c = 1 := mul_left_cancel (huniq.symm.trans (mul_one c).symm)
  rw [← hc1]
  exact hc

lemma weil_pow_eq_one (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  have hpow : ∀ n : ℕ, WeilIs P.A P.L k (x ^ n) y (c ^ n) := by
    intro n
    induction n with
    | zero => simpa using weil_one_left hW P k y hy
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (hW S P k T).2.1 _ _ _ _ _ ih hc
  have h1 := hpow k
  rw [hx] at h1
  exact ((hW S P k T).1 1 y (one_pow k) hy).unique h1 (weil_one_left hW P k y hy)

lemma weil_unique (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c c' : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) (hc' : WeilIs P.A P.L k x y c') : c = c' :=
  ((hW S P k T).1 x y hx hy).unique hc hc'

end Weil

section Gen

open ReciprocityTheory.ChartRestriction.G.DVR TopologicalSpace

lemma top_of_closedPoint {V : Type} [CommRing V] [IsLocalRing V] (U : (Spec (CommRingCat.of V)).Opens)
    (hU : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ U) : U = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  exact (IsLocalRing.specializes_closedPoint (R := V) y).mem_open U.isOpen hU

theorem gen_local {V : Type} [CommRing V] [IsLocalRing V]
    (M : LB (Spec (CommRingCat.of V))) (hM : M.IsLB) : ∃ e : M.Gen, e.IsGen := by

  have hp : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ ⨆ i, M.U i := by
    rw [hM.cover]
    exact TopologicalSpace.Opens.mem_top _
  obtain ⟨i0, hi0⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  have htop : M.U i0 = ⊤ := top_of_closedPoint (M.U i0) hi0
  have hle : ∀ W : (Spec (CommRingCat.of V)).Opens, W ≤ M.U i0 := fun W => by
    rw [htop]
    exact le_top
  have hid : ∀ {W : (Spec (CommRingCat.of V)).Opens} (h0 : W ≤ W) (z : Γ(Spec (CommRingCat.of V), W)ˣ), res h0 z = z := by
    intro W h0 z
    have h1 : homOfLE h0 = 𝟙 W := rfl
    ext
    simp [res, h1]

  refine ⟨⟨fun i => res (le_inf le_rfl (hle _) : M.U i ≤ M.U i ⊓ M.U i0) (M.g i i0)⟩, ?_⟩
  intro i j
  have hc := hM.cocycle i j i0
  have h' : M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j ⊓ M.U i0 := le_inf le_rfl (hle _)
  have hc' := congrArg (fun z => res h' z) hc
  simp only [map_mul, res_res', hid] at hc'
  simp only [res_res']
  exact hc'.symm

theorem gen_local_linComb {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X)
    (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of V) ⟶ X)) (ε : K → ℤ) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen :=
  gen_local _ (by
    first
      | exact linComb_isLB
      | exact linComb_isLB hL
      | exact linComb_isLB (hL := hL)
      | exact linComb_isLB hL φ ε
      | exact linComb_isLB L hL φ ε
      | exact linComb_isLB (L := L) (φ := φ) (ε := ε) hL
      | exact linComb_isLB L φ ε hL)

end Gen

end ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem torus_std (A X : Type) [CommRing A] [Nontrivial A] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Algebra.IsStandardSmoothOfRelativeDimension (Module.finrank ℤ X) A (AddMonoidAlgebra A X) := by
  classical
  let b := Module.finBasis ℤ X
  let f : (Fin (Module.finrank ℤ X) →₀ ℕ) →+ X :=
    b.repr.symm.toLinearMap.toAddMonoidHom.comp (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ))
  have hf : Function.Injective f := b.repr.symm.injective.comp (Finsupp.mapRange_injective _ Nat.cast_zero Nat.cast_injective)
  let P := MvPolynomial (Fin (Module.finrank ℤ X)) A
  let φ : P →ₐ[A] AddMonoidAlgebra A X := AddMonoidAlgebra.mapDomainAlgHom A A f
  have hφ : ∀ m a, φ (MvPolynomial.monomial m a) = AddMonoidAlgebra.single (f m) a := fun m a =>
    AddMonoidAlgebra.mapDomain_single
  let _ : Algebra P (AddMonoidAlgebra A X) := φ.toRingHom.toAlgebra
  have : IsScalarTower A P (AddMonoidAlgebra A X) := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  let one : Fin (Module.finrank ℤ X) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1
  have hr : ∀ n : ℕ, algebraMap P (AddMonoidAlgebra A X) (MvPolynomial.monomial one 1) ^ n =
      AddMonoidAlgebra.single (n • f one) 1 := fun n => by
    show φ _ ^ n = _
    rw [hφ, AddMonoidAlgebra.single_pow, one_pow]
  have : IsLocalization.Away (MvPolynomial.monomial one (1 : A) : P) (AddMonoidAlgebra A X) := by
    refine IsLocalization.Away.mk _ ?_ (fun s => ?_) (fun a c h => ⟨0, by rw [AddMonoidAlgebra.mapDomain_injective hf h]⟩)
    · refine IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-f one) 1) ?_
      show φ _ * _ = _
      rw [hφ, AddMonoidAlgebra.single_mul_single, add_neg_cancel, _root_.one_mul]; rfl
    · induction s using AddMonoidAlgebra.induction_linear with
      | zero => exact ⟨0, 0, by simp⟩
      | add s t hs ht =>
        obtain ⟨n, a, ha⟩ := hs
        obtain ⟨m, c, hc⟩ := ht
        refine ⟨n + m, a * MvPolynomial.monomial one 1 ^ m + c * MvPolynomial.monomial one 1 ^ n, ?_⟩
        rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← ha, ← hc]; ring
      | single x a =>
        let n : ℕ := ∑ i, (b.repr x i).natAbs
        refine ⟨n, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (b.repr x i + n).toNat) a, ?_⟩
        show _ = φ _
        rw [hr, hφ, AddMonoidAlgebra.single_mul_single, _root_.mul_one]
        congr 1
        apply b.repr.injective
        ext i
        have h₁ : (b.repr x i).natAbs ≤ n := Finset.single_le_sum (f := fun i => (b.repr x i).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        simp [f, one]
        omega
  have : Algebra.IsStandardSmooth A P := Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential.2
    ⟨inferInstance, _, KaehlerDifferential.mvPolynomialBasis A _, by rintro _ ⟨i, rfl⟩; exact ⟨MvPolynomial.X i, (KaehlerDifferential.mvPolynomialBasis_apply A _ i).symm⟩⟩
  have : Algebra.IsStandardSmoothOfRelativeDimension (Module.finrank ℤ X) A P :=
    (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth _).2 (by
      rw [rank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis A _), Fintype.card_fin])
  have := Algebra.IsStandardSmoothOfRelativeDimension.localization_away (S := AddMonoidAlgebra A X)
    (MvPolynomial.monomial one (1 : A) : P)
  have h := Algebra.IsStandardSmoothOfRelativeDimension.trans (Module.finrank ℤ X) 0 A P (AddMonoidAlgebra A X)
  rwa [zero_add] at h

theorem torus_dim (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    SmoothOfRelativeDimension (Module.finrank ℤ X) (splitTorus S X).hom := by
  have h : SmoothOfRelativeDimension (Module.finrank ℤ X) (splitTorusAff ZU X).hom :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Module.finrank ℤ X))).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2 (torus_std _ X)))
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) h

theorem dim_unique {X Y : Scheme.{0}} (f : X ⟶ Y) {n m : ℕ} (hn : SmoothOfRelativeDimension n f)
    (hm : SmoothOfRelativeDimension m f) (x : X) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hm.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f hn ⟨U, hU⟩ ⟨V, hV⟩ e
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(X, V)
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1 (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  have h₂ := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).right
    (Localization.Away t) t _ h
  let _ := ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra
  have r₁ := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ n h₁
  have r₂ := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ m h₂
  exact_mod_cast r₁.symm.trans r₂

theorem exists_dim {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (n : ℕ) (W : X.Opens), x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth f x
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  let _ := (f.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := h
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
  have h' : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (f.appLE U V e).hom := ⟨_, _, _, ‹_›, P, rfl⟩
  have : IsAffine U := hU
  have : IsAffine V := hV
  have : SmoothOfRelativeDimension P.dimension (f.resLE U V e) :=
    (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f U V e)).2 h'))
  refine ⟨P.dimension + 0, V, hx, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]; infer_instance

theorem dim_base {X S X' S' : Scheme.{0}} {f : X ⟶ S} {f' : X' ⟶ S'} {a : X' ⟶ X} {b : S' ⟶ S} (h : IsPullback a f' f b)
    {n m : ℕ} {W : X.Opens} (hW : SmoothOfRelativeDimension n (W.ι ≫ f)) (hm : SmoothOfRelativeDimension m f') (x : X')
    (hx : a x ∈ W) : n = m := by
  have h₁ : SmoothOfRelativeDimension n ((a ⁻¹ᵁ W).ι ≫ f') := (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    ((isPullback_morphismRestrict a W).paste_vert h) hW
  have h₂ : SmoothOfRelativeDimension (0 + m) ((a ⁻¹ᵁ W).ι ≫ f') := inferInstance
  exact (dim_unique _ h₁ h₂ ⟨x, hx⟩).trans (zero_add m)

theorem torsor_pullback {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B)
    [IsMonHom q] (h : IsPullback i (toUnit _) q η[B]) : IsPullback ((fst T G ≫ i) * snd T G) (snd T G) q q := by
  have hi : i ≫ q = 1 := h.w
  have : Mono i := h.flip.mono_snd_of_mono
  refine IsPullback.of_isLimit' ⟨by rw [MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul]⟩
    (PullbackCone.IsLimit.mk _ (fun s => lift (h.lift (s.fst * s.snd⁻¹) (toUnit _) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, mul_inv_cancel]; rfl)) s.snd) (fun s => ?_) (fun s => lift_snd _ _)
      (fun s m h₁ h₂ => ?_))
  · rw [MonObj.comp_mul, lift_fst_assoc, h.lift_fst, lift_snd, inv_mul_cancel_right]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, ← cancel_mono i, h.lift_fst, ← h₁, ← h₂, MonObj.comp_mul, mul_inv_cancel_right, Category.assoc]
    · rw [lift_snd, h₂]

theorem dimSplit : DimSplitStatement := by
  intro E _ _ _ H V _ _ _ t P
  have := t.semi.smooth
  obtain ⟨n, W, hW, dW⟩ := exists_dim t.G.hom (eSec t.G (closedPoint V))
  have all : ∀ y : Sp V, eSec t.G y ∈ W := fun y =>
    (congrArg (fun U => y ∈ U) (Scheme.preimage_eq_top_of_closedPoint_mem (eSec t.G) hW)).mpr trivial
  have unit : ∀ {S' : Scheme.{0}} (b : S' ⟶ Sp V) (y : S'),
      pullback.fst t.G.hom b (eSec ((Over.pullback b).obj t.G) y) ∈ W := fun b y =>
    (congrArg (fun g => g y ∈ W) (cubeMapOf (isGrpPullback_pullback t.G b)).e_comm).mpr (all _)

  have g₁ : n = P.A.g := by
    have := P.A.smoothDim
    have : IsIso P.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map P.U.gen.hom))
    have d : SmoothOfRelativeDimension (0 + P.A.g) (pullback.snd t.G.hom (jK V)) := by
      rw [show pullback.snd t.G.hom (jK V) = P.U.gen.hom.left ≫ P.A.A.hom from (Over.w P.U.gen.hom).symm]
      infer_instance
    exact (dim_base (IsPullback.of_hasPullback _ _) dW d _ (unit (jK V) (default : PrimeSpectrum (FractionRing V)))).trans
      (zero_add _)

  let c := P.U.gt 0
  have := c.q_hom
  have := c.i_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  have dT := torus_dim (Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))) P.D.toPre.X
  have : Smooth c.q.left := by
    have := dT.smooth
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((torsor_pullback c.i c.q c.isKernel).map (Over.forget _)).flip ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact c.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  have : Nontrivial (V ⧸ maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal V).ne_top)
  obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  obtain ⟨m, W₁, hW₁, d₁⟩ := exists_dim c.q.left (eSec (thickObj V (maximalIdeal V) 0 t.G) y)
  have g₂ : m = Module.finrank ℤ P.D.toPre.X := dim_base (c.isKernel.map (Over.forget _)) d₁ dT (eSec _ y)
    ((congrArg (fun g => g.left y ∈ W₁) (IsMonHom.one_hom c.i)).mpr hW₁)
  have dB : SmoothOfRelativeDimension P.D.toPre.P.g (thickObj V (maximalIdeal V) 0 P.D.toPre.P.A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      P.D.toPre.P.smoothDim
  have d₂ : SmoothOfRelativeDimension (m + P.D.toPre.P.g) (W₁.ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom) := by
    rw [← Over.w c.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension n ((pullback.fst t.G.hom (thick V (maximalIdeal V) 0) ⁻¹ᵁ W).ι ≫
      (thickObj V (maximalIdeal V) 0 t.G).hom) := (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    ((isPullback_morphismRestrict _ W).paste_vert (IsPullback.of_hasPullback _ _)) dW
  have g₃ : n = m + P.D.toPre.P.g := by
    let W₂ := pullback.fst t.G.hom (thick V (maximalIdeal V) 0) ⁻¹ᵁ W
    have e₁ : SmoothOfRelativeDimension (0 + n) ((W₂ ⊓ W₁).ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W₂ ⊓ W₁ ≤ W₂), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + (m + P.D.toPre.P.g)) ((W₂ ⊓ W₁).ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W₂ ⊓ W₁ ≤ W₁), Category.assoc]; infer_instance
    simpa using dim_unique _ e₁ e₂ ⟨_, unit _ y, hW₁⟩
  rw [← g₁, g₃, g₂]

end ReciprocityTheory.ChartRestriction.G.H1
end
end

