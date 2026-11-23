module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFreeOfFiniteProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
noncomputable section

namespace GlobalTheory.WeilOpenLocus

open GlobalTheory.CechPic GlobalTheory.DiagPairing GlobalTheory.LevCover

attribute [local instance] Over.cartesianMonoidalCategory

theorem biadd_noeth {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] (hG : Out.GlobalFnsSt)
    (hA : IsAbelianScheme A) (P : LB (G2 A).left) (hP : P.IsLB)
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) (T : Over S) (x x' y : T ⟶ A) :
    (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen,
      t.IsGen) ∧
    ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen,
      t.IsGen := by
  constructor
  · have := GlobalTheory.CubeNoeth.triv_add (𝟙 (A ⊗ A)) hG hA hP (by rw [Category.comp_id]; exact h₁)
      (by rw [Category.comp_id]; exact h₂) x x' y
    simp only [Category.comp_id] at this
    exact this
  · have sw : ∀ {T : Over S} (a b : T ⟶ A), lift a b ≫ lift (snd A A) (fst A A) = lift b a := fun a b => by
      rw [comp_lift, lift_snd, lift_fst]
    have := GlobalTheory.CubeNoeth.triv_add (lift (snd A A) (fst A A)) hG hA hP (by rw [sw]; exact h₂)
      (by rw [sw]; exact h₁) x x' y
    simp only [sw] at this
    exact this

theorem exists_weilIs_root {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (P : LB (G2 A).left) (hP : P.IsLB)
    (r₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (N : ℕ) (hN : 0 < N) {T : Over S} {x y : T ⟶ A}
    (hx : x ^ N = 1) (hy : y ^ N = 1) :
    ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N x y c₀ := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  let pc := fun {T : Over S} (a b : T ⟶ A) => pull (lift a b).left (cls P hP)
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc (x * x') y = pc x y + pc x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (biadd_noeth hG hA P hP r₁ r₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      dsimp only [pc]
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc x (y * y') = pc x y + pc x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (biadd_noeth hG hA P hP r₁ r₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      dsimp only [pc]
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : T ⟶ A, z ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (Out.overRes V), θ.pt = Out.overResι V ≫ z :=
    fun z hz p => by
      let x := Out.overResι ⊤ ≫ z
      have hx : x ^ N = 1 := by dsimp [x]; rw [← MonObj.comp_pow, hz, MonObj.comp_one]
      have powleft : ∀ {U : Over S} (a b : U ⟶ A) (k : ℕ), pc (a ^ k) b = k • pc a b := by
        intro U a b k
        have one : pc (1 : U ⟶ A) b = 0 := by
          have h := hB U 1 1 b
          rwa [_root_.mul_one, left_eq_add] at h
        induction k with
        | zero => rw [pow_zero, one, zero_smul]
        | succ k ih => rw [pow_succ, hB, ih, succ_nsmul]
      have powright : ∀ {U : Over S} (a b : U ⟶ A) (k : ℕ), pc a (b ^ k) = k • pc a b := by
        intro U a b k
        have one : pc a (1 : U ⟶ A) = 0 := by
          have h := hB' U a 1 1
          rwa [_root_.mul_one, left_eq_add] at h
        induction k with
        | zero => rw [pow_zero, one, zero_smul]
        | succ k ih => rw [pow_succ, hB', ih, succ_nsmul]
      have e : ∀ g : (Out.overRes (⊤ : T.left.Opens)) ⊗ A ⟶ A, pull g.left (cls _ hD) = pc g g := fun g => by
        rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
      have ha : (fst (Out.overRes (⊤ : T.left.Opens)) A ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
      have h1 : N • pc (fst (Out.overRes (⊤ : T.left.Opens)) A ≫ x) (fst (Out.overRes (⊤ : T.left.Opens)) A ≫ x) = 0 := by
        rw [← powleft, ha]
        have h := hB _ 1 1 (fst (Out.overRes (⊤ : T.left.Opens)) A ≫ x)
        rwa [_root_.mul_one, left_eq_add] at h
      have h2 : N • pc (fst (Out.overRes (⊤ : T.left.Opens)) A ≫ x) (snd (Out.overRes (⊤ : T.left.Opens)) A) = 0 := by
        rw [← powleft, ha]
        have h := hB _ 1 1 (snd (Out.overRes (⊤ : T.left.Opens)) A)
        rwa [_root_.mul_one, left_eq_add] at h
      have h3 : N • pc (snd (Out.overRes (⊤ : T.left.Opens)) A) (fst (Out.overRes (⊤ : T.left.Opens)) A ≫ x) = 0 := by
        rw [← powright, ha]
        have h := hB' _ (snd (Out.overRes (⊤ : T.left.Opens)) A) 1 1
        rwa [_root_.mul_one, left_eq_add] at h
      obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB A (P.pull (lift (𝟙 A) (𝟙 A)).left) N x), t.IsGen := by
        refine (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).1 ?_
        rw [cls_linComb hD, Fin.sum_univ_two]
        show (N : ℤ) • pull (snd (Out.overRes (⊤ : T.left.Opens)) A).left (cls _ hD) + (-(N : ℤ)) • pull ((fst (Out.overRes (⊤ : T.left.Opens)) A ≫ x) * snd (Out.overRes (⊤ : T.left.Opens)) A).left (cls _ hD) = 0
        rw [e, e, hB, hB', hB']
        simp only [natCast_zsmul, neg_smul, smul_add, h1, h2, h3]
        abel
      exact ⟨⊤, trivial, ⟨x, t, ht⟩, rfl⟩
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.CommutatorPairing.exists_weilIs hG hA hD (lifts x hx) (lifts y hy)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.CommutatorPairing.exists_weilIs hG hA hD (lifts 1 (one_pow N)) (lifts y hy)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := GlobalTheory.CommutatorPairing.weilIs_unique hG hA hD h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (x ^ (m + 1)) y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ c₀ (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD ih hc₀
  have hp := pw (N - 1)
  rw [Nat.sub_add_cancel hN, hx] at hp
  exact ⟨c₀, GlobalTheory.CommutatorPairing.weilIs_unique hG hA hD hp (e₁' ▸ hc₁), hc₀⟩

theorem weil_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (β₀ : cycAway M →+* k) (z₀ : kˣ), x₀ ≫ t = spMap β₀ → (z₀ : k) = β₀ (zetaAway M) → (∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x₀) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z₀ ^ (2 * omegaStd a b)))) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S) (β : cycAway M →+* k') (z : k'ˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k') = β (zetaAway M) → ∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b))) := by
  intro S _ M t G _ _ P h lev hA hP r₁ r₂ _hsym hM3 _hodd ladd ltors k _ _ x₀ β₀ z₀ hx₀ hz₀ Hx₀
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  have hM0 : M ≠ 0 := by omega
  have hMpos : 0 < M := by omega
  have hMS : IsUnit (M : Γ(S, ⊤)) := by
    have := (isUnit_natCast hM0).map (fnOn t)
    rwa [map_natCast] at this
  let ζu : (cycAway M)ˣ := (cycBase hM0).ζ
  have hζv : (ζu : cycAway M) = zetaAway M := rfl
  have hzeta : zetaAway M ^ M = 1 := Subtype.ext (Complex.isPrimitiveRoot_exp M hM0).pow_eq_one
  have hζu : ζu ^ M = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hζv, Units.val_one]; exact hzeta)
  have hζM : ∀ (k : Type) [Field k] (β : cycAway M →+* k), Units.map β.toMonoidHom ζu ^ M = 1 := fun k _ β => by
    rw [← map_pow, hζu, map_one]
  let P2 : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ℤ) → HkClopen.GeoCond S := fun a c k _ _ x =>
    ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t = spMap β → (z : k) = β (zetaAway M) →
      Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x) ≫ lev a)
        (toUnit (Over.mk x) ≫ lev c) (unitOn (z ^ (2 * omegaStd a c)))
  have locPair : ∀ a c, HkClopen.Loc (P2 a c) := fun a c => by
    obtain ⟨v, hv, hW⟩ := exists_weilIs_root hA P hP r₁ r₂ M hMpos (ltors a) (ltors c)
    refine (GlobalTheory.loc_units_eq S M v (Units.map (fnOn t).toMonoidHom (ζu ^ (2 * omegaStd a c))) hMS hv
      fun k _ _ g => ?_).congr fun k _ _ g => ?_
    · obtain ⟨β, hβ⟩ := exists_spMap (g ≫ t)
      rw [map_fnOn _ g β hβ, ← GlobalTheory.SiegCover.unitOn_pow', map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hζM, one_zpow]
      exact GlobalTheory.SiegCover.unitOn_one'
    · have hW' := GlobalTheory.CommPairing.weilIs_pull hG hA hD (toUnit (Over.mk g)) hW
      have hgl : (toUnit (Over.mk g)).left = g := by simpa using Over.w (toUnit (Over.mk g))
      rw [hgl] at hW'
      obtain ⟨β, hβ⟩ := exists_spMap (g ≫ t)
      have hu := map_fnOn _ g β hβ (ζu ^ (2 * omegaStd a c))
      rw [show Units.map β.toMonoidHom (ζu ^ (2 * omegaStd a c)) =
        Units.map β.toMonoidHom ζu ^ (2 * omegaStd a c) from map_zpow _ _ _] at hu
      have hzβ : ((Units.map β.toMonoidHom ζu : kˣ) : k) = β (zetaAway M) := by
        rw [Units.coe_map]; rfl
      constructor
      · intro E β' z hβ' hz
        obtain rfl : β = β' := spMap_inj' (hβ.symm.trans hβ')
        obtain rfl : z = Units.map β.toMonoidHom ζu := Units.ext (hz.trans hzβ.symm)
        rw [← hu, ← E]
        exact hW'
      · intro H
        exact GlobalTheory.CommutatorPairing.weilIs_unique hG hA hD hW' (hu ▸ H β _ hβ hzβ)
  have e1 : ∀ a c, lev (a + M • c) = lev a := fun a c => by
    rw [ladd, add_map_nsmul ladd, ltors, _root_.mul_one]
  have inv : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ S) (a a' c₁ c₂ : Fin h ⊕ Fin h → ℤ),
      P2 a a' k g → P2 (a + M • c₁) (a' + M • c₂) k g := by
    intro k _ _ g a a' c₁ c₂ H β z hβ hz
    have hzM : z ^ M = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hz, ← map_pow, hzeta, map_one, Units.val_one])
    obtain ⟨m, hm⟩ : ∃ m : ℤ, omegaStd (a + M • c₁) (a' + M • c₂) = omegaStd a a' + M * m :=
      ⟨_, GlobalTheory.SiegCover.omegaStd_add_nsmul M a a' c₁ c₂⟩
    have hz' : z ^ (2 * omegaStd (a + M • c₁) (a' + M • c₂)) = z ^ (2 * omegaStd a a') := by
      rw [hm, mul_add, zpow_add, show (2 : ℤ) * (M * m) = M * (2 * m) by ring, zpow_mul _ (M : ℤ), zpow_natCast,
        hzM, one_zpow, _root_.mul_one]
    show Out.WeilIs _ _ _ _ _ _
    rw [e1, e1, hz']
    exact H β z hβ hz
  obtain ⟨κ, hκ, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) hMpos
  haveI := hκ
  let r : κ → (Fin h ⊕ Fin h → ℤ) := Function.invFun q
  have localization₂ : HkClopen.Loc (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ S) => ∀ a a', P2 a a' k g) := by
    refine (HkClopen.Loc.all (I₀ := κ × κ) (P := fun i => P2 (r i.1) (r i.2)) fun i => locPair _ _).congr
      fun k _ _ g => ⟨fun H a a' => ?_, fun H i => H _ _⟩
    obtain ⟨c₁, e₁⟩ := hq (r (q a)) a (Function.invFun_eq ⟨a, rfl⟩)
    obtain ⟨c₂, e₂⟩ := hq (r (q a')) a' (Function.invFun_eq ⟨a', rfl⟩)
    rw [e₁, e₂]
    exact inv k g _ _ c₁ c₂ (H (q a, q a'))
  obtain ⟨V, hV, HV⟩ := localization₂
  refine ⟨⟨V, hV.isOpen⟩, ?_, fun k' _ _ x β z hxW hβ hz a b => ?_⟩
  · refine (HkClopen.range_subset_iff x₀ V).2 ((HV k x₀).2 fun a b β z hβ hz => ?_)
    obtain rfl : β₀ = β := spMap_inj' (hx₀.symm.trans hβ)
    obtain rfl : z₀ = z := Units.ext (hz₀.trans hz.symm)
    exact Hx₀ a b
  · exact (HV k' x).1 ((HkClopen.range_subset_iff x V).1 hxW) a b β z hβ hz

end GlobalTheory.WeilOpenLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightRecursiveValueWellDefined
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.StepVal

variable {k : Type} [CommRing k]

theorem isometric_pull_pull' {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {s : Z ⟶ Sp k} (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = s) (c : Z ⟶ X)
    (hc : c ≫ p = s) (e : g ≫ f = c) : ((L.pull f hf).pull g hg).Isometric (L.pull c hc) := by
  subst e
  have R := L.refines_pull_pull f hf g hg hc
  exact HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy =>
    ((R.φ σ c y hy).trans (add_zero _)).symm

theorem recVal_congr {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {e : ℕ}
    {h h' : Y → ℝ} (H : ∀ z : Y, Order.coheight z = 1 → h z = h' z) (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : recVal h L M hr = recVal h' L M hr := by
  unfold recVal
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  · rw [H z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)]

theorem dim_of_genericPoint {X Y : Scheme.{0}} [IsIntegral Y] {p : X ⟶ Sp k} (hp : IsAmb p) (i : Y ⟶ X)
    [IsClosedImmersion i] {x : X} {d : ℕ} (hx : HasDim x d) (hg : i (genericPoint Y) = x) :
    topologicalKrullDim Y = d := by
  have H := (_root_.GlobalTheory.MixHt.hasDim_basic k X p hp).2.2.2.2
  rw [← H.2 Y d, ← H.1 Y i (genericPoint Y) d, hg]
  exact hx

theorem recVal_indep_section (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) (hY : topologicalKrullDim Y = (m + 1 : ℕ)) {T}
    (hT : IsMix q m T) (L : Fin m → HermLB q) (N : HermLB q) {r r' : N.B.ι → Y.functionFieldˣ} (hr : IsRatSec N.B r)
    (hr' : IsRatSec N.B r') : recVal (T m L) L N hr = recVal (T m L) L N hr' := by
  cases m with
  | zero =>
    have H : ∀ z : Y, Order.coheight z = 1 → T 0 L z = Real.log (Nat.card (Y.residueField z)) := fun z hz =>
      hT.zero L z (((_root_.GlobalTheory.MixHt.dimOne k Y q hq 0 hY).1 z).1 hz)
    rw [recVal_congr H, recVal_congr H]
    exact _root_.GlobalTheory.CurveIndep.main k Y q hq hY N L r hr r' hr'
  | succ e => exact _root_.GlobalTheory.MixHt.recVal_indep_sec hInt hRec k Y q hq e hY T hT N L r hr r' hr'

theorem recVal_indep (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) (hY : topologicalKrullDim Y = (m + 1 : ℕ)) {T}
    (hT : IsMix q m T) (L L' : Fin m → HermLB q) (hL : ∀ a, (L a).Isometric (L' a)) (M M' : HermLB q)
    (hM : M.Isometric M') {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) {r' : M'.B.ι → Y.functionFieldˣ}
    (hr' : IsRatSec M'.B r') : recVal (T m L) L M hr = recVal (T m L') L' M' hr' := by
  have H := _root_.GlobalTheory.MixHt.recVal_iso_symm hInt k Y q hq m hY T hT M r hr
  obtain ⟨r₃, hr₃, e₃⟩ := H.2.2 L' M' hM
  rw [H.1 L L' hL, ← e₃]
  exact recVal_indep_section hInt hRec m hq hY hT L' M' hr₃ hr'

end GlobalTheory.MixHt.StepVal

namespace GlobalTheory.MixHt.StepVal

variable {k : Type} [CommRing k]

theorem recVal_eq_of_same (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ)
    (hall : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T)
    {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsAmb p) {T} (hT : IsMix p m T) {x : X} (hx : HasDim x (m + 1))
    (M : HermLB p) (L : Fin m → HermLB p) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k}
    (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q) (hg : i (genericPoint Y) = x)
    (M' M'' : HermLB q) (L' L'' : Fin m → HermLB q) (hM' : (M.pull i hi).Isometric M')
    (hM'' : (M.pull i hi).Isometric M'') (hL' : ∀ a, ((L a).pull i hi).Isometric (L' a))
    (hL'' : ∀ a, ((L a).pull i hi).Isometric (L'' a)) {r' : M'.B.ι → Y.functionFieldˣ} (hr' : IsRatSec M'.B r')
    {r'' : M''.B.ι → Y.functionFieldˣ} (hr'' : IsRatSec M''.B r'') :
    recVal (fun z => T m L (i z)) L' M' hr' = recVal (fun z => T m L (i z)) L'' M'' hr'' := by
  have hq : IsAmb q := by subst hi; exact hp.sub i
  have hY := dim_of_genericPoint hp i hx hg
  obtain ⟨T', hT'⟩ := hall k Y q hq
  have E : ∀ N : Fin m → HermLB q, (∀ a, ((L a).pull i hi).Isometric (N a)) → ∀ z : Y, Order.coheight z = 1 →
      T m L (i z) = T' m N z := fun N hN z hz =>
    _root_.GlobalTheory.MixHt.eq_of_isMix k X Y p q hp i hi m m T T' hT hT' m le_rfl le_rfl L N hN z
      (((_root_.GlobalTheory.MixHt.dimOne k Y q hq m hY).1 z).1 hz)
  rw [recVal_congr (E L' hL'), recVal_congr (E L'' hL'')]
  exact recVal_indep hInt hRec m hq hY hT' L' L'' (fun a => (hL' a).symm.trans (hL'' a)) M' M''
    (hM'.symm.trans hM'') hr' hr''

theorem recVal_eq_of_two (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ)
    (hall : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T)
    {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsAmb p) {T} (hT : IsMix p m T) {x : X} (hx : HasDim x (m + 1))
    (M : HermLB p) (L : Fin m → HermLB p)
    {Y₁ : Scheme.{0}} [IsIntegral Y₁] [IsLocallyNoetherian Y₁] {q₁ : Y₁ ⟶ Sp k}
    (i₁ : Y₁ ⟶ X) [IsClosedImmersion i₁] (hi₁ : i₁ ≫ p = q₁) (hg₁ : i₁ (genericPoint Y₁) = x)
    (M₁ : HermLB q₁) (L₁ : Fin m → HermLB q₁) (hM₁ : (M.pull i₁ hi₁).Isometric M₁)
    (hL₁ : ∀ a, ((L a).pull i₁ hi₁).Isometric (L₁ a)) {r₁ : M₁.B.ι → Y₁.functionFieldˣ} (hr₁ : IsRatSec M₁.B r₁)
    {Y₂ : Scheme.{0}} [IsIntegral Y₂] [IsLocallyNoetherian Y₂] {q₂ : Y₂ ⟶ Sp k}
    (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ p = q₂) (hg₂ : i₂ (genericPoint Y₂) = x)
    (M₂ : HermLB q₂) (L₂ : Fin m → HermLB q₂) (hM₂ : (M.pull i₂ hi₂).Isometric M₂)
    (hL₂ : ∀ a, ((L a).pull i₂ hi₂).Isometric (L₂ a)) {r₂ : M₂.B.ι → Y₂.functionFieldˣ} (hr₂ : IsRatSec M₂.B r₂) :
    recVal (fun z => T m L (i₁ z)) L₁ M₁ hr₁ = recVal (fun z => T m L (i₂ z)) L₂ M₂ hr₂ := by
  obtain ⟨g, hiso, hgi, hη⟩ := _root_.GlobalTheory.iso_of_closedImmersion_genericPoint_eq X Y₁ Y₂ i₁ i₂ (hg₁.trans hg₂.symm)
  have hgq : g ≫ q₁ = q₂ := by rw [← hi₁, ← hi₂, ← Category.assoc, hgi]
  have hq₁ : IsAmb q₁ := by subst hi₁; exact hp.sub i₁
  have hq₂ : IsAmb q₂ := by subst hi₂; exact hp.sub i₂
  have hY₁ := dim_of_genericPoint hp i₁ hx hg₁
  have tr := _root_.GlobalTheory.MixHt.transport k Y₁ Y₂ q₁ q₂ hq₁ hq₂ g hgq hη hiso m hY₁ (fun z => T m L (i₁ z)) L₁ M₁ r₁ hr₁
  rw [← tr]
  have hfun : (fun w => T m L (i₁ (g w))) = fun w => T m L (i₂ w) := by
    funext w
    rw [← hgi]
    simp
  rw [hfun]
  refine recVal_eq_of_same hInt hRec m hall hp hT hx M L i₂ hi₂ hg₂ _ _ _ _ ?_ hM₂ (fun a => ?_) hL₂ _ hr₂
  · exact (isometric_pull_pull' M i₁ hi₁ g hgq i₂ hi₂ hgi).symm.trans (hM₁.pull g hgq)
  · exact (isometric_pull_pull' (L a) i₁ hi₁ g hgq i₂ hi₂ hgi).symm.trans ((hL₁ a).pull g hgq)

theorem step_val : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ T,
    IsMix p m T → ∀ (x : X), HasDim x (m + 1) → ∀ (M : HermLB p) (L : Fin m → HermLB p), ∃ v : ℝ,
    ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = q), i (genericPoint Y) = x → ∀ (M' : HermLB q) (L' : Fin m → HermLB q),
    (M.pull i hi).Isometric M' → (∀ a, ((L a).pull i hi).Isometric (L' a)) →
    ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr := by
  intro hInt hRec m hall k _ X p hp T hT x hx M L
  classical
  by_cases H : ∃ v : ℝ, ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (q : Y ⟶ Sp k)
      (i : Y ⟶ X) (_ : IsClosedImmersion i) (hi : i ≫ p = q) (_ : i (genericPoint Y) = x) (M' : HermLB q)
      (L' : Fin m → HermLB q) (_ : (M.pull i hi).Isometric M') (_ : ∀ a, ((L a).pull i hi).Isometric (L' a))
      (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr
  · obtain ⟨v, Y₁, _, _, q₁, i₁, _, hi₁, hg₁, M₁, L₁, hM₁, hL₁, r₁, hr₁, rfl⟩ := H
    exact ⟨_, fun Y _ _ q i _ hi hg M' L' hM hL r hr =>
      recVal_eq_of_two hInt hRec m hall hp hT hx M L i₁ hi₁ hg₁ M₁ L₁ hM₁ hL₁ hr₁ i hi hg M' L' hM hL hr⟩
  · exact ⟨0, fun Y _ _ q i _ hi hg M' L' hM hL r hr =>
      absurd ⟨_, Y, ‹_›, ‹_›, q, i, ‹_›, hi, hg, M', L', hM, hL, r, hr, rfl⟩ H⟩

end GlobalTheory.MixHt.StepVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootLiftsFromResidueCompleteLocal
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.PolRootComplete

theorem root_given {S T : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (G2 A).left} (hP : P.IsLB) {t : T ⟶ S}
    (h : Root A P t) {B : Over T} [GrpObj B] [IsCommMonObj B] {β : B.left ⟶ A.left}
    {β₂ : (G2 B).left ⟶ (G2 A).left} (hβ : IsGrpPullback B A t β) (hsq : IsSquare β β₂) :
    ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) (P.pull β₂) := by
  obtain ⟨C, _, _, c, c₂, hc, hsqc, L, hL, H⟩ := h
  let φ : B.left ⟶ C.left := hc.1.lift β B.hom hβ.1.w
  have hφc : φ ≫ c = β := hc.1.lift_fst _ _ _
  have hφw : φ ≫ C.hom = B.hom ≫ 𝟙 T := (hc.1.lift_snd _ _ _).trans (Category.comp_id _).symm
  have hφ : IsGrpPullback B C (𝟙 T) φ := hc.cancel (hβ.congr (Category.id_comp t).symm hφc.symm) hφw
  obtain ⟨φ₂, hφ₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hφw
  have e : φ₂ ≫ c₂ = β₂ :=
    GlobalTheory.ZM.SiegPull.isSquare_unique (GlobalTheory.ZM.SiegPull.isSquare_comp hφ₂ hsqc) hsq hφc
  have hLφ : (L.pull φ).IsLB := pull_isLB hL φ
  refine ⟨L.pull φ, hLφ, ?_⟩
  have h1 : LBIso (abelian₂ B (L.pull φ)) ((abelian₂ C L).pull φ₂) :=
    GlobalTheory.ZM.SiegPull.lbIso_lam_pull hφ (GlobalTheory.GtBaseChange.lbIso_refl hLφ) hφ₂
  have h2 : LBIso ((abelian₂ C L).pull φ₂) (P.pull (φ₂ ≫ c₂)) := GlobalTheory.ZM.SiegPull.lbIso_pull_comp H φ₂
  rw [e] at h2
  exact LBIso.trans (LB.isLB_linComb hLφ _ _) (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB hP _) h1 h2

theorem root_of_closedFibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (P : LB (G2 B).left) (hP : P.IsLB)
    (g1 : ∃ u : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen)
    (g2 : ∃ u : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen)
    (gamp : RelAmple B (P.pull (lift (𝟙 B) (𝟙 B)).left))
    (h0 : ∃ L₀ : LB (thickObj R (maximalIdeal R) 0 B).left, L₀.IsLB ∧
      ∀ b₂ : (G2 (thickObj R (maximalIdeal R) 0 B)).left ⟶ (G2 B).left,
        IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) 0)) b₂ →
          LBIso (abelian₂ (thickObj R (maximalIdeal R) 0 B) L₀) (P.pull b₂)) :
    ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) P := by
  let Q : ∀ e, LB (thickObj R (maximalIdeal R) e B).left → Prop := fun e L => L.IsLB ∧
    ∀ b₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 B).left,
      IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) b₂ →
        LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) (P.pull b₂)
  have step : ∀ e (L : {L // Q e L}), ∃ L' : {L' // Q (e + 1) L'},
      LBIso (L'.1.pull (thickMap R (maximalIdeal R) e B)) L.1 := fun e L => by
    obtain ⟨L', h1', h2', h3'⟩ := _root_.GlobalTheory.TowerStep.step R B hB P hP g1 g2 e L.1 L.2.1 L.2.2
    exact ⟨⟨L', h1', h2'⟩, h3'⟩
  choose F hF using step
  obtain ⟨L₀, hL₀⟩ := h0
  let N : ∀ e, {L // Q e L} := fun e => Nat.rec ⟨L₀, hL₀⟩ (fun e L => F e L) e
  have hN : ∀ e, LBIso ((N (e + 1)).1.pull (thickMap R (maximalIdeal R) e B)) (N e).1 := fun e => hF e (N e)
  have hproj : GlobalTheory.AbLaw.IsProjBy B.hom := GlobalTheory.WtTower.isProjBy_of_relAmple B (pull_isLB hP _) gamp
  obtain ⟨M, hM, HM⟩ := GlobalTheory.LBAlgComplete.exists_lineBundle_of_reductions GlobalTheory.formalAlgebraisation R
    (maximalIdeal R) hR B hproj (fun e => thickObj R (maximalIdeal R) e B)
    (fun e => thickMap R (maximalIdeal R) e B) (fun e => pullback.fst B.hom (thick R (maximalIdeal R) e))
    (fun e => (isGrpPullback_pullback B (thick R (maximalIdeal R) e)).1)
    (fun e => (pullback.lift_fst _ _ _).trans (Category.comp_id _)) (fun e => (N e).1) (fun e => (N e).2.1)
    (fun e => (hN e).symm)
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R 0
  obtain ⟨b₂, hb₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare (isGrpPullback_pullback B (thick R (maximalIdeal R) 0)).1.w
  exact ⟨M, hM, _root_.GlobalTheory.PolRigid.lbIso_lam_of_quotient R (R ⧸ maximalIdeal R ^ (0 + 1)) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective B (thickObj R (maximalIdeal R) 0 B) (pullback.fst _ _) b₂ hB
    (isGrpPullback_pullback B _) hb₂ P hP g1 g2 M (N 0).1 hM (N 0).2.1 (HM 0).symm ((N 0).2.2 b₂ hb₂)⟩

theorem root_of_residue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ t : Sp R ⟶ S, Root A P (spMap (residue R) ≫ t) → Root A P t := by
  intro S A _ _ hA P hP h1 h2 hamp R _ _ _ hR t hroot
  obtain ⟨B, _, β, hβ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A t
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hβ
  haveI : IsCommMonObj B := hB.comm
  obtain ⟨β₂, hsq⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hβ.1.w
  obtain ⟨g1, g2⟩ := _root_.GlobalTheory.AxisTriv.axes_pull S (Sp R) A P hP h1 h2 t B β β₂ hβ hsq
  have gamp := _root_.GlobalTheory.DiagAmpleBC.relAmple_diag_pull S (Sp R) A hA P hP hamp t B β β₂ hβ.1 hsq
  have le : maximalIdeal R ≤ maximalIdeal R ^ (0 + 1) := by rw [zero_add, pow_one]
  have ethick : thick R (maximalIdeal R) 0 =
      spMap (Ideal.Quotient.factor le) ≫ spMap (residue R) := by
    simp only [thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hres : Root A P (thick R (maximalIdeal R) 0 ≫ t) := by
    rw [ethick, Category.assoc]
    exact hroot.comp hA _
  have hY := isGrpPullback_pullback B (thick R (maximalIdeal R) 0)
  obtain ⟨b₂, hb₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hY.1.w
  obtain ⟨L₀, hL₀, H₀⟩ := root_given hP hres (hY.comp hβ) (GlobalTheory.ZM.SiegPull.isSquare_comp hb₂ hsq)
  obtain ⟨L, hL, HL⟩ := root_of_closedFibre R hR B hB (P.pull β₂) (pull_isLB hP _) g1 g2 gamp
    ⟨L₀, hL₀, fun b₂' hb₂' => by
      have e : b₂' = b₂ := GlobalTheory.ZM.SiegPull.isSquare_unique hb₂' hb₂ rfl
      subst e
      exact LBIso.trans (LB.isLB_linComb hL₀ _ _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H₀
        (GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.GtBaseChange.lbIso_refl (pull_isLB hP β₂)) b₂').symm⟩
  exact ⟨B, inferInstance, inferInstance, β, β₂, hβ, hsq, L, hL, HL⟩

end GlobalTheory.PolRootComplete
end
end

