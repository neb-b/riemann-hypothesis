module

public import Mathlib
public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullback

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.TwoTorsionInclusion

private noncomputable abbrev Two (S : Scheme.{0}) : Scheme.{0} := ∐ fun _ : Fin 2 ↦ S

private noncomputable abbrev inc (S : Scheme.{0}) (i : Fin 2) : S ⟶ Two S :=
  Sigma.ι (fun _ : Fin 2 ↦ S) i

private noncomputable abbrev cd (S : Scheme.{0}) : Two S ⟶ S := Sigma.desc fun _ ↦ 𝟙 S

private lemma mem_zero_iff (S : Scheme.{0}) (x : Two S) :
    x ∈ (inc S 0).opensRange ↔ x ∉ (inc S 1).opensRange := by
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk (fun _ : Fin 2 ↦ S)).surjective x
  simp only [sigmaMk_mk, Scheme.Hom.mem_opensRange, inc, sigmaι_eq_iff]
  fin_cases i <;> simp

private lemma isClosed_one (S : Scheme.{0}) : IsClosed ((inc S 1).opensRange : Set (Two S)) := by
  rw [← isOpen_compl_iff]
  have : ((inc S 1).opensRange : Set (Two S))ᶜ = ((inc S 0).opensRange : Set (Two S)) := by
    ext x
    exact (mem_zero_iff S x).symm
  rw [this]
  exact (inc S 0).opensRange.isOpen

private lemma restrict_eq {S X Z : Scheme.{0}} (y : X ⟶ Two S) (i : Fin 2) (j : Z ⟶ X)
    (h : ∀ z, y (j z) ∈ (inc S i).opensRange) : j ≫ y = j ≫ y ≫ cd S ≫ inc S i := by
  have hr : Set.range (j ≫ y).base ⊆ Set.range (inc S i).base := by
    rintro _ ⟨z, rfl⟩
    exact h z
  set L := IsOpenImmersion.lift (inc S i) (j ≫ y) hr
  have e : L ≫ inc S i = j ≫ y := IsOpenImmersion.lift_fac _ _ _
  rw [← reassoc_of% e, ← e]
  simp [inc, cd]

private lemma core {S X : Scheme.{0}} (f : X ⟶ S) (W : X.Opens) (hW : IsClosed (W : Set X)) :
    ∃! y : X ⟶ Two S, y ≫ cd S = f ∧ y ⁻¹ᵁ (inc S 1).opensRange = W := by
  let W' : X.Opens := ⟨(W : Set X)ᶜ, hW.isOpen_compl⟩
  have hc : IsCompl W'.ι.opensRange W.ι.opensRange := by
    simp only [Scheme.Opens.opensRange_ι]
    constructor
    · rw [disjoint_iff, ← SetLike.coe_set_eq]
      ext x
      simp [W']
    · rw [codisjoint_iff, ← SetLike.coe_set_eq]
      ext x
      simp [W']
  obtain ⟨hcol⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl W'.ι W.ι hc
  have ext : ∀ {T : Scheme.{0}} (a b : X ⟶ T), W'.ι ≫ a = W'.ι ≫ b → W.ι ≫ a = W.ι ≫ b → a = b :=
    fun a b h0 h1 ↦ BinaryCofan.IsColimit.hom_ext hcol h0 h1
  have key : ∀ y' : X ⟶ Two S, y' ≫ cd S = f → y' ⁻¹ᵁ (inc S 1).opensRange = W →
      W'.ι ≫ y' = W'.ι ≫ f ≫ inc S 0 ∧ W.ι ≫ y' = W.ι ≫ f ≫ inc S 1 := by
    intro y' h1 h2
    constructor
    · rw [restrict_eq y' 0 W'.ι, reassoc_of% h1]
      intro z
      rw [mem_zero_iff]
      intro hz
      have hm : W'.ι z ∈ y' ⁻¹ᵁ (inc S 1).opensRange := hz
      rw [h2] at hm
      have hz' : z.1 ∉ W := z.2
      exact hz' hm
    · rw [restrict_eq y' 1 W.ι, reassoc_of% h1]
      intro z
      have hm : W.ι z ∈ y' ⁻¹ᵁ (inc S 1).opensRange := by
        rw [h2]
        exact z.2
      exact hm
  obtain ⟨y0, hy0, hy1⟩ := BinaryCofan.IsColimit.desc' hcol (W'.ι ≫ f ≫ inc S 0) (W.ι ≫ f ≫ inc S 1)
  obtain ⟨y, rfl⟩ : ∃ y : X ⟶ Two S, y = y0 := ⟨y0, rfl⟩
  change W'.ι ≫ y = _ at hy0
  change W.ι ≫ y = _ at hy1
  refine ⟨y, ⟨ext (y ≫ cd S) f (by rw [reassoc_of% hy0]; simp [inc, cd])
    (by rw [reassoc_of% hy1]; simp [inc, cd]), ?_⟩, ?_⟩
  · ext x
    by_cases hx : x ∈ W
    · obtain ⟨z, rfl⟩ : ∃ z : W.toScheme, W.ι z = x := ⟨⟨x, hx⟩, rfl⟩
      have e : y (W.ι z) = inc S 1 (f (W.ι z)) := by
        rw [show y (W.ι z) = (W.ι ≫ y) z from rfl, hy1] <;> rfl
      refine iff_of_true ?_ hx
      show y (W.ι z) ∈ (inc S 1).opensRange
      rw [e]
      exact ⟨_, rfl⟩
    · obtain ⟨z, rfl⟩ : ∃ z : W'.toScheme, W'.ι z = x := ⟨⟨x, hx⟩, rfl⟩
      have e : y (W'.ι z) = inc S 0 (f (W'.ι z)) := by
        rw [show y (W'.ι z) = (W'.ι ≫ y) z from rfl, hy0] <;> rfl
      refine iff_of_false ?_ hx
      show y (W'.ι z) ∉ (inc S 1).opensRange
      rw [e, ← mem_zero_iff]
      exact ⟨_, rfl⟩
  · rintro y' ⟨h1, h2⟩
    obtain ⟨k0, k1⟩ := key y' h1 h2
    exact ext _ _ (k0.trans hy0.symm) (k1.trans hy1.symm)

private lemma isIso_fst {S : Scheme.{0}} (T : Over S) : IsIso (fst T (Over.mk (𝟙 S))) := by
  have ht : IsTerminal (Over.mk (𝟙 S)) := Over.mkIdTerminal
  refine ⟨⟨lift (𝟙 T) (ht.from T), ?_, by simp⟩⟩
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · exact ht.hom_ext _ _

end UpperTheory.TwoTorsionInclusion

open UpperTheory.TwoTorsionInclusion in
theorem UpperTheory.exists_clopRep_trivial :
    ∀ (S : Scheme.{0}), ∃ (Y : Over S) (U : (Y ⊗ Over.mk (𝟙 S)).left.Opens), UpperTheory.RepresentationRank.Rep (Over.mk (𝟙 S)) Y U ∧ IsFinite Y.hom ∧ Etale Y.hom := by
  intro S
  refine ⟨Over.mk (cd S), (fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ⁻¹ᵁ (inc S 1).opensRange,
    ⟨(isClosed_one S).preimage (Scheme.Hom.continuous _), ?_⟩,
    (GlobalTheory.FinEt.isSplitOfRank_sigmaDesc S 2).isFinite, (GlobalTheory.FinEt.isSplitOfRank_sigmaDesc S 2).etale⟩
  intro T V hV
  have hiso : IsIso (fst T (Over.mk (𝟙 S))).left := by
    have := isIso_fst T
    exact (inferInstance : IsIso ((Over.forget S).map (fst T (Over.mk (𝟙 S)))))
  set φ := (fst T (Over.mk (𝟙 S))).left with hφ
  have h1 : ∀ x, inv φ (φ x) = x := fun x ↦ by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl
  have h2 : ∀ t, φ (inv φ t) = t := fun t ↦ by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hpre : ∀ (y : T ⟶ Over.mk (cd S)) x,
      x ∈ (y ▷ Over.mk (𝟙 S)).left ⁻¹ᵁ
        ((fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ⁻¹ᵁ (inc S 1).opensRange) ↔
        y.left (φ x) ∈ (inc S 1).opensRange := by
    intro y x
    show (fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ((y ▷ Over.mk (𝟙 S)).left x) ∈
      (inc S 1).opensRange ↔ _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, whiskerRight_fst, Over.comp_left,
      Scheme.Hom.comp_apply]
  let W : T.left.Opens := (inv φ) ⁻¹ᵁ V
  have hW : IsClosed (W : Set T.left) := hV.preimage (Scheme.Hom.continuous _)
  have hiff : ∀ y : T ⟶ Over.mk (cd S), (y ▷ Over.mk (𝟙 S)).left ⁻¹ᵁ
      ((fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ⁻¹ᵁ (inc S 1).opensRange) = V ↔
      y.left ⁻¹ᵁ (inc S 1).opensRange = W := by
    intro y
    constructor
    · intro h
      refine SetLike.ext fun t ↦ ?_
      show y.left t ∈ (inc S 1).opensRange ↔ inv φ t ∈ V
      rw [← h, hpre, h2]
    · intro h
      refine SetLike.ext fun x ↦ ?_
      rw [hpre]
      show φ x ∈ y.left ⁻¹ᵁ (inc S 1).opensRange ↔ x ∈ V
      rw [h]
      show inv φ (φ x) ∈ V ↔ x ∈ V
      rw [h1]
  obtain ⟨y0, ⟨e0, e1⟩, hu⟩ := core T.hom W hW
  refine ⟨Over.homMk y0 e0, (hiff _).2 e1, fun y hy ↦ ?_⟩
  exact Over.OverMorphism.ext (hu y.left ⟨Over.w y, (hiff y).1 hy⟩)
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsGTateIsoTwistOfSimilitude
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen UpperTheory.Lev

namespace UpperTheory.Lev

section Twist

variable {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
  {e : ℕ → Q → Q → kˣ → Prop}

private theorem ev_MN (I : GTateIso G k Q act e) {n : ℕ} (hn : 0 < n) {a b : G.La} (h : MN n a b) :
    I.ev n a = I.ev n b := by
  obtain ⟨c, rfl⟩ := h
  rw [I.add, (I.ker n hn (n • c)).2 ⟨c, rfl⟩, _root_.mul_one]

private theorem zpow_congr_of_dvd {u : kˣ} {n : ℕ} (hu : u ^ n = 1) {a b : ℤ} (h : (n : ℤ) ∣ a - b) :
    u ^ a = u ^ b := by
  obtain ⟨c, hc⟩ := h
  have hab : a = b + n * c := by linarith
  rw [hab, zpow_add, zpow_mul, zpow_natCast, hu, one_zpow, _root_.mul_one]

private theorem prim_zpow {u : kˣ} {n : ℕ} (hu : IsPrimitiveRoot u n) {v : ℤ}
    (hc : IsCoprime v (n : ℤ)) : IsPrimitiveRoot (u ^ v) n := by
  exact hu.zpow_of_gcd_eq_one v (Int.isCoprime_iff_gcd_eq_one.mp hc)

end Twist

end UpperTheory.Lev

theorem UpperTheory.exists_gTateIso_twist_of_similitude :
    ∀ {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
        (I : GTateIso G k Q act e) (g : GSim G),
        ∃ I' : GTateIso G k Q act e, ∀ n, 0 < n → ∀ x, I'.ev n x = I.ev n (g.f n x) := by
  intro G k _ Q _ act e I g
  have hφadd : ∀ n, 0 < n → ∀ x y, I.ev n (g.f n (x + y)) = I.ev n (g.f n x) * I.ev n (g.f n y) :=
    fun n hn x y => by rw [Lev.ev_MN I hn ((g.sim n hn).add x y), I.add]
  have hφpow : ∀ n, 0 < n → ∀ (j : ℕ) y, I.ev n (g.f n (j • y)) = I.ev n (g.f n y) ^ j := by
    intro n hn j y
    induction j with
    | zero =>
      rw [zero_smul, pow_zero]
      have h0 := hφadd n hn 0 0
      rw [add_zero] at h0
      exact (mul_eq_left.mp h0.symm)
    | succ j ih => rw [succ_nsmul, hφadd n hn, ih, pow_succ]
  refine ⟨⟨fun n => I.ζ n ^ g.ν n, ?_, ?_, fun n x => if n = 0 then I.ev 0 x else I.ev n (g.f n x),
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n hn
    exact Lev.prim_zpow (I.ζ_prim n hn) (g.sim n hn).cop
  · intro n m hn hm
    rw [← zpow_natCast, ← zpow_mul, mul_comm (g.ν _), zpow_mul, zpow_natCast, I.ζ_pow n m hn hm]
    exact Lev.zpow_congr_of_dvd (I.ζ_prim n hn).pow_eq_one (g.νtower n m hn hm)
  · intro n x y
    by_cases hn : n = 0
    · simp only [hn, if_true, I.add]
    · simp only [hn, if_false]
      exact hφadd n (Nat.pos_of_ne_zero hn) x y
  · intro n b x
    by_cases hn : n = 0
    · simp only [hn, if_true, I.lin]
    · simp only [hn, if_false]
      rw [Lev.ev_MN I (Nat.pos_of_ne_zero hn) ((g.sim n (Nat.pos_of_ne_zero hn)).lin b x), I.lin]
  · intro n hn x
    simp only [hn.ne', if_false]
    constructor
    · intro h1
      obtain ⟨y, hy⟩ := (I.ker n hn _).mp h1
      obtain ⟨c, hc⟩ := (g.sim n hn).inj x ⟨y, by rw [hy, zero_add]⟩
      exact ⟨c, by rw [hc, zero_add]⟩
    · rintro ⟨y, rfl⟩
      rw [hφpow n hn]
      exact (I.onto n hn _).mpr ⟨_, rfl⟩
  · intro n hn q
    simp only [hn.ne', if_false]
    rw [I.onto n hn]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := (g.sim n hn).surj z
      exact ⟨x, Lev.ev_MN I hn hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  · intro n m hn hm x
    simp only [(Nat.mul_pos hn hm).ne', hn.ne', if_false]
    rw [I.tower n m hn hm, Lev.ev_MN I hn (g.tower n m hn hm x)]
  · intro n hn x y
    simp only [hn.ne', if_false]
    have h := I.isom n hn (g.f n x) (g.f n y)
    have hd := ((g.sim n hn).isom x y)
    rw [Lev.zpow_congr_of_dvd (I.ζ_prim n hn).pow_eq_one hd] at h
    rw [← zpow_mul]
    exact h
  · intro n hn x
    simp only [hn.ne', if_false]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLevelObjPullbackOfCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen UpperTheory.Lev

noncomputable section

namespace UpperTheory.LevPull

open GlobalTheory.PELU
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (pφ pφ₂ isSquare pφ₂_fst pφ₂_snd isGrpPullback gen_refl)
open GlobalTheory.HTPullEvery (lift_pφ₂ map_left_pφ push_map)

section Act

variable {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A]

private def pullAct (a : OActN O A) : OActN O ((Over.pullback f).obj A) where
  act c := (Over.pullback f).map (a.act c)
  hom c := by have := a.hom c; infer_instance
  one := by simp [a.one]
  mul b c := by simp [a.mul]
  add b c := by
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f A) _ ?_
    rw [map_mul]
    simp only [push_map, a.add, MonObj.comp_mul]

private theorem pullAct_sq (a : OActN O A) (c : O) :
    ((pullAct f a).act c).left ≫ pφ f A = pφ f A ≫ (a.act c).left :=
  map_left_pφ f A (a.act c)

private theorem push_pullAct (a : OActN O A) {T : Over S'} (u : T ⟶ (Over.pullback f).obj A) (c : O) :
    pushHom (isGrpPullback f A) T (u ≫ (pullAct f a).act c) = pushHom (isGrpPullback f A) T u ≫ a.act c := by
  apply Over.OverMorphism.ext
  change (u ≫ (pullAct f a).act c).left ≫ pφ f A = (u.left ≫ pφ f A) ≫ (a.act c).left
  simp [pullAct_sq]

end Act

section Tan

variable {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A]

private theorem tanScal_iff (a : OActN O A) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S')
    (e : (epsPtR x ⟶ (Over.pullback f).obj A) ≃* (epsPtR (x ≫ f) ⟶ A))
    (he : ∀ v, (e v).left = v.left ≫ pφ f A) (c : O) (r : R') (v : epsPtR x ⟶ (Over.pullback f).obj A) :
    IsTanScal (pullAct f a) x c r v ↔ IsTanScal a (x ≫ f) c r (e v) := by
  have cart := isGrpPullback f A
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv cart (Over.mk x) (x ≫ f) rfl
  have unit : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ (Over.pullback f).obj A).left ≫ pφ f A := by
    rw [← he₀, map_one]
  have retr : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have scale : spMap (epsScaleR r) ≫ spMap (algebraMap R' (DualNumber R')) =
      spMap (algebraMap R' (DualNumber R')) := by
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have down : e (v ≫ (pullAct f a).act c) = e v ≫ a.act c := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, he, Category.assoc, pullAct_sq]
  have wv : v.left ≫ ((Over.pullback f).obj A).hom = spMap (algebraMap R' (DualNumber R')) ≫ x := Over.w v
  have wc : (v ≫ (pullAct f a).act c).left ≫ ((Over.pullback f).obj A).hom =
      spMap (algebraMap R' (DualNumber R')) ≫ x := Over.w _
  have w1 : (1 : Over.mk x ⟶ (Over.pullback f).obj A).left ≫ ((Over.pullback f).obj A).hom = x := Over.w _
  unfold IsTanScal
  rw [← down, he, he, unit]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by rw [← Category.assoc, h₁], by rw [h₂, Category.assoc]⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨cart.1.hom_ext (by simpa using h₁) ?_, cart.1.hom_ext (by simpa using h₂) ?_⟩
    · rw [Category.assoc, wv, w1, ← Category.assoc, retr, Category.id_comp]
    · rw [wc, Category.assoc, wv, ← Category.assoc, scale]

end Tan

section Tate

variable {G : GDatum}

private theorem tate_along {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : G.O → Q → Q} {act' : G.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (I : GTateIso G k Q act e) (r : Q ≃* Q') (hact : ∀ c q, r (act c q) = act' c (r q))
    (hisom : ∀ n, 0 < n → ∀ x y, e' n (r (I.ev n x)) (r (I.ev n y)) (I.ζ n ^ (2 * G.EF x y))) :
    ∃ I' : GTateIso G k Q' act' e', ∀ n x, I'.ev n x = r (I.ev n x) :=
  ⟨{ ζ := I.ζ
     ζ_prim := I.ζ_prim
     ζ_pow := I.ζ_pow
     ev := fun n x => r (I.ev n x)
     add := fun n x y => by rw [I.add, map_mul]
     lin := fun n c x => by rw [I.lin, hact]
     ker := fun n hn x => by rw [map_eq_one_iff r r.injective, I.ker n hn]
     onto := fun n hn q => by
       have : q ^ n = 1 ↔ (r.symm q) ^ n = 1 := by
         rw [← map_pow, map_eq_one_iff r.symm r.symm.injective]
       rw [this, I.onto n hn]
       exact exists_congr fun x => by rw [MulEquiv.eq_symm_apply]
     tower := fun n m hn hm x => by rw [← map_pow, I.tower n m hn hm]
     isom := hisom }, fun _ _ => rfl⟩

end Tate

section Obj

variable {S S' : Scheme.{0}} (f : S' ⟶ S) {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R}
  {N : ℕ} {s : S ⟶ Sp R}

private theorem geom_of_pull (o : GObj gb N s) (s' : S' ⟶ Sp R) (hs : f ≫ s = s') (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S') (β : R →+* k) (hx : x ≫ s' = spMap β) :
    ∃ I : GTateIso G k (Over.mk x ⟶ (Over.pullback f).obj o.A) (fun c g => g ≫ (pullAct f o.act).act c)
        (fun n g g' z => Out.WeilIs ((Over.pullback f).obj o.A)
          ((o.P.pull (pφ₂ f o.A)).pull (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 _)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ GlobalTheory.SiegelPull.secPull (isGrpPullback f o.A) (o.eta y) = I.ev N y := by
  have cart := isGrpPullback f o.A
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv cart (Over.mk x) (x ≫ f) rfl
  obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hs, hx])
  have back : ∀ q, (e.symm q).left ≫ pφ f o.A = q.left := fun q => by rw [← he, e.apply_symm_apply]
  have hact : ∀ c q, e.symm (q ≫ o.act.act c) = e.symm q ≫ (pullAct f o.act).act c := by
    intro c q
    rw [MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, pullAct_sq, ← Category.assoc, back]
  have hisom : ∀ n : ℕ, 0 < n → ∀ a a', Out.WeilIs ((Over.pullback f).obj o.A)
      ((o.P.pull (pφ₂ f o.A)).pull (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 _)).left) (n : ℤ)
      (e.symm (I.ev n a)) (e.symm (I.ev n a')) (unitOn (I.ζ n ^ (2 * G.EF a a'))) := fun n hn a a' =>
    (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A _ f (pφ f o.A) _ _ (pull_isLB o.isLB _)
      (pull_isLB (pull_isLB o.isLB _) _) cart
      (GlobalTheory.SiegelPull.diag_iso (isSquare f o.A) (gen_refl _ (pull_isLB o.isLB _))) (Over.mk x) n _ _
      (I.ev n a) (I.ev n a') _ (back _).symm (back _).symm).2 (I.isom n hn a a')
  obtain ⟨I', hI'⟩ := tate_along (Q' := Over.mk x ⟶ (Over.pullback f).obj o.A)
    (act' := fun c g => g ≫ (pullAct f o.act).act c)
    (e' := fun n g g' z => Out.WeilIs ((Over.pullback f).obj o.A)
      ((o.P.pull (pφ₂ f o.A)).pull (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 _)).left) n g g' (unitOn z))
    I e.symm hact hisom
  refine ⟨I', fun y => ?_⟩
  rw [hI', MulEquiv.eq_symm_apply, ← hI y]
  refine Eq.trans ?_ (GlobalTheory.SiegelPull.push_secPull cart (o.eta y) (Over.mk x))
  apply Over.OverMorphism.ext
  rw [he]
  rfl

private def baseChange (o : GObj gb N s) (s' : S' ⟶ Sp R) (hs : f ≫ s = s') : GObj gb N s' where
  A := (Over.pullback f).obj o.A
  ab :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (pullback.snd _ _); infer_instance }
  act := pullAct f o.act
  P := o.P.pull (pφ₂ f o.A)
  isLB := pull_isLB o.isLB (pφ₂ f o.A)
  rig₁ := by
    obtain ⟨t, ht⟩ := o.rig₁
    exact gen_chartPull (chartPullLinComb o.P _ _ _ _ (pφ f o.A)
      fun _ => Pdiv.PullbackComparison.lift_one_id f o.A) t ht
  rig₂ := by
    obtain ⟨t, ht⟩ := o.rig₂
    exact gen_chartPull (chartPullLinComb o.P _ _ _ _ (pφ f o.A)
      fun _ => Pdiv.PullbackComparison.lift_id_one f o.A) t ht
  symm := LBIso.chartPull (chartPullPull o.P _ _ rfl)
    (chartPullLinComb o.P _ _ _ _ (pφ₂ f o.A) fun _ => Pdiv.PullbackComparison.lift_swap f o.A) o.symm
  ample := (GlobalTheory.pol_pull S S' o.A _ f (pφ f o.A) _ _ (pull_isLB o.isLB _) (pull_isLB (pull_isLB o.isLB _) _) o.ab
    (isGrpPullback f o.A) (GlobalTheory.SiegelPull.diag_iso (isSquare f o.A) (gen_refl _ (pull_isLB o.isLB _)))).2.1 o.ample
  rosati c := by
    have h₁ : (fst ((Over.pullback f).obj o.A) _ ≫ (pullAct f o.act).act c).left ≫ pφ f o.A =
        pφ₂ f o.A ≫ (fst o.A o.A ≫ o.act.act c).left := by
      simp only [Over.comp_left, Category.assoc, pullAct_sq]
      rw [← Category.assoc, ← pφ₂_fst, Category.assoc]
    have h₂ : (snd ((Over.pullback f).obj o.A) _ ≫ (pullAct f o.act).act (G.star c).unop).left ≫ pφ f o.A =
        pφ₂ f o.A ≫ (snd o.A o.A ≫ o.act.act (G.star c).unop).left := by
      simp only [Over.comp_left, Category.assoc, pullAct_sq]
      rw [← Category.assoc, ← pφ₂_snd, Category.assoc]
    exact LBIso.chartPull
      (chartPullLinComb o.P _ _ _ _ (pφ₂ f o.A) fun _ =>
        lift_pφ₂ f o.A _ _ _ _ h₁ (pφ₂_snd f o.A).symm)
      (chartPullLinComb o.P _ _ _ _ (pφ₂ f o.A) fun _ =>
        lift_pφ₂ f o.A _ _ _ _ (pφ₂_fst f o.A).symm h₂)
      (o.rosati c)
  lie R' _ β x hx v hv := by
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback f o.A) (epsPtR x)
      (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f) (Category.assoc _ _ _).symm
    obtain ⟨w, hw, hsum⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc, hs, hx]) (e v)
      ((tanScal_iff f o.act x e he _ _ v).1 hv)
    refine ⟨fun i => e.symm (w i), fun i c => ?_, ?_⟩
    · rw [tanScal_iff f o.act x e he, e.apply_symm_apply]
      exact hw i c
    · rw [← e.symm_apply_apply v, hsum, map_list_prod, List.map_ofFn]
      rfl
  lieRank k _ _ x β hx i :=
    (GlobalTheory.LiePull.lieMult_pull (𝓞 G.F) S S' o.A _ f (pφ f o.A) (actF o.act) (actF (pullAct f o.act))
      (isGrpPullback f o.A) (fun c => pullAct_sq f o.act _) k x _ G.m).2
      (o.lieRank k (x ≫ f) β (by rw [Category.assoc, hs, hx]) i)
  eta y := GlobalTheory.SiegelPull.secPull (isGrpPullback f o.A) (o.eta y)
  eta_add y y' := by
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) _ ?_
    simp only [map_mul, GlobalTheory.SiegelPull.push_secPull', o.eta_add, MonObj.comp_mul]
  eta_lin c y := by
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) _ ?_
    simp only [push_pullAct, GlobalTheory.SiegelPull.push_secPull', o.eta_lin, Category.assoc]
  eta_ker y := by
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) _ ?_
    simp only [map_one, GlobalTheory.SiegelPull.push_secPull', o.eta_ker, MonObj.comp_one]
  geom k _ _ x β hx := geom_of_pull f o s' hs k x β hx

private def baseChangeMap (o : GObj gb N s) (s' : S' ⟶ Sp R) (hs : f ≫ s = s') :
    GObjMap (baseChange f o s' hs) o f where
  φ := pφ f o.A
  φ₂ := pφ₂ f o.A
  cart := isGrpPullback f o.A
  sq := isSquare f o.A
  act c := pullAct_sq f o.act c
  pol := gen_refl _ (pull_isLB o.isLB _)
  eta y := GlobalTheory.SiegelPull.secPull_left (isGrpPullback f o.A) _

end Obj

end UpperTheory.LevPull

theorem UpperTheory.exists_levelObj_pullback_of_charZero :
    ∀ {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R}
        (s' : S' ⟶ Sp R) (f : S' ⟶ S), f ≫ s = s' → ∀ o : GObj gb N s, ∃ o' : GObj gb N s', Nonempty (GObjMap o' o f) :=
  fun s' f hs o => ⟨_, ⟨UpperTheory.LevPull.baseChangeMap f o s' hs⟩⟩
end
end

