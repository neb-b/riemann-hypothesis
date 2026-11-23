module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NormalSchemeHeightOneStalkDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem normal_scheme_height_one_stalk_dvr : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], IsNormalScheme X → ∀ p : X, ringKrullDim (X.presheaf.stalk p) = 1 → ∃ _ : IsDomain (X.presheaf.stalk p), IsDiscreteValuationRing (X.presheaf.stalk p) := by
  intro X _ hn p hd
  obtain ⟨h1, h2⟩ := hn p
  refine ⟨h1, ?_⟩
  have hnf : ¬ IsField (X.presheaf.stalk p) := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hd
    exact zero_ne_one hd
  have hk : Ring.KrullDimLE 1 (X.presheaf.stalk p) := Ring.krullDimLE_iff.2 (by rw [hd]; rfl)
  have hd1 : Ring.DimensionLEOne (X.presheaf.stalk p) :=
    ⟨fun hne hp => Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hk _ hne hp⟩
  have hdd : IsDedekindDomain (X.presheaf.stalk p) := {}
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk p) hnf).out 3 1).1 hdd

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TorsionAlongGroupPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tors_push {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : U ⟶ S') (b : U ⟶ S) (hb : a ≫ f = b) :
    ∃ π : (Over.mk a ⟶ G') →* (Over.mk b ⟶ G), Function.Bijective π ∧ ∀ x, (π x).left = x.left ≫ φ := by
  subst hb
  have hw : ∀ x : Over.mk a ⟶ G', (x.left ≫ φ) ≫ G.hom = a ≫ f := by
    intro x
    have hx : x.left ≫ G'.hom = a := Over.w x
    rw [Category.assoc, h.1.w, ← Category.assoc, hx]
  let F : (Over.mk a ⟶ G') → (Over.mk (a ≫ f) ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (hw x)
  have hF : ∀ x, (F x).left = x.left ≫ φ := fun x => rfl
  have hmul : ∀ x y, F (x * y) = F x * F y := by
    intro x y
    apply Over.OverMorphism.ext
    rw [hF]
    exact (h.2 (Over.mk a) x y (F x) (F y) (hF x) (hF y)).symm
  refine ⟨MonoidHom.mk' F hmul, ⟨?_, ?_⟩, hF⟩
  · intro x y hxy
    apply Over.OverMorphism.ext
    have e1 : (F x).left = (F y).left := congrArg (fun g => Over.Hom.left g) hxy
    rw [hF, hF] at e1
    apply h.1.hom_ext e1
    rw [Over.w x, Over.w y]
  · intro g
    have hg : g.left ≫ G.hom = a ≫ f := Over.w g
    refine ⟨Over.homMk (h.1.lift g.left a hg) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    show (h.1.lift g.left a hg) ≫ φ = g.left
    exact h.1.lift_fst _ _ _

theorem tors_iff {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T) {X : Scheme.{0}}
    {x : Sp R ⟶ X} {G : Over X} [GrpObj G] {G₀ : Over (Sp R)} [GrpObj G₀] {ψ : G₀.left ⟶ G.left} (N : ℕ)
    (h : IsGrpPullback G₀ G x ψ) (i₀ : Γ.G.left ⟶ G₀.left) (hi : i₀ ≫ G₀.hom = Γ.G.hom) :
    Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ ↔ Γ.IsTorsionAlong G x N (i₀ ≫ ψ) := by
  have cancel : ∀ {W : Scheme.{0}} (u v : W ⟶ G₀.left), u ≫ ψ = v ≫ ψ → u ≫ G₀.hom = v ≫ G₀.hom → u = v :=
    fun u v e1 e2 => h.1.hom_ext e1 e2
  have base : ∀ (Y : Over (Sp R)) (y : Y ⟶ Γ.G), (y.left ≫ i₀) ≫ G₀.hom = Y.hom := by
    intro Y y
    rw [Category.assoc, hi]
    exact Over.w y
  have pushY : ∀ (Y : Over (Sp R)), ∃ π : (Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀) →* (Over.mk (Y.hom ≫ x) ⟶ G),
      Function.Bijective π ∧ ∀ g, (π g).left = g.left ≫ ψ := by
    intro Y
    exact tors_push h (Y.hom ≫ 𝟙 _) (Y.hom ≫ x) (by simp)
  have w1 : ∀ (Y : Over (Sp R)) (g : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀), g.left ≫ G₀.hom = Y.hom := by
    intro Y g
    have := Over.w g
    simpa using this
  constructor
  · intro t
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, h.1.w, ← Category.assoc, hi]
    · intro Y y z y₀ z₀ hy hz
      obtain ⟨π, -, hπ⟩ := pushY Y
      let y₁ : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀ := Over.homMk (y.left ≫ i₀) (by simpa using base Y y)
      let z₁ : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀ := Over.homMk (z.left ≫ i₀) (by simpa using base Y z)
      have ey : π y₁ = y₀ := by
        apply Over.OverMorphism.ext
        rw [hπ, hy]
        show (y.left ≫ i₀) ≫ ψ = _
        rw [Category.assoc]
      have ez : π z₁ = z₀ := by
        apply Over.OverMorphism.ext
        rw [hπ, hz]
        show (z.left ≫ i₀) ≫ ψ = _
        rw [Category.assoc]
      rw [← ey, ← ez, ← map_mul, hπ, t.mul Y y z y₁ z₁ rfl rfl, Category.assoc]
    · intro Y y z e
      apply t.inj Y y z
      apply cancel
      · simpa only [Category.assoc] using e
      · rw [base Y y, base Y z]
    · intro Y g
      obtain ⟨π, ⟨hinj, hsurj⟩, hπ⟩ := pushY Y
      obtain ⟨g₁, rfl⟩ := hsurj g
      rw [← map_pow, ← map_one π, hinj.eq_iff, t.kernel Y g₁, hπ]
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y, by rw [← hy, Category.assoc]⟩
      · rintro ⟨y, hy⟩
        refine ⟨y, cancel _ _ (by rw [Category.assoc, hy]) ?_⟩
        rw [base Y y, w1 Y g₁]
  · intro t
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hi, Category.comp_id]
    · intro Y y z y₀ z₀ hy hz
      obtain ⟨π, -, hπ⟩ := pushY Y
      have m := t.mul Y y z (π y₀) (π z₀) (by rw [hπ, hy, Category.assoc]) (by rw [hπ, hz, Category.assoc])
      rw [← map_mul, hπ] at m
      apply cancel
      · rw [m, Category.assoc]
      · rw [w1 Y, base Y]
    · intro Y y z e
      apply t.inj Y y z
      simp only [← Category.assoc, e]
    · intro Y g₁
      obtain ⟨π, ⟨hinj, -⟩, hπ⟩ := pushY Y
      rw [← hinj.eq_iff, map_pow, map_one, t.kernel Y (π g₁), hπ]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨y, cancel _ _ (by rw [Category.assoc, hy]) ?_⟩
        rw [base Y y, w1 Y g₁]
      · rintro ⟨y, hy⟩
        exact ⟨y, by rw [← hy, Category.assoc]⟩

theorem isTorsionAlong_iff_of_isGrpPullback : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (N : ℕ), IsGrpPullback G₀ G x ψ → (∀ i : Γ.G.left ⟶ G.left, Γ.IsTorsionAlong G x N i → ∃ i₀ : Γ.G.left ⟶ G₀.left, i₀ ≫ ψ = i ∧ Γ.IsTorsionAlong G₀ (𝟙 _) N i₀) ∧ ∀ i₀ : Γ.G.left ⟶ G₀.left, Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ → Γ.IsTorsionAlong G x N (i₀ ≫ ψ) := by
  intro R _ _ T _ Γ X x G _ G₀ _ ψ N h
  refine ⟨?_, ?_⟩
  · intro i t
    have w : i ≫ G.hom = Γ.G.hom ≫ x := t.isOver
    refine ⟨h.1.lift i Γ.G.hom w, h.1.lift_fst _ _ _, ?_⟩
    have e := (tors_iff Γ N h (h.1.lift i Γ.G.hom w) (h.1.lift_snd _ _ _)).2
    rw [h.1.lift_fst] at e
    exact e t
  · intro i₀ t
    have hi : i₀ ≫ G₀.hom = Γ.G.hom := by
      have := t.isOver
      simpa using this
    exact (tors_iff Γ N h i₀ hi).1 t

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwLiemult
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

private theorem isLieEigen_twistAct_iff {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct O G) (s : O ≃+* O) {k : Type} [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (v : epsPt t ⟶ G) :
    IsLieEigen (twistAct act s) t (τ.comp s.toRingHom) v ↔ IsLieEigen act t τ v := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun a => ?_⟩
    have := h1 (s.symm a)
    simpa [twistAct] using this
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun a => ?_⟩
    simpa [twistAct] using h1 (s a)

theorem tw_liemult : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] (act : OAct O G) (s : O ≃+* O) (k : Type) [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ), LieMult (twistAct act s) t (τ.comp s.toRingHom) n ↔ LieMult act t τ n := by
  intro O _ S G _ act s k _ t τ n
  simp only [LieMult, isLieEigen_twistAct_iff]

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwMb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

private theorem fix_rt_lemma {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) : g.s H.rt = H.rt := by
  apply RingOfIntegers.ext
  rw [HostAut.s, RingOfIntegers.mapRingEquiv_apply]
  exact g.fix

private theorem fix_gen_lemma_2 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) : g.s H.w0 = H.w0 ∧ g.s (H.bar H.w0) = H.bar H.w0 := by
  have hr := fix_rt_lemma g
  have hbr : g.s (H.bar H.rt) = H.bar H.rt := by
    have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by
      rw [← map_pow, H.rt_sq, map_neg, map_natCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · rw [h, hr]
    · rw [h, map_neg, hr]
  have two_ne : (2 : 𝓞 E) ≠ 0 := two_ne_zero
  constructor
  · apply mul_left_cancel₀ two_ne
    have h := congrArg g.s H.two_weight_eq_one_add_root
    rw [map_mul, map_ofNat, map_add (f := _), map_one, hr] at h
    rw [h, H.two_weight_eq_one_add_root]
  · apply mul_left_cancel₀ two_ne
    have h := congrArg (fun x => g.s (H.bar x)) H.two_weight_eq_one_add_root
    simp only [map_mul, map_ofNat, map_add (f := _), map_one] at h
    rw [h, hbr]
    have h2 := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_ofNat, map_add (f := _), map_one] at h2
    exact h2.symm

private theorem fix_adj_lemma_3 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) (a : 𝓞 E) (ha : a ∈ Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))) : g.s a = a ∧ g.s (H.bar a) = H.bar a := by
  obtain ⟨h1, h2⟩ := fix_gen_lemma_2 g
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨h1, h2⟩
  | algebraMap r =>
    simp
  | add x y _ _ hx hy =>
    simp only [map_add (f := _), hx.1, hy.1, hx.2, hy.2]
    exact ⟨trivial, trivial⟩
  | mul x y _ _ hx hy =>
    simp only [map_mul, hx.1, hy.1, hx.2, hy.2]
    exact ⟨trivial, trivial⟩

theorem tw_mb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (g : HostAut H), l.Mb.map (g.s : 𝓞 E →+* 𝓞 E) = l.Mb ∧ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)).map (g.s : 𝓞 E →+* 𝓞 E) = l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  intro E _ _ _ H l g
  set S : Set (𝓞 E) := {a : 𝓞 E | a ∈ l.Mb ∧ a ∈ Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))} with hSdef
  have hS : l.Mb = Ideal.span S := l.fromK
  constructor
  · rw [hS, Ideal.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [RingEquiv.coe_toRingHom]
      rw [(fix_adj_lemma_3 g y hy.2).1]
      exact hy
    · intro hx
      exact ⟨x, hx, by simp only [RingEquiv.coe_toRingHom]; exact (fix_adj_lemma_3 g x hx.2).1⟩
  · rw [hS, Ideal.map_span, Ideal.map_span, Set.image_image]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp only [RingEquiv.coe_toRingHom]
      exact ((fix_adj_lemma_3 g y hy.2).2).symm
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp only [RingEquiv.coe_toRingHom]
      exact (fix_adj_lemma_3 g y hy.2).2

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwSub
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_sub : ∀ (O : Type) [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L] (f : L →ₗ[O] TwMod s L) (I : Ideal O), I.map (s : O →+* O) ≤ I → ∀ x ∈ I • (⊤ : Submodule O L), (show L from f x) ∈ I • (⊤ : Submodule O L) := by
  intro O _ s L _ _ f I hI x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    have hsa : s a ∈ I := hI (Ideal.mem_map_of_mem (s : O →+* O) ha)
    have key : (show L from f (a • y)) = s a • (show L from f y) := f.map_smul a y
    rw [key]
    exact Submodule.smul_mem_smul hsa Submodule.mem_top
  · intro y z hy hz
    have key : (show L from f (y + z)) = (show L from f y) + (show L from f z) := f.map_add y z
    rw [key]
    exact Submodule.add_mem _ hy hz

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwTate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (a : TwIso D g) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : TateIso D k Q act e), ∃ J : TateIso D k Q (fun c y => act (g.s c) y) e, J.ζ = I.ζ ∧ ∀ n x, J.ev n x = I.ev n (a.a n x) := by
  intro E _ _ _ H D g a k _ Q _ act e I
  have ev_nsmul : ∀ (n : ℕ), 0 < n → ∀ y : D.La, I.ev n (n • y) = 1 := fun n hn y =>
    (I.ker n hn (n • y)).mpr ⟨y, rfl⟩
  have ev_split : ∀ (n : ℕ), 0 < n → ∀ (c : D.La) (f : TwMod g.s D.La),
      I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) = I.ev n (a.a n c) := by
    intro n hn c f
    have h1 : I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) = I.ev n (a.a n c) * I.ev n (n • (f : D.La)) :=
      I.add n _ _
    have h0 : I.ev n (n • (f : D.La)) = 1 := ev_nsmul n hn f
    exact h1.trans ((congrArg (fun q => I.ev n (a.a n c) * q) h0).trans (_root_.mul_one _))
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow,
            ev := fun n x => I.ev n (a.a n x),
            add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }, rfl, fun _ _ => rfl⟩
  · intro n x y
    rw [map_add (f := _)]
    exact I.add n _ _
  · intro n c x
    rw [map_smul]
    exact I.lin n (g.s c) (a.a n x)
  · intro n hn x
    exact (I.ker n hn (a.a n x)).trans (a.inj n hn x)
  · intro n hn x
    refine (I.onto n hn x).trans ⟨?_, ?_⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨c, f, hb⟩ := a.surj n hn b
      refine ⟨c, ?_⟩
      have h3 : I.ev n b = I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) := by
        rw [hb]
      exact (ev_split n hn c f).symm.trans h3.symm
    · rintro ⟨c, rfl⟩
      exact ⟨_, rfl⟩
  · intro n m hn hm x
    obtain ⟨f, hf⟩ := a.compat n m hn hm x
    have h4 : I.ev (n * m) (a.a (n * m) x) ^ m = I.ev n (a.a (n * m) x) := I.tower n m hn hm _
    have h5 : I.ev n (a.a (n * m) x) = I.ev n (((a.a n x + n • f : TwMod g.s D.La)) : D.La) := by
      rw [hf]
    exact h4.trans (h5.trans (ev_split n hn x f))
  · intro n hn x y
    have h := I.isom n hn (a.a n x) (a.a n y)
    obtain ⟨t, ht⟩ := a.isom n hn x y
    have hpow : I.ζ n ^ n = 1 := (I.ζ_prim n hn).pow_eq_one
    have heq : I.ζ n ^ (D.EF (a.a n x : D.La)) (a.a n y : D.La) = I.ζ n ^ (D.EF x) y := by
      have h2 : (D.EF (a.a n x : D.La)) (a.a n y : D.La) = (D.EF x) y + (n : ℤ) * t := by
        have : (twForm D g ((a.a n) x)) ((a.a n) y) = (D.EF (a.a n x : D.La)) (a.a n y : D.La) := rfl
        rw [← this]
        linarith
      rw [h2, zpow_add, zpow_mul, zpow_natCast, hpow, one_zpow, _root_.mul_one]
    show e n (I.ev n (a.a n x)) (I.ev n (a.a n y)) (I.ζ n ^ (D.EF x) y)
    rw [← heq]
    exact h

end PositivityTheory.UnitarySelfGeneration
end

