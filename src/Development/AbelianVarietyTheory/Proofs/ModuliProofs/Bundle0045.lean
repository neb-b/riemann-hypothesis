module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.coefficientField_integers_dedekind_fractionField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l), IsDedFrac (algebraMap (𝓞 c.F) c.F) ∧ Algebra.FiniteType ℤ (𝓞 c.F) ∧ (∀ A : ℕ, A ∣ l.A → ∃ b : RZ H 1 A →+* 𝓞 c.F, IsInc (RZ H 1 A).subtype (c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)) b) ∧ ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → IsDedFrac (c.V W).subtype ∧ (∀ n : ℕ, n.Coprime p → IsUnit (n : c.V W)) ∧ ∀ S A : ℕ, S.Coprime p → 0 < A → zeta A ∈ c.F → ∃ b : RZ H S A →+* c.V W, IsInc (RZ H S A).subtype (c.F.val.toRingHom.comp (c.V W).subtype) b := by
  first | exact @GlobalTheory.CoeffRings.coeff_isDedFrac | exact GlobalTheory.CoeffRings.coeff_isDedFrac | (intros; apply GlobalTheory.CoeffRings.coeff_isDedFrac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompPowEqOneOfPullbackHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomExt

theorem comp_pow_eq_one_of_pullback_hom {X T Z : Scheme.{0}} (g : T ⟶ X) {G G' Γ : Over X}
    [GrpObj G] [GrpObj G'] (F : (Over.pullback g).obj G ⟶ (Over.pullback g).obj G') [IsMonHom F]
    (p : Γ ⟶ G) (q : Γ ⟶ G') (c : Z ⟶ Γ.left) (s : Z ⟶ pullback G.hom g)
    (h₁ : s ≫ pullback.fst G.hom g = c ≫ p.left)
    (h₂ : s ≫ F.left ≫ pullback.fst G'.hom g = c ≫ q.left) (n : ℕ)
    (h : c ≫ (p ^ n).left = c ≫ (1 : Γ ⟶ G).left) :
    c ≫ (q ^ n).left = c ≫ (1 : Γ ⟶ G').left := by

  let pc : Over.mk (c ≫ Γ.hom) ⟶ Γ := Over.homMk c
  let ps : Over.mk (s ≫ pullback.snd G.hom g) ⟶ (Over.pullback g).obj G := Over.homMk s
  have ht : (Over.mk (s ≫ pullback.snd G.hom g)).hom ≫ g = c ≫ Γ.hom := by
    simp only [Over.mk_hom, Category.assoc, ← pullback.condition, reassoc_of% h₁, Over.w]
  have hp : GlobalTheory.TorsionLift.ptsEquiv g G _ _ ht ps = pc ≫ p := by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.TorsionLift.ptsEquiv_left]
    simpa [ps, pc] using h₁
  have hq : GlobalTheory.TorsionLift.ptsEquiv g G' _ _ ht (ps ≫ F) = pc ≫ q := by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.TorsionLift.ptsEquiv_left]
    simpa [ps, pc] using h₂
  have h1 : (1 : Over.mk (c ≫ Γ.hom) ⟶ G) = pc ≫ 1 := (MonObj.comp_one pc).symm
  have hpn : (pc ≫ p) ^ n = 1 := by
    rw [← MonObj.comp_pow, h1]
    apply Over.OverMorphism.ext
    exact h
  have hps : ps ^ n = 1 := by
    apply (GlobalTheory.TorsionLift.ptsEquiv g G _ _ ht).injective
    rw [map_pow, hp, hpn, map_one]
  have hqn : (pc ≫ q) ^ n = 1 := by
    rw [← hq, ← map_pow, ← MonObj.pow_comp, hps, MonObj.one_comp, map_one]
  have key : pc ≫ q ^ n = pc ≫ 1 := by
    rw [MonObj.comp_pow, hqn, MonObj.comp_one]
  exact congrArg (fun x => Over.Hom.left x) key

theorem exists_iso_pullback_pullback {X T Z : Scheme.{0}} (p : Z ⟶ T) (f : T ⟶ X) (r : Z ⟶ X)
    (h : p ≫ f = r) (G : Over X) [GrpObj G] :
    ∃ e : (Over.pullback r).obj G ≅ (Over.pullback p).obj ((Over.pullback f).obj G),
      IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst (pullback.snd G.hom f) p ≫ pullback.fst G.hom f =
        pullback.fst G.hom r := by
  subst h
  refine ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCompIso p f G, inferInstance, ?_⟩
  have key := congrArg (fun x => Over.Hom.left x)
    (conjugateEquiv_counit (Over.mapPullbackAdj (p ≫ f))
      ((Over.mapPullbackAdj p).comp (Over.mapPullbackAdj f)) (Over.mapComp p f).symm.hom G)
  have e : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCompIso p f G).hom.left =
      ((conjugateEquiv (Over.mapPullbackAdj (p ≫ f))
        ((Over.mapPullbackAdj p).comp (Over.mapPullbackAdj f)) (Over.mapComp p f).symm.hom).app
          G).left := rfl
  rw [e]
  simpa [Adjunction.comp_counit_app] using key

private lemma pullback_map_left_comp_fst {S S' : Scheme.{0}} (φ : S' ⟶ S) {A B : Over S} (F : A ⟶ B) :
    ((Over.pullback φ).map F).left ≫ pullback.fst B.hom φ = pullback.fst A.hom φ ≫ F.left := by
  simp

theorem exists_hom_along_dvr
    (H : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    {X U : Scheme.{0}} (j : U ⟶ X) {G G' : Over X} [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom f]
    (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
    [Algebra T K] [IsFractionRing T K] (a : Sp T ⟶ G.left) (c : Sp K ⟶ pullback G.hom j)
    (hc : c ≫ pullback.fst G.hom j = spMap (algebraMap T K) ≫ a) :
    ∃ (F : (Over.pullback (a ≫ G.hom)).obj G ⟶ (Over.pullback (a ≫ G.hom)).obj G')
      (s : Sp T ⟶ pullback G.hom (a ≫ G.hom)), IsMonHom F ∧
      s ≫ pullback.fst G.hom (a ≫ G.hom) = a ∧ s ≫ pullback.snd G.hom (a ≫ G.hom) = 𝟙 _ ∧
      spMap (algebraMap T K) ≫ s ≫ F.left ≫ pullback.fst G'.hom (a ≫ G.hom) =
        c ≫ f.left ≫ pullback.fst G'.hom j := by
  have huj : (c ≫ pullback.snd G.hom j) ≫ j = spMap (algebraMap T K) ≫ (a ≫ G.hom) := by
    rw [Category.assoc, ← pullback.condition, reassoc_of% hc]
  obtain ⟨e₁, he₁, hf₁⟩ := exists_iso_pullback_pullback (c ≫ pullback.snd G.hom j) j _ huj G
  obtain ⟨e₁', he₁', hf₁'⟩ := exists_iso_pullback_pullback (c ≫ pullback.snd G.hom j) j _ huj G'
  obtain ⟨e₂, he₂, hf₂⟩ :=
    exists_iso_pullback_pullback (spMap (algebraMap T K)) (a ≫ G.hom) _ rfl G
  obtain ⟨e₂', he₂', hf₂'⟩ :=
    exists_iso_pullback_pullback (spMap (algebraMap T K)) (a ≫ G.hom) _ rfl G'
  let fK := e₂.inv ≫ e₁.hom ≫ (Over.pullback (c ≫ pullback.snd G.hom j)).map f ≫ e₁'.inv ≫ e₂'.hom
  have hfK : IsMonHom fK := inferInstance
  obtain ⟨F, ⟨hF, hFK⟩, -⟩ := H T K ((Over.pullback (a ≫ G.hom)).obj G)
    ((Over.pullback (a ≫ G.hom)).obj G')
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (a ≫ G.hom) G hG)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (a ≫ G.hom) G' hG') fK hfK
  have hs : a ≫ G.hom = 𝟙 _ ≫ a ≫ G.hom := (Category.id_comp _).symm
  refine ⟨F, pullback.lift a (𝟙 _) hs, hF, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩

  have hK : (spMap (algebraMap T K) ≫ pullback.lift a (𝟙 _) hs) ≫
      ((Over.pullback (a ≫ G.hom)).obj G).hom = 𝟙 _ ≫ spMap (algebraMap T K) := by
    show (spMap (algebraMap T K) ≫ pullback.lift a (𝟙 _) hs) ≫ pullback.snd G.hom (a ≫ G.hom) = _
    rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  set σK := pullback.lift _ _ hK with hσK
  have inv_fst₁' : e₁'.inv.left ≫ pullback.fst G'.hom (spMap (algebraMap T K) ≫ a ≫ G.hom) =
      pullback.fst (pullback.snd G'.hom j) (c ≫ pullback.snd G.hom j) ≫ pullback.fst G'.hom j := by
    rw [← hf₁', ← Category.assoc, ← Over.comp_left, e₁'.inv_hom_id]
    simp
  have inv_fst₂ : e₂.inv.left ≫ pullback.fst G.hom (spMap (algebraMap T K) ≫ a ≫ G.hom) =
      pullback.fst (pullback.snd G.hom (a ≫ G.hom)) (spMap (algebraMap T K)) ≫
        pullback.fst G.hom (a ≫ G.hom) := by
    rw [← hf₂, ← Category.assoc, ← Over.comp_left, e₂.inv_hom_id]
    simp
  have hpt : σK ≫ e₂.inv.left ≫ e₁.hom.left ≫ pullback.fst _ _ = c := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      erw [hf₁]
      rw [inv_fst₂, hσK]
      erw [pullback.lift_fst_assoc]
      rw [Category.assoc, pullback.lift_fst, hc]
    · have hcond : pullback.fst (((Over.pullback j).obj G).hom) (c ≫ pullback.snd G.hom j) ≫
          pullback.snd G.hom j = pullback.snd _ _ ≫ c ≫ pullback.snd G.hom j := pullback.condition
      have hw₁ : e₁.hom.left ≫
          pullback.snd (((Over.pullback j).obj G).hom) (c ≫ pullback.snd G.hom j) =
          pullback.snd G.hom (spMap (algebraMap T K) ≫ a ≫ G.hom) := Over.w e₁.hom
      have hw₂ : e₂.inv.left ≫ pullback.snd G.hom (spMap (algebraMap T K) ≫ a ≫ G.hom) =
          pullback.snd (((Over.pullback (a ≫ G.hom)).obj G).hom) (spMap (algebraMap T K)) :=
        Over.w e₂.inv
      simp only [Category.assoc]
      rw [hcond, reassoc_of% hw₁, reassoc_of% hw₂, hσK, pullback.lift_snd_assoc,
        Category.id_comp]
  have step : spMap (algebraMap T K) ≫ pullback.lift a (𝟙 _) hs ≫ F.left =
      σK ≫ fK.left ≫ pullback.fst _ _ := by
    rw [← hFK, hσK, pullback_map_left_comp_fst, pullback.lift_fst_assoc, Category.assoc]
  have hmap : ((Over.pullback (c ≫ pullback.snd G.hom j)).map f).left ≫
      pullback.fst (pullback.snd G'.hom j) (c ≫ pullback.snd G.hom j) =
      pullback.fst (((Over.pullback j).obj G).hom) (c ≫ pullback.snd G.hom j) ≫ f.left :=
    pullback_map_left_comp_fst _ f
  rw [reassoc_of% step]
  simp only [fK, Over.comp_left, Category.assoc]
  erw [hf₂']
  rw [inv_fst₁', reassoc_of% hmap, reassoc_of% hpt]

end GlobalTheory.HomExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem exists_prime_gt_neg_not_isSquare (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3) (b : ℕ) :
    ∃ n : ℕ, b < n ∧ n.Prime ∧ Odd n ∧ ¬ IsSquare (-(d : ZMod n)) := by
  haveI : NeZero (4 * d) := ⟨by have := hd.pos; omega⟩
  obtain ⟨n, hn, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * d) (a := -1) isUnit_one.neg (max b d)
  have hdvd : 4 * d ∣ n + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hmod]; ring
  have h4 : n % 4 = 3 := by
    have : 4 ∣ n + 1 := Dvd.dvd.trans (Dvd.intro _ rfl) hdvd
    omega
  have hdn : (n : ZMod d) = -1 := by
    have : d ∣ n + 1 := Dvd.dvd.trans (Dvd.intro_left _ rfl) hdvd
    rw [← ZMod.natCast_eq_zero_iff] at this
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hlt : d < n := lt_of_le_of_lt (le_max_right _ _) hn
  haveI : Fact n.Prime := ⟨hp⟩
  haveI : Fact d.Prime := ⟨hd⟩
  refine ⟨n, lt_of_le_of_lt (le_max_left _ _) hn, hp, by rw [Nat.odd_iff]; omega, ?_⟩
  have h1 : IsSquare (d : ZMod n) := by
    rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h4 hd4 hlt.ne', hdn,
      ZMod.exists_sq_eq_neg_one_iff]
    simp [hd4]
  have h0 : (d : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hd.pos hlt
  intro h2
  have h3 : IsSquare (-1 : ZMod n) := by
    have := h2.div h1
    rwa [neg_div, div_self h0] at this
  rw [ZMod.exists_sq_eq_neg_one_iff] at h3
  exact h3 h4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_eq_of_mem_adjoin_quadratic_generator (H : Host E) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) :
    ∃ u v : ℤ, a = (u : 𝓞 E) + (v : 𝓞 E) * H.w0 := by
  first
  | exact @_root_.GlobalTheory.CMGeneratorSquareModuli.main
  | exact _root_.GlobalTheory.CMGeneratorSquareModuli.main
  | (apply _root_.GlobalTheory.CMGeneratorSquareModuli.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMGeneratorSquareModuli.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMGeneratorSquareModuli.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMGeneratorSquareModuli.main ..)

theorem bar_mem_of_mem (H : Host E) {n : ℕ} (hn : AuxiliaryInertOddPrime H n) (P : Ideal (𝓞 E)) (hP : P.IsPrime)
    (hnP : (n : 𝓞 E) ∈ P) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) (haP : a ∈ P) : H.bar a ∈ P := by
  obtain ⟨hp, hodd, hsq, -⟩ := hn
  haveI : Fact n.Prime := ⟨hp⟩
  have key : ∀ m : ℤ, (m : 𝓞 E) ∈ P → (n : ℤ) ∣ m := by
    intro m hm
    by_contra h
    have hc : IsCoprime (n : ℤ) m :=
      (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr h
    obtain ⟨s, t, hst⟩ := hc
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 E) = (s : 𝓞 E) * n + (t : 𝓞 E) * m := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hst.symm
    rw [this]
    exact P.add_mem (P.mul_mem_left _ hnP) (P.mul_mem_left _ hm)
  obtain ⟨u, v, rfl⟩ := exists_eq_of_mem_adjoin_quadratic_generator H ha
  have hN : (n : ℤ) ∣ (2 * u + v) ^ 2 + H.d * v ^ 2 := by
    apply key
    have : (((2 * u + v) ^ 2 + H.d * v ^ 2 : ℤ) : 𝓞 E) =
        (2 * ((2 * u + v : 𝓞 E) - v * H.rt)) * ((u : 𝓞 E) + v * H.w0) := by
      push_cast
      linear_combination (-((2 * u + v : 𝓞 E) - v * H.rt) * v) * H.two_weight_eq_one_add_root + (v : 𝓞 E) ^ 2 * H.rt_sq
    rw [this]
    exact P.mul_mem_left _ haP
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hN
  push_cast at hN
  have hv : (v : ZMod n) = 0 := by
    by_contra hv
    apply hsq
    refine ⟨(2 * u + v) / v, ?_⟩
    field_simp
    linear_combination -hN
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    subst this
    exact absurd hodd (by decide)
  have hu : (u : ZMod n) = 0 := by
    rw [hv] at hN
    simpa [h2] using hN
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hu hv
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨v', rfl⟩ := hv
  have : H.bar (((n * u' : ℤ) : 𝓞 E) + ((n * v' : ℤ) : 𝓞 E) * H.w0) =
      ((u' : 𝓞 E) + v' * H.bar H.w0) * n := by
    simp only [map_add (f := _), map_mul, map_intCast]
    push_cast
    ring
  rw [this]
  exact P.mul_mem_left _ hnP

theorem not_Mb_le (H : Host E) {n : ℕ} (hn : AuxiliaryInertOddPrime H n) (l : Level H) (P : Ideal (𝓞 E)) (hP : P.IsPrime)
    (hnP : (n : 𝓞 E) ∈ P) : ¬ l.Mb ≤ P := by
  intro h
  apply hP.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le h ?_
  rw [Ideal.map_le_iff_le_comap, l.fromK, Ideal.span_le]
  rintro a ⟨haM, ha⟩
  exact bar_mem_of_mem H hn P hP hnP ha (h haM)

theorem AuxiliaryInertOddPrime.coprime_level {H : Host E} {n : ℕ} (hn : AuxiliaryInertOddPrime H n) (l : Level H) : n.Coprime l.M := by
  rw [Nat.Prime.coprime_iff_not_dvd hn.1]
  rintro ⟨m, hm⟩
  have hnu : Ideal.span {(n : 𝓞 E)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 := hu.map (Algebra.norm ℤ)
    have h2 : Algebra.norm ℤ (n : 𝓞 E) = (n : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      rw [← Algebra.norm_algebraMap]; simp
    rw [h2, isUnit_pow_iff Module.finrank_pos.ne'] at h1
    exact (Nat.prime_iff_prime_int.mp hn.1).not_unit h1
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hnu
  have hnP : (n : 𝓞 E) ∈ P := hle (Ideal.mem_span_singleton_self _)
  have hM : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ P := by
    rw [l.prod, Ideal.span_singleton_le_iff_mem, hm]
    push_cast
    exact P.mul_mem_right _ hnP
  rcases hP.isPrime.mul_le.mp hM with h | h
  · exact not_Mb_le H hn l P hP.isPrime hnP h
  · rw [Ideal.map_le_iff_le_comap] at h
    haveI := hP.isPrime
    refine not_Mb_le H hn l _ (Ideal.comap_isPrime _ P) ?_ h
    rw [Ideal.mem_comap, map_natCast]
    exact hnP

theorem exists_large_auxiliary_prime (H : Host E) (b : ℕ) : ∃ n : ℕ, b < n ∧ AuxiliaryInertOddPrime H n := by
  obtain ⟨n, hn, hp, hodd, hsq⟩ := exists_prime_gt_neg_not_isSquare H.d H.d_prime
    (by have := H.d_mod; omega) (max b (NumberField.discr E).natAbs)
  refine ⟨n, lt_of_le_of_lt (le_max_left _ _) hn, hp, hodd, hsq, ?_⟩
  rw [Int.natCast_dvd]
  exact Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr (NumberField.discr_ne_zero E))
    (lt_of_le_of_lt (le_max_right _ _) hn)

theorem exists_two_auxiliary_inert_odd_primes_coprime_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
      (∃ n n' : ℕ, AuxiliaryInertOddPrime H n ∧ AuxiliaryInertOddPrime H n' ∧ n ≠ n') ∧
        ∀ n : ℕ, AuxiliaryInertOddPrime H n → ∀ l : Level H, n.Coprime l.M := by
  intro E _ _ _ H
  obtain ⟨n, -, hn⟩ := exists_large_auxiliary_prime H 0
  obtain ⟨n', hlt, hn'⟩ := exists_large_auxiliary_prime H n
  exact ⟨⟨n, n', hn, hn', hlt.ne⟩, fun _ h l => h.coprime_level l⟩

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DetExtend

theorem exists_oAct_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) : ∃ a' : OAct O ((Over.pullback f).obj G), ∀ c, a'.act c = (Over.pullback f).map (a.act c) :=
  ⟨{ act := fun c => (Over.pullback f).map (a.act c)
     hom := fun c => by have := a.hom c; infer_instance
     one := by rw [a.one, CategoryTheory.Functor.map_id]
     mul := fun x y => by rw [a.mul, CategoryTheory.Functor.map_comp]
     add := fun x y => by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _ }, fun _ => rfl⟩

theorem lieMult_fibre {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) {G : Over S} [GrpObj G] {O : Type}
    [CommRing O] (a : OAct O G) (a' : OAct O ((Over.pullback x).obj G))
    (h : ∀ c, a'.act c = (Over.pullback x).map (a.act c)) {k' : Type} [Field k'] (y : Sp k' ⟶ Sp k)
    (τ : O →+* k') (n : ℕ) : LieMult a' y τ n ↔ LieMult a (y ≫ x) τ n :=
  LiePull.lieMult_pull O _ _ G _ x _ a a' (isGrpPullback_pullback G x)
    (fun c => by rw [h]; exact pullback.lift_fst _ _ _) k' y τ n


open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap eigLat IsUnivChart) in
theorem lieMult_iff_finrank {k : Type} [Field k] {O : Type} [CommRing O] {G : Over (Sp k)} [GrpObj G]
    (act : OAct O G) [∀ a, IsMonHom (act.act a)] {n : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
    (τ : O →+* k) (N : ℕ) :
    LieMult act (𝟙 (Sp k)) τ N ↔ Module.finrank k (eigLat hx act.act (fun a => τ a)) = N := by
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ G) ≃* (epsR k ⟶ G) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl G)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have he' : ∀ w, (e.symm w).left = w.left := fun w => by rw [← he, e.apply_symm_apply]
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ G).left = η[G].left := Category.id_comp _
  let P : (epsR k ⟶ G) → Prop := fun w => IsTangent w ∧ ∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w
  have hP : ∀ w, IsLieEigen act (𝟙 _) τ w ↔ P (e w) := fun w =>
    and_congr (by rw [IsTangent, he, one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he]
      rfl)
  have key : LieMult act (𝟙 (Sp k)) τ N ↔ ∃ v : Fin N → (epsR k ⟶ G), (∀ i, P (v i)) ∧
      ∀ w, P w → ∃! c : Fin N → k, IsLieComb c v w :=
    ⟨LiePull.basis_transport e (P := IsLieEigen act (𝟙 _) τ) (Q := P)
      (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left) hP
      (fun c u v => by rw [he, he]; rfl) N,
    LiePull.basis_transport e.symm (Q := IsLieEigen act (𝟙 _) τ) (P := P)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
      (fun w => by rw [hP, e.apply_symm_apply]) (fun c u v => by rw [he', he']; rfl) N⟩
  have mem : ∀ c, c ∈ eigLat hx act.act (fun a => τ a) ↔ P (tvec (x := x) c) := fun c => by
    rw [Chart.mem_eigLat_iff]
    exact ⟨fun h => ⟨(Chart.isTan_iff _).1 (Chart.isTan_tvec hx c), fun a => (Chart.tvec_eig_iff hx _ _ _).2 (h a)⟩,
      fun h a => (Chart.tvec_eig_iff hx _ _ _).1 (h.2 a)⟩
  have ex : ∀ w, P w → ∃ c : eigLat hx act.act (fun a => τ a), w = tvec (x := x) c := fun w hw => by
    have h : w = tvec (x := x) _ := Chart.tcoord_spec hx w ((Chart.isTan_iff _).2 hw.1)
    exact ⟨⟨_, (mem _).2 (h ▸ hw)⟩, h⟩
  have comb : ∀ (b : Fin N → eigLat hx act.act (fun a => τ a)) (c : eigLat hx act.act (fun a => τ a))
      (d : Fin N → k), IsLieComb d (fun i => tvec (x := x) (b i)) (tvec (x := x) c) ↔
        Fintype.linearCombination k b d = c := fun b c d => by
    refine (Chart.isLieComb_iff d _ _).trans ?_
    obtain ⟨h, E⟩ := Chart.prodPts_tan hx d (fun i => tvec (x := x) (b i)) fun i => Chart.isTan_tvec hx _
    have E' : prodPts d (fun i => tvec (x := x) (b i)) = tvec (x := x) _ := Chart.tcoord_spec hx _ h
    rw [E', E, Subtype.ext_iff, Fintype.linearCombination_apply]
    simp only [Chart.tcoord_tvec, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    exact ⟨fun h => (Chart.tvec_inj hx h).symm, fun h => by rw [h]⟩
  rw [key]
  constructor
  · rintro ⟨v, hv, H⟩
    choose b hb using fun i => ex _ (hv i)
    obtain rfl : v = fun i => tvec (x := x) (b i) := funext hb
    rw [← (LinearEquiv.ofBijective (Fintype.linearCombination k b) ((Function.bijective_iff_existsUnique _).2
      fun c => (existsUnique_congr (comb b c)).1 (H _ ((mem _).1 c.2)))).finrank_eq, Module.finrank_fin_fun]
  · intro h
    let b := Module.finBasisOfFinrankEq _ _ h
    refine ⟨fun i => tvec (x := x) (b i), fun i => (mem _).1 (b i).2, fun w hw => ?_⟩
    obtain ⟨c, rfl⟩ := ex w hw
    refine (existsUnique_congr (comb b c)).2 ((Function.bijective_iff_existsUnique _).1 ?_ _)
    convert b.equivFun.symm.bijective using 1
    ext r
    simp [Fintype.linearCombination_apply]


open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap eigLat fB pushR dualMapA) in
theorem lieMult_extend {S : Scheme.{0}} {G : Over S} [GrpObj G] [Smooth G.hom] {K Ω : Type} [Field K] [Field Ω]
    (i : K →+* Ω) (x : Sp K ⟶ S) {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* K) (N : ℕ) :
    LieMult act (spMap i ≫ x) (i.comp τ) N ↔ LieMult act x τ N := by
  let _ := i.toAlgebra
  obtain ⟨a₁, h₁⟩ := exists_oAct_pullback x act
  have E₁ := lieMult_fibre x act a₁ h₁ (𝟙 _) τ N
  rw [Category.id_comp] at E₁
  rw [← E₁, ← lieMult_fibre x act a₁ h₁]
  have : Smooth ((Over.pullback x).obj G).hom := inferInstanceAs (Smooth (pullback.snd G.hom x))
  generalize_proofs at *
  set G₁ := (Over.pullback x).obj G
  obtain ⟨a₂, h₂⟩ := exists_oAct_pullback (fB K Ω) a₁
  have E₂ := lieMult_fibre (fB K Ω) a₁ a₂ h₂ (𝟙 _) (i.comp τ) N
  rw [Category.id_comp] at E₂
  refine E₂.symm.trans ?_
  have := a₁.hom
  have := a₂.hom
  obtain ⟨n, y, hy⟩ := Chart.univChartLoc G₁
  obtain ⟨y', hy', hc⟩ := Chart.tanBC_alg (R' := Ω) G₁ n y hy
  have hpt : ∀ c : Fin n → K, pushR G₁ (tvec (x := y') (algebraMap K Ω ∘ c)) =
      Chart.spMap (dualMapA K Ω) ≫ tvec (x := y) c := fun c =>
    Over.OverMorphism.ext (by rw [Chart.pushR_left, hc c]; rfl)
  have hL : ∀ a (c : Fin n → K), tmap hy' (a₂.act a) (algebraMap K Ω ∘ c) =
      algebraMap K Ω ∘ tmap hy (a₁.act a) c := fun a c => by
    apply Chart.tvec_inj hy'
    apply Chart.pushR_inj G₁
    rw [Chart.tvec_tmap hy', h₂, Chart.pushR_map, hpt, hpt, Chart.tvec_tmap hy, Category.assoc]
  have hr : Module.finrank K (eigLat hy a₁.act fun a => τ a) =
      Module.finrank Ω (eigLat hy' a₂.act fun a => i.comp τ a) :=
    Chart.finrank_eig_bc (fun a => tmap hy (a₁.act a)) (fun a => tmap hy' (a₂.act a)) hL τ
  rw [lieMult_iff_finrank a₂ hy', lieMult_iff_finrank a₁ hy, hr]

theorem exists_factor {O K Ω : Type} [CommRing O] [Algebra.IsIntegral ℤ O] [Field K] [IsAlgClosed K] [Field Ω]
    (i : K →+* Ω) (σ : O →+* Ω) : ∃ τ : O →+* K, i.comp τ = σ := by
  let _ := i.toAlgebra
  have h : ∀ a, σ a ∈ i.range := fun a => by
    have h₀ : IsIntegral ℤ (σ a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map σ.toIntAlgHom
    have h₁ : IsIntegral K (σ a) := h₀.tower_top
    exact minpoly.mem_range_of_degree_eq_one K _
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible h₁))
  let e : K ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun a b hab => i.injective (congrArg Subtype.val hab), i.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (σ.codRestrict _ h), RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (σ.codRestrict _ h a))

end GlobalTheory.DetExtend

theorem GlobalTheory.detCond_iff_of_field_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (G : Over S) [GrpObj G] (K Ω : Type) [Field K] [Field Ω] (i : K →+* Ω) (x : Sp K ⟶ S) [IsAlgClosed K] [CharZero K] (act : OAct (𝓞 E) G) (ρ : K), Smooth G.hom → (DetCond D act (spMap i ≫ x) (i ρ) ↔ DetCond D act x ρ) := by
  intro E _ _ _ H D S G _ K Ω _ _ i x _ _ act ρ _
  have key : ∀ τ : 𝓞 E →+* K,
      ((i.comp τ H.rt = i ρ → LieMult act (spMap i ≫ x) (i.comp τ) D.p) ∧
        (i.comp τ H.rt ≠ i ρ → LieMult act (spMap i ≫ x) (i.comp τ) D.q)) ↔
      ((τ H.rt = ρ → LieMult act x τ D.p) ∧ (τ H.rt ≠ ρ → LieMult act x τ D.q)) := fun τ => by
    rw [DetExtend.lieMult_extend, DetExtend.lieMult_extend, RingHom.comp_apply, Ne, i.injective.eq_iff]
  refine ⟨fun h τ => (key τ).1 (h _), fun h σ => ?_⟩
  obtain ⟨τ, rfl⟩ := DetExtend.exists_factor i σ
  exact (key τ).2 (h τ)
end

