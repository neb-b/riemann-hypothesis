module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0070
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartProjectionRespectsOrthogonality
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair


set_option maxHeartbeats 800000 in
theorem transfer_of_unif : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegData W I) (Av : Out.PolAV (Spec (CommRingCat.of (FractionRing W)))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D Av G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∀ τ : PtHom (spMap β) (spMap β) G D.toPre.P.A, (∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ (U.gt 0).pG.left) → ∀ n : ℕ, Transfer n U.cubG D.toPre.cub τ := by
  intro W _ _ I D Av G _ _ U Ω _ β hβ τ hτ n A _ _ x y h
  let β₀ : W ⧸ I ^ (0 + 1) →+* A := Ideal.Quotient.lift _ ((algebraMap Ω A).comp β) fun a ha => by
    rw [zero_add, pow_one] at ha
    rw [RingHom.comp_apply, hβ a ha, map_zero]
  let T₀ : Over (Spec (CommRingCat.of (W ⧸ I ^ (0 + 1)))) := Over.mk (spMap β₀)
  have hT : T₀.hom ≫ Out.thick W I 0 = (overAt (spMap β) A).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  let ρ : overAt (spMap β) A ⟶ Over.mk (T₀.hom ≫ Out.thick W I 0) :=
    Over.homMk (𝟙 (Sp A)) ((Category.id_comp _).trans hT)
  let φ : (T₀ ⟶ Out.thickObj W I 0 G) →* (overAt (spMap β) A ⟶ G) :=
    (preHom ρ).comp (UU.toBaseHom (UU.toBase_mul_pullback G (Out.thick W I 0)) T₀)
  have hφ : ∀ r, (φ r).left = r.left ≫ (Out.fstG I 0 G).left := fun r => Category.id_comp _
  have hψ : ∀ r, (τ A (φ r)).left = r.left ≫ (U.gt 0).pG.left := fun r => hτ A _ _ (hφ r).symm
  have inj : Function.Injective φ := fun r s e => Over.OverMorphism.ext (pullback.hom_ext
    ((hφ r).symm.trans ((congrArg (·.left) e).trans (hφ s))) ((Over.w r).trans (Over.w s).symm))
  have surj : Function.Surjective φ := fun v =>
    ⟨Over.homMk (pullback.lift v.left T₀.hom ((Over.w v).trans hT.symm)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  obtain ⟨x, rfl⟩ := surj x
  obtain ⟨y, rfl⟩ := surj y
  have hx : x ^ n = 1 := inj ((map_pow φ x n).trans (h.1.trans (map_one φ).symm))
  have hy : y ^ n = 1 := inj ((map_pow φ y n).trans (h.2.1.trans (map_one φ).symm))
  refine ⟨by rw [← map_pow, h.1, map_one], by rw [← map_pow, h.2.1, map_one], fun z J hJ => ?_⟩
  obtain ⟨N, hN⟩ := UU.exists_good_pt U.LG.isLB (Z := Sp A) z
  have key : ∀ a b d : T₀ ⟶ Out.thickObj W I 0 G,
      cubV D.toPre.cub z J (τ A (φ a)) (τ A (φ b)) (τ A (φ d)) *
        TorusInvariance.wVal U 0 z J N (a * b).left * TorusInvariance.wVal U 0 z J N (a * d).left *
        TorusInvariance.wVal U 0 z J N (b * d).left * TorusInvariance.wVal U 0 z J N (1 : T₀ ⟶ _).left =
      TorusInvariance.wVal U 0 z J N (a * b * d).left * TorusInvariance.wVal U 0 z J N a.left *
        TorusInvariance.wVal U 0 z J N b.left * TorusInvariance.wVal U 0 z J N d.left *
        cubV U.cubG z N (φ a) (φ b) (φ d) := by
    intro a b d
    have e := TorusInvariance.cube_val U (T := T₀) ![a, b, d] hJ hN
    have t₁ : WCub.tri (Out.thick W I 0) (U.gt 0).pG ![a, b, d] =
        (lift (τ A (φ a)) (lift (τ A (φ b)) (τ A (φ d)))).left := hom_ext_triple _ fun i => by
      rw [← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp only [x3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, lift_fst,
        lift_snd_assoc, lift_snd, hψ] <;> rfl
    have t₂ : WCub.tri (Out.thick W I 0) (Out.fstG I 0 G) ![a, b, d] =
        (lift (φ a) (lift (φ b) (φ d))).left := hom_ext_triple _ fun i => by
      rw [← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp only [x3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, lift_fst,
        lift_snd_assoc, lift_snd, hφ] <;> rfl
    have p : ∀ k : thK.{0}, (psum (Out.thickObj W I 0 G) ![a, b, d] k.down).left =
        (lift a (lift b d)).left ≫ thφ _ (x3 (Out.thickObj W I 0 G)) k := fun k =>
      congrArg (·.left) ((congrArg (fun q => psum _ q k.down) (funext fun i => by
        fin_cases i <;> simp [x3, preHom])).trans
        (psum_hom (preHom (lift a (lift b d))) (x3 (Out.thickObj W I 0 G)) k.down).symm)
    rw [t₁, t₂] at e
    simp only [p] at e
    exact UU.cub_alg (e.trans (congrArg₂ (· * ·) (prod_cub a b d (TorusInvariance.wVal U 0 z J N)) rfl))
  refine UU.cubN_ratio_twist ((τ A).comp φ) (fun r => TorusInvariance.wVal U 0 z J N r.left)
    (θ := cubV D.toPre.cub z J) (θ' := fun a b d => cubV U.cubG z N (φ a) (φ b) (φ d)) key hx hy ?_
  simpa only [cubN, map_mul, map_pow, map_one] using h.2.2 z N hN

end GlobalTheory.AlphaPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddPCvOfAddMod
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem nEval_cvAt {Ω A : Type} [Field Ω] [CommRing A] [Algebra Ω A] (s : MvPowerSeries (Fin 2) Ω)
    (hs : MvPowerSeries.constantCoeff s = 0) (f : PowerSeries Ω) (v : Fin 2 → A) (hv : ∀ i, IsNilpotent (v i)) :
    nEval (cvAt s f) v = nEval (σ := Unit) f (fun _ => nEval s v) :=
  ChartCompare.nEval_subst (σ := Unit) (fun _ => s) (fun _ => hs) f v hv

theorem formalAdd_cv_of_addMod :
    ∀ (Ω : Type) [Field Ω] (p d : ℕ) (F : Fin d → PS Ω 2 d) (ga : Fin d → PowerSeries Ω), (∀ j, PowerSeries.constantCoeff (ga j) = 0) → AddMod p F ga → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a a' : A), a ^ p = 0 → a' ^ p = 0 → addP F (cv ga a) (cv ga a') = cv ga (a + a') := by
  intro Ω _ p d F ga h0 hadd A _ _ a a' ha ha'
  funext i
  have hp : ∀ k : Fin 2, (![a, a'] : Fin 2 → A) k ^ p = 0 := fun k => by
    fin_cases k
    · exact ha
    · exact ha'
  have hv : ∀ k : Fin 2, IsNilpotent ((![a, a'] : Fin 2 → A) k) := fun k => ⟨p, hp k⟩
  have hz : nEval (MvPowerSeries.subst (fun q : Fin 2 × Fin d => cvAt (MvPowerSeries.X q.1) (ga q.2)) (F i) -
      cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (ga i)) (![a, a'] : Fin 2 → A) = 0 := by
    rw [evBasic_nEval_eq_tEval _ _ p hp, evBasic_tEval_eq_sum]
    refine Finset.sum_eq_zero fun e he => ?_
    rw [Fintype.mem_piFinset] at he
    rw [hadd i _ (Finset.mem_range.1 (he 0)) (Finset.mem_range.1 (he 1)), map_zero, zero_mul]
  have hc : ∀ q : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff (cvAt (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) Ω) (ga q.2)) = 0 := fun q =>
    MvPowerSeries.constantCoeff_subst_eq_zero (a := fun _ : Unit => (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) Ω))
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _)
      (fun _ => MvPowerSeries.constantCoeff_X _) (h0 q.2)
  rw [nEval_sub hv, sub_eq_zero, ChartCompare.nEval_subst _ hc _ _ hv, nEval_cvAt _ (by simp) _ _ hv,
    nEval_add hv, ChartCompare.nEval_X _ hv, ChartCompare.nEval_X _ hv] at hz
  refine Eq.trans ?_ hz
  unfold addP evP
  congr 1
  funext q
  rw [nEval_cvAt _ (MvPowerSeries.constantCoeff_X _) _ _ hv, ChartCompare.nEval_X _ hv]
  obtain ⟨k, j⟩ := q
  fin_cases k <;> rfl

end GlobalTheory.AlphaPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPMultiplicativeCharacterEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaChar
open Polynomial

theorem poly_eq_one {Ω : Type} [Field Ω] (p : ℕ) [CharP Ω p] (w : Polynomial Ω) (c : Ω)
    (hd : w.degree < p) (h0 : w.coeff 0 = 1) (h : derivative w = C c * w) : w = 1 := by
  have hw : w ≠ 0 := by rintro rfl; simp at h0
  have hc : c = 0 := by
    by_contra hc
    have h1 := degree_derivative_lt hw
    rw [h, degree_C_mul hc] at h1
    exact lt_irrefl _ h1
  rw [hc, C_0, zero_mul] at h
  ext n
  rcases n with _ | n
  · simpa using h0
  · simp only [coeff_one, Nat.succ_ne_zero, ite_false]
    by_cases hn : n + 1 < p
    · have h2 := congrArg (fun q : Polynomial Ω => q.coeff n) h
      simp only [coeff_derivative, coeff_zero] at h2
      have h3 : ((n : Ω) + 1) ≠ 0 := by
        intro h3
        have : ((n + 1 : ℕ) : Ω) = 0 := by exact_mod_cast h3
        rw [CharP.cast_eq_zero_iff Ω p] at this
        exact absurd (Nat.le_of_dvd (Nat.succ_pos n) this) (by omega)
      exact (mul_eq_zero.1 h2).resolve_right h3
    · apply coeff_eq_zero_of_degree_lt
      exact lt_of_lt_of_le hd (by exact_mod_cast (not_lt.1 hn))

theorem char_eq_one : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (u : ∀ (A : Type) [CommRing A] [Algebra Ω A], A → Aˣ), (∀ (A B : Type) [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (a : A), a ^ p = 0 → u B (f a) = Units.map (f : A →* B) (u A a)) → (∀ (A : Type) [CommRing A] [Algebra Ω A] (a a' : A), a ^ p = 0 → a' ^ p = 0 → u A (a + a') = u A a * u A a') → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → u A a = 1 := by
  intro Ω _ p hp _ u hnat hadd
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp0 : p ≠ 0 := by omega
  have hm : (X ^ p : Polynomial Ω).Monic := monic_X_pow p
  let R := AdjoinRoot (X ^ p : Polynomial Ω)
  let t : R := AdjoinRoot.root (X ^ p : Polynomial Ω)
  have ht : t ^ p = 0 := by
    have := AdjoinRoot.mk_self (f := (X ^ p : Polynomial Ω))
    rwa [map_pow, AdjoinRoot.mk_X] at this
  obtain ⟨w0, hw0⟩ := AdjoinRoot.mk_surjective (g := (X ^ p : Polynomial Ω)) (u R t : R)
  let w : Polynomial Ω := w0 %ₘ (X ^ p)
  have hwd : w.degree < p := by
    have := degree_modByMonic_lt w0 hm
    rwa [degree_X_pow] at this
  have hw : aeval t w = (u R t : R) := by
    rw [← hw0, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_mk]
    have := modByMonic_add_div w0 (X ^ p)
    exact ⟨-(w0 /ₘ X ^ p), by simp only [w]; linear_combination this⟩
  have key : ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 →
      (u A a : A) = aeval a w := by
    intro A _ _ a ha
    let f : R →ₐ[Ω] A := Ideal.Quotient.liftₐ (Ideal.span {(X ^ p : Polynomial Ω)}) (aeval a) (by
      intro q hq
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.1 hq
      simp [ha])
    have hf : f t = a := by
      change aeval a (X : Polynomial Ω) = a
      simp
    have h1 := hnat R A f t ht
    rw [hf] at h1
    rw [h1, ← hf, aeval_algHom_apply, hw]
    rfl
  have h0 : w.coeff 0 = 1 := by
    have h1 := hadd Ω 0 0 (zero_pow hp0) (zero_pow hp0)
    rw [add_zero, left_eq_mul] at h1
    have h2 := key Ω 0 (zero_pow hp0)
    rw [h1] at h2
    rw [coeff_zero_eq_aeval_zero, ← h2]; rfl
  have hder : derivative w = C ((derivative w).coeff 0) * w := by
    let D := DualNumber R
    let e : D := DualNumber.eps
    let j : R →ₐ[Ω] D := TrivSqZeroExt.inlAlgHom Ω R R
    have he : e ^ 2 = 0 := by rw [pow_two]; exact DualNumber.eps_mul_eps
    have hep : e ^ p = 0 := pow_eq_zero_of_le hp2 he
    have hs : (j t) ^ p = 0 := by rw [← map_pow, ht, map_zero]
    have hpD : (p : D) = 0 := by
      rw [← map_natCast (algebraMap Ω D), CharP.cast_eq_zero, map_zero]
    have hse : (j t + e) ^ p = 0 := by
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (j t) e
      rw [hr, hs, hep, hpD]; simp
    have h1 := congrArg Units.val (hadd D (j t) e hs hep)
    rw [Units.val_mul, key D _ hse, key D _ hs, key D _ hep,
      aeval_add_of_sq_eq_zero _ _ _ he] at h1
    have h2 : aeval e w = 1 + algebraMap Ω D ((derivative w).coeff 0) * e := by
      have := aeval_add_of_sq_eq_zero w 0 e he
      rw [zero_add] at this
      rw [this, ← coeff_zero_eq_aeval_zero', ← coeff_zero_eq_aeval_zero', h0, map_one]
    rw [h2, aeval_algHom_apply, aeval_algHom_apply, ← j.commutes, mul_add, _root_.mul_one,
      add_right_inj, ← _root_.mul_assoc, ← map_mul] at h1
    have hsnd : ∀ x : R, TrivSqZeroExt.snd (j x * e) = x := by
      intro x
      change TrivSqZeroExt.snd ((TrivSqZeroExt.inl x : DualNumber R) * DualNumber.eps) = x
      rw [DualNumber.snd_mul]; simp
    have h3 := congrArg TrivSqZeroExt.snd h1
    rw [hsnd, hsnd] at h3
    have h4 : aeval t (derivative w - C ((derivative w).coeff 0) * w) = 0 := by
      rw [map_sub, map_mul, aeval_C, h3]; ring
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h4
    have h5 := eq_zero_of_dvd_of_degree_lt h4 (by
      rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt degree_derivative_le hwd
      · rw [← smul_eq_C_mul]; exact lt_of_le_of_lt (degree_smul_le _ _) hwd)
    exact sub_eq_zero.1 h5
  have hone := poly_eq_one p w _ hwd h0 hder
  intro A _ _ a ha
  ext
  rw [key A a ha, hone]; simp

end GlobalTheory.AlphaChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubicalWeilTrivialOfLocalArtinianPoints
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem exists_isPullback_spec_of_isFinite {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (D : CommRingCat.{0})
    (e : Spec D ⟶ Y) :
    ∃ (H : CommRingCat.{0}) (φ : D ⟶ H) (y : Spec H ⟶ X), φ.hom.Finite ∧ IsPullback y (Spec.map φ) f e := by
  have : IsAffine (pullback f e) := isAffine_of_isAffineHom (pullback.snd f e)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback f e).isoSpec.inv ≫ pullback.snd f e)
  refine ⟨_, φ, (pullback f e).isoSpec.inv ≫ pullback.fst f e, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  · rw [hφ]
    exact (IsPullback.of_hasPullback f e).of_iso (pullback f e).isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)

theorem eq_of_forall_nilpotent_aug {Ω O : Type} [Field Ω] [IsAlgClosed Ω] [CommRing O] [Algebra Ω O]
    [Module.Finite Ω O] {a b : O}
    (h : ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) →
      ∀ g : O →ₐ[Ω] A, g a = g b) : a = b := by
  have : IsArtinianRing O := IsArtinianRing.of_finite Ω O
  refine sub_eq_zero.1 (eq_zero_of_localization _ fun q hq => ?_)
  rw [map_sub, sub_eq_zero]
  let A := Localization.AtPrime q
  let g : O →ₐ[Ω] A := IsScalarTower.toAlgHom Ω O A
  have hg : Function.Surjective g := IsArtinianRing.localization_surjective q.primeCompl A
  have : Module.Finite Ω A := Module.Finite.of_surjective g.toLinearMap hg
  have : IsArtinianRing A := IsArtinianRing.of_finite Ω A
  let r : A →ₐ[Ω] ResidueField A := IsScalarTower.toAlgHom Ω A (ResidueField A)
  have : Module.Finite Ω (ResidueField A) := Module.Finite.of_surjective r.toLinearMap residue_surjective
  let e : Ω ≃ₐ[Ω] ResidueField A :=
    AlgEquiv.ofBijective (Algebra.ofId Ω _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine h A (e.symm.toAlgHom.comp r) ?_ g
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  refine ⟨N, le_bot_iff.1 (le_trans (Ideal.pow_right_mono ?_ N) hN.le)⟩
  rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  intro t ht
  have : e.symm (r t) = 0 := ht
  exact (residue_eq_zero_iff t).1 ((map_eq_zero_iff _ e.symm.injective).1 this)

theorem cubWeil_one_of_local_artinian : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (n : ℕ), IsFinite ((𝟙 G) ^ n : G ⟶ G).left → ∀ (D : Type) [CommRing D] [Algebra Ω D] [Module.Finite Ω D] (x : overAt s D ⟶ G), x ^ n = 1 → (∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ (f : D →ₐ[Ω] A) (y : overAt s A ⟶ G), y ^ n = 1 → CubWeil c n (homAt s f ≫ x) y 1) → ∀ (T' : Over S) (ρ : T' ⟶ overAt s D) (y : T' ⟶ G), y ^ n = 1 → CubWeil c n (ρ ≫ x) y 1 := by
  intro Ω _ _ S s G _ _ L c n hfin D _ _ _ x hx h T' ρ y hy
  obtain ⟨H, φ, y₀, hφ, hpb⟩ := exists_isPullback_spec_of_isFinite ((𝟙 G) ^ n : G ⟶ G).left (CommRingCat.of D)
    (1 : overAt s D ⟶ G).left
  let : Algebra D H := φ.hom.toAlgebra
  let : Algebra Ω H := (φ.hom.comp (algebraMap Ω D)).toAlgebra
  have : IsScalarTower Ω D H := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite D H := hφ
  have : Module.Finite Ω H := Module.Finite.trans D H
  let j : D →ₐ[Ω] H := IsScalarTower.toAlgHom Ω D H
  have hj : (homAt s j).left = Spec.map φ := rfl
  have hpow : ∀ {T : Over S} (z : T ⟶ G), z.left ≫ ((𝟙 G) ^ n : G ⟶ G).left = (z ^ n).left := by
    intro T z
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {T : Over S} (r : T ⟶ overAt s D), r.left ≫ (1 : overAt s D ⟶ G).left = (1 : T ⟶ G).left := by
    intro T r
    rw [← Over.comp_left, MonObj.comp_one]
  have hw : y₀ ≫ G.hom = (overAt s H).hom := by
    rw [← Over.w ((𝟙 G) ^ n : G ⟶ G), ← Category.assoc, hpb.w, Category.assoc, Over.w (1 : overAt s D ⟶ G)]
    exact Over.w (homAt s j)
  let u : overAt s H ⟶ G := Over.homMk y₀ hw
  have hu : u ^ n = 1 := Over.OverMorphism.ext (by rw [← hpow, ← hone (homAt s j)]; exact hpb.w)
  have hx' : (homAt s j ≫ x) ^ n = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c hx' hu
  have hζ1 : ζ = 1 := by
    refine Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of H)).hom).1 ?_)
    refine eq_of_forall_nilpotent_aug (Ω := Ω) fun A _ _ π hπ g => ?_
    have h₁ := h A π hπ (g.comp j) (homAt s g ≫ u) (by rw [← MonObj.comp_pow, hu, MonObj.comp_one])
    rw [← hom_comp, Category.assoc] at h₁
    have e : (homAt s g).left.appTop.hom ζ.val = (homAt s g).left.appTop.hom (1 : Γ((overAt s H).left, ⊤)ˣ).val :=
      (congrArg Units.val ((hζ.comp (homAt s g)).unique h₁)).trans (map_one _).symm
    have nat := fun t => congrArg (fun q => q.hom t) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (g : H →+* A)))
    exact (nat _).symm.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom e).trans (nat _))
  subst hζ1
  have hl : y.left ≫ ((𝟙 G) ^ n : G ⟶ G).left = ρ.left ≫ (1 : overAt s D ⟶ G).left := by rw [hpow, hy, hone]
  let l : T' ⟶ overAt s H := Over.homMk (hpb.lift _ _ hl) (by
    rw [← Over.w (homAt s j), hj, ← Over.w ρ]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hpb.lift_snd _ _ hl)))
  have e₁ : l ≫ homAt s j = ρ := Over.OverMorphism.ext (hpb.lift_snd _ _ hl)
  have e₂ : l ≫ u = y := Over.OverMorphism.ext (hpb.lift_fst _ _ hl)
  have := hζ.comp l
  rwa [← Category.assoc, e₁, e₂, map_one] at this

end GlobalTheory.AlphaPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DegenerateDirectionOfNotNondegenerate
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.Reduce

open Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

def addDefect (F : Fin d → PS R 2 d) (ga : Fin d → PowerSeries R) (i : Fin d) : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.subst (fun q : Fin 2 × Fin d =>
    MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) R)) (ga q.2)) (F i) -
    MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) (ga i)

def cob (F : Fin d → PS R 2 d) (b : PS R 1 d) : PS R 2 d :=
  ev (n := 2) ![addOf F (pt R d 0) (pt R d 1)] b - ev (n := 2) ![pt R d 0] b - ev (n := 2) ![pt R d 1] b

theorem map_addDefect (ψ : R →+* S) (F : Fin d → PS R 2 d) (ga : Fin d → PowerSeries R)
    (h0 : ∀ i, PowerSeries.constantCoeff (ga i) = 0) (i : Fin d) :
    MvPowerSeries.map ψ (addDefect F ga i) =
      addDefect (fun i => MvPowerSeries.map ψ (F i)) (fun i => PowerSeries.map ψ (ga i)) i := by
  have hX : ∀ k : Fin 2, MvPowerSeries.HasSubst
      (fun _ : Unit => (MvPowerSeries.X k : MvPowerSeries (Fin 2) R)) := fun k =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hA : MvPowerSeries.HasSubst
      (fun _ : Unit => (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hq : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin d =>
      MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) R)) (ga q.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q =>
      MvPowerSeries.constantCoeff_subst_eq_zero (hX q.1) (fun _ => by simp) (h0 q.2))
  unfold addDefect
  rw [map_sub, MvPowerSeries.map_subst hq, MvPowerSeries.map_subst hA]
  simp only [MvPowerSeries.map_subst (hX _), map_add (f := _), MvPowerSeries.map_X]
  rfl

theorem map_cob (ψ : R →+* S) (F : Fin d → PS R 2 d) (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0)
    (b : PS R 1 d) :
    MvPowerSeries.map ψ (cob F b) = cob (fun i => MvPowerSeries.map ψ (F i)) (MvPowerSeries.map ψ b) := by
  unfold cob
  rw [map_sub, map_sub,
    map_ev' ψ _ (by intro j k; fin_cases j; exact cz_add F hF _ _ (cz_pt _) (cz_pt _) k),
    map_ev' ψ _ (by intro j k; fin_cases j; exact cz_pt _ k),
    map_ev' ψ _ (by intro j k; fin_cases j; exact cz_pt _ k),
    mp_cons, mp_cons, mp_cons, mp_nil, mp_add ψ _ _ _ (cz_pt _) (cz_pt _), mp_pt, mp_pt]

theorem map_cubicalTermLinearAlongTangent (ψ : R →+* S) (ph2 : PS R 3 d) (u : Fin d → R) :
    MvPowerSeries.map ψ (c2 ph2 u) = c2 (MvPowerSeries.map ψ ph2) (fun i => ψ (u i)) := by
  ext mu
  rw [MvPowerSeries.coeff_map]
  change ψ (∑ i : Fin d, _) = ∑ i : Fin d, _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPowerSeries.coeff_map]

theorem map_map {T σ : Type} [CommRing T] (ψ : R →+* S) (χ : S →+* T) (f : MvPowerSeries σ R) :
    MvPowerSeries.map (χ.comp ψ) f = MvPowerSeries.map χ (MvPowerSeries.map ψ f) := by
  ext mu
  simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]

end Ring

theorem exists_lift {C : Type} [Field C] (V : VF C) {σ : Type} (f : MvPowerSeries σ C)
    (hf : ∀ mu, V.Ge 0 (MvPowerSeries.coeff mu f)) :
    ∃ g : MvPowerSeries σ V.RR, MvPowerSeries.map V.RR.subtype g = f :=
  ⟨fun mu => ⟨MvPowerSeries.coeff mu f, hf mu⟩, by ext mu; rfl⟩

theorem degenerate_of_not_ndg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (d : ℕ) (Y : FBChart C V O d) (R₀ : Type) [CommRing R₀] (j : R₀ →+* V.RR) (F : Fin d → PS R₀ 2 d) (ph2 : PS R₀ 3 d), (∀ i, MvPowerSeries.constantCoeff (F i) = 0) → (∀ i, Y.B.G.F i = MvPowerSeries.map (V.RR.subtype.comp j) (F i)) → Y.B.ph2 = MvPowerSeries.map (V.RR.subtype.comp j) ph2 → ∀ (Ω : Type) [Field Ω] (ρ : V.RR →+* Ω), (∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C)) → ¬ NDG Y → Degenerate V.l (fun i => MvPowerSeries.map (ρ.comp j) (F i)) (MvPowerSeries.map (ρ.comp j) ph2) := by
  intro C _ _ V O _ _ d Y R₀ _ j F ph2 hF0 hF hph Ω _ ρ hρ hN
  unfold NDG at hN
  push Not at hN
  obtain ⟨ga, hcv, ⟨i₀, hi₀⟩, hadd, b, hb, hcob⟩ := hN
  have hlift : ∀ i, ∃ g : PowerSeries V.RR, PowerSeries.map V.RR.subtype g = ga i := fun i =>
    ⟨PowerSeries.mk fun n => ⟨PowerSeries.coeff n (ga i), (hcv i).2 n⟩, by ext n; simp⟩
  choose g hg using hlift
  obtain ⟨bR, rfl⟩ := exists_lift V b hb
  obtain rfl : ga = fun i => PowerSeries.map V.RR.subtype (g i) := funext fun i => (hg i).symm
  have hg0 : ∀ i, PowerSeries.constantCoeff (g i) = 0 := fun i => by
    have := (hcv i).1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    exact Subtype.ext this
  have hFR : Y.B.G.F = fun i => MvPowerSeries.map V.RR.subtype (MvPowerSeries.map j (F i)) :=
    funext fun i => by rw [hF i, map_map]
  have hFR0 : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.map j (F i)) = 0 := fun i => by
    rw [MvPowerSeries.constantCoeff_map, hF0 i, map_zero]
  rw [map_map] at hph
  simp only [map_map]
  refine ⟨fun i => PowerSeries.map ρ (g i), fun i => ?_, ⟨i₀, ?_⟩, fun i mu h0 h1 => ?_,
    MvPowerSeries.map ρ bR, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0 i, map_zero]
  · rw [PowerSeries.coeff_map] at hi₀ ⊢
    exact fun h => hi₀ ((hρ _).1 h)
  · have h : V.MM (MvPowerSeries.coeff mu (addDefect Y.B.G.F (fun i => PowerSeries.map V.RR.subtype (g i)) i)) :=
      hadd i mu h0 h1
    rw [hFR, ← map_addDefect V.RR.subtype _ g hg0 i, MvPowerSeries.coeff_map] at h
    change MvPowerSeries.coeff mu (addDefect (fun i => MvPowerSeries.map ρ (MvPowerSeries.map j (F i)))
      (fun i => PowerSeries.map ρ (g i)) i) = 0
    rw [← map_addDefect ρ _ g hg0 i, MvPowerSeries.coeff_map]
    exact (hρ _).2 h
  · change _ = cob (fun i => MvPowerSeries.map ρ (MvPowerSeries.map j (F i))) (MvPowerSeries.map ρ bR)
    simp only [PowerSeries.coeff_map]
    rw [← map_cob ρ _ hFR0, ← map_cubicalTermLinearAlongTangent, ← sub_eq_zero, ← map_sub]
    ext mu
    have h : V.MM (MvPowerSeries.coeff mu (c2 Y.B.ph2 (fun i => PowerSeries.coeff 1
        (PowerSeries.map V.RR.subtype (g i))) - cob Y.B.G.F (MvPowerSeries.map V.RR.subtype bR))) := hcob mu
    simp only [PowerSeries.coeff_map] at h
    rw [hFR, hph, ← map_cob V.RR.subtype _ hFR0, ← map_cubicalTermLinearAlongTangent, ← map_sub, MvPowerSeries.coeff_map] at h
    rw [MvPowerSeries.coeff_map, map_zero]
    exact (hρ _).2 h

end GlobalTheory.AlphaPair.Reduce
end
end

