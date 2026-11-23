module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

section RationalValues

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem le_iff_of_pow_eq_zpow {t a b : Γ} (h0 : 0 < t) (h1 : t < 1) {n n' : ℕ} (hn : 0 < n)
    (hn' : 0 < n') {m m' : ℤ} (ha : a ^ n = t ^ m) (hb : b ^ n' = t ^ m') :
    b ≤ a ↔ (m : ℚ) / n ≤ (m' : ℚ) / n' := by
  have e1 : a ^ (n * n') = t ^ (m * n') := by rw [pow_mul, ha, zpow_mul, zpow_natCast]
  have e2 : b ^ (n * n') = t ^ (m' * n) := by rw [mul_comm n, pow_mul, hb, zpow_mul, zpow_natCast]
  rw [← pow_le_pow_iff_left₀ zero_le' zero_le' (Nat.mul_pos hn hn').ne', e1, e2,
    zpow_le_zpow_iff_right_of_lt_one₀ h0 h1, div_le_div_iff₀ (by exact_mod_cast hn)
      (by exact_mod_cast hn')]
  norm_cast

theorem exists_ratAddValuation_of_pow_eq_zpow {F : Type*} [Field F] (w : Valuation F Γ) {t : Γ}
    (h0 : 0 < t) (h1 : t < 1) (h : ∀ x : F, x ≠ 0 → ∃ (n : ℕ) (m : ℤ), 0 < n ∧ w x ^ n = t ^ m) :
    ∃ v : AddValuation F (WithTop ℚ), ∀ (x : F) (m : ℤ), w x = t ^ m →
      v x = ((m : ℚ) : WithTop ℚ) := by
  classical
  choose! n m hn hnm using h
  let f : F → WithTop ℚ := fun x => if x = 0 then ⊤ else (((m x : ℚ) / n x : ℚ) : WithTop ℚ)
  have f0 : f 0 = ⊤ := if_pos rfl
  have key : ∀ (x : F) (a : ℕ) (b : ℤ), 0 < a → w x ^ a = t ^ b →
      f x = (((b : ℚ) / a : ℚ) : WithTop ℚ) := by
    intro x a b ha hab
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_pow ha.ne'] at hab
      exact (zpow_pos h0 b).ne hab
    simp only [f, if_neg hx, WithTop.coe_inj]
    exact le_antisymm ((le_iff_of_pow_eq_zpow h0 h1 (hn x hx) ha (hnm x hx) hab).1 le_rfl)
      ((le_iff_of_pow_eq_zpow h0 h1 ha (hn x hx) hab (hnm x hx)).1 le_rfl)
  have mono : ∀ x y : F, w y ≤ w x → f x ≤ f y := by
    intro x y hxy
    by_cases hy : y = 0
    · rw [hy, f0]; exact le_top
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero, le_zero_iff, Valuation.zero_iff] at hxy
      exact hy hxy
    simp only [f, if_neg hx, if_neg hy, WithTop.coe_le_coe]
    exact (le_iff_of_pow_eq_zpow h0 h1 (hn x hx) (hn y hy) (hnm x hx) (hnm y hy)).1 hxy
  refine ⟨AddValuation.of f f0 ?_ ?_ ?_, fun x b hb => ?_⟩
  · rw [key 1 1 0 one_pos (by simp)]
    simp
  · intro x y
    rcases le_max_iff.1 (w.map_add x y) with h | h
    · exact min_le_of_left_le (mono _ _ h)
    · exact min_le_of_right_le (mono _ _ h)
  · intro x y
    by_cases hx : x = 0
    · rw [hx, MulZeroClass.zero_mul, f0, top_add]
    by_cases hy : y = 0
    · rw [hy, MulZeroClass.mul_zero, f0, add_top]
    have hx' := hn x hx
    have hy' := hn y hy
    rw [key (x * y) (n x * n y) (m x * n y + m y * n x) (Nat.mul_pos hx' hy') (by
      rw [map_mul, mul_pow, pow_mul, mul_comm (n x), pow_mul, hnm x hx, hnm y hy,
        zpow_add₀ h0.ne', zpow_mul, zpow_mul, zpow_natCast, zpow_natCast])]
    simp only [f, if_neg hx, if_neg hy, ← WithTop.coe_add, WithTop.coe_inj]
    have : (n x : ℚ) ≠ 0 := by exact_mod_cast hx'.ne'
    have : (n y : ℚ) ≠ 0 := by exact_mod_cast hy'.ne'
    push_cast
    field_simp
  · change f x = _
    rw [key x 1 b one_pos (by simpa using hb)]
    simp

theorem exists_valuation_pow_eq_of_isAlgebraic {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Valuation F Γ) {x : F} (hx : IsAlgebraic K x) (hx0 : x ≠ 0) :
    ∃ (n : ℕ) (c : K), 0 < n ∧ c ≠ 0 ∧ w x ^ n = w (algebraMap K F c) := by
  classical
  obtain ⟨p, hp0, hp⟩ := hx
  let g : ℕ → F := fun i => algebraMap K F (p.coeff i) * x ^ i
  have hsum : ∑ i ∈ p.support, g i = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hp
    exact hp
  have hc : ∀ i ∈ p.support, w (algebraMap K F (p.coeff i)) ≠ 0 := fun i hi => by
    simpa using hi
  have hw : w x ≠ 0 := by simpa using hx0
  have aux : ∀ i ∈ p.support, ∀ j ∈ p.support, j < i → w (g i) = w (g j) →
      ∃ (n : ℕ) (c : K), 0 < n ∧ c ≠ 0 ∧ w x ^ n = w (algebraMap K F c) := by
    intro i hi j hj hji e
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hji
    refine ⟨d + 1, p.coeff j / p.coeff (j + d + 1), Nat.succ_pos d,
      div_ne_zero (Polynomial.mem_support_iff.1 hj) (Polynomial.mem_support_iff.1 hi), ?_⟩
    simp only [g, map_mul, map_pow] at e
    rw [map_div₀, map_div₀, eq_div_iff (hc _ hi)]
    apply mul_right_cancel₀ (pow_ne_zero j hw)
    rw [← e, _root_.add_assoc j, pow_add (w x) j]
    ac_rfl
  obtain ⟨i, hi, hmax⟩ := p.support.exists_max_image (fun i => w (g i))
    (Polynomial.support_nonempty.2 hp0)
  by_contra hne
  have hlt : ∀ j ∈ p.support \ {i}, w (g j) < w (g i) := by
    intro j hj
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    refine lt_of_le_of_ne (hmax j hj.1) fun e => hne ?_
    rcases lt_or_gt_of_ne hj.2 with h | h
    · exact aux i hi j hj.1 h e.symm
    · exact aux j hj.1 i hi h e
  have hgi : w (g i) ≠ 0 := by
    simp only [g, map_mul, map_pow]
    exact mul_ne_zero (hc i hi) (pow_ne_zero i hw)
  have := w.map_sum_eq_of_lt hi hlt
  rw [hsum, map_zero] at this
  exact hgi this.symm

end RationalValues

theorem exists_valOver_of_isAlgebraic {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) (F : Type) [Field F]
    [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] :
    ∃ v : AddValuation F (WithTop ℚ), ValOver ϖ F v := by
  let K := FractionRing V
  let f : V →+* F := (algebraMap K F).comp (algebraMap V K)
  have hf : Function.Injective f := (algebraMap K F).injective.comp (IsFractionRing.injective V K)
  obtain ⟨W, hW⟩ := (LocalSubring.range f).exists_le_valuationSubring
  obtain ⟨hW1, hW2⟩ := (localSubring_range_le_valuationSubring_iff f W).1 hW
  let w := W.valuation
  have h0 : 0 < w (f ϖ) := by
    rw [Valuation.pos_iff]
    exact (map_ne_zero_iff _ hf).2 hϖ.ne_zero
  have h1 : w (f ϖ) < 1 := (W.mem_nonunits_iff).1 (hW2 ϖ hϖ.not_isUnit)
  have hu : ∀ u : Vˣ, w (f u) = 1 := fun u =>
    W.valuation_unit (Units.map (f.codRestrict W hW1 : V →* W) u)
  have hval : ∀ (c : K) (n : ℤ), HasVal ϖ c n → w (algebraMap K F c) = w (f ϖ) ^ n := by
    rintro c n ⟨u, rfl⟩
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀]
    change w (f ϖ) ^ n * w (f u) = _
    rw [hu, _root_.mul_one]
  obtain ⟨v, hv⟩ := exists_ratAddValuation_of_pow_eq_zpow w h0 h1 fun x hx => by
    obtain ⟨n, c, hn, hc, e⟩ := exists_valuation_pow_eq_of_isAlgebraic (K := K) w
      (Algebra.IsAlgebraic.isAlgebraic x) hx
    obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hc
    exact ⟨n, m, hn, e.trans (hval c m hm)⟩
  exact ⟨v, fun c n hc => hv _ n (hval c n hc)⟩

theorem exists_complete_discreteValuationRing_map_le {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊤) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V),
      IsAdicComplete (maximalIdeal V) V ∧ Function.Injective φ ∧ I.map φ ≤ maximalIdeal V := by
  by_cases h : I = ⊥
  · let K := FractionRing R
    refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance,
      (PowerSeries.C (R := K)).comp (algebraMap R K), ?_,
      PowerSeries.C_injective.comp (IsFractionRing.injective R K), by simp [h]⟩
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  · obtain ⟨p, hp, hIp⟩ := I.exists_le_maximal hI
    have := hp.isPrime
    obtain ⟨O, _, _, _, hO, φ, h1, h2⟩ := exists_complete_discreteValuationRing_of_prime_lt
      (⊥ : Ideal R) p (lt_of_lt_of_le (bot_lt_iff_ne_bot.2 h) hIp)
    exact ⟨O, inferInstance, inferInstance, inferInstance, φ, hO,
      (RingHom.injective_iff_ker_eq_bot φ).2 h1, Ideal.map_le_iff_le_comap.2 (h2 ▸ hIp)⟩

theorem adic_base_embeds_valuation_algebraic_closure :
    (∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V), IsAdicComplete (maximalIdeal V) V ∧ Function.Injective φ ∧ I.map φ ≤ maximalIdeal V) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∃ v : AddValuation (AlgebraicClosure (FractionRing V)) (WithTop ℚ), ValOver ϖ (AlgebraicClosure (FractionRing V)) v := by
  refine ⟨fun R _ _ _ I hR => ?_, fun V _ _ _ ϖ hϖ => exists_valOver_of_isAlgebraic hϖ _⟩
  obtain ⟨hN, -, -, hc⟩ := hR
  refine exists_complete_discreteValuationRing_map_le ?_
  rintro rfl
  exact not_subsingleton R (IsHausdorff.subsingleton hc.toIsHausdorff)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitAgreeOfIsPullUnif
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


set_option maxHeartbeats 6400000 in
theorem arcWit_agree_of_isPullUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left), g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) → W.Agree W' ψ := by
  intro E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' hD₂ ⟨hφe, hee, w₂, hwe, T₂⟩ ψ bc hψ _ hbc hPU₂
    hact h3
  have he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G := by
    rw [Category.id_comp]
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ψ.hom)
  obtain ⟨wL₂, g₂, he₂, m₂, lev₂⟩ := hPU₂.lg
  have pg₂ := (isGen_iff wL₂).1 g₂
  refine ⟨hψ, hact, h3, he, pullCongr hbc wL₂,
    (isGen_iff _).2 (pgen_pullCongr hbc pg₂), ?_, fun n ψn hψn => ?_⟩
  · have HA := (maps_iff wL₂ _ (fun _ => eSec W'.t.G) _ W.P.U.LG.rig W'.P.U.LG.rig
      (Out.specOf (RingHom.id (PowerSeries k))) _ (rigPull_le _ _ he₂ W'.P.U.LG.L) (fun _ => rfl)).1 m₂
    have e0 : Out.specOf (RingHom.id (PowerSeries k)) = 𝟙 (𝟙_ (Over (Sp (PowerSeries k)))).left := by
      simp [Out.specOf]
    have HB : PMaps wL₂ (fun _ : PUnit => eSec W.t.G) (fun _ => eSec W'.t.G) (fun _ => 1) W.P.U.LG.rig W'.P.U.LG.rig
        (𝟙 _) := e0 ▸ HA
    exact (maps_iff (pullCongr hbc wL₂) _ (fun _ => eSec W'.t.G) _ W.P.U.LG.rig W'.P.U.LG.rig (𝟙 _) _
      (rigPull_le _ _ he W'.P.U.LG.L) (fun _ => rfl)).2 (pmaps_pullCongr hbc HB)
  · obtain ⟨h₂, hh₁, hh₂, ht₂, hw₂⟩ := lev₂ n
    have hfst : h₂ ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left =
        (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left ≫ ψ.hom.left := by
      rw [hh₁, hbc]
    obtain rfl : h₂ = ψn := by rw [hψn]; exact thick_map_eq ψ.hom h₂ hfst
    refine ⟨?_, fun A _ _ v => ⟨fun x pt₀ t₀ _ hg => ?_, fun j₀ jM jM' jL jL' H1 H2 H3 => ?_⟩⟩
    · exact (congrArg (fun f => (W.P.U.gt n).pG.left ≫ f) hφe.symm).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ W'.φ) hh₂)).trans (Category.assoc _ _ _))
    · obtain ⟨hψ₂, hm₂⟩ := ht₂ (W.e x)
      have P₂ := (maps_iff hD₂.w _ _ _ ((W.P.U.gt n).t (W.e x)) ((W'.P.U.gt n).t (hD₂.xe (W.e x))) h₂ _
        (Out.GeneratorPullback.pullAlong_le _ _ _ _ _ hψ₂) (fun _ => rfl)).1 hm₂
      have Q₂ := genRelR_transfer T₂ W'.P.D.toPre.P.isLB W.P.D.toPre.P.isLB
        (fun k => by rw [Category.assoc, hψ₂ k, Category.id_comp, Category.assoc])
        (pmaps_pullGen P₂ v (v ≫ h₂) rfl) t₀
      have Q₃ := genRelR_heq hφe hwe (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) v) t₀
      rw [← hee x]
      exact Q₂.2 (Q₃.2 hg)
    · have m1 := (top_le_iff_cpt _ _).1 H1
      have m2 := (top_le_iff_cpt _ _).1 H2
      have m3 := (top_le_iff_cpt _ _).1 H3
      have p2 : (v ≫ (W.P.U.gt n).pG.left) ≫ hD₂.e.hom.left ≫
          pullback.fst W'.P.D.toPre.P.A.hom (Out.specOf (RingHom.id (PowerSeries k))) =
          v ≫ h₂ ≫ (W'.P.U.gt n).pG.left := by rw [Category.assoc, hh₂]
      have p3 : (v ≫ h₂) ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left =
          (v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) ≫ ψ.hom.left := by
        rw [Category.assoc, hfst, Category.assoc]
      have e2 := congrArg (fun g => g (cpt A)) p2
      have e3 := congrArg (fun g => g (cpt A)) p3
      simp only at e2 e3
      have hjM := m1.2
      have mB1 : W'.φ ((hD₂.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom
          (Out.specOf (RingHom.id (PowerSeries k)))) ((v ≫ (W.P.U.gt n).pG.left) (cpt A))) ∈ a.D₀.P.L.U j₀ := by
        have := mem_pull.1 m2.1; rw [← e2] at this; exact this
      have mB2 : (hD₂.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (Out.specOf (RingHom.id (PowerSeries k))))
          ((v ≫ (W.P.U.gt n).pG.left) (cpt A)) ∈ W'.P.D.toPre.P.L.U jM' := by
        have := m2.2; rw [← e2] at this; exact this
      have mC1 := mem_pull.1 m3.1
      have mC2 := m3.2
      have mC3 : (bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id (PowerSeries k))))
          ((v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) (cpt A)) ∈ W'.P.U.LG.L.U jL' := by
        rw [hbc]; exact mC1
      have mD : (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left ((v ≫ h₂) (cpt A)) ∈ W'.P.U.LG.L.U jL' := by
        have e3' : (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left ((v ≫ h₂) (cpt A)) =
            ψ.hom.left ((v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) (cpt A)) := e3
        rw [e3']; exact mC1
      have R2 := T₂ _ (v ≫ (W.P.U.gt n).pG.left) (cpt A) j₀ jM' jM mB1 mB2 hjM
      rw [p2] at R2
      have RE := gw_heq hφe hwe (v ≫ (W.P.U.gt n).pG.left) (cpt A) j₀ jM
      have RU2 : gw hD₂.w (v ≫ (W.P.U.gt n).pG.left) (cpt A) jM' jM *
          gm v (cpt A) _ ((W.P.U.w n).s (fun _ => jM, fun _ => jL)) =
          gm (v ≫ h₂) (cpt A) _ ((W'.P.U.w n).s (fun _ => jM', fun _ => jL')) *
          gw wL₂ (v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) (cpt A) jL' jL := by
        have := gm_of_res_eq' (hw₂ (fun _ => jM') jM jL (fun _ => jL')) v (y := cpt A)
          ⟨⟨⟨⟨mem_pull.2 mB2, hjM⟩, ⟨mem_pull.2 hjM, mem_pull.2 mC2⟩⟩, ⟨mem_pull.2 m2.2, mem_pull.2 mD⟩⟩,
            ⟨mem_pull.2 mC3, mC2⟩⟩
        rw [gm_pull, gm_pull, gm_pull] at this
        · exact this
        · exact ⟨mem_pull.2 mC3, mC2⟩
        · exact ⟨mem_pull.2 m2.2, mem_pull.2 mD⟩
        · exact ⟨mem_pull.2 mB2, hjM⟩
      have EU := congrArg (· * gm v (cpt A) _ ((W.P.U.w n).s (fun _ => jM, fun _ => jL))) (RE.symm.trans R2)
      beta_reduce at EU
      rw [_root_.mul_assoc, RU2, ← _root_.mul_assoc, ← gw_pullCongr hbc wL₂] at EU
      apply toStkA_injective
      rw [map_mul, map_mul, map_mul, toStkA_valR, toStkA_valR, toStkA_valR, toStkA_valR, toStkA_valR]
      · have EU' := congrArg Units.val EU
        simp only [Units.val_mul] at EU'
        exact EU'
      all_goals first
        | exact H1
        | exact H2
        | exact H3
        | exact (top_le_iff_cpt _ _).2 ⟨mem_pull.2 m2.2, mem_pull.2 mD⟩
        | exact (top_le_iff_cpt _ _).2 ⟨mem_pull.2 m1.2, mem_pull.2 mC2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcNotAbelian

theorem isProper_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (K : Type) [Field K]
    (t : Spec (CommRingCat.of K) ⟶ S) (p : Spec (CommRingCat.of K)) (hp : t p ∈ abLocus G) :
    IsProper (pullback.snd G.hom t) := by
  let K' := AlgebraicClosure K
  let u : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have q : Spec (CommRingCat.of K') := (default : PrimeSpectrum K')
  have : Nonempty (Spec (CommRingCat.of K')) := ⟨q⟩
  have h₁ : IsProper (pullback.snd G.hom (u ≫ t)) :=
    hp K' (u ≫ t) ⟨q, congrArg (fun z => t z) (Subsingleton.elim (u q) p)⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have h₂ : UniversallyClosed (pullback.snd (pullback.snd G.hom t) u) := by
    rw [← P.isoPullback_hom_snd]; infer_instance
  have hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t) :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu h₂
  have := hG.separated
  have := hG.smooth
  exact ⟨⟩


open TorusToProper in
theorem subsingleton_of_mono (K : Type) [Field K] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Spec (CommRingCat.of K))) [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of K)) X ⟶ B) (hf : IsMonHom f) [Mono f] :
    Subsingleton X := by
  have h := splitTorus_hom_proper_trivial_field K X B f hf
  have e : ptFun K X (AddMonoidAlgebra K X) (univ K X) = ptFun K X (AddMonoidAlgebra K X) 1 := by
    rw [← cancel_mono f, h, ← Category.assoc, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  have e₂ := (ptFun_fst K X _ (univ K X)).symm.trans
    ((congrArg (fun z => z.left ≫ Rosenlicht.torusFst _ X) e).trans (ptFun_fst K X _ 1))
  have e₃ : charRing X _ (univ K X) = charRing X (AddMonoidAlgebra K X) 1 :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective e₂)
  have key : ∀ a : X, (AddMonoidAlgebra.single a 1 : AddMonoidAlgebra K X) = 1 := by
    intro a
    have := congrArg (fun φ => φ (AddMonoidAlgebra.single a 1)) e₃
    simp only [charRing_single] at this
    simpa [univ] using this
  exact ⟨fun a b => AddMonoidAlgebra.single_left_injective (one_ne_zero (α := K)) ((key a).trans (key b).symm)⟩

theorem subsingleton_of_mem_abLocus {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    (A : Type) [CommRing A] (hA : IsField A) (t : Spec (CommRingCat.of A) ⟶ S) (p : Spec (CommRingCat.of A))
    (hp : t p ∈ abLocus G) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ (Over.pullback t).obj G) (hf : IsMonHom f) [Mono f] :
    Subsingleton X := by
  letI := hA.toField
  have : IsProper ((Over.pullback t).obj G).hom := isProper_fibre G hG A t p hp
  exact subsingleton_of_mono A X _ f hf

end ArcNotAbelian


open ArcNotAbelian in
theorem arcWit_mem_range_jK_of_mem_range_j : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (χ : Sp (PowerSeries k) ⟶ Y.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (x : Sp (PowerSeries k)), χ x ∈ Set.range Y.j → x ∈ Set.range (jK (PowerSeries k)) := by
  intro E _ _ _ H D l Xo c k _ bF a O _ β Y χ W x hx
  refine mem_range_jK x fun hX => ?_
  have h₁ : χ x ∈ abLocus Y.t.G := by
    obtain ⟨p, hp⟩ := hx
    have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    rw [← hp]
    exact hz
  have h₂ : x ∈ abLocus W.t.G := (abLocus_pullback abLocusOne Y.t.semi W.m.cart.1 x).1 h₁
  have hmax : (Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one, ← PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have hF : IsField (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hle : Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1) ≤ x.asIdeal := by
    rw [zero_add, pow_one, Ideal.span_le, Set.singleton_subset_iff]; exact hX
  obtain ⟨p, hp⟩ : x ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  let g := W.P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hp' : thick (PowerSeries k) (Ideal.span {PowerSeries.X}) 0 p ∈ abLocus W.t.G := by
    rw [← hp] at h₂; exact h₂
  have hs := subsingleton_of_mem_abLocus W.t.G W.t.semi _ hF _ p hp' W.P.D.toPre.X g.i g.i_hom
  have hn : Nontrivial (a.restrict β).D₀.X := (a.restrict β).nontriv
  exact not_subsingleton _ (W.e.toEquiv.subsingleton)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoefFe
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefFE
open GlobalTheory.UT.CoefBasic

theorem coef_fe : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (y : D.X) (h o : GtPtF D F), GtPtF.IsIota y h → o.IsZero → ∀ (w : Frm D F k h.b) (w₁ : Frm D F k o.b), w.IsGen → FrmOne w₁ → (∀ z J, Good D.P.L z J → val w (𝟙 _) z J = (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi y) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) ^ k) → ∀ (s : Fam D F k) (α : D.X), coef s o w₁ (α + k • y) = coef s h w α := by
  intro hL R _ _ D F _ _ k y h o hh ho w w₁ hw hw₁ vw s α
  obtain ⟨hb, hs⟩ := (isIota_iff _ _).1 hh
  obtain ⟨ob, os⟩ := (isZero_iff _).1 ho
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := F) hL.1.globalFns k y α
  refine coef_eq fun z J hJ => ?_
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe y α u hu hc) _ (DegPre.zF D F).left z J hJ
  have u₀ := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at u₀
  have m := val_famMult (𝟙 (TF (R := R) F)) hJ k y α
  have p₁ : val (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J =
      val (D.psi y) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J ^ k := map_pow _ _ _
  have p₂ : val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J =
      val D.rigK ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J ^ k := map_pow _ _ _
  rw [p₁, p₂, Over.id_left, Category.id_comp] at m
  have r : val D.rigK (jFK (R := R) F) z J = rigV D (TF (R := R) F).hom z J := val_pull hJ _ _ _
  have z₁ : lift (𝟙 (TF (R := R) F)) o.b = DegPre.zF D F := by rw [ob]; rfl
  have z₂ : DegPre.zF D F ≫ DegPre.trF D F y = lift (𝟙 (TF (R := R) F)) h.b := by
    have a₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
    have a₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
    rw [trF_eq]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, a₁, lift_fst]
    · rw [lift_snd, hb, Category.assoc]
      refine (congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_
      rw [MonObj.comp_mul, a₂, ← Category.assoc, a₁, Category.id_comp, _root_.one_mul]
  rw [← Over.comp_left, z₂, u₀] at e
  have t := hs α z J hJ
  rw [Category.id_comp] at t
  rw [isCoef_coef h hw α s z J hJ, z₁, e, os _ z J hJ, hw₁.2 z J hJ, t, vw z J hJ]
  have m' := congrArg Units.val m
  rw [r] at m'
  simp only [Units.val_one, _root_.mul_one, id, mul_pow, _root_.mul_assoc]
  exact congrArg₂ (· * ·) rfl m'.symm

end GlobalTheory.UT.CoefFE
end
end

