module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

theorem zeta_eq_pow_div_of_dvd {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : zeta a = zeta b ^ (b / a) := by
  obtain ⟨c, rfl⟩ := h
  have ha : 0 < a := Nat.pos_of_mul_pos_right hb
  have hc : 0 < c := Nat.pos_of_mul_pos_left hb
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  rw [Nat.mul_div_cancel_left c ha, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem levelField_le_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [zeta_eq_pow_div_of_dvd l₂.A_pos h]
    exact pow_mem (IntermediateField.subset_adjoin ℚ ({H.rt0, zeta l₂.A} : Set ℂ) (by simp)) _

def baseOfFinerLevel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := (baseKA l₂).ρ
  ρ_sq := (baseKA l₂).ρ_sq
  ζ := IntermediateField.inclusion (levelField_le_of_dvd h) (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective (IntermediateField.inclusion_injective (levelField_le_of_dvd h))

def levelFieldIncl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : KA l →+* KA l₂ :=
  (IntermediateField.inclusion (levelField_le_of_dvd h)).toRingHom

theorem coe_levelFieldIncl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) (x : KA l) : ((levelFieldIncl h x : KA l₂) : ℂ) = (x : ℂ) :=
  IntermediateField.coe_inclusion (levelField_le_of_dvd h) x

theorem coe_baseKA_rho {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem levelFieldIncl_rho {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : levelFieldIncl h (baseKA l).ρ = (baseOfFinerLevel h).ρ :=
  Subtype.ext ((coe_levelFieldIncl h _).trans ((coe_baseKA_rho l).trans (coe_baseKA_rho l₂).symm))

theorem levelFieldIncl_zeta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : levelFieldIncl h (baseKA l).ζ = (baseOfFinerLevel h).ζ := rfl

theorem baseOfFinerLevel_rho {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : (baseOfFinerLevel h).ρ = (baseKA l₂).ρ := rfl

theorem baseOfFinerLevel_zeta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : (baseOfFinerLevel h).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, ← levelFieldIncl_zeta, coe_levelFieldIncl]
  exact zeta_eq_pow_div_of_dvd l₂.A_pos h

theorem exists_sabMap_of_base_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f g : S' ⟶ S} (n : SABMap t' t f) (h : f = g) :
    ∃ n' : SABMap t' t g, n'.φ = n.φ := by
  subst h
  exact ⟨n, rfl⟩

theorem exists_levelMap : (∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∃ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) := by
  intro hsm _ hlow hrep E _ _ _ H D l l₂ Xo Xo₂ _ hd
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨o, m₁, h₁, h₁A⟩ := hlow E H D l l₂ (KA l₂) (baseOfFinerLevel hA) (baseKA l₂) Xo₂.X Xo₂.s Xo₂.univ hd
    (baseOfFinerLevel_rho hA) (baseOfFinerLevel_zeta hA)
  have hred : IsReduced Xo₂.X := by
    have := Xo₂.smooth
    exact (hsm _ _ Xo₂.s (SmoothOfRelativeDimension.smooth D.dim Xo₂.s)).1
  obtain ⟨r, ⟨hr, ⟨m₂⟩⟩, -⟩ := hrep E H D l Xo (KA l₂) (baseOfFinerLevel hA) (levelFieldIncl hA) Xo₂.X Xo₂.s o hred
    (levelFieldIncl_rho hA) (levelFieldIncl_zeta hA)
  obtain ⟨m, hm⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₂.toSABMap m₁
  obtain ⟨n, hn⟩ := exists_sabMap_of_base_eq m (Category.id_comp r)
  have hφ : n.φ = m₁.φ ≫ m₂.toSABMap.φ := hn.trans hm
  refine ⟨r, levelFieldIncl hA, n, coe_levelFieldIncl hA, hr, fun a => ?_, fun a => ?_⟩
  · exact (congrArg (_ ≫ ·) hφ).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ m₂.toSABMap.φ) ((h₁ a).trans (Category.id_comp _))).trans (m₂.eta a)))
  · exact (congrArg (_ ≫ ·) hφ).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ m₂.toSABMap.φ) ((h₁A a).trans (Category.id_comp _))).trans (m₂.etaA a)))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelPeriod

open GlobalTheory.SiegelNormalForm Matrix

theorem exists_siegel_form : ∀ (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ a b, EF (bas a) (bas b) = omegaStd a b) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → ∃ h τ : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ h⁻¹ = (Matrix.of fun i j => Q (bas (Pi.single (.inr j) 1)) i) ∧ τ = h * (Matrix.of fun i j => Q (bas (Pi.single (.inl j) 1)) i) ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ z w, hermForm Hm z w = hermForm (((τ.map Complex.im)⁻¹).map Complex.ofReal) (h.mulVec z) (h.mulVec w)) ∧ ∀ a, h.mulVec (Q (bas a)) = τ.mulVec (fun i => (a (.inl i) : ℂ)) + fun i => (a (.inr i) : ℂ) := by
  intro La _ EF g bas Q Hm hbas ⟨_, _, _, hH, hpos, hE⟩
  unfold hermForm at hpos hE ⊢
  set e : Fin g → Fin g → ℂ := fun i => Q (bas (Pi.single (.inr i) 1)) with he
  set f : Fin g → Fin g → ℂ := fun i => Q (bas (Pi.single (.inl i) 1)) with hf
  have hee : ∀ i j, (e i ⬝ᵥ Hm *ᵥ star (e j)).im = 0 := fun i j => by
    simp only [he]
    rw [hE, hbas]; simp [omegaStd]
  have hff : ∀ i j, (f i ⬝ᵥ Hm *ᵥ star (f j)).im = 0 := fun i j => by
    simp only [hf]
    rw [hE, hbas]; simp [omegaStd]
  have hef : ∀ i j, (e i ⬝ᵥ Hm *ᵥ star (f j)).im = if i = j then -1 else 0 := fun i j => by
    simp only [he, hf]
    rw [hE, hbas]
    by_cases hij : i = j
    · subst hij; simp [omegaStd, Pi.single_apply]
    · simp [omegaStd, Pi.single_apply, hij, Ne.symm hij]
  let P : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k i => e i k
  let F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k i => f i k
  have hP : ∀ i, P *ᵥ Pi.single i 1 = e i := fun i => by
    ext k; simp [P]
  have hF : ∀ i, F *ᵥ Pi.single i 1 = f i := fun i => by
    ext k; simp [F]
  let Y : Matrix (Fin g) (Fin g) ℝ := (Pᵀ * Hm * P.map star).map Complex.re
  have hYe : ∀ i j, (Pᵀ * Hm * P.map star) i j = e i ⬝ᵥ Hm *ᵥ star (e j) := fun i j => by
    rw [← form_single (Pᵀ * Hm * P.map star), ← form_pull, hP, hP]
  have hY : Pᵀ * Hm * P.map star = Y.map (↑) := by
    ext i j
    apply Complex.ext
    · simp [Y]
    · rw [hYe, hee]; simp
  have hPu : IsUnit P := isUnit_of_lagrangian P Hm f hpos Y hY
    (fun i j => by rw [hP, hef])
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hPi : Function.Injective P.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hPu
  have hPP : ∀ z, P *ᵥ (P⁻¹ *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hPd, Matrix.one_mulVec]
  let τ : Matrix (Fin g) (Fin g) ℂ := P⁻¹ * F
  have hPτ : ∀ z, P *ᵥ (τ *ᵥ z) = F *ᵥ z := fun z => by
    rw [← Matrix.mulVec_mulVec, hPP]
  have hτ : ∀ j, P *ᵥ (τ *ᵥ Pi.single j 1) = f j := fun j => by
    rw [hPτ, hF]
  have hform : ∀ z w, (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (P *ᵥ w) = z ⬝ᵥ Y.map (↑) *ᵥ star w :=
    fun z w => by rw [form_pull, hY]
  have hYs : Yᵀ = Y := by
    ext i j
    have := congrArg Complex.re (form_conj hH (e i) (e j))
    simp only [Complex.star_def, Complex.conj_re] at this
    simp only [Y, Matrix.transpose_apply, Matrix.map_apply, hYe, this]
  have hYp : Y.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hYs) ?_
    intro a ha
    have hne : P *ᵥ (fun i => (a i : ℂ)) ≠ 0 := by
      intro h0
      have := hPi (h0.trans (Matrix.mulVec_zero P).symm)
      exact ha (funext fun i => by simpa using congrFun this i)
    have := hpos _ hne
    rw [hform] at this
    simpa [Matrix.mulVec, dotProduct] using this
  obtain ⟨hτs, hτp, hYτ⟩ := siegel_of_relations Y hYp τ
    (fun i j => by rw [← hform, hP, hτ, hef]) (fun i j => by rw [← hform, hτ, hτ, hff])
  have hYi : (τ.map Complex.im)⁻¹ = Y := Matrix.inv_eq_left_inv hYτ
  refine ⟨P⁻¹, τ, Matrix.isUnit_nonsing_inv_iff.2 hPu, Matrix.nonsing_inv_nonsing_inv P hPd, rfl,
    hτs, hτp, fun z w => ?_, fun a => hPi ?_⟩
  · rw [hYi, ← hform, hPP, hPP]
  · have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
      intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
    have h2 : a = ∑ i, a (.inl i) • Pi.single (.inl i) 1 + ∑ i, a (.inr i) • Pi.single (.inr i) 1 := by
      ext k; rcases k with k | k <;> simp [Finset.sum_apply, Pi.single_apply]
    rw [hPP, h1 (fun i => a (.inl i)), h1 (fun i => a (.inr i))]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, hP, hτ]
    conv_lhs => rw [h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_zsmul, he, hf]

end GlobalTheory.SiegelPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_smul_apply_eq_of_eq_on_invariants {G B D : Type*} [Group G] [Finite G] [CommRing B]
    [CommRing D] [IsDomain D] [MulSemiringAction G B] (x y : B →+* D)
    (h : ∀ b, (∀ g : G, g • b = b) → x b = y b) (b : B) : ∃ g : G, y b = x (g • b) := by
  classical
  have := Fintype.ofFinite G
  set P : Polynomial B := ∏ g : G, (Polynomial.X - Polynomial.C (g • b)) with hP
  have hinvP : ∀ k : G, k • P = P := by
    intro k
    rw [hP, Finset.smul_prod']
    exact Fintype.prod_bijective (k • ·) (MulAction.bijective k) _ _ (fun g => by
      rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul, smul_eq_mul])
  have hmap : P.map x = P.map y := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    apply h
    intro g
    rw [← Polynomial.coeff_smul, hinvP]
  have hb : P.eval b = 0 := by
    rw [hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
  have h0 : (P.map y).eval (y b) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hb, map_zero]
  rw [← hmap, Polynomial.eval_map, hP, Polynomial.eval₂_finsetProd] at h0
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h0
  obtain ⟨g, -, hg⟩ := Finset.prod_eq_zero_iff.mp h0
  exact ⟨g, sub_eq_zero.mp hg⟩

theorem exists_smul_eq_of_eq_on_invariants {G B D : Type*} [Group G] [Finite G] [CommRing B]
    [CommRing D] [IsDomain D] [MulSemiringAction G B] (x y : B →+* D)
    (h : ∀ b, (∀ g : G, g • b = b) → x b = y b) : ∃ g : G, ∀ b, y b = x (g • b) := by
  classical
  by_contra hne
  push Not at hne
  choose c hc using hne
  have := Fintype.ofFinite G
  let e := Fintype.equivFin G
  let p : Polynomial B := ∑ g : G, Polynomial.C (c g) * Polynomial.X ^ (e g : ℕ)
  have hcoef : ∀ g, p.coeff (e g) = c g := by
    intro g
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single g (fun g' _ hg' => if_neg (fun hh => hg' (e.injective (Fin.ext hh)).symm))
      (by simp), if_pos rfl]
  have hyp : ∀ q : Polynomial B, (∀ g : G, g • q = q) →
      Polynomial.mapRingHom x q = Polynomial.mapRingHom y q := by
    intro q hq
    ext n
    simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
    apply h
    intro g
    rw [← Polynomial.coeff_smul, hq]
  obtain ⟨g, hg⟩ := exists_smul_apply_eq_of_eq_on_invariants (G := G)
    (Polynomial.mapRingHom x) (Polynomial.mapRingHom y) hyp p
  have hgc := congrArg (fun q => q.coeff (e g)) hg
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_smul, hcoef] at hgc
  exact hc g hgc

theorem exists_aut_of_comp_eq_of_invariant {G : Type*} [Group G] [Finite G] {X X' T : Scheme.{0}}
    (ρ : G →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π)
    {W : X'.Opens} (hW : IsAffineOpen W)
    (hinv : ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    [IsAffine T] [IsIntegral T] (x y : T ⟶ X) (hxy : x ≫ π = y ≫ π)
    (hx : ⊤ ≤ x ⁻¹ᵁ π ⁻¹ᵁ W) : ∃ g, y = x ≫ (ρ g).asIso.hom := by
  have hU : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).asIso.hom ⁻¹ᵁ π ⁻¹ᵁ W := fun g => by
    show _ ≤ ((ρ g).asIso.hom ≫ π) ⁻¹ᵁ W
    rw [hπ g]
  let _ := sectionsAction ρ _ hU
  have hact : ∀ (g : G) (s : Γ(X, π ⁻¹ᵁ W)),
      g • s = (ρ g⁻¹).asIso.hom.appLE _ _ (hU g⁻¹) s := fun g s => rfl
  have hy : ⊤ ≤ y ⁻¹ᵁ π ⁻¹ᵁ W := by
    show ⊤ ≤ (y ≫ π) ⁻¹ᵁ W
    rw [← hxy]
    exact hx
  have key : ∀ (f f' : T ⟶ X') (_ : f = f') (h1 : ⊤ ≤ f ⁻¹ᵁ W) (h2 : ⊤ ≤ f' ⁻¹ᵁ W),
      f.appLE W ⊤ h1 = f'.appLE W ⊤ h2 := by
    rintro f f' rfl h1 h2
    rfl
  have hagree : ∀ s : Γ(X, π ⁻¹ᵁ W), (∀ g : G, g • s = s) →
      (x.appLE (π ⁻¹ᵁ W) ⊤ hx).hom s = (y.appLE (π ⁻¹ᵁ W) ⊤ hy).hom s := by
    intro s hs
    have hinv' : IsInvariantSection ρ _ s := by
      intro g
      refine ⟨hU g, ?_⟩
      have := hs g⁻¹
      rw [hact] at this
      simpa only [inv_inv] using this
    obtain ⟨t, rfl⟩ := hinv s hinv'
    have e1 := Scheme.Hom.comp_appLE x π W ⊤ hx
    have e2 := Scheme.Hom.comp_appLE y π W ⊤ hy
    have := congrArg (fun φ => φ.hom t) (key _ _ hxy hx hy)
    rw [e1, e2] at this
    exact this
  obtain ⟨g, hg⟩ := exists_smul_eq_of_eq_on_invariants (G := G) _ _ hagree
  refine ⟨g⁻¹, ?_⟩
  have h' : ⊤ ≤ (x ≫ (ρ g⁻¹).asIso.hom) ⁻¹ᵁ π ⁻¹ᵁ W := by
    show ⊤ ≤ x ⁻¹ᵁ ((ρ g⁻¹).asIso.hom ⁻¹ᵁ π ⁻¹ᵁ W)
    exact hx.trans (x.preimage_mono (hU g⁻¹))
  have heq : y.appLE (π ⁻¹ᵁ W) ⊤ hy = (x ≫ (ρ g⁻¹).asIso.hom).appLE (π ⁻¹ᵁ W) ⊤ h' := by
    ext s
    rw [← Scheme.Hom.appLE_comp_appLE x (ρ g⁻¹).asIso.hom _ _ _ (hU g⁻¹) hx]
    rw [hg s, hact]
    rfl
  have hA : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec y hA (isAffineOpen_top T) hy
  have h2 := IsAffineOpen.SpecMap_appLE_fromSpec (x ≫ (ρ g⁻¹).asIso.hom) hA (isAffineOpen_top T) h'
  rw [heq] at h1
  rw [IsAffineOpen.fromSpec_top] at h1 h2
  exact (cancel_epi _).1 (h1.symm.trans h2)

theorem isIntegralHom_of_invariant {G : Type*} [Group G] [Finite G] {X X' : Scheme.{0}}
    (ρ : G →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π)
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W)) : IsIntegralHom π := by
  rw [isIntegralHom_iff]
  refine ⟨inferInstance, fun W hW => ?_⟩
  have hU : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).asIso.hom ⁻¹ᵁ π ⁻¹ᵁ W := fun g => by
    show _ ≤ ((ρ g).asIso.hom ≫ π) ⁻¹ᵁ W
    rw [hπ g]
  let _ := sectionsAction ρ _ hU
  have hact : ∀ (g : G) (s : Γ(X, π ⁻¹ᵁ W)),
      g • s = (ρ g⁻¹).asIso.hom.appLE _ _ (hU g⁻¹) s := fun g s => rfl
  classical
  have := Fintype.ofFinite G
  intro s
  rcases subsingleton_or_nontrivial Γ(X, π ⁻¹ᵁ W) with hsub | hnt
  · rw [Subsingleton.elim s 0]
    exact RingHom.isIntegralElem_zero _
  set P : Polynomial Γ(X, π ⁻¹ᵁ W) := ∏ g : G, (Polynomial.X - Polynomial.C (g • s)) with hP
  have hinvP : ∀ k : G, k • P = P := by
    intro k
    rw [hP, Finset.smul_prod']
    exact Fintype.prod_bijective (k • ·) (MulAction.bijective k) _ _ (fun g => by
      rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul, smul_eq_mul])
  have hlift : P ∈ Polynomial.lifts (π.app W).hom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    apply hinv W hW
    intro g
    refine ⟨hU g, ?_⟩
    have := congrArg (fun q => q.coeff n) (hinvP g⁻¹)
    simp only [Polynomial.coeff_smul] at this
    rw [hact] at this
    simpa only [inv_inv] using this
  have hmonic : P.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun g _ => Polynomial.monic_X_sub_C _)
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, hP, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)

theorem quotient_isIntegral_surjective_orbits :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsIntegralHom π ∧ Surjective π ∧ (∀ x y : X, π x = π y → ∃ g, y = (ρ g).asIso.hom x) ∧ (∀ (k : Type) [Field k] (x y : Sp k ⟶ X), x ≫ π = y ≫ π → ∃ g, y = x ≫ (ρ g).asIso.hom) ∧ ∀ U : X.Opens, (∀ g, (ρ g).asIso.hom ⁻¹ᵁ U = U) → ∃ V : X'.Opens, π ⁻¹ᵁ V = U := by
  intro Γ _ _ X X' ρ π ⟨hAff, hπ, hV⟩
  have hinvAll : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W) := by
    intro W _ s hs
    apply (hV W).2 s
    intro g h
    obtain ⟨h', e⟩ := hs g
    exact e
  have hInt : IsIntegralHom π := isIntegralHom_of_invariant ρ π hπ hinvAll
  have hfield : ∀ (k : Type) [Field k] (x y : Sp k ⟶ X), x ≫ π = y ≫ π →
      ∃ g, y = x ≫ (ρ g).asIso.hom := by
    intro k _ x y hxy
    let p₀ : Sp k := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨W, hW, hmem, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := (x ≫ π) p₀) (U := ⊤) trivial
    refine exists_aut_of_comp_eq_of_invariant ρ π hπ hW (hinvAll W hW) x y hxy ?_
    intro p _
    have hp : p = p₀ := Subsingleton.elim _ _
    subst hp
    exact hmem
  have hpts : ∀ x y : X, π x = π y → ∃ g, y = (ρ g).asIso.hom x := by
    intro x y hxy
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
    have hab : (Scheme.fromSpecResidueField _ z ≫ pullback.fst π π) ≫ π =
        (Scheme.fromSpecResidueField _ z ≫ pullback.snd π π) ≫ π := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨g, hg⟩ := hfield ((pullback π π).residueField z) _ _ hab
    refine ⟨g, ?_⟩
    let s : Spec ((pullback π π).residueField z) := ⟨⊥, Ideal.isPrime_bot⟩
    have ha : (Scheme.fromSpecResidueField _ z ≫ pullback.fst π π) s = x := by
      show pullback.fst π π (Scheme.fromSpecResidueField _ z s) = x
      rw [Scheme.fromSpecResidueField_apply]
      exact hz1
    have hb : (Scheme.fromSpecResidueField _ z ≫ pullback.snd π π) s = y := by
      show pullback.snd π π (Scheme.fromSpecResidueField _ z s) = y
      rw [Scheme.fromSpecResidueField_apply]
      exact hz2
    rw [← hb, hg, ← ha]
    rfl
  have hsurj : Surjective π := by
    rw [surjective_iff]
    intro y
    obtain ⟨W, hW, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    have hA : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
    have heq := IsAffineOpen.SpecMap_appLE_fromSpec π hW hA le_rfl
    have hmem' : y ∈ Set.range hW.fromSpec := by
      rw [hW.range_fromSpec]
      exact hmem
    obtain ⟨p, rfl⟩ := hmem'
    have hint : (π.appLE W (π ⁻¹ᵁ W) le_rfl).hom.IsIntegral := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact hInt.isIntegral_app W hW
    have hinj : Function.Injective (π.appLE W (π ⁻¹ᵁ W) le_rfl).hom := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact (hV W).1
    obtain ⟨q, hq⟩ := hint.comap_surjective hinj p
    refine ⟨hA.fromSpec q, ?_⟩
    have := congrArg (fun f => f q) heq
    rw [← hq]
    exact this.symm
  have hopen : ∀ U : X.Opens, (∀ g, (ρ g).asIso.hom ⁻¹ᵁ U = U) → ∃ V : X'.Opens, π ⁻¹ᵁ V = U := by
    intro U hU
    have hcl : IsClosed (π '' (U : Set X)ᶜ) := π.isClosedMap _ U.isOpen.isClosed_compl
    refine ⟨⟨(π '' (U : Set X)ᶜ)ᶜ, hcl.isOpen_compl⟩, ?_⟩
    ext x
    show π x ∈ (π '' (U : Set X)ᶜ)ᶜ ↔ x ∈ U
    constructor
    · intro h
      by_contra hx
      exact h ⟨x, hx, rfl⟩
    · rintro hx ⟨y, hy, hxy⟩
      obtain ⟨g, rfl⟩ := hpts x y hxy.symm
      apply hy
      have hx' : x ∈ (ρ g).asIso.hom ⁻¹ᵁ U := by
        rw [hU g]
        exact hx
      exact hx'
  exact ⟨hInt, hsurj, hpts, hfield, hopen⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem isDomain_and_isIntegrallyClosed_stalk_Sp (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (y : Sp A) :
    IsDomain ((Sp A).presheaf.stalk y) ∧ IsIntegrallyClosed ((Sp A).presheaf.stalk y) := by
  have hy : (y.asIdeal : Ideal A).IsPrime := y.isPrime
  let _ : Algebra A ((Sp A).presheaf.stalk y) := StructureSheaf.stalkAlgebra A y
  have : IsLocalization.AtPrime ((Sp A).presheaf.stalk y) (y.asIdeal : Ideal A) :=
    StructureSheaf.IsLocalization.to_stalk A y
  exact isDomain_and_isIntegrallyClosed_atPrime_of_isDomain (B := A) (y.asIdeal : Ideal A)
    ((Sp A).presheaf.stalk y)

theorem isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s →
      IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X := by
  intro k _ X s hs
  have : Smooth s := hs
  have hN : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s
      (fun y => isDomain_and_isIntegrallyClosed_stalk_Sp k y)
  refine ⟨?_, hN, ?_⟩
  · have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      have := (hN x).1
      infer_instance
    exact isReduced_of_isReduced_stalk X
  · have : IsLocallyNoetherian (Sp k) := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian s

end GlobalTheory
end

