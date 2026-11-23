module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselSum
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem coef_mul_split : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → IsCoef R l l' F s → ∃ (Ft : κ → Mx k r → (Wq →L[ℂ] Wp)) (st : κ → ℂ), (∀ I, IsCoef (RI I) (lI I) (lI' I) (Ft I) (st I)) ∧ (∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om • F g = ∑ I, Ft I g) ∧ (∀ I, (¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) → st I = 0) ∧ ∀ I (κ₀ κ₁ : ℂ), (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) → st I = (ep I : ℂ) * κ₁ * star κ₀ * s := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI Wp _ _ _ _ Wq _ _ _ _ om om' l l' lI lI' F s
    hR hRI hF hT hC
  obtain ⟨m, x, y, X, hxy, hFg, hs⟩ := hC
  have hsm : ∀ v ∈ R.TK, v ∈ R.sm := (GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR).2.2.2.2.1
  have hsmI : ∀ I, ∀ v ∈ (RI I).TK, v ∈ (RI I).sm := fun I =>
    (GlobalTheory.rep_basic_of_isDS hK k r ε (muI I) (RI I) (hRI I)).2.2.2.2.1
  have hadj := (GlobalTheory.TensAdj.tens_adj hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT).2.2.2.2
  have hkf := (GlobalTheory.tensor_decomposition_kfinite hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw).2.2.2
  have hp : ∀ I (a : ι → ℂ), ∀ v ∈ R.TK, (∑ c, pr I c (tm R a v c)) ∈ (RI I).TK := fun I a v hv =>
    Submodule.sum_mem _ fun c _ => hkf I c _ (Submodule.smul_mem _ _ hv)
  refine ⟨fun I g => ∑ i, ⟪∑ c, pr I c (tm R om (x i) c), (RI I).σ g (∑ c, pr I c (tm R om' (y i) c))⟫_ℂ •
      ((ep I : ℂ) • X i),
    fun I => ∑ i, ⟪lI I (∑ c, pr I c (tm R om (x i) c)),
      ((ep I : ℂ) • X i) (lI' I (∑ c, pr I c (tm R om' (y i) c)))⟫_ℂ, ?_, ?_, ?_, ?_⟩
  · intro I
    exact ⟨m, fun i => ∑ c, pr I c (tm R om (x i) c), fun i => ∑ c, pr I c (tm R om' (y i) c),
      fun i => (ep I : ℂ) • X i, fun i => ⟨hp I om _ (hxy i).1, hp I om' _ (hxy i).2⟩, fun g _ => rfl, rfl⟩
  · intro g hg
    rw [hFg g hg, Finset.smul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hadj om om' _ (hsm _ (hxy i).1) _ (hsm _ (hxy i).2) g hg, Finset.sum_smul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [smul_smul, mul_comm]
  · intro I h
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases h with h | h
    · have : lI I (∑ c, pr I c (tm R om (x i) c)) = 0 := by
        by_contra hne
        exact h ⟨_, hsmI I _ (hp I om _ (hxy i).1), hne⟩
      rw [this, inner_zero_left]
    · have : lI' I (∑ c, pr I c (tm R om' (y i) c)) = 0 := by
        by_contra hne
        exact h ⟨_, hsmI I _ (hp I om' _ (hxy i).2), hne⟩
      rw [this, map_zero, inner_zero_right]
  · intro I κ₀ κ₁ h0 h1
    rw [hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h0 _ (hsm _ (hxy i).1), h1 _ (hsm _ (hxy i).2), map_smul, ContinuousLinearMap.smul_apply,
      inner_smul_left, inner_smul_right, inner_smul_right]
    simp only [starRingEnd_apply]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TypingsAgree
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionFactsCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Operators

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

end Operators

section Data

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]


open QForm in
theorem bOf_balance {ϖ : V} (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} {O : Type} [Ring O] [StarRing O]
    [Module O D.toPre.X] (ιD : D.toPre.OAct O) (hQ : IsQ D.toPre ϖ Q) (a : O) (χ χ' : D.toPre.X) :
    bOf D.toPre Q (a • χ) χ' = bOf D.toPre Q χ (star a • χ') := by
  have hL := D.toPre.P.isLB
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  obtain ⟨u, hu, hnorm⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb D.toPre.P.isLB _ _ (ιD.onB.rosati a)
  have hc := ιD.tau_bal a u hu hnorm χ χ'
  obtain ⟨_, _, hsA, hA⟩ := tau_val hϖ D hQ (a • χ) χ'
  obtain ⟨_, _, hsB, hB⟩ := tau_val hϖ D hQ χ (star a • χ')
  have hu0 := genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ u hu (lift (D.toPre.c χ) (D.toPre.c χ')).left
    (D.toPre.pt2 χ χ') (by simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift])
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hA hu0
  have := genHasVal_unique hϖ D.toPre.P.L hL _ _ _ _ _
    (genHasVal_corr hϖ D.toPre.P.L hL D.toPre.P.A.hom _ _ _ _ _ _ _ _
      (sumElim_sec hsA (fun k => by
        obtain ⟨q, hq⟩ := rosatiφ_over D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k
        show (_ ≫ rosatiφ D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k) ≫ _ = _
        rw [hq]; exact over_sec _ _)) hsB _ _
      (genHasVal_isGen D.toPre.P.L _ _ _ _ _ hB) hc h1) hB
  linarith

end Data

section Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}
  (P : PELUnif (maximalIdeal V) t) (F : Type) [Field F] [Algebra (FractionRing V) F]

end Unif

end GlobalTheory.TorsionFactsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilPairingPowPolAVEqProdField
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeilPower

open GlobalTheory.CommutatorPairing GlobalTheory.BoxPhi

variable {S : Scheme.{0}} {j : ℕ} {A A' : PolAV S} (pA : IsPowPolAV A' A j) {k : ℤ} {T : Over S}

theorem exists_box_theta (x : T ⟶ A'.A) (θ : Fin j → ThetaGrp A.A A.L k T) (hθ : ∀ i, (θ i).pt = x ≫ pA.pr i) :
    ∃ θ' : ThetaGrp A'.A A'.L k T, θ'.pt = x ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A'.A) (z : Z.left) (J J'),
      Good A.L z J → Good A'.L z J' →
      om pA.w z J J' a.left ^ k * om pA.w z J J' ((t ≫ x) * a).left ^ (-k) * thetaVal θ' t a z J' =
        ∏ i, thetaVal (θ i) t (a ≫ pA.pr i) z J := by
  have hP : ∀ i, translPt A'.A x ≫ pA.pr i = T ◁ pA.pr i ≫ translPt A.A (θ i).pt := fun i => by
    have := pA.hom i
    rw [hθ, BoxTheta.translPt_hom]
  obtain ⟨u, hu, hv⟩ := exists_box_gen (pr := fun i => (pA.pr i).left) A.isLB A'.isLB pA.w pA.w_gen (K := Fin 2)
    (φ' := ![(snd T A'.A).left, (translPt A'.A x).left])
    (φ := fun i => ![(snd T A.A).left, (translPt A.A (θ i).pt).left]) (ε := ![k, -k])
    (p := fun i => (T ◁ pA.pr i).left) (fun i a => by
      fin_cases a
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T (pA.pr i)).symm
      · exact congrArg (fun q => q.left) (hP i)) (fun i => (θ i).φ) (fun i => (θ i).isGen)
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J J' hJ hJ' => ?_⟩
  have e := hv _ (lift t a).left z J J' hJ hJ'
  rw [prod_theta x t a (om pA.w z J J')] at e
  refine e.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [← Over.comp_left, lift_whiskerLeft]
  rfl

theorem commVal_pow (hG : GlobalFnsSt) (θx' θy' : ThetaGrp A'.A A'.L k T) (θx θy : Fin j → ThetaGrp A.A A.L k T)
    (hx : ∀ i, (θx i).pt = θx'.pt ≫ pA.pr i) (hy : ∀ i, (θy i).pt = θy'.pt ≫ pA.pr i)
    {Z : Over S} (t : Z ⟶ T) (a : Z ⟶ A'.A) (z : Z.left) {J J'} (hJ : Good A.L z J) (hJ' : Good A'.L z J') :
    commVal θx' θy' t a z J' = ∏ i, commVal (θx i) (θy i) t (a ≫ pA.pr i) z J := by
  have := A'.isAb.comm
  obtain ⟨bx, ex, vx⟩ := exists_box_theta pA θx'.pt θx hx
  obtain ⟨by', ey, vy⟩ := exists_box_theta pA θy'.pt θy hy
  rw [commVal_indep hG A'.isAb A'.isLB θx' θy' bx by' t t (by rw [ex]) (by rw [ey]) a z J' hJ']
  have m : ∀ (x : T ⟶ A'.A) (i), ((t ≫ x) * a) ≫ pA.pr i = (t ≫ x ≫ pA.pr i) * (a ≫ pA.pr i) := fun x i => by
    have := pA.hom i
    rw [MonObj.mul_comp, Category.assoc]
  have e₁ := vx Z t a z J J' hJ hJ'
  have e₂ := vy Z t ((t ≫ θx'.pt) * a) z J J' hJ hJ'
  have e₃ := vy Z t a z J J' hJ hJ'
  have e₄ := vx Z t ((t ≫ θy'.pt) * a) z J J' hJ hJ'
  rw [mul_left_comm (t ≫ θy'.pt)] at e₂
  simp only [m, ← hx, ← hy] at e₂ e₄
  simp only [commVal, Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← e₁, ← e₂, ← e₃, ← e₄, ex, ey, zpow_neg]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem weilIs_pow (hG : GlobalFnsSt) [Subsingleton T.left] (x y : T ⟶ A'.A) (c : Fin j → Γ(T.left, ⊤)ˣ)
    (h : ∀ i, WeilIs A.A A.L k (x ≫ pA.pr i) (y ≫ pA.pr i) (c i)) : WeilIs A'.A A'.L k x y (∏ i, c i) := by
  intro p
  have h' : ∀ i, (∃ θx θy : ThetaGrp A.A A.L k (overRes ⊤), θx.pt = overResι ⊤ ≫ x ≫ pA.pr i ∧
      θy.pt = overResι ⊤ ≫ y ≫ pA.pr i) ∧ ∀ θx θy : ThetaGrp A.A A.L k (overRes ⊤),
      θx.pt = overResι ⊤ ≫ x ≫ pA.pr i → θy.pt = overResι ⊤ ≫ y ≫ pA.pr i →
      CommIsOf A.A A.L k θx θy (unitRes ⊤ (c i)) := fun i => by
    obtain ⟨V, hV, H⟩ := h i p
    obtain rfl : V = ⊤ := top_le_iff.1 fun q _ => by rw [Subsingleton.elim q p]; exact hV
    exact H
  choose θx θy hx hy using fun i => (h' i).1
  obtain ⟨bx, ex, -⟩ := exists_box_theta pA (overResι ⊤ ≫ x) θx (fun i => by rw [hx, Category.assoc])
  obtain ⟨by', ey, -⟩ := exists_box_theta pA (overResι ⊤ ≫ y) θy (fun i => by rw [hy, Category.assoc])
  refine ⟨⊤, trivial, ⟨bx, by', ex, ey⟩, fun θx' θy' ex' ey' => (commIsOf_iff A'.isLB _ _ _).2 fun Z t a z J' hJ' => ?_⟩
  choose J hJ using fun χ : Z.left ⟶ A.A.left => exists_chart A.isLB (χ z)
  rw [commVal_pow pA hG θx' θy' θx θy (fun i => by rw [hx, ex', Category.assoc])
    (fun i => by rw [hy, ey', Category.assoc]) t a z hJ hJ']
  refine (Finset.prod_congr rfl fun i _ => (commIsOf_iff A.isLB _ _ _).1 ((h' i).2 _ _ (hx i) (hy i)) Z t _ z J hJ).trans ?_
  exact (map_prod _ _ _).symm.trans (congrArg _ (map_prod (Units.map (⊤ : T.left.Opens).ι.appTop.hom.toMonoidHom) c _).symm)

theorem weilIs_pow_field : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (x x' : TFK (R := R) F ⟶ A'.A) (c : Fin j → Fˣ), (∀ i, WeilIs A.A A.L k (x ≫ pA.pr i) (x' ≫ pA.pr i) (unitOn (c i))) → WeilIs A'.A A'.L k x x' (unitOn (∏ i, c i)) := by
  intro hL _ _ _ R _ _ j A A' pA F _ _ k _ x x' c h
  have : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  have e : unitOn (∏ i, c i) = ∏ i, unitOn (c i) := map_prod (Units.map _) _ _
  rw [e]
  exact weilIs_pow pA hL.globalFns x x' (fun i => unitOn (c i)) h

end GlobalTheory.WeilPower
end
end

