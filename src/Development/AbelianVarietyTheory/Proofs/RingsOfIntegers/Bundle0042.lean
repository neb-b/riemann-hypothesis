module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSymmetricLiftOddOrderLocalRing
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLiftConst
open GlobalTheory.SymLiftOdd

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ}

private theorem surjective_appTop_of_section_surjective {Y Z W : Scheme.{0}} (p : Y ⟶ W) (q : Z ⟶ W) (σ : Y ⟶ Z) (r : Z ⟶ Y)
    (hσr : σ ≫ r = 𝟙 Y) (hσq : σ ≫ q = p) (hq : Function.Surjective q.appTop.hom) :
    Function.Surjective p.appTop.hom := by
  intro f
  obtain ⟨s, hs⟩ := hq (r.appTop.hom f)
  refine ⟨s, ?_⟩
  have e1 : p.appTop.hom s = σ.appTop.hom (q.appTop.hom s) := by
    subst hσq; simp <;> rfl
  have e2 : σ.appTop.hom (r.appTop.hom f) = (σ ≫ r).appTop.hom f := by
    simp <;> rfl
  rw [e1, hs, e2, hσr]
  simp

private theorem hom_baseOver_subsingleton {X : Over S} (f g : X ⟶ baseOver S) : f = g := by
  have hf : f.left ≫ 𝟙 S = X.hom := Over.w f
  have hg : g.left ≫ 𝟙 S = X.hom := Over.w g
  have hf' : f.left = X.hom := by simpa using hf
  have hg' : g.left = X.hom := by simpa using hg
  exact Over.OverMorphism.ext (hf'.trans hg'.symm)


omit [GrpObj A] in
theorem surj_fst_base (h : Function.Surjective (A ⊗ A).hom.appTop.hom) :
    Function.Surjective (fst (baseOver S) A).left.appTop.hom := by
  let g : A ⊗ A ⟶ baseOver S := Over.homMk (A ⊗ A).hom (by simp [baseOver])
  refine surjective_appTop_of_section_surjective (fst (baseOver S) A).left (A ⊗ A).hom
    (lift (snd (baseOver S) A) (snd (baseOver S) A)).left (lift g (snd A A)).left ?_ ?_ h
  · rw [← Over.comp_left, ← Over.id_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext
    · exact hom_baseOver_subsingleton _ _
    · simp
  · have h1 : (fst (baseOver S) A).left ≫ 𝟙 S = (baseOver S ⊗ A).hom := Over.w _
    have h1' : (fst (baseOver S) A).left = (baseOver S ⊗ A).hom := by simpa using h1
    rw [h1']
    exact Over.w _

theorem exists_constT (hs : Function.Surjective (fst T A).left.appTop.hom) (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → ((T ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
    (hF : ∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), ∏ k, h (φ k) ^ ε k = 1)
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ (m : T ⊗ A ⟶ A) (y : (T ⊗ A).left) (J), Good L y J →
      val u (lift (fst T A) m).left y J = gm (fst T A).left y ⊤ a := by
  have he : (lift (𝟙 T) (1 : T ⟶ A)).left ≫ (fst T A).left = 𝟙 T.left := by
    rw [← Over.comp_left, lift_fst, Over.id_left]
  obtain ⟨a, ha⟩ := GlobalTheory.SymLiftOdd.exists_const hL (fst T A).left (lift (𝟙 T) (1 : T ⟶ A)).left he hs hF hu
  refine ⟨a, fun m y J hJ => ?_⟩
  rw [ha _ _ y J hJ, ← Over.comp_left, lift_fst]

variable [IsCommMonObj A]

theorem exists_symConst (hs : Function.Surjective (fst T A).left.appTop.hom) (hL : L.IsLB) (θ : ThetaGrp A L k T)
    {nu : LB.Gen (negLB A L k T)} (hnu : nu.IsGen) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ (m : T ⊗ A ⟶ A) (y : (T ⊗ A).left) (J), Good L y J →
      val (symGen A L k θ nu) (lift (fst T A) m).left y J = gm (fst T A).left y ⊤ a := by
  refine GlobalTheory.SymLiftConst.exists_constT hs hL ?_ (GlobalTheory.SymLiftOdd.symGen_isGen θ hnu)
  intro U _ h
  have hb : (translT A θ.pt⁻¹).left ≫ (translPt A θ.pt).left = (snd T A).left := by
    rw [← Over.comp_left, translT_eq, lift_translPt, comp_inv', mul_inv_cancel_left]
  have hc : (negT A T).left ≫ (snd T A).left = (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
    rw [← Over.comp_left, negT_eq, lift_snd]
    rfl
  have hd : (negT A T).left ≫ (translPt A θ.pt).left =
      (translT A θ.pt⁻¹).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
    rw [← Over.comp_left, ← Over.comp_left, negT_eq, translT_eq, lift_translPt, ← Category.assoc, lift_snd, comp_inv']
    rw [show ∀ f : T ⊗ A ⟶ A, f ≫ (GrpObj.inv : A ⟶ A) = f⁻¹ from fun _ => rfl]
    rw [mul_inv_rev, inv_inv, mul_comm]
  simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, neg_neg, hb, hc, hd]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_one, neg_smul]
  abel

private theorem mul_pow_eq_one_and_mul_sq_eq_one_of_odd {U : Type} [CommGroup U] (a b c : U) (n : ℕ) (hn : Odd n) (h : a ^ n = b ^ 2)
    (hc : c = a ^ ((n - 1) / 2) * b⁻¹) : b * c ^ n = 1 ∧ a * c ^ 2 = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have hm : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hm] at hc
  subst hc
  constructor
  · have e : (a ^ m) ^ (2 * m + 1) = b ^ (2 * m) := by
      rw [← pow_mul, mul_comm, pow_mul, h, ← pow_mul]
    rw [mul_pow, e, inv_pow]
    group
  · rw [mul_pow, inv_pow, ← _root_.mul_assoc, ← pow_mul, ← pow_succ', show m * 2 + 1 = 2 * m + 1 by ring, h,
      mul_inv_cancel]

theorem exists_symLift (hs : Function.Surjective (fst T A).left.appTop.hom) (hL : L.IsLB) {n : ℕ} (hn : Odd n)
    {x : T ⟶ A} (hx : x ^ n = 1) (θ : ThetaGrp A L k T) (hθ : θ.pt = x) {nu : LB.Gen (negLB A L k T)}
    (hnu : nu.IsGen) : ∃ θ' : ThetaGrp A L k T, SymLift A L k n x θ' := by
  obtain ⟨α, hα⟩ := GlobalTheory.SymLiftConst.exists_symConst hs hL θ hnu
  have hx' : θ.pt ^ n = 1 := by rw [hθ]; exact hx
  obtain ⟨β, hβ⟩ := GlobalTheory.SymLiftConst.exists_constT hs hL (fun U _ h => form_pow hx' U h) (powGen_isGen θ n)
  have key : ∀ y J, Good L y J → gm (fst T A).left y ⊤ α ^ n = gm (fst T A).left y ⊤ β ^ 2 := by
    intro y J hJ
    refine defect_pow (fun m => thetaVal θ y J m) (fun m => negVal nu y J m) (fst T A ≫ x) n ?_ _ _ ?_ ?_
    · rw [← comp_pow', hx]
      simp
    · intro m
      exact (val_symGen θ nu hθ hJ m).symm.trans (hα m y J hJ)
    · have e := (val_powGen θ n hθ hJ 1).symm.trans (hβ 1 y J hJ)
      simpa only [_root_.mul_one] using e
  obtain ⟨θ', hpt, hsc⟩ := exists_scale hL θ (α ^ ((n - 1) / 2) * β⁻¹)
  have hpt' : θ'.pt = x := hpt.trans hθ
  have hc : ∀ y, gm (fst T A).left y ⊤ (α ^ ((n - 1) / 2) * β⁻¹) =
      gm (fst T A).left y ⊤ α ^ ((n - 1) / 2) * (gm (fst T A).left y ⊤ β)⁻¹ := by
    intro y
    rw [map_mul, map_pow, map_inv]
  refine ⟨θ', ⟨hpt', ?_, ?_⟩⟩
  · apply corr_of_val hL
    intro y J hJ
    rw [val_one, id_eq_lift, val_powGen θ' n hpt' hJ]
    simp only [hsc y J hJ]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      ← val_powGen θ n hθ hJ (snd T A), hβ _ y J hJ]
    exact (mul_pow_eq_one_and_mul_sq_eq_one_of_odd _ _ _ n hn (key y J hJ) (hc y)).1
  · refine ⟨nu, hnu, corr_of_val hL fun y J hJ => ?_⟩
    rw [val_one, id_eq_lift, val_symGen θ' nu hpt' hJ]
    simp only [hsc y J hJ]
    have e1 := (val_symGen θ nu hθ hJ (snd T A)).symm.trans (hα _ y J hJ)
    have e2 := (mul_pow_eq_one_and_mul_sq_eq_one_of_odd _ _ _ n hn (key y J hJ) (hc y)).2
    refine Eq.trans ?_ e2
    rw [← e1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

theorem exists_gen_neg (L : RigLB A) (h : L.IsSymmetric) (k : ℤ) (T : Over S) :
    ∃ nu : LB.Gen (negLB A L.L k T), nu.IsGen := by
  obtain ⟨s, hs, -⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric L h
  have hs1 := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L.L _ _ s hs (snd T A).left
  obtain ⟨s2, hs2⟩ := GlobalTheory.exists_gen_zsmul _ hs1 (-k)
  unfold negLB
  refine (exists_gen (K' := Fin 2) L.isLB (φ' := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
    (ε' := ![k, -k]) ?_ s2 hs2).elim fun nu hnu => ⟨nu, hnu.1⟩
  intro U _ hh
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Over.comp_left,
    _root_.mul_one, mul_neg, neg_neg]
  simp only [Category.comp_id]
  exact _root_.mul_comm _ _

theorem exists_symLift_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (k : ℕ), Odd k → ∀ a : baseOver (Sp V) ⟶ t.G, a ^ k = 1 → ∃ U : ThetaGrp t.G t.PP.L (k : ℤ) (baseOver (Sp V)), SymLift t.G t.PP.L (k : ℤ) k a U := by
  intro E _ _ _ H V _ _ t hsurj k hk a ha
  obtain ⟨θ, hθ⟩ := GlobalTheory.TorsionThetaLocal.exists_theta_of_pow_eq_one (Sp V) t.G t.PP t.cub V (𝟙 (Sp V)) k a ha
  obtain ⟨nu, hnu⟩ := exists_gen_neg t.PP t.sym (k : ℤ) (baseOver (Sp V))
  exact GlobalTheory.SymLiftConst.exists_symLift (surj_fst_base hsurj) t.PP.isLB hk ha θ hθ hnu

end GlobalTheory.SymLiftConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledShortLatticeLeOfShortGeneratorBound
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.PlaceTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace ShortClause

theorem val_mul {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vLa la (a * b) = vLa la a + vLa la b := by
  unfold vLa
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb)]
  ring

theorem val_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (a : K) (n : ℕ) :
    vLa la (a ^ n) = n * vLa la a := by
  unfold vLa
  rw [map_pow, WithZero.log_pow]
  simp

theorem val_nat_nonneg {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) :
    0 ≤ vLa la (p : K) := by
  unfold vLa
  have h1 : la.valuation K (p : K) ≤ 1 := by
    have := la.valuation_le_one (K := K) (p : 𝓞 K)
    simpa using this
  by_cases h0 : la.valuation K (p : K) = 0
  · rw [h0]; simp
  · have := (WithZero.log_le_log h0 one_ne_zero).2 h1
    rw [WithZero.log_one] at this
    omega

theorem thc_le_of_eq_zero {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (s : 𝓞 B.KO)
    (w : WeightFamilies.Wt D j)
    (hsc : s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n) = 0) :
    X.Thc s w ≤ B.Mlat j w := by
  intro F hF
  obtain ⟨F1, hF1, rfl⟩ := Submodule.mem_map.mp hF
  obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hF1
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  rw [hsc, zero_smul]
  exact (B.Mlat j w).zero_mem

end ShortClause


open ShortClause in
theorem thc_le_of_shortBound : ShortBoundSt → ∀ (D : D7) (T : Top D) (h : LawsP T) (_hs : LawsSh T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D), Oriented T EX → ∀ (w : WeightFamilies.Wt D j) (a b : ℕ) (s : 𝓞 T.Q.c.F), c2 D w ≤ a → Formalism.MainNotions.DIV.Cons.cHalf w ≤ b → s = (zOwnP D (T.dδ j w.n).pd w : 𝓞 T.Q.c.F) * nnW (recB h.toLawsCore) hinj EX w * (pPow D a b b : 𝓞 T.Q.c.F) → (recPJ h j hj).Thc s w ≤ (recB h.toLawsCore).Mlat j w := by
  intro hSB D T h hs j hj hinj EX hO w a b s ha hb hsE
  by_cases hsc : s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 T.Q.c.F) ^ (D.R.f * D.R.r * w.n) = 0
  · exact thc_le_of_eq_zero (recPJ h j hj) s w hsc
  refine Pf.Thc_le_Mlat (recPJ h j hj) s w ?_
  intro G hG la y
  have hG' : G.1 ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j w) := hG
  have key := Pf.le_val_of_mem_span (isVal_vAt (y : T.PtA j la))
    (fun g hg => hSB D T h hs j hj hinj EX hO w g hg la y) _ hG'
  refine le_trans ?_ (key.trans (recPJ_vAt_inc h j hj la y w G).ge)
  rw [EReal.coe_le_coe_iff, neg_le_neg_iff]
  set nn : 𝓞 T.Q.c.F := nnW (recB h.toLawsCore) hinj EX w with hnn
  have e : ((s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 T.Q.c.F) ^ (D.R.f * D.R.r * w.n) : 𝓞 T.Q.c.F) : T.Q.c.F) =
      (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) ^ (DF w + 2 * D.R.f * D.R.r * w.n) * (nn : T.Q.c.F) *
        ((pPow D a b b : ℕ) : T.Q.c.F) * ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) ^ (D.R.f * D.R.r * w.n) := by
    rw [hsE, zOwnP]
    push_cast
    ring
  have hne : (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) ^ (DF w + 2 * D.R.f * D.R.r * w.n) * (nn : T.Q.c.F) *
        ((pPow D a b b : ℕ) : T.Q.c.F) * ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) ^ (D.R.f * D.R.r * w.n) ≠ 0 := by
    rw [← e]
    exact fun h0 => hsc (RingOfIntegers.coe_eq_zero_iff.1 h0)
  have h4 := right_ne_zero_of_mul hne
  have h123 := left_ne_zero_of_mul hne
  have h3 := right_ne_zero_of_mul h123
  have h12 := left_ne_zero_of_mul h123
  have h2 := right_ne_zero_of_mul h12
  have h1 := left_ne_zero_of_mul h12
  have hv : vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F))
      ((s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 T.Q.c.F) ^ (D.R.f * D.R.r * w.n) : 𝓞 T.Q.c.F) : T.Q.c.F) =
      ((DF w + 2 * D.R.f * D.R.r * w.n : ℕ) : ℤ) * vLa la (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) + vLa la (nn : T.Q.c.F) +
        vLa la ((pPow D a b b : ℕ) : T.Q.c.F) +
        ((D.R.f * D.R.r * w.n : ℕ) : ℤ) * vLa la ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) := by
    rw [e, val_mul _ h123 h4, val_mul _ h12 h3, val_mul _ h1 h2, val_pow, val_pow]
  have hr := GlobalTheory.T.ramified_prime_loss_le_valuation_prime_power D T.Q.c.F la j w a b ha hb
  have hp : (0 : ℝ) ≤ ((vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) : ℤ) : ℝ) := by
    exact_mod_cast val_nat_nonneg _ _
  have hk : (0 : ℝ) ≤ ((vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) : ℤ) : ℝ) *
      ((D.R.f : ℝ) * D.R.r * w.n) := mul_nonneg hp (by positivity)
  refine le_trans ?_ (le_of_eq (congrArg (fun z : ℤ => (z : ℝ)) hv).symm)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  generalize ((vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F)) ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) : ℤ) : ℝ) = x
  push_cast
  nlinarith [hr, hk]

end GlobalTheory.PlaceTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SpecPowerSeriesHomExtOfJets
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransUnit

theorem hom_ext_of_jets : ∀ (V : Type) [CommRing V] [IsLocalRing V] (κ : Type) [Fintype κ] [DecidableEq κ] (Y : Scheme.{0}) (f g : Sp (MvPowerSeries κ V) ⟶ Y), (∀ m, spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ f = spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ g) → f = g := by
  intro V _ _ κ _ _ Y f g h
  have hs : Function.Surjective (jetA (V := V) κ 0 : MvPowerSeries κ V →+* Jet V κ 0) :=
    fun a => GlobalTheory.ChartCmp.FrameRatio.psJet_surj 0 a
  have hn : Nontrivial (Jet V κ 0) :=
    (Formalism.L2.Pj.jetAug : Jet V κ 0 →ₐ[V] V).toRingHom.domain_nontrivial
  have hl : IsLocalRing (Jet V κ 0) := IsLocalRing.of_surjective' _ hs
  have hc : spMap (jetA (V := V) κ 0 : MvPowerSeries κ V →+* Jet V κ 0) (closedPoint (Jet V κ 0)) =
      closedPoint (MvPowerSeries κ V) := by
    have : IsLocalHom (CommRingCat.ofHom (jetA (V := V) κ 0 : MvPowerSeries κ V →+* Jet V κ 0)).hom :=
      IsLocalHom.of_surjective _ hs
    exact Spec_closedPoint
  have hx : g (closedPoint (MvPowerSeries κ V)) = f (closedPoint (MvPowerSeries κ V)) := by
    rw [← hc]
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans (Eq.trans ?_ (Scheme.Hom.comp_apply _ _ _))
    rw [h]
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.existsUnique_factor_stalk f rfl
  obtain ⟨φ', hφ', -⟩ := GlobalTheory.existsUnique_factor_stalk g hx
  have : φ = φ' := by
    ext1
    refine RingHom.ext fun b => GlobalTheory.FrameBiextId.ps_ext fun m => ?_
    have h1 : spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ Spec.map φ =
        spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ Spec.map φ' := by
      rw [← cancel_mono (Y.fromSpecStalk _), Category.assoc, Category.assoc, hφ, hφ', h]
    rw [← Spec.map_comp, ← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom b)
  rw [← hφ', ← this, hφ]

end GlobalTheory.TransUnit
end
end

