module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolution
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralExtIsAlgClosedResidueField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierSeriesProductEqProductSeries
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesProd

theorem hasSum_of_sumI {R F Ix : Type} [CommRing R] [NormedField F] (φ : R →+* F)
    (h1 : ∀ a, ‖φ a‖ ≤ 1) (I : Ideal R) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (ϖ : R) (hI : I = Ideal.span {ϖ})
    (hϖ : ‖φ ϖ‖ ≤ r) [Module R F] (hs : ∀ (a : R) (x : F), a • x = φ a * x) {x : Ix → F} {s : F}
    (h : GlobalTheory.UT.SumI I x s) : HasSum x s := by
  obtain ⟨N, hN, -, -, h⟩ := h
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y ∈ N, ‖y‖ ≤ C := by
    obtain ⟨T, rfl⟩ := hN
    refine ⟨∑ t ∈ T, ‖t‖, fun y hy => ?_⟩
    obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hy
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [hs, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (h1 _)
  have hb : ∀ (n : ℕ) y, y ∈ I ^ n • N → ‖y‖ ≤ r ^ n * C := by
    intro n y hy
    rw [hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [hs, norm_mul, map_pow, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hϖ n) (hC z hz) (norm_nonneg _) (pow_nonneg hr0 n)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have ht : Filter.Tendsto (fun n : ℕ => r ^ n * C) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const C
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨S, hS⟩ := h n
  refine ⟨S, fun T hT => ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact (hb n _ (hS T hT)).trans_lt hn

theorem hasSum_conv {F X : Type} [NormedField F] [IsUltrametricDist F] [AddCommGroup X] {a b c : X → F} {x y : F}
    (ha : HasSum a x) (hb : HasSum b y) (hc : ∀ α, HasSum (fun χ => a χ * b (α - χ)) (c α)) :
    HasSum c (x * y) := by
  have : NonarchimedeanRing F :=
    { is_nonarchimedean := (IsUltrametricDist.nonarchimedeanAddGroup (M := F)).is_nonarchimedean }
  let e : X × X ≃ X × X :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun q => (q.1 + q.2, q.1)
      left_inv := fun q => by simp
      right_inv := fun q => by simp }
  exact ((e.hasSum_iff.2 (ha.mul_of_nonarchimedean hb))).prod_fiberwise hc

open GlobalTheory.FieldBaseChange GlobalTheory.UT

theorem mul_back {Y Y' X₁ X₂ Z₁ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k k' : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
    (hL₂ : L₂.IsLB) (n : Z₁ ⟶ Y') (hn : n ≫ h₁ = 𝟙 _) {a a' a'' b b' b''}
    (h : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b)
    (h' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k' g₁ h₁ a' (m ≫ f₂) (𝟙 _) b')
    (h'' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m (k + k') g₁ h₁ a'' (m ≫ f₂) (𝟙 _) b'')
    (hb : ∀ j, (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b''.f j) =
      (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b.f j) *
        (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b'.f j))
    (y : Z₁) (i : L₁.ι) (hi : g₁ y ∈ L₁.U i) :
    powVal a'' (𝟙 _) y i = powVal a (𝟙 _) y i * powVal a' (𝟙 _) y i := by
  have e₃ : g₁ = (n ≫ m) ≫ f₁ := by rw [Category.assoc, ← h.1, ← Category.assoc, hn, Category.id_comp]
  obtain ⟨i₂, a₂⟩ := exists_chart hL₂ (f₂ (m (n y)))
  have a₁ : f₁ (m (n y)) ∈ L₁.U i := by rw [e₃] at hi; exact hi
  have v := (isoRelM_iff w m k h₁ h.1 _ h.2.1 a b).1 h _ n y i₂ i a₂ a₁
  have v' := (isoRelM_iff w m k' h₁ h.1 _ h.2.1 a' b').1 h' _ n y i₂ i a₂ a₁
  have v'' := (isoRelM_iff w m (k + k') h₁ h.1 _ h.2.1 a'' b'').1 h'' _ n y i₂ i a₂ a₁
  have e : powVal b'' (n ≫ 𝟙 _) y i₂ = powVal b (n ≫ 𝟙 _) y i₂ * powVal b' (n ≫ 𝟙 _) y i₂ := by
    rw [Category.comp_id]
    exact (congrArg (gs n y _) (hb fun _ => i₂)).trans (gs_mul n y _ (mem_wchart.2 fun _ => a₂) _ _)
  rw [v, v', v'', hn, zpow_natCast, zpow_natCast, zpow_natCast, pow_add, _root_.mul_mul_mul_comm,
    ← Units.val_mul] at e
  exact (Units.mul_right_inj _).1 e

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_frm_mul {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k k' : ℕ}
    {b : TF (R := R) F ⟶ D.P.A} {w : Frm D F k b} {w' : Frm D F k' b} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ w'' : Frm D F (k + k') b, w''.IsGen ∧
      ∀ z J, Good D.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J := by
  obtain ⟨w'', h, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε (k + k'))
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [CoefBasic.prod_line, CoefBasic.prod_line, CoefBasic.prod_line, pow_add, pow_add, mul_inv,
        _root_.mul_mul_mul_comm])
    (LB.mulGen D.P.L _ _ _ _ w w') (DVR.mulGen_isGen _ _ _ _ _ _ _ hw hw')
  exact ⟨w'', h, fun z J hJ => (hv _ _ z J hJ).trans (val_mul hJ _ _ _)⟩

theorem exists_back {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    (F : Type) [Field F] [Algebra (FractionRing R) F] {w : W0 U} (hw : w.IsGen) {k k' : ℕ}
    {σ : U.SecGF F k} {σ' : U.SecGF F k'} {σ'' : U.SecGF F (k + k')} {s s' s''}
    (h : U.ExpandsG F k σ s) (h' : U.ExpandsG F k' σ' s') (h'' : U.ExpandsG F (k + k') σ'' s'')
    (hb : ∀ j, (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j)
        from σ''.f j) =
      (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j) from σ.f j) *
      (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j) from σ'.f j)) :
    ∃ (t : SecA A F k) (t' : SecA A F k') (t'' : SecA A F (k + k')), U.ExpandsF F k w t s ∧ U.ExpandsF F k' w t' s' ∧
      U.ExpandsF F (k + k') w t'' s'' ∧
      ∀ z J, Good A.L z J → sA t'' (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J := by
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have i₂ := fun k => (isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')).2
  obtain ⟨t, ht⟩ := (i₂ k σ).exists
  obtain ⟨t', ht'⟩ := (i₂ k' σ').exists
  obtain ⟨t'', ht''⟩ := (i₂ (k + k') σ'').exists
  exact ⟨t, t', t'', ⟨σ, ht, h⟩, ⟨σ', ht', h'⟩, ⟨σ'', ht'', h''⟩, fun z J hJ =>
    mul_back U.LG.isLB n.left (congrArg (fun q => q.left) hn) ht ht' ht'' hb z _ (hJ (𝟙 _ ≫ _))⟩

theorem main : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k k' : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b) (w' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k' g.b) (w'' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) (k + k') g.b), 1 ≤ k → 1 ≤ k' → w.IsGen → w'.IsGen → w''.IsGen → ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ (σ : u.U.toUnifPre.SecGF (PadicAlgCl p) k) (σ' : u.U.toUnifPre.SecGF (PadicAlgCl p) k') (σ'' : u.U.toUnifPre.SecGF (PadicAlgCl p) (k + k')) s s' s'', u.U.toUnifPre.ExpandsG (PadicAlgCl p) k σ s → u.U.toUnifPre.ExpandsG (PadicAlgCl p) k' σ' s' → u.U.toUnifPre.ExpandsG (PadicAlgCl p) (k + k') σ'' s'' → (∀ j, (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ''.f j) = σ.f j * (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ'.f j)) → ∀ x x', HasSum (fun χ => GlobalTheory.UT.coef s g w χ) x → HasSum (fun χ => GlobalTheory.UT.coef s' g w' χ) x' → HasSum (fun χ => GlobalTheory.UT.coef s'' g w'' χ) (κ * x * x') := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l k k' g w w' w'' hk hk' hw hw' hw''
  obtain ⟨w₃, hw₃, hv⟩ := exists_frm_mul hw hw'
  obtain ⟨c, hc, -, hcoef⟩ :=
    ((CoefBasic.coef_basic _ u.D.toPre (PadicAlgCl p) (k + k') g).2.2 w₃ hw₃).2.2.1 w'' hw''
  refine ⟨c, hc, fun σ σ' σ'' s s' s'' h h' h'' hb x x' hx hx' => ?_⟩
  obtain ⟨w₀, hw₀⟩ := u.U.ext
  obtain ⟨t, t', t'', e, e', e'', hm⟩ := exists_back u.U.toUnifPre (PadicAlgCl p) hw₀ h h' h'' hb
  let φ : u.V →+* PadicAlgCl p :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))
  have : CharZero u.V := φ.charZero
  have hadm : AdmBase u.V (IsLocalRing.maximalIdeal u.V) :=
    ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hS := _root_.GlobalTheory.UT.ProdConv.main hL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) w₀ hw₀ k k' (k + k') hk hk' rfl
    t t' t'' s s' s'' e e' e'' hm g w w' w₃ hw hw' hw₃ hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  have h1 : ∀ a, ‖φ a‖ ≤ 1 := fun a => (u.norm_le _).2 ⟨a, rfl⟩
  have hlt : ‖φ ϖ‖ < 1 := lt_of_le_of_ne (h1 ϖ) fun e1 => by
    obtain ⟨z, hz⟩ := (u.norm_le (algebraMap u.V (FractionRing u.V) ϖ)⁻¹).1 (by
      rw [map_inv₀, norm_inv]
      exact (congrArg (·⁻¹) e1).le.trans inv_one.le)
    have h0 : algebraMap u.V (FractionRing u.V) ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective u.V (FractionRing u.V))).2 hϖ.ne_zero
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one z (IsFractionRing.injective u.V (FractionRing u.V) ?_))
    rw [map_mul, hz, map_one, mul_inv_cancel₀ h0]
  have hsum := hasSum_conv hx hx' fun α =>
    letI : Module u.V (PadicAlgCl p) := Module.compHom _ (algebraMap u.V (FractionRing u.V))
    hasSum_of_sumI φ h1 _ (norm_nonneg _) hlt ϖ hϖ.maximalIdeal_eq le_rfl
      (fun a x => Algebra.smul_def (algebraMap u.V (FractionRing u.V) a) x) (hS α)
  simp only [hcoef, _root_.mul_assoc]
  exact hsum.mul_left c

end GlobalTheory.ZH.SeriesProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.GenSpread

section Rings

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isFractionRing_of_forall_div {R : Subalgebra o Ω} (h : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) :
    IsFractionRing R Ω := by
  refine IsFractionRing.of_field R Ω fun x => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := h x
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

theorem isNoetherianRing_of_fg [IsNoetherianRing o] {R : Subalgebra o Ω} (h : R.FG) : IsNoetherianRing R :=
  have : Algebra.FiniteType o R := (Subalgebra.fg_iff_finiteType _).1 h
  Algebra.FiniteType.isNoetherianRing o R

theorem exists_shrink {R : Subalgebra o Ω} (hR : R.FG) {J : Type} [Finite J] (a : J → R) (ha : ∀ i, a i ≠ 0)
    {X X₀ : Scheme.{0}} {f : X ⟶ Sp R} {f₀ : X₀ ⟶ Sp Ω} {φ : X₀ ⟶ X}
    (h : IsPullback φ f₀ f (spMap (algebraMap R Ω))) :
    ∃ (R' : Subalgebra o Ω) (g : R →+* R'), R ≤ R' ∧ R'.FG ∧ (algebraMap R' Ω).comp g = algebraMap R Ω ∧
      (∀ i, IsUnit (g (a i))) ∧ ∃ φ' : X₀ ⟶ pullback f (spMap g), φ' ≫ pullback.fst _ _ = φ ∧
        IsPullback φ' f₀ (pullback.snd f (spMap g)) (spMap (algebraMap R' Ω)) := by
  let R' : Subalgebra o Ω := R ⊔ Algebra.adjoin o (Set.range fun i => (a i : Ω)⁻¹)
  have hle : R ≤ R' := le_sup_left
  let g : R →+* R' := (Subalgebra.inclusion hle).toRingHom
  have e : spMap (algebraMap R' Ω) ≫ spMap g = spMap (algebraMap R Ω) := by
    rw [← Spec.map_comp]; rfl
  refine ⟨R', g, hle, hR.sup ?_, rfl, fun i => ?_,
    pullback.lift φ (f₀ ≫ spMap (algebraMap R' Ω)) (by rw [Category.assoc, e, h.w]), pullback.lift_fst _ _ _, ?_⟩
  · exact (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  · have hm : (a i : Ω)⁻¹ ∈ R' := (le_sup_right : _ ≤ R') (Algebra.subset_adjoin ⟨i, rfl⟩)
    refine IsUnit.of_mul_eq_one ⟨_, hm⟩ (Subtype.ext ?_)
    exact mul_inv_cancel₀ (fun h0 => ha i (Subtype.ext h0))
  · refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (spMap g))
    rwa [pullback.lift_fst, e]

end Rings

theorem comp_linComb {S : Scheme.{0}} {A : Over S} [GrpObj A] {T T' : Over S} (t : T' ⟶ T) {n : ℕ}
    (y : Fin n → (T ⟶ A)) (c : Fin n → ℕ) : t ≫ linComb y c = linComb (fun i => t ≫ y i) c := by
  have := map_list_prod (preHom (G := A) t) (List.ofFn fun i => y i ^ c i)
  simp only [List.map_ofFn, Function.comp_def, map_pow] at this
  exact this

theorem polAV_spreads_out : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R₀ : Subalgebra o Ω), R₀.FG → (∀ x : Ω, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) → ∀ (P : PolAV (Sp Ω)) (M : ℕ) (ze : oˣ), IsUnit (M : o) → HypS P.A P.L → ∀ lev : Out.Level P M (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze)), Laws → ∃ (R : Subalgebra o Ω) (P' : PolAV (Sp R)) (φ : P.A.left ⟶ P'.A.left) (lev' : Out.Level P' M (unitOn (Units.map (algebraMap o R).toMonoidHom ze))), R₀ ≤ R ∧ R.FG ∧ P'.g = P.g ∧ HypS P'.A P'.L ∧ IsGrpPullback P.A P'.A (spMap R.val.toRingHom) φ ∧ LBIso P.L (P'.L.pull φ) ∧ ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev.pt i).left ≫ φ = spMap R.val.toRingHom ≫ (lev'.pt i').left := by
  intro o Ω _ _ _ hB R₀ hR₀ hfr P M ze hM hS lev hL
  have := hB.ded
  obtain ⟨w₀, wd₀, hw₀, hwd₀, hww, hS₁, hS₂⟩ := hS
  have := P.isAb.proper
  have := P.isAb.smooth

  have := isFractionRing_of_forall_div hfr
  have := isNoetherianRing_of_fg hR₀
  obtain ⟨X₀, f₀, φ₀, H₀, N, hf₀, p₀, hH₀, aH₀, hN, eH₀⟩ := exists_projective_model (R := R₀) P.A.hom
    (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample) P.isLB
  obtain ⟨a₀, ha₀, Hsm⟩ := _root_.GlobalTheory.GenSpread.exists_smoothOfRelativeDimension R₀ Ω P.g X₀ _ f₀ _ φ₀ p₀ hf₀ P.smoothDim
  obtain ⟨R₁, g₁, le₁, hR₁, c₁, u₁, φ₁, e₁, p₁⟩ := exists_shrink hR₀ (fun _ : PUnit => a₀) (fun _ => ha₀) p₀
  have hsm₁ := Hsm R₁ g₁ (u₁ ⟨⟩) _ _ _ (IsPullback.of_hasPullback f₀ (spMap g₁))
  have hH₁ := LB.isLB_pull hH₀ (pullback.fst f₀ (spMap g₁))
  have aH₁ := @IsAmpleLB.pull_of_isAffineHom _ _ _ aH₀ (pullback.fst f₀ (spMap g₁))
    (MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback f₀ (spMap g₁)).flip inferInstance)
  have eH₁ := LBIso.trans (isLB_lbPow P.isLB N) (LB.isLB_pull hH₀ _) (LB.isLB_pull hH₁ _) eH₀
    (lbIso_pull_pull hH₀ φ₁ e₁.symm)
  have hf₁ : IsProper (pullback.snd f₀ (spMap g₁)) := inferInstance
  generalize H₀.pull (pullback.fst f₀ (spMap g₁)) = H₁ at hH₁ aH₁ eH₁
  clear e₁
  generalize pullback.snd f₀ (spMap g₁) = f₁ at hsm₁ hf₁ p₁
  generalize pullback f₀ (spMap g₁) = X₁ at f₁ φ₁ H₁ hsm₁ hf₁ p₁ hH₁ aH₁ eH₁
  have hfr₁ : ∀ x : Ω, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr x
    exact ⟨a, le₁ ha, b, le₁ hb, e⟩
  clear Hsm u₁ c₁ eH₀ aH₀ hH₀ p₀ ha₀

  have := isFractionRing_of_forall_div hfr₁
  have := isNoetherianRing_of_fg hR₁
  have hs₁ : Smooth f₁ := SmoothOfRelativeDimension.smooth P.g f₁
  have : LocallyOfFinitePresentation f₁ := inferInstance
  obtain ⟨a₁, ha₁, Hconn⟩ := _root_.GlobalTheory.GenSpread.exists_geometricallyConnected R₁ Ω X₁ _ f₁ _ φ₁ p₁ hs₁
    ((ProjSpace.isProjBy_iff_isProjOver f₁).2 (aH₁.isProjOver f₁)) P.isAb.geomConnected
  obtain ⟨a₂, ha₂, Hgrp⟩ := _root_.GlobalTheory.GenSpread.exists_grpObj R₁ Ω X₁ f₁ P.A φ₁ p₁ hs₁ hf₁
  obtain ⟨a₃, ha₃, Hlb⟩ := GlobalTheory.T.lineBundle_spreads_out_from_genericFibre_proper R₁ Ω X₁ _ f₁ _ φ₁ p₁ inferInstance hf₁ P.L P.isLB
  obtain ⟨a₄, ha₄, Hw⟩ := exists_hom f₁ f₁ p₁ (w₀.left ≫ φ₁) (by rw [Category.assoc, p₁.w, Over.w_assoc])
  obtain ⟨a₅, ha₅, Hwd⟩ := exists_hom f₁ f₁ p₁ (wd₀.left ≫ φ₁) (by rw [Category.assoc, p₁.w, Over.w_assoc])
  choose b hb Hpt using fun i => exists_hom (𝟙 (Sp R₁)) f₁ (φ := spMap (algebraMap R₁ Ω)) (p₀ := 𝟙 (Sp Ω))
    (IsPullback.of_vert_isIso ⟨by simp⟩) ((lev.pt i).left ≫ φ₁) (by
      rw [Category.assoc, p₁.w, Over.w_assoc]; simp)
  obtain ⟨R₂, g₂, le₂, hR₂, c₂, u₂, φ₂, e₂, p₂⟩ := exists_shrink hR₁ (Sum.elim ![a₁, a₂, a₃, a₄, a₅] b)
    (by rintro (i | i); · fin_cases i <;> assumption
        · exact hb i) p₁
  have es₂ : spMap (algebraMap R₂ Ω) ≫ spMap g₂ = spMap (algebraMap R₁ Ω) := by
    rw [← c₂, ← Spec.map_comp]; rfl
  have q₂ := IsPullback.of_hasPullback f₁ (spMap g₂)
  let G : Over (Sp R₂) := Over.mk (pullback.snd f₁ (spMap g₂))
  obtain ⟨_, hcomm, hG⟩ := Hgrp R₂ g₂ (u₂ (.inl 1)) (algebraMap R₂ Ω) Subtype.val_injective c₂ G
    (pullback.fst _ _) φ₂ q₂ e₂ p₂.w
  obtain ⟨L₂, hL₂, eL₂⟩ := Hlb R₂ g₂ (u₂ (.inl 2)) _ _ _ q₂.w
  replace eL₂ := eL₂ φ₂ e₂
  have endo : ∀ v₀ : P.A ⟶ P.A, (∃ u : G.left ⟶ X₁, u ≫ f₁ = pullback.fst f₁ (spMap g₂) ≫ f₁ ∧
      ∀ φ' : P.A.left ⟶ G.left, φ' ≫ pullback.fst f₁ (spMap g₂) = φ₁ → φ' ≫ u = v₀.left ≫ φ₁) →
      ∃ v : G ⟶ G, φ₂ ≫ v.left = v₀.left ≫ φ₂ := by
    rintro v₀ ⟨u, hu, hu'⟩
    refine ⟨Over.homMk (q₂.lift u G.hom (hu.trans q₂.w)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, e₂]
      exact hu' φ₂ e₂
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, p₂.w, Over.w_assoc]
      exact p₂.w
  obtain ⟨w, hw⟩ := endo w₀ (Hw R₂ g₂ (u₂ (.inl 3)) _ _ _ q₂.w)
  obtain ⟨wd, hwd⟩ := endo wd₀ (Hwd R₂ g₂ (u₂ (.inl 4)) _ _ _ q₂.w)
  have pts : ∀ i, ∃ y : baseOver (Sp R₂) ⟶ G, (lev.pt i).left ≫ φ₂ = spMap (algebraMap R₂ Ω) ≫ y.left := fun i => by
    obtain ⟨u, hu, hu'⟩ := Hpt i R₂ g₂ (u₂ (.inr i)) (Sp R₂) (spMap g₂) (𝟙 _) (by simp)
    refine ⟨Over.homMk (q₂.lift u (𝟙 _) (by simpa using hu)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, e₂]
      exact (hu' _ es₂).symm
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, p₂.w, Over.w_assoc]
      simp
  choose y hy using pts
  have hsm₂ : SmoothOfRelativeDimension P.g G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback q₂ hsm₁
  have hab : IsAbelianScheme G :=
    { comm := hcomm
      smooth := SmoothOfRelativeDimension.smooth P.g G.hom
      proper := inferInstanceAs (IsProper (pullback.snd f₁ (spMap g₂)))
      geomConnected := Hconn R₂ g₂ (u₂ (.inl 0)) _ _ _ q₂ }
  have hH₂ := LB.isLB_pull hH₁ (pullback.fst f₁ (spMap g₂))
  have aH₂ := @IsAmpleLB.pull_of_isAffineHom _ _ _ aH₁ (pullback.fst f₁ (spMap g₂))
    (MorphismProperty.of_isPullback (P := @IsAffineHom) q₂.flip inferInstance)
  have eH₂ := LBIso.trans (isLB_lbPow P.isLB N) (LB.isLB_pull hH₁ _) (LB.isLB_pull hH₂ _) eH₁
    (lbIso_pull_pull hH₁ φ₂ e₂.symm)
  have hfr₂ : ∀ x : Ω, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₁ x
    exact ⟨a, le₂ ha, b, le₂ hb, e⟩

  have := isFractionRing_of_forall_div hfr₂
  have := isNoetherianRing_of_fg hR₂
  have := hab.proper
  obtain ⟨d₀, hd₀, Hrig⟩ := _root_.GlobalTheory.GenSpread.exists_rigidified R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ P.rigid
  obtain ⟨d₁, hd₁, Hsym⟩ := _root_.GlobalTheory.GenSpread.exists_sym R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ P.sym
  obtain ⟨d₂, hd₂, Hk⟩ := _root_.GlobalTheory.GenSpread.exists_kTriv hL.globalFns R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂
    ((ProjSpace.isProjBy_iff_isProjOver G.hom).2 (aH₂.isProjOver G.hom)) P.ktriv
  obtain ⟨d₃, hd₃, Hs⟩ := _root_.GlobalTheory.SymSpread.exists_forall_hypS R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ w wd w₀ wd₀ hw hwd hw₀ hwd₀ hww hS₁ hS₂
  obtain ⟨d₄, hd₄, Hi⟩ := _root_.GlobalTheory.GenSpread.exists_forall_linComb_injective R₂ Ω G P.A φ₂ inferInstance hG _ M y lev.pt hy fun c c' h => by
    refine lev.indep (AlgebraicClosure Ω) (spMap (algebraMap Ω _)) c c' ?_
    rw [← comp_linComb, ← comp_linComb, h]
  obtain ⟨d₅, hd₅, Ha⟩ := exists_isAmpleLB G.hom hG.1 hL₂ hH₂ P.isLB aH₂ hN eL₂ eH₂
  obtain ⟨R₃, g₃, le₃, hR₃, c₃, u₃, φ₃, e₃, p₃⟩ := exists_shrink hR₂ ![d₀, d₁, d₂, d₃, d₄, d₅]
    (by intro i; fin_cases i <;> assumption) hG.1
  have es₃ : spMap (algebraMap R₃ Ω) ≫ spMap g₃ = spMap (algebraMap R₂ Ω) := by
    rw [← c₃, ← Spec.map_comp]; rfl
  have q₃ := isGrpPullback_pullback G (spMap g₃)
  have hL₃ := LB.isLB_pull hL₂ (pullback.fst G.hom (spMap g₃))
  have hab₃ : IsAbelianScheme ((Over.pullback (spMap g₃)).obj G) := by
    have hcomm₃ : IsCommMonObj ((Over.pullback (spMap g₃)).obj G) := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (q₃.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← q₃.2 T x y (pushPt q₃.1.w x) (pushPt q₃.1.w y) rfl rfl,
        ← q₃.2 T y x (pushPt q₃.1.w y) (pushPt q₃.1.w x) rfl rfl, _root_.mul_comm]
    exact { comm := hcomm₃
            smooth := MorphismProperty.of_isPullback (P := @Smooth) q₃.1 hab.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) q₃.1 hab.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) q₃.1 hab.geomConnected }
  have := hab₃.comm
  have := hab₃.proper
  let P' : PolAV (Sp R₃) :=
    { A := (Over.pullback (spMap g₃)).obj G
      isAb := hab₃
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback q₃.1 hsm₂
      L := L₂.pull (pullback.fst G.hom (spMap g₃))
      isLB := hL₃
      rigid := Hrig R₃ g₃ (u₃ 0) _ _ _ q₃ hL₃ (lbIso_refl hL₃)
      sym := Hsym R₃ g₃ (u₃ 1) _ _ _ q₃ hL₃ (lbIso_refl hL₃)
      ample := (relAmple_iff_isAmpleLB_of_isAffine _ hL₃).2 (Ha R₃ g₃ (u₃ 5) _ _ _ q₃.1)
      ktriv := Hk R₃ g₃ (u₃ 2) _ _ _ q₃ hL₃ (lbIso_refl hL₃) }
  have hG₃ : IsGrpPullback P.A P'.A (spMap (algebraMap R₃ Ω)) φ₃ :=
    IsGrpPullback.cancel q₃ (hG.congr es₃.symm e₃.symm) p₃.w
  have eL₃ : LBIso P.L (P'.L.pull φ₃) := LBIso.trans P.isLB (LB.isLB_pull hL₂ _) (LB.isLB_pull hL₃ _) eL₂
    (lbIso_pull_pull hL₂ φ₃ e₃.symm)
  let y' : Fin (2 * P.g) → (baseOver (Sp R₃) ⟶ P'.A) := fun i =>
    Over.homMk (q₃.1.lift (spMap g₃ ≫ (y i).left) (𝟙 _) (by simp)) (q₃.1.lift_snd _ _ _)
  have hy' : ∀ i, (y' i).left ≫ pullback.fst G.hom (spMap g₃) = spMap g₃ ≫ (y i).left := fun i =>
    q₃.1.lift_fst _ _ _
  have hy₃ : ∀ (i₀ : Fin (2 * P.g)) (i : Fin (2 * P'.g)), (i₀ : ℕ) = i →
      (lev.pt i₀).left ≫ φ₃ = spMap (algebraMap R₃ Ω) ≫ (y' i).left := by
    intro i₀ i hi
    obtain rfl : i₀ = i := Fin.ext hi
    refine q₃.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hy', e₃, hy, reassoc_of% es₃]
    · rw [Category.assoc, Category.assoc, hG₃.1.w, Over.w_assoc, Over.w]
      simp
  have hfr₃ : ∀ x : Ω, ∃ a ∈ R₃, ∃ b ∈ R₃, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₂ x
    exact ⟨a, le₃ ha, b, le₃ hb, e⟩
  have := isFractionRing_of_forall_div hfr₃
  have := isNoetherianRing_of_fg hR₃
  obtain ⟨lev', hlev⟩ := _root_.GlobalTheory.level_of_generic_of_indep hL R₃ Ω P' P φ₃ hG₃ eL₃ rfl M (Units.map (algebraMap o R₃).toMonoidHom ze) _
    (by simpa using hM.map (algebraMap o R₃)) rfl lev y' hy₃ (Hi R₃ g₃ (u₃ 4) _ _ y' q₃ hy')
  refine ⟨R₃, P', φ₃, lev', le₁.trans (le₂.trans le₃), hR₃, rfl, Hs R₃ g₃ (u₃ 3) _ _ _ q₃ hL₃ (lbIso_refl hL₃),
    hG₃, eL₃, ?_⟩
  rw [hlev]
  exact hy₃

end GlobalTheory.GenSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableExtensionMultiplesOfSemistable
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

theorem isAbelianScheme_overPullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) := by
  constructor
  · have := h.comm
    infer_instance
  · have := h.smooth
    change Smooth (pullback.snd A.hom f)
    infer_instance
  · have := h.proper
    change IsProper (pullback.snd A.hom f)
    infer_instance
  · have := h.geomConnected
    change GeometricallyConnected (pullback.snd A.hom f)
    infer_instance

end GlobalTheory
end

