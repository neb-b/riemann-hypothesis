module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2701
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonCharacterLatticeOfGoodReductionTrait
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GoodRed

theorem subsingleton_lattice_of_extends : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F)
    (ξ : Sp T.V ⟶ F.X), jK T.V ≫ ξ = T.y → Subsingleton T.D.toPre.X := by
  intro g n o _ ζ F T ξ hξ

  have hB := GlobalTheory.isAbelianScheme_pullback_obj ξ F.univ.A F.univ.ab
  haveI := T.U.gen_hom

  have h₁ := ((isGrpPullback_of_iso T.U.gen).comp T.cart).congr ((Category.id_comp _).trans hξ.symm) rfl
  have h₂ := (isGrpPullback_pullback ((Over.pullback ξ).obj F.univ.A) (jK T.V)).comp (isGrpPullback_pullback F.univ.A ξ)
  obtain ⟨e, he, -⟩ := grpPullback_iso h₁ h₂

  obtain ⟨E, -, -⟩ := TraitUniq.extIso T.semi (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB) e he
  have hp : IsProper T.G.hom := by
    have := hB.proper
    have : IsIso E.hom.left := inferInstanceAs (IsIso ((Over.forget _).map E.hom))
    rw [← Over.w E.hom]
    infer_instance

  have hmax : (maximalIdeal T.V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (T.V ⧸ maximalIdeal T.V ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  letI := hF.toField
  let k := T.U.gt 0
  have m : Mono k.i := ⟨fun a b h => k.isKernel.hom_ext h (CartesianMonoidalCategory.toUnit_unique _ _)⟩
  exact ArcNotAbelian.subsingleton_of_mem_abLocus T.G T.semi _ hF _ (closedPoint _)
    (fun _ _ _ _ _ => inferInstance) T.D.toPre.X k.i k.i_hom

end GlobalTheory.Poinc.GoodRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzJetConj
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HilbFam

theorem sz_jet_conj : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 →  ∀ (τ : ℍ) (ω : ℂ), Sz l lam 0 (jT τ) → ω ^ 12 = DD τ → ω ≠ 0 → Sz l lam ρ ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) / ω ^ 2) → Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ) (jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ / ω ^ wt (2 * s) κ) := by
  intro hE F _ _ _ hF s N _ L hs hL _ z hz l _ lam κ y M M' b e ρ₀ ρ he hze hM hML hLv hN hρ hρ0 hM' hy hy0 τ ω hj hω hω0 hst
  obtain ⟨h0, hadd, hmul, hmono, hint, hsum⟩ := GlobalTheory.QFam.SzSum.sz_ring l lam
  have hpow : ∀ (x : ℂ) (n : ℕ), Sz l lam ρ x → Sz l lam (n * ρ) (x ^ n) := by
    intro x n hx
    induction n with
    | zero => simpa using hint 1
    | succ n ih =>
      have := hmul _ _ _ _ ih hx
      rw [pow_succ]
      convert this using 1
      push_cast
      ring
  have hneg : Sz l lam ρ (-((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) / ω ^ 2)) := by
    simpa only [zero_sub] using (hadd ρ _ _ (h0 ρ) hst).2
  rw [_root_.GlobalTheory.HilbFam.jet_conj_expand hE F hF s N L hs (Nat.pos_of_ne_zero (NeZero.ne N)) hL τ κ (wB N y), Finset.sum_div]
  refine hsum _ _ _ _ fun μ hμ ↦ ?_
  have hle : ∀ i, μ i ≤ κ i := Finset.mem_Iic.mp hμ
  have hs' : ∑ i, κ i = ∑ i, (κ i - μ i) + ∑ i, μ i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ (Nat.sub_add_cancel (hle i)).symm
  have hh := _root_.GlobalTheory.HilbFam.size_values_hfun hE F hF s N L hs hL z hz l lam μ y M M' b e ρ₀ ρ he hze hM hML hLv hN hρ hρ0 hM' hy hy0 τ ω hj hω
  have key := hmul _ _ _ _ (hmul _ _ _ _ (hint (∏ i, rco (2 * s) (κ i) (μ i))) (hpow _ (∑ i, (κ i - μ i)) hneg)) hh
  rw [GlobalTheory.wB_nonhol_correction N y τ]
  have hw : wt (2 * s) κ = 2 * (∑ i, (κ i - μ i)) + wt (2 * s) μ := by
    unfold wt
    rw [hs']
    ring
  convert key using 1
  · rw [hs']
    push_cast
    ring
  · rw [hw, pow_add, pow_mul, ← neg_div, div_pow]
    field_simp

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalPointTorusExtensionAdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem toUnit_left_eq {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem prod_zpow_add {F : Type} [Field F] {I : Type} [Fintype I] (x : I → F) (p q : I → ℤ)
    (hp : ∏ i, x i ^ p i ≠ 0) (hq : ∏ i, x i ^ q i ≠ 0) :
    ∏ i, x i ^ (p i + q i) = (∏ i, x i ^ p i) * ∏ i, x i ^ q i := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => zpow_add' ?_
  rcases eq_or_ne (x i) 0 with h | h
  · refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · by_contra hn
      exact hp (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, zero_zpow _ hn]))
    · by_contra hn
      exact hq (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, zero_zpow _ hn]))
  · exact Or.inl h

theorem tautPt_isAdd : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (a a' : Fin T.r → ℤ) (g g' g'' : GtPtF D F), TautPt T ω s ε n D e β ββ w F a g → TautPt T ω s ε n D e β ββ w F a' g' → TautPt T ω s ε n D e β ββ w F (a + a') g'' → g.IsAdd g' g'' := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF F _ _ a a' g g' g'' hg hg' hg''
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Over.mk ((TF (R := V) F).hom ≫ spMap ω) ⟶ 𝟙_ (Over (Sp W)),
      ρ.left = (TF (R := V) F).hom ≫ spMap ω := ⟨toUnit _, toUnit_left_eq _⟩
  have hpt : ∀ (x : TF (R := V) F ⟶ D.P.A) (b : Fin T.r → ℤ),
      x.left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ b).left → x.left ≫ β = (ρ ≫ T.c₀ b).left :=
    fun x b h => by rw [h, Over.comp_left, hρ, Category.assoc]
  have hb : g''.b = g.b * g'.b := by
    obtain ⟨hpb, hmul⟩ := hF.1
    have e1 := hmul (TF (R := V) F) g.b g'.b (ρ ≫ T.c₀ a) (ρ ≫ T.c₀ a') (hpt _ _ hg.1).symm (hpt _ _ hg'.1).symm
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [hpt _ _ hg''.1, ← e1, ← MonObj.comp_mul, ← T.c₀_add]
    · rw [Over.w, Over.w]
  refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isAdd_iff g g' g'').2 ⟨hb, fun χ y J hJ => ?_⟩
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀, Good T.M.L y J₀ :=
    ⟨fun ψ => (exists_chart T.M.isLB (ψ y)).choose, fun ψ => (exists_chart T.M.isLB (ψ y)).choose_spec⟩
  obtain ⟨k, hk, hv⟩ := hg.2 χ
  obtain ⟨k', hk', hv'⟩ := hg'.2 χ
  obtain ⟨k'', hk'', hv''⟩ := hg''.2 χ
  have v := hv y J₀ J hJ₀ hJ
  have v' := hv' y J₀ J hJ₀ hJ
  have v'' := hv'' y J₀ J hJ₀ hJ
  have hl : lamVal w (lift (DegPre.cF D F χ) g''.b).left y J₀ J =
      lamVal w (lift (DegPre.cF D F χ) (g.b * g'.b)).left y J₀ J := by rw [hb]
  rw [hl] at v''

  have hkk : k'' = k * k' := by
    refine Units.ext ?_
    rw [Units.val_mul, hk'', hk, hk']
    simp only [map_add (f := _)]
    exact prod_zpow_add _ _ _ (hk ▸ k.ne_zero) (hk' ▸ k'.ne_zero)
  have hG : gm (𝟙 (TF (R := V) F).left) y ⊤ (unitOn k'') =
      gm (𝟙 (TF (R := V) F).left) y ⊤ (unitOn k) * gm (𝟙 (TF (R := V) F).left) y ⊤ (unitOn k') := by
    rw [hkk, unitOn, unitOn, unitOn, map_mul, map_mul]

  have hyc : (DegPre.cF D F χ).left ≫ β = (ρ ≫ T.c₀ ((n : ℤ) • e χ)).left := by
    rw [Over.comp_left, Category.assoc, hF.2.2.2.1 χ, Over.comp_left, hρ, toUnit_left_eq, Category.assoc]
  have wa := (GlobalTheory.T.mumfordBundleIso_additive_cubicalStructure T ε n V D ω s e β ββ w hB hF (TF (R := V) F) g.b g'.b (DegPre.cF D F χ)
    (ρ ≫ T.c₀ a) (ρ ≫ T.c₀ a') (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (hpt _ _ hg.1) (hpt _ _ hg'.1) hyc y J₀ J hJ₀ hJ).2
  simp only [id] at wa

  have hs01 : ∀ x y' z : Over.mk ((TF (R := V) F).hom ≫ spMap ω) ⟶ T.B,
      cubV T.cub y J₀ x y' z = cubV T.cub y J₀ y' x z := by
    intro x y' z
    have h := (val_corr hJ₀ T.cub.cubeSymmetric_swap_first (lift x (lift y' z)).left).trans
      (val_cub T.cub (lift x (lift y' z)) hJ₀ _ _ _)
    refine h.trans ?_
    congr 1 <;> simp [x3]
  have hs12 : ∀ x y' z : Over.mk ((TF (R := V) F).hom ≫ spMap ω) ⟶ T.B,
      cubV T.cub y J₀ x y' z = cubV T.cub y J₀ x z y' := by
    intro x y' z
    have h := (val_corr hJ₀ T.cub.cubeSymmetric_swap_last (lift x (lift y' z)).left).trans
      (val_cub T.cub (lift x (lift y' z)) hJ₀ _ _ _)
    refine h.trans ?_
    congr 1 <;> simp [x3]
  have hC := (hs01 (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (ρ ≫ T.c₀ a) (ρ ≫ T.c₀ a')).trans
    (hs12 (ρ ≫ T.c₀ a) (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (ρ ≫ T.c₀ a'))
  have corr := corr_of_val T.M.isLB
    (t := LB.mulGen T.M.L _ _ _ _ (T.τ₀ (a + a') ((n : ℤ) • e χ))
      (LB.pullGen T.M.L (thφ T.B (x3 T.B)) thε T.cub.t
        (lift (T.c₀ a) (lift (T.c₀ a') (T.c₀ ((n : ℤ) • e χ)))).left))
    (t' := LB.mulGen T.M.L _ _ _ _ (T.τ₀ a ((n : ℤ) • e χ)) (T.τ₀ a' ((n : ℤ) • e χ))) (fun y' J' hJ' =>
      (val_mul hJ' _ _ _).trans (Eq.trans (congrArg (_ * ·) ((val_pull hJ' _ _ _).trans
        (congrArg (fun r => val T.cub.t r y' J') (Category.id_comp _)))) ((T.τ₀_add a a' _ y' J' hJ').trans
          (val_mul hJ' _ _ _).symm)))
  have et := (val_mul hJ₀ _ _ ρ.left).symm.trans ((val_corr hJ₀ corr ρ.left).trans (val_mul hJ₀ _ _ _))
  rw [val_cub T.cub ρ hJ₀] at et
  have sy : ∀ b b', val (T.τ₀ b b') ((TF (R := V) F).hom ≫ spMap ω) y J₀ = val (T.τ₀ b' b) ρ.left y J₀ :=
    fun b b' => (congrArg (fun r => val (T.τ₀ b b') r y J₀) hρ).symm.trans
      (val_corr hJ₀ (corr_of_val T.M.isLB (T.τ₀_symm b b')) ρ.left)
  rw [sy] at v v' v''
  have hth : DVR.th D y J (DVR.cP D (TF (R := V) F) χ) g.b g'.b = cubV D.cub y J (DegPre.cF D F χ) g.b g'.b := rfl
  rw [v, v', v'', hth]
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul hG
  have a₂ := congrArg Additive.ofMul wa
  have a₃ := congrArg Additive.ofMul hC
  have a₄ := congrArg Additive.ofMul et
  simp only [ofMul_mul] at a₁ a₂ a₃ a₄ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃ + a₄

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantLeCommonBoundMonomial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.DivBound

theorem theta_pow_le : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ))), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → ∀ c : WithZero (Multiplicative ℤ), (∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ c) → ∀ a, ∃ w : Fin 8 → X, 𝔪.YY a w ∧ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≤ c ^ ((X₁.S.r * X₁.S.N) ^ 2) * ν (algebraMap V (FractionRing V) (mono W t δ w)) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 ν h1 h2 c hc a
  obtain ⟨yy1, -, yy3, -⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  by_cases hm : maximalIdeal V = ⊥
  · obtain ⟨w, hw⟩ := yy1 a
    refine ⟨w, hw, ?_⟩
    have hu : IsUnit (mono W t δ w) := by
      by_contra hn
      exact 𝔪.mono_ne_zero w ((Submodule.mem_bot V).1 (hm ▸ (mem_maximalIdeal _).2 hn))
    have h1' : ν (algebraMap V (FractionRing V) (mono W t δ w)) = 1 := by
      refine le_antisymm (h1 _) ?_
      have e : ν (algebraMap V (FractionRing V) (mono W t δ w)) * ν (algebraMap V (FractionRing V) (hu.unit⁻¹ : Vˣ)) = 1 := by
        rw [← map_mul, ← map_mul, hu.mul_val_inv, map_one, map_one]
      calc (1 : WithZero (Multiplicative ℤ)) = _ := e.symm
        _ ≤ ν (algebraMap V (FractionRing V) (mono W t δ w)) * 1 := mul_le_mul' le_rfl (h1 _)
        _ = _ := _root_.mul_one _
    rw [h1', _root_.mul_one]
    exact pow_le_pow_left' (hc a) _
  · obtain ⟨V', _, _, _, _, j, k, hcn, hj, hjl, hk, hν⟩ := GlobalTheory.DivBound.exists_cdvr_valuation_le V 𝔪.cn ν h1 h2 hm
    obtain ⟨𝔫, hyk, hyy⟩ := GlobalTheory.Poinc.Sep.MemBC.uMem_baseChange_values g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 V' j k hcn hj hjl hk
    obtain ⟨b, hb⟩ := GlobalTheory.Poinc.IntTerm.DvrScale.exists_dvd_pow g n F W Z i X₁ z₁ act V' (j.comp ev) X m (fun i => j (t i)) δ 𝔫
    obtain ⟨w, r, hw, he⟩ := hb a
    obtain ⟨mu, hmu⟩ := yy1 a
    have hn3 := (GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V' (j.comp ev) X m (fun i => j (t i)) δ 𝔫).2.2.1
    have hw' : 𝔪.YY a w := (yy3 a mu w hmu).2 ((hn3 a mu w (hyy a mu hmu)).1 hw)
    refine ⟨w, hw', ?_⟩
    have hmono : mono W (fun i => j (t i)) δ w = j (mono W t δ w) := by
      simp [mono, map_prod, map_pow]
    have key := hν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2))
      (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) * algebraMap V (FractionRing V) (mono W t δ w))
      ⟨r, by rw [map_pow, ← hyk, he, map_mul, map_pow, ← hyk, hk, hmono]; ring⟩
    rw [map_pow, map_mul, map_pow] at key
    exact key.trans (mul_le_mul' (pow_le_pow_left' (hc b) _) le_rfl)

end GlobalTheory.Poinc.Sep.DivBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTwoLevelsPrimitiveAtTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegCmp

theorem prim_comp_of_isIntegral : ∀ {V W K : Type} [CommRing V] [CommRing W] [Field K] (f : V →+* W) (j : W →+* K), f.IsIntegral → ∀ {J : Type} (c : J → K), Prim j c → Prim (j.comp f) c := by
  intro V W K _ _ _ f j hf J c hc
  letI := f.toAlgebra
  letI := j.toAlgebra
  letI : Algebra V K := (j.comp f).toAlgebra
  haveI : IsScalarTower V W K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral V W := ⟨hf⟩
  have key : ∀ x : K, j.IsIntegralElem x → (j.comp f).IsIntegralElem x := fun x hx =>
    (isIntegral_trans (R := V) (A := W) x hx : IsIntegral V x)
  exact ⟨fun a => key _ (hc.1 a), let ⟨a, h0, h1⟩ := hc.2; ⟨a, h0, key _ h1⟩⟩

theorem exists_ext_fractionRing : ∀ (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (f : V →+* W) (fK : FractionRing V →+* FractionRing W), f.IsIntegral → (∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K), ∃ io' : FractionRing W →+* K, io'.comp fK = io := by
  intro V W _ _ _ _ f fK hf hfK K _ _ io
  letI := fK.toAlgebra
  letI := io.toAlgebra
  have hint : ∀ w : W, IsIntegral (FractionRing V) (algebraMap W (FractionRing W) w) := by
    intro w
    obtain ⟨p, hp, hpe⟩ := hf w
    refine ⟨p.map (algebraMap V (FractionRing V)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap (FractionRing V) (FractionRing W)).comp (algebraMap V (FractionRing V)) =
        (algebraMap W (FractionRing W)).comp f := by
      ext a; exact hfK a
    rw [this, ← Polynomial.hom_eval₂, hpe, map_zero]
  have hmem : ∀ w : W, algebraMap W (FractionRing W) w ∈ algebraicClosure (FractionRing V) (FractionRing W) :=
    fun w => mem_algebraicClosure_iff.2 (hint w).isAlgebraic
  haveI : Algebra.IsAlgebraic (FractionRing V) (FractionRing W) := by
    constructor
    intro z
    rw [← mem_algebraicClosure_iff]
    obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors W) z
    simp only [IsFractionRing.mk'_eq_div]
    exact div_mem (hmem w) (hmem s)
  refine ⟨(IsAlgClosed.lift : FractionRing W →ₐ[FractionRing V] K).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : FractionRing W →ₐ[FractionRing V] K).commutes x

theorem theta_two_levels_prim : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ S) (P : PolAV (Sp (FractionRing V))) (α : P.A.left ⟶ G.left), IsGrpPullback P.A G y α → LBIso P.L (L.pull α) → (letI := P.isAb.comm; HypS P.A P.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ G L ρ m m' (spMap io ≫ y) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by

  intro S G _ _ L ρ hL hρ V _ _ _ hV y P α hα hLα hS K _ _ io m m' N N' d d' hm hm3 hmu hm' hm3' hmu' hth
  letI := P.isAb.comm
  obtain ⟨ρP, hρP⟩ := P.rigid
  have h1 : HasTh₂ P.A P.L ρP m m' (spMap io) d d' :=
    (ThMove.hasTh₂_move S G L ρ hL hρ _ P.A P.L ρP y α P.isLB hρP hα hLα m m' N N' K (spMap io) d d').2 hth
  obtain ⟨W, _, _, _, _, f, fK, hWc, hfi, hfinj, hfK, A, β, hβ, hLβ, G', _, _, gen, hG', hgen, E, hE⟩ := _root_.GlobalTheory.SplitSemiAbModel.exists_split_model V hV P
  letI := A.isAb.comm
  have hSA : HypS A.A A.L :=
    SymBaseChange.hypS_baseChange _ _ P.A A.A (spMap fK) β P.L A.L P.isLB A.isLB hβ hLβ hS
  obtain ⟨D, U, -⟩ := GlobalTheory.ZH.thmU_and_uTors.1 W hWc A G' hG' ⟨E, hE⟩ hSA gen hgen
  obtain ⟨io', hio'⟩ := exists_ext_fractionRing V W f fK hfi hfK K io
  obtain ⟨ρA, hρA⟩ := A.rigid
  have hx : spMap io' ≫ spMap fK = spMap io := by
    rw [← hio']; simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h2 : HasTh₂ A.A A.L ρA m m' (spMap io') d d' := by
    refine (ThMove.hasTh₂_move _ P.A P.L ρP P.isLB hρP _ A.A A.L ρA (spMap fK) β A.isLB hρA hβ hLβ
      m m' N N' K (spMap io') d d').2 ?_
    rw [hx]; exact h1
  have hmuW : IsUnit (m : W) := by simpa using hmu.map f
  have hmuW' : IsUnit (m' : W) := by simpa using hmu'.map f
  obtain ⟨a, ha, hp, hp'⟩ := GlobalTheory.T.uniformised_trait_theta_constants_two_levels_integral W hWc D A G' hG' U ρA hρA K io' m m' N N' d d' hm hm3 hmuW hm' hm3' hmuW' h2
  have hcomp : (io'.comp (algebraMap W (FractionRing W))).comp f = io.comp (algebraMap V (FractionRing V)) := by
    ext x; simp [← hfK, ← hio']
  refine ⟨a, ha, ?_, ?_⟩
  · rw [← hcomp]; exact prim_comp_of_isIntegral f _ hfi _ hp
  · rw [← hcomp]; exact prim_comp_of_isIntegral f _ hfi _ hp'

end GlobalTheory.SiegCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBaseFormTimesFibreClass
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.CellDens

theorem dens_smul {n : ℕ} (c : ℂ) (β : Alt n) : dens (c • β) = c * dens β := by
  simp [dens, mul_div_assoc]

theorem dens_blocks (n d : ℕ) (J T : Type) [Fintype J] [Fintype T] (ε : Fin n ≃ Fin d ⊕ J) (lev : J → T) (ρ : T → ℕ)
    (K : T → Fin n → Fin n → ℂ) (r : T → ℕ) (hr : ∀ t, r t = Fintype.card {j // lev j = t})
    (hK : ∀ t j, lev j ≠ t → ρ t ≤ ρ (lev j) → ∀ b, K t (ε.symm (.inr j)) b = 0 ∧ K t b (ε.symm (.inr j)) = 0)
    (α : Alt d) :
    dens (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, (kappa * K t a b) • sym (a, b)) ^ r t : Ev n) : Alt n)) =
      dens α * ∏ t, ((r t).factorial / (Real.pi : ℂ) ^ r t *
        (Matrix.of fun a b : {j // lev j = t} => K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1))).det) := by
  rw [_root_.GlobalTheory.FlagTri.dens_blockTri n d J T ε lev ρ (fun t a b => kappa * K t a b) r hr
    (fun t j h1 h2 b => by simp [(hK t j h1 h2 b).1, (hK t j h1 h2 b).2]) α]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 (t : T) : (∑ a : {j // lev j = t}, ∑ b : {j // lev j = t},
      (kappa * K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1))) • sym (ε.symm (.inr a.1), ε.symm (.inr b.1)) : Ev n) ^ r t =
      ((r t).factorial / (Real.pi : ℂ) ^ r t *
        (Matrix.of fun a b : {j // lev j = t} => K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1))).det) •
        ∏ a : {j // lev j = t}, (Complex.I / 2) • sym (ε.symm (.inr a.1), ε.symm (.inr a.1)) := by
    have h := _root_.GlobalTheory.FlagCell2.pow_card_sum_sym n {j // lev j = t} (fun a => ε.symm (.inr a.1))
      (fun a b hab => Subtype.ext (Sum.inr_injective (ε.symm.injective hab)))
      (kappa • Matrix.of fun a b : {j // lev j = t} => K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1)))
    rw [Matrix.det_smul, ← hr t] at h
    refine Eq.trans h ?_
    rw [Finset.prod_smul, Finset.prod_const, Finset.card_univ, ← hr t, smul_smul]
    congr 1
    have hk : kappa = (Real.pi : ℂ)⁻¹ * (Complex.I / 2) := by
      rw [kappa]; field_simp
    rw [hk, mul_pow, inv_pow]
    ring
  simp only [h1]
  rw [Finset.prod_smul, Fintype.prod_fiberwise lev
    (fun j => (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j))), Subalgebra.coe_smul, mul_smul_comm, dens_smul,
    _root_.GlobalTheory.FlagCell2.BaseVol.dens_pull_mul_vol n d J ε α, mul_comm]

theorem cellPot_add {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (x : Root m)
    (j : Cell m) (h1 : j.root ≠ x) (h2 : x.2.val ≤ j.root.2.val) (z : V n) (c : ℂ) :
    cellPot ε G x (z + c • coordVec (ε.symm (.inr j))) = cellPot ε G x z := by
  have hb : bsL ε (z + c • coordVec (ε.symm (.inr j))) = bsL ε z := by
    ext a
    simp [bsL_apply, coordVec]
  have hf (j' : Cell m) (h : j' ≠ j) : fb ε (z + c • coordVec (ε.symm (.inr j))) j' = fb ε z j' := by
    simp [fb, coordVec, h]
  unfold cellPot
  rw [hb]
  congr 2
  refine _root_.GlobalTheory.FlagCell2.grD_upU_gram_eq _ _ _ _ _ fun s hs => hf _ ?_
  rintro rfl
  exact h1 (Sigma.ext rfl (heq_of_eq (le_antisymm hs h2)))

theorem dens_cellForm : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (a : V d → Alt d) (w : V n), (∀ τ, (G (bsL ε w) τ).PosDef) → (∀ τ, MContDiffAt 2 (fun v => G v τ) (bsL ε w)) → dens (cellForm ε G a w) = dens (a (bsL ε w)) * (fibDens (G (bsL ε w)) (fb ε w) : ℝ) := by
  intro ι _ m n d ε G a w hG hC
  have e : cellFib ε G w = ∏ x : Root m, (∑ p, ∑ q,
      (kappa * -leviForm (cellPot ε G x) w (coordVec p) (coordVec q)) • sym (p, q)) ^ (m x.1 - 1 - x.2 : ℕ) := by
    simp only [cellFib, fibrePoint, map_prod, map_pow, map_neg, map_X, aeval_X, ofValues, ddc, mul_neg, neg_smul,
      Finset.sum_neg_distrib]
  have hk : kappa ≠ 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [kappa, hπ]
  rw [cellForm, e, dens_blocks n d (Cell m) (Root m) ε Cell.root (fun x => x.2.val)
    (fun x p q => -leviForm (cellPot ε G x) w (coordVec p) (coordVec q)) (fun x => m x.1 - 1 - x.2)
    (fun x => by convert (GlobalTheory.T.gradedLine_potential_hessian_det_own_row ι m n d ε G w x (hG _) (hC _)).1.symm) ?_]
  · congr 1
    rw [fibDens, Fintype.prod_sigma, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← _root_.GlobalTheory.FlagCellDens.main _ _ (hG τ), Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.ofReal_mul]
    congr 1
    · push_cast
      rfl
    · convert (GlobalTheory.T.gradedLine_potential_hessian_det_own_row ι m n d ε G w ⟨τ, i⟩ (hG _) (hC _)).2 <;> rfl
  · intro x j h1 h2 b
    have h := _root_.GlobalTheory.ddc_eq_zero_of_invariant n (cellPot ε G x) w (coordVec (ε.symm (.inr j))) (coordVec b)
      (_root_.GlobalTheory.CellPotSmooth.cellPot_contDiffAt ι m n d ε G w x (hG _) (hC _)).1 (cellPot_add ε G x j h1 h2)
    simp only [ddc, mul_eq_zero, hk, false_or] at h
    simp [h.1, h.2]

end GlobalTheory.FlagCell2.CellDens
end

