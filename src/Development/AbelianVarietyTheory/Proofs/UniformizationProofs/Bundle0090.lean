module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0085

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistThroughIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.TwistCompare

section Abstract

variable {X N Y V S₀ Z : Scheme.{0}} {L : LB X} {M : LB N} {c₀ : Y ⟶ X} {q : Y ⟶ N}

def wv (w : LB.Iso (L.pull c₀) (M.pull q)) (f : Z ⟶ Y) (z : Z) (JL : (Z ⟶ X) → L.ι) (JM : (Z ⟶ N) → M.ι) :
    (Z.presheaf.stalk z)ˣ := GlobalTheory.FieldBaseChange.isoVal w f z (JM (f ≫ q)) (JL (f ≫ c₀))

theorem val_through_iso (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull c₀) (M.pull q)} (hw : w.IsGen)
    (n : X ⟶ Y) (hn : n ≫ c₀ = 𝟙 X) (s m : V ⟶ X) (a : N ⟶ N) (hc : m ≫ n ≫ q = (s ≫ n ≫ q) ≫ a) (k' k : ℤ)
    (b : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 N, a] ![k', -k])) (hb : b.IsGen)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![s, m] ![k', -k])) (hα : α.IsGen)
    (p : V ⟶ S₀) (e : S₀ ⟶ V) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h₀ : ∀ y JL JM, Good L y JL → Good M y JM → val b (e ≫ s ≫ n ≫ q) y JM =
      wv w (e ≫ s ≫ n) y JL JM ^ k' * wv w (e ≫ m ≫ n) y JL JM ^ (-k) * val α e y JL)
    (r : Z ⟶ V) (z : Z) (JL) (JM) (hJL : Good L z JL) (hJM : Good M z JM) :
    val b (r ≫ s ≫ n ≫ q) z JM =
      wv w (r ≫ s ≫ n) z JL JM ^ k' * wv w (r ≫ m ≫ n) z JL JM ^ (-k) * val α r z JL := by
  obtain ⟨u, hu, hv⟩ := GlobalTheory.ThetaBaseChange.exists_unpull hw n hn rfl
  have hc' : ∀ κ, (![s, m] : Fin 2 → _) κ ≫ n ≫ q = (s ≫ n ≫ q) ≫ (![𝟙 N, a] : Fin 2 → _) κ := fun κ => by
    fin_cases κ
    exacts [(Category.comp_id _).symm, hc]
  obtain ⟨α', hα', hm⟩ := H1.exists_gen_move hM hL u hu ![𝟙 N, a] ![s, m] ![k', -k] (s ≫ n ≫ q) hc' b hb
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ V) (z : Z) (JL) (JM), Good L z JL → Good M z JM →
      val b (r ≫ s ≫ n ≫ q) z JM =
        wv w (r ≫ s ≫ n) z JL JM ^ k' * wv w (r ≫ m ≫ n) z JL JM ^ (-k) * val α' r z JL := by
    intro Z r z JL JM hJL hJM
    have g : ∀ f : V ⟶ X, gw u (r ≫ f) z (JM (r ≫ f ≫ n ≫ q)) (JL (r ≫ f)) = wv w (r ≫ f ≫ n) z JL JM := fun f => by
      rw [hv Z (r ≫ f) z _ _ (hJM (r ≫ f ≫ n ≫ q)) (hJL (r ≫ f)), wv]
      simp only [Category.assoc, hn, Category.comp_id]
    have := hm Z r z (fun κ => JM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q)) (fun κ => JL (r ≫ (![s, m] : Fin 2 → _) κ))
      (fun κ => hJM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q)) (fun κ => hJL (r ≫ (![s, m] : Fin 2 → _) κ))
    rw [Fin.prod_univ_two, g, g] at this
    rw [val_of b _ z JM (fun κ => JM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q))
      (fun κ => by rw [hc', Category.assoc])]
    exact this
  rw [key Z r z JL JM hJL hJM]
  refine congrArg _ (gen_unique hL p e he hp hα' hα (fun y J hJ => ?_) Z r z JL hJL)
  choose J' hJ' using fun ψ : S₀ ⟶ N => exists_chart hM (ψ y)
  exact mul_left_cancel ((key _ e y J J' hJ hJ').symm.trans (h₀ y J J' hJ hJ'))

end Abstract

section Rig

variable {S Z : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

abbrev rval (rig : LB.Gen (L.pull (eSec A))) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    (Z.presheaf.stalk z)ˣ := val (L := L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J

theorem val_rigT {T : Over S} (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (r : Z ⟶ T.left) {y : Z} {J} (hJ : Good L y J) :
    val (rigT A L rig T k) r y J = rval rig (r ≫ T.hom) y J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ y _ hy _).trans ?_))
  exact gm_pull r T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem exists_two (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hr : rig.IsGen) (a : A.left ⟶ A.left) (k' k : ℤ)
    (β : LB.Gen (LB.LinComb L (K := Fin 3) ![𝟙 _, a, (1 : A ⟶ A).left] ![k', -k, k - k'])) (hβ : β.IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 _, a] ![k', -k]), b.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
        val b r z J = val β r z J * rval rig (r ≫ A.hom) z J ^ (k' - k) := by
  obtain ⟨b, hb, hv⟩ := exists_gen hL (φ' := ![𝟙 _, a]) (ε' := ![k', -k]) (fun U _ h => by
      have e : (1 : A ⟶ A).left = A.hom ≫ eSec A := rfl
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_three, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val, e]
      rw [_root_.mul_assoc, ← zpow_add, sub_add_sub_cancel, sub_self, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ β (rigT A L rig A (k' - k)))
    (mulGen_isGen _ _ _ _ _ _ _ hβ (GlobalTheory.NormTheta.rigT_isGen hr _))
  exact ⟨b, hb, fun Z r z J hJ => (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans
    (congrArg _ (val_rigT rig _ r hJ)))⟩

end Rig

theorem alg_origin {M : Type} [CommGroup M] {w r g : M} (k' k : ℤ) (h : w * r = g) :
    1 * g ^ (k' - k) = w ^ k' * w ^ (-k) * r ^ (k' - k) := by
  rw [← h, _root_.one_mul, mul_zpow, ← zpow_add, sub_eq_add_neg]

theorem dualNumber_unit_mul_decomposition {M : Type} [CommRing M] {w w' α b : Mˣ} {v v' t t' : M} {k' k : ℕ}
    (h₁ : v' = (w ^ k').val * t') (h₂ : v = (w' ^ k).val * t) (h₃ : t' = α.val * t)
    (h₄ : b = w ^ (k' : ℤ) * w' ^ (-(k : ℤ)) * α) : v' = v * b.val := by
  have e : w ^ k' * α = w' ^ k * b := by
    rw [h₄, zpow_neg, zpow_natCast, zpow_natCast, mul_comm (w ^ k') _⁻¹, _root_.mul_assoc, mul_inv_cancel_left]
  rw [h₁, h₂, h₃, ← _root_.mul_assoc, ← Units.val_mul, e, Units.val_mul, mul_right_comm]

theorem twist_through_iso : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U) (F : Type) [Field F] [Algebra (FractionRing R) F] (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ β (eSec G)) (LB.oneGen U.LG.L) → ∀ (w₀ : W0 U) (ρ), NormW U w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') (v : U.SecGF F k) (v' : U.SecGF F k'), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) v → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k' (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) v' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval v' (𝟙 _) y J = sval v (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y J * (val β (UnifPre.gFK (G := G) F) y J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (UnifPre.gFK (G := G) F ≫ G.hom) y J ^ ((k' : ℤ) - k)).val := by
  intro hG R _ _ I D A G _ _ U E F _ _ k' k β hβ nβ w₀ ρ hw ψ m hm hψ hm' α hα nα t t' v v' H H' HT y J hJ
  have := U.gen_hom
  have := E.homA
  have := E.homG
  obtain ⟨b, hb, vb⟩ := exists_two U.LG.isLB U.LG.rigGen E.aG.left (k' : ℤ) (k : ℤ) β hβ
  have hn : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have hn' : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  have f₁ : ((Over.pullback (jK R)).map E.aG).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ E.aG.left := pullback.lift_fst _ _ _
  have f₂ : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK R)).map E.aG := by
    rw [Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]
  have f₃ : m.left ≫ U.gen.inv.left =
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left) ≫ ((Over.pullback (jK R)).map E.aG).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, hm', Category.assoc, f₂, Category.assoc]
  have hc : m.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ E.aG.left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) f₃).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) f₁).trans (by simp only [Category.assoc]))))
  have o₀ : eSec A.A ≫ U.gen.inv.left = eSec ((Over.pullback (jK R)).obj G) := by
    rw [← EvalZero.eK_gen U, Category.assoc, hn', Category.comp_id]
  have o₁ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left =
      jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G) := by
    rw [← Category.assoc, ← Over.comp_left, ptSecT, lift_snd, ← o₀]; rfl
  have o₂ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ m.left ≫ U.gen.inv.left =
      jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G) := by
    rw [← Category.assoc, ← Over.comp_left, hm', ptSecT, lift_snd_assoc, MonObj.one_comp, ← o₀]; rfl
  have o₃ : (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) ≫ U.gen.hom.left = jFK (R := R) F ≫ eSec A.A :=
    (Category.assoc _ _ _).trans (congrArg _ (EvalZero.eK_gen U))
  have o₄ : (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) ≫ pullback.fst G.hom (jK R) =
      (jFK (R := R) F ≫ jK R) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg _ EvalZero.eK_fst).trans (Category.assoc _ _ _).symm)
  have o₅ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫
      pullback.fst G.hom (jK R) = (jFK (R := R) F ≫ jK R) ≫ eSec G :=
    Eq.trans (Eq.trans (by simp only [Category.assoc]) (congrArg (· ≫ _) o₁)) o₄
  have o₆ : ((jFK (R := R) F ≫ jK R) ≫ eSec G) ≫ G.hom = jFK (R := R) F ≫ jK R :=
    (Category.assoc _ _ _).trans ((congrArg _ (Over.w η[G])).trans (Category.comp_id _))
  obtain ⟨JA, hA⟩ : ∃ JA, Good A.L y JA := by
    choose J' hJ' using fun χ : (UnifPre.GF (G := G) F).left ⟶ A.A.left => exists_chart A.isLB (χ y)
    exact ⟨J', hJ'⟩
  have key := val_through_iso A.isLB U.LG.isLB hw.1 U.gen.inv.left hn (snd (TFK (R := R) F) A.A).left m.left
    E.aG.left hc k' k b hb α hα (fst (TFK (R := R) F) A.A).left (ptSecT A.A 1).left
    (by rw [← Over.comp_left, ptSecT, lift_fst]; rfl) (surj_fst hG A.isAb _) (fun z JL JM hL hM => by
      have a₁ := (val_pull hM β (eSec G) (jFK (R := R) F ≫ jK R)).symm.trans
        ((val_corr hM nβ (jFK (R := R) F ≫ jK R)).trans (val_one _))
      have a₂ := (val_pull hL α _ (𝟙 _)).symm.trans ((val_corr hL nα (𝟙 _)).trans (val_rigT ρ _ _ hL))
      rw [Category.id_comp, Category.id_comp] at a₂
      have a₃ : wv w₀ (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) z JL JM * rval ρ (jFK (R := R) F) z JL =
          rval U.LG.rig (jFK (R := R) F ≫ jK R) z JM := by
        refine Units.ext (Eq.trans ?_ (EvalZero.normW_ext U F hw z hL hM))
        rw [← o₃, ← o₄]
        rfl
      rw [o₅, o₁, o₂, vb _ _ z JM hM]
      refine (congrArg₂ (· * ·) a₁ (congrArg (fun x => rval U.LG.rig x z JM ^ ((k' : ℤ) - k)) o₆)).trans ?_
      exact (alg_origin _ _ a₃).trans (congrArg _ a₂.symm)) (U.genF F).left y JA J hA hJ
  have g₁ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_snd_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have g₂ : (U.genF F).left ≫ m.left ≫ U.gen.inv.left = (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left ≫
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, hm', Category.assoc, f₂, lift_snd_assoc, Category.assoc,
      Iso.hom_inv_id_assoc, whiskerLeft_snd]
  have g₃ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      UnifPre.gFK (G := G) F := Eq.trans (by simp only [Category.assoc]) (congrArg (· ≫ _) g₁)
  have g₄ : (U.genF F).left ≫ ψ.left = (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left ≫ (U.genF F).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, hψ, Category.assoc, lift_fst, whiskerLeft_fst]
    · rw [Category.assoc, hm, hm', Category.assoc, lift_snd, lift_snd_assoc, whiskerLeft_snd_assoc, E.ext,
        Category.assoc]
  rw [g₃, g₁, g₂, vb _ _ y J hJ] at key
  have b₁ := GlobalTheory.BoxExpansion.isoRel_val H' (𝟙 _) y hA hJ
  have b₂ := GlobalTheory.BoxExpansion.isoRel_val H (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y hA hJ
  have b₃ := twist_val HT (U.genF F).left y hA
  rw [Category.comp_id, Category.id_comp, Category.id_comp] at b₁
  rw [Category.comp_id, ← g₄] at b₂
  exact dualNumber_unit_mul_decomposition b₁ b₂ b₃ key

end GlobalTheory.UT.TwistCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO CoefBasic

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}

theorem sep (D : DegData V (maximalIdeal V)) : D.toPre.P.A.left.IsSeparated := by
  have := D.toPre.P.isAb.proper
  exact ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩

theorem lift_left (q : TF (R := V) F ⟶ D.toPre.P.A) : ∃ ψ, q.left = (ιS hϖ hv).left ≫ ψ := by
  obtain ⟨m, rfl⟩ := exists_liftO hϖ hv q
  exact ⟨m.left, rfl⟩

theorem exists_genV_gt (g : GtPtF D.toPre F) (χ : D.toPre.X) : ∃ r, GenV hϖ hv (g.s χ) r :=
  exists_genV D.toPre.P.isLB (g.isGen χ) fun i => by fin_cases i <;> exact lift_left _

theorem exists_genV_frm {k : ℕ} {b : TF (R := V) F ⟶ D.toPre.P.A} {w : Frm D.toPre F k b} (hw : w.IsGen) :
    ∃ r, GenV hϖ hv w r :=
  exists_genV D.toPre.P.isLB hw fun i => by fin_cases i <;> exact lift_left _

theorem hv_cub (x x' y : TF (R := V) F ⟶ D.toPre.P.A) :
    HV hϖ hv D.toPre.P.L (fun _ _ h => h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ *
      (h (x' * y).left)⁻¹ * h x.left * h x'.left * h y.left * (h (1 : TF (R := V) F ⟶ D.toPre.P.A).left)⁻¹)
      (fun z J => (th D.toPre z J x x' y).val) 1 := by
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv x
  obtain ⟨m', hm'⟩ := exists_liftO hϖ hv x'
  obtain ⟨n, hn⟩ := exists_liftO hϖ hv y
  exact (hv_gen (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.isGen
    (lift m (lift m' n)).left (r := (lift x (lift x' y)).left)
    (by rw [← Over.comp_left, comp_lift, comp_lift, hm, hm', hn])).congr (fun U _ h => prod_cub x x' y h)
    (fun _ _ _ => rfl)

theorem add_of_cub {g g' g'' : GtPtF D.toPre F} {χ χ' χ'' : D.toPre.X} {x x' y : TF (R := V) F ⟶ D.toPre.P.A}
    {r r' r'' : ℚ} (a : GenV hϖ hv (g.s χ) r) (a' : GenV hϖ hv (g'.s χ') r') (a'' : GenV hϖ hv (g''.s χ'') r'')
    (hσ : ∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ D.toPre.P.A.left) → U),
      (∏ i, h (DegPre.gtφ D.toPre F g''.b χ'' i) ^ DegPre.gtε i) * (h (x * x' * y).left * (h (x * x').left)⁻¹ *
        (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left * h y.left *
        (h (1 : TF (R := V) F ⟶ D.toPre.P.A).left)⁻¹) =
      (∏ i, h (DegPre.gtφ D.toPre F g.b χ i) ^ DegPre.gtε i) * ∏ i, h (DegPre.gtφ D.toPre F g'.b χ' i) ^ DegPre.gtε i)
    (hf : ∀ z J, Good D.toPre.P.L z J → val (g''.s χ'') (𝟙 _) z J * th D.toPre z J x x' y =
      val (g.s χ) (𝟙 _) z J * val (g'.s χ') (𝟙 _) z J) : r'' = r + r' := by
  have := sep D
  obtain ⟨c, hc, H⟩ := hv_of_genV a
  obtain ⟨c', hc', H'⟩ := hv_of_genV a'
  obtain ⟨c'', hc'', H''⟩ := hv_of_genV a''
  have e := (H''.mul (hv_cub x x' y)).cmp D.toPre.P.isLB (H.mul H') hσ
    (fun z J hJ => by simpa only [Units.val_mul] using congrArg Units.val (hf z J hJ).symm)
  rw [_root_.mul_one, AddValuation.map_mul, hc, hc', hc''] at e
  exact_mod_cast e

theorem exists_gtV (g : GtPtF D.toPre F) : ∃! l : D.toPre.X →+ ℚ, GtV hϖ hv g l := by
  have := sep D
  choose l hl using exists_genV_gt (hϖ := hϖ) (hv := hv) g
  refine ⟨AddMonoidHom.mk' l fun χ χ' => add_of_cub (x := cP D.toPre _ χ) (x' := cP D.toPre _ χ') (y := g.b)
    (hl χ) (hl χ') (hl (χ + χ')) (fun U _ h => ?_) (fun z J hJ => ?_), hl,
    fun l' hl' => AddMonoidHom.ext fun χ => genV_unique D.toPre.P.isLB (hl' χ) (hl χ)⟩
  · rw [prod_gt, prod_gt, prod_gt, cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have e := gt_mul (𝟙 (TF (R := V) F)) hJ g χ χ'
    rwa [Category.id_comp, Over.id_left] at e

theorem gtV_add {g g' g'' : GtPtF D.toPre F} {l l' : D.toPre.X → ℚ} (h : g.IsAdd g' g'') (a : GtV hϖ hv g l)
    (a' : GtV hϖ hv g' l') : GtV hϖ hv g'' (l + l') := fun χ => by
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 h
  obtain ⟨r, hr⟩ := exists_genV_gt (hϖ := hϖ) (hv := hv) g'' χ
  have e := add_of_cub (x := cP D.toPre _ χ) (x' := g.b) (y := g'.b) (a χ) (a' χ) hr (fun U _ h => by
    rw [prod_gt, prod_gt, prod_gt, hb, ← _root_.mul_assoc (cP D.toPre _ χ) g.b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel) (hs χ)
  rwa [e] at hr

theorem genV_frmOne {k : ℕ} {b : TF (R := V) F ⟶ D.toPre.P.A} {w : Frm D.toPre F k b} (hw : FrmOne w) (hb : b = 1) :
    GenV hϖ hv w 0 := by
  have := sep D
  obtain ⟨r, hr⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw.1
  obtain ⟨c, hc, H⟩ := hv_of_genV hr
  have e := H.cmp D.toPre.P.isLB HV.one (fun U _ h => by rw [prod_line, hb, mul_inv_cancel])
    (fun z J hJ => by simp only [hw.2 z J hJ, Units.val_one])
  rw [hc, AddValuation.map_one] at e
  obtain rfl : r = 0 := by exact_mod_cast e
  exact hr

theorem gtV_qk (hVR : VRatioGtStatement) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k)
    (p : QkPt D.toPre F k) : GtV hϖ hv p.g fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / k := fun α => by
  have hL := D.toPre.P.isLB
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv (D := D) p.g.b
  obtain ⟨G₀, hG₀⟩ := exists_gen_of_local D.toPre.P.L hL (gtφO hϖ hv m α) DegPre.gtε
  have hg : ∀ i, DegPre.gtφ D.toPre F p.g.b α i = (ιS hϖ hv).left ≫ gtφO hϖ hv m α i := by
    intro i; fin_cases i
    · show (padd D.toPre.P.A (DegPre.cF D.toPre F α) p.g.b).left = (ιS hϖ hv).left ≫ (cP D.toPre _ α * m).left
      rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hm]; rfl
    · show (DegPre.cF D.toPre F α).left = (ιS hϖ hv).left ≫ (cP D.toPre _ α).left
      rw [← Over.comp_left, comp_cP]; rfl
    · show p.g.b.left = (ιS hϖ hv).left ≫ m.left
      rw [← Over.comp_left, hm]
    · show (DegPre.zeroF D.toPre F).left = (ιS hϖ hv).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left
      rw [← Over.comp_left, MonObj.comp_one]; rfl
  obtain ⟨t, -, ht⟩ := exists_ratio hL (p.g.s α) (p.g.isGen α)
    (LB.pullGen D.toPre.P.L _ _ G₀ (ιS hϖ hv).left) (pullGen_isGen _ _ _ _ hG₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hg])
  have ht' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
        (val G₀ (r ≫ (ιS hϖ hv).left) z J).val := fun Z r z J hJ => by
    rw [ht Z r z J hJ, val_pull hJ]
  obtain ⟨q, hq, hkq⟩ := hVR V ϖ hϖ D Q hQ F v hv k hk p m hm α G₀ hG₀ t ht'
  refine ⟨gtφO hϖ hv m α, hg, G₀, hG₀, t, ?_, fun z J hJ => ?_⟩
  · simp only [hq, ← hkq, mul_div_cancel_left₀ _ hk0]
  · have e := ht' _ (𝟙 _) z J hJ
    rwa [Category.id_comp] at e

theorem gtV_iota (hVR : VRatioGtStatement) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {g : GtPtF D.toPre F}
    {y : D.toPre.X} (h : GtPtF.IsIota y g) : GtV hϖ hv g fun χ => (QForm.bOf D.toPre Q y χ : ℚ) := by
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := F)
  obtain ⟨hb, hs⟩ := (isZero_iff o).1 ho
  have hadd : o.IsAdd g g := (isAdd_iff _ _ _).2 ⟨by rw [hb, _root_.one_mul], fun χ z J hJ => by
    have C : IsCub (th D.toPre (T := TF (R := V) F) z J) := isCub_cubV D.toPre.cub hJ
    rw [hs χ z J hJ, hb, C.face₂, mul_comm]⟩
  have hn : GtPtF.IsNsmul 1 g g := by
    refine ⟨![o, g], ?_, fun i => ?_, rfl⟩
    · simpa only [Matrix.cons_val_zero] using ho
    · fin_cases i; exact hadd
  have e := gtV_qk (hϖ := hϖ) (hv := hv) hVR hQ (le_refl 1) ⟨y, g, g, hn, h⟩
  simpa only [Nat.cast_one, div_one] using e

theorem le_v_int {k : ℕ} {g : GtPtF D.toPre F} {w : Frm D.toPre F k g.b} {χ : D.toPre.X} {σ : D.toPre.SecB k χ} {σF}
    (hσ : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) σF
      (D.toPre.famφB χ) (DegPre.famε k) σ (DegPre.prB D.toPre F).left 1) {x : F} (hx : IsCoef k g w χ σF x)
    {l ω : ℚ} (hl : GenV hϖ hv (g.s χ) l) (hω : GenV hϖ hv w ω) : ((l + ω : ℚ) : WithTop ℚ) ≤ v x := by
  have := sep D
  have hL := D.toPre.P.isLB
  obtain ⟨c, hc, H⟩ := hv_of_genV hl
  obtain ⟨c', hc', H'⟩ := hv_of_genV hω
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv g.b
  obtain ⟨a, ha, A⟩ := hv_sec (hϖ := hϖ) (hv := hv) hL σ m.left (r := g.b.left) (by rw [← Over.comp_left, hm])
  have R := ((hv_gen (hϖ := hϖ) (hv := hv) (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1)
    D.toPre.rig_gen (TO hϖ hv).hom (Over.w (ιS hϖ hv))).pow k).smul x
  have e := R.cmp hL ((A.mul H).mul H') (fun U _ h => by
      have e₀ : (TF (R := V) F).hom ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := rfl
      have e₁ : SectionScalarValuation.cQ D.toPre (TF (R := V) F) χ = cP D.toPre _ χ := rfl
      rw [SectionScalarValuation.prod_famB, prod_gt, prod_line, Fintype.prod_unique, e₀, e₁, mul_comm g.b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (fun z J hJ => by
      have e₂ := SectionScalarValuation.secScal_sval hσ (lift (𝟙 (TF (R := V) F)) g.b).left z hJ
      rw [← Over.comp_left, lift_snd] at e₂
      have e₃ := hx z J hJ
      rw [← e₂] at e₃
      exact e₃.symm)
  rw [one_pow, _root_.mul_one, AddValuation.map_mul, AddValuation.map_mul, hc, hc'] at e
  rw [e, WithTop.coe_add]
  exact add_le_add_left (le_add_of_nonneg_left ha) _

theorem le_v_coef {k : ℕ} {g : GtPtF D.toPre F} {w : Frm D.toPre F k g.b} (hw : w.IsGen) {χ : D.toPre.X}
    {s : Fam D.toPre F k} {r l ω : ℚ} (hs : VGe D F v k χ (s.s χ) r) (hl : GenV hϖ hv (g.s χ) l)
    (hω : GenV hϖ hv w ω) : ((r + l + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) := by
  obtain ⟨n, a, σ, σF, hσ, ha, hsum⟩ := hs
  choose x hx using fun i => exists_isCoef g hw χ (σF i)
  have e : coef s g w χ = ∑ i, a i * x i := coef_eq fun z J hJ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [SectionScalarValuation.sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) _ z hJ, cst_eq, map_sum, Finset.sum_mul,
      Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have b : gs (lift (𝟙 (TF (R := V) F)) g.b).left z ⊤ (gF D.toPre F (a i)) = cst F z (a i) := by
      refine (gs_pull _ (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl
    have c := hx i z J hJ
    rw [b, map_mul, ← cst_eq, ← cst_eq, _root_.mul_assoc, c]
    ring
  rw [e]
  refine AddValuation.map_le_sum v fun i _ => ?_
  rw [AddValuation.map_mul, add_assoc, WithTop.coe_add]
  exact add_le_add (ha i) (le_v_int (hσ i) (hx i) hl hω)

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ g : GtPtF D.toPre F, (∃! l : D.toPre.X →+ ℚ, GtV hϖ hv g l) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), w.IsGen → ∃! r, GenV hϖ hv w r) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), FrmOne w → g.b = 1 → GenV hϖ hv w 0) ∧ (∀ (g' g'' : GtPtF D.toPre F) l l', g.IsAdd g' g'' → GtV hϖ hv g l → GtV hϖ hv g' l' → GtV hϖ hv g'' (l + l')) ∧ (∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, GtV hϖ hv p.g fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / k) ∧ (∀ y, GtPtF.IsIota y g → GtV hϖ hv g fun χ => (QForm.bOf D.toPre Q y χ : ℚ)) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (w : Frm D.toPre F k g.b) (s : Fam D.toPre F k), w.IsGen → NullV v (coef s g w) ∧ ∀ l ω r, GtV hϖ hv g l → GenV hϖ hv w ω → NuGe D Q F v k s r → ∀ χ, ((r + (Q χ : ℚ) / k + l χ + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) := by
  intro _ hTW hVR _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv g
  have := sep D
  have bound : ∀ (k : ℕ) (w : Frm D.toPre F k g.b) (s : Fam D.toPre F k), w.IsGen → ∀ l ω r, GtV hϖ hv g l →
      GenV hϖ hv w ω → NuGe D Q F v k s r →
      ∀ χ, ((r + (Q χ : ℚ) / k + l χ + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) :=
    fun k w s hw l ω r hl hω hs χ => le_v_coef hw (hs χ) (hl χ) hω
  refine ⟨exists_gtV g, fun k w hw => ?_, fun k w => genV_frmOne, fun g' g'' l l' => gtV_add,
    fun k hk p => gtV_qk hVR hQ hk p, fun y => gtV_iota hVR hQ, fun k hk w s hw => ⟨fun q => ?_, bound k w s hw⟩⟩
  · obtain ⟨r, hr⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw
    exact ⟨r, hr, fun r' hr' => genV_unique D.toPre.P.isLB hr' hr⟩
  · obtain ⟨l, hl, -⟩ := exists_gtV (hϖ := hϖ) (hv := hv) g
    obtain ⟨ω, hω⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw
    obtain ⟨r, hr⟩ := exists_nuGe hϖ hv hTW hQ hk s
    refine (finite_sublevel hϖ hQ hk l (q - r - ω)).subset fun χ hχ => ?_
    have h : r + (Q χ : ℚ) / k + l χ + ω < q := WithTop.coe_lt_coe.1 ((bound k w s hw l ω r hl hω hr χ).trans_lt hχ)
    show (Q χ : ℚ) / k + l χ ≤ q - r - ω
    linarith

end GlobalTheory.UT.CoefVal
end
end

