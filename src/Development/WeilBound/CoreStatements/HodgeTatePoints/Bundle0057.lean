module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.PpicLamdiff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ppic
open GlobalTheory.CechPic GlobalTheory.UU

noncomputable def tqOfIso {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (T : TQ G X) {A : Over S}
    [GrpObj A] (hA : IsAbelianScheme A) (β : T.B ≅ A) [IsMonHom β.hom] : TQ G X :=
  haveI : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  { B := A
    comm := hA.comm
    isAb := hA
    q := T.q ≫ β.hom
    i := T.i
    q_hom := by have := T.q_hom; infer_instance
    i_hom := T.i_hom
    q_flat := by have := T.q_flat; rw [Over.comp_left]; infer_instance
    q_surj := by have := T.q_surj; rw [Over.comp_left]; infer_instance
    q_affine := by have := T.q_affine; rw [Over.comp_left]; infer_instance
    isKernel := by
      have sq : IsPullback η[T.B] (𝟙 _) β.hom η[A] :=
        IsPullback.of_vert_isIso ⟨by rw [IsMonHom.one_hom, Category.id_comp]⟩
      have h := T.isKernel.paste_vert sq
      rwa [Category.comp_id] at h
    loc := fun b χ => by
      obtain ⟨V, hV, u, hu⟩ := T.loc (β.inv.left b) χ
      have le : (T.q ≫ β.hom).left ⁻¹ᵁ (β.inv.left ⁻¹ᵁ V) ≤ T.q.left ⁻¹ᵁ V := by
        rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, Category.assoc, β.hom_inv_id, Category.comp_id]
      exact ⟨β.inv.left ⁻¹ᵁ V, hV, res le u, hu.res le⟩ }

theorem lamdiff : (∀ (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (T : GlobalTheory.UU.TQ G X) (N : LB T.B.left), N.IsLB → ∀ t : LB.Gen (N.pull T.q.left), t.IsGen → ∃ (χ : X) (t' : LB.Gen (N.pull T.q.left)), T.GenWt N t' χ) → ∀ (Q : Out.PolAV (Sp ℂ)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] (T : GlobalTheory.UU.TQ G X) (β : T.B ≅ Q.A), IsMonHom β.hom → ∀ M : LB Q.A.left, M.IsLB → LBIso (M.pull (T.q ≫ β.hom).left) (Q.L.pull (T.q ≫ β.hom).left) → ∃ u : LB.Gen (abelian₂ Q.A (LB.div M Q.L)), u.IsGen := by
  intro hw Q X _ _ _ G _ _ T β hβ M hM hiso
  haveI := hβ
  have hL := Q.isLB
  have hN : (LB.div M Q.L).IsLB := LB.isLB_div hM hL
  have hNp : ((LB.div M Q.L).pull (T.q ≫ β.hom).left).IsLB := LB.isLB_pull hN _
  have hc : cls ((LB.div M Q.L).pull (T.q ≫ β.hom).left) hNp = 0 := by
    rw [cls_pull hN _ hNp, cls_div hM hL hN, map_sub,
      ← cls_pull hM _ (LB.isLB_pull hM _), ← cls_pull hL _ (LB.isLB_pull hL _), sub_eq_zero]
    exact (cls_eq_iff _ _).2 hiso
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff hNp).1 hc
  let T' := tqOfIso T Q.isAb β
  obtain ⟨χ, t', ht'⟩ := hw ℂ X G T' (LB.div M Q.L) hN t ht
  obtain ⟨N', s, hN', hs, u, hu⟩ := GlobalTheory.WtBundle.exists_genWt T' χ
  have hI : LBIso (LB.div M Q.L) N' := GlobalTheory.UU.lbIso_of_genWt _ X G T' _ N' t' s χ hN hN' ht' hs
  have hLam : (abelian₂ Q.A (LB.div M Q.L)).IsLB := LB.isLB_linComb hN _ _
  have hLam' : (abelian₂ Q.A N').IsLB := LB.isLB_linComb hN' _ _
  have h0 := (cls_eq_zero_iff hLam').2 ⟨u, hu⟩
  refine (cls_eq_zero_iff hLam).1 ?_
  refine (cls_linComb hN _ _ hLam).trans ?_
  rw [(cls_eq_iff hN hN').2 hI]
  exact (cls_linComb hN' _ _ hLam').symm.trans h0

end PositivityTheory.HtPt.Ppic
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.PpicQuot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ppic

theorem exists_factor_torus {K : Type} [Field K] [IsAlgClosed K] {G B B' : Over (Sp K)} [GrpObj G] [GrpObj B] [GrpObj B']
    (hB' : IsAbelianScheme B') {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i : splitTorus (Sp K) X ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] [Flat q.left] [Surjective q.left]
    [QuasiCompact q.left] (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (f : G ⟶ B') [IsMonHom f] :
    ∃ a : B ⟶ B', q ≫ a = f := by
  haveI : IsProper B'.hom := hB'.proper
  have hif : i ≫ f = toUnit _ ≫ η :=
    GlobalTheory.splitTorus_hom_proper_trivial_field K X B' (i ≫ f) inferInstance
  refine GlobalTheory.ExtensionRigidity.exists_factor q f ?_
  intro W a b hab
  have h1 := map_div (IsMonHom.monoidHom q W) a b
  simp only [IsMonHom.monoidHom_apply] at h1
  rw [hab, div_self'] at h1
  have hc : (a / b) ≫ q = toUnit W ≫ η := by rw [h1, Hom.one_def]
  have e2 : (a / b) ≫ f = 1 := by
    rw [← hk.lift_fst (a / b) (toUnit W) hc, Category.assoc, hif, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have h3 := map_div (IsMonHom.monoidHom f W) a b
  simp only [IsMonHom.monoidHom_apply] at h3
  rw [e2] at h3
  exact div_eq_one.1 h3.symm

theorem quot : ∀ (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] (τ : TorusExtension G) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : GlobalTheory.UU.TQ G X), letI := τ.grpB; ∃ e : τ.B ≅ T.B, IsMonHom e.hom ∧ τ.q ≫ e.hom = T.q := by
  intro G _ _ τ X _ _ _ T
  letI := τ.grpB
  letI := τ.addCommGroup
  haveI := τ.free
  haveI := τ.finite
  haveI := τ.q_hom
  haveI := τ.q_flat
  haveI := τ.q_surjective
  haveI := τ.q_quasiCompact
  haveI := τ.i_hom
  haveI := T.q_hom
  haveI := T.q_flat
  haveI := T.q_surj
  haveI := T.q_affine
  haveI := T.i_hom
  obtain ⟨a, ha⟩ := exists_factor_torus T.isAb τ.i τ.q τ.isKernel T.q
  obtain ⟨b, hb⟩ := exists_factor_torus τ.isAbelian T.i T.q T.isKernel τ.q
  haveI : Epi τ.q := Over.epi_of_epi_left _
  haveI : Epi T.q := Over.epi_of_epi_left _
  haveI : MorphismProperty.IsStableUnderComposition @Surjective :=
    { comp_mem := fun f g hf hg => by haveI := hf; haveI := hg; infer_instance }
  haveI : Epi (τ.q ⊗ₘ τ.q) := by
    haveI : Flat (τ.q ⊗ₘ τ.q).left :=
      MorphismProperty.pullbackMap (P := @Flat) τ.q_flat τ.q_flat (Over.w τ.q).symm (Over.w τ.q).symm
    haveI : Surjective (τ.q ⊗ₘ τ.q).left :=
      MorphismProperty.pullbackMap (P := @Surjective) τ.q_surjective τ.q_surjective
        (Over.w τ.q).symm (Over.w τ.q).symm
    haveI : QuasiCompact (τ.q ⊗ₘ τ.q).left :=
      MorphismProperty.pullbackMap (P := @QuasiCompact) τ.q_quasiCompact τ.q_quasiCompact
        (Over.w τ.q).symm (Over.w τ.q).symm
    exact Over.epi_of_epi_left _
  have hma : IsMonHom a := by
    refine ⟨?_, ?_⟩
    · rw [← IsMonHom.one_hom τ.q, Category.assoc, ha, IsMonHom.one_hom]
    · rw [← cancel_epi (τ.q ⊗ₘ τ.q), ← IsMonHom.mul_hom_assoc, ha, IsMonHom.mul_hom,
        tensorHom_comp_tensorHom_assoc, ha]
  refine ⟨⟨a, b, ?_, ?_⟩, hma, ha⟩
  · rw [← cancel_epi τ.q, reassoc_of% ha, hb, Category.comp_id]
  · rw [← cancel_epi T.q, reassoc_of% hb, ha, Category.comp_id]

end PositivityTheory.HtPt.Ppic
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.PpicWeight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ppic
open GlobalTheory.UU ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

theorem unit_prod_eq_one {K : Type} [Field K] [IsAlgClosed K] {A B : Over (Sp K)} [GeometricallyIntegral (A ⊗ B).hom]
    (a : 𝟙_ (Over (Sp K)) ⟶ A) (b : 𝟙_ (Over (Sp K)) ⟶ B) (v : Γ((A ⊗ B).left, ⊤)) (hv : IsUnit v)
    (h₁ : (lift (𝟙 A) (toUnit A ≫ b)).left.appTop.hom v = 1)
    (h₂ : (lift (toUnit B ≫ a) (𝟙 B)).left.appTop.hom v = 1) : v = 1 := by
  let Y := A ⊗ B
  let e : 𝟙_ (Over (Sp K)) ⟶ Y := lift a b
  let m : Y ⊗ Y ⟶ Y := lift (fst Y Y ≫ fst A B) (snd Y Y ≫ snd A B)
  have h1 : (toUnit Y ≫ e).left = Y.hom ≫ e.left := by rw [Over.comp_left, toUnit_left]
  have e₁ : lift (𝟙 Y) (toUnit Y ≫ e) ≫ m = fst A B ≫ lift (𝟙 A) (toUnit A ≫ b) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp [m]
    · simp only [m, e, Category.assoc, lift_snd, lift_snd_assoc]
      rw [← Category.assoc, toUnit_unique (fst A B ≫ toUnit A) (toUnit _)]
  have e₂ : lift (toUnit Y ≫ e) (𝟙 Y) ≫ m = snd A B ≫ lift (toUnit B ≫ a) (𝟙 B) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp only [m, e, Category.assoc, lift_fst, lift_fst_assoc]
      rw [← Category.assoc, toUnit_unique (snd A B ≫ toUnit B) (toUnit _)]
    · simp [m]
  have e₃ : lift (𝟙 Y) (𝟙 Y) ≫ m = 𝟙 Y := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_ <;> simp [m, Y]
  have key : m.left.appTop.hom v = 1 := by
    refine GlobalTheory.UnitRigidity.unit_eq_one_of_axes Y.hom e.left (Over.w _) (lift (𝟙 Y) (toUnit Y ≫ e)).left
      (lift (toUnit Y ≫ e) (𝟙 Y)).left ?_ ?_ ?_ ?_ _ (hv.map _) ?_ ?_
    · exact congrArg (·.left) (lift_fst (𝟙 Y) (toUnit Y ≫ e))
    · exact (congrArg (·.left) (lift_snd (𝟙 Y) (toUnit Y ≫ e))).trans h1
    · exact (congrArg (·.left) (lift_fst (toUnit Y ≫ e) (𝟙 Y))).trans h1
    · exact congrArg (·.left) (lift_snd (toUnit Y ≫ e) (𝟙 Y))
    · refine (over_appTop_comp _ m v).trans ?_
      rw [e₁, ← over_appTop_comp, h₁, map_one]
    · refine (over_appTop_comp _ m v).trans ?_
      rw [e₂, ← over_appTop_comp, h₂, map_one]
  have := over_appTop_comp (lift (𝟙 Y) (𝟙 Y)) m v
  rw [key, map_one, e₃, Over.id_left, Scheme.Hom.id_appTop] at this
  exact this.symm

theorem appTop_chV {S : Scheme.{0}} {X : Type} [AddCommGroup X] {W Z : Over S} (p : W ⟶ Z) (t : Z ⟶ splitTorus S X)
    (χ : X) : p.left.appTop.hom (chV t χ).val = (chV (p ≫ t) χ).val := by
  rw [chV_val, chV_val, over_appTop_comp]

theorem chV_one {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (χ : X) :
    chV (1 : Z ⟶ splitTorus S X) χ = 1 := by rw [chV, map_one]; rfl

theorem unit_eq_char {K : Type} [Field K] [IsAlgClosed K] {X : Type} [AddCommGroup X] [TwoUniqueSums X]
    {G : Over (Sp K)} [GeometricallyIntegral (splitTorus (Sp K) X ⊗ G).hom] (b : 𝟙_ (Over (Sp K)) ⟶ G)
    (ρ : Γ((splitTorus (Sp K) X ⊗ G).left, ⊤)ˣ)
    (h : (lift (1 : G ⟶ splitTorus (Sp K) X) (𝟙 G)).left.appTop.hom ρ.val = 1) :
    ∃ χ : X, ρ = chV (fst (splitTorus (Sp K) X) G) χ := by
  let T := splitTorus (Sp K) X
  obtain ⟨c, χ, -, hc⟩ := torus_units K X (ρ.isUnit.map (lift (𝟙 T) (toUnit T ≫ b)).left.appTop.hom)
  have hχ : chi (S := Sp K) X χ = (chV (𝟙 T) χ).val := by
    rw [chV_val, Over.id_left, Scheme.Hom.id_appTop, GlobalTheory.SplitTorus.charUnit_val]
    rfl
  rw [hχ] at hc
  have c1 : T.hom.appTop.hom c = 1 := by
    have e := congrArg (1 : T ⟶ T).left.appTop.hom hc
    have q : (1 : T ⟶ T) ≫ lift (𝟙 T) (toUnit T ≫ b) = (toUnit T ≫ b) ≫ lift (1 : G ⟶ T) (𝟙 G) := by
      rw [comp_lift, comp_lift, Category.comp_id, Category.comp_id, MonObj.comp_one, ← Category.assoc,
        toUnit_unique (_ ≫ toUnit T) (toUnit T)]
    rw [over_appTop_comp, q, ← over_appTop_comp, h, map_one, map_mul, appTop_chV, Category.comp_id, chV_one,
      Units.val_one, _root_.mul_one, ← appTop_comp_apply, Over.w] at e
    exact e.symm
  rw [c1, _root_.one_mul] at hc
  refine ⟨χ, mul_inv_eq_one.1 (Units.ext ?_)⟩
  have inv : ∀ {W : Over (Sp K)} (p : W ⟶ T ⊗ G), p.left.appTop.hom ρ.val = (chV (p ≫ fst T G) χ).val →
      p.left.appTop.hom (ρ * (chV (fst T G) χ)⁻¹).val = 1 := fun p hp => by
    rw [Units.val_mul, map_mul, hp, ← appTop_chV, ← map_mul, Units.mul_inv, map_one]
  refine unit_prod_eq_one η[T] b _ (Units.isUnit _) (inv _ ?_) (inv _ ?_)
  · rw [lift_fst]
    exact hc
  · rw [lift_fst, ← Hom.one_def, chV_one]
    exact h

theorem weight : ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (T : GlobalTheory.UU.TQ G X) (N : LB T.B.left), N.IsLB → ∀ t : LB.Gen (N.pull T.q.left), t.IsGen → ∃ (χ : X) (t' : LB.Gen (N.pull T.q.left)), T.GenWt N t' χ := by
  intro k _ _ X _ _ _ G _ _ T N hN t ht
  have := T.q_hom
  have := T.i_hom
  let H := splitTorus (Sp k) X
  obtain ⟨_, _⟩ := GlobalTheory.TrivDescentCompare.smooth_conn T
  obtain ⟨_, _⟩ := GlobalTheory.TrivDescentCompare.smooth_conn (TQ.torus (Sp k) X)
  have : TwoUniqueSums X := inferInstance
  have : Smooth (H ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst H.hom G.hom ≫ H.hom))
  have : GeometricallyConnected (pullback.fst H.hom G.hom) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) (IsPullback.of_hasPullback H.hom G.hom).flip ‹_›
  have : GeometricallyConnected (H ⊗ G).hom := GeometricallyConnected.comp (pullback.fst H.hom G.hom) H.hom
  have : GeometricallyIntegral (H ⊗ G).hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have hq : ∀ (Z : Over (Sp k)) (s : Z ⟶ H) (g : Z ⟶ G), ((s ≫ T.i) * g).left ≫ T.q.left = g.left ≫ T.q.left :=
    fun Z s g => GlobalTheory.TrivDescentCompare.act_q T s g
  let a : H ⊗ G ⟶ G := (fst H G ≫ T.i) * snd H G
  obtain ⟨ρ, hρ⟩ := exists_ratio hN (φ := fun _ : PUnit => a.left ≫ T.q.left)
    (φ' := fun _ : PUnit => (snd H G).left ≫ T.q.left) (ε := fun _ => 1) (funext fun _ => hq _ _ _)
    (LB.pullGen N (fun _ : PUnit => T.q.left) (fun _ => 1) t a.left)
    (LB.pullGen N (fun _ : PUnit => T.q.left) (fun _ => 1) t (snd H G).left)
    (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _)
  have hv : ∀ (Z : Over (Sp k)) (s : Z ⟶ H) (g : Z ⟶ G) (z : Z.left) (J), Good N z J →
      val (L := N) (φ := fun _ : PUnit => T.q.left) (ε := fun _ => 1) t ((s ≫ T.i) * g).left z J =
        gm (lift s g).left z ⊤ ρ * val (L := N) (φ := fun _ : PUnit => T.q.left) (ε := fun _ => 1) t g.left z J := by
    intro Z s g z J hJ
    have e := hρ _ (lift s g).left z J hJ
    rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, lift_snd, MonObj.comp_mul, lift_fst_assoc,
      lift_snd] at e
    exact e
  obtain ⟨χ, hχ⟩ := unit_eq_char η[G] ρ (by
    have e : Units.map (lift (1 : G ⟶ H) (𝟙 G)).left.appTop.hom.toMonoidHom ρ = 1 := unit_ext fun z _ => by
      obtain ⟨J, hJ⟩ := exists_good_pt hN z
      have e := hv G 1 (𝟙 G) z J hJ
      rw [MonObj.one_comp, _root_.one_mul] at e
      rw [← gm_top, map_one]
      exact (right_eq_mul.1 e)
    exact congrArg Units.val e)
  refine ⟨χ, t, ht, fun j => isWt_of_gm _ χ fun Z s g z hz => ?_⟩
  obtain ⟨J, hJ, hj⟩ := exists_good N hN z (fun _ : PUnit => g.left ≫ T.q.left) j (fun _ _ _ => rfl)
    (fun _ => (mem_pull (L := N) (F := T.q.left)).1 hz)
  have e := hv Z s g z J hJ
  rw [val_of _ _ _ _ j (fun u => (congrArg J (hq Z s g)).trans (hj u)), val_of _ _ _ _ j hj] at e
  refine e.trans (congrArg (· * _) ?_)
  rw [gm_charUnit, gm_top, hχ]
  refine congrArg _ (Units.ext ?_)
  exact (appTop_chV _ _ _).trans (by rw [lift_fst])

end PositivityTheory.HtPt.Ppic
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.PquoFibre
section
namespace PositivityTheory.HtPt.Pquo

section BaseChange

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.UU

theorem exists_tq_baseChange_over : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G]
    (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F →
    ∀ Q : TQ G X, ∃ (Q' : TQ G' X) (p : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B f p ∧
      Q'.q.left ≫ p = F ≫ Q.q.left := by
  intro S S' f X _ G _ G' _ F hF Q
  obtain ⟨i', hi, -⟩ := existsUnique_torusCompat hF.1 Q.i
  have := Q.i_hom
  have := Q.q_hom
  have hA := Q.isAb
  let B' : Over S' := (Over.pullback f).obj Q.B
  let p : B'.left ⟶ Q.B.left := pullback.fst Q.B.hom f
  have hB : IsGrpPullback B' Q.B f p := isGrpPullback_pullback Q.B f
  have w : (F ≫ Q.q.left) ≫ Q.B.hom = G'.hom ≫ f := by rw [Category.assoc, Over.w, hF.1.w]
  let q' : G' ⟶ B' := Over.homMk (hB.1.lift _ _ w) (hB.1.lift_snd _ _ w)
  have hq : q'.left ≫ p = F ≫ Q.q.left := hB.1.lift_fst _ _ w
  have sq : IsPullback F q'.left Q.q.left p := by
    refine IsPullback.of_bot ?_ hq.symm hB.1
    rw [Over.w, Over.w]; exact hF.1
  have hAb : IsAbelianScheme B' := by
    have := hA.comm
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    exact
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd Q.B.hom f); infer_instance
        proper := by change IsProper (pullback.snd Q.B.hom f); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd Q.B.hom f); infer_instance }
  have ker : IsPullback i' (toUnit _) q' (η[B']) := by
    have k₀ : IsPullback Q.i.left (splitTorus S X).hom Q.q.left (η[Q.B]).left := by
      have := Q.isKernel.map (Over.forget S)
      rw [← Rosenlicht.toUnit_left]
      exact this
    have k₁ := (SplitTorus.isPullback_bcMap f X).paste_horiz k₀
    have e₁ : SplitTorus.bcMap f X ≫ Q.i.left = i'.left ≫ F := torusCompat_iff.1 hi
    have e₂ := eSec_comp_of_isGrpPullback hB
    have w' : i'.left ≫ q'.left = (splitTorus S' X).hom ≫ (η[B']).left := by
      refine hB.1.hom_ext ?_ ?_
      · rw [Category.assoc, hq, ← Category.assoc, ← e₁, k₁.w]
        exact (congrArg (_ ≫ ·) e₂.symm).trans (Category.assoc _ _ _).symm
      · rw [Category.assoc, Over.w, Over.w, Category.assoc, Over.w]
        exact (Category.comp_id _).symm
    rw [e₁] at k₁
    have k₂ : IsPullback i'.left (splitTorus S' X).hom q'.left (η[B']).left :=
      IsPullback.of_right (k₁.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
        (by simp) (by simpa using e₂.symm)) w' sq
    rw [← Rosenlicht.toUnit_left] at k₂ w'
    exact IsPullback.of_map (Over.forget S') (Over.OverMorphism.ext w') k₂
  refine ⟨{ B := B'
            comm := hAb.comm
            isAb := hAb
            q := q'
            i := i'
            q_hom := isMonHom_of_over_isMonHom hF hB Q.q q' hq
            i_hom := hi.isMonHom hF
            q_flat := MorphismProperty.of_isPullback (P := @Flat) sq Q.q_flat
            q_surj := MorphismProperty.of_isPullback (P := @Surjective) sq Q.q_surj
            q_affine := isAffineHom_isStableUnderBaseChange.of_isPullback sq Q.q_affine
            isKernel := ker
            loc := fun b χ => ?_ }, p, hB, hq⟩
  obtain ⟨V, hb, u, hu⟩ := Q.loc (p b) χ
  have hV : q'.left ⁻¹ᵁ p ⁻¹ᵁ V ≤ F ⁻¹ᵁ Q.q.left ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hq, Scheme.Hom.comp_preimage]
  exact ⟨p ⁻¹ᵁ V, hb, Units.map (F.appLE _ _ hV).hom.toMonoidHom u, hu.pull hF hi hV⟩

end BaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj


attribute [local instance] SplitExt.free SplitExt.finite in
theorem fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (Pu : PELUnif (IsLocalRing.maximalIdeal V) tV) (P : AbPart tV (spMap r)), ∃ (Q : Out.PolAV (Sp ℂ)) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (T : GlobalTheory.UU.TQ P.tK.G X) (β : T.B ≅ Q.A), IsMonHom β.hom ∧ LBIso P.tK.PP.L (Q.L.pull (T.q ≫ β.hom).left) := by
  intro E _ _ _ H V _ _ _ r tV _ hk Pu P
  obtain ⟨s, hs⟩ : ∃ s : V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1) →+* ℂ,
      s.comp (Ideal.Quotient.mk _) = r :=
    ⟨Ideal.Quotient.lift _ r fun a ha => by
      rw [zero_add, pow_one, ← hk] at ha
      exact ha, RingHom.ext fun _ => rfl⟩
  have e : spMap s ≫ Out.thick V (IsLocalRing.maximalIdeal V) 0 = spMap r := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]
  obtain ⟨Ex, -, d, π, hπ, hd, -⟩ := GlobalTheory.ZH.UFib.exists_gtDatum_of_gtCoord V _ Pu.D.toPre 0 tV.G (Pu.U.gt 0)
  have hG := isGrpPullback_pullback tV.G (Out.thick V (IsLocalRing.maximalIdeal V) 0)
  have w : P.m.φ ≫ tV.G.hom = (P.tK.G.hom ≫ spMap s) ≫ Out.thick V (IsLocalRing.maximalIdeal V) 0 := by
    rw [Category.assoc, e]
    exact P.m.cart.1.w
  obtain ⟨F, hF₁, hF₂⟩ : ∃ F : P.tK.G.left ⟶ (Out.thickObj V (IsLocalRing.maximalIdeal V) 0 tV.G).left,
      F ≫ pullback.fst tV.G.hom (Out.thick V (IsLocalRing.maximalIdeal V) 0) = P.m.φ ∧
      F ≫ (Out.thickObj V (IsLocalRing.maximalIdeal V) 0 tV.G).hom = P.tK.G.hom ≫ spMap s :=
    ⟨hG.1.lift _ _ w, hG.1.lift_fst _ _ w, hG.1.lift_snd _ _ w⟩
  have hF : IsGrpPullback P.tK.G (Out.thickObj V (IsLocalRing.maximalIdeal V) 0 tV.G) (spMap s) F :=
    IsGrpPullback.cancel hG (P.m.cart.congr e.symm hF₁.symm) hF₂
  obtain ⟨T, p, hp, hq⟩ := exists_tq_baseChange_over _ _ _ _ _ _ _ hF (GlobalTheory.UU.TQ.ofGtDatum d)
  obtain ⟨Q, φ, -, hφ, hQ⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap r) Pu.D.toPre.P
  obtain ⟨β, hβ, hβ'⟩ := grpPullback_iso ((IsGrpPullback.comp hp hπ).congr e rfl) hφ
  refine ⟨Q, Ex.X, inferInstance, inferInstance, inferInstance, T, β, hβ, ?_⟩
  have hc : (T.q ≫ β.hom).left ≫ φ = F ≫ (Pu.U.gt 0).pG.left := by
    rw [Over.comp_left, Category.assoc, hβ', ← hd]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) hq).trans (Category.assoc _ _ _))
  have h₁ : LBIso P.tK.PP.L (tV.PP.L.pull P.m.φ) := GlobalTheory.LN.GenericPoint.lbIso_of_sabMap P.m
  have h₂ : LBIso (Pu.U.LG.L.pull P.m.φ) (Pu.D.toPre.P.L.pull ((T.q ≫ β.hom).left ≫ φ)) :=
    LBIso.chartPull (chartPullSame Pu.U.LG.L _ _ _ F fun _ => hF₁.symm)
      (chartPullSame Pu.D.toPre.P.L _ _ _ F fun _ => hc) ⟨Pu.U.w 0, Pu.U.w_gen 0⟩
  rw [Pu.bundle] at h₂
  have h₃ : LBIso (Q.L.pull (T.q ≫ β.hom).left) (Pu.D.toPre.P.L.pull ((T.q ≫ β.hom).left ≫ φ)) :=
    GlobalTheory.LN.GenericPoint.lbIso_pull hQ _ rfl
  exact LBIso.trans P.tK.PP.isLB (pull_isLB tV.PP.isLB _) (pull_isLB Q.isLB _) h₁
    (LBIso.trans (pull_isLB tV.PP.isLB _) (pull_isLB Pu.D.toPre.P.isLB _) (pull_isLB Q.isLB _) h₂ h₃.symm)

end PositivityTheory.HtPt.Pquo
end

