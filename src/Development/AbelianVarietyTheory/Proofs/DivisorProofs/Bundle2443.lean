module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaValueSubsingletonBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

noncomputable section

namespace GlobalTheory.UPoinc.USum

theorem exists_isTwVal_of_subsingleton : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A), Subsingleton T.left → Odd m → N = m ^ 2 → τ.IsGen → x ^ N = 1 → h ^ m = β ≫ z₀ → ∃ v, IsTwVal P N m θ τ β x h v := by
  intro B P N m T₀ T θ z₀ τ β x h hT hm hN hτ hx hh
  subst hN
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hL := P.isLB
  obtain ⟨α, hα⟩ : ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left]
      ![((m ^ 2 : ℕ) : ℤ), -1]), α.IsGen := by
    rw [Nat.cast_pow]
    exact GlobalTheory.EmbLocal.exists_mulPull hG P m T
  obtain ⟨U, hU⟩ : ∃ U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) T, SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U := by
    rcases isEmpty_or_nonempty T.left with he | ⟨⟨p⟩⟩
    · exact GlobalTheory.GlobalLift.exists_symLift_empty hL (m ^ 2) x
    · obtain ⟨V, hV, H⟩ := GlobalTheory.EmbLocal.exists_symLift_near hG P (k := m ^ 2) hm.pow x hx p
      obtain ⟨θ', hθ'⟩ := H T (𝟙 T) (by
        rintro _ ⟨q, rfl⟩
        rwa [Subsingleton.elim ((𝟙 T : T ⟶ T).left q) p])
      rw [Category.id_comp] at hθ'
      exact ⟨θ', hθ'⟩
  rcases U with ⟨pt, φU, hφU⟩
  obtain rfl : x = pt := hU.pt_eq.symm
  obtain ⟨s, hs⟩ := GlobalTheory.VVRank.exists_isTwistPull P.A (ψ := mulT P.A T m) (m := snd T P.A ^ m) (hm := lift_snd _ _)
    (a := ((m ^ 2 : ℕ) : ℤ)) (b := 1) hL hα (GlobalTheory.VVRank.pullS P.A 1 β θ)
  obtain ⟨σ, hσ⟩ := GlobalTheory.VVRank.exists_isTwistPull P.A (ψ := translT P.A x) (m := translPt P.A x)
    (hm := lift_snd _ _) hL hφU s
  have e₁ : (ptSecT P.A h).left ≫ (snd T P.A).left = h.left := GlobalTheory.ThetaPtMove.ptSecT_snd h
  have e₂ : (ptSecT P.A h).left ≫ (snd T P.A ^ m).left = (h ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, GlobalTheory.ThetaCompare.pt_snd]
  have e₃ : β.left ≫ z₀.left = (h ^ m).left := by rw [← Over.comp_left, hh]
  obtain ⟨τ', hτ', vτ'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hL (φ' := fun _ : Fin 1 => h.left)
    (ε' := fun _ => ((m ^ 2 : ℕ) : ℤ))
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, e₃, zpow_neg, zpow_one]
      group)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A h).left) (LB.pullGen P.L _ _ τ β.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (DVR.pullGen_isGen _ _ _ _ hτ _))
  obtain ⟨v, hv⟩ := GlobalTheory.ThetaPtExist.exists_isValueAt hL σ h τ' hτ'
  refine ⟨v, α, ⟨x, φU, hφU⟩, hα, hU, fun Z r z J hJ => ?_⟩
  have q1 := GlobalTheory.ThetaPtMove.sv_of_isValueAt hv r z hJ
  have q2 := GlobalTheory.VVRank.sv_of_isTwistPull P.A hσ (r ≫ (ptSecT P.A h).left) z hJ
  have q3 := GlobalTheory.VVRank.sv_of_isTwistPull P.A hs (r ≫ (ptSecT P.A (x * h)).left) z hJ
  have q4 := GlobalTheory.VVRank.sv_pullS P.A 1 β θ (r ≫ (ptSecT P.A ((x * h) ^ m)).left) z hJ
  rw [Category.assoc, GlobalTheory.ThetaCompare.pt_translT] at q2
  rw [Category.assoc, GlobalTheory.ThetaCompare.pt_mulT] at q3
  rw [vτ' Z r z J hJ, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_mul hJ, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ] at q1
  rw [← q1, q2, q3, q4, Units.val_mul, Category.assoc, _root_.mul_assoc]
  rfl

end GlobalTheory.UPoinc.USum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformLiftSectionsThickeningTower
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

theorem exists_lift_sections_tower : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (L : ∀ e, LB (Y e).left) (u : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))), (∀ e, (L e).IsLB ∧ (u e).IsGen) → LBIso (L 0) (GlobalTheory.AbLaw.pw H₀ k) → ∀ σ₀ : LB.Sec (L 0), ∃ σ : ∀ e, LB.Sec (L e), σ 0 = σ₀ ∧ ∀ e, Rel (β e) (u e) (σ (e + 1)) (σ e) := by
  intro R _ _ I Y β hY H₀ n s₀ hH hva
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy R I Y β hY H₀ n s₀ hH hva
  obtain ⟨k₀, hk₀⟩ := _root_.GlobalTheory.FormalAlg.towerCech_h1_uniform R I Y β hY n C
  refine ⟨k₀, fun k hk L u hL hL0 σ₀ => ?_⟩
  let γ : ∀ e, (Y 0).left ⟶ (Y e).left := fun e =>
    Nat.rec (motive := fun e => (Y 0).left ⟶ (Y e).left) (𝟙 _) (fun e g => g ≫ β e) e
  have hγs : ∀ e, γ e ≫ β e = γ (e + 1) := fun e => rfl
  have hP : (GlobalTheory.AbLaw.pw H₀ k).IsLB := isLB_pw hH _
  have hiso : ∀ e, LBIso ((L e).pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) := by
    intro e
    induction e with
    | zero => exact LBIso.chartPull (chartPullPull (L 0) (𝟙 _)) (chartPullId _) hL0
    | succ e ih =>
      refine LBIso.trans (pull_isLB (hL (e + 1)).1 _) (pull_isLB (hL e).1 _) hP ?_ ih
      exact LBIso.chartPull (chartPullSame (L (e + 1)) (fun _ => γ (e + 1)) (fun _ => β e) (fun _ => 1) (γ e)
        (fun _ => rfl)) (chartPullPull (L e) (γ e)) (LBIso.symm ⟨u e, (hL e).2⟩)
  have step : ∀ e (σ : LB.Sec (L e)), ∃ σ' : LB.Sec (L (e + 1)), Rel (β e) (u e) σ' σ := fun e σ =>
    _root_.GlobalTheory.FormalAlg.lift_step R I Y β hY n C H₀ s₀ hH hC γ rfl hγs e k (hk₀ k hk (e + 1)) (L e) (L (e + 1)) (u e)
      (hL e).1 (hL (e + 1)).1 (hL e).2 (hiso (e + 1)) σ
  choose f hf using step
  let σ : ∀ e, LB.Sec (L e) := fun e => Nat.rec (motive := fun e => LB.Sec (L e)) σ₀ (fun e s => f e s) e
  exact ⟨σ, rfl, fun e => hf e (σ e)⟩

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverPullbackSemiAbelianModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.Mum.CoverPull

theorem pt_mem_abLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (w : Sp Ω), M.pt w ∈ abLocus Z.G := by
  intro o Ω _ _ _ _ S ρS M U₀ EE hO Z w
  haveI : IsProper ρS.P.A.hom := ρS.P.isAb.proper
  haveI : IsProper ((Over.pullback Z.u₀).obj ρS.P.A).hom := by
    show IsProper (pullback.snd ρS.P.A.hom Z.u₀)
    infer_instance
  refine GlobalTheory.range_subset_abLocus_of_isProper (G' := (Over.pullback Z.u₀).obj ρS.P.A) (f := U₀.ι) (φ := Z.φ) Z.semi Z.cart.1 ?_
  have hm : M.pt w ∈ U₀ := M.top_le_preimage_pt hO.ne (x := w) trivial
  exact ⟨⟨_, hm⟩, rfl⟩

theorem exists_unif_pullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (T : Scheme.{0}) (h : T ⟶ M.Z) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ξ : Sp W ⟶ T, ((ξ ≫ h) ⁻¹' abLocus Z.G).Nonempty → ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ ((Over.pullback h).obj Z.G).left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'), IsGrpPullback G' ((Over.pullback h).obj Z.G) ξ β ∧ LBIso U'.LG.L ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull β) := by
  intro o Ω _ _ _ S ρS M U₀ EE Z T h W _ _ _ hW ξ hab
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → ∀ F : Y ⟶ X, (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  obtain ⟨hdvr, hc, hch⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  haveI := hch
  obtain ⟨D, A, U, hl, -⟩ := Z.unif W inferInstance inferInstance hc (ξ ≫ h) hab
  have hpt : (pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ) ≫ h = pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ ≫ h := Category.assoc _ _ _
  let β : pullback Z.G.hom (ξ ≫ h) ⟶ pullback Z.G.hom h :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ξ) (pullback.condition.trans hpt.symm)
  have hβf : β ≫ pullback.fst Z.G.hom h = pullback.fst Z.G.hom (ξ ≫ h) := pullback.lift_fst _ _ _
  have hβs : β ≫ pullback.snd Z.G.hom h = pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ := pullback.lift_snd _ _ _
  refine ⟨(Over.pullback (ξ ≫ h)).obj Z.G, inferInstance, inferInstance, β, D, A, U, ?_, ?_⟩
  · refine (isGrpPullback_pullback Z.G h).cancel ?_ hβs
    exact (isGrpPullback_pullback Z.G (ξ ≫ h)).congr rfl hβf.symm
  · exact LBIso.trans U.LG.isLB (pull_isLB Z.L.isLB _) (pull_isLB (pull_isLB Z.L.isLB _) _) hl
      (GlobalTheory.GenSpread.lbIso_pull_pull Z.L.isLB β hβf.symm)

end GlobalTheory.Mum.CoverPull

namespace GlobalTheory.Mum

theorem exists_uCover_of_zhOut : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → GlobalTheory.ZH.ZHOut ρS M U₀ EE → ∀ (b : o →+* R₁) (e : Ω →+* FractionRing R₁), (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ C : UCover R₁, C.A = A₁ := by
  intro R₁ _ _ _ o Ω _ _ _ _ S ρS M U₀ EE hO Z b e hb A₁ φ hcart hlb
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → ∀ F : Y ⟶ X, (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have hs : IsProper M.s := GlobalTheory.SpreadAb.isProper_of_isProjOver hO.proj
  have hy : (spMap e ≫ M.pt) ≫ M.s = jK R₁ ≫ spMap b := by
    rw [Category.assoc, M.pt_s, jK, spMap, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact hb x
  obtain ⟨M', h, hgp, -⟩ := _root_.GlobalTheory.Mum.exists_modif_graph R₁ o b M.Z M.s hs _ hy
  obtain ⟨P₀, hP₀⟩ := _root_.GlobalTheory.ZH.exists_cp_zhOut o Ω S ρS M U₀ EE hO Z
  have hw : pullback.fst Z.G.hom h ≫ Z.G.hom = ((Over.pullback h).obj Z.G).hom ≫ h := pullback.condition
  have mul : ∀ (T : Over M'.S) (x y : T ⟶ (Over.pullback h).obj Z.G), toBase hw (x * y) = toBase hw x * toBase hw y := by
    intro T x y
    exact Over.OverMorphism.ext ((isGrpPullback_pullback Z.G h).2 T x y (toBase hw x) (toBase hw y) rfl rfl).symm
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, -⟩ := GlobalTheory.UU.exists_isCPMap P₀ mul _ (pull_isLB P₀.L.isLB _) _
    (GlobalTheory.UU.pullIso_isGen P₀.L.isLB _)
  obtain ⟨α, hα, hαl⟩ := _root_.GlobalTheory.MumGen.genFibre_pullback R₁ o Ω S ρS M U₀ EE hO Z e M' h hgp A₁ φ hcart hlb
  refine ⟨{ toModif := M'
            G := (Over.pullback h).obj Z.G
            semi := by
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · have := Z.semi.comm; infer_instance
              · have := Z.semi.smooth; change Smooth (pullback.snd Z.G.hom h); infer_instance
              · have := Z.semi.separated; change IsSeparated (pullback.snd Z.G.hom h); infer_instance
              · have := Z.semi.quasiCompact; change QuasiCompact (pullback.snd Z.G.hom h); infer_instance
              · have := Z.semi.geomConnected; change GeometricallyConnected (pullback.snd Z.G.hom h); infer_instance
              · intro K _ _ q
                obtain ⟨E⟩ := Z.semi.fibres K (q ≫ h)
                let em : (Over.pullback (q ≫ h)).mapMon.obj (Mon.mk Z.G) ≅
                    (Over.pullback q).mapMon.obj ((Over.pullback h).mapMon.obj (Mon.mk Z.G)) :=
                  (Functor.mapMonNatIso (Over.pullbackComp q h) ≪≫ Functor.mapMonCompIso).app (Mon.mk Z.G)
                let e : (Over.pullback (q ≫ h)).obj Z.G ≅ (Over.pullback q).obj ((Over.pullback h).obj Z.G) :=
                  (Mon.forget _).mapIso em
                haveI : IsMonHom e.hom := by
                  show IsMonHom em.hom.hom
                  infer_instance
                haveI := E.grpB
                haveI := E.q_hom
                haveI := E.i_hom
                haveI : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv
                refine ⟨{ X := E.X
                          addCommGroup := E.addCommGroup
                          free := E.free
                          finite := E.finite
                          B := E.B
                          grpB := E.grpB
                          isAbelian := E.isAbelian
                          q := e.inv ≫ E.q
                          q_hom := inferInstance
                          q_flat := by rw [Over.comp_left]; have := E.q_flat; infer_instance
                          q_surjective := by rw [Over.comp_left]; have := E.q_surjective; infer_instance
                          q_quasiCompact := by rw [Over.comp_left]; have := E.q_quasiCompact; infer_instance
                          i := E.i ≫ e.hom
                          i_hom := inferInstance
                          isKernel := ?_ }⟩
                refine IsPullback.of_iso E.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
            P := ⟨⟨_, rig, pull_isLB P₀.L.isLB _, hr⟩, c, s, h₁, h₂, h₃⟩
            A := A₁
            α := α
            α_cart := hα
            α_lb := by
              show LBIso A₁.L ((P₀.L.L.pull (pullback.fst Z.G.hom h)).pull α)
              rw [hP₀]; exact hαl
            trait := ?_ }, rfl⟩
  intro W _ _ _ hW φW ξ hφ hξ
  obtain ⟨w, k, hk⟩ := _root_.GlobalTheory.Mum.modif_pt_over_gen R₁ M' W φW ξ hφ hξ
  have hab : ((ξ ≫ h) ⁻¹' abLocus Z.G).Nonempty := by
    refine ⟨w, ?_⟩
    have e1 : (ξ ≫ h) w = M.pt ((spMap e) k) := by
      rw [Scheme.Hom.comp_apply, hk, ← Scheme.Hom.comp_apply, hgp, Scheme.Hom.comp_apply]
    show (ξ ≫ h) w ∈ abLocus Z.G
    rw [e1]
    exact CoverPull.pt_mem_abLocus o Ω S ρS M U₀ EE hO Z _
  obtain ⟨G', iG, cG, β, D', A', U', hβ, hl⟩ := CoverPull.exists_unif_pullback o Ω S ρS M U₀ EE Z M'.S h W hW ξ hab
  have hid : spMap (RingHom.id W) ≫ ξ = ξ := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine ⟨W, _, inferInstance, inferInstance, RingHom.id W, G', iG, cG, β, D', A', U', hW, Function.injective_id,
    RingHom.Finite.id W, hid.symm ▸ hβ, ?_⟩
  show LBIso U'.LG.L ((P₀.L.L.pull (pullback.fst Z.G.hom h)).pull β)
  rw [hP₀]; exact hl

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentTriangularFactor
section
set_option autoImplicit false

open Matrix
open GlobalTheory.FlagFibre (Low)

namespace GlobalTheory.FlagCell

theorem exists_elim_row {R : Type} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (i : Fin m)
    (h : IsUnit (A.submatrix (Fin.castLE i.2.le) (Fin.castLE i.2.le)).det) :
    ∃ r : Fin m → R, r i = 1 ∧ (∀ k, i < k → r k = 0) ∧ ∀ j, j < i → ∑ k, r k * A k j = 0 := by
  classical
  set c : Fin i → Fin m := Fin.castLE i.2.le with hc
  set B := A.submatrix c c with hB
  set x : Fin i → R := (fun j => A i (c j)) ᵥ* B⁻¹ with hx
  have hxB : x ᵥ* B = fun j => A i (c j) := by
    rw [hx, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ h, Matrix.vecMul_one]
  have hlt : ∀ l, c l < i := fun l => l.2
  refine ⟨Pi.single i 1 - ∑ l, Pi.single (c l) (x l), ?_, ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.single_eq_same, Finset.sum_apply]
    rw [Finset.sum_eq_zero fun l _ => Pi.single_eq_of_ne (hlt l).ne' _, sub_zero]
  · intro k hk
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [Finset.sum_eq_zero fun l _ => Pi.single_eq_of_ne ((hlt l).trans hk).ne' _,
      Pi.single_eq_of_ne hk.ne', sub_zero]
  · intro j hj
    have hj' : c ⟨j, hj⟩ = j := rfl
    have h1 := congrFun hxB ⟨j, hj⟩
    simp only [Matrix.vecMul, dotProduct, hB, Matrix.submatrix_apply, hj'] at h1
    simp only [Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, one_mul]
    rw [h1, sub_self]

theorem exists_lu (R : Type) [CommRing R] (m : ℕ) (A : Matrix (Fin m) (Fin m) R)
    (h : ∀ l : Fin (m + 1), IsUnit (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det) :
    ∃ (n : Low m → R) (M : Matrix (Fin m) (Fin m) R),
      M.BlockTriangular id ∧ IsUnit M.det ∧ A = uniR n * M := by
  classical
  choose r h1 h0 hA using fun i : Fin m => exists_elim_row A i (h i.castSucc)
  let L : Matrix (Fin m) (Fin m) R := Matrix.of r
  have hL : L.BlockTriangular OrderDual.toDual := fun i k hk => h0 i k hk
  have hdet : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L hL]
    exact Finset.prod_eq_one fun i _ => h1 i
  have hu : IsUnit L.det := hdet ▸ isUnit_one
  have hAu : IsUnit A.det := by simpa using h (Fin.last m)
  letI := L.invertibleOfIsUnitDet hu
  have hLi : L⁻¹.BlockTriangular OrderDual.toDual := Matrix.blockTriangular_inv_of_blockTriangular hL
  have hd : ∀ i, L⁻¹ i i = 1 := by
    intro i
    have := congrFun (congrFun (Matrix.mul_nonsing_inv L hu) i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.one_apply_eq] at this
    · have h2 : L i i = 1 := h1 i
      rwa [h2, one_mul] at this
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [hLi (i := k) (j := i) hk, mul_zero]
      · rw [hL (i := i) (j := k) hk, zero_mul]
    · simp
  refine ⟨fun s => L⁻¹ s.1.1 s.1.2, L * A, fun i j hj => hA i j hj, ?_, ?_⟩
  · rw [Matrix.det_mul]; exact hu.mul hAu
  · have : (uniR fun s : Low m => L⁻¹ s.1.1 s.1.2) = L⁻¹ := by
      ext a b
      rw [uniR_apply]
      split_ifs with hab hab'
      · rfl
      · rw [hab', hd]
      · exact (hLi (i := a) (j := b) (show a < b from lt_of_le_of_ne (not_lt.1 hab) hab')).symm
    rw [this, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hu, Matrix.one_mul]

end GlobalTheory.FlagCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem IntFam.existsUnique_over : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ)
    (F₀ : IntFam I D k) (F : Type) [Field F] [Algebra (FractionRing R) F], ∃! s : Fam D F k, F₀.Over s := by
  intro R _ _ I D k F₀ F _ _
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hL := D.P.isLB
  have hext : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F₀.F.s α)
      (D.famφB α) (DegPre.famε k) (F₀.f α) (DegPre.prB D (FractionRing R)).left 1 := fun α => by
    have h := F₀.ext α
    have e : scal (DegPre.BF D (FractionRing R)).hom (1 : R) = 1 := by
      unfold scal
      rw [map_one, map_one]
    rwa [e] at h
  have hov : F₀.Over (famPull D (FractionRing R) F hG k F₀.F) := fun α => by
    refine SectionScalarValuation.secScal_of_sval hL fun y J hJ => ?_
    refine Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm
    refine Eq.trans ?_ (SectionScalarValuation.secScal_sval (hext α) _ y hJ)
    congr 1
    rw [Category.assoc, ← Over.comp_left, famMap_snd]
  refine ⟨_, hov, fun s hs => fam_ext fun α j => congrArg (fun q => LB.Sec.f q j)
    (sec_ext' hL fun y J hJ => ?_)⟩
  rw [← SectionScalarValuation.secScal_sval (hs α) (𝟙 _) y hJ, SectionScalarValuation.secScal_sval (hov α) (𝟙 _) y hJ]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePushoutTorsorSectionDifference
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem isSec_sub_root_eq {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {n : ℕ}
    {b : Fn0 A} {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {s s' : RootFn A D}
    (hs : IsSec n b x s) (hs' : IsSec n b x s') {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z z' : Pt A D') (hz : z ^ n = spOver φ ≫ x) (hz' : z' ^ n = spOver φ ≫ x) :
    s D' φ z' - s' D' φ z' = s D' φ z - s' D' φ z := by
  have hw : (z⁻¹ * z') ^ n = 1 := by rw [mul_pow, inv_pow, hz, hz', inv_mul_cancel]
  have e : z' = z * (z⁻¹ * z') := (mul_inv_cancel_left z z').symm
  rw [e, hs.2 D' φ z _ hz hw, hs'.2 D' φ z _ hz hw]
  abel

theorem isSec_sub_natural {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {b : Fn0 A} {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {s s' : RootFn A D}
    (hs : IsSec n b x s) (hs' : IsSec n b x s') {D' : Type} [CommRing D'] [Algebra R D']
    {D'' : Type} [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'')
    (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) :
    s D'' (ψ.comp φ) (spOver ψ ≫ z) - s' D'' (ψ.comp φ) (spOver ψ ≫ z) = ψ (s D' φ z - s' D' φ z) := by
  rw [hs.1 D' D'' φ ψ z hz, hs'.1 D' D'' φ ψ z hz, map_sub]

theorem root_spOver {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {D' : Type} [CommRing D'] [Algebra R D']
    {D'' : Type} [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'')
    (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) : (spOver ψ ≫ z) ^ n = spOver (ψ.comp φ) ≫ x := by
  rw [← MonObj.comp_pow z n (spOver ψ), hz, ← Category.assoc, spOver_comp]

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem isSec_sub_existsUnique : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ (b : Fn0 A) (D : Type) [CommRing D] [Algebra R D] (x : Pt A D) (s s' : RootFn A D),
    IsSec n b x s → IsSec n b x s' → ∃! e : D, ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (z : Pt A D'), z ^ n = spOver φ ≫ x → s D' φ z - s' D' φ z = φ e := by
  intro R _ A _ _ n hR b D _ _ x s s' hs hs'
  obtain ⟨D₁, _, _, ψ, z₀, hψ, hz₀⟩ := hR D x
  have hdesc := GlobalTheory.ff_descent_pairs R D D₁ ψ hψ (s D₁ ψ z₀ - s' D₁ ψ z₀) (fun E _ _ α β hαβ ↦ by
    rw [← isSec_sub_natural hs hs' ψ α z₀ hz₀, ← isSec_sub_natural hs hs' ψ β z₀ hz₀]
    have hα := root_spOver ψ α z₀ hz₀
    have hβ := root_spOver ψ β z₀ hz₀
    rw [hαβ] at hα ⊢
    exact isSec_sub_root_eq hs hs' (β.comp ψ) (spOver β ≫ z₀) (spOver α ≫ z₀) hβ hα)
  obtain ⟨e, he, heu⟩ := hdesc
  have key : ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D'), z ^ n = spOver φ ≫ x →
      s D' φ z - s' D' φ z = φ e := by
    intro D' _ _ φ z hz
    obtain ⟨E', _, _, ψ', φ', hψ', hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
    have hinj : Function.Injective ψ' := by
      letI : Algebra D' E' := (ψ' : D' →+* E').toAlgebra
      haveI : Module.FaithfullyFlat D' E' := hψ'
      exact FaithfulSMul.algebraMap_injective D' E'
    apply hinj
    have h1 := root_spOver φ ψ' z hz
    have h2 := root_spOver ψ φ' z₀ hz₀
    rw [← isSec_sub_natural hs hs' φ ψ' z hz]
    rw [hsq] at h1 ⊢
    rw [isSec_sub_root_eq hs hs' _ _ _ h2 h1, isSec_sub_natural hs hs' ψ φ' z₀ hz₀, ← he]
    exact (congrArg (fun f : D →ₐ[R] E' ↦ f e) hsq).symm
  exact ⟨e, key, fun e' he' ↦ heu e' ((he' D₁ ψ z₀ hz₀).symm)⟩

end GlobalTheory.PtExt
end

