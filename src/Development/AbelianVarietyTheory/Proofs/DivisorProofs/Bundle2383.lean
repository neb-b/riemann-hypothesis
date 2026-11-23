module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPullbackPrescribed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCompGroupPullbackIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LamPullComp

section Iso

variable {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {B' : Over S₁} [GrpObj B']
  {G' : Over S₂} [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left} {β₂ : (G2 B').left ⟶ (G2 G).left}
  {sq : (G2 G').left ⟶ (G2 B').left} {L : LB G.left} {L' : LB G'.left}

theorem pt_eq (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (I : ULift.{0} (Finset (Fin 2))) (x : (G2 G').left) :
    lamφ G I (β₂ (sq x)) = φ (lamφ G' I x) :=
  congrArg (fun g => g x) (h I)

theorem iso_le (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ)
    (p : (((abelian₂ G L).pull β₂).pull sq).ι × (abelian₂ G' L').ι) (I : ULift.{0} (Finset (Fin 2))) :
    (((abelian₂ G L).pull β₂).pull sq).U p.1 ⊓ (abelian₂ G' L').U p.2 ≤
      lamφ G' I ⁻¹ᵁ ((L.pull φ).U (fun _ => p.1 PUnit.unit PUnit.unit I) ⊓ L'.U (p.2 I)) := fun x hx =>
  ⟨mem_pull.2 (by
    have := Set.mem_iInter.1 (mem_pull.1 (mem_pull.1 hx.1)) I
    show φ (lamφ G' I x) ∈ _
    rw [← pt_eq h I x]; exact this), Set.mem_iInter.1 hx.2 I⟩

def iso2 (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) :
    LB.Iso (abelian₂ G' L') (((abelian₂ G L).pull β₂).pull sq) :=
  ⟨fun p => ∏ I, (res (iso_le h p I)
    (pullU (lamφ G' I) _ (v.s (fun _ => p.1 PUnit.unit PUnit.unit I, p.2 I)))) ^ lamε I⟩

theorem mumfordBundle_pullback_composite_germ_iso (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) {Y : Scheme.{0}}
    (r : Y ⟶ (G2 G').left) (y : Y) (j : PUnit → ULift.{0} (Finset (Fin 2)) → L.ι)
    (k : ULift.{0} (Finset (Fin 2)) → L'.ι)
    (hj : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j PUnit.unit I)) (hk : ∀ I, lamφ G' I (r y) ∈ L'.U (k I)) :
    gw (iso2 h v) r y j k = ∏ I, gw v (r ≫ lamφ G' I) y (j PUnit.unit I) (k I) ^ lamε I := by
  have hm : r y ∈ (((abelian₂ G L).pull β₂).pull sq).U (fun _ => j) ⊓ (abelian₂ G' L').U k :=
    ⟨mem_pull.2 (mem_pull.2 (Set.mem_iInter.2 fun I => by
      show lamφ G I (β₂ (sq (r y))) ∈ L.U (j PUnit.unit I)
      rw [pt_eq h]; exact hj I)), Set.mem_iInter.2 hk⟩
  unfold gw
  dsimp only [iso2]
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun I _ => (map_zpow _ _ _).trans (congrArg (· ^ lamε I) ?_))
  exact (gm_res r y _ hm _).trans (gm_pull r (lamφ G' I) y ((L.pull φ).U (fun _ => j PUnit.unit I) ⊓ L'.U (k I))
    ⟨mem_pull.2 (hj I), hk I⟩ _)

theorem mumfordBundle_pullback_composite_isGen (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) (hv : PGen v) :
    PGen (iso2 h v) := by
  intro Y r y j j' k k' hj hj' hk hk'
  have bj := mem_pull.1 hj
  have bj' := mem_pull.1 hj'
  have aj : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j PUnit.unit I) := fun I => by
    rw [← pt_eq h I]; exact Set.mem_iInter.1 bj I
  have aj' : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j' PUnit.unit I) := fun I => by
    rw [← pt_eq h I]; exact Set.mem_iInter.1 bj' I
  have ak : ∀ I, lamφ G' I (r y) ∈ L'.U (k I) := fun I => Set.mem_iInter.1 hk I
  have ak' : ∀ I, lamφ G' I (r y) ∈ L'.U (k' I) := fun I => Set.mem_iInter.1 hk' I
  rw [mumfordBundle_pullback_composite_germ_iso h v r y j k aj ak, mumfordBundle_pullback_composite_germ_iso h v r y j' k' aj' ak']
  have e₀ := gm_pull_g (abelian₂ G L) β₂ (r ≫ sq) y j j' hj hj'
  have e₁ := gm_linComb L (lamφ G) lamε ((r ≫ sq) ≫ β₂) y (j PUnit.unit) (j' PUnit.unit) bj bj'
  have e₂ := gm_linComb L' (lamφ G') lamε r y k k' hk hk'
  erw [e₀, e₁, e₂]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [hv Y (r ≫ lamφ G' I) y (j PUnit.unit I) (j' PUnit.unit I) (k I) (k' I) (aj I) (aj' I) (ak I) (ak' I),
    Category.assoc, Category.assoc, Category.assoc, h, mul_zpow, mul_zpow, inv_zpow]

end Iso

theorem lamIso_comp_pull : ∀ {S S₁ S₂ S₀ : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (B' : Over S₁) [GrpObj B'] (G' : Over S₂) [GrpObj G'] [IsCommMonObj G'] (T : Over S₀) [GrpObj T] [IsCommMonObj T] (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S₁) (β' : B'.left ⟶ G.left) (Φ : G'.left ⟶ B'.left) (φ : G'.left ⟶ G.left) (β₂ : (G2 B').left ⟶ (G2 G).left) (β₂' : (G2 B').left ⟶ (G2 T).left) (L : LB G.left) (L' : LB G'.left) (M : LB T.left) (gp' : IsGrpPullback B' G f₁ β') (gΦ : IsGrpPullback G' B' f₂ Φ), IsSquare β' β₂ → Φ ≫ β' = φ → L.IsLB → L'.IsLB → M.IsLB → ∀ (v : LB.Iso L' (L.pull φ)) (w₁ : LB.Iso ((abelian₂ G L).pull β₂) ((abelian₂ T M).pull β₂')), v.IsGen → w₁.IsGen → ∃ w : LB.Iso (abelian₂ G' L') ((abelian₂ T M).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂')), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ T.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  intro S S₁ S₂ S₀ G _ _ B' _ G' _ _ T _ _ f₁ f₂ β' Φ φ β₂ β₂' L L' M gp' gΦ hsq hΦ hL hL' hM v w₁ hv hw₁
  have gp : IsGrpPullback G' G (f₂ ≫ f₁) φ := (IsGrpPullback.comp gΦ gp').congr rfl hΦ
  have e1 : GlobalTheory.HalfBC.sqOf gΦ ≫ β₂ = GlobalTheory.HalfBC.sqOf gp := by
    apply pullback.hom_ext
    · show _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, hsq.1, ← Category.assoc]
      unfold GlobalTheory.HalfBC.sqOf
      rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      show ((fst G' G').left ≫ Φ) ≫ β' = (fst G' G').left ≫ φ
      rw [Category.assoc, hΦ]
    · show _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, hsq.2, ← Category.assoc]
      unfold GlobalTheory.HalfBC.sqOf
      rw [← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
      show ((snd G' G').left ≫ Φ) ≫ β' = (snd G' G').left ≫ φ
      rw [Category.assoc, hΦ]
  have h : ∀ I, GlobalTheory.HalfBC.sqOf gΦ ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ := fun I => by
    rw [← Category.assoc, e1, GlobalTheory.HalfBC.sqOf_lamφ]
  have hΛT : (abelian₂ T M).IsLB := DVR.linComb_isLB _ hM _ _
  have hΛG : ((abelian₂ G L).pull β₂).IsLB := LB.isLB_pull (DVR.linComb_isLB _ hL _ _) _
  have hΛ' : (abelian₂ G' L').IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨w, Tw⟩ := exists_comp hΛG w₁ (iso2 h v) ((isGen_iff _).1 hw₁) (mumfordBundle_pullback_composite_isGen h v ((isGen_iff v).1 hv)) hΛT hΛ'
  refine ⟨w, (isGen_iff _).2 (Tw.pgen_comp hΛG ((isGen_iff _).1 hw₁) (mumfordBundle_pullback_composite_isGen h v ((isGen_iff v).1 hv))), ?_⟩
  intro Z p z J J₁ J' hJ hJ₁ hJ'
  have t := Tw Z p z (fun I => J (p ≫ (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ lamφ T I))
    (fun _ I => J₁ ((p ≫ lamφ G' I) ≫ φ)) (fun I => J' (p ≫ lamφ G' I))
    (Set.mem_iInter.2 fun I => hJ (p ≫ (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ lamφ T I))
    (mem_pull.2 (Set.mem_iInter.2 fun I => by
      show lamφ G I (β₂ (GlobalTheory.HalfBC.sqOf gΦ (p z))) ∈ L.U (J₁ ((p ≫ lamφ G' I) ≫ φ))
      rw [pt_eq h]; exact hJ₁ ((p ≫ lamφ G' I) ≫ φ)))
    (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ G' I))
  refine t.trans (congrArg₂ (· * ·) ?_ ?_)
  · show _ = gw w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z (fun I => J ((p ≫ GlobalTheory.HalfBC.sqOf gΦ) ≫ β₂' ≫ lamφ T I))
      (fun _ I => J₁ ((p ≫ GlobalTheory.HalfBC.sqOf gΦ) ≫ β₂ ≫ lamφ G I))
    simp only [Category.assoc, h]
  · exact mumfordBundle_pullback_composite_germ_iso h v p z _ _ (fun I => hJ₁ ((p ≫ lamφ G' I) ≫ φ)) (fun I => hJ' (p ≫ lamφ G' I))

end GlobalTheory.LamPullComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoSquarePassesSecondIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FactorPull

theorem lam_down_gen : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {B C : Over S} {B₁ C₁ : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj C]
  [IsCommMonObj C] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj C₁] [IsCommMonObj C₁] {δ : C₁.left ⟶ C.left} {M : LB B.left} {N : LB C.left} {M₁ : LB B₁.left} {N₁ : LB C₁.left}
  (gC : IsGrpPullback C₁ C f δ), M.IsLB → N.IsLB → M₁.IsLB → N₁.IsLB → ∀ (β₂ : (G2 B₁).left ⟶ (G2 B).left) (u : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ B M).pull β₂)), u.IsGen →
  ∀ (v' : LB.Iso N₁ (N.pull δ)), v'.IsGen → ∀ {m : (G2 B).left ⟶ (G2 C).left} {m₁ : (G2 B₁).left ⟶ (G2 C₁).left},
    m₁ ≫ sqOf gC = β₂ ≫ m → ∀ (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen →
    ∃ w₁ : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ C₁ N₁).pull m₁), w₁.IsGen ∧
      ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 B₁).left) (z : Z) I J I₁ J₁, Good N z I → Good M z J → Good N₁ z I₁ →
        Good M₁ z J₁ → (∏ k, om v' z I I₁ ((p ≫ m₁) ≫ lamφ C₁ k) ^ lamε k) * lamVal w₁ p z I₁ J₁ =
          lamVal w (p ≫ β₂) z I J * lamVal u p z J J₁ := by
  intro S S' f B C B₁ C₁ _ _ _ _ _ _ _ _ δ M N M₁ N₁ gC hM hN hM₁ hN₁ β₂ u hu v' hv' m m₁ hm w hw
  have lM : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have lN : (abelian₂ C N).IsLB := DVR.linComb_isLB _ hN _ _
  have lM₁ : (abelian₂ B₁ M₁).IsLB := DVR.linComb_isLB _ hM₁ _ _
  have lN₁ : (abelian₂ C₁ N₁).IsLB := DVR.linComb_isLB _ hN₁ _ _
  have pw := (isGen_iff _).1 hw
  have pu := (isGen_iff u).1 hu
  have pv' := pgen_lamIso gC v' ((isGen_iff v').1 hv')
  obtain ⟨w₂, T⟩ := exists_comp lM w u pw pu lN lM₁
  have p₂ := pgen_pullCongr hm.symm (T.pgen_comp lM pw pu)
  obtain ⟨w₁, T'⟩ := exists_cancel lN (lamIso gC v') (pullCongr hm.symm w₂) pv' p₂ lN₁ lM₁
  refine ⟨w₁, (isGen_iff _).2 (T'.pgen_cancel lN pv' p₂), fun Z p z I J I₁ J₁ hI hJ hI₁ hJ₁ => ?_⟩
  have e : (p ≫ m₁) ≫ sqOf gC = (p ≫ β₂) ≫ m := by rw [Category.assoc, hm, Category.assoc]
  have t := T Z p z (fun k => I (((p ≫ β₂) ≫ m) ≫ lamφ C k))
    (fun k => J ((p ≫ β₂) ≫ lamφ B k)) (fun k => J₁ (p ≫ lamφ B₁ k))
    (Set.mem_iInter.2 fun k => hI (((p ≫ β₂) ≫ m) ≫ lamφ C k))
    (Set.mem_iInter.2 fun k => hJ ((p ≫ β₂) ≫ lamφ B k))
    (Set.mem_iInter.2 fun k => hJ₁ (p ≫ lamφ B₁ k))
  have t' := T' Z p z (fun k => I (((p ≫ m₁) ≫ sqOf gC) ≫ lamφ C k))
    (fun k => I₁ ((p ≫ m₁) ≫ lamφ C₁ k)) (fun k => J₁ (p ≫ lamφ B₁ k))
    (Set.mem_iInter.2 fun k => hI (((p ≫ m₁) ≫ sqOf gC) ≫ lamφ C k))
    (Set.mem_iInter.2 fun k => hI₁ ((p ≫ m₁) ≫ lamφ C₁ k))
    (Set.mem_iInter.2 fun k => hJ₁ (p ≫ lamφ B₁ k))
  replace t' := (gw_pullCongr _ _ _ _ _ _).symm.trans (t'.trans (congrArg₂ (· * ·) (gw_lam gC v' (p ≫ m₁) z hI hI₁) rfl))
  rw [e] at t'
  replace t' := t.symm.trans t'
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) (t'.symm.trans (congrArg₂ (· * ·) ?_ ?_))
  · show Geo.Tor.gw w₁ p z (fun k => I₁ (p ≫ m₁ ≫ lamφ C₁ k)) (fun k => J₁ (p ≫ lamφ B₁ k)) = _
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw w (p ≫ β₂) z (fun k => I ((p ≫ β₂) ≫ m ≫ lamφ C k))
      (fun k => J ((p ≫ β₂) ≫ lamφ B k))
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw u p z (fun k => J (p ≫ β₂ ≫ lamφ B k)) (fun k => J₁ (p ≫ lamφ B₁ k))
    simp only [Category.assoc]

end GlobalTheory.FactorPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackHomPairTrivialAxes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumAxes

theorem one_comp_hom' {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : X ⟶ M) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem gen_pull_lam {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (c : T ⟶ G2 G) (hc : c ≫ fst G G = 1 ∨ c ≫ snd G G = 1) :
    ∃ t : ((abelian₂ G L).pull c.left).Gen, t.IsGen := by
  have hR : GlobalTheory.CoordToExt.Refines ((abelian₂ G L).pull c.left) L
      (fun p : PUnit × ULift.{0} (Finset (Fin 2)) => c.left ≫ (psum G (x2 G) p.2.down).left)
      (fun p => (-1) ^ (2 - p.2.down.card) * 1) :=
    (GlobalTheory.CoordToExt.refines_self (L := L) _ _).linComb _ _
  refine hR.exists_gen hL (φ' := PEmpty.elim) (ε' := PEmpty.elim) ?_ (LB.oneGen L) GlobalTheory.CoordToExt.isGen_one
  intro U _ h
  have hp : ∀ I : Finset (Fin 2), c.left ≫ (psum G (x2 G) I).left = (psum G ![c ≫ fst G G, c ≫ snd G G] I).left :=
    fun I => by
      have := psum_hom (preHom (G := G) c) (x2 G) I
      have e : (fun i => preHom (G := G) c (x2 G i)) = ![c ≫ fst G G, c ≫ snd G G] := by
        funext i; fin_cases i <;> rfl
      rw [e] at this
      exact congrArg (fun z => z.left) this
  simp only [hp]
  rw [Fintype.prod_prod_type]
  have hu : (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by decide
  simp only [Finset.univ_unique, Finset.prod_singleton, hu]
  simp only [Finset.prod_insert (by decide : (⟨∅⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{0}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{1}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0, 1}⟩} : Finset _)),
    Finset.prod_singleton]
  have p0 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs ∅ = 1 := fun _ => rfl
  have p1 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0} = xs 0 * 1 := fun _ => rfl
  have p2 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {1} = xs 1 * 1 := fun _ => rfl
  have p3 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0, 1} = xs 0 * (xs 1 * 1) := fun _ => rfl
  simp only [p0, p1, p2, p3, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, Finset.univ_eq_empty,
    Finset.prod_empty]
  rcases hc with hc | hc <;> simp [hc]

theorem gen_axes : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (L : LB G'.left), L.IsLB → ∀ (u v : G ⟶ G'), IsMonHom u → IsMonHom v → ∀ P : LB (G2 G).left, P.IsLB →
    LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ u) (snd G G ≫ v)).left) →
    (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧
      (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) := by
  intro S G G' _ _ _ _ L hL u v hu hv P hP hiso
  have hΛ : (abelian₂ G' L).IsLB := GlobalTheory.SabBaseChange.cube_isLB (x2 G') hL
  have key : ∀ a : G ⟶ G2 G, (a ≫ lift (fst G G ≫ u) (snd G G ≫ v)) ≫ fst G' G' = 1 ∨
      (a ≫ lift (fst G G ≫ u) (snd G G ≫ v)) ≫ snd G' G' = 1 → ∃ t : (P.pull a.left).Gen, t.IsGen := by
    intro a ha
    have h1 : LBIso (P.pull a.left) ((abelian₂ G' L).pull (a ≫ lift (fst G G ≫ u) (snd G G ≫ v)).left) :=
      GlobalTheory.Ex.GenericFibre.lbIso_pull hiso a.left (Over.comp_left ..)
    obtain ⟨t, ht⟩ := gen_pull_lam hL _ ha
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hΛ _) (pull_isLB hP _) h1.symm t ht
  refine ⟨key _ (Or.inl ?_), key _ (Or.inr ?_)⟩
  · rw [Category.assoc, lift_fst, lift_fst_assoc]; exact one_comp_hom' u
  · rw [Category.assoc, lift_snd, lift_snd_assoc]; exact one_comp_hom' v

end GlobalTheory.MumAxes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackInclusionFactorSymmetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MumSymPull

open GlobalTheory.CoordToExt GlobalTheory.RigidTranslate

variable {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}

omit [IsCommMonObj G] in
theorem comp_psum {n : ℕ} (h : T' ⟶ T) (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    h ≫ psum G x I = psum G (fun k => h ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rw [← Category.assoc, comp_toUnit]
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [← ih]
    exact MonObj.comp_mul _ _ _

def chartPullCube (L : LB G.left) (s t : T ⟶ G) (h : T' ⟶ T) (s' t' : T' ⟶ G) (hs : s' = h ≫ s) (ht : t' = h ≫ t) :
    ChartPull (cubeLB G ![s', t'] L) (cubeLB G ![s, t] L) h.left :=
  chartPullSame L _ _ _ h.left fun I => by
    rw [← Over.comp_left, comp_psum]
    congr 2
    funext k
    fin_cases k
    exacts [hs, ht]

theorem cube_swap (hL : L.IsLB) (s t : T ⟶ G) : LBIso (cubeLB G ![s, t] L) (cubeLB G ![t, s] L) := by
  refine lbIso_of_refines hL (refines_self _ _) (refines_self _ _) _ isGen_one fun U _ f => ?_
  refine (congrArg₂ (· * ·) (Fintype.prod_empty _) (prod_square ![s, t] fun x => f x.left)).trans
    (Eq.symm ((prod_square ![t, s] fun x => f x.left).trans ?_))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, _root_.one_mul, _root_.mul_comm t s]
  rw [mul_right_comm (f _) (f t.left)⁻¹]

theorem cube_pull (hL : L.IsLB) (s t : T ⟶ G) (h : T' ⟶ T) (s' t' : T' ⟶ G) (hs : s' = h ≫ s) (ht : t' = h ≫ t) :
    LBIso (cubeLB G ![s', t'] L) ((cubeLB G ![s, t] L).pull h.left) := by
  have r : LBIso (cubeLB G ![s, t] L) (cubeLB G ![s, t] L) := exists_iso hL rfl _
  exact LBIso.chartPull (chartPullCube L s t h s' t' hs ht) (GlobalTheory.chartPullPull _ h.left) r

theorem cube_adj {a b : G ⟶ G}
    (H : LBIso (cubeLB G ![fst G G ≫ a, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ b] L)) (s t : T ⟶ G) :
    LBIso (cubeLB G ![s ≫ a, t] L) (cubeLB G ![s, t ≫ b] L) :=
  LBIso.chartPull (chartPullCube L _ _ (lift s t) _ _ (by simp) (by simp))
    (chartPullCube L _ _ (lift s t) _ _ (by simp) (by simp)) H

theorem lbIso_swap : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (L : LB G'.left), L.IsLB → ∀ (O : Type) [Ring O] [StarRing O] (oG : RingAct G' O), (∀ a : O, LBIso (cubeLB G' ![fst G' G' ≫ oG.act a, snd G' G'] L) (cubeLB G' ![fst G' G', snd G' G' ≫ oG.act (star a)] L)) → ∀ (e f : O) (inc : G ⟶ G'), IsMonHom inc → inc ≫ oG.act e = inc → star e * f * e = star e * star f * e → ∀ P : LB (G2 G).left, P.IsLB → LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act f)).left) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) := by
  intro S G G' _ _ _ _ L hL O _ _ oG hadj e f inc _ he hef P hP hPL
  have cI : ∀ s t : G2 G ⟶ G', (cubeLB G' ![s, t] L).IsLB := fun s t => DVR.linComb_isLB _ hL _ _
  have lI : (abelian₂ G' L).IsLB := DVR.linComb_isLB _ hL _ _
  set x : G2 G ⟶ G' := fst G G ≫ inc with hx
  set y : G2 G ⟶ G' := snd G G ≫ inc with hy
  have xe : x ≫ oG.act e = x := by rw [hx, Category.assoc, he]
  have ye : y ≫ oG.act e = y := by rw [hy, Category.assoc, he]
  have h₁ : LBIso P (cubeLB G' ![x, y ≫ oG.act f] L) :=
    hPL.trans hP (pull_isLB lI _) (cI _ _) (cube_pull hL _ _ _ _ _ (by simp) (by simp [hy])).symm
  have h₂ : LBIso (P.pull (lift (snd G G) (fst G G)).left) (cubeLB G' ![y, x ≫ oG.act f] L) :=
    LBIso.chartPull (GlobalTheory.chartPullPull P _)
      (chartPullCube L _ _ (lift (snd G G) (fst G G)) _ _ (by simp [hx, hy]) (by simp [hx, hy])) h₁
  have h₃ := cube_swap hL y (x ≫ oG.act f)
  have h₄ := cube_adj (hadj f) x y
  have h₅ := cube_adj (hadj e) x (y ≫ oG.act (star f))
  have h₆ := cube_adj (hadj e) x (y ≫ oG.act f)
  rw [xe] at h₅ h₆
  have k : (y ≫ oG.act (star f)) ≫ oG.act (star e) = (y ≫ oG.act f) ≫ oG.act (star e) := by
    have := congrArg (fun a => y ≫ oG.act a) hef
    simp only [oG.map_mul] at this
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc, ye] at this
    exact this.symm
  rw [k] at h₅
  have h₇ : LBIso (cubeLB G' ![y, x ≫ oG.act f] L) (cubeLB G' ![x, y ≫ oG.act f] L) :=
    h₃.trans (cI _ _) (cI _ _) (cI _ _) (h₄.trans (cI _ _) (cI _ _) (cI _ _)
      (h₅.trans (cI _ _) (cI _ _) (cI _ _) h₆.symm))
  exact h₁.trans hP (cI _ _) (pull_isLB hP _) (h₇.symm.trans (cI _ _) (cI _ _) (pull_isLB hP _) h₂.symm)

end GlobalTheory.MumSymPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem degPre_c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = 1 := by
  have h := D.c_add 0 0
  rw [add_zero, padd, ← Hom.mul_def] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

theorem tens_inc_pr_facts (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (i₀ : Fin r) :
    IsMonHom (T.inc i₀) ∧ T.inc i₀ ≫ T.pr i₀ = 𝟙 _ ∧ T.pr i₀ ≫ T.inc i₀ = T.act (Matrix.single i₀ i₀ 1) ∧
      ∀ y, D'.c (T.xi i₀ y) = D.c y ≫ T.inc i₀ := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr']
    rw [(T.pr_hom i).one_hom]
    split_ifs
    · simp
    · rw [comp_one, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr']
    rw [(T.pr_hom i).mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, T.inc_pr']
    split_ifs
    · simp
    · rw [comp_one]
      have : ((1 : D.P.A ⟶ D.P.A) ⊗ₘ (1 : D.P.A ⟶ D.P.A)) = lift (fst _ _ ≫ 1) (snd _ _ ≫ 1) := by
        ext <;> simp
      rw [this, ← Hom.mul_def, comp_one, comp_one, _root_.mul_one]
  · simpa using T.inc_pr' i₀ i₀
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr', Tens.act_pr]
    by_cases h : i = i₀
    · subst h
      rw [if_pos rfl, Category.comp_id, Finset.prod_eq_single i]
      · simp [Matrix.single_apply]
      · intro j _ hj
        simp [Matrix.single_apply, Ne.symm hj]
      · simp
    · rw [if_neg h, comp_one]
      symm
      apply Finset.prod_eq_one
      intro j _
      simp [Matrix.single_apply, Ne.symm h]
  · intro y
    apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr', T.c_pr]
    by_cases h : i = i₀
    · subst h
      simp [Tens.xi]
    · rw [if_neg h, comp_one]
      simp [Tens.xi, Pi.single_apply, h, degPre_c_zero]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentX
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_ext_of_isNilpotent :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ ψ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        (∀ i, φ (X i) = ψ (X i)) → φ = ψ := by
  intro k _ σ _ A _ _ φ ψ hφ h
  classical
  obtain ⟨N₁, h₁⟩ := GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ A φ hφ
  obtain ⟨N₂, h₂⟩ := GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ A ψ (fun i => h i ▸ hφ i)
  have hp : φ.comp (MvPolynomial.coeToMvPowerSeries.algHom k) =
      ψ.comp (MvPolynomial.coeToMvPowerSeries.algHom k) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [h i]
  have hm : ∀ (α : σ →₀ ℕ) (c : k), φ (monomial α c) = ψ (monomial α c) := by
    intro α c
    have := DFunLike.congr_fun hp (MvPolynomial.monomial α c)
    simpa [MvPolynomial.coe_monomial] using this
  have hfin : {α : σ →₀ ℕ | α.degree ≤ N₁ + N₂}.Finite := Finsupp.finite_of_degree_le _
  apply AlgHom.ext
  intro f
  set p : MvPowerSeries σ k := ∑ α ∈ hfin.toFinset, monomial α (coeff α f) with hpdef
  have hc : ∀ α : σ →₀ ℕ, α.degree ≤ N₁ + N₂ → coeff α (f - p) = 0 := by
    intro α hα
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, hpdef, map_sum, Finset.sum_eq_single α]
    · simp
    · intro β _ hβ
      rw [coeff_monomial_ne hβ.symm]
    · intro hn
      exact absurd (by simpa using hα) hn
  have e₁ : φ (f - p) = 0 := h₁ _ (fun α hα => hc α (by omega))
  have e₂ : ψ (f - p) = 0 := h₂ _ (fun α hα => hc α (by omega))
  have e₃ : φ p = ψ p := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hpdef, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun α _ => hm _ _)
  rw [map_sub, sub_eq_zero] at e₁ e₂
  rw [e₁, e₂, e₃]

end GlobalTheory
end

